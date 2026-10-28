/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <algorithm>
#include <array>
#include <atomic>
#include <cerrno>
#include <cstdio>
#include <cstring>
#include <deque>
#include <functional>
#include <mutex>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <memory>
#include <fcntl.h>
#include <sys/stat.h>
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
#include <sys/mman.h>
#include <unistd.h>
#endif
#include "runtime/object.h"
#include "runtime/hash.h"
#include "runtime/io.h"
#include "runtime/thread.h"
#include "util/name.h"
#include "paperlean/fast_import.h"
#include "paperlean/side_file.h"
#include "paperlean/olean_pack.h"

/*
The imported states of simp sets (`Lean.Meta.mkSimpExt`) and of `Lean.Meta.instanceExtension`, that
is, the fold of `ScopedEnvExtension.addImportedFn` over their global entries, built by replaying the
fold's insertions on compact models of the data structures and allocating the resulting objects once
at the end.

The models follow the code they replace exactly (`Lean/Data/PersistentHashMap.lean`,
`Lean/Meta/DiscrTree/Basic.lean`, `SimpTheorems.addSimpEntry`, `addInstanceEntry`), including the
order of keys in collision nodes and of values in trie leaves, which values replace equal ones, and
the capacity of every array (from how the array was created and how many elements were pushed).
Object identity is upstream's too: every key, value and other object is the one the fold would
hold, e.g. a DiscrTree node holds the key object of the last entry inserted through it.

Compared objects are interned: `==` of the respective `BEq` instance becomes equality of class ids,
and the order of trie children (`Key.lt`, a total order whose equivalence is `==`) an order of known
nodes. An import image (`LEAN_IMPORT_IMAGE`, written by `writeImportImage` for an olean pack)
holds the interned form of every entry of the pack, so that replaying the entries of packed modules
calls no Lean function and reads no entry; other entries are interned when they are replayed.
*/

namespace lean {
extern "C" uint8 lean_paperlean_discr_tree_key_lt(obj_arg a, obj_arg b);
extern "C" uint64 lean_paperlean_discr_tree_key_hash(obj_arg k);
extern "C" uint8 lean_paperlean_discr_tree_key_beq(obj_arg a, obj_arg b);
extern "C" obj_res lean_paperlean_discr_tree_create_nodes_probe(obj_arg k, obj_arg v);
extern "C" obj_res lean_paperlean_simp_theorem_keys(obj_arg t);
extern "C" uint8 lean_paperlean_simp_theorem_post(obj_arg t);
extern "C" obj_res lean_paperlean_simp_theorem_proof(obj_arg t);
extern "C" obj_res lean_paperlean_simp_theorem_origin(obj_arg t);
extern "C" uint64 lean_paperlean_origin_hash(obj_arg o);
extern "C" uint8 lean_paperlean_origin_kind(obj_arg o);
extern "C" obj_res lean_paperlean_origin_key(obj_arg o);
extern "C" obj_res lean_paperlean_origin_converse(obj_arg o);
extern "C" obj_res lean_paperlean_origin_mk_eqn(obj_arg n);
extern "C" obj_res lean_paperlean_instance_entry_keys(obj_arg e);
extern "C" obj_res lean_paperlean_instance_entry_val(obj_arg e);
extern "C" obj_res lean_paperlean_instance_entry_global_name(obj_arg e);
extern "C" uint8 lean_expr_eqv(b_obj_arg a, b_obj_arg b);


namespace {
// The exported Lean functions take their arguments owned.
inline uint8 key_lt(object * a, object * b) { lean_inc(a); lean_inc(b); return lean_paperlean_discr_tree_key_lt(a, b); }
inline uint64 key_hash(object * k) { lean_inc(k); return lean_paperlean_discr_tree_key_hash(k); }
inline uint8 key_beq(object * a, object * b) { lean_inc(a); lean_inc(b); return lean_paperlean_discr_tree_key_beq(a, b); }
inline uint64 origin_hash(object * o) { lean_inc(o); return lean_paperlean_origin_hash(o); }
inline uint8 origin_kind(object * o) { lean_inc(o); return lean_paperlean_origin_kind(o); }
template<class F> inline object * get(F f, object * o) { lean_inc(o); return f(o); }

// The kinds of extensions whose state is replayed (`Lean.PaperLean.ImportState`).
enum class state_kind : uint8 { simp = 0, instances = 1 };

// =======================================
// Arrays

// The capacity of an array of `size` elements and capacity `cap` after `Array.push`, if the array
// is exclusive or else (the persistent `#[]`) copied (`lean_array_push`).
size_t push_capacity(size_t size, size_t cap, bool exclusive) {
    if (exclusive) return cap > size ? cap : (cap + 1) * 2;
    return cap < 2 * size + 1 ? (cap + 1) * 2 : cap;
}

object * alloc_array(size_t size, size_t cap) { return lean_alloc_array(size, cap); }

// =======================================
// `PersistentHashMap`

constexpr unsigned g_shift = 5;
constexpr size_t g_branching = 32;
constexpr size_t g_max_depth = 7;
constexpr size_t g_max_collisions = 4;

// A key in a map: its class under the map's `==`, its `hash`, and the object the map holds.
struct hkey { uint32 id; uint64 hash; object * obj; };

// A map built from `initial`, an empty map whose root is a shared entries node: the fold's first
// update copies its entries array. Values are opaque `uint64`s that `materialize` turns into objects.
class hmap {
    // A slot of an entries node, or a reference to a node: 0 = `Entry.null`, else `i << 2 | tag` with
    // tag 1 = `Entry.entry` of the pair `m_pairs[i]`, 2 = the entries node `m_entries[i]`, 3 = the
    // collision node `m_collisions[i]`.
    using slot = uint32;
    struct pair { hkey key; uint64 val; };
    struct entries_node { slot slots[g_branching] = {}; };
    // `Node.collision keys vals`: the pairs in their order, and the capacity of both arrays, which
    // are always pushed and erased together
    struct collision_node {
        uint32 size = 0, cap = 0;
        bool big = false;                  // whether the pairs are in `m_big`
        uint32 m_small[g_max_collisions];
        std::vector<uint32> m_big;         // used once there are more pairs (at `maxDepth`)
        uint32 * pairs() { return big ? m_big.data() : m_small; }
        uint32 const * pairs() const { return big ? m_big.data() : m_small; }
        void push(uint32 p) {
            cap = static_cast<uint32>(push_capacity(size, cap, true));
            if (!big && size == g_max_collisions) { m_big.assign(m_small, m_small + size); big = true; }
            if (big) m_big.push_back(p); else m_small[size] = p;
            size++;
        }
        // `Array.eraseIdx`: elements move down, the capacity stays.
        void erase(uint32 i) {
            uint32 * ps = pairs();
            for (uint32 j = i; j + 1 < size; j++) ps[j] = ps[j + 1];
            size--;
            if (big) m_big.pop_back();
        }
    };
    // deques: references stay valid while nodes are added
    std::deque<pair> m_pairs;
    std::deque<entries_node> m_entries;
    std::deque<collision_node> m_collisions;
    int64 m_root = -1;    // the root's entries node, -1: still `initial`
    object * m_initial;

    static slot tag(size_t i, unsigned t) { lean_assert(i < (1u << 30)); return static_cast<slot>(i << 2) | t; }
    uint32 new_pair(hkey const & k, uint64 v) { m_pairs.push_back(pair { k, v }); return static_cast<uint32>(m_pairs.size() - 1); }
    slot new_entries() { m_entries.emplace_back(); return tag(m_entries.size() - 1, 2); }
    slot new_collision(uint32 p1, uint32 p2) {
        // `mkCollisionNode`: `Array.mkEmpty maxCollisions` and two pushes
        m_collisions.emplace_back();
        collision_node & c = m_collisions.back();
        c.cap = g_max_collisions;
        c.m_small[0] = p1;
        c.m_small[1] = p2;
        c.size = 2;
        return tag(m_collisions.size() - 1, 3);
    }
    slot root() { if (m_root < 0) m_root = static_cast<int64>(new_entries() >> 2); return tag(m_root, 2); }
    bool same(uint32 p, hkey const & k) const { return m_pairs[p].key.id == k.id; }

    // `insertAux` on the node `r` with the pair `p`; the node that replaces `r`
    slot insert_aux(slot r, size_t h, size_t depth, uint32 p) {
        hkey const & k = m_pairs[p].key;
        if ((r & 3) == 3) {
            // `insertAtCollisionNode`
            collision_node & c = m_collisions[r >> 2];
            bool found = false;
            for (uint32 i = 0; i < c.size && !found; i++)
                if (same(c.pairs()[i], k)) { c.pairs()[i] = p; found = true; }
            if (!found) c.push(p);
            if (depth >= g_max_depth || c.size < g_max_collisions) return r;
            // split into a fresh entries node, inserting the pairs in their order
            slot e = new_entries();
            for (uint32 i = 0; i < c.size; i++) {
                uint32 q = c.pairs()[i];
                size_t hi = static_cast<size_t>(m_pairs[q].key.hash) >> (g_shift * (depth - 1));
                e = insert_aux(e, hi, depth, q);
            }
            return e;
        }
        slot & s = m_entries[r >> 2].slots[h & (g_branching - 1)];
        if (s == 0) s = tag(p, 1);
        else if ((s & 3) != 1) s = insert_aux(s, h >> g_shift, depth + 1, p);
        else if (same(s >> 2, k)) s = tag(p, 1);
        else s = new_collision(s >> 2, p);
        return r;
    }

    // `isUnaryNode`
    bool unary(slot r, uint32 & p) const {
        if ((r & 3) == 3) {
            collision_node const & c = m_collisions[r >> 2];
            if (c.size != 1) return false;
            p = c.pairs()[0];
            return true;
        }
        bool found = false;
        for (slot s : m_entries[r >> 2].slots) {
            if ((s & 3) >= 2) return false;
            if ((s & 3) == 1) {
                if (found) return false;
                found = true;
                p = s >> 2;
            }
        }
        return found;
    }

    // `alterAux` with a function that maps every value to `some v`
    slot upsert_aux(slot r, size_t h, size_t depth, uint32 p) {
        hkey const & k = m_pairs[p].key;
        if ((r & 3) == 3) {
            collision_node & c = m_collisions[r >> 2];
            for (uint32 i = 0; i < c.size; i++) {
                if (same(c.pairs()[i], k)) {
                    // erased and pushed again, so it moves to the end
                    c.erase(i);
                    c.push(p);
                    return r;
                }
            }
            return insert_aux(r, h, depth, p);
        }
        slot & s = m_entries[r >> 2].slots[h & (g_branching - 1)];
        if (s == 0) {
            s = tag(p, 1);
        } else if ((s & 3) == 1) {
            s = same(s >> 2, k) ? tag(p, 1) : new_collision(s >> 2, p);
        } else {
            s = upsert_aux(s, h >> g_shift, depth + 1, p);
            uint32 u;
            if (unary(s, u)) s = tag(u, 1);
        }
        return r;
    }

    // `eraseAux`
    void erase_aux(slot r, size_t h, hkey const & k) {
        if ((r & 3) == 3) {
            collision_node & c = m_collisions[r >> 2];
            for (uint32 i = 0; i < c.size; i++)
                if (same(c.pairs()[i], k)) { c.erase(i); return; }
            return;
        }
        slot & s = m_entries[r >> 2].slots[h & (g_branching - 1)];
        if (s == 0) return;
        if ((s & 3) == 1) {
            if (same(s >> 2, k)) s = 0;
            return;
        }
        erase_aux(s, h >> g_shift, k);
        uint32 u;
        if (unary(s, u)) s = tag(u, 1);
    }

    // The pair of `k`, if any.
    bool find_pair(hkey const & k, uint32 & p) const {
        if (m_root < 0) return false;
        slot r = tag(m_root, 2);
        size_t h = static_cast<size_t>(k.hash);
        while (true) {
            if ((r & 3) == 3) {
                collision_node const & c = m_collisions[r >> 2];
                for (uint32 i = 0; i < c.size; i++)
                    if (same(c.pairs()[i], k)) { p = c.pairs()[i]; return true; }
                return false;
            }
            slot s = m_entries[r >> 2].slots[h & (g_branching - 1)];
            if (s == 0) return false;
            if ((s & 3) == 1) {
                if (!same(s >> 2, k)) return false;
                p = s >> 2;
                return true;
            }
            r = s;
            h >>= g_shift;
        }
    }

    template<class F> object * materialize_node(slot r, F const & value) const {
        if ((r & 3) == 3) {
            collision_node const & c = m_collisions[r >> 2];
            object * ks = alloc_array(c.size, c.cap);
            object * vs = alloc_array(c.size, c.cap);
            for (uint32 i = 0; i < c.size; i++) {
                pair const & q = m_pairs[c.pairs()[i]];
                lean_inc(q.key.obj);
                lean_array_set_core(ks, i, q.key.obj);
                lean_array_set_core(vs, i, value(q.val));
            }
            object * res = lean_alloc_ctor(1, 2, 0);
            lean_ctor_set(res, 0, ks);
            lean_ctor_set(res, 1, vs);
            return res;
        }
        entries_node const & n = m_entries[r >> 2];
        object * es = alloc_array(g_branching, g_branching);
        for (size_t j = 0; j < g_branching; j++) {
            slot s = n.slots[j];
            object * e;
            if (s == 0) {
                e = lean_box(2);
            } else if ((s & 3) == 1) {
                pair const & q = m_pairs[s >> 2];
                e = lean_alloc_ctor(0, 2, 0);
                lean_inc(q.key.obj);
                lean_ctor_set(e, 0, q.key.obj);
                lean_ctor_set(e, 1, value(q.val));
            } else {
                e = lean_alloc_ctor(1, 1, 0);
                lean_ctor_set(e, 0, materialize_node(s, value));
            }
            lean_array_set_core(es, j, e);
        }
        object * res = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(res, 0, es);
        return res;
    }

public:
    explicit hmap(object * initial) : m_initial(initial) {}
    // The root stays an entries node: only collision nodes are replaced (when split), and they
    // are never roots.
    void insert(hkey const & k, uint64 v) { insert_aux(root(), static_cast<size_t>(k.hash), 1, new_pair(k, v)); }
    void upsert(hkey const & k, uint64 v) { upsert_aux(root(), static_cast<size_t>(k.hash), 1, new_pair(k, v)); }
    void erase(hkey const & k) {
        // the shared empty root: nothing to erase and nothing written
        if (m_root < 0) return;
        erase_aux(tag(m_root, 2), static_cast<size_t>(k.hash), k);
    }
    bool contains(hkey const & k) const { uint32 p; return find_pair(k, p); }
    // The value of `k`, if any.
    bool find(hkey const & k, uint64 & v) const {
        uint32 p;
        if (!find_pair(k, p)) return false;
        v = m_pairs[p].val;
        return true;
    }
    // The map (a `PersistentHashMap` is represented by its root node).
    template<class F> object * materialize(F const & value) const {
        if (m_root < 0) { lean_inc(m_initial); return m_initial; }
        return materialize_node(tag(m_root, 2), value);
    }
};

// Whether `m` is an empty map whose root the fold would copy on its first update.
bool is_empty_map(object * m) {
    if (lean_is_scalar(m) || lean_ptr_tag(m) != 0 || lean_ctor_num_objs(m) != 1 || !lean_is_persistent(m)) return false;
    object * es = lean_ctor_get(m, 0);
    if (lean_is_scalar(es) || lean_ptr_tag(es) != LeanArray || lean_array_size(es) != g_branching ||
        lean_array_capacity(es) != g_branching || !lean_is_persistent(es))
        return false;
    for (size_t j = 0; j < g_branching; j++)
        if (lean_array_get_core(es, j) != lean_box(2)) return false;
    return true;
}


// =======================================
// `DiscrTree`

// The empty arrays `createNodes` starts nodes with, persistent arrays shared by all nodes: the
// values of an inner node and the children of a leaf (two distinct `#[]` constants).
object * g_trie_no_values = nullptr;
object * g_trie_no_children = nullptr;
std::once_flag g_trie_empty_once;

bool init_trie_empty() {
    std::call_once(g_trie_empty_once, [] {
        // `createNodes #[k, k] v 1 = .node #[] #[(k, .node #[v] #[])]` (`Key.star` and `0` are scalars)
        object * probe = lean_paperlean_discr_tree_create_nodes_probe(lean_box(0), lean_box(0));
        object * vs = lean_ctor_get(probe, 0);
        object * cs = lean_ctor_get(probe, 1);
        object * leaf = lean_ctor_get(lean_array_get_core(cs, 0), 1);
        object * leaf_cs = lean_ctor_get(leaf, 1);
        auto empty = [](object * a) { return lean_is_persistent(a) && lean_array_size(a) == 0 && lean_array_capacity(a) == 0; };
        if (empty(vs) && empty(leaf_cs) && lean_array_capacity(cs) == 1 && lean_array_capacity(lean_ctor_get(leaf, 0)) == 1) {
            g_trie_no_values = vs;
            g_trie_no_children = leaf_cs;
        }
        lean_dec(probe);
    });
    return g_trie_no_values != nullptr;
}

// =======================================
// Import images
//
// An image refers to the objects of one olean pack by their addresses. Per extension it holds the
// classes of the names and origins of all entries, the known trie nodes, and per entries array of a
// packed part the interned entries. All tables are checked when an extension's state is first
// built: its checksum, and that every index and object lies in range.

constexpr char g_image_kind[] = "import-image";
constexpr uint32 g_image_format = 1;
constexpr uint32 g_none = UINT32_MAX;

struct image_range { uint64 off, num; };
struct image_tree { image_range nodes, children, classes, roots; };
struct image_ext {
    image_range name;           // the extension's name, as `ext_name_key` bytes
    uint32 kind, unused;
    image_tree trees[2];        // simp sets: `pre`, `post`; instances: `discrTree`
    image_range names;          // `image_name`
    image_range names_index;    // open addressing by hash: class + 1, 0 = empty
    image_range origins;        // `image_origin`
    image_range origins_index;  // open addressing by key: class + 1, 0 = empty
    image_range arrays;         // open addressing by address: `image_array`, address 0 = empty
    image_range entries;        // `image_entry`
    image_range steps;          // `image_step`
    uint64 checksum;            // `side_file_checksum` of the bytes of all ranges in this order
};
struct image_header {
    side_file_header common;
    uint32 format, num_exts;
    uint64 pack_checksum, pack_base, pack_size;   // the pack the object addresses are in
    uint64 size;
    uint64 exts_off;
};
struct image_node { uint64 key; uint32 first_child, num_children, first_class, num_classes; };
struct image_root { uint64 hash; uint32 node, unused; };      // sorted by hash
struct image_name { uint64 hash, rep; };
struct image_origin { uint64 key, hash; };                     // key: name class << 2 | origin kind
struct image_array { uint64 addr; uint32 first, count; };
struct image_step { uint64 key; uint32 node, unused; };
// kinds: 0 `.thm`, 1 `.toUnfold`, 2 `.toUnfoldThms`, 3 instance, 4 scoped (not replayed)
struct image_entry {
    uint8 kind, tree, okind, unused;
    uint32 first_step, num_steps, vclass;
    uint64 h0;                  // the hash of the first key
    uint32 cls, converse, decl, unused2;
    uint64 value, obj;
};
static_assert(sizeof(image_entry) == 56, "image_entry is packed");

template<class T> T const * range_ptr(char const * base, image_range r) { return reinterpret_cast<T const *>(base + r.off); }
inline size_t slot_of(uint64 h, size_t size) { return (h * 0x9e3779b97f4a7c15ull >> 20) & (size - 1); }

// =======================================
// Classes

// Name classes (`Name.beq`): those of an image, then others found by hash and `Name.beq`.
class name_classes {
    image_name const * m_img = nullptr;
    size_t m_img_num = 0;
    uint32 const * m_index = nullptr;
    size_t m_index_size = 0;
    std::vector<image_name> m_dyn;
    std::unordered_map<uint64, std::vector<uint32>> m_dyn_by_hash;
public:
    void load(image_name const * img, size_t n, uint32 const * index, size_t index_size) {
        m_img = img; m_img_num = n; m_index = index; m_index_size = index_size;
    }
    size_t size() const { return m_img_num + m_dyn.size(); }
    uint64 hash(uint32 c) const { return c < m_img_num ? m_img[c].hash : m_dyn[c - m_img_num].hash; }
    object * rep(uint32 c) const {
        return reinterpret_cast<object *>(c < m_img_num ? m_img[c].rep : m_dyn[c - m_img_num].rep);
    }
    uint32 get(object * n) {
        uint64 h = lean_name_hash(n);
        if (m_index_size) {
            for (size_t i = slot_of(h, m_index_size); m_index[i] != 0; i = (i + 1) & (m_index_size - 1)) {
                uint32 c = m_index[i] - 1;
                if (m_img[c].hash == h && lean_name_eq(reinterpret_cast<object *>(m_img[c].rep), n)) return c;
            }
        }
        std::vector<uint32> & cs = m_dyn_by_hash[h];
        for (uint32 c : cs)
            if (lean_name_eq(rep(c), n)) return c;
        uint32 c = static_cast<uint32>(size());
        m_dyn.push_back(image_name { h, reinterpret_cast<uint64>(n) });
        cs.push_back(c);
        return c;
    }
};

// Classes of `==` on `Origin`: equal origins have the same kind (`origin_kind`) and equal keys.
class origin_classes {
    image_origin const * m_img = nullptr;
    size_t m_img_num = 0;
    uint32 const * m_index = nullptr;
    size_t m_index_size = 0;
    std::vector<image_origin> m_dyn;
    std::unordered_map<uint64, uint32> m_dyn_ids;
public:
    void load(image_origin const * img, size_t n, uint32 const * index, size_t index_size) {
        m_img = img; m_img_num = n; m_index = index; m_index_size = index_size;
    }
    static uint64 key_of(uint8 kind, uint32 name_class) { return static_cast<uint64>(name_class) << 2 | kind; }
    size_t size() const { return m_img_num + m_dyn.size(); }
    uint64 hash(uint32 c) const { return c < m_img_num ? m_img[c].hash : m_dyn[c - m_img_num].hash; }
    uint64 key(uint32 c) const { return c < m_img_num ? m_img[c].key : m_dyn[c - m_img_num].key; }
    uint32 find(uint64 key) const {
        if (m_index_size) {
            for (size_t i = slot_of(key, m_index_size); m_index[i] != 0; i = (i + 1) & (m_index_size - 1))
                if (m_img[m_index[i] - 1].key == key) return m_index[i] - 1;
        }
        auto it = m_dyn_ids.find(key);
        return it == m_dyn_ids.end() ? g_none : it->second;
    }
    // `hash` computes the class's hash if the class is new.
    template<class F> uint32 get(uint64 key, F const & hash) {
        uint32 c = find(key);
        if (c != g_none) return c;
        c = static_cast<uint32>(size());
        m_dyn.push_back(image_origin { key, hash() });
        m_dyn_ids.emplace(key, c);
        return c;
    }
};

// The known nodes of a trie: per node a key of the edge into it, its children in `Key.lt` order and,
// for nodes where values end, a representative of each class of `==`-equal values (what `==`
// compares: a theorem's proof or an instance's value). The fold's trie consists of some of them.
// Root nodes are found by their key's hash and `==`, children by `Key.lt`, whose equivalence is `==`.
class trie_universe {
    image_node const * m_img = nullptr;
    uint32 m_img_num = 0;
    uint32 const * m_img_children = nullptr;
    uint64 const * m_img_classes = nullptr;
    image_root const * m_img_roots = nullptr;
    size_t m_img_num_roots = 0;
    struct node {
        object * key;
        std::vector<uint32> children;
        std::vector<object *> classes;
    };
    std::deque<node> m_dyn;
    std::unordered_map<uint32, std::vector<uint32>> m_img_children_ext;   // image nodes with new children
    std::vector<bool> m_has_children_ext;
    std::unordered_map<uint32, std::vector<object *>> m_img_classes_ext;  // and their new classes
    std::unordered_map<uint64, std::vector<uint32>> m_dyn_roots;
    uint32 add(object * key) {
        m_dyn.push_back(node { key, {}, {} });
        return static_cast<uint32>(m_img_num + m_dyn.size() - 1);
    }
public:
    struct span {
        uint32 const * b, * e;
        uint32 const * begin() const { return b; }
        uint32 const * end() const { return e; }
        size_t size() const { return e - b; }
        uint32 operator[](size_t i) const { return b[i]; }
    };
    void load(image_node const * nodes, uint32 num, uint32 const * children, uint64 const * classes,
              image_root const * roots, size_t num_roots) {
        m_img = nodes; m_img_num = num; m_img_children = children; m_img_classes = classes;
        m_img_roots = roots; m_img_num_roots = num_roots;
    }
    size_t size() const { return m_img_num + m_dyn.size(); }
    object * key(uint32 n) const {
        return n < m_img_num ? reinterpret_cast<object *>(m_img[n].key) : m_dyn[n - m_img_num].key;
    }
    span children(uint32 n) const {
        if (n >= m_img_num) {
            std::vector<uint32> const & cs = m_dyn[n - m_img_num].children;
            return span { cs.data(), cs.data() + cs.size() };
        }
        if (!m_has_children_ext.empty() && m_has_children_ext[n]) {
            std::vector<uint32> const & cs = m_img_children_ext.find(n)->second;
            return span { cs.data(), cs.data() + cs.size() };
        }
        uint32 const * b = m_img_children + m_img[n].first_child;
        return span { b, b + m_img[n].num_children };
    }
    uint32 root(object * k, uint64 h) {
        image_root const * it = std::lower_bound(m_img_roots, m_img_roots + m_img_num_roots, h,
            [](image_root const & r, uint64 x) { return r.hash < x; });
        for (; it != m_img_roots + m_img_num_roots && it->hash == h; ++it)
            if (key(it->node) == k || key_beq(key(it->node), k)) return it->node;
        std::vector<uint32> & ns = m_dyn_roots[h];
        for (uint32 n : ns)
            if (key(n) == k || key_beq(key(n), k)) return n;
        uint32 n = add(k);
        ns.push_back(n);
        return n;
    }
    uint32 child(uint32 n, object * k) {
        span cs = children(n);
        size_t lo = 0, hi = cs.size();
        while (lo < hi) {
            size_t mid = (lo + hi) / 2;
            if (key_lt(key(cs[mid]), k)) lo = mid + 1; else hi = mid;
        }
        if (lo < cs.size() && (key(cs[lo]) == k || !key_lt(k, key(cs[lo])))) return cs[lo];
        uint32 c = add(k);
        if (n >= m_img_num) {
            std::vector<uint32> & v = m_dyn[n - m_img_num].children;
            v.insert(v.begin() + lo, c);
        } else {
            auto it = m_img_children_ext.find(n);
            if (it == m_img_children_ext.end()) {
                it = m_img_children_ext.emplace(n, std::vector<uint32>(cs.begin(), cs.end())).first;
                if (m_has_children_ext.empty()) m_has_children_ext.resize(m_img_num, false);
                m_has_children_ext[n] = true;
            }
            it->second.insert(it->second.begin() + lo, c);
        }
        return c;
    }
    uint32 value_class(uint32 n, object * cmp) {
        uint32 base = 0;
        std::vector<object *> * ext;
        if (n < m_img_num) {
            image_node const & in = m_img[n];
            for (uint32 i = 0; i < in.num_classes; i++) {
                object * r = reinterpret_cast<object *>(m_img_classes[in.first_class + i]);
                if (r == cmp || lean_expr_eqv(r, cmp)) return i;
            }
            base = in.num_classes;
            ext = &m_img_classes_ext[n];
        } else {
            ext = &m_dyn[n - m_img_num].classes;
        }
        for (size_t i = 0; i < ext->size(); i++)
            if ((*ext)[i] == cmp || lean_expr_eqv((*ext)[i], cmp)) return base + static_cast<uint32>(i);
        ext->push_back(cmp);
        return base + static_cast<uint32>(ext->size() - 1);
    }
    // for writing an image of a universe without image part
    std::vector<object *> const & dyn_classes(uint32 n) const { return m_dyn[n].classes; }
    std::vector<std::pair<uint64, uint32>> dyn_roots() const {
        std::vector<std::pair<uint64, uint32>> r;
        for (auto const & p : m_dyn_roots) for (uint32 n : p.second) r.push_back({ p.first, n });
        std::sort(r.begin(), r.end());
        return r;
    }
};

// =======================================
// Entries

// One step of an entry's keys: the node of the prefix and the entry's key object.
struct entry_step { object * key; uint32 node; };

// An entry in interned form (`image_entry` with the steps and objects at hand).
struct entry_desc {
    uint8 kind = 4, tree = 0, okind = 0;
    entry_step const * steps = nullptr;
    uint32 num_steps = 0, vclass = 0;
    uint64 h0 = 0;
    uint32 cls = g_none, converse = g_none, decl = g_none;
    object * value = nullptr, * obj = nullptr;
};

// The capacity of an array that the fold builds from `#[]` (shared, `start == 0`) or from a fresh
// array of `start` elements and capacity `start`, by pushes up to `size` elements.
size_t pushed_capacity(size_t start, size_t size) {
    size_t cap = start;
    bool exclusive = start > 0;
    for (size_t n = start; n < size; n++) {
        cap = push_capacity(n, cap, exclusive);
        exclusive = true;
    }
    return cap;
}

// `n` zero-initialized elements of a trivial type; large blocks are mapped, so that the pages that
// are never written are never touched.
template<class T> class zeroed_array {
    T * m_data = nullptr;
    size_t m_size = 0;
    bool m_mapped = false;
    void release() {
        if (!m_data) return;
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
        if (m_mapped) { munmap(m_data, m_size * sizeof(T)); return; }
#endif
        free(m_data);
    }
public:
    zeroed_array() {}
    zeroed_array(zeroed_array const &) = delete;
    zeroed_array & operator=(zeroed_array const &) = delete;
    ~zeroed_array() { release(); }
    size_t size() const { return m_size; }
    T & operator[](size_t i) { return m_data[i]; }
    T const & operator[](size_t i) const { return m_data[i]; }
    // Grows to at least `n` elements, keeping the existing ones.
    void grow(size_t n) {
        if (n <= m_size) return;
        n = std::max(n, 2 * m_size);
        T * data = nullptr;
        bool mapped = false;
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
        if (n * sizeof(T) >= (1u << 20)) {
            void * m = mmap(nullptr, n * sizeof(T), PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
            if (m != MAP_FAILED) { data = static_cast<T *>(m); mapped = true; }
        }
#endif
        if (!data) data = static_cast<T *>(calloc(n, sizeof(T)));
        if (!data) throw std::bad_alloc();
        if (m_size) memcpy(static_cast<void *>(data), m_data, m_size * sizeof(T));
        release();
        m_data = data;
        m_size = n;
        m_mapped = mapped;
    }
};

// The fold's trie, as nodes of a `trie_universe`, and its root map.
class trie_builder {
    // A node of the universe in the fold's trie; all zero if the fold did not create it.
    struct tstate {
        object * key;          // the key of the last entry inserted through the node
        uint32 vals;           // 1 + the index of its first value in `m_vals`, 0 = none
        uint32 nvals : 31;     // the number of values
        // whether `createNodes` made it a leaf, with `#[v]` and `#[]` children, rather than an inner
        // node with `#[]` and one child
        uint32 leaf : 1;
    };
    static_assert(sizeof(tstate) == 16, "tstate is small");
    // the values of a node in their order, as a list
    struct vrec { object * value; uint32 cls; uint32 next; };
    trie_universe & m_universe;
    zeroed_array<tstate> m_states;      // by node
    std::vector<vrec> m_vals;
    std::vector<uint32> m_children;     // scratch for `materialize_node`
    hmap m_root;

    bool created(uint32 n) const { return m_states[n].key != nullptr; }
    // `insertVal` of `v` of class `cls`: an equal value is replaced in place, a new one pushed
    void insert_val(tstate & t, object * v, uint32 cls) {
        uint32 last = 0;
        for (uint32 l = t.vals; l; l = m_vals[l - 1].next) {
            if (m_vals[l - 1].cls == cls) { m_vals[l - 1].value = v; return; }
            last = l;
        }
        m_vals.push_back(vrec { v, cls, 0 });
        uint32 l = static_cast<uint32>(m_vals.size());
        if (last) m_vals[last - 1].next = l;
        else t.vals = l;
        t.nvals++;
    }
    // `createNodes keys v i`, for the node `steps[i].node` of the prefix of length `i + 1`.
    void create(entry_desc const & d, size_t i) {
        for (;; i++) {
            tstate & t = m_states[d.steps[i].node];
            t.key = d.steps[i].key;
            if (i + 1 == d.num_steps) {
                t.leaf = 1;
                insert_val(t, d.value, d.vclass);
                return;
            }
        }
    }
    // `insertAux keys v i`; the merge with an existing child takes the entry's key
    void insert_aux(entry_desc const & d, size_t i) {
        for (;; i++) {
            tstate & t = m_states[d.steps[i].node];
            t.key = d.steps[i].key;
            if (i + 1 == d.num_steps) {
                insert_val(t, d.value, d.vclass);
                return;
            }
            if (!created(d.steps[i + 1].node)) {
                create(d, i + 1);
                return;
            }
        }
    }

    object * materialize_node(uint32 n) {
        tstate const & t = m_states[n];
        object * vs;
        if (t.nvals == 0) {
            vs = g_trie_no_values;
        } else {
            vs = alloc_array(t.nvals, pushed_capacity(t.leaf ? 1 : 0, t.nvals));
            size_t k = 0;
            for (uint32 l = t.vals; l; l = m_vals[l - 1].next) {
                object * v = m_vals[l - 1].value;
                lean_inc(v);
                lean_array_set_core(vs, k++, v);
            }
        }
        size_t base = m_children.size();
        for (uint32 c : m_universe.children(n))
            if (created(c)) m_children.push_back(c);
        size_t num = m_children.size() - base;
        object * cs;
        if (num == 0) {
            cs = g_trie_no_children;
        } else {
            cs = alloc_array(num, pushed_capacity(t.leaf ? 0 : 1, num));
            for (size_t k = 0; k < num; k++) {
                uint32 c = m_children[base + k];
                object * pair = lean_alloc_ctor(0, 2, 0);
                lean_inc(m_states[c].key);
                lean_ctor_set(pair, 0, m_states[c].key);
                lean_ctor_set(pair, 1, materialize_node(c));
                lean_array_set_core(cs, k, pair);
            }
        }
        m_children.resize(base);
        object * r = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(r, 0, vs);
        lean_ctor_set(r, 1, cs);
        return r;
    }

public:
    trie_builder(trie_universe & universe, object * initial_root) : m_universe(universe), m_root(initial_root) {}
    // `insertKeyValue d keys v`
    void insert(entry_desc const & d) {
        // the entry's nodes are in the universe already
        m_states.grow(m_universe.size());
        uint32 r = d.steps[0].node;
        // the root map's `alter`, which takes the entry's key
        m_root.upsert(hkey { r, d.h0, d.steps[0].key }, r);
        if (created(r)) insert_aux(d, 0);
        else create(d, 0);
    }
    object * materialize() {
        return m_root.materialize([&](uint64 r) { return materialize_node(static_cast<uint32>(r)); });
    }
};

// The interning of one extension's entries, possibly starting from an image's.
struct interning {
    state_kind kind;
    trie_universe trees[2];
    name_classes names;
    origin_classes origins;
    std::vector<object *> owned;           // objects obtained from Lean, released at the end
    std::vector<entry_step> steps;         // of the entry described last
    explicit interning(state_kind k) : kind(k) {}
    ~interning() { for (object * o : owned) lean_dec(o); }
    object * own(object * o) { owned.push_back(o); return o; }

    uint32 origin_class(object * o, uint8 & okind) {
        okind = origin_kind(o);
        uint32 nc = names.get(own(get(lean_paperlean_origin_key, o)));
        return origins.get(origin_classes::key_of(okind, nc), [&] { return origin_hash(o); });
    }
    // The path of `keys` in tree `t`; false if `keys` is empty (the fold panics).
    bool path(object * keys, unsigned t, entry_desc & d) {
        size_t n = lean_array_size(keys);
        if (n == 0) return false;
        steps.resize(n);
        object * k0 = lean_array_get_core(keys, 0);
        d.h0 = key_hash(k0);
        steps[0] = entry_step { k0, trees[t].root(k0, d.h0) };
        for (size_t i = 1; i < n; i++) {
            object * k = lean_array_get_core(keys, i);
            steps[i] = entry_step { k, trees[t].child(steps[i - 1].node, k) };
        }
        d.steps = steps.data();
        d.num_steps = static_cast<uint32>(n);
        return true;
    }
    // `e`, an element of `Entry.global`, in interned form, calling the Lean functions; false if the
    // models do not cover it.
    bool describe(object * e, entry_desc & d) {
        d = entry_desc();
        if (kind == state_kind::instances) {
            d.kind = 3;
            object * val = own(get(lean_paperlean_instance_entry_val, e));
            object * name = own(get(lean_paperlean_instance_entry_global_name, e));
            if (!path(own(get(lean_paperlean_instance_entry_keys, e)), 0, d)) return false;
            d.vclass = trees[0].value_class(d.steps[d.num_steps - 1].node, val);
            d.value = e;
            if (!lean_is_scalar(name)) {
                d.obj = lean_ctor_get(name, 0);
                d.cls = names.get(d.obj);
            }
            return true;
        }
        switch (lean_ptr_tag(e)) {
        case 0: {   // `.thm t`
            object * t = lean_ctor_get(e, 0);
            d.kind = 0;
            lean_inc(t);
            d.tree = lean_paperlean_simp_theorem_post(t) ? 1 : 0;
            object * origin = own(get(lean_paperlean_simp_theorem_origin, t));
            object * proof = own(get(lean_paperlean_simp_theorem_proof, t));
            if (!path(own(get(lean_paperlean_simp_theorem_keys, t)), d.tree, d)) return false;
            d.vclass = trees[d.tree].value_class(d.steps[d.num_steps - 1].node, proof);
            d.value = t;
            d.obj = origin;
            d.cls = origin_class(origin, d.okind);
            if (d.okind != 0) {
                d.decl = static_cast<uint32>(origins.key(d.cls) >> 2);
                d.converse = origins.get(origin_classes::key_of(3 - d.okind, d.decl), [&] {
                    object * c = get(lean_paperlean_origin_converse, origin);
                    uint64 h = origin_hash(lean_ctor_get(c, 0));
                    lean_dec(c);
                    return h;
                });
            }
            return true;
        }
        case 1:     // `.toUnfold n`
            d.kind = 1;
            d.obj = lean_ctor_get(e, 0);
            d.cls = names.get(d.obj);
            return true;
        case 2:     // `.toUnfoldThms n thms`
            d.kind = 2;
            d.obj = lean_ctor_get(e, 0);
            d.cls = names.get(d.obj);
            d.value = lean_ctor_get(e, 1);
            return true;
        default:
            return false;
        }
    }
};

// =======================================
// Replaying

// `SimpTheorems`: `pre`, `post`, `lemmaNames`, `toUnfold`, `erased`, `toUnfoldThms`
constexpr unsigned g_simp_theorems_fields = 6;
// `Instances`: `discrTree`, `instanceNames`, `erased`
constexpr unsigned g_instances_fields = 3;

struct simp_replay {
    interning & in;
    trie_builder pre, post;
    hmap lemma_names, to_unfold, erased, to_unfold_thms;
    simp_replay(interning & i, object * init) :
        in(i), pre(i.trees[0], lean_ctor_get(init, 0)), post(i.trees[1], lean_ctor_get(init, 1)),
        lemma_names(lean_ctor_get(init, 2)), to_unfold(lean_ctor_get(init, 3)),
        erased(lean_ctor_get(init, 4)), to_unfold_thms(lean_ctor_get(init, 5)) {}

    hkey origin_key(uint32 c, object * o) const { return hkey { c, in.origins.hash(c), o }; }
    hkey name_key(uint32 c, object * n) const { return hkey { c, in.names.hash(c), n }; }

    // `SimpTheorems.eraseCore thmId`, where `thmId` is of class `c` and kind `okind`, with key class
    // `decl`
    void erase_core(object * thm_id, uint32 c, uint8 okind, uint32 decl) {
        erased.insert(origin_key(c, thm_id), 0);
        lemma_names.erase(origin_key(c, thm_id));
        if (okind != 0) {
            hkey dk = name_key(decl, nullptr);
            to_unfold.erase(dk);
            uint64 thms;
            if (to_unfold_thms.find(dk, thms)) {
                object * arr = reinterpret_cast<object *>(thms);
                for (size_t i = 0; i < lean_array_size(arr); i++) {
                    // `.decl thm true (inv := false)`
                    object * o = in.own(get(lean_paperlean_origin_mk_eqn, lean_array_get_core(arr, i)));
                    uint8 k;
                    uint32 oc = in.origin_class(o, k);
                    erase_core(o, oc, k, static_cast<uint32>(in.origins.key(oc) >> 2));
                }
            }
        }
    }
    void add(entry_desc const & d) {
        switch (d.kind) {
        case 0:
            // `eraseFwdIfBwd`: the converse is a new `Origin` object
            if (d.converse != g_none && lemma_names.contains(origin_key(d.converse, nullptr))) {
                object * c = in.own(get(lean_paperlean_origin_converse, d.obj));
                erase_core(lean_ctor_get(c, 0), d.converse, static_cast<uint8>(3 - d.okind), d.decl);
            }
            (d.tree ? post : pre).insert(d);
            lemma_names.insert(origin_key(d.cls, d.obj), 0);
            break;
        case 1:
            to_unfold.insert(name_key(d.cls, d.obj), 0);
            break;
        case 2:
            to_unfold_thms.insert(name_key(d.cls, d.obj), reinterpret_cast<uint64>(d.value));
            break;
        }
    }
    object * materialize() {
        auto unit = [](uint64) { return lean_box(0); };
        object * r = lean_alloc_ctor(0, g_simp_theorems_fields, 0);
        lean_ctor_set(r, 0, pre.materialize());
        lean_ctor_set(r, 1, post.materialize());
        lean_ctor_set(r, 2, lemma_names.materialize(unit));
        lean_ctor_set(r, 3, to_unfold.materialize(unit));
        lean_ctor_set(r, 4, erased.materialize(unit));
        lean_ctor_set(r, 5, to_unfold_thms.materialize([](uint64 v) {
            object * a = reinterpret_cast<object *>(v); lean_inc(a); return a; }));
        return r;
    }
};

struct instances_replay {
    interning & in;
    trie_builder tree;
    hmap instance_names;
    object * erased;
    instances_replay(interning & i, object * init) :
        in(i), tree(i.trees[0], lean_ctor_get(init, 0)), instance_names(lean_ctor_get(init, 1)),
        erased(lean_ctor_get(init, 2)) {}
    void add(entry_desc const & d) {
        tree.insert(d);
        // `erased.erase n` leaves `erased` the empty map of the initial state
        if (d.cls != g_none)
            instance_names.insert(hkey { d.cls, in.names.hash(d.cls), d.obj }, reinterpret_cast<uint64>(d.value));
    }
    object * materialize() {
        object * r = lean_alloc_ctor(0, g_instances_fields, 0);
        lean_ctor_set(r, 0, tree.materialize());
        lean_ctor_set(r, 1, instance_names.materialize([](uint64 v) {
            object * e = reinterpret_cast<object *>(v); lean_inc(e); return e; }));
        lean_inc(erased);
        lean_ctor_set(r, 2, erased);
        return r;
    }
};

// Whether `init` is the initial state the models start from: a structure of `n` empty maps.
bool valid_initial(object * init, unsigned n) {
    if (lean_is_scalar(init) || lean_ptr_tag(init) != 0 || lean_ctor_num_objs(init) != n) return false;
    for (unsigned i = 0; i < n; i++)
        if (!is_empty_map(lean_ctor_get(init, i))) return false;
    return true;
}

// =======================================
// Loading an image

// The header's checksum: of the header with this field zero, then of the extension records.
uint64 image_checksum(image_header hdr, char const * exts, size_t size) {
    hdr.common.checksum = 0;
    return side_file_checksum(exts, size, side_file_checksum(&hdr, sizeof(hdr)));
}

struct loaded_image {
    char const * begin = nullptr;
    image_header hdr;
    image_ext const * exts = nullptr;
    // per extension: 0 = not yet checked, 1 = usable, 2 = not
    std::unique_ptr<std::atomic<uint8>[]> state;
    std::unique_ptr<std::mutex[]> check_mutex;
};

std::once_flag g_image_once;
loaded_image * g_image = nullptr;

#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
void load_image() {
    char const * fname = getenv("LEAN_IMPORT_IMAGE");
    if (!fname || !*fname) return;
    auto warn = [&](char const * why) { fprintf(stderr, "warning: ignoring import image '%s': %s\n", fname, why); };
    int fd = open(fname, O_RDONLY);
    if (fd < 0) { warn(strerror(errno)); return; }
    struct stat st;
    image_header hdr;
    if (fstat(fd, &st) != 0 || static_cast<uint64>(st.st_size) < sizeof(hdr) ||
        pread(fd, &hdr, sizeof(hdr), 0) != static_cast<ssize_t>(sizeof(hdr))) {
        close(fd); warn("not a PaperLean side file"); return;
    }
    if (char const * why = check_side_file_header(hdr.common, g_image_kind, sizeof(image_header))) {
        close(fd); warn(why); return;
    }
    uint64_t pack_checksum, pack_base, pack_size;
    if (hdr.format != g_image_format) { close(fd); warn("written by a different version"); return; }
    if (hdr.size != static_cast<uint64>(st.st_size)) { close(fd); warn("its size differs from the recorded one"); return; }
    if (!first_pack_identity(pack_checksum, pack_base, pack_size) || pack_checksum != hdr.pack_checksum ||
        pack_base != hdr.pack_base || pack_size != hdr.pack_size) {
        close(fd); warn("it belongs to another olean pack than the first of LEAN_OLEAN_PACK"); return;
    }
    void * m = mmap(nullptr, hdr.size, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);
    if (m == MAP_FAILED) { warn(strerror(errno)); return; }
    if (hdr.exts_off % 8 != 0 || hdr.exts_off > hdr.size || hdr.num_exts > (hdr.size - hdr.exts_off) / sizeof(image_ext) ||
        image_checksum(hdr, static_cast<char const *>(m) + hdr.exts_off, hdr.num_exts * sizeof(image_ext)) != hdr.common.checksum) {
        munmap(m, hdr.size); warn("corrupt (checksum mismatch)"); return;
    }
    loaded_image * img = new loaded_image();
    img->begin = static_cast<char const *>(m);
    img->hdr = hdr;
    img->exts = reinterpret_cast<image_ext const *>(img->begin + hdr.exts_off);
    img->state.reset(new std::atomic<uint8>[hdr.num_exts]);
    img->check_mutex.reset(new std::mutex[hdr.num_exts]);
    for (uint32 i = 0; i < hdr.num_exts; i++) img->state[i].store(0);
    g_image = img;
}
#else
void load_image() {}
#endif

// Whether all tables of `x` are in range and consistent, and its checksum matches.
bool check_image_ext(loaded_image const & img, image_ext const & x) {
    uint64 size = img.hdr.size;
    image_range const * ranges[] = { &x.name, &x.trees[0].nodes, &x.trees[0].children, &x.trees[0].classes,
        &x.trees[0].roots, &x.trees[1].nodes, &x.trees[1].children, &x.trees[1].classes, &x.trees[1].roots,
        &x.names, &x.names_index, &x.origins, &x.origins_index, &x.arrays, &x.entries, &x.steps };
    size_t elems[] = { 1, sizeof(image_node), 4, 8, sizeof(image_root), sizeof(image_node), 4, 8, sizeof(image_root),
        sizeof(image_name), 4, sizeof(image_origin), 4, sizeof(image_array), sizeof(image_entry), sizeof(image_step) };
    uint64 h = side_file_checksum(nullptr, 0);
    for (size_t i = 0; i < sizeof(ranges) / sizeof(ranges[0]); i++) {
        image_range r = *ranges[i];
        if (r.off % 8 != 0 || r.off > size || r.num > (size - r.off) / elems[i] || r.num > UINT32_MAX) return false;
        h = side_file_checksum(img.begin + r.off, r.num * elems[i], h);
    }
    if (h != x.checksum || x.kind > 1) return false;
    auto pow2 = [](uint64 n) { return n == 0 || (n & (n - 1)) == 0; };
    if (!pow2(x.names_index.num) || !pow2(x.origins_index.num) || !pow2(x.arrays.num) || x.arrays.num == 0) return false;
    // all objects are in the pack the image describes, the first one
    auto obj_ok = [&](uint64 a) { return a % 8 == 0 && a >= img.hdr.pack_base && a - img.hdr.pack_base < img.hdr.pack_size; };
    // keys and names may also be scalars
    auto key_ok = [&](uint64 a) { return (a & 1) == 1 || obj_ok(a); };
    for (unsigned t = 0; t < 2; t++) {
        image_tree const & tr = x.trees[t];
        image_node const * nodes = range_ptr<image_node>(img.begin, tr.nodes);
        uint32 const * children = range_ptr<uint32>(img.begin, tr.children);
        for (uint64 i = 0; i < tr.nodes.num; i++) {
            image_node const & n = nodes[i];
            if (!key_ok(n.key) || n.first_child > tr.children.num || n.num_children > tr.children.num - n.first_child ||
                n.first_class > tr.classes.num || n.num_classes > tr.classes.num - n.first_class)
                return false;
        }
        // the children of a node come after it, so the trie has no cycles
        for (uint64 i = 0; i < tr.nodes.num; i++)
            for (uint32 j = 0; j < nodes[i].num_children; j++) {
                uint32 c = children[nodes[i].first_child + j];
                if (c >= tr.nodes.num || c <= i) return false;
            }
        uint64 const * classes = range_ptr<uint64>(img.begin, tr.classes);
        for (uint64 i = 0; i < tr.classes.num; i++) if (!obj_ok(classes[i])) return false;
        image_root const * roots = range_ptr<image_root>(img.begin, tr.roots);
        for (uint64 i = 0; i < tr.roots.num; i++)
            if (roots[i].node >= tr.nodes.num || (i > 0 && roots[i - 1].hash > roots[i].hash)) return false;
    }
    image_name const * names = range_ptr<image_name>(img.begin, x.names);
    for (uint64 i = 0; i < x.names.num; i++) if (!key_ok(names[i].rep)) return false;
    uint32 const * ni = range_ptr<uint32>(img.begin, x.names_index);
    bool empty_slot = x.names_index.num == 0;
    for (uint64 i = 0; i < x.names_index.num; i++) {
        if (ni[i] == 0) empty_slot = true;
        else if (ni[i] > x.names.num) return false;
    }
    uint32 const * oi = range_ptr<uint32>(img.begin, x.origins_index);
    bool empty_origin_slot = x.origins_index.num == 0;
    for (uint64 i = 0; i < x.origins_index.num; i++) {
        if (oi[i] == 0) empty_origin_slot = true;
        else if (oi[i] > x.origins.num) return false;
    }
    image_origin const * origins = range_ptr<image_origin>(img.begin, x.origins);
    for (uint64 i = 0; i < x.origins.num; i++) if ((origins[i].key >> 2) >= x.names.num) return false;
    image_array const * arrays = range_ptr<image_array>(img.begin, x.arrays);
    bool empty_array_slot = false;
    for (uint64 i = 0; i < x.arrays.num; i++) {
        if (arrays[i].addr == 0) { empty_array_slot = true; continue; }
        if (!obj_ok(arrays[i].addr) || arrays[i].first > x.entries.num || arrays[i].count > x.entries.num - arrays[i].first)
            return false;
    }
    if (!empty_slot || !empty_origin_slot || !empty_array_slot) return false;
    image_entry const * entries = range_ptr<image_entry>(img.begin, x.entries);
    image_step const * steps = range_ptr<image_step>(img.begin, x.steps);
    for (uint64 i = 0; i < x.entries.num; i++) {
        image_entry const & e = entries[i];
        if (e.kind > 4) return false;
        if (e.kind == 4) continue;
        if ((x.kind == 0) == (e.kind == 3)) return false;
        bool tree_entry = e.kind == 0 || e.kind == 3;
        if (tree_entry) {
            uint64 nodes = x.trees[e.tree & 1].nodes.num;
            if (e.tree > (x.kind == 0 ? 1 : 0) || e.num_steps == 0 || e.first_step > x.steps.num ||
                e.num_steps > x.steps.num - e.first_step || !obj_ok(e.value))
                return false;
            for (uint32 s = 0; s < e.num_steps; s++)
                if (steps[e.first_step + s].node >= nodes || !key_ok(steps[e.first_step + s].key)) return false;
            image_node const & leaf = range_ptr<image_node>(img.begin, x.trees[e.tree].nodes)[steps[e.first_step + e.num_steps - 1].node];
            if (e.vclass >= leaf.num_classes) return false;
        }
        if (e.kind == 0) {
            if (e.cls >= x.origins.num || !obj_ok(e.obj) || e.okind > 2 ||
                (e.okind != 0 && (e.converse >= x.origins.num || e.decl >= x.names.num)) ||
                (e.okind == 0 && e.converse != g_none))
                return false;
        } else if (e.kind == 1 || e.kind == 2) {
            if (e.cls >= x.names.num || !key_ok(e.obj) || (e.kind == 2 && !obj_ok(e.value))) return false;
        } else if (e.kind == 3) {
            if (e.cls != g_none && (e.cls >= x.names.num || !key_ok(e.obj))) return false;
        }
    }
    return true;
}

// The index of the image's tables for the extension with `extension_name_key` `key`, -1 if none.
int64 find_image_ext(std::string const & key) {
    std::call_once(g_image_once, load_image);
    if (!g_image) return -1;
    for (uint32 i = 0; i < g_image->hdr.num_exts; i++) {
        image_ext const & x = g_image->exts[i];
        if (x.name.off > g_image->hdr.size || x.name.num > g_image->hdr.size - x.name.off) continue;
        if (x.name.num == key.size() && memcmp(g_image->begin + x.name.off, key.data(), key.size()) == 0) return i;
    }
    return -1;
}

// Whether the image's tables `i` are usable; they are checked the first time, on any thread.
bool image_ext_usable(uint32 i) {
    uint8 st = g_image->state[i].load(std::memory_order_acquire);
    if (st == 0) {
        std::lock_guard<std::mutex> lock(g_image->check_mutex[i]);
        st = g_image->state[i].load(std::memory_order_acquire);
        if (st == 0) {
            st = check_image_ext(*g_image, g_image->exts[i]) ? 1 : 2;
            if (st == 2) fprintf(stderr, "warning: ignoring the import image's tables for an extension: corrupt\n");
            g_image->state[i].store(st, std::memory_order_release);
        }
    }
    return st == 1;
}

// The image's tables for the extension named `ext_name`, if usable.
image_ext const * image_ext_of(b_obj_arg ext_name) {
    std::string key;
    extension_name_key(ext_name, key);
    int64 i = find_image_ext(key);
    return i >= 0 && image_ext_usable(static_cast<uint32>(i)) ? &g_image->exts[i] : nullptr;
}

void load_interning(interning & in, image_ext const & x) {
    char const * b = g_image->begin;
    for (unsigned t = 0; t < 2; t++) {
        image_tree const & tr = x.trees[t];
        in.trees[t].load(range_ptr<image_node>(b, tr.nodes), static_cast<uint32>(tr.nodes.num),
                         range_ptr<uint32>(b, tr.children), range_ptr<uint64>(b, tr.classes),
                         range_ptr<image_root>(b, tr.roots), tr.roots.num);
    }
    in.names.load(range_ptr<image_name>(b, x.names), x.names.num, range_ptr<uint32>(b, x.names_index), x.names_index.num);
    in.origins.load(range_ptr<image_origin>(b, x.origins), x.origins.num,
                    range_ptr<uint32>(b, x.origins_index), x.origins_index.num);
}

// The interned entries of an entries array of a packed part, if the image has them.
image_array const * image_array_of(image_ext const & x, object * a) {
    image_array const * arrays = range_ptr<image_array>(g_image->begin, x.arrays);
    uint64 addr = reinterpret_cast<uint64>(a);
    for (size_t i = slot_of(addr, x.arrays.num); arrays[i].addr != 0; i = (i + 1) & (x.arrays.num - 1))
        if (arrays[i].addr == addr) return &arrays[i];
    return nullptr;
}

// =======================================
// Writing an image

struct image_writer {
    std::string data;
    uint64 base;    // file offset of `data`
    image_range append(void const * p, size_t elem, size_t n) {
        while (data.size() % 8) data.push_back(0);
        image_range r { base + data.size(), n };
        if (n > 0) data.append(static_cast<char const *>(p), elem * n);
        return r;
    }
    template<class T> image_range append(std::vector<T> const & v) { return append(v.data(), sizeof(T), v.size()); }
};

template<class F> std::vector<uint32> open_index(size_t n, F const & hash_of) {
    size_t size = 1;
    while (size < 2 * n + 1) size *= 2;
    std::vector<uint32> index(size, 0);
    for (size_t c = 0; c < n; c++) {
        size_t i = slot_of(hash_of(c), size);
        while (index[i] != 0) i = (i + 1) & (size - 1);
        index[i] = static_cast<uint32>(c + 1);
    }
    return index;
}

// The tables of one extension, interning all entries of all packed parts.
bool write_image_ext(image_writer & w, object * ext_name, state_kind kind, image_ext & x, size_t & num_entries) {
    interning in(kind);
    std::vector<image_entry> entries;
    std::vector<image_step> steps;
    std::vector<std::pair<uint64, std::pair<uint32, uint32>>> arrays;
    std::unordered_set<object *> seen;
    uint64_t pack_checksum, pack_base, pack_size;
    if (!first_pack_identity(pack_checksum, pack_base, pack_size)) return false;
    // only objects of the first pack can be referred to; keys and names may also be scalars
    auto in_pack = [&](void const * p) {
        uint64 a = reinterpret_cast<uint64>(p);
        return p && a >= pack_base && a - pack_base < pack_size;
    };
    auto key_in_pack = [&](void const * p) { return (reinterpret_cast<uintptr_t>(p) & 1) == 1 || in_pack(p); };
    // arrays with an entry that the image cannot describe are left out; imports replay them by
    // calling Lean functions
    size_t left_out = 0;
    for_each_first_pack_ext_entries(ext_name, [&](object * a) {
        if (!seen.insert(a).second) return;
        size_t first = entries.size(), first_step = steps.size();
        bool ok = true;
        for (size_t i = 0; i < lean_array_size(a) && ok; i++) {
            object * e = lean_array_get_core(a, i);
            image_entry ie = {};
            ie.kind = 4;
            ie.cls = ie.converse = ie.decl = g_none;
            if (lean_ptr_tag(e) == 0) {
                entry_desc d;
                if (!in.describe(lean_ctor_get(e, 0), d)) { ok = false; break; }
                ie.kind = d.kind; ie.tree = d.tree; ie.okind = d.okind;
                ie.first_step = static_cast<uint32>(steps.size());
                ie.num_steps = d.num_steps;
                for (uint32 s = 0; s < d.num_steps; s++) {
                    if (!key_in_pack(d.steps[s].key)) ok = false;
                    steps.push_back(image_step { reinterpret_cast<uint64>(d.steps[s].key), d.steps[s].node, 0 });
                }
                ie.vclass = d.vclass; ie.h0 = d.h0;
                ie.cls = d.cls; ie.converse = d.converse; ie.decl = d.decl;
                ie.value = reinterpret_cast<uint64>(d.value); ie.obj = reinterpret_cast<uint64>(d.obj);
                if (ie.kind != 1 && !in_pack(d.value)) ok = false;
                if ((ie.kind != 3 || ie.cls != g_none) && !key_in_pack(d.obj)) ok = false;
            }
            entries.push_back(ie);
        }
        if (!ok) {
            entries.resize(first);
            steps.resize(first_step);
            left_out++;
            return;
        }
        arrays.push_back({ reinterpret_cast<uint64>(a), { static_cast<uint32>(first), static_cast<uint32>(entries.size() - first) } });
    });
    auto skip = [&](char const * reason) {
        fprintf(stderr, "warning: writeImportImage: leaving out %s: %s\n", name(ext_name).to_string().c_str(), reason);
        return false;
    };
    if (left_out > 0)
        fprintf(stderr, "warning: writeImportImage: %s: leaving out %zu entries arrays that it cannot describe\n",
                name(ext_name).to_string().c_str(), left_out);
    if (arrays.empty()) return false;
    std::string key;
    extension_name_key(ext_name, key);
    x = {};
    x.name = w.append(key.data(), 1, key.size());
    x.kind = static_cast<uint32>(kind);
    for (unsigned t = 0; t < 2; t++) {
        trie_universe const & u = in.trees[t];
        std::vector<image_node> nodes;
        std::vector<uint32> children;
        std::vector<uint64> classes;
        for (uint32 n = 0; n < u.size(); n++) {
            image_node in_node = {};
            in_node.key = reinterpret_cast<uint64>(u.key(n));
            in_node.first_child = static_cast<uint32>(children.size());
            for (uint32 c : u.children(n)) children.push_back(c);
            in_node.num_children = static_cast<uint32>(children.size()) - in_node.first_child;
            in_node.first_class = static_cast<uint32>(classes.size());
            for (object * c : u.dyn_classes(n)) {
                if (!in_pack(c)) return skip("a value class is not in the pack");
                classes.push_back(reinterpret_cast<uint64>(c));
            }
            in_node.num_classes = static_cast<uint32>(classes.size()) - in_node.first_class;
            if (!key_in_pack(u.key(n))) return skip("a key is not in the pack");
            nodes.push_back(in_node);
        }
        std::vector<image_root> roots;
        for (auto const & r : u.dyn_roots()) roots.push_back(image_root { r.first, r.second, 0 });
        x.trees[t].nodes = w.append(nodes);
        x.trees[t].children = w.append(children);
        x.trees[t].classes = w.append(classes);
        x.trees[t].roots = w.append(roots);
    }
    std::vector<image_name> names;
    for (uint32 c = 0; c < in.names.size(); c++) {
        if (!key_in_pack(in.names.rep(c))) return skip("a name is not in the pack");
        names.push_back(image_name { in.names.hash(c), reinterpret_cast<uint64>(in.names.rep(c)) });
    }
    x.names = w.append(names);
    x.names_index = w.append(open_index(names.size(), [&](size_t c) { return names[c].hash; }));
    std::vector<image_origin> origins;
    for (uint32 c = 0; c < in.origins.size(); c++) origins.push_back(image_origin { in.origins.key(c), in.origins.hash(c) });
    x.origins = w.append(origins);
    x.origins_index = w.append(open_index(origins.size(), [&](size_t c) { return origins[c].key; }));
    size_t asize = 1;
    while (asize < 2 * arrays.size() + 1) asize *= 2;
    std::vector<image_array> table(asize, image_array { 0, 0, 0 });
    for (auto const & a : arrays) {
        size_t i = slot_of(a.first, asize);
        while (table[i].addr != 0) i = (i + 1) & (asize - 1);
        table[i] = image_array { a.first, a.second.first, a.second.second };
    }
    x.arrays = w.append(table);
    x.entries = w.append(entries);
    x.steps = w.append(steps);
    num_entries += entries.size();
    return true;
}

// The checksum of the tables of `x` as `check_image_ext` computes it.
uint64 image_ext_checksum(char const * file, image_ext const & x) {
    image_range const * ranges[] = { &x.name, &x.trees[0].nodes, &x.trees[0].children, &x.trees[0].classes,
        &x.trees[0].roots, &x.trees[1].nodes, &x.trees[1].children, &x.trees[1].classes, &x.trees[1].roots,
        &x.names, &x.names_index, &x.origins, &x.origins_index, &x.arrays, &x.entries, &x.steps };
    size_t elems[] = { 1, sizeof(image_node), 4, 8, sizeof(image_root), sizeof(image_node), 4, 8, sizeof(image_root),
        sizeof(image_name), 4, sizeof(image_origin), 4, sizeof(image_array), sizeof(image_entry), sizeof(image_step) };
    uint64 h = side_file_checksum(nullptr, 0);
    for (size_t i = 0; i < sizeof(ranges) / sizeof(ranges[0]); i++)
        h = side_file_checksum(file + ranges[i]->off, ranges[i]->num * elems[i], h);
    return h;
}
}

extern "C" uint8 lean_paperlean_imported_state_kind(obj_arg ext_name);
extern "C" obj_res lean_paperlean_imported_state_initial(obj_arg ext_name);

namespace {
bool g_replay_enabled = false;

// The nonempty arrays of `as`, in order.
std::vector<object *> nonempty_arrays(b_obj_arg as) {
    std::vector<object *> r;
    for (size_t m = 0; m < lean_array_size(as); m++) {
        object * a = lean_array_get_core(as, m);
        if (lean_array_size(a) > 0) r.push_back(a);
    }
    return r;
}

// The state that the fold builds from `initial` and the entries arrays `arrays`, with the image's
// tables `x` if not `nullptr`; `nullptr` if the models do not cover an entry. Calls Lean functions
// only for the arrays that are not in the image.
object * replay_state(state_kind kind, image_ext const * x, object * initial, std::vector<object *> const & arrays) {
    interning in(kind);
    if (x) load_interning(in, *x);
    std::vector<entry_step> steps;
    auto for_each = [&](auto const & add) -> bool {
        for (object * a : arrays) {
            if (image_array const * ia = x ? image_array_of(*x, a) : nullptr) {
                if (ia->count != lean_array_size(a)) return false;
                image_entry const * es = range_ptr<image_entry>(g_image->begin, x->entries) + ia->first;
                image_step const * ss = range_ptr<image_step>(g_image->begin, x->steps);
                for (uint32 i = 0; i < ia->count; i++) {
                    image_entry const & e = es[i];
                    if (e.kind == 4) continue;
                    entry_desc d;
                    d.kind = e.kind; d.tree = e.tree; d.okind = e.okind;
                    steps.resize(e.num_steps);
                    for (uint32 s = 0; s < e.num_steps; s++)
                        steps[s] = entry_step { reinterpret_cast<object *>(ss[e.first_step + s].key), ss[e.first_step + s].node };
                    d.steps = steps.data(); d.num_steps = e.num_steps;
                    d.vclass = e.vclass; d.h0 = e.h0;
                    d.cls = e.cls; d.converse = e.converse; d.decl = e.decl;
                    d.value = reinterpret_cast<object *>(e.value); d.obj = reinterpret_cast<object *>(e.obj);
                    add(d);
                }
            } else {
                for (size_t i = 0; i < lean_array_size(a); i++) {
                    object * e = lean_array_get_core(a, i);
                    // `Entry.global a` is constructor 0, `Entry.scoped ns a` constructor 1
                    if (lean_ptr_tag(e) != 0) continue;
                    entry_desc d;
                    if (!in.describe(lean_ctor_get(e, 0), d)) return false;
                    add(d);
                }
            }
        }
        return true;
    };
    object * r = nullptr;
    size_t replayed = 0;
    if (kind == state_kind::simp) {
        simp_replay s(in, initial);
        if (for_each([&](entry_desc const & d) { s.add(d); replayed++; })) r = replayed ? s.materialize() : initial;
    } else {
        instances_replay s(in, initial);
        if (for_each([&](entry_desc const & d) { s.add(d); replayed++; })) r = replayed ? s.materialize() : initial;
    }
    // with no entry, the fold's state is the initial state itself
    if (r == initial) lean_inc(initial);
    return r;
}

unsigned num_fields(state_kind kind) { return kind == state_kind::simp ? g_simp_theorems_fields : g_instances_fields; }

// =======================================
// Prefetching

// The number of entries from which a state is replayed on its own thread.
constexpr size_t g_prefetch_min_entries = 1000;

// A replay started on another thread when `finalizePersistentExtensions` begins, or after it collects
// the entries of extensions registered meanwhile; `ScopedEnvExtension.addImportedFn`, called by
// `finalizePersistentExtensions` on the same thread, takes its state if it is called with the same
// initial state and the same entries arrays, and `finalizePersistentExtensions` drops the others of
// its thread when it ends, so no replay outlives the regions of the import. The thread reads only
// the image, the entries arrays and the initial state, all persistent, calls pure Lean functions on
// the entries that are not in the image (of the modules the image's pack does not have), and
// allocates the state's objects, which pass to the importing thread when it joins.
struct prefetch {
    std::thread::id owner;             // the importing thread
    std::string key;                   // `extension_name_key` of the extension
    object * initial = nullptr;        // owned
    std::vector<object *> arrays;      // the nonempty entries arrays, persistent
    object * result = nullptr;         // set by the thread: the state, `nullptr` if not replayed
    std::unique_ptr<lthread> thread;
    void join() { if (thread) { thread->join(); thread.reset(); } }
    ~prefetch() { join(); if (initial) lean_dec(initial); }
};
std::mutex g_prefetch_mutex;
std::vector<std::unique_ptr<prefetch>> * g_prefetches = new std::vector<std::unique_ptr<prefetch>>();

// Removes the prefetches of the current thread for which `pred` holds.
template<class P> std::vector<std::unique_ptr<prefetch>> remove_prefetches(P const & pred) {
    std::vector<std::unique_ptr<prefetch>> r;
    std::lock_guard<std::mutex> lock(g_prefetch_mutex);
    std::thread::id self = std::this_thread::get_id();
    for (auto it = g_prefetches->begin(); it != g_prefetches->end();) {
        if ((*it)->owner == self && pred(**it)) { r.push_back(std::move(*it)); it = g_prefetches->erase(it); }
        else ++it;
    }
    return r;
}

// Waits for prefetches and releases their states (a state marked persistent stays allocated).
void drop_prefetches(std::vector<std::unique_ptr<prefetch>> & ps) {
    for (auto & p : ps) {
        p->join();
        if (p->result) lean_dec(p->result);
        p->result = nullptr;
    }
}

// Whether the image's table of entries arrays of `x` can be searched by `image_array_of` before
// `x` is checked: in range, a power of two in size, with an empty slot.
bool arrays_table_ok(image_ext const & x) {
    image_range r = x.arrays;
    if (r.off % 8 != 0 || r.off > g_image->hdr.size || r.num > (g_image->hdr.size - r.off) / sizeof(image_array) ||
        r.num == 0 || (r.num & (r.num - 1)) != 0)
        return false;
    image_array const * arrays = range_ptr<image_array>(g_image->begin, r);
    for (uint64 i = 0; i < r.num; i++) if (arrays[i].addr == 0) return true;
    return false;
}

// The state of a prefetch for the extension named `ext_name` started with `initial` and the
// nonempty arrays of `as`, if any; prefetches for the extension with other arguments are dropped.
object * take_prefetched(b_obj_arg ext_name, b_obj_arg initial, b_obj_arg as) {
    {
        std::lock_guard<std::mutex> lock(g_prefetch_mutex);
        if (g_prefetches->empty()) return nullptr;
    }
    std::string key;
    extension_name_key(ext_name, key);
    std::vector<std::unique_ptr<prefetch>> mine = remove_prefetches([&](prefetch const & p) { return p.key == key; });
    if (mine.empty()) return nullptr;
    std::vector<object *> arrays = nonempty_arrays(as);
    object * r = nullptr;
    for (auto & p : mine) {
        bool usable = !r && p->initial == initial && p->arrays == arrays;
        {
            // the time the import waits for the prefetch it takes, if import timing is enabled
            std::unique_ptr<scoped_import_timer> t(usable ? new scoped_import_timer(counter_prefetch_wait) : nullptr);
            p->join();
        }
        if (!p->result) continue;
        if (usable) r = p->result;
        else lean_dec(p->result);
    }
    return r;
}
}

/* enableImportedStateReplay : BaseIO Unit -- once `Lean.PaperLean.ImportState` is initialized */
extern "C" LEAN_EXPORT obj_res lean_paperlean_enable_imported_state_replay() {
    g_replay_enabled = true;
    return lean_box(0);
}

/* prefetchImportedState (extName : @& Name) (as : @& Array (Array EnvExtensionEntry)) (persistent : Bool) :
     BaseIO Unit
   Starts replaying the state of the extension named `extName` from the entries `as` on another
   thread, if it is replayed and the import image has most of its entries, and enough of them. With `persistent`, the state is marked persistent, as `finalizeImport` marks the
   environment. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_prefetch_imported_state(b_obj_arg ext_name, b_obj_arg as, uint8 persistent) {
    if (!g_replay_enabled || import_legacy_mode()) return lean_box(0);
    std::string key;
    extension_name_key(ext_name, key);
    int64 xi = find_image_ext(key);
    if (xi < 0) return lean_box(0);
    // with import timing, why a state with image tables is not prefetched
    auto skip = [&](char const * why) {
        if (import_timing_enabled())
            fprintf(stderr, "paperlean-counter prefetch.%s ext=%s\n", why, name(ext_name).to_string().c_str());
        return lean_box(0);
    };
    if (!arrays_table_ok(g_image->exts[xi])) return skip("badTable");
    std::vector<object *> arrays = nonempty_arrays(as);
    // the entries in the image, and the others, which the thread replays by calling Lean functions
    size_t n = 0, others = 0;
    for (object * a : arrays) {
        if (image_array const * ia = image_array_of(g_image->exts[xi], a)) {
            if (ia->count != lean_array_size(a)) return skip("badArray");
            n += ia->count;
        } else {
            // the thread must not change reference counts in the entries: a persistent array is
            // in a region read from a file, or `markPersistent` marked it with everything it refers to
            if (!lean_is_persistent(a)) return skip("notPersistent");
            others += lean_array_size(a);
        }
    }
    if (n < g_prefetch_min_entries) return arrays.empty() ? lean_box(0) : skip("small");
    if (others > n) return skip("mostlyNotInImage");
    // `finalizePersistentExtensions` prefetches each extension once and drops the prefetches of its
    // thread when it ends, so a pending prefetch of the extension on this thread is stale
    std::vector<std::unique_ptr<prefetch>> stale = remove_prefetches([&](prefetch const & p) { return p.key == key; });
    drop_prefetches(stale);
    lean_inc(ext_name);
    uint8 okind = lean_paperlean_imported_state_kind(ext_name);
    if (okind > 1 || g_image->exts[xi].kind != okind || !init_trie_empty()) return skip("kind");
    state_kind kind = static_cast<state_kind>(okind);
    lean_inc(ext_name);
    object * initial_opt = lean_paperlean_imported_state_initial(ext_name);
    if (lean_is_scalar(initial_opt)) return skip("noInitial");
    object * initial = lean_ctor_get(initial_opt, 0);
    lean_inc(initial);
    lean_dec(initial_opt);
    // the other thread must not change reference counts in the initial state
    if (!lean_is_persistent(initial) || !valid_initial(initial, num_fields(kind))) {
        lean_dec(initial);
        return skip("initial");
    }
    auto p = std::unique_ptr<prefetch>(new prefetch());
    p->owner = std::this_thread::get_id();
    p->key = key;
    p->initial = initial;
    p->arrays = std::move(arrays);
    prefetch * q = p.get();
    uint32 i = static_cast<uint32>(xi);
    bool mark = persistent != 0;
    p->thread.reset(new lthread([q, i, kind, mark] {
        if (!image_ext_usable(i)) return;
        object * r = replay_state(kind, &g_image->exts[i], q->initial, q->arrays);
        if (r && mark) lean_mark_persistent(r);
        q->result = r;
    }));
    if (import_timing_enabled())
        fprintf(stderr, "paperlean-counter prefetch.started ext=%s entries=%zu\n", name(ext_name).to_string().c_str(), n);
    std::lock_guard<std::mutex> lock(g_prefetch_mutex);
    g_prefetches->push_back(std::move(p));
    return lean_box(0);
}

/* dropPrefetchedReplays (env : @& Environment) : BaseIO Unit
   Waits for the prefetches of the current thread that were not taken and releases them; called when
   `finalizePersistentExtensions` ends. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_drop_prefetched_replays(b_obj_arg) {
    std::vector<std::unique_ptr<prefetch>> mine = remove_prefetches([](prefetch const &) { return true; });
    drop_prefetches(mine);
    return lean_box(0);
}

/* paperleanImportedState? {α σ : Type} (extName : @& Name) (initial : @& σ)
     (as : @& Array (Array (ScopedEnvExtension.Entry α))) : BaseIO (Option σ)
   The state `ScopedEnvExtension.addImportedFn` folds from the global entries of `as`, for a simp set
   or the instance extension, if it is replayed. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_imported_state(b_obj_arg ext_name, b_obj_arg initial, b_obj_arg as) {
    if (!g_replay_enabled || import_legacy_mode()) return lean_box(0);
    auto some = [](object * r) {
        object * o = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(o, 0, r);
        return o;
    };
    if (object * r = take_prefetched(ext_name, initial, as)) return some(r);
    lean_inc(ext_name);
    uint8 okind = lean_paperlean_imported_state_kind(ext_name);
    if (okind > 1) return lean_box(0);
    state_kind kind = static_cast<state_kind>(okind);
    image_ext const * x = image_ext_of(ext_name);
    // without an image, the models are only built to be compared with the fold
    if (!x && !import_check_mode()) return lean_box(0);
    // a registered extension that is not replayed would go unchecked
    auto decline = [&](char const * why) {
        if (import_check_mode())
            fprintf(stderr, "PAPERLEAN_IMPORT=check: the imported state of %s is not replayed: %s\n",
                    name(ext_name).to_string().c_str(), why);
        return lean_box(0);
    };
    if (!init_trie_empty()) return decline("unexpected `createNodes`");
    if (x && x->kind != static_cast<uint32>(kind)) return decline("the image has another kind");
    if (!valid_initial(initial, num_fields(kind))) return decline("unexpected initial state");
    object * r = replay_state(kind, x, initial, nonempty_arrays(as));
    if (!r) return decline("an entry with no keys");
    return some(r);
}

/* writeImportImageCore (out : @& String) (exts : @& Array (Name × UInt8)) : IO Nat
   Writes the import image of the first olean pack for the extensions `exts` of the given kinds. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_write_import_image(b_obj_arg oout, b_obj_arg oexts) {
#if defined(LEAN_MMAP) && !defined(LEAN_WINDOWS)
    std::string out(lean_string_cstr(oout));
    image_header hdr = {};
    init_side_file_header(hdr.common, g_image_kind, sizeof(image_header));
    hdr.format = g_image_format;
    if (!first_pack_identity(hdr.pack_checksum, hdr.pack_base, hdr.pack_size) || !init_trie_empty())
        return io_result_mk_error("writeImportImage: no olean pack is in use");
    std::vector<std::pair<object *, state_kind>> kinds;
    for (size_t i = 0; i < lean_array_size(oexts); i++) {
        object * p = lean_array_get_core(oexts, i);
        uint8 k = lean_unbox(lean_ctor_get(p, 1));
        if (k <= 1) kinds.push_back({ lean_ctor_get(p, 0), static_cast<state_kind>(k) });
    }
    image_writer w;
    // the extension records follow the header, the tables them
    hdr.exts_off = sizeof(image_header);
    w.base = hdr.exts_off + kinds.size() * sizeof(image_ext);
    std::vector<image_ext> exts;
    size_t num_entries = 0;
    for (auto const & k : kinds) {
        image_ext x;
        if (write_image_ext(w, k.first, k.second, x, num_entries)) exts.push_back(x);
    }
    while (w.data.size() % 8) w.data.push_back(0);
    hdr.num_exts = static_cast<uint32>(exts.size());
    // tables were laid out for `kinds.size()` records; pad the records to that number
    std::string file(sizeof(image_header) + kinds.size() * sizeof(image_ext), '\0');
    file += w.data;
    for (image_ext & x : exts) x.checksum = image_ext_checksum(file.data(), x);
    if (!exts.empty()) memcpy(&file[hdr.exts_off], exts.data(), exts.size() * sizeof(image_ext));
    hdr.size = file.size();
    hdr.common.checksum = image_checksum(hdr, file.data() + hdr.exts_off, hdr.num_exts * sizeof(image_ext));
    memcpy(&file[0], &hdr, sizeof(hdr));
    std::string tmp = out + ".tmp." + std::to_string(getpid());
    FILE * f = fopen(tmp.c_str(), "wb");
    if (!f || fwrite(file.data(), 1, file.size(), f) != file.size() || fclose(f) != 0) {
        std::remove(tmp.c_str());
        return io_result_mk_error("writeImportImage: failed to write '" + out + "'");
    }
    if (std::rename(tmp.c_str(), out.c_str()) != 0) {
        std::remove(tmp.c_str());
        return io_result_mk_error("writeImportImage: failed to write '" + out + "'");
    }
    return io_result_mk_ok(lean_usize_to_nat(num_entries));
#else
    (void)oout;
    return io_result_mk_error("writeImportImage: not supported on this platform");
#endif
}
}
