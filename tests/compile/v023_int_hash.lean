import Init

namespace PortableHash

-- The kernel reduces both original hash equations by rfl for variable payloads.
example (n : Nat) : hash (Int.ofNat n) = UInt64.ofNat (2 * n) := rfl
example (n : Nat) : hash (Int.negSucc n) = UInt64.ofNat (2 * n + 1) := rfl
example : hash (Int.negSucc (2^130 + 3)) = UInt64.ofNat (2 * (2^130 + 3) + 1) := rfl
example (n : Nat) : hash n = UInt64.ofNat n := rfl
example {n : Nat} (x : Fin n) : hash x = UInt64.ofNat x.val := rfl

@[noinline] def direct (x : Int) := hash x

-- Exercise passing the dictionary through a genuinely generic, nonspecialized boundary.
@[noinline, nospecialize] def generic [Hashable α] (x : α) := hash x
@[noinline] def viaGeneric (x : Int) := generic x

@[noinline, nospecialize] def withDictionary (d : Hashable α) (x : α) := @hash α d x
@[noinline, instance_reducible] def dictionary : Hashable Int := inferInstance
@[noinline] def viaDictionary (x : Int) := withDictionary dictionary x

@[noinline] def partialHash : Int → UInt64 := hash
@[noinline, nospecialize] def applyHash (f : α → UInt64) (x : α) := f x
@[noinline] def viaHigherOrder (x : Int) := applyHash partialHash x

end PortableHash


private def expected : Int → UInt64
  | .ofNat n => UInt64.ofNat (2 * n)
  | .negSucc n => UInt64.ofNat (2 * n + 1)

private def verify : IO Unit := do
  for bits in [0, 1, 31, 32, 62, 63, 64, 65, 127, 128, 1024, 4096] do
    let p := 2 ^ bits
    for n in [0, p - 1, p, p + 1, p + 3] do
      for x in [Int.ofNat n, Int.negSucc n] do
        let ref := expected x
        for h in [PortableHash.direct, PortableHash.viaGeneric, PortableHash.viaDictionary,
                  PortableHash.viaHigherOrder] do
          unless h x == ref do throw <| IO.userError s!"Int hash mismatch at {bits} bits"


def main : IO Unit := do
  verify
  IO.println "exact Int hash passed"
