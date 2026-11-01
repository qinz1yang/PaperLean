# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Tests that code compiled by PaperLean refers only to declarations that official Lean has, with
# official Lean's calling conventions, so that official Lean can load and run what PaperLean built:
# - callers compiled by PaperLean (in a non-module file, also under `compiler.small` 10 and 100, and
#   in a `module`) of upstream functions that PaperLean modifies, some of them inlined or
#   specialized into their callers (`withTraceNode`, `Meta.realizeValue`), of an instance PaperLean
#   adds (`toJson` of import artifact maps), and of functions of which the toolchain has
#   specializations (`Array.contains` on strings: official Lean's, and one of a PaperLean module, which
#   no caller gets) declare the external functions listed, all of which official Lean 4.35.0-rc3
#   exports with these prototypes (official Lean's own lists differ only where it inlines or
#   specializes the upstream functions whose bodies call PaperLean's code, which are `@[noinline]`, or
#   `@[nospecialize]` too, in PaperLean);
# - `inline_abi.lean` finds no body of Lean's that an importer may inline under any
#   `compiler.small`, or specializes, and that reaches PaperLean's code, and prints the calling
#   conventions of the upstream functions whose compiled code PaperLean changes or that it makes
#   `@[noinline]`, which are official Lean's (its expected output).

cat > "$TMP_DIR/Callers.lean" <<'EOF2'
import Lean
import Lake.Load.Workspace
open Lean Meta Elab

/-! Callers of upstream functions that PaperLean modifies, some of them inlined into their callers. -/

def c1 (env : Environment) (n : Name) : Bool := isNoncomputable env n
def c2 (e : Expr) : MetaM LBool := isProofQuick e
def c3 (a : KeyedDeclsAttribute Nat) (env : Environment) (k : Name) :
    List (KeyedDeclsAttribute.AttributeEntry Nat) := a.getEntries env k
def c4 (e : Expr) : MetaM (Array SynthInstance.Instance) := SynthInstance.getInstances e
def c5 (e : Expr) : MetaM (Option Expr) := synthInstanceCore? e
def c6 (e : Expr) : MetaM Bool := isProof e
def c7 (env : Environment) (n : Name) : Bool := isNoncomputable env n (asyncMode := .local)
def c8 (d : DiscrTree Nat) (e : Expr) : MetaM (Array Nat) := d.getUnify e
def c9 (env : Environment) (n : Name) : Option IR.Decl := IR.findEnvDecl env n
def c10 (x : CoreM Nat) : CoreM Nat := withTraceNode `foo (fun _ => return "") x
def c11 (ext : ScopedEnvExtension Nat Nat Nat) (env : Environment) : Nat := ext.getState env
unsafe def c12 (df : KeyedDeclsAttribute.Def Nat) : IO (KeyedDeclsAttribute Nat) := KeyedDeclsAttribute.init df
def d1 (env : Environment) (n : Name) := env.find? n
def d2 (env : Environment) (n : Name) := env.contains n
def d3 (env : Environment) (n : Name) := env.findAsync? n
def d4 (env : Environment) (n : Name) := env.findConstVal? n
def d5 (ext : EnvExtension Nat) (env : Environment) := ext.getState env
def d6 (ext : SimplePersistentEnvExtension Nat Nat) (env : Environment) := ext.getState env
def d7 (ext : TagDeclarationExtension) (env : Environment) (n : Name) := ext.isTagged env n
def d8 (env : Environment) (opts : Options) (ns : Name) (od : List OpenDecl) (n : Name) :=
  ResolveName.resolveGlobalName env opts ns od n
def d9 (env : Environment) (n : Name) := env.containsOnBranch n
def d10 (n : Name) : CoreM ConstantInfo := getConstInfo n
def d11 (x : MetaM Nat) : MetaM Nat := withTraceNodeBefore `foo (fun _ => return "") x
def d12 (opts : Options) : CoreM Nat := profileitM Exception "x" opts (pure 1)
def d14 (ext : MapDeclarationExtension Nat) (env : Environment) (n : Name) := ext.find? env n
def d15 (ext : ParametricAttribute Nat) (env : Environment) (n : Name) := ext.getParam? env n
def d16 (attr : KeyedDeclsAttribute Nat) (env : Environment) (k : Name) := attr.getValues env k
def d17 (e : Expr) : MetaM Bool := do return (← isClass? e).isSome
def d18 (env : Environment) := env.checked.get
def d19 (x : MetaM Nat) : MetaM Nat := withTraceNode `foo (fun _ => return "") x
def d20 (x : TermElabM Nat) : TermElabM Nat := withTraceNode `foo (fun _ => return "") x
def d21 (env : Environment) (stx : Syntax) := expandMacroImpl? env stx
unsafe def d22 (env : Environment) (opts : Options) (n : Name) : Except String Nat := env.evalConst Nat opts n
def d23 (stx : Syntax) : MacroM AttributeKind := Elab.toAttributeKind stx
def d24 (e : Expr) : MetaM Expr := inferType e
def d25 (e : Expr) : MetaM Expr := whnf e
def d26 (e : Expr) : MetaM FunInfo := getFunInfo e
def d27 (e : Expr) (n : Nat) : MetaM FunInfo := getFunInfoNArgs e n

structure K where
  n : Nat
  deriving BEq, Hashable, TypeName

def e1 (c : Name) : MetaM K := realizeValue c ({ n := 1 } : K) (pure { n := 2 })
def e2 (a : Array String) (s : String) : Bool := a.contains s
def e3 (m : Std.HashMap String Nat) (s : String) : Option Nat := m.get? s
def e4 (m : NameMap ImportArtifacts) : Json := toJson m
def e5 (c : Lake.LoadConfig) : BaseIO (Option Lake.Workspace) := (Lake.loadWorkspace c).run?'
def e6 [BEq α] [Hashable α] [TypeName α] (env : Environment) (n : Name) (key : α)
    (mk : Environment → Options → BaseIO Dynamic) : IO Dynamic :=
  env.realizeValue n key mk
EOF2
cat > "$TMP_DIR/Mod.lean" <<'EOF2'
module
public import Lean
open Lean Meta

/-! A `module`, which sees only the exported bodies of Lean's, specializing `Meta.realizeValue`. -/

public structure K where
  n : Nat
  deriving BEq, Hashable, TypeName

public def m1 (c : Name) : MetaM K := realizeValue c ({ n := 1 } : K) (pure { n := 2 })
EOF2
cat > "$TMP_DIR/callers.expected.out" <<'EOF2'
double lean_float_div(double, double);
double lean_float_of_nat(lean_object*);
double lean_float_sub(double, double);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toAttributeKind(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_realizeValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstanceCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Options_empty;
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_noncomputableExt;
lean_object* l_Lean_profileitM___at___00Lean_Elab_shareCommonPreDefs_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_trace_profiler_threshold;
lean_object* l_Lean_trace_profiler_useHeartbeats;
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(lean_object*);
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(lean_object*);
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_FunInd_0__Lean_Tactic_FunInd_withLetDecls_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_promise_new();
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_set_heartbeats(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
return lean_io_result_mk_ok(lean_box(0));
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_add(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_Environment_areRealizationsEnabledForConst(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isNoncomputable(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
void lean_initialize();
EOF2
cat > "$TMP_DIR/callers10.expected.out" <<'EOF2'
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_div(double, double);
double lean_float_sub(double, double);
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toAttributeKind(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_realizeValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstanceCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_maxHeartbeats;
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_noncomputableExt;
lean_object* l_Lean_profileitIOUnsafe___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_trace_profiler_threshold;
lean_object* l_Lean_trace_profiler_useHeartbeats;
lean_object* l_List_mapTR_loop___at___00Lean_KeyedDeclsAttribute_getValues_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_promise_new();
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_io_set_heartbeats(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_option_get_or_block(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
return lean_io_result_mk_ok(lean_box(0));
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_add(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_Environment_areRealizationsEnabledForConst(lean_object*, lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isNoncomputable(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
void lean_initialize();
EOF2
cat > "$TMP_DIR/callers100.expected.out" <<'EOF2'
double lean_float_div(double, double);
double lean_float_mul(double, double);
double lean_float_of_bits(uint64_t);
double lean_float_sub(double, double);
double lean_uint64_to_float(uint64_t);
lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg___lam__0(lean_object*);
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toAttributeKind(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_IR_declMapExt;
lean_object* l_Lean_KeyedDeclsAttribute_ExtensionState_insert___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg___lam__1___boxed(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg___lam__3___boxed(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg___lam__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object*);
lean_object* l_Lean_MessageData_stripNestedTags(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isPropQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstanceCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_mkNewPath___redArg(size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_findAux___redArg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_insertAux___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_attributeMapRef;
lean_object* l_Lean_instInhabitedPPFns_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPPFns_default___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPPFns_default___lam__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPPFns_default___lam__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPPFns_default___lam__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_interruptExceptionId;
lean_object* l_Lean_maxHeartbeats;
lean_object* l_Lean_noncomputableExt;
lean_object* l_Lean_ppExt;
lean_object* l_Lean_pp_rawOnError;
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_trace_profiler_threshold;
lean_object* l_Lean_trace_profiler_useHeartbeats;
lean_object* l_List_foldl___at___00Lean_MacroScopesView_review_spec__0(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___00Lean_KeyedDeclsAttribute_getValues_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(lean_object*, lean_object*);
lean_object* l_List_range_loop(lean_object*, lean_object*);
lean_object* l_Nat_toDigitsCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00Lean_Kernel_Environment_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Module_importArtsFacetConfig_spec__0_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_EnvironmentHeader_moduleNames_spec__0(size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Float_Model_UnpackedFloat_shiftToExponent_spec__0(lean_object*, lean_object*);
lean_object* l___private_Init_Prelude_0__Lean_extractMacroScopesAux(lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ImportingFlag_0__Lean_importingRef;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeBaseIO___redArg(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_promise_new();
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_io_set_heartbeats(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_log2(lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_option_get_or_block(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
lean_object* lean_string_of_usize(size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* lean_system_platform_nbits(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
return lean_io_result_mk_ok(lean_box(0));
size_t lean_array_size(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_add(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_of_nat_mk(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t l_Array_binSearchAux___at___00Lean_TagDeclarationExtension_isTagged_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_Name_isInaccessibleUserName(lean_object*);
uint8_t l_Lean_Name_quickCmpAux(lean_object*, lean_object*);
uint8_t l_Lean_isNoncomputable(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_EmitC_0__Lean_Compiler_LCNF_Arg_toCString_spec__1_spec__2___redArg(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_io_initializing();
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
void lean_initialize();
EOF2
cat > "$TMP_DIR/mod.expected.out" <<'EOF2'
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Options_empty;
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_promise_new();
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_set_heartbeats(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_usize_to_nat(size_t);
return lean_io_result_mk_ok(lean_box(0));
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_add(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t l_Lean_Environment_areRealizationsEnabledForConst(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
void lean_initialize();
EOF2
cat > "$TMP_DIR/inline_abi.expected.out" <<'EOF2'
Lake.compileLeanModule: obj obj obj obj obj obj tobj obj obj obj void : obj
Lake.compileLeanModule (impure): obj obj obj obj obj obj tobj obj obj obj lcVoid : obj
Lake.compileLeanModule._boxed: obj obj obj obj obj obj tobj obj obj obj tagged : obj
Lake.compileLeanModule._boxed (impure): obj obj obj obj obj obj tobj obj obj obj tagged : obj
Lake.download: obj obj @& obj obj void : obj
Lake.download (impure): obj obj @& obj obj lcVoid : obj
Lake.download._boxed: obj obj obj obj tagged : obj
Lake.download._boxed (impure): obj obj obj obj tagged : obj
Lake.tar: obj obj u8 @& obj obj void : obj
Lake.tar (impure): obj obj UInt8 @& obj obj lcVoid : obj
Lake.tar._boxed: obj obj tagged obj obj tagged : obj
Lake.tar._boxed (impure): obj obj tagged obj obj tagged : obj
Lake.fetchFileHash: obj u8 @& obj @& tobj @& tobj @& tobj @& obj obj void : obj
Lake.fetchFileHash (impure): obj UInt8 @& obj @& tobj @& tobj @& tobj @& obj obj lcVoid : obj
Lake.fetchFileHash._redArg: obj u8 @& obj obj void : obj
Lake.fetchFileHash._redArg (impure): obj UInt8 @& obj obj lcVoid : obj
Lake.fetchFileHash._boxed: obj tagged obj tobj tobj tobj obj obj tagged : obj
Lake.fetchFileHash._boxed (impure): obj tagged obj tobj tobj tobj obj obj tagged : obj
Lake.fetchFileHash._redArg._boxed: obj tagged obj obj tagged : obj
Lake.fetchFileHash._redArg._boxed (impure): obj tagged obj obj tagged : obj
Lake.Module.cacheOutputHashes: obj void : obj
Lake.Module.cacheOutputHashes (impure): obj lcVoid : obj
Lake.Module.cacheOutputHashes._boxed: obj tagged : obj
Lake.Module.cacheOutputHashes._boxed (impure): obj tagged : obj
Lake.Workspace.runBuild: ◾ obj obj obj void : obj
Lake.Workspace.runBuild (impure): lcErased obj obj obj lcVoid : obj
Lake.Workspace.runBuild._redArg: obj obj obj void : obj
Lake.Workspace.runBuild._redArg (impure): obj obj obj lcVoid : obj
Lake.Workspace.runBuild._boxed: tobj obj obj obj tagged : obj
Lake.Workspace.runBuild._boxed (impure): tobj obj obj obj tagged : obj
Lake.Workspace.runBuild._redArg._boxed: obj obj obj tagged : obj
Lake.Workspace.runBuild._redArg._boxed (impure): obj obj obj tagged : obj
Lake.loadWorkspace: obj @& obj void : obj
Lake.loadWorkspace (impure): obj @& obj lcVoid : obj
Lake.loadWorkspace._boxed: obj obj tagged : obj
Lake.loadWorkspace._boxed (impure): obj obj tagged : obj
Lean.isNoncomputable: obj tobj @& tobj : u8
Lean.isNoncomputable (impure): obj tobj @& tobj : UInt8
Lean.isNoncomputable._boxed: obj tobj tobj : tagged
Lean.isNoncomputable._boxed (impure): obj tobj tobj : tagged
Lean.Elab.Command.runTermElabM: ◾ obj @& obj @& tobj void : obj
Lean.Elab.Command.runTermElabM (impure): lcErased obj @& obj @& tobj lcVoid : obj
Lean.Elab.Command.runTermElabM._redArg: obj @& obj @& tobj void : obj
Lean.Elab.Command.runTermElabM._redArg (impure): obj @& obj @& tobj lcVoid : obj
Lean.Elab.Command.runTermElabM._boxed: tobj obj obj tobj tagged : obj
Lean.Elab.Command.runTermElabM._boxed (impure): tobj obj obj tobj tagged : obj
Lean.Elab.Command.runTermElabM._redArg._boxed: obj obj tobj tagged : obj
Lean.Elab.Command.runTermElabM._redArg._boxed (impure): obj obj tobj tagged : obj
Lean.Elab.runFrontend: obj obj obj tobj u32 tobj @& tobj u8 @& obj obj u8 tobj tobj tobj tobj void : obj
Lean.Elab.runFrontend (impure): obj obj obj tobj UInt32 tobj @& tobj UInt8 @& obj obj UInt8 tobj tobj tobj tobj lcVoid : obj
Lean.Elab.runFrontend._boxed: obj obj obj tobj tobj tobj tobj tagged obj obj tagged tobj tobj tobj tobj tagged : obj
Lean.Elab.runFrontend._boxed (impure): obj obj obj tobj tobj tobj tobj tagged obj obj tagged tobj tobj tobj tobj tagged : obj
Lean.Elab.Term.runTactic: tobj tobj tobj u8 @& obj @& tobj @& obj @& tobj @& obj @& tobj void : obj
Lean.Elab.Term.runTactic (impure): tobj tobj tobj UInt8 @& obj @& tobj @& obj @& tobj @& obj @& tobj lcVoid : obj
Lean.Elab.Term.runTactic._boxed: tobj tobj tobj tagged obj tobj obj tobj obj tobj tagged : obj
Lean.Elab.Term.runTactic._boxed (impure): tobj tobj tobj tagged obj tobj obj tobj obj tobj tagged : obj
Lean.EnvExtension.modifyState: ◾ obj obj tobj @& tobj tobj : obj
Lean.EnvExtension.modifyState (impure): lcErased obj obj tobj @& tobj tobj : obj
Lean.EnvExtension.modifyState._redArg: obj obj tobj @& tobj tobj : obj
Lean.EnvExtension.modifyState._redArg (impure): obj obj tobj @& tobj tobj : obj
Lean.EnvExtension.modifyState._boxed: tobj obj obj tobj tobj tobj : obj
Lean.EnvExtension.modifyState._boxed (impure): tobj obj obj tobj tobj tobj : obj
Lean.EnvExtension.modifyState._redArg._boxed: obj obj tobj tobj tobj : obj
Lean.EnvExtension.modifyState._redArg._boxed (impure): obj obj tobj tobj tobj : obj
Lean.EnvExtension.setState: ◾ obj obj tobj @& tobj : obj
Lean.EnvExtension.setState (impure): lcErased obj obj tobj @& tobj : obj
Lean.EnvExtension.setState._redArg: obj obj tobj @& tobj : obj
Lean.EnvExtension.setState._redArg (impure): obj obj tobj @& tobj : obj
Lean.EnvExtension.setState._boxed: tobj obj obj tobj tobj : obj
Lean.EnvExtension.setState._boxed (impure): tobj obj obj tobj tobj : obj
Lean.EnvExtension.setState._redArg._boxed: obj obj tobj tobj : obj
Lean.EnvExtension.setState._redArg._boxed (impure): obj obj tobj tobj : obj
Lean.Environment.AddConstAsyncResult.commitConst: obj obj tobj tobj void : obj
Lean.Environment.AddConstAsyncResult.commitConst (impure): obj obj tobj tobj lcVoid : obj
Lean.Environment.AddConstAsyncResult.commitConst._boxed: obj obj tobj tobj tagged : obj
Lean.Environment.AddConstAsyncResult.commitConst._boxed (impure): obj obj tobj tobj tagged : obj
Lean.Environment.addConstAsync: obj tobj u8 tobj u8 u8 void : obj
Lean.Environment.addConstAsync (impure): obj tobj UInt8 tobj UInt8 UInt8 lcVoid : obj
Lean.Environment.addConstAsync._boxed: obj tobj tagged tobj tagged tagged tagged : obj
Lean.Environment.addConstAsync._boxed (impure): obj tobj tagged tobj tagged tagged tagged : obj
Lean.Environment.containsOnBranch: @& obj @& tobj : u8
Lean.Environment.containsOnBranch (impure): @& obj @& tobj : UInt8
Lean.Environment.containsOnBranch._boxed: obj tobj : tagged
Lean.Environment.containsOnBranch._boxed (impure): obj tobj : tagged
Lean.Environment.enableRealizationsForConst: obj obj tobj void : obj
Lean.Environment.enableRealizationsForConst (impure): obj obj tobj lcVoid : obj
Lean.Environment.enableRealizationsForConst._boxed: obj obj tobj tagged : obj
Lean.Environment.enableRealizationsForConst._boxed (impure): obj obj tobj tagged : obj
Lean.Environment.find?: obj tobj u8 : tobj
Lean.Environment.find? (impure): obj tobj UInt8 : tobj
Lean.Environment.find?._boxed: obj tobj tagged : tobj
Lean.Environment.find?._boxed (impure): obj tobj tagged : tobj
Lean.Environment.findAsync?: obj tobj u8 : tobj
Lean.Environment.findAsync? (impure): obj tobj UInt8 : tobj
Lean.Environment.findAsync?._boxed: obj tobj tagged : tobj
Lean.Environment.findAsync?._boxed (impure): obj tobj tagged : tobj
Lean.Environment.findConstVal?: obj tobj u8 : tobj
Lean.Environment.findConstVal? (impure): obj tobj UInt8 : tobj
Lean.Environment.findConstVal?._boxed: obj tobj tagged : tobj
Lean.Environment.findConstVal?._boxed (impure): obj tobj tagged : tobj
Lean.Environment.findTask: obj tobj u8 : obj
Lean.Environment.findTask (impure): obj tobj UInt8 : obj
Lean.Environment.findTask._boxed: obj tobj tagged : obj
Lean.Environment.findTask._boxed (impure): obj tobj tagged : obj
Lean.Environment.getLocalConstantInfos: @& obj u8 void : obj
Lean.Environment.getLocalConstantInfos (impure): @& obj UInt8 lcVoid : obj
Lean.Environment.getLocalConstantInfos._boxed: obj tagged tagged : obj
Lean.Environment.getLocalConstantInfos._boxed (impure): obj tagged tagged : obj
Lean.Environment.realizeValue: ◾ obj obj tobj obj tobj tobj obj void : obj
Lean.Environment.realizeValue (impure): lcErased obj obj tobj obj tobj tobj obj lcVoid : obj
Lean.Environment.realizeValue._redArg: obj obj tobj obj tobj tobj obj void : obj
Lean.Environment.realizeValue._redArg (impure): obj obj tobj obj tobj tobj obj lcVoid : obj
Lean.Environment.realizeValue._boxed: tobj obj obj tobj obj tobj tobj obj tagged : obj
Lean.Environment.realizeValue._boxed (impure): tobj obj obj tobj obj tobj tobj obj tagged : obj
Lean.Environment.realizeValue._redArg._boxed: obj obj tobj obj tobj tobj obj tagged : obj
Lean.Environment.realizeValue._redArg._boxed (impure): obj obj tobj obj tobj tobj obj tagged : obj
Lean.Environment.toKernelEnv: obj : obj
Lean.Environment.toKernelEnv (impure): obj : obj
Lean.finalizeImport: @& obj obj obj u32 u8 u8 u8 u8 u8 void : obj
Lean.finalizeImport (impure): @& obj obj obj UInt32 UInt8 UInt8 UInt8 UInt8 UInt8 lcVoid : obj
Lean.finalizeImport._boxed: obj obj obj tobj tagged tagged tagged tagged tagged tagged : obj
Lean.finalizeImport._boxed (impure): obj obj obj tobj tagged tagged tagged tagged tagged tagged : obj
Lean.importModules: obj obj u32 obj u8 u8 u8 tobj void : obj
Lean.importModules (impure): obj obj UInt32 obj UInt8 UInt8 UInt8 tobj lcVoid : obj
Lean.importModules._boxed: obj obj tobj obj tagged tagged tagged tobj tagged : obj
Lean.importModules._boxed (impure): obj obj tobj obj tagged tagged tagged tobj tagged : obj
Lean.mkModuleData: obj u8 @& tobj void : obj
Lean.mkModuleData (impure): obj UInt8 @& tobj lcVoid : obj
Lean.mkModuleData._boxed: obj tagged tobj tagged : obj
Lean.mkModuleData._boxed (impure): obj tagged tobj tagged : obj
Lean.KeyedDeclsAttribute.getEntries: ◾ @& obj obj @& tobj : tobj
Lean.KeyedDeclsAttribute.getEntries (impure): lcErased @& obj obj @& tobj : tobj
Lean.KeyedDeclsAttribute.getEntries._redArg: @& obj obj @& tobj : tobj
Lean.KeyedDeclsAttribute.getEntries._redArg (impure): @& obj obj @& tobj : tobj
Lean.KeyedDeclsAttribute.getEntries._boxed: tobj obj obj tobj : tobj
Lean.KeyedDeclsAttribute.getEntries._boxed (impure): tobj obj obj tobj : tobj
Lean.KeyedDeclsAttribute.getEntries._redArg._boxed: obj obj tobj : tobj
Lean.KeyedDeclsAttribute.getEntries._redArg._boxed (impure): obj obj tobj : tobj
Lean.KeyedDeclsAttribute.addBuiltin: ◾ @& obj tobj tobj tobj void : obj
Lean.KeyedDeclsAttribute.addBuiltin (impure): lcErased @& obj tobj tobj tobj lcVoid : obj
Lean.KeyedDeclsAttribute.addBuiltin._redArg: @& obj tobj tobj tobj void : obj
Lean.KeyedDeclsAttribute.addBuiltin._redArg (impure): @& obj tobj tobj tobj lcVoid : obj
Lean.KeyedDeclsAttribute.addBuiltin._boxed: tobj obj tobj tobj tobj tagged : obj
Lean.KeyedDeclsAttribute.addBuiltin._boxed (impure): tobj obj tobj tobj tobj tagged : obj
Lean.KeyedDeclsAttribute.addBuiltin._redArg._boxed: obj tobj tobj tobj tagged : obj
Lean.KeyedDeclsAttribute.addBuiltin._redArg._boxed (impure): obj tobj tobj tobj tagged : obj
Lean.Meta.isProofQuick: obj @& obj @& tobj @& obj @& tobj void : obj
Lean.Meta.isProofQuick (impure): obj @& obj @& tobj @& obj @& tobj lcVoid : obj
Lean.Meta.isProofQuick._boxed: obj obj tobj obj tobj tagged : obj
Lean.Meta.isProofQuick._boxed (impure): obj obj tobj obj tobj tagged : obj
Lean.Meta.synthInstance: obj tobj @& obj @& tobj @& obj @& tobj void : obj
Lean.Meta.synthInstance (impure): obj tobj @& obj @& tobj @& obj @& tobj lcVoid : obj
Lean.Meta.synthInstance._boxed: obj tobj obj tobj obj tobj tagged : obj
Lean.Meta.synthInstance._boxed (impure): obj tobj obj tobj obj tobj tagged : obj
Lean.Meta.synthInstanceCore?: obj tobj @& obj @& tobj @& obj @& tobj void : obj
Lean.Meta.synthInstanceCore? (impure): obj tobj @& obj @& tobj @& obj @& tobj lcVoid : obj
Lean.Meta.synthInstanceCore?._boxed: obj tobj obj tobj obj tobj tagged : obj
Lean.Meta.synthInstanceCore?._boxed (impure): obj tobj obj tobj obj tobj tagged : obj
Lean.ResolveName.resolveGlobalName: obj @& obj tobj tobj tobj : tobj
Lean.ResolveName.resolveGlobalName (impure): obj @& obj tobj tobj tobj : tobj
Lean.ResolveName.resolveGlobalName._boxed: obj obj tobj tobj tobj : tobj
Lean.ResolveName.resolveGlobalName._boxed (impure): obj obj tobj tobj tobj : tobj
Lean.ResolveName.resolveNamespace: obj tobj tobj tobj : tobj
Lean.ResolveName.resolveNamespace (impure): obj tobj tobj tobj : tobj
Lean.resolveNamespace: ◾ obj obj obj obj tobj : tobj
Lean.resolveNamespace (impure): lcErased obj obj obj obj tobj : tobj
Lean.resolveNamespace._redArg: obj obj obj obj tobj : tobj
Lean.resolveNamespace._redArg (impure): obj obj obj obj tobj : tobj
Lean.ScopedEnvExtension.addImportedFn: ◾ ◾ ◾ obj @& obj @& obj void : obj
Lean.ScopedEnvExtension.addImportedFn (impure): lcErased lcErased lcErased obj @& obj @& obj lcVoid : obj
Lean.ScopedEnvExtension.addImportedFn._redArg: obj @& obj @& obj void : obj
Lean.ScopedEnvExtension.addImportedFn._redArg (impure): obj @& obj @& obj lcVoid : obj
Lean.ScopedEnvExtension.addImportedFn._boxed: tobj tobj tobj obj obj obj tagged : obj
Lean.ScopedEnvExtension.addImportedFn._boxed (impure): tobj tobj tobj obj obj obj tagged : obj
Lean.ScopedEnvExtension.addImportedFn._redArg._boxed: obj obj obj tagged : obj
Lean.ScopedEnvExtension.addImportedFn._redArg._boxed (impure): obj obj obj tagged : obj
Lean.ScopedEnvExtension.getState: ◾ ◾ ◾ @& tobj @& obj obj @& tobj : tobj
Lean.ScopedEnvExtension.getState (impure): lcErased lcErased lcErased @& tobj @& obj obj @& tobj : tobj
Lean.ScopedEnvExtension.getState._redArg: @& tobj @& obj obj @& tobj : tobj
Lean.ScopedEnvExtension.getState._redArg (impure): @& tobj @& obj obj @& tobj : tobj
Lean.ScopedEnvExtension.getState._boxed: tobj tobj tobj tobj obj obj tobj : tobj
Lean.ScopedEnvExtension.getState._boxed (impure): tobj tobj tobj tobj obj obj tobj : tobj
Lean.ScopedEnvExtension.getState._redArg._boxed: tobj obj obj tobj : tobj
Lean.ScopedEnvExtension.getState._redArg._boxed (impure): tobj obj obj tobj : tobj
Lean.Server.dedupReferences: @& obj u8 : obj
Lean.Server.dedupReferences (impure): @& obj UInt8 : obj
Lean.Server.dedupReferences._boxed: obj tagged : obj
Lean.Server.dedupReferences._boxed (impure): obj tagged : obj
Lean.Server.getModuleContainingDecl?: @& obj @& tobj : tobj
Lean.Server.getModuleContainingDecl? (impure): @& obj @& tobj : tobj
Lean.Server.getModuleContainingDecl?._boxed: obj tobj : tobj
Lean.Server.getModuleContainingDecl?._boxed (impure): obj tobj : tobj
Lean.instFromJsonModuleArtifacts.fromJson: tobj : obj
Lean.instFromJsonModuleArtifacts.fromJson (impure): tobj : obj
Lean.instToJsonModuleArtifacts.toJson: obj : tobj
Lean.instToJsonModuleArtifacts.toJson (impure): obj : tobj
Lean.instToJsonModuleSetup.toJson: obj : tobj
Lean.instToJsonModuleSetup.toJson (impure): obj : tobj
Lean.Expr.instantiateLevelParams: @& obj tobj tobj : obj
Lean.Expr.instantiateLevelParams (impure): @& obj tobj tobj : obj
Lean.Expr.instantiateLevelParams._boxed: obj tobj tobj : obj
Lean.Expr.instantiateLevelParams._boxed (impure): obj tobj tobj : obj
Lean.SearchPath.findWithExt: tobj @& obj tobj void : obj
Lean.SearchPath.findWithExt (impure): tobj @& obj tobj lcVoid : obj
Lean.SearchPath.findWithExt._boxed: tobj obj tobj tagged : obj
Lean.SearchPath.findWithExt._boxed (impure): tobj obj tobj tagged : obj
Lean.findLean: tobj tobj void : obj
Lean.findLean (impure): tobj tobj lcVoid : obj
Lean.findLean._boxed: tobj tobj tagged : obj
Lean.findLean._boxed (impure): tobj tobj tagged : obj
Lean.findOLean: tobj void : obj
Lean.findOLean (impure): tobj lcVoid : obj
Lean.findOLean._boxed: tobj tagged : obj
Lean.findOLean._boxed (impure): tobj tagged : obj
Lean.moduleNameOfFileName: obj tobj void : obj
Lean.moduleNameOfFileName (impure): obj tobj lcVoid : obj
Lean.moduleNameOfFileName._boxed: obj tobj tagged : obj
Lean.moduleNameOfFileName._boxed (impure): obj tobj tagged : obj
Lean.Meta.realizeValue: ◾ ◾ obj obj tobj tobj tobj tobj obj @& obj @& tobj @& obj @& tobj void : obj
Lean.Meta.realizeValue (impure): lcErased lcErased obj obj tobj tobj tobj tobj obj @& obj @& tobj @& obj @& tobj lcVoid : obj
Lean.Meta.realizeValue._redArg: obj obj tobj tobj tobj tobj obj @& obj @& tobj @& obj @& tobj void : obj
Lean.Meta.realizeValue._redArg (impure): obj obj tobj tobj tobj tobj obj @& obj @& tobj @& obj @& tobj lcVoid : obj
Lean.Meta.realizeValue._boxed: tobj tobj obj obj tobj tobj tobj tobj obj obj tobj obj tobj tagged : obj
Lean.Meta.realizeValue._boxed (impure): tobj tobj obj obj tobj tobj tobj tobj obj obj tobj obj tobj tagged : obj
Lean.Meta.realizeValue._redArg._boxed: obj obj tobj tobj tobj tobj obj obj tobj obj tobj tagged : obj
Lean.Meta.realizeValue._redArg._boxed (impure): obj obj tobj tobj tobj tobj obj obj tobj obj tobj tagged : obj
Lean.IR.findEnvDecl: obj tobj : tobj
Lean.IR.findEnvDecl (impure): obj tobj : tobj
Lean.Meta.SynthInstance.getInstances: obj @& obj @& tobj @& obj @& tobj void : obj
Lean.Meta.SynthInstance.getInstances (impure): obj @& obj @& tobj @& obj @& tobj lcVoid : obj
Lean.Meta.SynthInstance.getInstances._boxed: obj obj tobj obj tobj tagged : obj
Lean.Meta.SynthInstance.getInstances._boxed (impure): obj obj tobj obj tobj tagged : obj
Lean.Environment.realizeConst: obj tobj tobj obj void : obj
Lean.Environment.realizeConst (impure): obj tobj tobj obj lcVoid : obj
Lean.Environment.realizeConst._boxed: obj tobj tobj obj tagged : obj
Lean.Environment.realizeConst._boxed (impure): obj tobj tobj obj tagged : obj
Lean.Compiler.LCNF.main: obj obj @& obj @& tobj void : obj
Lean.Compiler.LCNF.main (impure): obj obj @& obj @& tobj lcVoid : obj
Lean.Compiler.LCNF.main._boxed: obj obj obj tobj tagged : obj
Lean.Compiler.LCNF.main._boxed (impure): obj obj obj tobj tagged : obj
Lean.instFromJsonModuleSetup.fromJson: tobj : obj
Lean.instFromJsonModuleSetup.fromJson (impure): tobj : obj
Lean.Environment.evalConst: ◾ @& obj @& obj @& tobj u8 : obj
Lean.Environment.evalConst (impure): lcErased @& obj @& obj @& tobj UInt8 : obj
Lean.Environment.evalConst._redArg: @& obj @& obj @& tobj u8 : obj
Lean.Environment.evalConst._redArg (impure): @& obj @& obj @& tobj UInt8 : obj
Lean.Environment.evalConst._boxed: tobj obj obj tobj tagged : obj
Lean.Environment.evalConst._boxed (impure): tobj obj obj tobj tagged : obj
Lean.Environment.evalConst._redArg._boxed: obj obj tobj tagged : obj
Lean.Environment.evalConst._redArg._boxed (impure): obj obj tobj tagged : obj
Lean.Meta.inferTypeImp: obj obj tobj obj tobj void : obj
Lean.Meta.inferTypeImp (impure): obj obj tobj obj tobj lcVoid : obj
Lean.Meta.inferTypeImp._boxed: obj obj tobj obj tobj tagged : obj
Lean.Meta.inferTypeImp._boxed (impure): obj obj tobj obj tobj tagged : obj
Lean.Meta.whnfImp: obj obj tobj obj tobj void : obj
Lean.Meta.whnfImp (impure): obj obj tobj obj tobj lcVoid : obj
Lean.Meta.whnfImp._boxed: obj obj tobj obj tobj tagged : obj
Lean.Meta.whnfImp._boxed (impure): obj obj tobj obj tobj tagged : obj
Lean.Elab.expandMacroImpl?: obj tobj @& obj obj : obj
Lean.Elab.expandMacroImpl? (impure): obj tobj @& obj obj : obj
Lean.Elab.expandMacroImpl?._boxed: obj tobj obj obj : obj
Lean.Elab.expandMacroImpl?._boxed (impure): obj tobj obj obj : obj
Lean.Elab.toAttributeKind: @& tobj @& obj obj : obj
Lean.Elab.toAttributeKind (impure): @& tobj @& obj obj : obj
Lean.Elab.toAttributeKind._boxed: tobj obj obj : obj
Lean.Elab.toAttributeKind._boxed (impure): tobj obj obj : obj
Lean.Elab.Term.elabWithDeclName: tobj tobj @& obj @& tobj @& obj @& tobj @& obj @& tobj void : obj
Lean.Elab.Term.elabWithDeclName (impure): tobj tobj @& obj @& tobj @& obj @& tobj @& obj @& tobj lcVoid : obj
Lean.Elab.Term.elabWithDeclName._boxed: tobj tobj obj tobj obj tobj obj tobj tagged : obj
Lean.Elab.Term.elabWithDeclName._boxed (impure): tobj tobj obj tobj obj tobj obj tobj tagged : obj
Lean.ModuleSetup.load: @& obj void : obj
Lean.ModuleSetup.load (impure): @& obj lcVoid : obj
Lean.ModuleSetup.load._boxed: obj tagged : obj
Lean.ModuleSetup.load._boxed (impure): obj tagged : obj
Lean.Meta.getFunInfo: obj tobj @& obj @& tobj @& obj @& tobj void : obj
Lean.Meta.getFunInfo (impure): obj tobj @& obj @& tobj @& obj @& tobj lcVoid : obj
Lean.Meta.getFunInfo._boxed: obj tobj obj tobj obj tobj tagged : obj
Lean.Meta.getFunInfo._boxed (impure): obj tobj obj tobj obj tobj tagged : obj
Lean.Meta.getFunInfoNArgs: obj tobj @& obj @& tobj @& obj @& tobj void : obj
Lean.Meta.getFunInfoNArgs (impure): obj tobj @& obj @& tobj @& obj @& tobj lcVoid : obj
Lean.Meta.getFunInfoNArgs._boxed: obj tobj obj tobj obj tobj tagged : obj
Lean.Meta.getFunInfoNArgs._boxed (impure): obj tobj obj tobj obj tobj tagged : obj
Lean.registerScopedEnvExtensionUnsafe: ◾ ◾ ◾ obj void : obj
Lean.registerScopedEnvExtensionUnsafe (impure): lcErased lcErased lcErased obj lcVoid : obj
Lean.registerScopedEnvExtensionUnsafe._redArg: obj void : obj
Lean.registerScopedEnvExtensionUnsafe._redArg (impure): obj lcVoid : obj
Lean.registerScopedEnvExtensionUnsafe._boxed: tobj tobj tobj obj tagged : obj
Lean.registerScopedEnvExtensionUnsafe._boxed (impure): tobj tobj tobj obj tagged : obj
Lean.registerScopedEnvExtensionUnsafe._redArg._boxed: obj tagged : obj
Lean.registerScopedEnvExtensionUnsafe._redArg._boxed (impure): obj tagged : obj
Lake.Module.inputFacetConfig:  : obj
Lake.Module.inputFacetConfig (impure):  : obj
Lake.Module.leanArtsFacetConfig:  : obj
Lake.Module.leanArtsFacetConfig (impure):  : obj
_private.Lake.Build.Module.0.Lake.Module.buildLean: obj obj obj @& tobj @& tobj @& tobj @& obj obj void : obj
_private.Lake.Build.Module.0.Lake.Module.buildLean (impure): obj obj obj @& tobj @& tobj @& tobj @& obj obj lcVoid : obj
_private.Lake.Build.Module.0.Lake.Module.buildLean._boxed: obj obj obj tobj tobj tobj obj obj tagged : obj
_private.Lake.Build.Module.0.Lake.Module.buildLean._boxed (impure): obj obj obj tobj tobj tobj obj obj tagged : obj
_private.Lake.Build.Module.0.Lake.Module.recBuildLean: obj obj @& tobj @& tobj @& tobj @& obj obj void : obj
_private.Lake.Build.Module.0.Lake.Module.recBuildLean (impure): obj obj @& tobj @& tobj @& tobj @& obj obj lcVoid : obj
_private.Lake.Build.Module.0.Lake.Module.recBuildLean._boxed: obj obj tobj tobj tobj obj obj tagged : obj
_private.Lake.Build.Module.0.Lake.Module.recBuildLean._boxed (impure): obj obj tobj tobj tobj obj obj tagged : obj
_private.Lake.Build.Module.0.Lake.Module.recFetchInput: obj obj @& tobj @& tobj @& tobj @& obj obj void : obj
_private.Lake.Build.Module.0.Lake.Module.recFetchInput (impure): obj obj @& tobj @& tobj @& tobj @& obj obj lcVoid : obj
_private.Lake.Build.Module.0.Lake.Module.recFetchInput._boxed: obj obj tobj tobj tobj obj obj tagged : obj
_private.Lake.Build.Module.0.Lake.Module.recFetchInput._boxed (impure): obj obj tobj tobj tobj obj obj tagged : obj
_private.Lake.CLI.Main.0.Lake.lakeCli: obj tobj obj void : obj
_private.Lake.CLI.Main.0.Lake.lakeCli (impure): obj tobj obj lcVoid : obj
_private.Lake.CLI.Main.0.Lake.lakeCli._boxed: obj tobj obj tagged : obj
_private.Lake.CLI.Main.0.Lake.lakeCli._boxed (impure): obj tobj obj tagged : obj
_private.Lean.Environment.0.Lean.EnvExtension.getStateUnsafe: ◾ @& tobj @& obj obj @& tobj tobj : tobj
_private.Lean.Environment.0.Lean.EnvExtension.getStateUnsafe (impure): lcErased @& tobj @& obj obj @& tobj tobj : tobj
_private.Lean.Environment.0.Lean.EnvExtension.getStateUnsafe._redArg: @& tobj @& obj obj @& tobj tobj : tobj
_private.Lean.Environment.0.Lean.EnvExtension.getStateUnsafe._redArg (impure): @& tobj @& obj obj @& tobj tobj : tobj
_private.Lean.Environment.0.Lean.EnvExtension.getStateUnsafe._boxed: tobj tobj obj obj tobj tobj : tobj
_private.Lean.Environment.0.Lean.EnvExtension.getStateUnsafe._boxed (impure): tobj tobj obj obj tobj tobj : tobj
_private.Lean.Environment.0.Lean.EnvExtension.getStateUnsafe._redArg._boxed: tobj obj obj tobj tobj : tobj
_private.Lean.Environment.0.Lean.EnvExtension.getStateUnsafe._redArg._boxed (impure): tobj obj obj tobj tobj : tobj
_private.Lean.Meta.FunInfo.0.Lean.Meta.getFunInfoAux: obj tobj @& obj @& tobj @& obj @& tobj void : obj
_private.Lean.Meta.FunInfo.0.Lean.Meta.getFunInfoAux (impure): obj tobj @& obj @& tobj @& obj @& tobj lcVoid : obj
_private.Lean.Meta.FunInfo.0.Lean.Meta.getFunInfoAux._boxed: obj tobj obj tobj obj tobj tagged : obj
_private.Lean.Meta.FunInfo.0.Lean.Meta.getFunInfoAux._boxed (impure): obj tobj obj tobj obj tobj tagged : obj
_private.Lake.Build.Library.0.Lake.LeanLib.recCollectLocalModules: obj obj @& tobj @& tobj @& tobj @& obj obj void : obj
_private.Lake.Build.Library.0.Lake.LeanLib.recCollectLocalModules (impure): obj obj @& tobj @& tobj @& tobj @& obj obj lcVoid : obj
_private.Lake.Build.Library.0.Lake.LeanLib.recCollectLocalModules._boxed: obj obj tobj tobj tobj obj obj tagged : obj
_private.Lake.Build.Library.0.Lake.LeanLib.recCollectLocalModules._boxed (impure): obj obj tobj tobj tobj obj obj tagged : obj
_private.Lean.Meta.SynthInstance.0.Lean.Meta.cacheResult: obj u8 tobj tobj @& obj @& tobj @& obj @& tobj void : obj
_private.Lean.Meta.SynthInstance.0.Lean.Meta.cacheResult (impure): obj UInt8 tobj tobj @& obj @& tobj @& obj @& tobj lcVoid : obj
_private.Lean.Meta.SynthInstance.0.Lean.Meta.cacheResult._redArg: obj u8 tobj tobj @& tobj void : obj
_private.Lean.Meta.SynthInstance.0.Lean.Meta.cacheResult._redArg (impure): obj UInt8 tobj tobj @& tobj lcVoid : obj
_private.Lean.Meta.SynthInstance.0.Lean.Meta.cacheResult._boxed: obj tagged tobj tobj obj tobj obj tobj tagged : obj
_private.Lean.Meta.SynthInstance.0.Lean.Meta.cacheResult._boxed (impure): obj tagged tobj tobj obj tobj obj tobj tagged : obj
_private.Lean.Meta.SynthInstance.0.Lean.Meta.cacheResult._redArg._boxed: obj tagged tobj tobj tobj tagged : obj
_private.Lean.Meta.SynthInstance.0.Lean.Meta.cacheResult._redArg._boxed (impure): obj tagged tobj tobj tobj tagged : obj
_private.Lean.Meta.WHNF.0.Lean.Meta.cache: u8 obj obj @& obj @& tobj @& obj @& tobj void : obj
_private.Lean.Meta.WHNF.0.Lean.Meta.cache (impure): UInt8 obj obj @& obj @& tobj @& obj @& tobj lcVoid : obj
_private.Lean.Meta.WHNF.0.Lean.Meta.cache._redArg: u8 obj obj @& obj @& tobj void : obj
_private.Lean.Meta.WHNF.0.Lean.Meta.cache._redArg (impure): UInt8 obj obj @& obj @& tobj lcVoid : obj
_private.Lean.Meta.WHNF.0.Lean.Meta.cache._boxed: tagged obj obj obj tobj obj tobj tagged : obj
_private.Lean.Meta.WHNF.0.Lean.Meta.cache._boxed (impure): tagged obj obj obj tobj obj tobj tagged : obj
_private.Lean.Meta.WHNF.0.Lean.Meta.cache._redArg._boxed: tagged obj obj obj tobj tagged : obj
_private.Lean.Meta.WHNF.0.Lean.Meta.cache._redArg._boxed (impure): tagged obj obj obj tobj tagged : obj
_private.Lean.Elab.Term.TermElabM.0.Lean.Elab.Term.elabUsingElabFnsAux: obj tobj tobj u8 tobj @& obj @& tobj @& obj @& tobj @& obj @& tobj void : obj
_private.Lean.Elab.Term.TermElabM.0.Lean.Elab.Term.elabUsingElabFnsAux (impure): obj tobj tobj UInt8 tobj @& obj @& tobj @& obj @& tobj @& obj @& tobj lcVoid : obj
_private.Lean.Elab.Term.TermElabM.0.Lean.Elab.Term.elabUsingElabFnsAux._boxed: obj tobj tobj tagged tobj obj tobj obj tobj obj tobj tagged : obj
_private.Lean.Elab.Term.TermElabM.0.Lean.Elab.Term.elabUsingElabFnsAux._boxed (impure): obj tobj tobj tagged tobj obj tobj obj tobj obj tobj tagged : obj
_private.Lean.Environment.0.Lean.finalizePersistentExtensions: obj obj obj void : obj
_private.Lean.Environment.0.Lean.finalizePersistentExtensions (impure): obj obj obj lcVoid : obj
_private.Lean.Environment.0.Lean.finalizePersistentExtensions._boxed: obj obj obj tagged : obj
_private.Lean.Environment.0.Lean.finalizePersistentExtensions._boxed (impure): obj obj obj tagged : obj
_private.Lean.Environment.0.Lean.Environment.modifyCheckedAsync: obj obj : obj
_private.Lean.Environment.0.Lean.Environment.modifyCheckedAsync (impure): obj obj : obj
_private.Lake.CLI.Main.0.Lake.lake: tobj obj void : obj
_private.Lake.CLI.Main.0.Lake.lake (impure): tobj obj lcVoid : obj
_private.Lake.CLI.Main.0.Lake.lake._boxed: tobj obj tagged : obj
_private.Lake.CLI.Main.0.Lake.lake._boxed (impure): tobj obj tagged : obj
EOF2
# (the declarations of functions and variables of other modules, normalized)
externals() {
  grep -E '^(extern )?[a-z_0-9]+\*? (l|lean)_[A-Za-z0-9_]+(\(.*\))?;$' "$1" | sed -E 's/^extern //' | sort -u
}
cp inline_abi.lean "$TMP_DIR/"
cd "$TMP_DIR"
lean Callers.lean -c Callers.c > callers.out 2>&1 || fail "Callers.lean failed: $(cat callers.out)"
externals Callers.c > callers.produced.out
$DIFF -- callers.expected.out callers.produced.out ||
  fail "the compiled callers refer to other functions than those official Lean has"
# (the same callers where more is inlined)
for t in 10 100; do
  sed "s/^open Lean Meta Elab$/open Lean Meta Elab\nset_option compiler.small $t/" Callers.lean > Callers$t.lean
  lean Callers$t.lean -c Callers$t.c > callers$t.out 2>&1 || fail "Callers$t.lean failed: $(cat callers$t.out)"
  externals Callers$t.c > callers$t.produced.out
  $DIFF -- callers$t.expected.out callers$t.produced.out ||
    fail "under compiler.small $t, the compiled callers refer to other functions than those official Lean has"
done
lean Mod.lean -c Mod.c > mod.out 2>&1 || fail "Mod.lean failed: $(cat mod.out)"
externals Mod.c > mod.produced.out
$DIFF -- mod.expected.out mod.produced.out ||
  fail "the compiled module refers to other functions than those official Lean has"
lean inline_abi.lean > inline_abi.produced.out 2>&1 || fail "inline_abi.lean failed: $(cat inline_abi.produced.out)"
$DIFF -- inline_abi.expected.out inline_abi.produced.out ||
  fail "a body of Lean's that importers compile reaches PaperLean's code, or a calling convention changed"
