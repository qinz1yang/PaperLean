/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.PaperLean.NativeLibs

@[extern "lean_paperlean_portable_c_symbol_guard"]
opaque guardCustomSymbols (bytes : @& ByteArray) (names : @& Array String) : Option String

def main : IO Unit := do
  let c ← IO.FS.readFile "Example.c"
  let data ← Lean.PaperLean.moduleNativeData #["Example.olean"]
  unless data.exports == #["paperlean_fixture_own"] do
    throw <| IO.userError s!"unexpected export metadata {data.exports}"
  let some guard := guardCustomSymbols c.toUTF8 data.exports
    | throw <| IO.userError "generated custom export was excluded"
  unless (guardCustomSymbols c.toUTF8 (data.exports ++ #["assert", "printf"])) == some guard do
    throw <| IO.userError "an unused declaration changed the compiler guard"
  IO.FS.writeFile "safe.h" guard
  for bad in #["__FILE__", "_Pragma", "__builtin_FILE", "asm"] do
    let source := c.replace "paperlean_fixture_own" bad
    if (guardCustomSymbols source.toUTF8 #[bad]).isSome then
      throw <| IO.userError s!"reserved extern accepted: {bad}"
  for bad in #["#include \"adjacent.h\"\n", "#define P(x, y) x ## y\n",
      "int v_a(void) <% return 1; %>\n",
      "int v_a(void) { return 1'000 + sizeof(__FILE__) + 1'000; }\n"] do
    let footer := "#ifdef __cplusplus\n}\n#endif"
    let source := c.replace footer (bad ++ footer)
    if source == c || (guardCustomSymbols source.toUTF8 data.exports).isSome then
      throw <| IO.userError "unexpected acceptance of noncanonical C"
  let used := c.replace "paperlean_fixture_own" "assert"
  let some macroGuard := guardCustomSymbols used.toUTF8 #["assert"]
    | throw <| IO.userError "expected a compiler guard for the used extern"
  IO.FS.writeFile "macro.c" used
  IO.FS.writeFile "macro.h" macroGuard

  let math ← IO.FS.readFile "MathFixture.c"
  -- These symbols come from imported Init declarations; MathFixture does not declare any externs.
  let some mathGuard := guardCustomSymbols math.toUTF8 #[]
    | throw <| IO.userError "a standard Init floating-point call was excluded"
  IO.FS.writeFile "math.h" mathGuard
  for name in #["pow", "sqrt", "ceil", "floor", "floorf"] do
    unless mathGuard.contains s!"lean_paperlean_stdmath_{name}\"" do
      throw <| IO.userError s!"unbound math symbol: {name}"
  let proto := "double pow(double, double);"
  for altered in #[
      "double pow(double);",
      "double pow(double, double) {return 0;}",
      "extern double (*pow)(double, double);",
      "double lean_paperlean_stdmath_pow(double, double);",
      ""] do
    let source := math.replace proto altered
    if source == math || (guardCustomSymbols source.toUTF8 #["pow"]).isSome then
      throw <| IO.userError s!"untrusted math definition or prototype passed: {altered}"
  let footer := "#ifdef __cplusplus\n}\n#endif"
  let foreign := math.replace footer ("double (*v_function)(double, double) = pow;\n" ++ footer)
  if math == foreign || (guardCustomSymbols foreign.toUTF8 #["pow"]).isSome then
    throw <| IO.userError "address of a reserved math function passed"
