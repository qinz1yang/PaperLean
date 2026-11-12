import Lean
open Lean

/-- `Lean.Compiler.LCNF.Specialize.CacheEntry` (the extension is private to its module, so the entries
are read from the module files). -/
structure CacheEntry where
  key : Expr
  declName : Name

/-- The specialization cache entries (`specCacheExt`) that the toolchain's own module files hold, as
`module <TAB> specialization <TAB> Name.hash` lines, written to the file given as the first argument; the library
directory (`lib/lean` of the toolchain) is the second. -/
unsafe def main (args : List String) : IO Unit := do
  let out := args[0]!
  let lib : System.FilePath := args[1]!
  let ext := `Lean.Compiler.LCNF.Specialize.specCacheExt
  let mut lines : Array String := #[]
  let mut nfiles := 0
  for root in ["Init", "Std", "Lean", "Lake"] do
    let files ← (lib / root).walkDir
    for f in files do
      let s := f.toString
      unless s.endsWith ".olean" do continue
      let rel := (s.drop (lib.toString.length + 1)).toString
      let mod := (rel.replace ".olean" "").replace "/" "."
      -- the parts of the module, in order (later parts refer to objects of earlier ones)
      let mut parts := #[f]
      for sfx in [".olean.server", ".olean.private"] do
        let g : System.FilePath := s.replace ".olean" sfx
        if ← g.pathExists then parts := parts.push g
      let datas ← readModuleDataParts parts
      nfiles := nfiles + 1
      for (data, _) in datas do
        for (n, es) in data.entries do
          -- (the extension is private to its module, so its name may be mangled)
          if n == ext || (n.toString.endsWith "specCacheExt" && (`Lean.Compiler.LCNF.Specialize).isPrefixOf n.eraseMacroScopes || n.toString.endsWith ".specCacheExt") then
            for e in es do
              let ce : CacheEntry := unsafeCast e
              lines := lines.push s!"{mod}\t{ce.declName}\t{ce.declName.hash}"
  IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"{lines.size} entries from {nfiles} files"
