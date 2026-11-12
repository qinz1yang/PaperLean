# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# A non-`meta` definition of type `Syntax` in a module cannot be evaluated by the
# interpreter, so `evalSyntaxConstant` must fail for it even when the definition happens
# to have the shape of a `quoteAutoTactic` value.  `QuotedSyntax.ofConstant?` must not
# return the value without `evalCheckMeta`'s last-line `getIRPhases` check.

cd "$TMP_DIR"
cat > M.lean <<'EOF2'
module
import Lean
open Lean

def myTac : Syntax :=
  Syntax.node SourceInfo.none
    (Name.str (Name.str (Name.str (Name.str Name.anonymous "Lean") "Parser") "Tactic") "tacticTrivial")
    (Array.empty : Array Syntax)

theorem withTac (h : autoParam True myTac) : True := h
example : True := withTac
EOF2
capture_fail lean M.lean
check_out_contains 'neither marked nor imported as `meta`'
