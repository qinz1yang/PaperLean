# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Both outer module jobs are registered before a sibling build starts. They must
# acquire and release their own one-slot scheduler while the sibling stays active.
cd "$TMP_DIR"
mkdir -p Root
export LAKE_ARTIFACT_CACHE=false PAPERLEAN_ACCELERATE=1 PAPERLEAN_SCHEDULE_SLOTS=1
export PAPERLEAN_BUILD_PACKS=0
cat > lakefile.lean <<'END'
import Lake
open Lake
open Lake DSL
package overlap
lean_lib Root

private def awaitBoth (left right : System.FilePath) (timeout : Nat) : IO Bool := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) - start < timeout do
    if (← left.pathExists) && (← right.pathExists) then return true
    IO.sleep 20
  return false

script overlapTest do
  let ws ← getWorkspace
  let some root := ws.findModule? `Root | error "missing Root"
  let task ← IO.asTask <| ws.runBuild (root.leanArts.fetch)
  let base := ws.dir / "started"
  unless ← awaitBoth base base 30000 do error "outer build did not start"
  let result ← ws.runBuild do
    IO.FS.writeFile (ws.dir / "continue") "ok"
    let done ← awaitBoth (ws.root.leanLibDir / "Root/A.olean") (ws.root.leanLibDir / "Root/B.olean") 20000
    return Job.pure done
  IO.ofExcept (← IO.wait task) >>= fun _ => pure ()
  unless result do error "outer module jobs could not both finish before the nested run released the scheduler"
  return 0
END
cat > Root/Base.lean <<'END'
import Lean
run_cmd do
  IO.FS.writeFile "started" "ok"
  let start ← IO.monoMsNow
  while !(← System.FilePath.pathExists "continue") do
    if (← IO.monoMsNow) - start > 30000 then throwError "outer timed out"
    IO.sleep 20
def base : Nat := 0
END
cat > Root/A.lean <<'END'
import Root.Base
def a := base + 1
END
cat > Root/B.lean <<'END'
import Root.Base
def b := base + 2
END
cat > Root.lean <<'END'
import Root.A
import Root.B
END
run lake run overlapTest
