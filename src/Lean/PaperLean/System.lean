/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.System.IO

public section

/-! Small system functions for the `paperlean` command (`src/paperlean/system.cpp`). -/

namespace Lean.PaperLean

@[extern "lean_paperlean_version"]
private opaque versionCore : Unit → String

/-- PaperLean's version: `<PaperLean version>-lean<Lean version>`, e.g. `0.1.0-lean4.35.0-rc3`. -/
def version : String := versionCore ()

/-- Sets the variable `name` of this process to `value`, or unsets it; processes started later
inherit it. -/
@[extern "lean_paperlean_set_env"]
opaque setEnv (name : @& String) (value : @& Option String) : BaseIO Unit

/-- Whether a process with id `pid` exists. -/
@[extern "lean_paperlean_process_alive"]
opaque processAlive (pid : UInt32) : BaseIO Bool

/-- The number of hardware threads. -/
@[extern "lean_paperlean_num_cpus"]
opaque numCPUs : BaseIO Nat

/-- The bytes of physical memory, `0` if unknown. -/
@[extern "lean_paperlean_total_memory"]
opaque totalMemory : BaseIO Nat

@[extern "lean_paperlean_native_libs_available"]
private opaque nativeLibsAvailableCore : Unit → Bool

/-- Whether this build of Lean uses native libraries of packages (`src/paperlean/native_libs.cpp`):
on Linux and macOS. -/
def nativeLibsAvailable : Bool := nativeLibsAvailableCore ()

/-- The number of bytes available to this user on the file system of `path`. -/
@[extern "lean_paperlean_free_space"]
opaque freeSpace (path : @& String) : IO Nat

end Lean.PaperLean
