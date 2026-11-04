/-
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.System.IO

-- (no `SizeOf` instances for PaperLean's types: an instance of a module of `Lean` would be one of
-- every environment that imports it, which Lean's searches would try)
set_option genSizeOf false
set_option genInjectivity false

public section

/-! Small system functions for the `paperlean` command (`src/paperlean/system.cpp`). -/

namespace Lean.PaperLean

@[extern "lean_paperlean_version"]
private opaque versionCore : Unit → String

/-- PaperLean's version: `<PaperLean version>-lean<Lean version>`, e.g. `0.1.0-lean4.35.0-rc3`. -/
def version : String := versionCore ()

@[extern "lean_paperlean_build"]
private opaque buildCore : Unit → String

/-- The build of PaperLean: the first 12 digits of its commit, followed by a hash of the uncommitted
changes if there are any (`src/paperlean/build_id.cmake`). -/
def build : String := buildCore ()

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

/-- The seconds since the epoch, as file times count them. -/
@[extern "lean_paperlean_wall_seconds"]
opaque wallSeconds : BaseIO Nat

/-- The bytes of physical memory, `0` if unknown. -/
@[extern "lean_paperlean_total_memory"]
opaque totalMemory : BaseIO Nat

@[extern "lean_paperlean_native_libs_available"]
private opaque nativeLibsAvailableCore : Unit → Bool

/-- Whether this build of Lean uses native libraries of packages (`src/paperlean/native_libs.cpp`):
on Linux and macOS. -/
def nativeLibsAvailable : Bool := nativeLibsAvailableCore ()

/-- The identity of the file at `path`, as olean packs record it: its device, inode, size, and the
seconds and nanoseconds of its modification and status change times, as 7 64-bit integers in the
machine's byte order (one `stat`); `none` if it cannot be read. Unlike a modification time, the
status change time cannot be set (`touch`, `cp -p`, `tar`). -/
@[extern "lean_paperlean_file_identity"]
opaque fileIdentity (path : @& String) : BaseIO (Option ByteArray)

/-- Limits the address space of this process to what it holds now and `extra` bytes more, or lifts that
limit if `extra` is `0`: allocations beyond it fail. It does nothing on other systems than Linux. -/
@[extern "lean_paperlean_limit_address_space"]
opaque limitAddressSpace (extra : USize) : BaseIO Unit

/-- The number of bytes available to this user on the file system of `path`. -/
@[extern "lean_paperlean_free_space"]
opaque freeSpace (path : @& String) : IO Nat

end Lean.PaperLean
