# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# The compiler processes that PaperLean runs at once by default (`paperlean prepare` and the
# preparation during `paperlean build`, `autoJobs`: one per CPU and per 2 GB of memory) follow what
# this process may use, not the machine: on Linux its CPU affinity (a batch scheduler's, `taskset`'s
# or a container's CPU set) and its cgroups' CPU quotas and memory limits (a batch job's or a
# container's), v2 and v1, of its cgroup and every ancestor. Sized for the machine, a 32-CPU batch job
# on an 80-CPU node ran 80 compiler processes and could exceed the job's memory limit.
# `PAPERLEAN_TEST_CGROUP=<dir>` makes PaperLean read `<dir>/self` and `<dir>/fs` for
# `/proc/self/cgroup` and `/sys/fs/cgroup`.
[ "$(uname -s)" = Linux ] || exit 0
unset PAPERLEAN_IMPORT PAPERLEAN_IMPORT_TIMING LEAN_OLEAN_PACK LEAN_IMPORT_IMAGE PAPERLEAN_NATIVE_LIBS
unset ELAN_TOOLCHAIN
ROOT="$(cd "$TMP_DIR" && pwd -P)"
cd "$ROOT"
cat > res.lean <<'END'
import Lean.PaperLean.System
def main : IO Unit := do
  IO.println s!"cpus={← Lean.PaperLean.numCPUs} mem={← Lean.PaperLean.totalMemory}"
END
aff=$(python3 -c 'import os; print(len(os.sched_getaffinity(0)))')
first=$(python3 -c 'import os; print(min(os.sched_getaffinity(0)))')
phys=$(( $(getconf _PHYS_PAGES) * $(getconf PAGE_SIZE) ))
min() { if [ "$1" -lt "$2" ]; then echo "$1"; else echo "$2"; fi; }
# Runs the program under the cgroup files of $1 (`-` for the process's own) and, if $2 is given,
# on that CPU only.
probe() {
  local cg=$1 cpu=${2:-}
  local pre=()
  [ "$cg" = - ] || pre=(env "PAPERLEAN_TEST_CGROUP=$ROOT/$cg")
  if [ -n "$cpu" ]; then
    capture "${pre[@]}" python3 -c 'import os, sys; os.sched_setaffinity(0, {int(sys.argv[1])}); os.execvp(sys.argv[2], sys.argv[2:])' \
      "$cpu" lean --run res.lean
  else
    capture "${pre[@]}" lean --run res.lean
  fi
}

# The process's own limits: never more than its CPU set and the machine's memory.
probe -
cpus=$(sed -n 's/^cpus=\([0-9]*\) .*/\1/p' "$CAPTURED.out.produced")
mem=$(sed -n 's/.* mem=\([0-9]*\)$/\1/p' "$CAPTURED.out.produced")
[ -n "$cpus" ] && [ "$cpus" -ge 1 ] && [ "$cpus" -le "$aff" ] || fail "numCPUs $cpus is not within the $aff CPUs of the affinity"
[ -n "$mem" ] && [ "$mem" -le "$phys" ] || fail "totalMemory $mem exceeds the machine's $phys bytes"

# No cgroup limits: the affinity and the machine's memory.
mkdir -p cg0/fs
printf '0::/\n' > cg0/self
probe cg0
check_out_contains "cpus=$aff mem=$phys"
# Restricted to one CPU (as by `taskset -c`), on a machine with more.
if [ "$(python3 -c 'import os; print(os.cpu_count())')" -gt 1 ]; then
  probe cg0 "$first"
  check_out_contains "cpus=1 mem=$phys"
fi

# cgroup v2: 1.5 CPUs of quota (rounded up to 2) in the process's cgroup, 3 GB of memory in its
# parent (its own says `max`), no quota in the parent.
mkdir -p cg2/fs/a/b
printf '0::/a/b\n' > cg2/self
printf '3000000000\n' > cg2/fs/a/memory.max
printf 'max\n' > cg2/fs/a/b/memory.max
printf '150000 100000\n' > cg2/fs/a/b/cpu.max
printf 'max 100000\n' > cg2/fs/a/cpu.max
probe cg2
check_out_contains "cpus=$(min "$aff" 2) mem=$(min "$phys" 3000000000)"

# cgroup v1 (as a batch scheduler's): the CPU quota of the job (1 CPU) in the `cpu,cpuacct`
# hierarchy, the memory limit of the job (2 GB) above the step's (v1's "no limit").
mkdir -p "cg1/fs/cpu,cpuacct/job" cg1/fs/memory/job/step
printf '12:memory:/job/step\n5:cpu,cpuacct:/job\n1:name=systemd:/job\n' > cg1/self
printf '100000\n' > "cg1/fs/cpu,cpuacct/job/cpu.cfs_quota_us"
printf '100000\n' > "cg1/fs/cpu,cpuacct/job/cpu.cfs_period_us"
printf '2000000000\n' > cg1/fs/memory/job/memory.limit_in_bytes
printf '9223372036854771712\n' > cg1/fs/memory/job/step/memory.limit_in_bytes
probe cg1
check_out_contains "cpus=1 mem=$(min "$phys" 2000000000)"

# `paperlean prepare` without `-j` runs as many compiler processes as those limits allow: one.
mkdir -p ws/dep/Dep
cd ws
cat > dep/lakefile.toml <<'END'
name = "dep"
defaultTargets = ["Dep"]
[[lean_lib]]
name = "Dep"
END
printf 'def base (n : Nat) : Nat := n + 1\n' > dep/Dep/Base.lean
cat > dep/Dep/Twice.lean <<'END'
import Lean
macro "twice! " x:term : term => `($x + $x)
END
printf 'import Dep.Base\nimport Dep.Twice\n' > dep/Dep.lean
cat > lakefile.toml <<'END'
name = "root"
defaultTargets = ["Root"]
[[require]]
name = "dep"
path = "dep"
[[lean_lib]]
name = "Root"
END
printf 'import Dep\n#eval twice! base 20\n' > Root.lean
run lake build Dep
capture env "PAPERLEAN_TEST_CGROUP=$ROOT/cg1" lake paperlean prepare
check_out_contains "Compiling the native library of dep (1 jobs"
