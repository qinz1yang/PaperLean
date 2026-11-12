# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# `display_cumulative_profiling_times` iterates the process-global profiling
# map while `report_profiling_time` may update it from a worker thread.  The
# display must take `g_cum_times_mutex` (and format a snapshot, not the live
# map).  The source check fails on the unfixed file; the ThreadSanitizer run
# then exercises the actual interleaving when the compiler supports it.

SRC=${SRC:-$(cd "$TEST_DIR/.." && pwd)}
TIMES="$SRC/src/library/time_task.cpp"
[ -f "$TIMES" ] || fail "cannot find $TIMES"
if ! sed -n '/void display_cumulative_profiling_times/,/^}/p' "$TIMES" | grep -q 'lock_guard<mutex>'; then
  fail "display_cumulative_profiling_times does not take the profile-map lock"
fi

WS="$TMP_DIR/library-profile-lock"
mkdir -p "$WS"
cd "$WS"
cat > Race.cpp <<'CPP'
#include <thread>
#include <sstream>
#include <string>
#include "library/time_task.h"

using namespace lean;

int main() {
  initialize_time_task();
  report_profiling_time("init", second_duration(0.000001));
  std::thread writer([] {
    for (int i = 0; i < 20000; ++i)
      report_profiling_time("cat" + std::to_string(i % 100), second_duration(0.000001));
  });
  std::ostringstream sink;
  for (int i = 0; i < 2000; ++i)
    display_cumulative_profiling_times(sink);
  writer.join();
  finalize_time_task();
  return 0;
}
CPP
CXX=${CXX:-$(command -v clang++ || command -v g++ || true)}
if [ -n "$CXX" ] && leanc --print-cflags > /dev/null 2>&1; then
  CFLAGS=$(leanc --print-cflags)
  LDFLAGS=$(leanc --print-ldflags)
  if "$CXX" -std=c++17 -O1 -g -fsanitize=thread -fno-omit-frame-pointer \
      $CFLAGS -I"$SRC/src" "$TIMES" Race.cpp $LDFLAGS -o race > tsan-build.log 2>&1; then
    TSAN_OPTIONS=halt_on_error=1:exitcode=66 ./race > tsan-run.log 2>&1
    rc=$?
    if [ $rc != 0 ]; then
      cat tsan-run.log >&2
      fail "ThreadSanitizer detected a race in display_cumulative_profiling_times (exit $rc)"
    fi
  else
    echo "ThreadSanitizer build unavailable; the source check above already rejected the old code"
  fi
else
  echo "no C++ compiler; the source check above already rejected the old code"
fi
true
