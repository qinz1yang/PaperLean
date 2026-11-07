# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
# Failed closure relocation must release both mmap and malloc-backed regions.
case "$(uname -s)" in Darwin|Linux) ;; *) exit 0 ;; esac
cp region_closure_save.lean region_closure_load.lean region_probe.c region_missing_library.py "$TMP_DIR/"
cd "$TMP_DIR"
run "${CC:-cc}" -I "$(lean --print-prefix)/include" -c -o region_probe.o region_probe.c
for name in region_closure_save region_closure_load; do
  run lean -c "$name.c" "$name.lean"
  if [[ "$name" == region_closure_load ]]; then
    run leanc -o "$name" "$name.c" region_probe.o
  else
    run leanc -o "$name" "$name.c"
  fi
done
run ./region_closure_save fixture.olean 4194304
run python3 region_missing_library.py fixture.olean fixture-missing.olean 4194304
run ./region_closure_load fixture-missing.olean 64 mapped
run ./region_closure_load fixture-missing.olean 64 fallback
