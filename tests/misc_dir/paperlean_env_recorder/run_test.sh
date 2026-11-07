leanc ${LEANC_OPTS-} -o env_recorder.produced env_recorder.c
run ./env_recorder.produced
run env PAPERLEAN_DEBUG_REUSE=1 ./env_recorder.produced
