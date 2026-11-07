# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.

# The repository: above `src`, or above `stage0/src` in the copy that `make update-stage0` makes
get_filename_component(PAPERLEAN_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../.." ABSOLUTE)
if(NOT EXISTS "${PAPERLEAN_ROOT}/paperlean/VERSION")
  get_filename_component(PAPERLEAN_ROOT "${PAPERLEAN_ROOT}/.." ABSOLUTE)
endif()
# PaperLean's version, written into `.paperlean` headers
file(STRINGS "${PAPERLEAN_ROOT}/paperlean/VERSION" PAPERLEAN_VERSION LIMIT_COUNT 1)
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS "${PAPERLEAN_ROOT}/paperlean/VERSION")
# The id of the build, so that data that another build wrote is not used even if it has the same
# version (`build_id.cmake`), computed by every build. Sources without a commit get one of their own
# for each build directory.
if(NOT PAPERLEAN_UNKNOWN_BUILD)
  string(RANDOM LENGTH 12 ALPHABET 0123456789abcdef r)
  set(PAPERLEAN_UNKNOWN_BUILD "unknown-${r}" CACHE INTERNAL "the build id of sources without a commit")
endif()
set(PAPERLEAN_BUILD_ID_ARGS -DROOT=${PAPERLEAN_ROOT} -DOUT=${CMAKE_CURRENT_BINARY_DIR}/include/paperlean_build.h
  -DFALLBACK=${PAPERLEAN_UNKNOWN_BUILD} -P ${CMAKE_CURRENT_SOURCE_DIR}/build_id.cmake)
execute_process(COMMAND ${CMAKE_COMMAND} ${PAPERLEAN_BUILD_ID_ARGS})
add_custom_target(paperlean_build_id COMMAND ${CMAKE_COMMAND} ${PAPERLEAN_BUILD_ID_ARGS}
  BYPRODUCTS ${CMAKE_CURRENT_BINARY_DIR}/include/paperlean_build.h VERBATIM)

add_library(
  paperlean
  OBJECT
  fast_import.cpp
  graph_diff.cpp
  olean_pack.cpp
  import_state.cpp
  inst_lparams.cpp
  interp_cache.cpp
  lookup_cache.cpp
  mvars_probe.cpp
  native_libs.cpp
  replace.cpp
  speculation.cpp
  setup_index.cpp
  system.cpp
)
target_compile_definitions(paperlean PRIVATE PAPERLEAN_VERSION="${PAPERLEAN_VERSION}")
target_include_directories(paperlean PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/include)
add_dependencies(paperlean paperlean_build_id)
