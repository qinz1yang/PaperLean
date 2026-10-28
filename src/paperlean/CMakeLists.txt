# PaperLean's version, written into `.paperlean` headers
file(STRINGS "${CMAKE_CURRENT_SOURCE_DIR}/../../paperlean/VERSION" PAPERLEAN_VERSION LIMIT_COUNT 1)
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/../../paperlean/VERSION")

add_library(
  paperlean
  OBJECT
  fast_import.cpp
  graph_diff.cpp
  olean_pack.cpp
  import_state.cpp
  inst_lparams.cpp
  interp_cache.cpp
  native_libs.cpp
  speculation.cpp
  system.cpp
)
target_compile_definitions(paperlean PRIVATE PAPERLEAN_VERSION="${PAPERLEAN_VERSION}")
