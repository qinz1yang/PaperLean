# Copyright (c) 2026 PaperLean contributors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Writes the header `OUT` defining `PAPERLEAN_BUILD`, the id of the build, unless it defines that id
# already (so that only a new id recompiles its users): the first 12 digits of the commit of the
# sources (`PAPERLEAN_COMMIT` of an exported tree, else the checkout's `HEAD`), followed by `-` and 8
# digits of a hash of how the working tree differs from it (tracked and untracked files) if it does,
# so that builds of different sources have different ids; `FALLBACK` if there is no commit.
#   cmake -DROOT=<repository> -DOUT=<header> -DFALLBACK=<id> -P build_id.cmake
if(EXISTS "${ROOT}/PAPERLEAN_COMMIT")
  file(STRINGS "${ROOT}/PAPERLEAN_COMMIT" commit LIMIT_COUNT 1)
  set(changes "")
else()
  execute_process(COMMAND git rev-parse HEAD WORKING_DIRECTORY "${ROOT}"
    OUTPUT_VARIABLE commit OUTPUT_STRIP_TRAILING_WHITESPACE ERROR_QUIET)
  # (hashed by git, as the diff can be large, e.g. after `make update-stage0`)
  set(diff git diff HEAD --binary --no-ext-diff --no-textconv --no-color)
  execute_process(COMMAND ${diff} --quiet WORKING_DIRECTORY "${ROOT}" RESULT_VARIABLE dirty ERROR_QUIET)
  set(changes "")
  if(NOT dirty EQUAL 0)
    execute_process(COMMAND ${diff} COMMAND git hash-object --stdin WORKING_DIRECTORY "${ROOT}"
      OUTPUT_VARIABLE changes ERROR_QUIET)
  endif()
  set(others git -c core.quotePath=false ls-files --others --exclude-standard)
  execute_process(COMMAND ${others} WORKING_DIRECTORY "${ROOT}" OUTPUT_VARIABLE untracked ERROR_QUIET)
  if(NOT untracked STREQUAL "")
    execute_process(COMMAND ${others} COMMAND git hash-object --no-filters --stdin-paths WORKING_DIRECTORY "${ROOT}"
      OUTPUT_VARIABLE contents ERROR_QUIET)
    string(APPEND changes "${untracked}${contents}")
  endif()
endif()
if(commit MATCHES "^[0-9a-f]+$")
  string(SUBSTRING "${commit}" 0 12 id)
  if(NOT changes STREQUAL "")
    string(SHA256 h "${changes}")
    string(SUBSTRING "${h}" 0 8 h)
    string(APPEND id "-${h}")
  endif()
else()
  set(id "${FALLBACK}")
endif()
set(text "#pragma once\n#define PAPERLEAN_BUILD \"${id}\"\n")
if(EXISTS "${OUT}")
  file(READ "${OUT}" old)
endif()
if(NOT old STREQUAL text)
  file(WRITE "${OUT}" "${text}")
endif()
