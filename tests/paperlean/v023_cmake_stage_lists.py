#!/usr/bin/env python3
"""Configure four tiny real ExternalProjects with the selected production top-level CMake file."""
import argparse
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time


KEYS = ('CMAKE_DIAGNOSTIC_INIT', 'CMAKE_OSX_ARCHITECTURES', 'CMAKE_V023_PLATFORM',
        'LEAN_VERSION_V023_LIST', 'V023_COMMON', 'V023_SCOPED', 'V023_STAGE1_ONLY')
COMMON = r'alpha;literal\;semicolon;;space words;__LEAN_STAGE_LIST_SEPARATOR__|tail'
COMMON_ELEMENTS = ['alpha', 'literal;semicolon', '', 'space words', '__LEAN_STAGE_LIST_SEPARATOR__|tail']
SCOPED = {0: (r'zero;literal\;zero', ['zero', 'literal;zero']),
          1: (r'one;literal\;one', ['one', 'literal;one'])}


def probe_code():
    return '''file(MAKE_DIRECTORY "${CMAKE_BINARY_DIR}/v023-probe")
foreach(key IN ITEMS ''' + ' '.join(KEYS) + ''')
  if(DEFINED ${key})
    set(value "${${key}}")
    file(WRITE "${CMAKE_BINARY_DIR}/v023-probe/${key}.raw" "${value}")
    list(LENGTH value count)
    file(WRITE "${CMAKE_BINARY_DIR}/v023-probe/${key}.count" "${count}")
    if(count GREATER 0)
      math(EXPR last "${count} - 1")
      foreach(i RANGE 0 ${last})
        list(GET value ${i} item)
        file(WRITE "${CMAKE_BINARY_DIR}/v023-probe/${key}.${i}" "${item}")
      endforeach()
    endif()
  endif()
endforeach()
'''


def read_value(directory, key):
    root = directory / 'v023-probe'
    raw = root / (key + '.raw')
    if not raw.exists():
        return None
    count = int((root / (key + '.count')).read_text())
    return raw.read_text(), [(root / f'{key}.{i}').read_text() for i in range(count)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('run without Python -O')
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    if any(work.iterdir()):
        raise SystemExit('--work must be empty')
    cmake = shutil.which('cmake')
    true = shutil.which('true')
    if not cmake or not true:
        raise SystemExit('this Unix Makefiles fixture requires cmake and true')
    source = work / 'fixture source'
    outer = (args.source_root.resolve() / 'CMakeLists.txt').read_text()
    assert outer.count('project(LEAN CXX C)') == 1
    # Use the actual production forwarding code and actual stage0/1/2/3 ExternalProject_Add
    # invocations. Change only language enablement and record the received parent values.
    outer = outer.replace('project(LEAN CXX C)', probe_code() + '\nproject(LEAN NONE)')
    for sub in ('src', 'stage0/src'):
        child = source / sub
        child.mkdir(parents=True)
        (child / 'CMakeLists.txt').write_text('cmake_minimum_required(VERSION 3.21)\n' +
                                             probe_code() + '\nproject(v023_nested NONE)\n')
    (source / 'CMakeLists.txt').write_text(outer)
    records = []

    def run(label, argv):
        start = time.monotonic()
        log_path = work / (label + '.log')
        with log_path.open('wb') as log:
            proc = subprocess.Popen([str(x) for x in argv], cwd=work, stdout=log, stderr=subprocess.STDOUT,
                                    start_new_session=True)
            timed_out = False
            try:
                proc.wait(timeout=120)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
        records.append({'command': [str(x) for x in argv], 'exit': proc.returncode, 'timeout': timed_out,
                        'seconds': time.monotonic() - start, 'log': str(log_path)})
        (work / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
        if timed_out or proc.returncode:
            raise SystemExit(f'{label} failed; see {log_path}')
        if 'Ignoring extra path from command line' in log_path.read_text(errors='replace'):
            raise AssertionError(f'{label}: a forwarded value became a positional command argument')

    for mode in ('typed', 'untyped'):
        build = work / mode
        arch = 'CMAKE_OSX_ARCHITECTURES' + (':STRING' if mode == 'typed' else '')
        run(mode + '-outer', [cmake, '-S', source, '-B', build, '-G', 'Unix Makefiles',
            '-DUSE_MIMALLOC=OFF', '-DFETCHCONTENT_FULLY_DISCONNECTED=ON', '-DCADICAL=' + true, '-DLEANTAR=' + true,
            '-D' + arch + '=arm64;x86_64', '-DCMAKE_DIAGNOSTIC_INIT:STRING=CMD_DEPRECATED=WARN;CMD_UNUSED_CLI=WARN',
            '-DCMAKE_V023_PLATFORM:STRING=' + COMMON, '-DLEAN_VERSION_V023_LIST=' + COMMON,
            '-DV023_COMMON=' + COMMON, '-DV023_SCOPED=generic;scope',
            '-DSTAGE0_V023_SCOPED=' + SCOPED[0][0], '-DSTAGE1_V023_SCOPED:STRING=' + SCOPED[1][0],
            '-DSTAGE1_V023_STAGE1_ONLY:STRING=' + COMMON,
            '-DSTAGE1_CMAKE_OSX_ARCHITECTURES:STRING=x86_64;arm64'])
        # stage3-configure pulls the three preceding real nested projects, all with NONE languages.
        run(mode + '-nested', [cmake, '--build', build, '--target', 'stage3-configure', '--parallel', '2'])
        diagnostic = read_value(build, 'CMAKE_DIAGNOSTIC_INIT')
        assert diagnostic is not None and len(diagnostic[1]) >= 2
        assert read_value(build / 'stage0', 'CMAKE_DIAGNOSTIC_INIT') == diagnostic
        for stage in range(4):
            directory = build / f'stage{stage}'
            expected = ('x86_64;arm64', ['x86_64', 'arm64']) if stage == 1 else ('arm64;x86_64', ['arm64', 'x86_64'])
            assert read_value(directory, 'CMAKE_OSX_ARCHITECTURES') == expected, (mode, stage, 'architectures')
            shared = (COMMON, COMMON_ELEMENTS)
            assert read_value(directory, 'LEAN_VERSION_V023_LIST') == shared, (mode, stage, 'format list')
            assert read_value(directory, 'CMAKE_V023_PLATFORM') == (shared if stage == 0 else None), (mode, stage, 'platform')
            assert read_value(directory, 'V023_COMMON') == (None if stage == 0 else shared), (mode, stage, 'common')
            assert read_value(directory, 'V023_SCOPED') == SCOPED.get(stage, ('generic;scope', ['generic', 'scope'])), (mode, stage, 'override')
            assert read_value(directory, 'V023_STAGE1_ONLY') == (shared if stage == 1 else None), (mode, stage, 'stage1 only')
    (work / 'result.json').write_text(json.dumps({'status': 'passed', 'modes': ['typed', 'untyped'],
        'nested_stages': [0, 1, 2, 3], 'raw_and_decoded_list_elements_checked': True}, indent=2) + '\n')


if __name__ == '__main__':
    main()
