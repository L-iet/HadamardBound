#!/usr/bin/env bash
# Local equivalent of Palomar's toolchain-bundled independent-kernel check.
# Policy reference pinned in submission/upstream-references.json.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v bwrap >/dev/null
prefix=$(lean --print-prefix)
temporary_config=$(mktemp)
trap 'rm -f "$temporary_config"' EXIT
python3 - "$prefix" "$temporary_config" <<'PY'
import json, pathlib, sys
prefix = pathlib.Path(sys.argv[1])
config = json.loads(pathlib.Path('comparator.json').read_text())
assert 'external_kernels' not in config, 'Do not submit external_kernels'
config.pop('enable_nanoda', None)
names = {'nanoda': 'nanoda_bin', 'con-ron': 'con-ron'}
for binary in ['lake', 'leanexport', 'leanchecker', *names.values()]:
    assert (prefix / 'bin' / binary).is_file(), f'Missing bundled tool: {binary}'
config['external_kernels'] = {name: [str(prefix / 'bin' / binary)]
                              for name, binary in names.items()}
pathlib.Path(sys.argv[2]).write_text(json.dumps(config))
PY
lake comparator --config "$temporary_config" "$@"
