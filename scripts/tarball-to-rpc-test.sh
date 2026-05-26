#!/usr/bin/env bash
# Convert a kore-rpc-booster bug-report tarball into a runDirectoryTest-compatible
# test directory under booster/test/rpc-integration/.
#
# Usage: scripts/tarball-to-rpc-test.sh <tarball> <name>
#
# Creates:
#   booster/test/rpc-integration/resources/<name>.kore          — Haskell backend def
#   booster/test/rpc-integration/resources/<name>.haskell.kore  — same (for kompile)
#   booster/test/rpc-integration/resources/<name>.llvm.kore     — LLVM backend def
#   booster/test/rpc-integration/resources/<name>.kompile       — script to rebuild dylib
#   booster/test/rpc-integration/test-<name>/state-NNN.<method> — one per request
#   booster/test/rpc-integration/test-<name>/params-NNN.json    — extra params (execute/simplify/add-module)
#   booster/test/rpc-integration/test-<name>/response-NNN.json  — golden responses (id normalised to 1)
#
# Request-type mapping:
#   execute, simplify  →  state file contains the KoreJson state; extra params in params-NNN.json
#   add-module         →  state file contains raw Kore module text; extra params in params-NNN.json
#   all others         →  full JSON-RPC envelope sent verbatim (.send), id normalised to 1
#
# After creation, verify with:
#   cd booster/test/rpc-integration && ./runDirectoryTest.sh test-<name>
# Regenerate golden responses after an intentional behaviour change:
#   cd booster/test/rpc-integration && ./runDirectoryTest.sh test-<name> --regenerate

set -euo pipefail

tarball=${1?"Usage: $(basename "$0") <tarball> <name>"}
name=${2?"Usage: $(basename "$0") <tarball> <name>"}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RESOURCES="$REPO_ROOT/booster/test/rpc-integration/resources"
TEST_DIR="$REPO_ROOT/booster/test/rpc-integration/test-$name"

if [ -d "$TEST_DIR" ]; then
    echo "Test directory $TEST_DIR already exists — aborting to avoid overwrite." >&2
    echo "Remove it first if you want to regenerate: rm -rf $TEST_DIR" >&2
    exit 1
fi
mkdir -p "$TEST_DIR"

TMPD=$(mktemp -d)
trap 'rm -rf "$TMPD"' EXIT

echo "Extracting $tarball …"
tar xf "$tarball" -C "$TMPD"

# ── Definitions ───────────────────────────────────────────────────────────────

echo "Installing definitions into $RESOURCES/ …"
cp "$TMPD/definition.kore" "$RESOURCES/$name.kore"
cp "$TMPD/definition.kore" "$RESOURCES/$name.haskell.kore"

if [ -f "$TMPD/llvm_definition/definition.kore" ]; then
    cp "$TMPD/llvm_definition/definition.kore" "$RESOURCES/$name.llvm.kore"
    echo "  (LLVM definition installed)"
fi

# kompile script — rebuild the LLVM backend library when PLUGIN_DIR is set
cat > "$RESOURCES/$name.kompile" << 'KOMPILE_EOF'
#!/usr/bin/env bash
# Rebuild the LLVM backend .so for this test's definition.
# Run from inside booster/test/rpc-integration/resources/ with PLUGIN_DIR set.
# See docs/2026-05-25-submitting-test-cases.md for the full workflow.
set -euo pipefail
name=$(basename "$0" .kompile)
mkdir -p dt
llvm-kompile-matching "$name.llvm.kore" qbaL ./dt 1/2
for lib in libff libcryptopp blake2; do
    LIBFILE=$(find "${PLUGIN_DIR}" -name "${lib}.a" | head -1)
    [ -z "$LIBFILE" ] && { echo "[Error] Unable to locate ${lib}.a" >&2; exit 1; }
    PLUGIN_LIBS+="$LIBFILE "
    PLUGIN_INCLUDE+="-I$(dirname "$LIBFILE")/../include "
done
PLUGIN_CPP="${PLUGIN_DIR}/include/plugin-c/crypto.cpp ${PLUGIN_DIR}/include/plugin-c/plugin_util.cpp"
llvm-kompile "$name.llvm.kore" ./dt c -- \
    -fPIC -std=c++20 -o interpreter \
    $PLUGIN_LIBS $PLUGIN_INCLUDE $PLUGIN_CPP \
    -lcrypto -lssl -lprocps
cp interpreter.so "$name.so"
KOMPILE_EOF
chmod +x "$RESOURCES/$name.kompile"

# ── Request / response pairs ──────────────────────────────────────────────────

total=$(ls "$TMPD/sequence/" | wc -l)
num_requests=$(( total / 2 ))
echo "Processing $num_requests request/response pairs …"

n=0
i=0
while [ $i -lt $total ]; do
    seq_req=$(printf '%03d' $i)
    seq_resp=$(printf '%03d' $(( i + 1 )))
    i=$(( i + 2 ))

    req_file="$TMPD/$(cat "$TMPD/sequence/$seq_req")"
    resp_file="$TMPD/$(cat "$TMPD/sequence/$seq_resp")"

    test_num=$(printf '%03d' $n)
    method=$(python3 -c "import json; print(json.load(open('$req_file')).get('method','unknown'))")

    case "$method" in
        execute|simplify)
            # State file: the KoreJson state only
            python3 - "$req_file" "$TEST_DIR/state-$test_num.$method" << 'PY'
import json, sys
d = json.load(open(sys.argv[1]))
with open(sys.argv[2], 'w') as f:
    json.dump(d['params']['state'], f, indent=2)
    f.write('\n')
PY
            # Params file: remaining params (omit 'state'); skip if empty
            python3 - "$req_file" "$TEST_DIR/params-$test_num.json" << 'PY'
import json, sys, os
d = json.load(open(sys.argv[1]))
p = {k: v for k, v in d['params'].items() if k != 'state'}
if p:
    with open(sys.argv[2], 'w') as f:
        json.dump(p, f, indent=2)
        f.write('\n')
else:
    # nothing to write — remove the placeholder if the shell created one
    try: os.unlink(sys.argv[2])
    except FileNotFoundError: pass
PY
            ;;
        add-module)
            # State file: raw Kore module text
            python3 - "$req_file" "$TEST_DIR/state-$test_num.add-module" << 'PY'
import json, sys
d = json.load(open(sys.argv[1]))
with open(sys.argv[2], 'w') as f:
    f.write(d['params']['module'])
    if not d['params']['module'].endswith('\n'):
        f.write('\n')
PY
            # Params file: remaining params (omit 'module')
            python3 - "$req_file" "$TEST_DIR/params-$test_num.json" << 'PY'
import json, sys, os
d = json.load(open(sys.argv[1]))
p = {k: v for k, v in d['params'].items() if k != 'module'}
if p:
    with open(sys.argv[2], 'w') as f:
        json.dump(p, f, indent=2)
        f.write('\n')
else:
    try: os.unlink(sys.argv[2])
    except FileNotFoundError: pass
PY
            ;;
        *)
            # Send verbatim with id normalised to 1
            python3 - "$req_file" "$TEST_DIR/state-$test_num.send" << 'PY'
import json, sys
d = json.load(open(sys.argv[1]))
d['id'] = 1
with open(sys.argv[2], 'w') as f:
    json.dump(d, f, indent=2)
    f.write('\n')
PY
            ;;
    esac

    # Golden response: normalise id to 1
    python3 - "$resp_file" "$TEST_DIR/response-$test_num.json" << 'PY'
import json, sys
d = json.load(open(sys.argv[1]))
d['id'] = 1
with open(sys.argv[2], 'w') as f:
    json.dump(d, f, indent=2)
    f.write('\n')
PY

    printf "  %s  %-12s\n" "$test_num" "$method"
    n=$(( n + 1 ))
done

echo ""
echo "Created: $TEST_DIR  ($n tests)"
echo ""
echo "Verify:"
echo "  cd booster/test/rpc-integration && ./runDirectoryTest.sh test-$name"
echo ""
echo "To regenerate golden responses after a behaviour change:"
echo "  ./runDirectoryTest.sh test-$name --regenerate"
