#!/usr/bin/env bash
# Nova Worker build pipeline (NON-OBFUSCATED, BPB-parity):
#   esbuild (bundle + keep cloudflare:sockets EXTERNAL + minify)
#     -> inject per-build random junk (optional, on by default)
#     -> terser mangle (folds the junk into short native-looking names)
#
# WHY NO javascript-obfuscator: string-array/RC4 obfuscation is what broke us. It can encode the
# 'cloudflare:sockets' import specifier, and Cloudflare links that built-in by scanning for the
# literal string at deploy time -> once encoded it can't link -> Error 1101 at LOAD. It also makes
# the code look malware-like to automated scanners. BPB's shipped release does NOT obfuscate; it
# uses esbuild + terser + random junk. This mirrors that: lighter, readable, and it always loads.
#
# The real 1101 defense lives in the SOURCE: a STATIC `import { connect as cfSocketConnect } from
# 'cloudflare:sockets'`. ES import specifiers are never rewritten by minifiers, so the module always
# links. Do not turn this back into a dynamic import('cloudflare:sockets').
#
# The junk step is the ONLY "anti-fingerprint" that helps: every build differs, so Cloudflare can't
# match deployments by a byte signature. It does NOT change your ToS exposure (running a proxy still
# breaks CF Self-Serve Agreement 2.2.1(j)); that needs fresh accounts + distribution, not code tricks.
#
# Usage: ./build-worker.sh [source.js] [out.js]
#   defaults: sourcecode.optimized.js -> worker.js
#   env: JUNK=0 to disable the per-build random junk step (default JUNK=1)
set -euo pipefail
SRC="${1:-sourcecode.optimized.js}"
OUT="${2:-worker.js}"
JUNK="${JUNK:-1}"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT

echo "1/4 esbuild (bundle, external cloudflare:sockets, minify)..."
npx --yes esbuild "$SRC" --bundle --format=esm --target=esnext \
  --external:cloudflare:sockets --minify --outfile="$TMP/bundled.js"

STEP_IN="$TMP/bundled.js"
if [ "$JUNK" = "1" ]; then
  echo "2/4 inject per-build random junk (every build differs)..."
  node - "$TMP/bundled.js" "$TMP/junked.js" <<'NODE'
const fs = require('fs');
const [,, inFile, outFile] = process.argv;
const rnd = (min, max) => min + Math.floor(Math.random() * (max - min + 1));
const nLet = rnd(50, 500), nFn = rnd(50, 500);
let junk = '';
for (let i = 0; i < nLet; i++) junk += `let _nvj_l${i}=${rnd(0, 2 ** 31)};`;
for (let i = 0; i < nFn; i++) junk += `function _nvj_f${i}(){return ${rnd(0, 2 ** 31)};}`;
fs.writeFileSync(outFile, junk + '\n' + fs.readFileSync(inFile, 'utf8'));
console.error(`    +${nLet} dead lets, +${nFn} dead funcs`);
NODE
  STEP_IN="$TMP/junked.js"
else
  echo "2/4 (junk step skipped: JUNK=0)"
fi

echo "3/4 terser (mangle; keep import specifier + default export + the junk)..."
npx --yes terser "$STEP_IN" --module \
  --compress "dead_code=false,unused=false,toplevel=false,drop_console=false" \
  --mangle "toplevel=true" \
  --format "comments=false" \
  --output "$OUT"

echo "4/4 verify..."
cp "$OUT" "$TMP/chk.mjs"
node --check "$TMP/chk.mjs" || { echo "FAIL: does not parse"; exit 1; }
if grep -q "cloudflare:sockets" "$OUT"; then echo "FAIL: 'cloudflare:sockets' present -> signature tell not removed (should use request.fetcher.connect)"; exit 1; fi
grep -qE "as default|export default|export\{[^}]*default" "$OUT" || { echo "FAIL: no default export (Worker entry missing)"; exit 1; }
if grep -qE "_0x[0-9a-f]{4,}" "$OUT"; then echo "WARN: found _0x string-array markers (unexpected for a non-obfuscated build)"; fi
if grep -q "_nvj_" "$OUT"; then echo "FAIL: junk names leaked un-mangled (terser did not run?)"; exit 1; fi
echo "OK: $OUT ($(wc -c < "$OUT") bytes, $(gzip -c "$OUT" | wc -c | tr -d ' ') gzip) parses, no 'cloudflare:sockets' tell, default export present, non-obfuscated."
