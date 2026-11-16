#!/bin/sh
# Build the ELF of one target in Docker and write its link inputs.
# Usage: sh tools/build_target.sh <manifest>
# The output directory is <directory of the manifest>/build.
# The script builds the ELF two times in two containers. The two ELF files must be equal.
# It stops with a non-zero exit status on any error or difference.
set -eu

if [ "$#" -ne 1 ]; then
  echo "usage: sh build_target.sh <manifest>" >&2
  exit 2
fi
tools=$(cd "$(dirname "$0")" && pwd)
mdir=$(cd "$(dirname "$1")" && pwd)
manifest="$mdir/$(basename "$1")"

# Read and validate the manifest. The Python program prints shell assignments.
settings=$(python3 -I -B - "$manifest" <<'EOF'
import json
import os
import re
import shlex
import sys

path = sys.argv[1]
m = json.load(open(path))


def fail(msg, code=1):
    print(f"manifest {path}: {msg}", file=sys.stderr)
    sys.exit(code)


def need(cond, msg):
    if not cond:
        fail(msg)


WORD = re.compile(r"[A-Za-z0-9_.,=/+-]+")
need(m.get("schema") == "go-kraken.target/1", "schema is not go-kraken.target/1")
name = m.get("name")
need(isinstance(name, str) and re.fullmatch(r"[a-z0-9][a-z0-9_-]*", name), "bad name")
need(os.path.basename(os.path.dirname(os.path.abspath(path))) == name, "the manifest directory name is not the name")
src = m.get("source")
need(isinstance(src, dict), "source is not an object")
if src.get("kind") == "go-standard-library":
    need(isinstance(src.get("package"), str) and src["package"], "source: no package")
elif src.get("kind") == "go-module":
    for k in ("module", "version", "go_sum"):
        need(isinstance(src.get(k), str) and src[k], f"source: no {k}")
    fail("source kind go-module: this script cannot build a module source yet", 2)
else:
    fail(f"source: unknown kind {src.get('kind')!r}")
go = m.get("go")
need(isinstance(go, dict), "go is not an object")
need(isinstance(go.get("version"), str) and re.fullmatch(r"[0-9]+\.[0-9]+(\.[0-9]+)?", go["version"]), "go: bad version")
need(isinstance(go.get("docker_image"), str) and re.fullmatch(r"[a-z0-9./_-]+:[A-Za-z0-9._-]+@sha256:[0-9a-f]{64}",
                                                           go["docker_image"]), "go: docker_image is not pinned by a digest")
env = go.get("env")
need(isinstance(env, dict) and all(re.fullmatch(r"[A-Z][A-Z0-9_]*", k) and isinstance(v, str) and WORD.fullmatch(v)
                                   for k, v in env.items()), "go: bad env")
for k in ("flags", "tags"):
    need(isinstance(go.get(k), list) and all(isinstance(x, str) and WORD.fullmatch(x) for x in go[k]), f"go: bad {k}")
main = m.get("main_package")
need(isinstance(main, str) and main and not os.path.isabs(main), "main_package is not a relative path")
mainabs = os.path.realpath(os.path.join(os.path.dirname(path), main))
for f in ("go.mod", "main.go"):
    need(os.path.isfile(os.path.join(mainabs, f)), f"main_package: no {f}")
fns = m.get("functions")
need(isinstance(fns, list) and fns, "functions is empty")
for f in fns:
    need(isinstance(f, dict) and isinstance(f.get("symbol"), str) and isinstance(f.get("lean_constant"), str),
         "a function needs symbol and lean_constant")
syms = [f["symbol"] for f in fns]
need(len(set(syms)) == len(syms), "a function symbol occurs twice")
need(isinstance(m.get("runtime_callees"), list), "runtime_callees is not a list")
items = m.get("data_items")
need(isinstance(items, list), "data_items is not a list")
for d in items:
    need(isinstance(d, dict) and all(isinstance(d.get(k), str) for k in ("id", "symbol", "kind")),
         "a data item needs id, symbol and kind")
if items:
    fail("data_items: this script has no data extractor yet", 2)
out = {
    "NAME": name,
    "IMAGE": go["docker_image"],
    "GO_VERSION": go["version"],
    "ENV_ARGS": " ".join(f"-e {k}={v}" for k, v in env.items()),
    "ENV_TEXT": " ".join(f"{k}={v}" for k, v in env.items()),
    "FLAGS": " ".join(["-buildvcs=false"] + go["flags"]),
    "TAGS": ",".join(go["tags"]),
    "MAIN": mainabs,
    "REGEX": "^(?:" + "|".join(re.escape(s) for s in syms) + ")$",
    "SYMBOLS": "\n".join(syms),
}
for k, v in out.items():
    print(f"{k}={shlex.quote(v)}")
EOF
)
eval "$settings"

build="$mdir/build"
second="$build/second-build"
mkdir -p "$build/norm" "$second"
tagarg=""
if [ -n "$TAGS" ]; then
  tagarg="-tags=$TAGS"
fi

# One container per call: no network, a 4 GiB memory limit, a fresh build cache.
# $ENV_ARGS, $FLAGS and $tagarg hold no spaces inside a word (the manifest check makes sure).
go_run() {
  out=$1
  shift
  # shellcheck disable=SC2086
  docker run --rm --network none --memory 4g --user "$(id -u):$(id -g)" \
    $ENV_ARGS -e GOTOOLCHAIN=local -e GOFLAGS= -e HOME=/tmp -e GOCACHE=/tmp/go-cache \
    -v "$MAIN:/src:ro" -v "$out:/out" -w /src "$IMAGE" "$@"
}

sha() {
  shasum -a 256 "$1" | cut -d' ' -f1
}

# shellcheck disable=SC2086
go_run "$build" go build $FLAGS $tagarg -o /out/target-amd64 .
# shellcheck disable=SC2086
go_run "$second" go build $FLAGS $tagarg -o /out/target-amd64 .
elf_sha=$(sha "$build/target-amd64")
second_sha=$(sha "$second/target-amd64")
if [ "$elf_sha" != "$second_sha" ]; then
  echo "the two builds differ: $elf_sha and $second_sha" >&2
  echo "the second ELF stays in $second" >&2
  exit 1
fi
rm "$second/target-amd64"
rmdir "$second"

version=$(go_run "$build" go version)
case "$version" in
  "go version go$GO_VERSION "*) ;;
  *)
    echo "the image has another Go version: $version (manifest: $GO_VERSION)" >&2
    exit 1
    ;;
esac
go_run "$build" go tool objdump -gnu -s "$REGEX" /out/target-amd64 > "$build/target.objdump"
go_run "$build" go tool nm -size -sort address /out/target-amd64 > "$build/target-amd64.nm"

# The disassembly must hold each function of the manifest exactly once, and no other function.
python3 -I -B - "$build/target.objdump" "$SYMBOLS" <<'EOF'
import sys

got = [l.split()[1].removesuffix("(SB)") for l in open(sys.argv[1]) if l.startswith("TEXT ")]
want = sys.argv[2].split("\n")
if sorted(got) != sorted(want):
    sys.exit(f"objdump functions {got} are not the manifest functions {want}")
EOF

{
  echo "go: $version"
  echo "image: $IMAGE"
  echo "env: $ENV_TEXT"
  echo "flags: $FLAGS"
  echo "tags: ${TAGS:-none}"
  echo "elf sha256: $elf_sha"
  echo "objdump sha256: $(sha "$build/target.objdump")"
  echo "nm sha256: $(sha "$build/target-amd64.nm")"
  echo "main.go sha256: $(sha "$MAIN/main.go")"
  echo "manifest sha256: $(sha "$manifest")"
} > "$build/build-ids.txt"
cat "$build/build-ids.txt"

rm -f "$build"/norm/*.S
python3 -I -B "$tools/convert_objdump.py" "$build/target.objdump" "$build/target-amd64.nm" "$build/norm" --norm
ls "$build/norm"
