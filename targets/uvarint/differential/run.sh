#!/bin/sh
# Differential run of the uvarint target: Go binary.Uvarint against the Lean Uvarint.decode.
# Usage: sh targets/uvarint/differential/run.sh <work-dir>
# All generated files go into <work-dir>. Nothing is written into the tree.
# The Go program runs natively in the container. It checks Go semantics, not the amd64 code.
# Exit 0 only when the two outputs are equal.
set -eu

if [ "$#" -ne 1 ]; then
  echo "usage: sh run.sh <work-dir>" >&2
  exit 2
fi
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$1"
work=$(cd "$1" && pwd)
lean_dir="$here/../../../lean"

# The image, the flags and the tags of the manifest.
settings=$(python3 -I -B - "$here/../manifest.json" <<'EOF'
import json
import re
import shlex
import sys

go = json.load(open(sys.argv[1]))["go"]
word = re.compile(r"[A-Za-z0-9_.,=/+-]+")
if not all(isinstance(x, str) and word.fullmatch(x) for x in go["flags"] + go["tags"]):
    sys.exit("manifest: a flag or a tag is not one plain word")
flags = ["-buildvcs=false"] + go["flags"] + ([f"-tags={','.join(go['tags'])}"] if go["tags"] else [])
print(f"IMAGE={shlex.quote(go['docker_image'])}")
print(f"FLAGS={shlex.quote(' '.join(flags))}")
EOF
)
eval "$settings"

python3 -I -B "$here/cases.py" > "$work/cases.txt"

# One container per step: no network, a 4 GiB memory limit.
# GOOS and GOARCH are not set: the program runs on the architecture of the container.
go_run() {
  docker run --rm -i --network none --memory 4g --user "$(id -u):$(id -g)" \
    -e CGO_ENABLED=0 -e GOTOOLCHAIN=local -e GOFLAGS= -e HOME=/tmp -e GOCACHE=/tmp/go-cache \
    -v "$here:/src:ro" -v "$work:/work" -w /src "$IMAGE" "$@"
}
# shellcheck disable=SC2086
go_run go build $FLAGS -o /work/go-differential .
go_run go version > "$work/go-version.txt"
go_run /work/go-differential < "$work/cases.txt" > "$work/go.txt"

(cd "$lean_dir" && lake env lean --run "$here/Differential.lean" "$work/cases.txt") > "$work/lean.txt"

cases=$(wc -l < "$work/cases.txt" | tr -d ' ')
echo "go: $(cat "$work/go-version.txt")"
echo "cases: $cases"
echo "go lines: $(wc -l < "$work/go.txt" | tr -d ' ')"
echo "lean lines: $(wc -l < "$work/lean.txt" | tr -d ' ')"
# Each output must have one line per case. Two empty outputs are equal but check nothing.
if [ "$(wc -l < "$work/go.txt" | tr -d ' ')" != "$cases" ]; then
  echo "the Go output does not have one line per case" >&2
  exit 1
fi
if cmp "$work/go.txt" "$work/lean.txt"; then
  echo "equal: Go and Lean agree on all $cases cases"
else
  echo "the outputs differ. The differing lines:" >&2
  diff "$work/go.txt" "$work/lean.txt" >&2 || true
  exit 1
fi
