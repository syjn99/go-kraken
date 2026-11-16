#!/bin/sh
# Differential run of the uvarint target: Go binary.Uvarint against the Lean Uvarint.decode.
# Usage: sh targets/uvarint/differential/run.sh <work directory> [amd64|arm64]
# The script writes all its files into the work directory. It writes no file into the tree.
# The Go program runs on the architecture of the container. It checks the Go semantics, not either target ELF.
# The exit status is 0 only when the two outputs are equal.
set -eu

if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
  echo "usage: sh run.sh <work directory> [amd64|arm64]" >&2
  exit 2
fi
arch_env=""
case "${2:-}" in
  amd64|arm64) arch_env="-e GOOS=linux -e GOARCH=$2" ;;
  "") ;;
  *) echo "unsupported architecture: $2" >&2; exit 2 ;;
esac
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
print(f"GO_VERSION={shlex.quote(go['version'])}")
print(f"IMAGE={shlex.quote(go['docker_image'])}")
print(f"FLAGS={shlex.quote(' '.join(flags))}")
EOF
)
eval "$settings"

python3 -I -B "$here/cases.py" > "$work/cases.txt"
cases=$(wc -l < "$work/cases.txt" | tr -d ' ')
if [ "$cases" -eq 0 ]; then
  echo "the case list is empty" >&2
  exit 1
fi

# `lake env lean` does not check that the build is current. The build of the specification must be current.
(cd "$lean_dir" && lake build --no-build Uvarint.Spec) > /dev/null || {
  echo "Uvarint.Spec is not built or not current: run lake build Uvarint first" >&2
  exit 1
}

# One container for each step: no network and a memory limit of 4 GiB.
# The optional architecture selects the compiled Go binary. The pinned compiler image stays unchanged.
go_run() {
  docker run $arch_env --rm -i --network none --memory 4g --user "$(id -u):$(id -g)" \
    -e CGO_ENABLED=0 -e GOTOOLCHAIN=local -e GOFLAGS= -e HOME=/tmp -e GOCACHE=/tmp/go-cache \
    -v "$here:/src:ro" -v "$work:/work" -w /src "$IMAGE" "$@"
}
# shellcheck disable=SC2086
go_run go build $FLAGS -o /work/go-differential .
go_run go version > "$work/go-version.txt"
case "$(cat "$work/go-version.txt")" in
  "go version go$GO_VERSION linux/"*) ;;
  *) echo "unexpected Go version or architecture" >&2; exit 1 ;;
esac
go_run go version -m /work/go-differential > "$work/go-build-info.txt"
python3 -I -B - "$work/go-build-info.txt" "${2:-}" "$GO_VERSION" <<'EOF'
import re
import sys

text = open(sys.argv[1]).read()
settings = dict(re.findall(r"^\s*build\s+(GOOS|GOARCH)=(\w+)$", text, re.M))
if not text.splitlines()[0].endswith(": go" + sys.argv[3]):
    sys.exit("the differential binary has a different Go version")
if settings.get("GOOS") != "linux" or settings.get("GOARCH") not in ("amd64", "arm64"):
    sys.exit("the differential binary has an unsupported target")
if sys.argv[2] and settings["GOARCH"] != sys.argv[2]:
    sys.exit("the differential binary has a different target architecture")
print("target: linux/" + settings["GOARCH"])
EOF
go_run /work/go-differential < "$work/cases.txt" > "$work/go.txt"

(cd "$lean_dir" && lake env lean --run "$here/Differential.lean" "$work/cases.txt") > "$work/lean.txt"

echo "go: $(cat "$work/go-version.txt")"
echo "cases: $cases"
echo "go lines: $(wc -l < "$work/go.txt" | tr -d ' ')"
echo "lean lines: $(wc -l < "$work/lean.txt" | tr -d ' ')"
# Each output must have one line per case.
if [ "$(wc -l < "$work/go.txt" | tr -d ' ')" != "$cases" ]; then
  echo "the Go output does not have one line per case" >&2
  exit 1
fi
if cmp "$work/go.txt" "$work/lean.txt"; then
  echo "equal: Go and Lean agree on all $cases cases"
else
  echo "the outputs are different. These are the different lines:" >&2
  diff "$work/go.txt" "$work/lean.txt" >&2 || true
  exit 1
fi
