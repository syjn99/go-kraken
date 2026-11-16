import Kraken.X64.Parser
import Machine.Include

/-!
# Code of `encoding/binary.Uvarint` (Go 1.26.10, linux/amd64, GOAMD64=v1)

The converted assembly of the pilot target. `go-kraken/tools/convert_objdump.py` writes the file.
-/

namespace Uvarint

/-- `encoding/binary.Uvarint` (`encoding/binary/varint.go`). 6 labels and 47 instructions. -/
def Code.uvarint : Program := include_x64_code "../targets/uvarint/build/norm/encoding_binary.Uvarint.S"

end Uvarint
