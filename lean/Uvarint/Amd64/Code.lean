import Kraken.X64.Parser
import Machine.Amd64.Include

/-!
# Code of `encoding/binary.Uvarint` (Go 1.26.10, linux/amd64, GOAMD64=v1)

The converted assembly of the pilot target. `tools/convert_objdump.py` writes the assembly file.
-/

namespace Uvarint.Amd64.Code

/-- `encoding/binary.Uvarint` (`encoding/binary/varint.go`). 6 labels and 47 instructions. -/
def uvarint : Program := include_amd64_code "../targets/uvarint/amd64/build/norm/encoding_binary.Uvarint.S"

end Uvarint.Amd64.Code
