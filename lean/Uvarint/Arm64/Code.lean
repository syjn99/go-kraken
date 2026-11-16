import Machine.Arm64.Include
import Kraken.AArch64.Semantics

namespace Uvarint.Arm64.Code

/-- Go 1.26.10 linux/arm64 Uvarint: 40 instructions and six labels. -/
def uvarint : Program := include_arm64_code "../targets/uvarint/build-arm64/norm/encoding_binary.Uvarint.S"

/-- Instruction addresses and sizes follow the pinned ELF. Labels occupy no bytes. -/
instance layout : Layout where
  start := 0x8d090
  size i := match uvarint[i]? with
    | some (.instr _) => 4
    | _ => 0

def executable : Executable := layout uvarint

end Uvarint.Arm64.Code
