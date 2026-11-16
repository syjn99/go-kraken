import Uvarint.Arm64.Code
import Kraken.AArch64.Semantics

namespace Uvarint.Arm64.Code

/-- Instruction addresses and sizes follow the pinned ELF. Labels occupy no bytes. -/
instance layout : Layout where
  start := 0x8d090
  size i := match uvarint[i]? with
    | some (.instr _) => 4
    | _ => 0

def executable : Executable := layout uvarint

end Uvarint.Arm64.Code
