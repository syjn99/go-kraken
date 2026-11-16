module
public import Uvarint.Arm64.Code
public import Kraken.AArch64.Semantics

@[expose] public section

namespace Uvarint.Arm64.Code

/-- Instruction addresses and sizes follow the pinned ELF. Labels occupy no bytes. -/
def layout (code : Program) : Layout where
  start := 0x8d090
  size i := match code[i]? with
    | some (.instr _) => 4
    | _ => 0

instance : Layout := layout uvarint

def executable : Executable := layout uvarint uvarint

end Uvarint.Arm64.Code
