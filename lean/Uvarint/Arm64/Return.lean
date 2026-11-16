module
public import Uvarint.Arm64.ReturnStatement
import all Kraken.AArch64.Semantics
import all Kraken.Layout

public section

open Uvarint.Arm64.Code

namespace Uvarint.Arm64

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- All four compiled returns branch to x30, without a stack pop or a memory change. -/
theorem returns : return_statement (layout uvarint uvarint) .X30 := by
  intro s pc hp
  simp [List.mem_cons] at hp
  rcases hp with h | h | h | h <;> subst pc
  all_goals
    apply step_cps
    simp [Kraken.Layout.start, Kraken.Layout.size, step1, Executable.step, Kraken.Executable.directivesAtAddress,
      Kraken.Executable.withAddresses.eq_1, Kraken.Executable.withAddresses.eq_2, layout, uvarint, Kraken.Layout.apply,
      Directives.interp.eq_1, Directives.interp.eq_2, Directive.interp, Instr.interp, Operation.interp,
      Effects.All, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, Reg64s.getXReg,
      BitVec.take, BitVec.signed]

    apply Eventually.done
    constructor
    · simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, Reg64s.getXReg, RegOrZr.base,
        BitVec.take, BitVec.signed, Int64.ofInt, Int64.ofBitVec, UInt64.toInt64]
    · rfl

end Uvarint.Arm64
