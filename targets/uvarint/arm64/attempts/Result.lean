module
import Uvarint.Arm64.Statements
import all Kraken.AArch64.Semantics
import all Kraken.Layout

open Uvarint.Arm64

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- This attempt must fail until the spill, loop invariant, and all exit obligations have proofs. -/
theorem full_result_attempt : result_statement := by
  intro s buf spill R hspill hlength hcapacity hbound hpointer hstack hstackbound hreturn hmem
  cases outcome : Uvarint.decode buf
  all_goals
    apply step_cps
    simp [Kraken.Layout.start, Kraken.Layout.size, step1, Executable.step, Code.executable,
      Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses.eq_1,
      Kraken.Executable.withAddresses.eq_2, Code.layout, Code.uvarint, Kraken.Layout.apply,
      Directives.interp.eq_1, Directives.interp.eq_2, Directive.interp, Instr.interp, Operation.interp,
      Effects.All, AddrExpr.interpStore, AddrExpr.checkSPAlignment, AddrExpr.eval]
