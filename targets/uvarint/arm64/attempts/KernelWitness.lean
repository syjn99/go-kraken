module
import Uvarint.Arm64.WitnessProofs
import all Kraken.AArch64.Semantics
import all Kraken.Layout
import all Kraken.Mem
import all Kraken.ToBytes

open Uvarint.Arm64 Uvarint.Arm64.Witness

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Kernel reduction does not currently establish the concrete empty execution. -/
theorem empty_attempt : execution_statement Code.executable [] (0, 0) := by
  apply check_sound
  decide +kernel

/-- Kernel reduction does not currently establish the concrete normal execution. -/
theorem value_attempt : execution_statement Code.executable [1] (1, 1) := by
  apply check_sound
  decide +kernel

/-- Kernel reduction does not currently establish the concrete overflow execution. -/
theorem overflow_attempt : execution_statement Code.executable (List.replicate 9 0xFF ++ [2])
    (0, UInt64.ofInt (-10)) := by
  apply check_sound
  decide +kernel
