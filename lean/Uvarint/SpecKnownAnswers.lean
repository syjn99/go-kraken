module
public import Uvarint.Spec

@[expose] public section

namespace Uvarint

/-- Expected answers follow the base-128 format and the Go length rule. Both architectures share this table. -/
def knownAnswers : List (List UInt8 × Result) :=
  [([], .incomplete),
   ([0x00], .value 0 1),
   ([0x01], .value 1 1),
   ([0xAC, 0x02], .value 300 2),
   ([0x80], .incomplete),
   (List.replicate 9 0xFF ++ [0x01], .value 0xFFFFFFFFFFFFFFFF 10),
   (List.replicate 9 0xFF ++ [0x02], .overflow 10),
   (List.replicate 10 0x80 ++ [0x00], .overflow 11),
   (List.replicate 10 0x80, .incomplete)]

/-- The specification agrees with every independently stated answer. -/
theorem knownAnswers_correct : knownAnswers.all (fun c => decide (decode c.1 = c.2)) = true := by decide

end Uvarint
