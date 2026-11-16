import Uvarint.Amd64.WitnessDecodeResult

/-! The main theorem and the witnesses of the uvarint target. The axioms gate checks that each name is in its dump. -/

#print axioms Uvarint.Amd64.Decode.result
#print axioms Uvarint.Amd64.Witness.DecodeResult.premises_hold
#print axioms Uvarint.Amd64.Witness.DecodeResult.runs
#print axioms Uvarint.Amd64.Witness.DecodeResult.runs_empty
#print axioms Uvarint.Amd64.Witness.DecodeResult.runs_one_byte
#print axioms Uvarint.Amd64.Witness.DecodeResult.runs_maximum
