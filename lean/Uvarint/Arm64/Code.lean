module
public import Machine.Arm64.Include

@[expose] public section

namespace Uvarint.Arm64.Code

/-- Go 1.26.10 linux/arm64 Uvarint: 40 instructions and six labels. -/
def uvarint : Program := include_arm64_code "../targets/uvarint/arm64/build/norm/encoding_binary.Uvarint.S"

end Uvarint.Arm64.Code
