import PicoFV.RV64IM.Equivalence.Common
import PicoFV.RV64IM.Equivalence.RType
import PicoFV.RV64IM.Equivalence.RTypeW
import PicoFV.RV64IM.Equivalence.IType
import PicoFV.RV64IM.Equivalence.Addiw
import PicoFV.RV64IM.Equivalence.ShiftIOp
import PicoFV.RV64IM.Equivalence.ShiftIWOp
import PicoFV.RV64IM.Equivalence.MulFamily
import PicoFV.RV64IM.Equivalence.DivFamily
import PicoFV.RV64IM.Equivalence.UType
import PicoFV.RV64IM.Equivalence.Jumps
import PicoFV.RV64IM.Equivalence.BType
import PicoFV.RV64IM.Equivalence.Stores
import PicoFV.RV64IM.Equivalence.Loads

/-! The RV64IM opcode equivalence theorems, one file per instruction class; `Common` holds
the definitions they share. -/
