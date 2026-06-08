import PicoFV.Fundamentals.Core
import PicoFV.Fundamentals.KoalaBear
import PicoFV.Fundamentals.Word
import PicoFV.Fundamentals.Interaction

import PicoFV.RV64IM.Transpiler.Transpiler

import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Buses
import PicoFV.RV64IM.RVSail.Execution
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Opcodes.Opcodes

-- Extracted constraint definitions (from Pico Rust source)
import PicoFV.RV64IM.Extraction.AddChip
import PicoFV.RV64IM.Extraction.AddGadget
import PicoFV.RV64IM.Extraction.AddwChip
import PicoFV.RV64IM.Extraction.AddwGadget
import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Extraction.BitwiseChip
import PicoFV.RV64IM.Extraction.BitwiseGadget
import PicoFV.RV64IM.Extraction.BitwiseU16Gadget
import PicoFV.RV64IM.Extraction.CpuChip
import PicoFV.RV64IM.Extraction.DivRemChip
import PicoFV.RV64IM.Extraction.IsEqualWordGadget
import PicoFV.RV64IM.Extraction.IsZeroGadget
import PicoFV.RV64IM.Extraction.IsZeroWordGadget
import PicoFV.RV64IM.Extraction.LtChip
import PicoFV.RV64IM.Extraction.LtSignedGadget
import PicoFV.RV64IM.Extraction.LtUnsignedGadget
import PicoFV.RV64IM.Extraction.LtWordU16Gadget
import PicoFV.RV64IM.Extraction.MemoryReadWriteChip
import PicoFV.RV64IM.Extraction.MulChip
import PicoFV.RV64IM.Extraction.MulGadget
import PicoFV.RV64IM.Extraction.SLLChip
import PicoFV.RV64IM.Extraction.ShiftRightChip
import PicoFV.RV64IM.Extraction.SubChip
import PicoFV.RV64IM.Extraction.SubGadget
import PicoFV.RV64IM.Extraction.SubwChip
import PicoFV.RV64IM.Extraction.SubwGadget
import PicoFV.RV64IM.Extraction.U16MSBGadget
import PicoFV.RV64IM.Extraction.U16ToU8GadgetSafe
import PicoFV.RV64IM.Extraction.U16ToU8GadgetUnsafe

-- Air wrappers (gadgets)
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.SubAirs
import PicoFV.RV64IM.Airs.U16MSBGadget
import PicoFV.RV64IM.Airs.U16ToU8GadgetUnsafe
import PicoFV.RV64IM.Airs.U16ToU8GadgetSafe
import PicoFV.RV64IM.Airs.IsZeroGadget
import PicoFV.RV64IM.Airs.IsZeroWordGadget
import PicoFV.RV64IM.Airs.IsEqualWordGadget
import PicoFV.RV64IM.Airs.AddGadget
import PicoFV.RV64IM.Airs.AddwGadget
import PicoFV.RV64IM.Airs.SubGadget
import PicoFV.RV64IM.Airs.SubwGadget
import PicoFV.RV64IM.Airs.BitwiseGadget
import PicoFV.RV64IM.Airs.BitwiseU16Gadget
import PicoFV.RV64IM.Airs.LtWordU16Gadget
import PicoFV.RV64IM.Airs.LtSignedGadget
import PicoFV.RV64IM.Airs.LtUnsignedGadget
import PicoFV.RV64IM.Airs.MulGadget

-- Air wrappers (chips)
import PicoFV.RV64IM.Airs.AddChip
import PicoFV.RV64IM.Airs.AddwChip
import PicoFV.RV64IM.Airs.SubChip
import PicoFV.RV64IM.Airs.SubwChip
import PicoFV.RV64IM.Airs.BitwiseChip
import PicoFV.RV64IM.Airs.LtChip
import PicoFV.RV64IM.Airs.MulChip
import PicoFV.RV64IM.Airs.SLLChip
import PicoFV.RV64IM.Airs.ShiftRightChip
import PicoFV.RV64IM.Airs.DivRemChip
import PicoFV.RV64IM.Airs.MemoryReadWriteChip
import PicoFV.RV64IM.Airs.CpuChip

-- Constraints (human-readable + identification lemmas)
import PicoFV.RV64IM.Constraints.AddGadget
import PicoFV.RV64IM.Constraints.AddChip
import PicoFV.RV64IM.Constraints.SubGadget
import PicoFV.RV64IM.Constraints.SubChip
import PicoFV.RV64IM.Constraints.AddwGadget
import PicoFV.RV64IM.Constraints.AddwChip
import PicoFV.RV64IM.Constraints.SubwGadget
import PicoFV.RV64IM.Constraints.SubwChip
import PicoFV.RV64IM.Constraints.BitwiseChip
import PicoFV.RV64IM.Constraints.U16MSBGadget
import PicoFV.RV64IM.Constraints.LtWordU16Gadget
import PicoFV.RV64IM.Constraints.LtSignedGadget
import PicoFV.RV64IM.Constraints.LtChip
import PicoFV.RV64IM.Constraints.SLLChip
import PicoFV.RV64IM.Constraints.ShiftRightChip
import PicoFV.RV64IM.Constraints.IsZeroGadget
import PicoFV.RV64IM.Constraints.IsZeroWordGadget
import PicoFV.RV64IM.Constraints.IsEqualWordGadget
import PicoFV.RV64IM.Constraints.U16ToU8GadgetSafe
import PicoFV.RV64IM.Constraints.MulGadget
import PicoFV.RV64IM.Constraints.MulChip
import PicoFV.RV64IM.Constraints.DivRemChip
import PicoFV.RV64IM.Constraints.MemoryReadWriteChip
import PicoFV.RV64IM.Constraints.CpuChip
import PicoFV.RV64IM.Constraints.CpuChipInterpretations

-- Spec (semantic specifications)
import PicoFV.RV64IM.Spec.AddGadget
import PicoFV.RV64IM.Spec.AddChip
import PicoFV.RV64IM.Spec.SubGadget
import PicoFV.RV64IM.Spec.SubChip
import PicoFV.RV64IM.Spec.AddwGadget
import PicoFV.RV64IM.Spec.AddwChip
import PicoFV.RV64IM.Spec.SubwGadget
import PicoFV.RV64IM.Spec.SubwChip
import PicoFV.RV64IM.Spec.BitwiseChip
import PicoFV.RV64IM.Spec.U16MSBGadget
import PicoFV.RV64IM.Spec.LtWordU16Gadget
import PicoFV.RV64IM.Spec.LtSignedGadget
import PicoFV.RV64IM.Spec.LtChip
import PicoFV.RV64IM.Spec.SLLChip
import PicoFV.RV64IM.Spec.ShiftRightChip
import PicoFV.RV64IM.Spec.IsZeroGadget
import PicoFV.RV64IM.Spec.IsZeroWordGadget
import PicoFV.RV64IM.Spec.IsEqualWordGadget
import PicoFV.RV64IM.Spec.U16ToU8GadgetSafe
import PicoFV.RV64IM.Spec.MulGadgetCore
import PicoFV.RV64IM.Spec.MulGadget
import PicoFV.RV64IM.Spec.MulChip
import PicoFV.RV64IM.Spec.DivRemChip
import PicoFV.RV64IM.Spec.MemoryReadWriteChip

-- Equivalence (Sail ↔ Pico)
import PicoFV.RV64IM.Equivalence.Equivalence
