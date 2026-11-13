//! Standalone wrapper AIRs for Pico's gadgets, so each gadget's constraints can be extracted on
//! their own. A wrapper lays out the gadget's inputs, its column struct and its flags in a fixed
//! column order (the one `PicoFV/RV64IM/Airs/` uses) and calls the gadget's `eval` on them.

use std::borrow::Borrow;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::Field;
use pico_mle_core::air::{any_air::BaseAirWithPublicValues, symbolic::SymbolicRapBuilder};
use pico_vm::{
    chips::gadgets::{
        add::AddGadget, addw::AddwGadget, bitwise::BitWiseGadget, bitwise_u16::BitWiseU16Gadget,
        is_equal_word::IsEqualWordGadget, is_zero::IsZeroGadget, is_zero_word::IsZeroWordGadget,
        lt_signed::LtSignedGadget, lt_unsigned::LtUnsignedGadget, lt_word_u16::LtWordU16Gadget,
        msb::U16MSBGadget, mul::MulGadget, sub::SubGadget, subw::SubwGadget,
        u16_to_u8::U16ToU8Gadget,
    },
    compiler::word::Word,
};

#[derive(Clone, Copy, Debug)]
pub enum Gadget {
    Add,
    Sub,
    Addw,
    Subw,
    U16Msb,
    IsZero,
    IsZeroWord,
    IsEqualWord,
    LtWordU16,
    LtSigned,
    LtUnsigned,
    Bitwise,
    BitwiseU16,
    Mul,
    U16ToU8Safe,
    U16ToU8Unsafe,
}

pub const ALL: [Gadget; 16] = [
    Gadget::Add,
    Gadget::Sub,
    Gadget::Addw,
    Gadget::Subw,
    Gadget::U16Msb,
    Gadget::IsZero,
    Gadget::IsZeroWord,
    Gadget::IsEqualWord,
    Gadget::LtWordU16,
    Gadget::LtSigned,
    Gadget::LtUnsigned,
    Gadget::Bitwise,
    Gadget::BitwiseU16,
    Gadget::Mul,
    Gadget::U16ToU8Safe,
    Gadget::U16ToU8Unsafe,
];

impl Gadget {
    /// The Lean namespace of the extracted module.
    pub fn lean_name(self) -> &'static str {
        match self {
            Gadget::Add => "AddGadget",
            Gadget::Sub => "SubGadget",
            Gadget::Addw => "AddwGadget",
            Gadget::Subw => "SubwGadget",
            Gadget::U16Msb => "U16MSBGadget",
            Gadget::IsZero => "IsZeroGadget",
            Gadget::IsZeroWord => "IsZeroWordGadget",
            Gadget::IsEqualWord => "IsEqualWordGadget",
            Gadget::LtWordU16 => "LtWordU16Gadget",
            Gadget::LtSigned => "LtSignedGadget",
            Gadget::LtUnsigned => "LtUnsignedGadget",
            Gadget::Bitwise => "BitwiseGadget",
            Gadget::BitwiseU16 => "BitwiseU16Gadget",
            Gadget::Mul => "MulGadget",
            Gadget::U16ToU8Safe => "U16ToU8GadgetSafe",
            Gadget::U16ToU8Unsafe => "U16ToU8GadgetUnsafe",
        }
    }
}

impl<F: Field> BaseAir<F> for Gadget {
    fn width(&self) -> usize {
        match self {
            Gadget::Add | Gadget::Sub => 13,
            Gadget::Addw | Gadget::Subw => 12,
            Gadget::U16Msb => 3,
            Gadget::IsZero => 4,
            Gadget::IsZeroWord => 16,
            Gadget::IsEqualWord | Gadget::LtSigned => 20,
            Gadget::LtWordU16 => 17,
            Gadget::LtUnsigned => 15,
            Gadget::Bitwise | Gadget::BitwiseU16 => 26,
            Gadget::Mul => 63,
            Gadget::U16ToU8Safe | Gadget::U16ToU8Unsafe => 9,
        }
    }
}

impl<F: Field> BaseAirWithPublicValues<F> for Gadget {}

fn word<V: Copy>(s: &[V]) -> Word<V> {
    Word(core::array::from_fn(|i| s[i]))
}

fn expr_word<V: Copy, E: From<V>>(s: &[V]) -> Word<E> {
    Word(core::array::from_fn(|i| s[i].into()))
}

fn expr_array<V: Copy, E: From<V>, const N: usize>(s: &[V]) -> [E; N] {
    core::array::from_fn(|i| s[i].into())
}

impl<F: Field> Air<SymbolicRapBuilder<F>> for Gadget {
    fn eval(&self, builder: &mut SymbolicRapBuilder<F>) {
        // Owned copy of the row, so `builder` is free to be borrowed mutably by the gadget.
        let local = builder.main().current_slice().to_vec();
        let l = &local[..];
        match self {
            Gadget::Add => AddGadget::<F>::eval(
                builder,
                word(&l[0..4]),
                word(&l[4..8]),
                *l[8..12].borrow(),
                l[12],
            ),
            Gadget::Sub => SubGadget::<F>::eval(
                builder,
                word(&l[0..4]),
                word(&l[4..8]),
                *l[8..12].borrow(),
                l[12].into(),
            ),
            Gadget::Addw => AddwGadget::<F>::eval(
                builder,
                expr_word(&l[0..4]),
                expr_word(&l[4..8]),
                *l[8..11].borrow(),
                l[11].into(),
            ),
            Gadget::Subw => SubwGadget::<F>::eval(
                builder,
                word(&l[0..4]),
                word(&l[4..8]),
                *l[8..11].borrow(),
                l[11].into(),
            ),
            Gadget::U16Msb => {
                U16MSBGadget::<F>::eval(builder, l[0].into(), *l[1..2].borrow(), l[2].into())
            }
            Gadget::IsZero => {
                IsZeroGadget::<F>::eval(builder, l[0].into(), *l[1..3].borrow(), l[3].into())
            }
            Gadget::IsZeroWord => IsZeroWordGadget::<F>::eval(
                builder,
                expr_word(&l[0..4]),
                *l[4..15].borrow(),
                l[15].into(),
            ),
            Gadget::IsEqualWord => IsEqualWordGadget::<F>::eval(
                builder,
                expr_word(&l[0..4]),
                expr_word(&l[4..8]),
                *l[8..19].borrow(),
                l[19].into(),
            ),
            Gadget::LtWordU16 => LtWordU16Gadget::<F>::eval(
                builder,
                expr_word(&l[0..4]),
                expr_word(&l[4..8]),
                *l[8..16].borrow(),
                l[16].into(),
            ),
            Gadget::LtSigned => LtSignedGadget::<F>::eval(
                builder,
                word(&l[0..4]),
                word(&l[4..8]),
                *l[8..18].borrow(),
                l[18],
                l[19].into(),
            ),
            Gadget::LtUnsigned => LtUnsignedGadget::<F>::eval(
                builder,
                expr_word(&l[0..4]),
                expr_word(&l[4..8]),
                *l[8..14].borrow(),
                l[14].into(),
            ),
            Gadget::Bitwise => BitWiseGadget::<F>::eval(
                builder,
                expr_array(&l[0..8]),
                expr_array(&l[8..16]),
                *l[16..24].borrow(),
                l[24].into(),
                l[25].into(),
            ),
            Gadget::BitwiseU16 => {
                BitWiseU16Gadget::<F>::eval(
                    builder,
                    expr_word(&l[0..4]),
                    expr_word(&l[4..8]),
                    *l[8..24].borrow(),
                    l[24].into(),
                    l[25].into(),
                );
            }
            Gadget::Mul => MulGadget::<F>::eval(
                builder,
                word(&l[0..4]),
                word(&l[4..8]),
                word(&l[8..12]),
                *l[12..57].borrow(),
                l[57].into(),
                l[58].into(),
                l[59].into(),
                l[60].into(),
                l[61].into(),
                l[62].into(),
            ),
            Gadget::U16ToU8Safe => {
                U16ToU8Gadget::<F>::eval_u16_to_u8_safe(
                    builder,
                    expr_array(&l[0..4]),
                    *l[4..8].borrow(),
                    l[8].into(),
                );
            }
            Gadget::U16ToU8Unsafe => {
                U16ToU8Gadget::<F>::eval_u16_to_u8_unsafe(
                    builder,
                    expr_array(&l[0..4]),
                    *l[4..8].borrow(),
                );
            }
        }
    }
}
