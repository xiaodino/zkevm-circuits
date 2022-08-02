use crate::{evm_circuit::util::constraint_builder::BaseConstraintBuilder, util::Expr};
use eth_types::Field;
use gadgets::util::{not, select};
use halo2_proofs::circuit::AssignedCell;
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

const KECCAK_WIDTH: usize = 5 * 5 * 64;
const KECCAK_RATE: usize = 1088;
const KECCAK_RATE_IN_BYTES: usize = KECCAK_RATE / 8;

const KECCAK_DATA_REGION_WIDTH: usize = 64;
const KECCAK_REGION_HEIGHT: usize = KECCAK_RATE / KECCAK_DATA_REGION_WIDTH;

#[rustfmt::skip]
/// KeccakMultiGadgetPaddingConfig
/// Circuit Layout is like this, each row is a KeccakSubRowConfig with 64 bits data.
///        +-----------+-----------------+--------------+---------------+-------------+----------------+------------+
/// 1st      prev_xxxx    d_bits[0..64]    d_lens[0..8]   s_flags[0..8]   d_rlcs[0..8]  curr_last_xxxx   randomness  
///        +-----------+-----------------+--------------+---------------+-------------+----------------+------------+
///                                                                                             |            |
///            +--------------------------------------------------------------------------------+            |
///            |                                                                                             |
///        +-----------+-----------------+--------------+---------------+-------------+----------------+------------+
/// 2nd      prev_xxxx    d_bits[0..64]    d_lens[0..8]   s_flags[0..8]   d_rlcs[0..8]  curr_last_xxxx   randomness   
///  .     +-----------+-----------------+--------------+---------------+-------------+----------------+------------+
///  .                                                                                          |            |
/// (middle)   +--------------------------------------------------------------------------------+            |
///  .         |                                                                                             |
///  .     +-----------+-----------------+--------------+---------------+-------------+----------------+------------+
/// 15th     prev_xxxx    d_bits[0..64]    d_lens[0..8]   s_flags[0..8]   d_rlcs[0..8]  curr_last_xxxx   randomness  
///  .     +-----------+-----------------+--------------+---------------+-------------+----------------+------------+
///                                                                                             |            |
///            +--------------------------------------------------------------------------------+            |
///            |                                                                                             |
///        +-----------+-----------------+--------------+---------------+-------------+----------------+------------+
/// last     prev_xxxx    d_bits[0..64]    d_lens[0..8]   s_flags[0..8]   d_rlcs[0..8]  curr_last_xxxx   randomness  
/// (16th) +-----------+-----------------+--------------+---------------+-------------+----------------+------------+
#[derive(Clone, Debug)]
pub struct KeccakMultiGadgetPaddingConfig<F> {
    q_enable: Selector,
    first_row_config: KeccakSubRowConfig<F>,
    middle_row_config: KeccakSubRowConfig<F>,
    last_row_config: KeccakSubRowConfig<F>,
    randomness: Column<Advice>,
    _marker: PhantomData<F>,
}

pub(crate) struct KeccakPaddingSubRow<F: Field> {
    pub(crate) q_end: u64,
    prev_len: u32,
    prev_rlc: F,
    prev_s_flag: bool,
    prev_padding_sum: u32,
    curr_len: u32,
    curr_rlc: F,
    curr_s_flag: bool,
    curr_padding_sum: u32,
    randomness: F,
    pub(crate) d_bits: [u8; KECCAK_DATA_REGION_WIDTH],
    pub(crate) d_lens: [u32; KECCAK_DATA_REGION_WIDTH / 8],
    pub(crate) d_rlcs: [F; KECCAK_DATA_REGION_WIDTH / 8],
    pub(crate) s_flags: [bool; KECCAK_DATA_REGION_WIDTH / 8],
}

///KeccakSubRowConfig
#[derive(Clone, Debug)]
pub struct KeccakSubRowConfig<F> {
    q_enable: Selector,
    q_end: Column<Advice>,
    prev_len: Column<Advice>,
    prev_rlc: Column<Advice>,
    prev_s_flag: Column<Advice>,
    prev_padding_sum: Column<Advice>,
    curr_len: Column<Advice>,
    curr_rlc: Column<Advice>,
    curr_s_flag: Column<Advice>,
    curr_padding_sum: Column<Advice>,
    d_bits: [Column<Advice>; KECCAK_DATA_REGION_WIDTH],
    d_lens: [Column<Advice>; KECCAK_DATA_REGION_WIDTH / 8],
    d_rlcs: [Column<Advice>; KECCAK_DATA_REGION_WIDTH / 8],
    s_flags: [Column<Advice>; KECCAK_DATA_REGION_WIDTH / 8],
    randomness: Column<Advice>,

    _marker: PhantomData<F>,
}

impl<F: Field> KeccakSubRowConfig<F> {
    fn configure(
        meta: &mut ConstraintSystem<F>,
        is_first_row: bool,
        is_last_row: bool,
    ) -> KeccakSubRowConfig<F> {
        let q_enable = meta.selector();
        let q_end = meta.advice_column();
        let prev_len = meta.advice_column();
        let prev_rlc = meta.advice_column();
        let prev_s_flag = meta.advice_column();
        let prev_padding_sum = meta.advice_column();
        let curr_len = meta.advice_column();
        let curr_rlc = meta.advice_column();
        let curr_s_flag = meta.advice_column();
        let curr_padding_sum = meta.advice_column();
        let d_bits = [(); KECCAK_DATA_REGION_WIDTH].map(|_| meta.advice_column());
        let d_lens = [(); KECCAK_DATA_REGION_WIDTH / 8].map(|_| meta.advice_column());
        let d_rlcs = [(); KECCAK_DATA_REGION_WIDTH / 8].map(|_| meta.advice_column());
        let s_flags = [(); KECCAK_DATA_REGION_WIDTH / 8].map(|_| meta.advice_column());
        let randomness = meta.advice_column();

        meta.enable_equality(prev_len);
        meta.enable_equality(prev_rlc);
        meta.enable_equality(prev_s_flag);
        meta.enable_equality(prev_padding_sum);
        meta.enable_equality(curr_len);
        meta.enable_equality(curr_rlc);
        meta.enable_equality(curr_s_flag);
        meta.enable_equality(curr_padding_sum);

        if is_first_row {
            meta.create_gate("prev should be 0 for the 1st row", |meta| {
                let mut cb = BaseConstraintBuilder::new(5);

                // len & rlc are passed down by previous circuit, they are not necessarily 0.
                cb.require_zero(
                    "prev_s_flag == 0",
                    meta.query_advice(prev_s_flag, Rotation::cur()),
                );
                cb.require_zero(
                    "prev_padding_sum == 0",
                    meta.query_advice(prev_padding_sum, Rotation::cur()),
                );

                cb.gate(meta.query_selector(q_enable))
            });
        }

        meta.create_gate("boolean checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            //TODO: could be removed if combined with keccak circuit?
            for data_bit in d_bits {
                let b = meta.query_advice(data_bit, Rotation::cur());
                cb.require_boolean("input data bit", b);
            }

            for s_flag in s_flags {
                let s = meta.query_advice(s_flag, Rotation::cur());
                cb.require_boolean("boolean state bit", s);
            }

            for i in 1..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                let s_i_sub1 = meta.query_advice(s_flags[i - 1], Rotation::cur());

                cb.require_boolean("boolean state switch", s_i - s_i_sub1);
            }

            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("padding bit checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            for i in 1..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                let s_i_sub1 = meta.query_advice(s_flags[i - 1], Rotation::cur());
                let d_bit_0 = meta.query_advice(d_bits[8 * i], Rotation::cur());
                let s_padding_start = s_i - s_i_sub1;
                cb.condition(s_padding_start, |cb| {
                    cb.require_equal("start with 1", d_bit_0, 1u64.expr());
                });
            }

            if is_last_row {
                let s_last = meta.query_advice(s_flags[s_flags.len() - 1], Rotation::cur());
                let d_last = meta.query_advice(d_bits[d_bits.len() - 1], Rotation::cur());

                cb.condition(s_last, |cb| {
                    cb.require_equal("end with 1", d_last, 1u64.expr())
                });
            }
            cb.gate(meta.query_selector(q_enable))
        });

        if is_last_row {
            meta.create_gate("sum padding check", |meta| {
                let mut cb = BaseConstraintBuilder::new(5);

                let prev_padding_sum = meta.query_advice(prev_padding_sum, Rotation::cur());

                let mut sum_padding_bits = prev_padding_sum;
                for i in 0..s_flags.len() {
                    let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                    sum_padding_bits = d_bits[i * 8..(i + 1) * 8]
                        .iter()
                        .map(|b| meta.query_advice(*b, Rotation::cur()))
                        .fold(sum_padding_bits, |sum, b| sum + s_i.clone() * b);
                }

                cb.require_equal("sum(padding_bits) == 2", sum_padding_bits, 2u64.expr());
                cb.gate(meta.query_selector(q_enable))
            });
        } else {
            meta.create_gate("sum padding", |meta| {
                let mut cb = BaseConstraintBuilder::new(5);

                let prev_padding_sum = meta.query_advice(prev_padding_sum, Rotation::cur());
                let curr_padding_sum = meta.query_advice(curr_padding_sum, Rotation::cur());

                let mut sum_padding_bits = prev_padding_sum;
                for i in 0..s_flags.len() {
                    let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                    sum_padding_bits = d_bits[i * 8..(i + 1) * 8]
                        .iter()
                        .map(|b| meta.query_advice(*b, Rotation::cur()))
                        .fold(sum_padding_bits, |sum, b| sum + s_i.clone() * b);
                }

                cb.require_equal(
                    "sum(padding_bits) == curr_padding_sum",
                    sum_padding_bits,
                    curr_padding_sum,
                );
                cb.gate(meta.query_selector(q_enable))
            });
        }

        meta.create_gate("input len check", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let len_0 = meta.query_advice(d_lens[0], Rotation::cur());
            let prev_len = meta.query_advice(prev_len, Rotation::cur());
            let s_0 = meta.query_advice(s_flags[0], Rotation::cur());

            cb.require_equal("len[0] = prev_len + !s_0", len_0, prev_len + not::expr(s_0));

            for i in 1..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                let len_i = meta.query_advice(d_lens[i], Rotation::cur());
                let len_i_sub1 = meta.query_advice(d_lens[i - 1], Rotation::cur());
                cb.require_equal(
                    "len[i] = len[i-1] + !s_i",
                    len_i,
                    len_i_sub1 + not::expr(s_i),
                );
            }

            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("input rlc check", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let s_0 = meta.query_advice(s_flags[0], Rotation::cur());
            let rlc_0 = meta.query_advice(d_rlcs[0], Rotation::cur());
            let rlc_prev = meta.query_advice(prev_rlc, Rotation::cur());
            let r = meta.query_advice(randomness, Rotation::cur());
            let input_byte_0 = d_bits[0..8]
                .iter()
                .map(|bit| meta.query_advice(*bit, Rotation::cur()))
                .fold(0u64.expr(), |v, b| v * 2u64.expr() + b);
            cb.require_equal(
                "rlc[i] = rlc[i-1]*r if s == 0 else rlc[i]",
                rlc_0,
                select::expr(s_0, rlc_prev.clone(), rlc_prev.clone() * r + input_byte_0),
            );

            for i in 1..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                let rlc_i = meta.query_advice(d_rlcs[i], Rotation::cur());
                let rlc_i_sub1 = meta.query_advice(d_rlcs[i - 1], Rotation::cur());
                let r = meta.query_advice(randomness, Rotation::cur());
                let input_byte_i = d_bits[i * 8..(i + 1) * 8]
                    .iter()
                    .map(|bit| meta.query_advice(*bit, Rotation::cur()))
                    .fold(0u64.expr(), |v, b| v * 2u64.expr() + b);
                cb.require_equal(
                    "rlc[i] = rlc[i-1]*r if s == 0 else rlc[i]",
                    rlc_i,
                    select::expr(
                        s_i,
                        rlc_i_sub1.clone(),
                        rlc_i_sub1.clone() * r + input_byte_i,
                    ),
                );
            }

            cb.gate(meta.query_selector(q_enable))
        });

        if is_last_row {
            meta.create_gate("input ending check", |meta| {
                let mut cb = BaseConstraintBuilder::new(5);

                let s_last = meta.query_advice(s_flags[s_flags.len() - 1], Rotation::cur());
                let q_end = meta.query_advice(q_end, Rotation::cur());

                cb.require_equal("s_last == q_end", s_last, q_end);
                cb.gate(meta.query_selector(q_enable))
            });
        }

        KeccakSubRowConfig {
            q_enable,
            q_end,
            prev_len,
            prev_rlc,
            prev_s_flag,
            prev_padding_sum,
            curr_len,
            curr_rlc,
            curr_s_flag,
            curr_padding_sum,
            d_bits,
            d_lens,
            d_rlcs,
            s_flags,

            randomness,
            _marker: PhantomData,
        }
    }

    /// Returns (last_len, last_rlc, last_s, randomness)
    fn process(
        &self,
        mut layouter: &mut impl Layouter<F>,
        prev_len: &AssignedCell<F, F>,
        prev_rlc: &AssignedCell<F, F>,
        prev_s_flag: &AssignedCell<F, F>,
        prev_padding_sum: &AssignedCell<F, F>,
        curr_sub_row: &KeccakPaddingSubRow<F>,
        row_idx: u32,
    ) -> Result<
        (
            AssignedCell<F, F>,
            AssignedCell<F, F>,
            AssignedCell<F, F>,
            AssignedCell<F, F>,
        ),
        Error,
    > {
        // copy prev to current row
        layouter.assign_region(
            || format!("assign keccak sub row round {}", row_idx),
            |mut region| {
                self.set_row(
                    &mut region,
                    0,
                    curr_sub_row.q_end,
                    prev_len,
                    prev_rlc,
                    prev_s_flag,
                    prev_padding_sum,
                    curr_sub_row,
                )
            },
        )
    }

    fn set_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        q_end: u64,
        prev_len: &AssignedCell<F, F>,
        prev_rlc: &AssignedCell<F, F>,
        prev_s_flag: &AssignedCell<F, F>,
        prev_padding_sum: &AssignedCell<F, F>,
        curr_sub_row: &KeccakPaddingSubRow<F>,
    ) -> Result<
        (
            AssignedCell<F, F>,
            AssignedCell<F, F>,
            AssignedCell<F, F>,
            AssignedCell<F, F>,
        ),
        Error,
    > {
        let d_bits = curr_sub_row.d_bits;
        let d_lens = curr_sub_row.d_lens;
        let d_rlcs = curr_sub_row.d_rlcs;
        let s_flags = curr_sub_row.s_flags;
        let randomness = curr_sub_row.randomness;

        self.q_enable.enable(region, offset)?;

        // copy prev values
        prev_len.copy_advice(|| "prev len", region, self.prev_len, offset)?;
        prev_rlc.copy_advice(|| "prev rlc", region, self.prev_rlc, offset)?;
        prev_s_flag.copy_advice(|| "prev s_flag", region, self.prev_s_flag, offset)?;
        prev_padding_sum.copy_advice(
            || "prev padding sum",
            region,
            self.prev_padding_sum,
            offset,
        )?;

        // Input bits w/ padding
        for (idx, (bit, column)) in d_bits.iter().zip(self.d_bits.iter()).enumerate() {
            region.assign_advice(
                || format!("assign input data bit {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
            )?;
        }

        for (idx, (s_flag, column)) in s_flags.iter().zip(self.s_flags.iter()).enumerate() {
            region.assign_advice(
                || format!("assign input data select flag {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*s_flag as u64)),
            )?;
        }

        for (idx, (d_len, column)) in d_lens.iter().zip(self.d_lens.iter()).enumerate() {
            region.assign_advice(
                || format!("assign input data len {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*d_len as u64)),
            )?;
        }

        for (idx, (d_rlc, column)) in d_rlcs.iter().zip(self.d_rlcs.iter()).enumerate() {
            region.assign_advice(
                || format!("assign input data rlc {} {}", idx, offset),
                *column,
                offset,
                || Ok(*d_rlc),
            )?;
        }

        region.assign_advice(
            || format!("assign q_end{}", offset),
            self.q_end,
            offset,
            || Ok(F::from(q_end)),
        )?;

        region.assign_advice(
            || format!("assign randomness{}", offset),
            self.randomness,
            offset,
            || Ok(randomness),
        )?;

        // output the curr len,rlc,s_flag & padding
        let curr_len = region.assign_advice(
            || format!("assign curr_len{}", offset),
            self.curr_len,
            offset,
            || Ok(F::from(curr_sub_row.curr_len as u64)),
        )?;

        let curr_rlc = region.assign_advice(
            || format!("assign curr_rlc{}", offset),
            self.curr_rlc,
            offset,
            || Ok(curr_sub_row.curr_rlc),
        )?;

        let curr_s_flag = region.assign_advice(
            || format!("assign curr_s_flag{}", offset),
            self.curr_s_flag,
            offset,
            || Ok(F::from(curr_sub_row.curr_s_flag)),
        )?;

        let curr_padding_sum = region.assign_advice(
            || format!("assign curr_padding_sum{}", offset),
            self.curr_padding_sum,
            offset,
            || Ok(F::from(curr_sub_row.curr_padding_sum as u64)),
        )?;

        Ok((curr_len, curr_rlc, curr_s_flag, curr_padding_sum))
    }
}

/// KeccakPaddingCircuit
#[derive(Default)]
pub struct KeccakMultiGadgetPaddingCircuit<F: Field> {
    inputs: Vec<KeccakPaddingSubRow<F>>,
    size: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> KeccakMultiGadgetPaddingCircuit<F> {
    fn r() -> F {
        F::from(123456)
    }
}

impl<F: Field> Circuit<F> for KeccakMultiGadgetPaddingCircuit<F> {
    type Config = KeccakMultiGadgetPaddingConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        KeccakMultiGadgetPaddingConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.synthesize(
            &mut layouter,
            self.size,
            &self.inputs,
            KeccakMultiGadgetPaddingCircuit::r(),
        )?;
        Ok(())
    }
}

impl<F: Field> KeccakMultiGadgetPaddingConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.selector();
        let first_row_config = KeccakSubRowConfig::configure(meta, true, false);
        let middle_row_config = KeccakSubRowConfig::configure(meta, false, false);
        let last_row_config = KeccakSubRowConfig::configure(meta, false, true);
        let randomness = meta.advice_column();

        KeccakMultiGadgetPaddingConfig {
            q_enable,
            first_row_config,
            middle_row_config,
            last_row_config,
            randomness,
            _marker: PhantomData,
        }
    }

    pub(crate) fn synthesize(
        &self,
        mut layouter: &mut impl Layouter<F>,
        _size: usize,
        keccak_padding_row: &Vec<KeccakPaddingSubRow<F>>,
        randomness: F,
    ) -> Result<(), Error> {
        assert_eq!(keccak_padding_row.len(), 17);

        let mut prev_values = layouter.assign_region(
            || "assign prev value of the first row",
            |mut region| {
                let offset = 0;
                //TODO: rlc and len should be a input from previous circuit
                let prev_len = region.assign_advice(
                    || format!("assign prev_len{}", offset),
                    self.first_row_config.prev_len,
                    offset,
                    || Ok(F::from(keccak_padding_row[0].prev_len as u64)),
                )?;
                let prev_rlc = region.assign_advice(
                    || format!("assign prev_rlc{}", offset),
                    self.first_row_config.prev_rlc,
                    offset,
                    || Ok(keccak_padding_row[0].prev_rlc),
                )?;
                let prev_s_flag = region.assign_advice(
                    || format!("assign prev_s_flag{}", offset),
                    self.first_row_config.prev_s_flag,
                    offset,
                    || Ok(F::zero()),
                )?;
                let prev_padding_sum = region.assign_advice(
                    || format!("assign prev_padding_sum{}", offset),
                    self.first_row_config.prev_padding_sum,
                    offset,
                    || Ok(F::zero()),
                )?;
                Ok((prev_len, prev_rlc, prev_s_flag, prev_padding_sum))
            },
        )?;

        let mut prev_len = prev_values.0;
        let mut prev_rlc = prev_values.1;
        let mut prev_s_flag = prev_values.2;
        let mut prev_padding_sum = prev_values.3;

        prev_values = self.first_row_config.process(
            layouter,
            &prev_len,
            &prev_rlc,
            &prev_s_flag,
            &prev_padding_sum,
            &keccak_padding_row[0],
            0,
        )?;

        prev_len = prev_values.0;
        prev_rlc = prev_values.1;
        prev_s_flag = prev_values.2;
        prev_padding_sum = prev_values.3;

        for i in 1..16 {
            prev_values = self.middle_row_config.process(
                layouter,
                &prev_len,
                &prev_rlc,
                &prev_s_flag,
                &prev_padding_sum,
                &keccak_padding_row[i],
                i as u32,
            )?;

            prev_len = prev_values.0;
            prev_rlc = prev_values.1;
            prev_s_flag = prev_values.2;
            prev_padding_sum = prev_values.3;
        }

        self.last_row_config.process(
            layouter,
            &prev_len,
            &prev_rlc,
            &prev_s_flag,
            &prev_padding_sum,
            &keccak_padding_row[16],
            16 as u32,
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use crate::keccak_circuit::keccak_padding::KeccakPaddingRow;

    use super::*;
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr};

    fn verify<F: Field>(k: u32, inputs: Vec<KeccakPaddingSubRow<F>>, success: bool) {
        let circuit = KeccakMultiGadgetPaddingCircuit::<F> {
            inputs,
            size: 2usize.pow(k),
            _marker: PhantomData,
        };

        let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
        let err = prover.verify();
        let print_failures = true;
        if err.is_err() && print_failures {
            for e in err.err().iter() {
                for s in e.iter() {
                    println!("{}", s);
                }
            }
        }
        let err = prover.verify();
        assert_eq!(err.is_ok(), success);
    }

    fn generate_padding_sub_rows<F: Field>(data_len: u32) -> Vec<KeccakPaddingSubRow<F>> {
        let mut keccak_padding = KeccakPaddingRow::<F> {
            d_bits: [0; KECCAK_WIDTH],
            d_lens: [0; KECCAK_RATE_IN_BYTES],
            d_rlcs: [F::from(0u64); KECCAK_RATE_IN_BYTES],
            s_flags: [false; KECCAK_RATE_IN_BYTES],
            q_end: 1u64,
        };

        let data_len_offset = data_len % KECCAK_RATE_IN_BYTES as u32;
        let data_len_base = (data_len / KECCAK_RATE_IN_BYTES as u32) * KECCAK_RATE_IN_BYTES as u32;

        keccak_padding.s_flags[0] = data_len_offset == 0u32;
        keccak_padding.d_lens[0] = data_len_base + !keccak_padding.s_flags[0] as u32;

        for i in 1 as usize..KECCAK_RATE_IN_BYTES {
            keccak_padding.s_flags[i] = {
                if (i as u32) < data_len_offset {
                    false
                } else {
                    true
                }
            };
            keccak_padding.d_lens[i] =
                keccak_padding.d_lens[i - 1] + !keccak_padding.s_flags[i] as u32;
        }

        for i in data_len_offset as usize..KECCAK_RATE {
            keccak_padding.d_bits[i] = 0u8;
        }
        keccak_padding.d_bits[data_len_offset as usize * 8] = 1;
        keccak_padding.d_bits[KECCAK_RATE - 1] = 1;

        println!("{:?}", keccak_padding.s_flags);
        println!("{:?}", keccak_padding.d_bits);
        println!("{:?}", keccak_padding.d_lens);

        let mut out = Vec::<KeccakPaddingSubRow<F>>::new();
        let mut curr_len = data_len_base;
        let mut curr_rlc = F::zero();
        let mut curr_s_flag = false;
        let mut curr_padding_sum = 0;
        let randomness = KeccakMultiGadgetPaddingCircuit::r();

        for i in 0..KECCAK_RATE / 64 {
            let prev_len = curr_len;
            let prev_rlc = curr_rlc;
            let prev_s_flag = curr_s_flag;
            let prev_padding_sum = curr_padding_sum;

            curr_len = keccak_padding.s_flags[i * 8..(i + 1) * 8]
                .iter()
                .fold(prev_len, |sum, v| sum + (!v as u32));
            curr_rlc = keccak_padding.d_bits[i * 64..(i + 1) * 64]
                .chunks(8)
                .map(|bits| bits.iter().fold(0, |byte, bit| byte * 2 + bit))
                .zip(keccak_padding.s_flags[i * 8..(i + 1) * 8].iter())
                .fold(prev_rlc, |rlc, (byte, flag)| {
                    rlc * randomness + F::from(byte as u64 * (!flag as u64))
                });
            curr_s_flag = keccak_padding.s_flags[(i + 1) * 8 - 1];
            curr_padding_sum = keccak_padding.d_bits[i * 64..(i + 1) * 64]
                .iter()
                .enumerate()
                .fold(prev_padding_sum, |sum, (idx, v)| {
                    println!(
                        "{} + {} * {}",
                        sum,
                        *v,
                        keccak_padding.s_flags[i * 8 + idx / 8]
                    );
                    sum + (*v as u32) * (keccak_padding.s_flags[i * 8 + idx / 8] as u32)
                });
            println!("{}", curr_padding_sum);
            assert!(curr_padding_sum <= 2);

            let sub_row = KeccakPaddingSubRow::<F> {
                q_end: 1u64,
                prev_len,
                prev_rlc,
                prev_s_flag,
                prev_padding_sum,
                curr_len: curr_len,
                curr_rlc: curr_rlc,
                curr_s_flag: curr_s_flag,
                curr_padding_sum: curr_padding_sum,
                randomness: randomness,
                d_bits: keccak_padding.d_bits[i * 64..(i + 1) * 64]
                    .try_into()
                    .unwrap(),
                d_lens: keccak_padding.d_lens[i * 8..(i + 1) * 8]
                    .try_into()
                    .unwrap(),
                d_rlcs: keccak_padding.d_rlcs[i * 8..(i + 1) * 8]
                    .try_into()
                    .unwrap(),
                s_flags: keccak_padding.s_flags[i * 8..(i + 1) * 8]
                    .try_into()
                    .unwrap(),
            };
            out.push(sub_row);
        }

        out
    }

    static K: u32 = 8;

    #[test]
    fn bit_keccak_len_0() {
        let input = generate_padding_sub_rows::<Fr>(0);
        verify::<Fr>(K, input, true);
    }

    #[test]
    fn bit_keccak_len_1() {
        let input = generate_padding_sub_rows::<Fr>(1);
        verify::<Fr>(K, input, true);
    }

    #[test]
    fn bit_keccak_len_2() {
        let input = generate_padding_sub_rows::<Fr>(2);
        verify::<Fr>(K, input, true);
    }

    #[test]
    fn bit_keccak_len_135() {
        let input = generate_padding_sub_rows::<Fr>(135);
        verify::<Fr>(K, input, true);
    }

    #[test]
    fn bit_keccak_len_300() {
        let input = generate_padding_sub_rows::<Fr>(300);
        verify::<Fr>(K, input, true);
    }

    #[test]
    fn bit_keccak_invalid_padding_begin() {
        // first bit is 0
        let mut input = generate_padding_sub_rows::<Fr>(11);
        input[1].d_bits[11 * 8 % 64] = 0u8;
        verify::<Fr>(K, input, false);
    }

    #[test]
    fn bit_keccak_invalid_padding_end() {
        // last bit is 0
        let mut input = generate_padding_sub_rows::<Fr>(73);
        let row_idx = (KECCAK_RATE - 1) / 64;
        let bit_idx = (KECCAK_RATE - 1) % 64;
        input[row_idx].d_bits[bit_idx] = 0u8;
        verify::<Fr>(K, input, false);
    }

    #[test]
    fn bit_keccak_invalid_padding_mid() {
        // some 1 in padding
        let mut input = generate_padding_sub_rows::<Fr>(123);
        let row_idx = (KECCAK_RATE - 2) / 64;
        let bit_idx = (KECCAK_RATE - 2) % 64;
        input[row_idx].d_bits[bit_idx] = 1u8;
        verify::<Fr>(K, input, false);
    }

    #[test]
    fn bit_keccak_invalid_input_len() {
        // wrong len
        let mut input = generate_padding_sub_rows::<Fr>(123);
        let row_idx = 124 / 8;
        let bit_idx = 124 % 8;
        input[row_idx].d_lens[bit_idx] = 124;
        verify::<Fr>(K, input, false);
    }
}
