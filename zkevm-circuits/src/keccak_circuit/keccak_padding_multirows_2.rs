use crate::{evm_circuit::util::constraint_builder::BaseConstraintBuilder, util::Expr};
use eth_types::Field;
use gadgets::util::{not, select};
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

const KECCAK_REGION_WIDTH: usize = 64;
const KECCAK_REGION_WIDTH_IN_BYTES: usize = KECCAK_REGION_WIDTH / 8;
const KECCAK_REGION_HEIGHT: u64 = 17;
const KECCAK_RATE: usize = 1088;
const KECCAK_RATE_IN_BYTES: usize = KECCAK_RATE / 8;

/// KeccakPaddingConfig
#[derive(Clone, Debug)]
pub struct KeccakPaddingConfig<F> {
    q_enable: Selector,
    q_end: Column<Advice>,
    is_first_row: Column<Fixed>,
    is_last_row: Column<Fixed>,
    curr_len: Column<Advice>,
    curr_rlc: Column<Advice>,
    curr_s_flag: Column<Advice>,
    curr_padding_sum: Column<Advice>,
    d_bits: [Column<Advice>; KECCAK_REGION_WIDTH],
    d_lens: [Column<Advice>; KECCAK_REGION_WIDTH / 8],
    d_rlcs: [Column<Advice>; KECCAK_REGION_WIDTH / 8],
    s_flags: [Column<Advice>; KECCAK_REGION_WIDTH / 8],
    randomness: Column<Advice>,

    _marker: PhantomData<F>,
}

#[derive(Debug)]
pub(crate) struct KeccakPaddingBlock<F: Field> {
    pub(crate) q_end: u64,
    pub(crate) acc_rlc: F,
    pub(crate) acc_len: u32,
    pub(crate) block_rows: [KeccakPaddingBlockRow<F>; KECCAK_REGION_HEIGHT as usize],
}

#[derive(Debug)]
pub(crate) struct KeccakPaddingBlockRow<F: Field> {
    pub(crate) curr_len: u32,
    pub(crate) curr_rlc: F,
    pub(crate) curr_s_flag: bool,
    pub(crate) curr_padding_sum: u32,
    pub(crate) d_bits: [u8; KECCAK_REGION_WIDTH],
    pub(crate) d_lens: [u32; KECCAK_REGION_WIDTH_IN_BYTES],
    pub(crate) d_rlcs: [F; KECCAK_REGION_WIDTH_IN_BYTES],
    pub(crate) s_flags: [bool; KECCAK_REGION_WIDTH_IN_BYTES],
}

/// KeccakPaddingCircuit
#[derive(Default)]
pub struct KeccakPaddingCircuit<F: Field> {
    inputs: Vec<KeccakPaddingBlock<F>>,
    size: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> KeccakPaddingCircuit<F> {
    fn r() -> F {
        F::from(123456)
    }
}

impl<F: Field> Circuit<F> for KeccakPaddingCircuit<F> {
    type Config = KeccakPaddingConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        KeccakPaddingConfig::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, layouter: impl Layouter<F>) -> Result<(), Error> {
        config.assign(
            layouter,
            self.size,
            &self.inputs[0],
            KeccakPaddingCircuit::r(),
        )?;
        Ok(())
    }
}

impl<F: Field> KeccakPaddingConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.selector();
        let q_end = meta.advice_column();
        let is_first_row = meta.fixed_column();
        let is_last_row = meta.fixed_column();
        let curr_len = meta.advice_column();
        let curr_rlc = meta.advice_column();
        let curr_s_flag = meta.advice_column();
        let curr_padding_sum = meta.advice_column();
        let d_bits = [(); KECCAK_REGION_WIDTH].map(|_| meta.advice_column());
        let d_lens = [(); KECCAK_REGION_WIDTH / 8].map(|_| meta.advice_column());
        let d_rlcs = [(); KECCAK_REGION_WIDTH / 8].map(|_| meta.advice_column());
        let s_flags = [(); KECCAK_REGION_WIDTH / 8].map(|_| meta.advice_column());
        let randomness = meta.advice_column();

        meta.create_gate("prev should be 0 for the 1st row", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            // len & rlc are passed down by previous circuit, they are not necessarily 0.
            let is_first = meta.query_fixed(is_first_row, Rotation::cur());

            cb.condition(is_first.clone(), |cb| {
                cb.require_zero(
                    "prev_s_flag == 0",
                    meta.query_advice(curr_s_flag, Rotation::prev()),
                );
            });
            cb.condition(is_first.clone(), |cb| {
                cb.require_zero(
                    "prev_padding_sum == 0",
                    meta.query_advice(curr_padding_sum, Rotation::prev()),
                );
            });

            cb.gate(meta.query_selector(q_enable))
        });

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

            let is_first = meta.query_fixed(is_first_row, Rotation::cur());
            cb.require_boolean("boolean first flag", is_first);

            let is_last = meta.query_fixed(is_last_row, Rotation::cur());
            cb.require_boolean("boolean first flag", is_last);

            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("start/end padding bit check", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let s_0 = meta.query_advice(s_flags[0], Rotation::cur());
            let s_prev = meta.query_advice(curr_s_flag, Rotation::prev());
            let d_bit_0 = meta.query_advice(d_bits[0], Rotation::cur());
            let s_padding_start = s_0 - s_prev;
            cb.condition(s_padding_start, |cb| {
                cb.require_equal(
                    "start with 1 if the padding start from pos 0",
                    d_bit_0,
                    1u64.expr(),
                );
            });

            for i in 1..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                let s_i_sub1 = meta.query_advice(s_flags[i - 1], Rotation::cur());
                let d_bit_0 = meta.query_advice(d_bits[8 * i], Rotation::cur());
                let s_padding_start = s_i - s_i_sub1;
                cb.condition(s_padding_start, |cb| {
                    cb.require_equal("start with 1 inside row", d_bit_0, 1u64.expr());
                });
            }

            let is_last = meta.query_fixed(is_last_row, Rotation::cur());
            let s_last = meta.query_advice(s_flags[s_flags.len() - 1], Rotation::cur());
            let d_last = meta.query_advice(d_bits[d_bits.len() - 1], Rotation::cur());

            let s_padding_end = s_last * is_last;
            cb.condition(s_padding_end, |cb| {
                cb.require_equal("end with 1", d_last, 1u64.expr())
            });

            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("sum padding", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let prev_padding_sum = meta.query_advice(curr_padding_sum, Rotation::prev());
            let curr_padding_sum = meta.query_advice(curr_padding_sum, Rotation::cur());

            let mut sum_padding_bits = prev_padding_sum;
            for i in 0..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                sum_padding_bits = d_bits[i * 8..(i + 1) * 8]
                    .iter()
                    .map(|b| meta.query_advice(*b, Rotation::cur()))
                    .fold(sum_padding_bits, |sum, b| sum + s_i.clone() * b);
            }

            let last_row = meta.query_fixed(is_last_row, Rotation::cur());
            cb.require_equal(
                "sum(padding_bits) == curr_padding_sum",
                sum_padding_bits,
                curr_padding_sum.clone(),
            );
            cb.condition(last_row, |cb| {
                cb.require_equal(
                    "sum(padding_bits) == 2",
                    2u64.expr(),
                    curr_padding_sum.clone(),
                )
            });
            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("input len check", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let prev_len = meta.query_advice(curr_len, Rotation::prev());
            let len_0 = meta.query_advice(d_lens[0], Rotation::cur());
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

            let r = meta.query_advice(randomness, Rotation::cur());
            cb.require_equal(
                "using same randomness",
                meta.query_advice(randomness, Rotation::prev()),
                r.clone(),
            );

            let s_0 = meta.query_advice(s_flags[0], Rotation::cur());
            let rlc_0 = meta.query_advice(d_rlcs[0], Rotation::cur());
            let rlc_prev = meta.query_advice(curr_rlc, Rotation::prev());
            let input_byte_0 = d_bits[0..8]
                .iter()
                .map(|bit| meta.query_advice(*bit, Rotation::cur()))
                .fold(0u64.expr(), |v, b| v * 2u64.expr() + b);
            cb.require_equal(
                "rlc[0] = prev_rlc*r + byte[0] if s == 0 else rlc_prev",
                rlc_0,
                select::expr(
                    s_0,
                    rlc_prev.clone(),
                    rlc_prev.clone() * r.clone() + input_byte_0,
                ),
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

        meta.create_gate("input ending check", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let s_last = meta.query_advice(s_flags[s_flags.len() - 1], Rotation::cur());
            let q_end = meta.query_advice(q_end, Rotation::cur());

            let last_row = meta.query_fixed(is_last_row, Rotation::cur());
            cb.condition(last_row, |cb| {
                cb.require_equal("s_last == q_end", s_last, q_end);
            });
            cb.gate(meta.query_selector(q_enable))
        });

        KeccakPaddingConfig {
            q_enable,
            q_end,
            is_first_row,
            is_last_row,
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

    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        _size: usize,
        keccak_padding_block: &KeccakPaddingBlock<F>,
        randomness: F,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assign keccak rounds",
            |mut region| {
                self.set_region(&mut region, 0, keccak_padding_block, randomness)?;
                Ok(())
            },
        )
    }

    fn set_region(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        data_block: &KeccakPaddingBlock<F>,
        randomness: F,
    ) -> Result<(), Error> {
        let enabled_region_offset = offset + 1;
        self.q_enable.enable(region, enabled_region_offset)?;

        // setup 0 row, the prev of the enabled region
        region.assign_advice(
            || format!("assign curr_len{}", offset),
            self.curr_len,
            offset,
            || Ok(F::from(data_block.acc_len as u64)),
        )?;

        region.assign_advice(
            || format!("assign curr_rlc{}", offset),
            self.curr_rlc,
            offset,
            || Ok(data_block.acc_rlc),
        )?;

        region.assign_advice(
            || format!("assign curr_s_flag{}", offset),
            self.curr_s_flag,
            offset,
            || Ok(F::zero()),
        )?;
        region.assign_advice(
            || format!("assign curr_padding_sum{}", offset),
            self.curr_padding_sum,
            offset,
            || Ok(F::zero()),
        )?;
        region.assign_advice(
            || format!("assign randomness{}", offset),
            self.randomness,
            offset,
            || Ok(F::from(randomness)),
        )?;

        //then the row setup loop
        for i in 0..KECCAK_REGION_HEIGHT as usize {
            // Input bits w/ padding
            let row_data = &data_block.block_rows[i];
            let d_bits = row_data.d_bits;
            let d_lens = row_data.d_lens;
            let d_rlcs = row_data.d_rlcs;
            let s_flags = row_data.s_flags;

            for (idx, (bit, column)) in d_bits.iter().zip(self.d_bits.iter()).enumerate() {
                region.assign_advice(
                    || format!("assign input data bit {} {}", idx, offset),
                    *column,
                    enabled_region_offset + i,
                    || Ok(F::from(*bit as u64)),
                )?;
            }

            for (idx, (s_flag, column)) in s_flags.iter().zip(self.s_flags.iter()).enumerate() {
                region.assign_advice(
                    || format!("assign input data select flag {} {}", idx, offset),
                    *column,
                    enabled_region_offset + i,
                    || Ok(F::from(*s_flag as u64)),
                )?;
            }

            for (idx, (d_len, column)) in d_lens.iter().zip(self.d_lens.iter()).enumerate() {
                region.assign_advice(
                    || format!("assign input data len {} {}", idx, offset),
                    *column,
                    enabled_region_offset + i,
                    || Ok(F::from(*d_len as u64)),
                )?;
            }

            for (idx, (d_rlc, column)) in d_rlcs.iter().zip(self.d_rlcs.iter()).enumerate() {
                region.assign_advice(
                    || format!("assign input data rlc {} {}", idx, offset),
                    *column,
                    enabled_region_offset + i,
                    || Ok(*d_rlc),
                )?;
            }

            region.assign_fixed(
                || format!("assign fixed first flag {}", offset),
                self.is_first_row,
                enabled_region_offset + i,
                || Ok(F::from((i == 0) as u64)),
            )?;

            region.assign_fixed(
                || format!("assign fixed first flag {}", offset),
                self.is_last_row,
                enabled_region_offset + i,
                || Ok(F::from((i + 1 == KECCAK_REGION_HEIGHT as usize) as u64)),
            )?;

            // output the curr len,rlc,s_flag & padding
            region.assign_advice(
                || format!("assign curr_len{}", offset),
                self.curr_len,
                enabled_region_offset + i,
                || Ok(F::from(row_data.curr_len as u64)),
            )?;

            region.assign_advice(
                || format!("assign curr_rlc{}", offset),
                self.curr_rlc,
                enabled_region_offset + i,
                || Ok(row_data.curr_rlc),
            )?;

            region.assign_advice(
                || format!("assign curr_s_flag{}", offset),
                self.curr_s_flag,
                enabled_region_offset + i,
                || Ok(F::from(row_data.curr_s_flag)),
            )?;
            region.assign_advice(
                || format!("assign curr_padding_sum{}", offset),
                self.curr_padding_sum,
                enabled_region_offset + i,
                || Ok(F::from(row_data.curr_padding_sum as u64)),
            )?;

            region.assign_advice(
                || format!("assign randomness{}", offset),
                self.randomness,
                enabled_region_offset + i,
                || Ok(F::from(randomness)),
            )?;

            region.assign_advice(
                || format!("assign q_end{}", offset),
                self.q_end,
                enabled_region_offset + i,
                || Ok(F::from(data_block.q_end)),
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use crate::keccak_circuit::keccak_padding::tests::generate_padding;
    use crate::keccak_circuit::keccak_padding::KeccakPaddingRow;

    use super::*;
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr};

    fn verify<F: Field>(k: u32, input: KeccakPaddingBlock<F>, success: bool) {
        let circuit = KeccakPaddingCircuit::<F> {
            inputs: vec![input],
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

    fn from_full_padding_block<F: Field>(
        keccak_padding_full_row: &KeccakPaddingRow<F>,
    ) -> KeccakPaddingBlock<F> {
        let mut rows = Vec::<KeccakPaddingBlockRow<F>>::new();
        let mut curr_len = keccak_padding_full_row.acc_len;
        let mut curr_rlc = keccak_padding_full_row.acc_rlc;
        let mut curr_padding_sum = 0;
        let mut curr_s_flag: bool;

        for i in 0..KECCAK_REGION_HEIGHT as usize {
            let prev_padding_sum = curr_padding_sum;

            curr_len =
                keccak_padding_full_row.d_lens[(i + 1) * KECCAK_REGION_WIDTH_IN_BYTES as usize - 1];
            println!("{:?}", curr_len);

            curr_rlc =
                keccak_padding_full_row.d_rlcs[(i + 1) * KECCAK_REGION_WIDTH_IN_BYTES as usize - 1];
            println!("{:?}", curr_rlc);

            curr_s_flag = keccak_padding_full_row.s_flags
                [(i + 1) * KECCAK_REGION_WIDTH_IN_BYTES as usize - 1];
            curr_padding_sum = keccak_padding_full_row.d_bits[i * 64..(i + 1) * 64]
                .iter()
                .enumerate()
                .fold(prev_padding_sum, |sum, (idx, v)| {
                    // println!(
                    //     "{} + {} * {}",
                    //     sum,
                    //     *v,
                    //     keccak_padding.s_flags[i * 8 + idx / 8]
                    // );
                    sum + (*v as u32) * (keccak_padding_full_row.s_flags[i * 8 + idx / 8] as u32)
                });
            println!("{}", curr_padding_sum);
            // assert!(curr_padding_sum <= 2);

            let sub_row = KeccakPaddingBlockRow::<F> {
                curr_len: curr_len,
                curr_rlc: curr_rlc,
                curr_s_flag: curr_s_flag,
                curr_padding_sum: curr_padding_sum,
                d_bits: keccak_padding_full_row.d_bits[i * 64..(i + 1) * 64]
                    .try_into()
                    .unwrap(),
                d_lens: keccak_padding_full_row.d_lens[i * 8..(i + 1) * 8]
                    .try_into()
                    .unwrap(),
                d_rlcs: keccak_padding_full_row.d_rlcs[i * 8..(i + 1) * 8]
                    .try_into()
                    .unwrap(),
                s_flags: keccak_padding_full_row.s_flags[i * 8..(i + 1) * 8]
                    .try_into()
                    .unwrap(),
            };
            rows.push(sub_row);
        }

        KeccakPaddingBlock::<F> {
            q_end: 1u64,
            acc_len: keccak_padding_full_row.acc_len,
            acc_rlc: keccak_padding_full_row.acc_rlc,
            block_rows: rows.try_into().unwrap(),
        }
    }

    static K: u32 = 8;

    #[test]
    fn bit_keccak_len_0() {
        let full_data = generate_padding::<Fr>(0);
        let input = from_full_padding_block(&full_data);
        verify::<Fr>(K, input, true);
    }

    #[test]
    fn bit_keccak_len_1() {
        let full_data = generate_padding::<Fr>(1);
        let input = from_full_padding_block(&full_data);
        verify::<Fr>(K, input, true);
    }

    #[test]
    fn bit_keccak_len_2() {
        let full_data = generate_padding::<Fr>(2);
        let input = from_full_padding_block(&full_data);
        verify::<Fr>(K, input, true);
    }

    #[test]
    fn bit_keccak_len_135() {
        let full_data = generate_padding::<Fr>(135);
        let input = from_full_padding_block(&full_data);

        verify::<Fr>(K, input, true);
    }

    #[test]
    fn bit_keccak_len_300() {
        let full_data = generate_padding::<Fr>(300);
        let input = from_full_padding_block(&full_data);

        verify::<Fr>(K, input, true);
    }

    #[test]
    fn bit_keccak_invalid_padding_begin() {
        // first bit is 0
        let mut full_data = generate_padding::<Fr>(11);
        full_data.d_bits[11 * 8] = 0u8;
        let input = from_full_padding_block(&full_data);
        verify::<Fr>(K, input, false);
    }

    #[test]
    fn bit_keccak_invalid_padding_end() {
        // last bit is 0
        let mut full_data = generate_padding::<Fr>(73);
        full_data.d_bits[KECCAK_RATE - 1] = 0u8;
        let input = from_full_padding_block(&full_data);
        verify::<Fr>(K, input, false);
    }

    #[test]
    fn bit_keccak_invalid_padding_mid() {
        // some 1 in padding
        let mut full_data = generate_padding::<Fr>(123);
        full_data.d_bits[KECCAK_RATE - 2] = 1u8;
        let input = from_full_padding_block(&full_data);
        verify::<Fr>(K, input, false);
    }

    #[test]
    fn bit_keccak_invalid_input_len() {
        // wrong len
        let mut full_data = generate_padding::<Fr>(123);
        full_data.d_lens[124] = 124;
        let input = from_full_padding_block(&full_data);
        verify::<Fr>(K, input, false);
    }
}
