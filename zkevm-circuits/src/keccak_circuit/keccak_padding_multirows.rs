use crate::keccak_circuit::keccak_utils::*;
use crate::{evm_circuit::util::constraint_builder::BaseConstraintBuilder, util::Expr};
use eth_types::Field;
use gadgets::util::{not, select};
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

const KECCAK_WIDTH: usize = 5 * 5 * 64;
const KECCAK_RATE: usize = 1088;
const KECCAK_RATE_IN_BYTES: usize = KECCAK_RATE / 8;

/// KeccakPaddingConfig
#[derive(Clone, Debug)]
pub struct KeccakMultiRowPaddingConfig<F> {
    q_enable: Selector,
    q_end: Column<Advice>,
    d_bits_builder: BaseAdviceColumnBuilder,
    d_lens_builder: BaseAdviceColumnBuilder,
    d_rlcs_builder: BaseAdviceColumnBuilder,
    s_flags_builder: BaseAdviceColumnBuilder,
    randomness: Column<Advice>,

    _marker: PhantomData<F>,
}

pub(crate) struct KeccakPaddingRow<F: Field> {
    pub(crate) q_end: u64,
    pub(crate) d_bits: [u8; KECCAK_WIDTH],
    pub(crate) d_lens: [u32; KECCAK_RATE_IN_BYTES],
    pub(crate) d_rlcs: [F; KECCAK_RATE_IN_BYTES],
    pub(crate) s_flags: [bool; KECCAK_RATE_IN_BYTES],
}

/// KeccakPaddingCircuit
#[derive(Default)]
pub struct KeccakMultiRowPaddingCircuit<F: Field> {
    inputs: Vec<KeccakPaddingRow<F>>,
    size: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> KeccakMultiRowPaddingCircuit<F> {
    fn r() -> F {
        F::from(123456)
    }
}

impl<F: Field> Circuit<F> for KeccakMultiRowPaddingCircuit<F> {
    type Config = KeccakMultiRowPaddingConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        KeccakMultiRowPaddingConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.assign(
            layouter,
            self.size,
            &self.inputs[0],
            KeccakMultiRowPaddingCircuit::r(),
        )?;
        Ok(())
    }
}

impl<F: Field> KeccakMultiRowPaddingConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.selector();
        let q_end = meta.advice_column();
        let data_column_builder =
            BaseAdviceColumnBuilder::configure(meta, KECCAK_RATE as u32, 64, (0, 0));
        let len_column_builder =
            BaseAdviceColumnBuilder::configure(meta, KECCAK_RATE_IN_BYTES as u32, 8, (0, 0));
        let rls_column_builder =
            BaseAdviceColumnBuilder::configure(meta, KECCAK_RATE_IN_BYTES as u32, 8, (0, 0));
        let s_flag_column_builder =
            BaseAdviceColumnBuilder::configure(meta, KECCAK_RATE_IN_BYTES as u32, 8, (0, 0));
        let randomness = meta.advice_column();

        meta.create_gate("boolean checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            //TODO: could be removed if combined with keccak circuit?
            for i in 0..data_column_builder.size() {
                let b = data_column_builder.query_advice(meta, i);
                cb.require_boolean("input data bit", b);
            }

            for i in 0..s_flag_column_builder.size() {
                let s = s_flag_column_builder.query_advice(meta, i);
                cb.require_boolean("boolean state bit", s);
            }

            for i in 1..s_flag_column_builder.size() {
                let s_i = s_flag_column_builder.query_advice(meta, i);
                let s_i_sub1 = s_flag_column_builder.query_advice(meta, i - 1);

                cb.require_boolean("boolean state switch", s_i - s_i_sub1);
            }

            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("padding bit checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            for i in 1..s_flag_column_builder.size() {
                let s_i = s_flag_column_builder.query_advice(meta, i);
                let s_i_sub1 = s_flag_column_builder.query_advice(meta, i - 1);
                let d_bit_0 = data_column_builder.query_advice(meta, 8 * i);
                let s_padding_start = s_i - s_i_sub1;
                cb.condition(s_padding_start, |cb| {
                    cb.require_equal("start with 1", d_bit_0, 1u64.expr());
                });
            }

            let s_last = s_flag_column_builder.query_advice(meta, s_flag_column_builder.size() - 1);
            let d_last = data_column_builder.query_advice(meta, KECCAK_RATE as u32 - 1);

            cb.condition(s_last, |cb| {
                cb.require_equal("end with 1", d_last, 1u64.expr())
            });
            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("intermedium 0 checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let mut sum_padding_bits = 0u64.expr();
            for i in 0..s_flag_column_builder.size() {
                let s_i = s_flag_column_builder.query_advice(meta, i);

                sum_padding_bits = (i * 8..(i + 1) * 8)
                    .map(|k| data_column_builder.query_advice(meta, k))
                    .fold(sum_padding_bits, |sum, b| sum + s_i.clone() * b);
            }

            cb.require_equal("sum(padding_bits) == 2", sum_padding_bits, 2u64.expr());
            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("input len check", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            for i in 1..s_flag_column_builder.size() {
                let s_i = s_flag_column_builder.query_advice(meta, i);
                let len_i = len_column_builder.query_advice(meta, i);
                let len_i_sub1 = len_column_builder.query_advice(meta, i - 1);

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

            for i in 1..s_flag_column_builder.size() {
                let s_i = s_flag_column_builder.query_advice(meta, i);
                let rlc_i = rls_column_builder.query_advice(meta, i);
                let rlc_i_sub1 = rls_column_builder.query_advice(meta, i - 1);

                let r = meta.query_advice(randomness, Rotation::cur());
                let input_byte_i = (i * 8..(i + 1) * 8)
                    .map(|k| data_column_builder.query_advice(meta, k))
                    .fold(0u64.expr(), |v, b| v * 2u64.expr() + b);
                cb.require_equal(
                    "rlc[i] = rlc[i-1]*r if s == 0 else rlc[i]",
                    rlc_i,
                    select::expr(
                        s_i,
                        rlc_i_sub1.clone(),
                        rlc_i_sub1.clone() * r + input_byte_i,
                    ),
                )
            }

            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("input ending check", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let s_last = s_flag_column_builder.query_advice(meta, s_flag_column_builder.size() - 1);
            let q_end = meta.query_advice(q_end, Rotation::cur());

            cb.require_equal("s_last == q_end", s_last, q_end);
            cb.gate(meta.query_selector(q_enable))
        });

        KeccakMultiRowPaddingConfig {
            q_enable,
            q_end,
            d_bits_builder: data_column_builder,
            d_lens_builder: len_column_builder,
            d_rlcs_builder: rls_column_builder,
            s_flags_builder: s_flag_column_builder,
            randomness,
            _marker: PhantomData,
        }
    }

    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        _size: usize,
        keccak_padding_row: &KeccakPaddingRow<F>,
        randomness: F,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assign keccak rounds",
            |mut region| {
                self.set_row(
                    &mut region,
                    0,
                    keccak_padding_row.q_end,
                    keccak_padding_row.d_bits,
                    keccak_padding_row.d_lens,
                    keccak_padding_row.d_rlcs,
                    keccak_padding_row.s_flags,
                    randomness,
                )?;
                Ok(())
            },
        )
    }

    fn set_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        q_end: u64,
        d_bits: [u8; KECCAK_WIDTH],
        d_lens: [u32; KECCAK_RATE_IN_BYTES],
        d_rlcs: [F; KECCAK_RATE_IN_BYTES],
        s_flags: [bool; KECCAK_RATE_IN_BYTES],
        randomness: F,
    ) -> Result<(), Error> {
        self.q_enable.enable(region, offset)?;

        // Input bits w/ padding
        for (idx, bit) in d_bits.iter().enumerate() {
            self.d_bits_builder
                .assign_advice(region, idx, offset as i32, F::from(*bit as u64))?;
        }

        for (idx, s_flag) in s_flags.iter().enumerate() {
            self.s_flags_builder.assign_advice(
                region,
                idx,
                offset as i32,
                F::from(*s_flag as u64),
            )?;
        }

        for (idx, d_len) in d_lens.iter().enumerate() {
            self.d_lens_builder.assign_advice(
                region,
                idx,
                offset as i32,
                F::from(*d_len as u64),
            )?;
        }

        for (idx, d_rlc) in d_rlcs.iter().enumerate() {
            self.d_rlcs_builder
                .assign_advice(region, idx, offset as i32, *d_rlc)?;
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

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use super::*;
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr};

    fn verify<F: Field>(k: u32, inputs: Vec<KeccakPaddingRow<F>>, success: bool) {
        let circuit = KeccakMultiRowPaddingCircuit::<F> {
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

    fn generate_padding<F: Field>(data_len: u32) -> KeccakPaddingRow<F> {
        let mut output = KeccakPaddingRow::<F> {
            d_bits: [0; KECCAK_WIDTH],
            d_lens: [0; KECCAK_RATE_IN_BYTES],
            d_rlcs: [F::from(0u64); KECCAK_RATE_IN_BYTES],
            s_flags: [false; KECCAK_RATE_IN_BYTES],
            q_end: 1u64,
        };

        let data_len_offset = data_len % KECCAK_RATE_IN_BYTES as u32;
        let data_len_base = (data_len / KECCAK_RATE_IN_BYTES as u32) * KECCAK_RATE_IN_BYTES as u32;

        output.s_flags[0] = data_len_offset == 0u32;
        output.d_lens[0] = data_len_base + !output.s_flags[0] as u32;

        for i in 1 as usize..KECCAK_RATE_IN_BYTES {
            output.s_flags[i] = {
                if (i as u32) < data_len_offset {
                    false
                } else {
                    true
                }
            };
            output.d_lens[i] = output.d_lens[i - 1] + !output.s_flags[i] as u32;
        }

        for i in data_len_offset as usize..KECCAK_RATE {
            output.d_bits[i] = 0u8;
        }
        output.d_bits[data_len_offset as usize * 8] = 1;
        output.d_bits[KECCAK_RATE - 1] = 1;

        println!("{:?}", output.s_flags);
        println!("{:?}", output.d_bits);
        println!("{:?}", output.d_lens);
        output
    }

    static K: u32 = 8;

    #[test]
    fn bit_keccak_len_0() {
        let input = generate_padding::<Fr>(0);
        verify::<Fr>(K, vec![input], true);
    }

    #[test]
    fn bit_keccak_len_1() {
        let input = generate_padding::<Fr>(1);
        verify::<Fr>(K, vec![input], true);
    }

    #[test]
    fn bit_keccak_len_2() {
        let input = generate_padding::<Fr>(2);
        verify::<Fr>(K, vec![input], true);
    }

    #[test]
    fn bit_keccak_len_135() {
        let input = generate_padding::<Fr>(135);
        verify::<Fr>(K, vec![input], true);
    }

    #[test]
    fn bit_keccak_len_300() {
        let input = generate_padding::<Fr>(300);
        verify::<Fr>(K, vec![input], true);
    }

    #[test]
    fn bit_keccak_invalid_padding_begin() {
        // first bit is 0
        let mut input = generate_padding::<Fr>(11);
        input.d_bits[11 * 8] = 0u8;
        verify::<Fr>(K, vec![input], false);
    }

    #[test]
    fn bit_keccak_invalid_padding_end() {
        // last bit is 0
        let mut input = generate_padding::<Fr>(73);
        input.d_bits[KECCAK_RATE - 1] = 0u8;
        verify::<Fr>(K, vec![input], false);
    }

    #[test]
    fn bit_keccak_invalid_padding_mid() {
        // some 1 in padding
        let mut input = generate_padding::<Fr>(123);
        input.d_bits[KECCAK_RATE - 2] = 1u8;
        verify::<Fr>(K, vec![input], false);
    }

    #[test]
    fn bit_keccak_invalid_input_len() {
        // wrong len
        let mut input = generate_padding::<Fr>(123);
        input.d_lens[124] = 124;
        verify::<Fr>(K, vec![input], false);
    }
}
