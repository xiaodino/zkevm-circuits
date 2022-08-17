use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{Circuit, ConstraintSystem, Error},
};
use std::{env::var, marker::PhantomData};

use super::{
    keccak_bit::{keccak, KeccakBitConfig, KeccakRow, ABSORB_WIDTH_PER_ROW, C_WIDTH, KECCAK_WIDTH},
    keccak_padding_multirows_2::{KeccakPaddingBlock, KeccakPaddingConfig},
};

fn get_degree() -> usize {
    var("DEGREE")
        .unwrap_or_else(|_| "8".to_string())
        .parse()
        .expect("Cannot parse DEGREE env var as usize")
}

/// KeccakBitConfig
#[derive(Clone, Debug)]
pub struct KeccakCompleteBitConfig<F> {
    keccak_config: KeccakBitConfig<F>,
    padding_config: KeccakPaddingConfig<F>,
}

/// KeccakBitCircuit
pub struct KeccakCompleteBitCircuit<F: Field> {
    inputs: Vec<KeccakRow<F>>,
    size: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> KeccakCompleteBitCircuit<F> {
    fn r() -> F {
        F::from(123456)
    }
}

impl<F: Field> Default for KeccakCompleteBitCircuit<F> {
    fn default() -> Self {
        let mut rows: Vec<KeccakRow<F>> = vec![KeccakRow {
            s_bits: [0u8; KECCAK_WIDTH],
            c_bits: [0u8; C_WIDTH],
            a_bits: [0u8; ABSORB_WIDTH_PER_ROW],
            q_end: 1u64,
            hash_rlc: F::zero(),
            input_len: 0u64,
            input_rlc: F::zero(),
        }];

        // Actual keccaks
        keccak(
            &mut rows,
            (0u64..65536).map(|v| (v % 255) as u8).collect::<Vec<_>>(),
            KeccakCompleteBitCircuit::r(),
        );
        KeccakCompleteBitCircuit::<F> {
            inputs: rows,
            size: 2usize.pow(18),
            _marker: PhantomData,
        }
    }
}

impl<F: Field> Circuit<F> for KeccakCompleteBitCircuit<F> {
    type Config = KeccakCompleteBitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        KeccakCompleteBitConfig::configure(meta, KeccakCompleteBitCircuit::r())
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.load(&mut layouter)?;
        config.assign(
            layouter,
            self.size,
            &self.inputs,
            KeccakCompleteBitCircuit::r(),
        )?;
        Ok(())
    }
}

impl<F: Field> KeccakCompleteBitConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>, r: F) -> Self {
        let keccak_config = KeccakBitConfig::configure(meta, r);
        let padding_config =
            KeccakPaddingConfig::configure(meta, Some(keccak_config.a_bits), keccak_config.q_end);

        KeccakCompleteBitConfig {
            keccak_config: keccak_config,
            padding_config: padding_config,
        }
    }

    fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        _size: usize,
        witness: &[KeccakRow<F>],
        r: F,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assign keccak rounds with padding",
            |mut region| {
                assert!(witness.len() % 25 == 1);
                for (offset, keccak_row) in witness.iter().enumerate() {
                    self.keccak_config.set_row(
                        &mut region,
                        offset,
                        keccak_row.q_end,
                        keccak_row.hash_rlc,
                        keccak_row.s_bits,
                        keccak_row.c_bits,
                        keccak_row.a_bits,
                    )?;

                    if (offset + 1) % 25 == 1 && offset > 0 {
                        let keccak_padding_block: &KeccakPaddingBlock<F> =
                            &witness[offset - 25..offset + 1].try_into().unwrap();
                        // for row in &keccak_padding_block.block_rows {
                        //     println!("row: {:?}", row);
                        // }
                        self.padding_config.set_region(
                            &mut region,
                            offset - 25, // to align the data with padding
                            keccak_padding_block,
                            r,
                        )?;
                    }
                }

                Ok(())
            },
        )
    }

    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.keccak_config.load(layouter)
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use crate::keccak_circuit::keccak_bit::{keccak, ABSORB_WIDTH_PER_ROW, C_WIDTH, KECCAK_WIDTH};

    use super::*;
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr};

    fn verify<F: Field>(k: u32, inputs: Vec<KeccakRow<F>>, success: bool) {
        let circuit = KeccakCompleteBitCircuit::<F> {
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

    fn complete_keccak<F: Field>(bytes: Vec<u8>, r: F) -> Vec<KeccakRow<F>> {
        // Dummy first row so that the initial data is absorbed
        // The initial data doesn't really matter, `q_end` just needs to be enabled.
        let mut rows: Vec<KeccakRow<F>> = vec![KeccakRow {
            s_bits: [0u8; KECCAK_WIDTH],
            c_bits: [0u8; C_WIDTH],
            a_bits: [0u8; ABSORB_WIDTH_PER_ROW],
            q_end: 1u64,
            hash_rlc: F::zero(),
            input_len: 0u64,
            input_rlc: F::zero(),
        }];

        // Actual keccaks
        keccak(&mut rows, bytes, r);
        rows
    }

    #[test]
    fn complete_bit_keccak_nil() {
        let k = 8;
        let r = KeccakCompleteBitCircuit::r();
        let inputs = complete_keccak(vec![], r);
        verify::<Fr>(k, inputs, true);
    }

    #[test]
    fn complete_bit_keccak_0() {
        let k = 8;
        let r = KeccakCompleteBitCircuit::r();
        let inputs = complete_keccak(vec![0], r);
        verify::<Fr>(k, inputs, true);
    }

    #[test]
    fn complete_bit_keccak_135() {
        let k = 8;
        let r = KeccakCompleteBitCircuit::r();
        let inputs = complete_keccak((0..135).collect(), r);
        verify::<Fr>(k, inputs, true);
    }

    #[test]
    fn complete_bit_keccak_136() {
        let k = 8;
        let r = KeccakCompleteBitCircuit::r();
        let inputs = complete_keccak((0..136).collect(), r);
        verify::<Fr>(k, inputs, true);
    }

    #[test]
    fn complete_bit_keccak_211() {
        let k = 8;
        let r = KeccakCompleteBitCircuit::r();
        let inputs = complete_keccak((0..211).collect(), r);
        verify::<Fr>(k, inputs, true);
    }

    #[test]
    fn complete_bit_keccak_12345() {
        let k = 12;
        let r = KeccakCompleteBitCircuit::r();
        let inputs = complete_keccak((0..12345u64).map(|v| v as u8).collect(), r);
        verify::<Fr>(k, inputs, true);
    }
}
