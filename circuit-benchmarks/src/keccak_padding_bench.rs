//! State circuit benchmarks

#[cfg(test)]
mod tests {
    use ark_std::{end_timer, start_timer};
    use halo2_proofs::plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, SingleVerifier,
    };
    use halo2_proofs::{
        pairing::bn256::{Bn256, Fr, G1Affine},
        poly::commitment::{Params, ParamsVerifier},
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use std::env::var;
    use std::fs::File;
    use std::io::BufReader;
    use zkevm_circuits::keccak_circuit::{
        keccak_padding::KeccakPaddingCircuit,
        keccak_padding_multi_gadgets::KeccakMultiGadgetPaddingCircuit,
        keccak_padding_multirows::KeccakMultiRowPaddingCircuit,
        keccak_padding_multirows_2::KeccakPaddingMultiRowsExCircuit,
    };

    #[cfg_attr(not(feature = "benches"), ignore)]
    fn bench_circuit(
        empty_circuit: impl Circuit<Fr>,
        param: Option<Params<G1Affine>>,
        degree: u32,
    ) {
        // Initialize the polynomial commitment parameters
        let rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        // Bench setup generation
        let setup_message = format!("Setup generation with degree = {}", degree);
        let start1 = start_timer!(|| setup_message);
        let general_params = match param {
            Some(param) => param,
            None => {
                println!("Regenerate params with degree {}", degree);
                let general_params: Params<G1Affine> =
                    Params::<G1Affine>::unsafe_setup::<Bn256>(degree);
                general_params
            }
        };
        let verifier_params: ParamsVerifier<Bn256> =
            general_params.verifier(degree as usize * 2).unwrap();

        end_timer!(start1);

        // Initialize the proving key
        let vk = keygen_vk(&general_params, &empty_circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&general_params, vk, &empty_circuit).expect("keygen_pk should not fail");
        // Create a proof
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

        // Bench proof generation time
        let proof_message = format!("Packed Keccak Multi Proof generation with {} rows", degree);
        let start2 = start_timer!(|| proof_message);
        create_proof(
            &general_params,
            &pk,
            &[empty_circuit],
            &[&[]],
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");
        let proof = transcript.finalize();
        end_timer!(start2);

        // Bench verification time
        let start3 = start_timer!(|| "Keccak Proof verification");
        let mut verifier_transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        let strategy = SingleVerifier::new(&verifier_params);

        verify_proof(
            &verifier_params,
            pk.get_vk(),
            strategy,
            &[&[]],
            &mut verifier_transcript,
        )
        .expect("failed to verify bench circuit");
        end_timer!(start3);
    }

    #[test]
    fn bench_naive_keccak_padding_circuit_prover() {
        let degree: u32 = var("DEGREE")
            .unwrap_or(String::from("12"))
            .parse()
            .expect("Cannot parse DEGREE env var as u32");

        let params: Option<Params<G1Affine>> = {
            let params_path: String = var("PARAMS_PATH")
                .unwrap_or(String::from(format!("./params-{}", degree)))
                .parse()
                .expect("Cannot parse PARAMS_PATH env var");
            File::open(&params_path)
                .and_then(|fs| Params::read::<_>(&mut BufReader::new(fs)))
                .ok()
        };

        println!("type1:");
        let empty_circuit = KeccakPaddingCircuit::<Fr>::default();
        bench_circuit(empty_circuit, params, degree);
    }

    #[test]
    fn bench_keccak_padding_multi_gadgets_circuit_prover() {
        let degree: u32 = var("DEGREE")
            .unwrap_or(String::from("12"))
            .parse()
            .expect("Cannot parse DEGREE env var as u32");

        let params: Option<Params<G1Affine>> = {
            let params_path: String = var("PARAMS_PATH")
                .unwrap_or(String::from(format!("./params-{}", degree)))
                .parse()
                .expect("Cannot parse PARAMS_PATH env var");
            File::open(&params_path)
                .and_then(|fs| Params::read::<_>(&mut BufReader::new(fs)))
                .ok()
        };

        println!("type2:");
        let empty_circuit = KeccakMultiGadgetPaddingCircuit::<Fr>::default();
        bench_circuit(empty_circuit, params, degree);
    }

    #[test]
    fn bench_keccak_padding_multi_row_circuit_prover() {
        let degree: u32 = var("DEGREE")
            .unwrap_or(String::from("12"))
            .parse()
            .expect("Cannot parse DEGREE env var as u32");

        let params: Option<Params<G1Affine>> = {
            let params_path: String = var("PARAMS_PATH")
                .unwrap_or(String::from(format!("./params-{}", degree)))
                .parse()
                .expect("Cannot parse PARAMS_PATH env var");
            File::open(&params_path)
                .and_then(|fs| Params::read::<_>(&mut BufReader::new(fs)))
                .ok()
        };

        println!("type3:");
        let empty_circuit = KeccakMultiRowPaddingCircuit::<Fr>::default();
        bench_circuit(empty_circuit, params, degree);
    }

    #[test]
    fn bench_keccak_padding_multi_row_2_circuit_prover() {
        let degree: u32 = var("DEGREE")
            .unwrap_or(String::from("12"))
            .parse()
            .expect("Cannot parse DEGREE env var as u32");

        let params: Option<Params<G1Affine>> = {
            let params_path: String = var("PARAMS_PATH")
                .unwrap_or(String::from(format!("./params-{}", degree)))
                .parse()
                .expect("Cannot parse PARAMS_PATH env var");
            File::open(&params_path)
                .and_then(|fs| Params::read::<_>(&mut BufReader::new(fs)))
                .ok()
        };

        println!("type4:");
        let empty_circuit = KeccakPaddingMultiRowsExCircuit::<Fr>::default();
        bench_circuit(empty_circuit, params, degree);
    }
}
