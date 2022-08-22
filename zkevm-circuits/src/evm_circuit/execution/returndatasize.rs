use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_MEMORY_ADDRESS,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            from_bytes, CachedRegion, RandomLinearCombination,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::CallContextFieldTag,
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::{Field, ToLittleEndian};
use halo2_proofs::plonk::Error;

#[derive(Clone, Debug)]
pub(crate) struct ReturnDataSizeGadget<F> {
    same_context: SameContextGadget<F>,
    return_data_size: RandomLinearCombination<F, N_BYTES_MEMORY_ADDRESS>,
}

impl<F: Field> ExecutionGadget<F> for ReturnDataSizeGadget<F> {
    const NAME: &'static str = "RETURNDATASIZE";

    const EXECUTION_STATE: ExecutionState = ExecutionState::RETURNDATASIZE;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        // Add lookup constraint in the call context for the returndatasize field.
        let return_data_size = cb.query_rlc();
        cb.call_context_lookup(
            false.expr(),
            None,
            CallContextFieldTag::LastCalleeReturnDataLength,
            from_bytes::expr(&return_data_size.cells),
        );

        // The returndatasize should be pushed to the top of the stack.
        cb.stack_push(return_data_size.expr());

        let step_state_transition = StepStateTransition {
            rw_counter: Delta(2.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta((-1).expr()),
            gas_left: Delta(-OpcodeId::RETURNDATASIZE.constant_gas_cost().expr()),
            ..Default::default()
        };

        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            return_data_size,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _tx: &Transaction,
        _call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let return_data_size = block.rws[step.rw_indices[1]].stack_value();

        self.return_data_size.assign(
            region,
            offset,
            Some(
                return_data_size.to_le_bytes()[..N_BYTES_MEMORY_ADDRESS]
                    .try_into()
                    .unwrap(),
            ),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::{
        test::{rand_bytes, run_test_circuit},
        witness::block_convert,
    };
    use eth_types::{address, bytecode, Word};
    use itertools::Itertools;
    use mock::TestContext;

    fn test_ok(return_data_size: usize, is_root: bool) {
        let bytecode = bytecode! {
            RETURNDATASIZE
            STOP
        };

        let block_data = if is_root {
            bus_mapping::mock::BlockData::new_from_geth_data(
                TestContext::<2, 1>::new(
                    None,
                    |accs| {
                        accs[0]
                            .address(address!("0x0000000000000000000000000000000000000000"))
                            .balance(Word::from(1u64 << 30));
                        accs[1]
                            .address(address!("0x0000000000000000000000000000000000000010"))
                            .balance(Word::from(1u64 << 20))
                            .code(bytecode);
                    },
                    |mut txs, accs| {
                        txs[0]
                            .from(accs[0].address)
                            .to(accs[1].address)
                            .input(rand_bytes(32).into())
                            .gas(Word::from(40000));
                    },
                    |block, _tx| block.number(0xcafeu64),
                )
                .unwrap()
                .into(),
            )
        } else {
            bus_mapping::mock::BlockData::new_from_geth_data(
                TestContext::<3, 1>::new(
                    None,
                    |accs| {
                        accs[0]
                            .address(address!("0x0000000000000000000000000000000000000000"))
                            .balance(Word::from(1u64 << 30));
                        accs[1]
                            .address(address!("0x0000000000000000000000000000000000000010"))
                            .balance(Word::from(1u64 << 20))
                            .code(bytecode! {
                                PUSH1(0)
                                PUSH1(0)
                                PUSH32(return_data_size)
                                PUSH1(0)
                                PUSH1(0)
                                PUSH1(0x20)
                                GAS
                                CALL
                                STOP
                            });
                        accs[2]
                            .address(address!("0x0000000000000000000000000000000000000020"))
                            .balance(Word::from(1u64 << 20))
                            .code(bytecode);
                    },
                    |mut txs, accs| {
                        txs[0]
                            .from(accs[0].address)
                            .to(accs[1].address)
                            .gas(Word::from(30000));
                    },
                    |block, _tx| block.number(0xcafeu64),
                )
                .unwrap()
                .into(),
            )
        };
        let mut builder = block_data.new_circuit_input_builder();
        builder
            .handle_block(&block_data.eth_block, &block_data.geth_traces)
            .unwrap();
        let block = block_convert(&builder.block, &builder.code_db);
        assert_eq!(run_test_circuit(block), Ok(()));
    }

    #[test]
    fn return_datasize_gadget_root() {
        for (return_data_size, is_root) in vec![32, 64, 96, 128, 256, 512, 1024]
            .into_iter()
            .cartesian_product([true, false])
        {
            test_ok(return_data_size, is_root);
        }
    }
}
