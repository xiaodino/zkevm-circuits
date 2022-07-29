use eth_types::Field;
use halo2_proofs::{
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, VirtualCells},
    poly::Rotation,
};

/// BaseAdviceColumnBuilder
#[derive(Clone, Debug)]
pub struct BaseAdviceColumnBuilderConfig {
    pub(crate) data_size: u32,
    pub(crate) start_point: (i32, i32),
    pub(crate) advices: Vec<Column<Advice>>,
}

impl BaseAdviceColumnBuilderConfig {
    fn new(advices: Vec<Column<Advice>>, data_size: u32, start_point: (i32, i32)) -> Self {
        BaseAdviceColumnBuilderConfig {
            data_size,
            start_point: start_point,
            advices: advices,
        }
    }

    fn query_advice_coordinates(&self, input_idx: u32) -> (Column<Advice>, Rotation) {
        let region_width = self.advices.len() as u32;
        let column_idx = (input_idx % region_width) as usize;
        let rotation_idx = (input_idx / region_width) as i32 - self.start_point.1;
        (self.advices[column_idx], Rotation(rotation_idx))
    }
}

/// BaseAdviceColumnBuilder
#[derive(Clone, Debug)]
pub struct BaseAdviceColumnBuilder {
    pub(crate) config: BaseAdviceColumnBuilderConfig,
}

impl BaseAdviceColumnBuilder {
    /// configuire()
    pub fn configure<F: Field>(
        meta: &mut ConstraintSystem<F>,
        data_size: u32,
        region_width: u32,
        start_point: (i32, i32),
    ) -> Self {
        //TODO: x offset not supported now.
        assert_eq!(start_point.0, 0);

        let advices = (0..region_width)
            .into_iter()
            .map(|_| meta.advice_column())
            .collect();

        BaseAdviceColumnBuilder {
            config: BaseAdviceColumnBuilderConfig::new(advices, data_size, start_point),
        }
    }

    /// query_advice
    pub fn query_advice<F: Field>(
        &self,
        meta: &mut VirtualCells<'_, F>,
        input_idx: u32,
    ) -> Expression<F> {
        let config = &self.config;
        let (col, rot) = config.query_advice_coordinates(input_idx);
        meta.query_advice(col, rot)
    }

    /// show (column, rotation) of the index-ed advice cell
    pub fn relative_advice_coordinate(&self, input_idx: u32) -> (Column<Advice>, Rotation) {
        let config = &self.config;
        config.query_advice_coordinates(input_idx)
    }

    /// assign the cell value to i-th cell
    pub fn assign_advice<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        input_idx: usize,
        offset: i32,
        value: F,
    ) -> Result<(), Error> {
        let (col, rot) = self.relative_advice_coordinate(input_idx as u32);

        region.assign_advice(
            || format!("assign input data select flag {} {}", input_idx, offset),
            col,
            (offset + rot.0) as usize,
            || Ok(value),
        )?;

        Ok(())
    }

    /// return size of the managed data
    pub fn size(&self) -> u32 {
        self.config.data_size
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::pairing::bn256::Fr;

    #[test]
    fn configure_works() {
        let cs = &mut ConstraintSystem::<Fr>::default();
        let advice_builder = BaseAdviceColumnBuilder::configure(cs, 100, 100, (0, 0));
        assert_eq!(advice_builder.config.data_size, 100);
        assert_eq!(advice_builder.config.advices.len(), 100);
    }

    #[test]
    fn query_works() {
        let cs = &mut ConstraintSystem::<Fr>::default();
        let advice_builder = BaseAdviceColumnBuilder::configure(cs, 500, 100, (0, 0));
        let (col, rot) = advice_builder.config.query_advice_coordinates(0);
        assert_eq!(col, advice_builder.config.advices[0]);
        assert_eq!(rot, Rotation(0));

        let (col, rot) = advice_builder.config.query_advice_coordinates(98);
        assert_eq!(col, advice_builder.config.advices[98]);
        assert_eq!(rot, Rotation(0));

        let (col, rot) = advice_builder.config.query_advice_coordinates(101);
        assert_eq!(col, advice_builder.config.advices[1]);
        assert_eq!(rot, Rotation(1));

        let (col, rot) = advice_builder.config.query_advice_coordinates(305);
        assert_eq!(col, advice_builder.config.advices[5]);
        assert_eq!(rot, Rotation(3));
    }

    #[test]
    fn query_works_non_zero_offset() {
        let cs = &mut ConstraintSystem::<Fr>::default();
        let advice_builder = BaseAdviceColumnBuilder::configure(cs, 500, 100, (0, 3));
        let (col, rot) = advice_builder.config.query_advice_coordinates(0);
        assert_eq!(col, advice_builder.config.advices[0]);
        assert_eq!(rot, Rotation(-3));

        let (col, rot) = advice_builder.config.query_advice_coordinates(101);
        assert_eq!(col, advice_builder.config.advices[1]);
        assert_eq!(rot, Rotation(-2));

        let (col, rot) = advice_builder.config.query_advice_coordinates(305);
        assert_eq!(col, advice_builder.config.advices[5]);
        assert_eq!(rot, Rotation(0));
    }

    #[test]
    #[should_panic]
    fn query_not_works_non_zero_x_offset() {
        let cs = &mut ConstraintSystem::<Fr>::default();
        BaseAdviceColumnBuilder::configure(cs, 500, 100, (1, 1));
    }
}
