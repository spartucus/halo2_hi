use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
};
use halo2_proofs::{dev::MockProver, pasta::Fp};
use std::marker::PhantomData;
// use plotters::prelude::*;

// const * a^2 + b * c = d
// a * a + b * c = d

// advice, fixed(selector), instance column

#[derive(Clone, Debug)]
struct MyConfig {
    advice: [Column<Advice>; 2],
    instance: Column<Instance>,
    s_mul: Selector,
    s_add: Selector,
}

struct MyChip<F: FieldExt> {
    config: MyConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> MyChip<F> {
    fn new(config: MyConfig) -> Self {
        MyChip {
            config,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone)]
struct Number<F: FieldExt>(AssignedCell<F, F>);

impl<F: FieldExt> MyChip<F> {
    fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<F>,
    ) -> Result<Number<F>, Error> {
        layouter.assign_region(
            || "load private",
            |mut region| {
                region
                    .assign_advice(
                        || "private input",
                        self.config.advice[0],
                        0,
                        || value,
                    )
                    .map(Number)
            },
        )
    }

    fn load_constant(
        &self,
        mut layouter: impl Layouter<F>,
        constant: F,
    ) -> Result<Number<F>, Error> {
        layouter.assign_region(
            || "load constant",
            |mut region| {
                region
                    .assign_advice_from_constant(
                        || "constant value",
                        self.config.advice[0],
                        0,
                        constant,
                    )
                    .map(Number)
            },
        )
    }

    fn mul(
        &self,
        mut layouter: impl Layouter<F>,
        a: Number<F>,
        b: Number<F>,
    ) -> Result<Number<F>, Error> {
        layouter.assign_region(
            || "mul",
            |mut region| {
                self.config.s_mul.enable(&mut region, 0)?;

                // copy cell value to region's advice cell and constrains them to be equal.
                a.0.copy_advice(|| "lhs", &mut region, self.config.advice[0], 0)?;
                b.0.copy_advice(|| "rhs", &mut region, self.config.advice[1], 0)?;

                let value = a.0.value().and_then(|a| b.0.value().map(|b| *a * *b));
                region
                    .assign_advice(
                        || "lhs * rhs",
                        self.config.advice[0],
                        1,
                        || value,
                    )
                    .map(Number)
            },
        )
    }

    fn add(
        &self,
        mut layouter: impl Layouter<F>,
        a: Number<F>,
        b: Number<F>,
    ) -> Result<Number<F>, Error> {
        layouter.assign_region(
            || "add",
            |mut region| {
                self.config.s_add.enable(&mut region, 0)?;

                a.0.copy_advice(|| "lhs", &mut region, self.config.advice[0], 0)?;
                b.0.copy_advice(|| "rhs", &mut region, self.config.advice[1], 0)?;

                let value = a.0.value().and_then(|a| b.0.value().map(|b| *a + *b));
                region
                    .assign_advice(
                        || "lhs + rhs",
                        self.config.advice[0],
                        1,
                        || value,
                    )
                    .map(Number)
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: Number<F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(num.0.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit<F: FieldExt> {
    constant: F,
    a: Value<F>,
    b: Value<F>,
    c: Value<F>,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = MyConfig;

    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column()];
        let instance = meta.instance_column();
        let constant = meta.fixed_column();

        // Enable the ability to enforce equality over cells in each column
        meta.enable_equality(instance);
        meta.enable_constant(constant);
        for adc in &advice {
            meta.enable_equality(*adc);
        }

        let s_mul = meta.selector();
        let s_add = meta.selector();

        meta.create_gate("mul", |cell| {
            let lhs = cell.query_advice(advice[0], Rotation::cur());
            let rhs = cell.query_advice(advice[1], Rotation::cur());
            let out = cell.query_advice(advice[0], Rotation::next());
            let s_mul = cell.query_selector(s_mul);

            vec![(lhs * rhs - out) * s_mul]
        });

        meta.create_gate("add", |cell| {
            let lhs = cell.query_advice(advice[0], Rotation::cur());
            let rhs = cell.query_advice(advice[1], Rotation::cur());
            let out = cell.query_advice(advice[0], Rotation::next());
            let s_add = cell.query_selector(s_add);

            vec![(lhs + rhs - out) * s_add]
        });

        Self::Config {
            advice,
            instance,
            s_mul,
            s_add,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = MyChip::new(config);

        let a = chip.load_private(layouter.namespace(|| "load a"), self.a)?;
        let b = chip.load_private(layouter.namespace(|| "load b"), self.b)?;
        let c = chip.load_private(layouter.namespace(|| "load c"), self.c)?;

        let constant = chip.load_constant(layouter.namespace(|| "load constant"), self.constant)?;

        let aa = chip.mul(layouter.namespace(|| "a * a"), a.clone(), a)?;
        let bc = chip.mul(layouter.namespace(|| "b * c"), b, c)?;
        let aa_bc = chip.add(layouter.namespace(|| "a^2 + b*c"), aa, bc)?;
        let d = chip.mul(
            layouter.namespace(|| "constant * (a^2 + b * c)"),
            constant,
            aa_bc,
        )?;

        chip.expose_public(layouter.namespace(|| "expose d"), d, 0)
    }
}

fn main() {
    use std::time::Instant;

    let a = Fp::from(10);
    let b = Fp::from(5);
    let c = Fp::from(3);
    let constant = Fp::from(2);

    // (100 + 15) * 2 = 115 * 2 = 230
    let d = Fp::from(((u32::pow(10, 2) + 5 * 3) * 2) as u64);

    let circuit = MyCircuit {
        constant,
        a: Value::known(a),
        b: Value::known(b),
        c: Value::known(c),
    };

    let public_input = vec![d];

    let now = Instant::now();
    let prover = MockProver::run(5, &circuit, vec![public_input]).unwrap();
    let elapsed = now.elapsed();
    println!("Elapsed: {:.2?}", elapsed);
    assert_eq!(prover.verify(), Ok(()));
    // println!("{:?}", prover);

    // Create the area you want to draw on.
    // Use SVGBackend if you want to render to .svg instead.
    
    // let root = BitMapBackend::new("layout.png", (1024, 768)).into_drawing_area();
    // root.fill(&WHITE).unwrap();
    // let root = root
    //     .titled("Example Circuit Layout", ("sans-serif", 60))
    //     .unwrap();

    // halo2_proofs::dev::CircuitLayout::default()
    //     // You can optionally render only a section of the circuit.
    //     .view_width(0..2)
    //     .view_height(0..16)
    //     // You can hide labels, which can be useful with smaller areas.
    //     .show_labels(true)
    //     // Render the circuit onto your area!
    //     // The first argument is the size parameter for the circuit.
    //     .render(5, &circuit, &root)
    //     .unwrap();


    // // Generate the DOT graph string.
    // let dot_string = halo2_proofs::dev::circuit_dot_graph(&circuit);

    // // Now you can either handle it in Rust, or just
    // // print it out to use with command-line tools.
    // print!("{}", dot_string);
}
