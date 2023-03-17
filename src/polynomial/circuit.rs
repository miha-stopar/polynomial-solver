use bus_mapping::{circuit_input_builder::CircuitsParams, mock::BlockData};
use eth_types::{bytecode, geth_types::GethData, ToWord, Word};
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr, plonk::Circuit};
use mock::test_ctx::TestContext;
use num::Rational32;
use num_traits::{One, ToPrimitive, Zero};
use num_bigint::{BigInt, BigUint, RandBigInt, Sign};
use polyexen::{
    analyze::{bound_base, find_bounds_poly, Analysis},
    expr::{ExprDisplay, Expr},
    plaf::{
        backends::halo2::PlafH2Circuit,
        frontends::halo2::{gen_witness, get_plaf},
        Cell, CellDisplay, Plaf, PlafDisplayBaseTOML, PlafDisplayFixedCSV, VarDisplay,
    },
};
use std::{fmt, collections::{HashMap, HashSet}};
use zkevm_circuits::{
    bytecode_circuit::circuit::BytecodeCircuit,
    copy_circuit::CopyCircuit,
    evm_circuit::EvmCircuit,
    exp_circuit::ExpCircuit,
    keccak_circuit::KeccakCircuit,
    pi_circuit::PiTestCircuit as PiCircuit,
    state_circuit::StateCircuit,
    super_circuit::SuperCircuit,
    tx_circuit::TxCircuit,
    util::SubCircuit,
    witness::{block_convert, Block},
};

use std::{
    fs::File,
    io::{self, Write},
};

use crate::polynomial::division::tests::r;

use super::division::tests::QPoly;

fn name_challanges(plaf: &mut Plaf) {
    plaf.set_challange_alias(0, "r_word".to_string());
    plaf.set_challange_alias(1, "r_keccak".to_string());
    plaf.set_challange_alias(2, "r_evm_lookup".to_string());
}

fn write_files(name: &str, plaf: &Plaf) -> Result<(), io::Error> {
    let mut base_file = File::create(format!("out/{}.toml", name))?;
    let mut fixed_file = File::create(format!("out/{}_fixed.csv", name))?;
    write!(base_file, "{}", PlafDisplayBaseTOML(plaf))?;
    write!(fixed_file, "{}", PlafDisplayFixedCSV(plaf))?;
    Ok(())
}

fn gen_small_block() -> Block<Fr> {
    let bytecode = bytecode! {
        PUSH32(0x1234)
        PUSH32(0x5678)
        ADD
        STOP
    };
    let block: GethData = TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode)
        .unwrap()
        .into();

    let mut builder = BlockData::new_from_geth_data_with_params(
        block.clone(),
        CircuitsParams {
            max_rws: 128,
            max_txs: 1,
            max_calldata: 64,
            max_copy_rows: 128,
            max_bytecode: 32,
            max_keccak_rows: 128,
            // max_evm_rows: 128,
            max_evm_rows: 8,
            max_exp_steps: 128,
        },
    )
    .new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();
    let block = block_convert(&builder.block, &builder.code_db).unwrap();
    block
}

fn gen_empty_block() -> Block<Fr> {
    let block: GethData = TestContext::<0, 0>::new(None, |_| {}, |_, _| {}, |b, _| b)
        .unwrap()
        .into();

    let mut builder = BlockData::new_from_geth_data_with_params(
        block.clone(),
        CircuitsParams {
            max_rws: 128,
            max_txs: 1,
            max_calldata: 64,
            max_copy_rows: 128,
            max_bytecode: 128,
            max_keccak_rows: 1024,
            max_evm_rows: 16,
            max_exp_steps: 128,
        },
    )
    .new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();
    let block = block_convert(&builder.block, &builder.code_db).unwrap();
    block
}

fn gen_circuit_plaf<C: Circuit<Fr> + SubCircuit<Fr>>(name: &str, k: u32, block: &Block<Fr>) {
    let circuit = C::new_from_block(&block);
    let mut plaf = get_plaf(k, &circuit).unwrap();
    name_challanges(&mut plaf);
    write_files(name, &plaf).unwrap();
}

fn circuit_plaf_mock_prover<C: Circuit<Fr> + SubCircuit<Fr>>(name: &str, k: u32) {
    let block = gen_small_block();

    let circuit = C::new_from_block(&block);
    let mut plaf = get_plaf(k, &circuit).unwrap();
    name_challanges(&mut plaf);
    write_files(name, &plaf).unwrap();
    let instance = circuit.instance();
    let challenges = vec![Fr::from(0x100), Fr::from(0x100), Fr::from(0x100)];
    let wit = gen_witness(k, &circuit, &plaf, challenges, instance.clone()).unwrap();

    let plaf_circuit = PlafH2Circuit { plaf, wit };

    let mock_prover = MockProver::<Fr>::run(k, &plaf_circuit, instance).unwrap();
    mock_prover.assert_satisfied_par();
}

fn demo_get_plaf() {
    let block = gen_empty_block();
    gen_circuit_plaf::<EvmCircuit<Fr>>("evm", 18, &block);
    gen_circuit_plaf::<StateCircuit<Fr>>("state", 17, &block);
    gen_circuit_plaf::<TxCircuit<Fr>>("tx", 19, &block);
    gen_circuit_plaf::<BytecodeCircuit<Fr>>("bytecode", 9, &block);
    gen_circuit_plaf::<CopyCircuit<Fr>>("copy", 9, &block);
    gen_circuit_plaf::<KeccakCircuit<Fr>>("keccak", 11, &block);
    gen_circuit_plaf::<ExpCircuit<Fr>>("exp", 10, &block);
    gen_circuit_plaf::<PiCircuit<Fr, 1, 64>>("pi", 17, &block);
    gen_circuit_plaf::<SuperCircuit<Fr, 1, 64, 0x100>>("super", 19, &block);
}

fn build_poly(expr: Expr<Cell>, vars: &mut HashMap<usize, &str>) -> QPoly
{
    use Expr::*;

    match expr {
        Pow(e, f) => {
            let e = build_poly(*e, vars);
            let mut poly = QPoly::one();
            for _ in 0..f {
                poly = poly * e.clone();
            }
            poly
        }
        Neg(e) => {
            let e = build_poly(*e, vars);
            let min = QPoly::new_constant(Rational32::from(-1));
            min * e
        }
        Const(f) => {
            QPoly::new_constant(Rational32::from(f.to_i32().unwrap()))
        },
        Var(v) => {
            let l = vars.len();
            println!("{}", v.to_string());
            vars.insert(l, "foo");
            println!("{}", l);
            QPoly::new_var(l.try_into().unwrap())
        },
        Sum(es) => {
            let mut poly = QPoly::zero();
            for x in es.into_iter().map(|x| build_poly(x, vars)) {
                poly = poly + x;
            }

            poly
        }
        Mul(es) => {
            let mut poly = QPoly::one();
            for x in es.into_iter().map(|x| build_poly(x, vars)) {
                poly = poly * x;
            }

            poly
        }
    }
}

fn demo_analysis() {
    let block = gen_empty_block();
    let circuit = BytecodeCircuit::<Fr>::new_from_block(&block);
    let k = 9;
    let mut plaf = get_plaf(k, &circuit).unwrap();
    name_challanges(&mut plaf);

    let p = BigUint::parse_bytes(b"100000000000000000000000000000000", 16).unwrap()
        - BigUint::from(159u64);
    let mut analysis = Analysis::new();
    let cell_fmt =
        |f: &mut fmt::Formatter<'_>, c: &Cell| write!(f, "{}", CellDisplay { c, plaf: &plaf });
    for offset in 0..plaf.info.num_rows {
        for poly in &plaf.polys {
            let exp = plaf.resolve(&poly.exp, offset);
            let exp = exp.simplify(&p);
            println!(
                "\"{}\" {}",
                poly.name,
                ExprDisplay {
                    e: &exp,
                    var_fmt: cell_fmt
                }
            );

            let mut vars = HashMap::new();
            let p = build_poly(exp, &mut vars);
            println!("{}", p);
            println!("======");

            // find_bounds_poly(&exp, &p, &mut analysis);
        }
    }
    let bound_base = bound_base(&p);
    for (cell, attrs) in &analysis.vars_attrs {
        if attrs.bound == bound_base {
            continue;
        }
        println!(
            "{}",
            CellDisplay {
                c: cell,
                plaf: &plaf
            }
        );
        println!("  {:?}", attrs.bound);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::{division::tests::*, grobner_basis::grobner_basis};

    #[test]
    fn circuit_test() {
        env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();
        demo_analysis();

        let [x, y, z]: [QPoly; 3] = QPoly::new_variables([2, 1, 0u8]).try_into().unwrap();
        let eqs = [
            x.clone() * x.clone() + y.clone() * y.clone() + z.clone() * z.clone() - r(1),
            x.clone() * x.clone() - y.clone() + z.clone() * z.clone(),
            x.clone() - z.clone(),
        ];

        let grobner_basis = grobner_basis(&mut eqs.into_iter());
        println!("Gröbner Basis:");
        for p in grobner_basis.iter() {
            println!("{}", p);
        }
    }
}

