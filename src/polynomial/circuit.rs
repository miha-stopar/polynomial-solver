use bus_mapping::{circuit_input_builder::CircuitsParams, mock::BlockData};
use eth_types::{bytecode, geth_types::GethData, ToWord, Word};
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr, plonk::Circuit};
use mock::test_ctx::TestContext;
use num::BigRational;
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
use std::{fmt, collections::{HashMap}};
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

use super::{division::tests::QPoly, Polynomial, monomial_ordering::Lex};

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
            max_evm_rows: 128,
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
            max_evm_rows: 128,
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

fn build_constraint(expr: Expr<Cell>, variables: &mut HashMap<String, QPoly>, plaf: &Plaf, poly_info: &mut PolyInfo, simplification: bool) -> Constraint
{
    use Expr::*;

    match expr {
        Pow(e, f) => {
            let c = build_constraint(*e, variables, plaf, poly_info, simplification);
            let mut poly = QPoly::one();
            for _ in 0..f {
                poly = poly * c.poly.clone();
            }
            Constraint::new_from_poly(poly)
        }
        Neg(e) => {
            let c = build_constraint(*e, variables, plaf, poly_info, simplification);
            let min = QPoly::new_constant(BigRational::from(BigInt::from(-1)));
            Constraint::new_from_poly(min * c.poly)
        }
        Const(f) => {
            if f == BigUint::from(1234u64) {
                // TODO(miha): note that in plaf.rs the challenge is for now resolved
                // to Const(BigUint::from(1234u64))
                let challenge_name = "challenge";
                if !variables.contains_key(challenge_name) {
                    let l = variables.len();
                    let poly = QPoly::new_var(l.try_into().unwrap());
                    variables.insert(challenge_name.to_owned(), poly.clone());
                    Constraint::new_from_poly(poly)
                } else {
                    let poly = variables.get(challenge_name).unwrap();
                    Constraint::new_from_poly(poly.clone())
                }
            } else {
                let poly = QPoly::new_constant(BigRational::from(BigInt::from(f)));
                Constraint::new_from_poly(poly)
            }
        },
        Var(v) => {
            let cell_fmt =
                |f: &mut fmt::Formatter<'_>, c: &Cell| write!(f, "{}", CellDisplay { c, plaf: &plaf });
            let f = format!(
                "{}",
                ExprDisplay {
                    e: &Var(v),
                    var_fmt: cell_fmt
                }
            );

            // println!("++++==++++");
            // println!("{}", f);

            let mut var_name: String = "".to_owned();
            if simplification {
                let s = f.split("[").collect::<Vec<_>>();
                let curr_row = s[1].split("]").collect::<Vec<_>>()[0].parse::<i32>().unwrap();

                var_name = s[0].to_owned();
                if poly_info.var_to_rows.contains_key(&var_name) {
                    let v = poly_info.var_to_rows.get(&var_name).unwrap();
                    if !v.contains(&curr_row) {
                        var_name = var_name.to_owned() + &v.len().to_string().to_owned();
                    }

                } else {
                    let mut v = vec![];
                    v.push(curr_row);
                    poly_info.var_to_rows.insert(var_name.to_owned(), v);
                }

                if poly_info.min_row == -1 {
                    poly_info.min_row = curr_row;
                } else {
                    if curr_row < poly_info.min_row {
                        poly_info.min_row = curr_row;
                    }
                }
            } else {
                var_name = f;
            }
            
            // println!("{}", var_name);
            // println!("{}", row);

            // TODO: for each rotation a new variable is to be introduced (only for simplification = true)

            if !variables.contains_key(&var_name) {
                let l = variables.len();
                let poly = QPoly::new_var(l.try_into().unwrap());
                variables.insert(var_name.to_owned(), poly.clone());
                Constraint::new_from_poly(poly)
            } else {
                let poly = variables.get(&var_name).unwrap();
                Constraint::new_from_poly(poly.clone())
            }
        },
        Sum(es) => {
            let mut poly = QPoly::zero();
            for x in es.into_iter().map(|x| build_constraint(x, variables, plaf, poly_info, simplification)) {
                poly = poly + x.poly;
            }

            Constraint::new_from_poly(poly)
        }
        Mul(es) => {
            let mut poly = QPoly::one();
            for x in es.into_iter().map(|x| build_constraint(x, variables, plaf, poly_info, simplification)) {
                poly = poly * x.poly;
            }

            Constraint::new_from_poly(poly)
        }
    }
}

#[derive(Clone)]
struct Constraint {
    name: String,
    poly: Polynomial<Lex, u8, BigRational, i16>,
}

impl Constraint {
    fn new_from_poly(poly: Polynomial<Lex, u8, BigRational, i16>) -> Self {
        Constraint{name: "".to_owned(), poly}
    }
}

impl std::fmt::Display for Constraint {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{} {}", self.name, self.poly)
    }
}

struct PolyInfo {
    min_row: i32,
    var_to_rows: HashMap<String, Vec<i32>>,
}

impl PolyInfo {
    fn new() -> Self {
        PolyInfo{min_row: -1, var_to_rows: HashMap::new()}
    }
}

impl std::fmt::Display for PolyInfo {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{}", self.min_row)
    }
}

fn get_circuit_polys() -> Vec<Constraint> {
    let block = gen_empty_block();
    let circuit = BytecodeCircuit::<Fr>::new_from_block(&block);
    let k = 9;

    // let circuit = StateCircuit::<Fr>::new_from_block(&block);
    // let k = 17;

    // let circuit = KeccakCircuit::<Fr>::new_from_block(&block);
    // let k = 11;

    let mut plaf = get_plaf(k, &circuit).unwrap();
    name_challanges(&mut plaf);

    let p = BigUint::parse_bytes(b"100000000000000000000000000000000", 16).unwrap()
        - BigUint::from(159u64);
    // let mut analysis = Analysis::new();
    let cell_fmt =
        |f: &mut fmt::Formatter<'_>, c: &Cell| write!(f, "{}", CellDisplay { c, plaf: &plaf });

    let mut constraints = vec![];

    let mut count = 0;
    let mut variables:HashMap<String, QPoly> = HashMap::new();
    let mut fixed_column_per_constraint = HashMap::new();

    // Either simplification or assignment
    let simplification = true;
    let mut name_to_constraint = HashMap::new();

    for offset in 0..plaf.info.num_rows {
        for poly in &plaf.polys {
            let exp = plaf.resolve(&poly.exp, offset);
            let exp = exp.simplify(&p);
            /*
            If you want fixed_columns to be included in the polynomials, you need to comment out
            the following instruction
                        ColumnKind::Fixed => Const(
                            self.fixed[column.index][offset]
                                .clone()
                                .unwrap_or_else(BigUint::zero),
                        ),
            in resolve function in polyexen/src/plaf.rs.
            */

            println!(
                "\"{}\" {}",
                poly.name,
                ExprDisplay {
                    e: &exp,
                    var_fmt: cell_fmt
                }
            );

            let mut poly_info = PolyInfo::new();
            
            let mut c = build_constraint(exp, &mut variables, &plaf, &mut poly_info, simplification);
            c.name = poly.name.clone();
            name_to_constraint.insert(poly.name.clone(), c.clone());

            if !fixed_column_per_constraint.contains_key(&poly.name) {
                let mut l = vec![];
                l.push(poly_info.min_row);
                fixed_column_per_constraint.insert(&poly.name, l);
            } else {
                let l = fixed_column_per_constraint.get_mut(&poly.name).unwrap();
                l.push(poly_info.min_row);
            }

            println!("{}", c.poly);
            // println!("poly_info: {}", poly_info);

            constraints.push(c);
            count += 1;

            if count == 5 {
                println!("=============");

                // println!("{:?}", fixed_column_per_constraint);

                let first_constraint = &constraints[0];
                let q_fixed = fixed_column_per_constraint[&first_constraint.name].clone();
                let mut q_fixed_columns = vec![];
                q_fixed_columns.push(q_fixed);
                let mut constraint_to_fixed_column = HashMap::<String, usize>::new();
                constraint_to_fixed_column.insert(first_constraint.name.clone(), 0);

                // Merge the same fixed columns together:
                for (name, list) in fixed_column_per_constraint.into_iter() {
                    let mut fixed_column_found = false;
                    for (ind, q_fixed) in q_fixed_columns.iter().enumerate() {
                        if list == *q_fixed {
                            let c = name_to_constraint.get(name).unwrap();
                            constraint_to_fixed_column.insert(c.name.clone(), ind);
                            fixed_column_found = true;
                            break;
                        }
                    }
                    if !fixed_column_found {
                        q_fixed_columns.push(list);
                        constraint_to_fixed_column.insert(name.clone(), q_fixed_columns.len() - 1);
                    }
                }

                // println!("Constraint to fixed column index:");
                // println!("{:?}", constraint_to_fixed_column);

                println!("variables count: {}", variables.len());
                
                return constraints
            }
        }
    }

    constraints
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::{grobner_basis::grobner_basis};

    #[test]
    fn circuit_test() {
        env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();
        let mut constraints = get_circuit_polys();
        // constraints = constraints[0..7].to_vec();

        println!("{}", constraints.len());

        let polys = constraints.into_iter().map(|x| x.poly);

        let grobner_basis = grobner_basis(&mut polys.into_iter());
        println!("Gröbner Basis:");
        for p in grobner_basis.iter() {
            println!("{}", p);
        }
    }
}

