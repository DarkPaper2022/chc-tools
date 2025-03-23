use std::{env, process::exit};

use argparse::{ArgumentParser, Store};
use chclia2chcbv::{convert_chclia_2_chcbv, convert_datalogchc_2_chc};
use walkdir::WalkDir;

#[derive(Debug, PartialEq)]
enum Usage {
    Lia2bv,
    DatalogCHC2CHC,
}

impl std::fmt::Display for Usage {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            Usage::Lia2bv => write!(f, "l2b"),
            Usage::DatalogCHC2CHC => write!(f, "d2c"),
        }
    }
}

fn main() {
    /*
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <file>", args[0]);
        return;
    }
    let path = &args[1];
    */
    let mut path = String::new();
    let mut usage_str = String::new();
    let usage: Usage;
    let usage_help = format!("Usage: {} or {}",  Usage::Lia2bv, Usage::DatalogCHC2CHC);

    {
        let mut ap = ArgumentParser::new();
        ap.set_description("Convert CHCLIA to CHCBV");
        ap.refer(&mut path)
            .add_argument("path", Store, "Path to file")
            .required();
        ap.refer(&mut usage_str)
            .add_argument("usage", Store, &usage_help)
            .required();
        ap.parse_args_or_exit();
    }

    match usage_str.as_str() {
        "l2b" => usage = Usage::Lia2bv,
        "d2c" => usage = Usage::DatalogCHC2CHC,
        _ => {
            eprintln!("Invalid usage: {}", usage_str);
            eprintln!("{}", usage_help);
            exit(1)
        }
    }


    for entry in WalkDir::new(path) {
        if let Ok(entry) = entry {
            if entry.path().is_dir() {
                continue;
            }
            if usage == Usage::Lia2bv {
                match convert_chclia_2_chcbv(entry.path().to_str().unwrap()) {
                    Ok(bv_expr) => {
                        // println!("success: {}", entry.path().to_str().unwrap());
                        println!("{}", bv_expr);
                    }
                    Err(err) => {
                        eprintln!("Failed to convert: {:?}", entry.path());
                        eprintln!("{}", err);
                        exit(1)
                    }
                }
            } else if usage == Usage::DatalogCHC2CHC {
                match convert_datalogchc_2_chc(entry.path().to_str().unwrap()) {
                    Ok(bv_expr) => {
                        // println!("success: {}", entry.path().to_str().unwrap());
                        println!("{}", bv_expr);
                    }
                    Err(err) => {
                        eprintln!("Failed to convert: {:?}", entry.path());
                        eprintln!("{}", err);
                        exit(1)
                    }
                }
            }
        }
    }
}
