use std::{fs, process::exit};

use argparse::{ArgumentParser, Store};
use chclia2chcbv::{
    classify_file_with_io, convert_chclia_2_chcbv_with_io, convert_datalogchc_2_chc_with_io
};
use walkdir::WalkDir;

#[derive(Debug, PartialEq)]
enum Usage {
    Lia2bv,
    DatalogCHC2CHC,
    Classify, // FILES smt/unknown -> smt/uflia or smt/auflia or smt/qf_uflia ...
}

impl std::fmt::Display for Usage {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            Usage::Lia2bv => write!(f, "l2b"),
            Usage::DatalogCHC2CHC => write!(f, "d2c"),
            Usage::Classify => write!(f, "classify"),
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
    let usage_help = format!("Usage: {} or {}", Usage::Lia2bv, Usage::DatalogCHC2CHC);

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

    let usage = match usage_str.as_str() {
        "l2b" => Usage::Lia2bv,
        "d2c" => Usage::DatalogCHC2CHC,
        "classify" => Usage::Classify,
        _ => {
            eprintln!("Invalid usage: {}", usage_str);
            eprintln!("{}", usage_help);
            panic!();
        }
    };

    for entry in WalkDir::new(path) {
        let entry = match entry {
            Ok(e) => e,
            Err(_) => return, // 读取目录失败，直接跳过
        };

        if entry.path().is_dir() {
            return; // 跳过目录
        }

        let path_str = match entry.path().to_str() {
            Some(s) => s,
            None => return, // 无法转换路径，跳过
        };

        let re = match usage {
            Usage::Lia2bv => convert_chclia_2_chcbv_with_io(path_str),
            Usage::DatalogCHC2CHC => convert_datalogchc_2_chc_with_io(path_str),
            Usage::Classify => classify_file_with_io(path_str),
        };
        if re.is_err() {
            eprintln!("Error processing file: {}", path_str);
            eprintln!("Error: {}", re.unwrap_err());
            panic!();
        }
    }
}
