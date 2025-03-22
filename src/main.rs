use std::{env, process::exit};

use chclia2chcbv::convert_chclia_2_chcbv;
use walkdir::WalkDir;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <file>", args[0]);
        return;
    }
    let path = &args[1];
    for entry in WalkDir::new(path) {
        if let Ok(entry) = entry {
            if entry.path().is_dir() {
                continue;
            }
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
        }
    }
}
