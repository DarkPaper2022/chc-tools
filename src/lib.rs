use nom::bytes::complete::tag;
use nom::bytes::complete::{is_not, take_while1};
use nom::character::complete::{multispace0, multispace1};
use nom::combinator::map;
use nom::multi::separated_list0;
use nom::sequence::{pair, preceded};
use nom::{
    branch::alt,
    character::complete::{char, digit1},
    combinator::{map_res, recognize},
    sequence::delimited,
    IResult,
};
use std::fs;
use std::process::exit;
use std::{env, vec};
use walkdir::WalkDir;

static BIT_WIDTH: usize = 64;
static SIGNED: bool = true;

#[derive(Debug, Clone)]
pub enum RawExpr {
    Atom(Atom),
    List(Vec<RawExpr>),
}

impl RawExpr {
    fn to_string(&self) -> String {
        match self {
            RawExpr::Atom(atom) => atom.to_string(),
            RawExpr::List(v) => format!(
                "({})",
                v.iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
        }
    }
}

#[derive(Debug, Clone)]
enum Atom {
    Int(i64),
    Float(f64),
    Symbol(String),
}

impl Atom {
    fn to_string(&self) -> String {
        match self {
            Atom::Int(i) => i.to_string(),
            Atom::Float(f) => f.to_string(),
            Atom::Symbol(s) => s.to_string(),
        }
    }
}

/// 解析表达式：可以是原子类型或列表类型
fn parse_expr(input: &str) -> IResult<&str, RawExpr> {
    alt((parse_list, parse_atom))(input)
}

/// 解析一个表达式列表 (用括号括起来)
fn parse_list(input: &str) -> IResult<&str, RawExpr> {
    map(
        delimited(
            char('('),
            preceded(multispace0, separated_list0(multispace1, parse_expr)),
            preceded(multispace0, char(')')),
        ),
        RawExpr::List,
    )(input)
}

/// 解析整数
fn parse_int(input: &str) -> IResult<&str, Atom> {
    map_res(digit1, |s: &str| s.parse::<i64>().map(Atom::Int))(input)
}

/// 解析浮点数
fn parse_float(input: &str) -> IResult<&str, Atom> {
    map_res(
        recognize(pair(digit1, pair(char('.'), digit1))),
        |s: &str| s.parse::<f64>().map(Atom::Float),
    )(input)
}

/// 解析符号 (支持字母、下划线和部分特殊字符)
fn parse_symbol(input: &str) -> IResult<&str, Atom> {
    // debug info
    alt((parse_symbol_piped, parse_symbol_token))(input)
}

fn parse_symbol_piped(input: &str) -> IResult<&str, Atom> {
    // 使用 `delimited` 来匹配以 '|' 开头和结尾的内容
    map(
        delimited(tag("|"), is_not("|"), tag("|")), // 匹配 '|' 包围的内容
        |s: &str| {
            let symbol = format!("|{}|", s.to_string());
            Atom::Symbol(symbol)
        }, // 将内容转换为 `Atom::Symbol`
    )(input)
}

/// 解析符号 (支持字母、下划线和部分特殊字符)
fn parse_symbol_token(input: &str) -> IResult<&str, Atom> {
    // debug info
    map(
        take_while1(|c: char| {
            c.is_alphabetic() || c.is_digit(10) || "+-*/=!@#$%^&?><._".contains(c)
        }),
        |s: &str| Atom::Symbol(s.to_string()),
    )(input)
}

/// 解析 `Atom`
fn parse_atom(input: &str) -> IResult<&str, RawExpr> {
    alt((
        map(parse_int, RawExpr::Atom),
        map(parse_float, RawExpr::Atom),
        map(parse_symbol, RawExpr::Atom),
    ))(input)
}

fn wrapped_content(content: &str) -> String {
    format!("({})", content)
}

pub fn parse_wrapped_content(content: &str) -> Result<RawExpr, String> {
    let wrapped_content = wrapped_content(content);
    match parse_expr(&wrapped_content) {
        Ok(("", expr)) => Ok(expr),
        Ok((rem, _)) => {
            // eprintln!("解析失败: 未能解析完整: {:?}", rem);
            Err("未能解析完整".to_string())
        }
        Err(err) => {
            // eprintln!("解析失败: {:?}", err);
            Err(format!("解析失败: \n{}", err).to_string())
        }
    }
}

pub fn parse_by_filename(filename: &str) -> Result<RawExpr, String> {
    let content =
        fs::read_to_string(filename).expect(format!("Failed to read file: {}", filename).as_str());
    parse_wrapped_content(&content)
}

fn find_big_int_expr(expr: &RawExpr) -> Option<&RawExpr> {
    match expr {
        RawExpr::List(v) => {
            for e in v {
                if let Some(sub_expr) = find_big_int_expr(e) {
                    return Some(sub_expr);
                }
            }
            None
        }
        RawExpr::Atom(Atom::Symbol(s)) => {
            if s.chars().all(|c| c.is_digit(10)) {
                return Some(expr);
            }
            None
        }
        _ => None,
    }
}

fn find_negetive_expr(expr: &RawExpr) -> Option<&RawExpr> {
    match expr {
        RawExpr::List(v) => {
            if v.len() == 2 {
                if let RawExpr::Atom(Atom::Symbol(op)) = &v[0] {
                    if op == "-" {
                        return Some(expr);
                    }
                }
            }
            for e in v {
                if let Some(sub_expr) = find_negetive_expr(e) {
                    return Some(sub_expr);
                }
            }
            None
        }
        _ => None,
    }
}

fn find_strange_negetive_expr(expr: &RawExpr) -> Option<&RawExpr> {
    match expr {
        RawExpr::List(v) => {
            if v.len() == 2 {
                if let RawExpr::Atom(Atom::Symbol(op)) = &v[0] {
                    if op == "-" {
                        match &v[1] {
                            RawExpr::Atom(Atom::Int(i)) => {}
                            _ => {
                                return Some(expr);
                            }
                        }
                    }
                }
            }
            for e in v {
                if let Some(sub_expr) = find_strange_negetive_expr(e) {
                    return Some(sub_expr);
                }
            }
            None
        }
        _ => None,
    }
}

fn find_float_expr(expr: &RawExpr) -> Option<&RawExpr> {
    match expr {
        RawExpr::List(v) => {
            for e in v {
                if let Some(sub_expr) = find_float_expr(e) {
                    return Some(sub_expr);
                }
            }
            None
        }
        RawExpr::Atom(Atom::Float(_)) => Some(expr),
        _ => None,
    }
}

fn find_mod_expr(expr: &RawExpr) -> Option<&RawExpr> {
    match expr {
        RawExpr::List(v) => {
            for e in v {
                if let Some(sub_expr) = find_mod_expr(e) {
                    return Some(sub_expr);
                }
            }
            None
        }
        RawExpr::Atom(Atom::Symbol(s)) => {
            if s == "%" || s == "mod" {
                return Some(expr);
            }
            None
        }
        _ => None,
    }
}

// @T
fn replace_operand_lia_to_bv(op: &str) -> &str {
    // not so good
    if SIGNED && BIT_WIDTH == 64 {
        return match op {
            "+" => "bvadd",
            "-" => "bvsub",
            "*" => "bvmul",
            "%" | "mod" => "bvsmod",
            "rem" => "bvsrem",
            "div" => "bvsdiv",
            ">=" => "bvsge",
            "<=" => "bvsle",
            ">" => "bvsgt",
            "<" => "bvslt",
            "Int" => "(_ BitVec 64)",
            "AUFLIA" => "AUFBV",
            "UFLIA" => "UFBV",
            _ => op,
        };
    } else if !SIGNED && BIT_WIDTH == 64 {
        return match op {
            "+" => "bvadd",
            "-" => "bvsub",
            "*" => "bvmul",
            "%" | "mod" => {
                panic!("bvumod not supported")
            }
            "div" => "bvudiv",
            "rem" => "bvurem",
            ">=" => "bvuge",
            "<=" => "bvule",
            ">" => "bvugt",
            "<" => "bvult",
            "Int" => "(_ BitVec 64)",
            "AUFLIA" => "AUFBV",
            "UFLIA" => "UFBV",
            _ => op,
        };
    } else {
        panic!("not supported")
    }
}

// @T
fn replace_operand_datalog_to_chc(op: &str) -> &str {
    return match op {
        "rule" => "assert",
        _ => op,
    };
}

fn bad_expr_filter(expr: &RawExpr) -> Result<&RawExpr, String> {
    match find_big_int_expr(expr) {
        Some(big_int_expr) => {
            return Err(format!("big int founded: {:?}", big_int_expr));
        }
        None => {}
    }
    match find_float_expr(expr) {
        Some(float_expr) => {
            return Err(format!("float founded: {:?}", float_expr));
        }
        None => {}
    }
    if SIGNED == false {
        match find_mod_expr(expr) {
            Some(mod_expr) => {
                return Err(format!("mod founded in unsigned logic: {:?}", mod_expr));
            }
            None => {}
        }
    }
    return Ok(expr);
}

// @T
fn to_bv_sexpr(expr: &RawExpr) -> Result<RawExpr, String> {
    bad_expr_filter(expr).map(to_bv_sexpr_rec)
}

fn to_bv_sexpr_rec(expr: &RawExpr) -> RawExpr {
    match expr {
        RawExpr::Atom(Atom::Symbol(s)) => {
            RawExpr::Atom(Atom::Symbol(replace_operand_lia_to_bv(s).to_string()))
        }
        RawExpr::List(v) => {
            if v.len() == 2 {
                if let RawExpr::Atom(Atom::Symbol(op)) = &v[0] {
                    if op == "-" {
                        return RawExpr::List(vec![
                            RawExpr::Atom(Atom::Symbol("bvneg".to_string())),
                            to_bv_sexpr_rec(&v[1]),
                        ]);
                    }
                }
            }
            RawExpr::List(v.iter().map(to_bv_sexpr_rec).collect())
        }
        RawExpr::Atom(Atom::Int(i)) => RawExpr::List(vec![
            RawExpr::Atom(Atom::Symbol("_".to_string())),
            RawExpr::Atom(Atom::Symbol(format!("bv{}", i))),
            RawExpr::Atom(Atom::Int(BIT_WIDTH as i64)), // warning: run for only one time
        ]),
        _ => {
            panic!("unexpected expr: {:?}", expr)
        }
    }
}

pub fn convert_chclia_2_chcbv(filename: &str) -> Result<String, String> {
    let expr = parse_by_filename(filename).map_err(|e| e)?;
    let bv_expr = to_bv_sexpr(&expr).map_err(|e| e)?;

    match bv_expr {
        RawExpr::List(v) => {
            let new_v: Vec<String> = v.into_iter().map(|e| e.to_string()).collect();
            Ok(new_v.join("\n"))
        }
        _ => Err("strange bv expr.".to_string()),
    }
}


