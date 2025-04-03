use nom::bytes::complete::tag;
use nom::bytes::complete::{is_not, take_while1};
use nom::character::complete::{multispace0, multispace1};
use nom::combinator::map;
use nom::multi::separated_list0;
use nom::sequence::{pair, preceded};
use nom::FindSubstring;
use nom::{
    branch::alt,
    character::complete::{char, digit1},
    combinator::{map_res, recognize},
    sequence::delimited,
    IResult,
};
use once_cell::sync::Lazy;
use std::fs;
use std::vec;

static BIT_WIDTH: usize = 64;
static SIGNED: bool = true;
#[derive(Debug, Clone)]
pub enum Logic {
    QF_UFLIA,
    UFLIA,
    QF_AUFLIA,
    AUFLIA,
    QF_UFBV,
    UFBV,
    QF_AUFBV,
    AUFBV,
    ALL,
}

impl Logic {
    fn to_head(&self) -> RawExpr {
        match self {
            Logic::QF_UFLIA => SET_LOGIC_QFUFLIA.clone(),
            Logic::UFLIA => SET_LOGIC_UFLIA.clone(),
            Logic::QF_AUFLIA => SET_LOGIC_QFAUFLIA.clone(),
            Logic::AUFLIA => SET_LOGIC_AUFLIA.clone(),
            Logic::QF_UFBV => SET_LOGIC_QFUFBV.clone(),
            Logic::UFBV => SET_LOGIC_UFBV.clone(),
            Logic::QF_AUFBV => SET_LOGIC_QFAUFBV.clone(),
            Logic::AUFBV => SET_LOGIC_AUFBV.clone(),
            Logic::ALL => SET_LOGIC_ALL.clone(),
        }
    }
}

pub fn fix_directory(logic: &Logic, unclassified_path: &str) -> Option<String> {
    let cnt = unclassified_path.matches("unclassified").count();
    if cnt != 1 {
        return None;
    }
    let dir_name = match logic {
        Logic::QF_UFLIA => "qf_uflia",
        Logic::UFLIA => "uflia",
        Logic::QF_AUFLIA => "qf_auflia",
        Logic::AUFLIA => "auflia",
        Logic::QF_UFBV => "qf_ufbv",
        Logic::UFBV => "ufbv",
        Logic::QF_AUFBV => "qf_aufbv",
        Logic::AUFBV => "aufbv",
        Logic::ALL => "all",
    };
    let classified_path = unclassified_path.replace("unclassified", dir_name);
    return Some(classified_path);
}

pub fn fix_chc_to_pricise_logic(
    logic: &Logic,
    unclassified_expr: RawExpr,
) -> Result<RawExpr, String> {
    let RawExpr::List(mut v) = unclassified_expr else {
        return Err(format!("not a normal chc: {:?}", unclassified_expr));
    };

    if let Some(RawExpr::List(maybe_setlogic)) = v.first() {
        if maybe_setlogic.len() == 2 {
            if let RawExpr::Atom(Atom::Symbol(s)) = &maybe_setlogic[0] {
                if s == "set-logic" {
                    v[0] = logic.to_head();
                    return Ok(RawExpr::List(v));
                }
            }
        }
    }

    Err(format!("set logic not found"))
}

#[test]
fn fix_directory_test() {
    let logic = Logic::QF_UFLIA;
    let unclassified_path = "/home/someone/Documents/some_project/smt/unclassified/seahorn_trans/2024.SV-Comp/loops/for_infinite_loop_2.smt2";
    let classified_path = fix_directory(&logic, unclassified_path);
    assert_eq!(classified_path, Some("/home/someone/Documents/some_project/smt/qf_uflia/seahorn_trans/2024.SV-Comp/loops/for_infinite_loop_2.smt2".to_string()));
}

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

    pub fn to_file_content(&self) -> Result<String, String> {
        match self {
            RawExpr::List(v) => {
                let new_v: Vec<String> = v.into_iter().map(|e| e.to_string()).collect();
                Ok(new_v.join("\n"))
            }
            _ => Err("strange chc expr.".to_string()),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Atom {
    Int(i64),
    Float(f64),
    Symbol(String), // TODO: use 'static &str for some cases
    String(String),
}

impl Atom {
    fn to_string(&self) -> String {
        match self {
            Atom::Int(i) => i.to_string(),
            Atom::Float(f) => f.to_string(),
            Atom::Symbol(s) => s.to_string(),
            Atom::String(s) => s.to_string(),
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

fn parse_string(input: &str) -> IResult<&str, Atom> {
    // 使用 `delimited` 来匹配以 '|' 开头和结尾的内容
    map(
        delimited(tag("\""), is_not("\""), tag("\"")), // 匹配 '|' 包围的内容
        |s: &str| {
            let string = format!("\"{}\"", s.to_string());
            Atom::String(string)
        }, // 将内容转换为 `Atom::Symbol`
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
            c.is_alphabetic() || c.is_digit(10) || "+-*/=!@#$%^&?><._:".contains(c)
        }),
        |s: &str| Atom::Symbol(s.to_string()),
    )(input)
}

/// 解析 `Atom`
fn parse_atom(input: &str) -> IResult<&str, RawExpr> {
    alt((
        map(parse_int, RawExpr::Atom),
        map(parse_float, RawExpr::Atom),
        map(parse_string, RawExpr::Atom),
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
            Err(format!("未能解析完整: \n{}", rem).to_string())
        }
        Err(err) => {
            // eprintln!("解析失败: {:?}", err);
            Err(format!("解析失败: \n{}", err).to_string())
        }
    }
}

pub fn parse_by_filename(filename: &str) -> Result<RawExpr, String> {
    let content = fs::read_to_string(filename).map_err(|err| format!("读取文件失败:\n{}", err))?;
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

fn _find_strange_negetive_expr(expr: &RawExpr) -> Option<&RawExpr> {
    match expr {
        RawExpr::List(v) => {
            if v.len() == 2 {
                if let RawExpr::Atom(Atom::Symbol(op)) = &v[0] {
                    if op == "-" {
                        match &v[1] {
                            RawExpr::Atom(Atom::Int(_)) => {}
                            _ => {
                                return Some(expr);
                            }
                        }
                    }
                }
            }
            for e in v {
                if let Some(sub_expr) = _find_strange_negetive_expr(e) {
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

fn find_unsupported_expr(expr: &RawExpr) -> Option<&RawExpr> {
    match expr {
        RawExpr::List(v) => {
            for e in v {
                if let Some(sub_expr) = find_unsupported_expr(e) {
                    return Some(sub_expr);
                }
            }
            None
        }
        RawExpr::Atom(Atom::Symbol(s)) => {
            if s == "mod" || s == "div" || s == "rem" || s == "*" {
                return Some(expr);
            }
            None
        }
        _ => None,
    }
}

fn find_array_expr(expr: &RawExpr) -> Option<&RawExpr> {
    match expr {
        RawExpr::List(v) => {
            for e in v {
                if let Some(sub_expr) = find_array_expr(e) {
                    return Some(sub_expr);
                }
            }
            None
        }
        RawExpr::Atom(Atom::Symbol(s)) => {
            if s == "Array" {
                return Some(expr);
            }
            None
        }
        _ => None,
    }
}

fn find_quantifier_expr(expr: &RawExpr) -> Option<&RawExpr> {
    match expr {
        RawExpr::List(v) => {
            for e in v {
                if let Some(sub_expr) = find_quantifier_expr(e) {
                    return Some(sub_expr);
                }
            }
            None
        }
        RawExpr::Atom(Atom::Symbol(s)) => {
            if s == "forall" || s == "exists" {
                return Some(expr);
            }
            None
        }
        _ => None,
    }
}

fn find_bitvec_expr(expr: &RawExpr) -> Option<&RawExpr> {
    match expr {
        RawExpr::List(v) => {
            for e in v {
                if let Some(sub_expr) = find_bitvec_expr(e) {
                    return Some(sub_expr);
                }
            }
            None
        }
        RawExpr::Atom(Atom::Symbol(s)) => {
            if s == "BitVec" {
                return Some(expr);
            }
            None
        }
        _ => None,
    }
}

pub fn check_logic(expr: &RawExpr) -> Logic {
    let has_quantifier = find_quantifier_expr(expr).is_some();
    let has_array = find_array_expr(expr).is_some();
    let has_unsupported = find_unsupported_expr(expr).is_some();
    let has_bv = find_bitvec_expr(expr).is_some();
    if has_unsupported {
        return Logic::ALL;
    }
    if has_quantifier && has_array && !has_bv {
        return Logic::AUFLIA;
    } else if has_quantifier && !has_array && !has_bv {
        return Logic::UFLIA;
    } else if !has_quantifier && has_array && !has_bv {
        return Logic::QF_AUFLIA;
    } else if !has_quantifier && !has_array && !has_bv {
        return Logic::QF_UFLIA;
    } else if has_quantifier && has_array && has_bv {
        return Logic::AUFBV;
    } else if !has_quantifier && has_array && has_bv {
        return Logic::QF_AUFBV;
    } else if has_quantifier && !has_array && has_bv {
        return Logic::UFBV;
    } else if !has_quantifier && !has_array && has_bv {
        return Logic::QF_UFBV;
    }
    panic!("should unreachable")
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
        "declare-rel" => "declare-fun",
        "declare-var" => "declare-const",
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
pub fn to_bv_sexpr(expr: &RawExpr) -> Result<RawExpr, String> {
    let filtered = bad_expr_filter(&expr)?;
    let bv = to_bv_sexpr_rec(filtered);
    let tagged = add_const_head(bv, LIA2BV_TAG.clone());
    return tagged;
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
        RawExpr::Atom(Atom::Float(f)) => {
            panic!("float not supported: {:?}", f);
        }
        RawExpr::Atom(Atom::String(s)) => RawExpr::Atom(Atom::String(s.to_string())),
    }
}

pub fn datalog_to_chc_sexpr(expr: &RawExpr) -> Result<RawExpr, String> {
    let chc = datalog_to_chc_sexpr_rec(expr);
    let tailed = datalog_to_chc_sexpr_tail(chc)?;
    let tagged = add_const_head(tailed, DATALOG2CHC_TAG.clone())?;
    let logic_specified = add_const_head(tagged, SET_LOGIC_HORN.clone());
    return logic_specified;
}

fn datalog_to_chc_sexpr_tail(expr: RawExpr) -> Result<RawExpr, String> {
    // if the last is "query ..."
    if let RawExpr::List(mut v) = expr {
        if v.len() > 0 {
            if let Some(RawExpr::List(v_query)) = v.pop() {
                if v_query.len() == 2 {
                    if let RawExpr::Atom(Atom::Symbol(op)) = &v_query[0] {
                        if op == "query" {
                            v.push(RawExpr::List(vec![
                                RawExpr::Atom(Atom::Symbol("assert".to_string())),
                                v_query[1].clone(),
                            ]));
                            v.push(RawExpr::List(vec![RawExpr::Atom(Atom::Symbol(
                                "check-sat".to_string(),
                            ))]));
                            return Ok(RawExpr::List(v));
                        }
                    }
                }
            }
        }
    }
    Err("not a normal chc".to_string())
}

fn datalog_to_chc_sexpr_rec(expr: &RawExpr) -> RawExpr {
    match expr {
        RawExpr::Atom(Atom::Symbol(s)) => {
            RawExpr::Atom(Atom::Symbol(replace_operand_datalog_to_chc(s).to_string()))
        }
        RawExpr::List(v) => {
            // if first is a symbol declare-rel
            if v.len() == 3 {
                if let RawExpr::Atom(Atom::Symbol(op)) = &v[0] {
                    if op == "declare-rel" {
                        return RawExpr::List(vec![
                            RawExpr::Atom(Atom::Symbol(
                                replace_operand_datalog_to_chc(op).to_string(),
                            )),
                            v[1].clone(),
                            v[2].clone(),
                            RawExpr::Atom(Atom::Symbol("Bool".to_string())),
                        ]);
                    }
                }
            }
            RawExpr::List(v.iter().map(datalog_to_chc_sexpr_rec).collect())
        }
        _ => expr.clone(),
    }
}

fn add_const_head(expr: RawExpr, head: RawExpr) -> Result<RawExpr, String> {
    let RawExpr::List(mut v) = expr else {
        return Err(format!("not a normal chc: {:?}", expr));
    };

    if let Some(RawExpr::List(maybe_setlogic)) = v.first() {
        if maybe_setlogic.len() == 2 {
            if let RawExpr::Atom(Atom::Symbol(s)) = &maybe_setlogic[0] {
                if s == "set-logic" {
                    v.insert(1, head);
                    return Ok(RawExpr::List(v));
                }
            }
        }
    }

    v.insert(0, head);
    Ok(RawExpr::List(v))
}

pub fn convert_chclia_2_chcbv_with_io(path_str: &str) -> Result<(), String> {
    let expr = parse_by_filename(path_str)?;
    let chc_expr = to_bv_sexpr(&expr)?;
    let file_content = chc_expr.to_file_content()?;
    println!("{}", file_content);
    Ok(())
}

pub fn convert_datalogchc_2_chc_with_io(path_str: &str) -> Result<(), String> {
    let expr = parse_by_filename(path_str)?;
    let chc_expr = datalog_to_chc_sexpr(&expr)?;
    let file_content = chc_expr.to_file_content()?;
    println!("{}", file_content);
    Ok(())
}

pub fn classify_file_with_io(path_str: &str) -> Result<(), String> {
    let expr = parse_by_filename(path_str)?;
    let logic = check_logic(&expr);
    // fix expr
    let classified_expr = fix_chc_to_pricise_logic(&logic, expr)?;
    let file_content = classified_expr.to_file_content()?;
    // write
    let dst_file: String = fix_directory(&logic, path_str).ok_or("Failed to fix directory")?;
    fs::create_dir_all(dst_file.clone()).map_err(|e| e.to_string())?;
    fs::write(dst_file.clone(), file_content).map_err(|e| e.to_string())?;
    println!("Classified file written to: {}", dst_file);
    Ok(())
}

const LIA2BV_TAG: Lazy<RawExpr> = Lazy::new(|| {
    RawExpr::List(vec![
        RawExpr::Atom(Atom::Symbol("set-info".to_string())),
        RawExpr::Atom(Atom::Symbol(":notes".to_string())),
        RawExpr::Atom(Atom::Symbol("|lia2bv|".to_string())),
    ])
});
const DATALOG2CHC_TAG: Lazy<RawExpr> = Lazy::new(|| {
    RawExpr::List(vec![
        RawExpr::Atom(Atom::Symbol("set-info".to_string())),
        RawExpr::Atom(Atom::Symbol(":notes".to_string())),
        RawExpr::Atom(Atom::Symbol("|datalog2chc|".to_string())),
    ])
});

const SET_LOGIC_QFUFLIA: Lazy<RawExpr> = Lazy::new(|| {
    RawExpr::List(vec![
        RawExpr::Atom(Atom::Symbol("set-logic".to_string())),
        RawExpr::Atom(Atom::Symbol("QF_UFLIA".to_string())),
    ])
});
const SET_LOGIC_UFLIA: Lazy<RawExpr> = Lazy::new(|| {
    RawExpr::List(vec![
        RawExpr::Atom(Atom::Symbol("set-logic".to_string())),
        RawExpr::Atom(Atom::Symbol("UFLIA".to_string())),
    ])
});
const SET_LOGIC_AUFLIA: Lazy<RawExpr> = Lazy::new(|| {
    RawExpr::List(vec![
        RawExpr::Atom(Atom::Symbol("set-logic".to_string())),
        RawExpr::Atom(Atom::Symbol("AUFLIA".to_string())),
    ])
});
const SET_LOGIC_ALL: Lazy<RawExpr> = Lazy::new(|| {
    RawExpr::List(vec![
        RawExpr::Atom(Atom::Symbol("set-logic".to_string())),
        RawExpr::Atom(Atom::Symbol("ALL".to_string())),
    ])
});
const SET_LOGIC_QFAUFLIA: Lazy<RawExpr> = Lazy::new(|| {
    RawExpr::List(vec![
        RawExpr::Atom(Atom::Symbol("set-logic".to_string())),
        RawExpr::Atom(Atom::Symbol("QF_AUFLIA".to_string())),
    ])
});
const SET_LOGIC_QFUFBV: Lazy<RawExpr> = Lazy::new(|| {
    RawExpr::List(vec![
        RawExpr::Atom(Atom::Symbol("set-logic".to_string())),
        RawExpr::Atom(Atom::Symbol("QF_UFBV".to_string())),
    ])
});
const SET_LOGIC_UFBV: Lazy<RawExpr> = Lazy::new(|| {
    RawExpr::List(vec![
        RawExpr::Atom(Atom::Symbol("set-logic".to_string())),
        RawExpr::Atom(Atom::Symbol("UFBV".to_string())),
    ])
});
const SET_LOGIC_AUFBV: Lazy<RawExpr> = Lazy::new(|| {
    RawExpr::List(vec![
        RawExpr::Atom(Atom::Symbol("set-logic".to_string())),
        RawExpr::Atom(Atom::Symbol("AUFBV".to_string())),
    ])
});
const SET_LOGIC_QFAUFBV: Lazy<RawExpr> = Lazy::new(|| {
    RawExpr::List(vec![
        RawExpr::Atom(Atom::Symbol("set-logic".to_string())),
        RawExpr::Atom(Atom::Symbol("QF_AUFBV".to_string())),
    ])
});
const SET_LOGIC_HORN: Lazy<RawExpr> = Lazy::new(|| {
    RawExpr::List(vec![
        RawExpr::Atom(Atom::Symbol("set-logic".to_string())),
        RawExpr::Atom(Atom::Symbol("HORN".to_string())),
    ])
});
