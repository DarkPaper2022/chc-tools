use chclia2chcbv::{convert_chclia_2_chcbv, convert_datalogchc_2_chc, parse_wrapped_content};

#[cfg(test)]
mod tests {
    use std::process::Command;

    use chclia2chcbv::parse_by_filename;

    use super::*;

    #[test]
    fn test_fail_1() {
        let content = "func arg)";
        match parse_wrapped_content(&content) {
            Ok(expr) => {
                println!("解析成功: {:?}", expr);
                panic!("错误解析");
            }
            Err(_) => {}
        }
    }

    #[test]
    fn test_one_int() {
        let content = "123";
        match parse_wrapped_content(&content) {
            Ok(expr) => {
                println!("解析成功: {:?}", expr);
            }
            Err(err) => {
                println!("解析失败: {}", err);
                panic!("解析失败");
            }
        }
    }
    #[test]
    fn test_one_symbol_1() {
        let content = "abc";
        match parse_wrapped_content(&content) {
            Ok(expr) => {
                println!("解析成功: {:?}", expr);
            }
            Err(err) => {
                println!("解析失败: {}", err);
                panic!("解析失败");
            }
        }
    }

    #[test]
    fn test_two_symbols() {
        let content = "func arg";
        match parse_wrapped_content(&content) {
            Ok(expr) => {
                println!("解析成功: {:?}", expr);
            }
            Err(err) => {
                println!("解析失败: {}", err);
                panic!("解析失败");
            }
        }
    }

    #[test]
    fn empty_list() {
        let content = "()";
        match parse_wrapped_content(&content) {
            Ok(expr) => {
                println!("解析成功: {:?}", expr);
            }
            Err(err) => {
                println!("解析失败: {}", err);
                panic!("解析失败");
            }
        }
    }

    #[test]
    fn test_operator_induction() {
        let content = "(assert (=> main@entry.split false))";
        match parse_wrapped_content(&content) {
            Ok(expr) => {
                println!("解析成功: {:?}", expr);
            }
            Err(err) => {
                println!("解析失败: {}", err);
                panic!("解析失败");
            }
        }
    }

    #[test]
    fn test_one_symbol_2() {
        let content = "main@%sm2_0";
        match parse_wrapped_content(&content) {
            Ok(expr) => {
                println!("解析成功: {:?}", expr);
            }
            Err(err) => {
                println!("解析失败: {}", err);
                panic!("解析失败");
            }
        }
    }

    #[test]
    fn test_one_normal_file() {
        let content = "
(set-logic AUFLIA)
(declare-fun verifier.error (Bool Bool Bool) Bool)
(declare-fun main@entry ((Array Int Int)) Bool)
(declare-fun main@entry.split () Bool)
(assert (=> true (verifier.error false false false)))
(assert (=> true (verifier.error false true true)))
(assert (=> true (verifier.error true false true)))
(assert (=> true (verifier.error true true true)))
(assert (forall ((main@%sm2_0 (Array Int Int))) (=> true (main@entry main@%sm2_0))))
(assert (forall ((main@entry.split_0 Bool)
         (main@entry_0 Bool)
         (main@%_5_0 Bool)
         (main@%_3_0 Bool)
         (main@%_4_0 Bool)
         (main@%.0..0..0..i_0 Int)
         (main@%_0_0 Int)
         (main@%sm1_0 (Array Int Int))
         (main@%_1_0 Int)
         (@my_jump_buffer_0 Int)
         (main@%sm3_0 (Array Int Int))
         (main@%.0.sroa_cast1_0 Int)
         (main@%sm2_0 (Array Int Int))
         (main@%sm_0 (Array Int Int)))
  (let ((a!1 (and (main@entry main@%sm2_0)
                  (= main@%sm_0 main@%sm2_0)
                  (> main@%_0_0 0)
                  (= main@%.0.sroa_cast1_0 main@%_0_0)
                  (= main@%sm1_0 (store main@%sm3_0 main@%_0_0 0))
                  (= main@%_1_0 (+ @my_jump_buffer_0 (* 0 164) (* 0 164)))
                  (or (<= @my_jump_buffer_0 0) (> main@%_1_0 0))
                  (= main@%.0..0..0..i_0 (select main@%sm1_0 main@%_0_0))
                  (= main@%_3_0 (= main@%.0..0..0..i_0 0))
                  (not main@%_4_0)
                  main@%_3_0
                  (not main@%_5_0)
                  (=> main@entry.split_0 (and main@entry.split_0 main@entry_0))
                  main@entry.split_0)))
    (=> a!1 main@entry.split))))
(assert (=> main@entry.split false))
(check-sat)
        ";
        match parse_wrapped_content(&content) {
            Ok(expr) => {
                println!("解析成功: {:?}", expr);
            }
            Err(err) => {
                println!("解析失败: {}", err);
                panic!("解析失败");
            }
        }
    }

    #[test]
    fn test_one_normal_file_2() {
        let content = "
(set-logic AUFLIA)
(declare-fun |hanoi| ( Bool Bool Bool (Array Int Int) (Array Int Int) Int Int ) Bool)
(declare-fun |hanoi@_1| ( (Array Int Int) Int ) Bool)
(declare-fun |hanoi@UnifiedReturnBlock.split| ( (Array Int Int) (Array Int Int) Int Int ) Bool)
(declare-fun |applyHanoi@tailrecurse| ( (Array Int Int) (Array Int Int) Int Int Int ) Bool)
(declare-fun |applyHanoi@tailrecurse._crit_edge| ( (Array Int Int) (Array Int Int) Int Int ) Bool)
(declare-fun |main@entry.split| ( ) Bool)
(declare-fun |main@entry| ( (Array Int Int) ) Bool)
(declare-fun |applyHanoi@_1| ( (Array Int Int) Int Int ) Bool)
(declare-fun |applyHanoi| ( Bool Bool Bool (Array Int Int) (Array Int Int) Int Int ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (v_4 Bool) (v_5 Bool) (v_6 Bool) ) 
    (=>
      (and
        (and true (= v_4 true) (= v_5 true) (= v_6 true))
      )
      (applyHanoi v_4 v_5 v_6 A B C D)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (v_4 Bool) (v_5 Bool) (v_6 Bool) ) 
    (=>
      (and
        (and true (= v_4 false) (= v_5 true) (= v_6 true))
      )
      (applyHanoi v_4 v_5 v_6 A B C D)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (v_4 Bool) (v_5 Bool) (v_6 Bool) ) 
    (=>
      (and
        (and true (= v_4 false) (= v_5 false) (= v_6 false))
      )
      (applyHanoi v_4 v_5 v_6 A B C D)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (v_4 Bool) (v_5 Bool) (v_6 Bool) ) 
    (=>
      (and
        (applyHanoi@tailrecurse._crit_edge A B D C)
        (and (= v_4 true) (= v_5 false) (= v_6 false))
      )
      (applyHanoi v_4 v_5 v_6 A B C D)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) ) 
    (=>
      (and
        true
      )
      (applyHanoi@_1 A B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C (Array Int Int)) (D Bool) (E Bool) (F Int) (G (Array Int Int)) (H (Array Int Int)) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (applyHanoi@_1 G I K)
        (and (or (not E) (not B) (not A))
     (or (not E) (not D) (= C G))
     (or (not E) (not D) (= H C))
     (or (not E) (not D) (= F K))
     (or (not E) (not D) (= J F))
     (or (not D) (and E D))
     (or (not E) (and E A))
     (= D true)
     (= B (= K 0)))
      )
      (applyHanoi@tailrecurse G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F Bool) (G (Array Int Int)) (H Int) (I (Array Int Int)) (J Bool) (K Bool) (L Int) (M (Array Int Int)) (N (Array Int Int)) (O Int) (P Int) (Q Int) (v_17 Bool) (v_18 Bool) (v_19 Bool) ) 
    (=>
      (and
        (applyHanoi@tailrecurse M B O D Q)
        (applyHanoi v_17 v_18 v_19 E G H O)
        (and (= v_17 true)
     (= v_18 false)
     (= v_19 false)
     (= F (= H 0))
     (= A (select B O))
     (= C (+ 1 A))
     (= H (+ (- 1) D))
     (or (not K) (not J) (= I G))
     (or (not K) (not J) (= N I))
     (or (not K) (not J) (= L H))
     (or (not K) (not J) (= P L))
     (or (not K) (not J) (not F))
     (or (not J) (and K J))
     (= J true)
     (= E (store B O C)))
      )
      (applyHanoi@tailrecurse M N O P Q)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D (Array Int Int)) (E (Array Int Int)) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (applyHanoi@_1 E G H)
        (and (or (not C) (not B) (= D E))
     (or (not C) (not B) (= F D))
     (or (not C) (not B) A)
     (or (not B) (and C B))
     (= B true)
     (= A (= H 0)))
      )
      (applyHanoi@tailrecurse._crit_edge E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Bool) (H Bool) (I (Array Int Int)) (J Bool) (K Bool) (L (Array Int Int)) (M (Array Int Int)) (N (Array Int Int)) (O Int) (P Int) (v_16 Bool) (v_17 Bool) (v_18 Bool) ) 
    (=>
      (and
        (applyHanoi@tailrecurse M B O D P)
        (applyHanoi v_16 v_17 v_18 E I F O)
        (and (= v_16 true)
     (= v_17 false)
     (= v_18 false)
     (= H (= F 0))
     (= A (select B O))
     (= F (+ (- 1) D))
     (= C (+ 1 A))
     (or (not K) (not G) H)
     (or (not K) (not J) (= L I))
     (or (not K) (not J) (= N L))
     (or (not J) (and K J))
     (or (not K) (and K G))
     (= J true)
     (= E (store B O C)))
      )
      (applyHanoi@tailrecurse._crit_edge M N O P)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (v_4 Bool) (v_5 Bool) (v_6 Bool) ) 
    (=>
      (and
        (and true (= v_4 true) (= v_5 true) (= v_6 true))
      )
      (hanoi v_4 v_5 v_6 A B C D)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (v_4 Bool) (v_5 Bool) (v_6 Bool) ) 
    (=>
      (and
        (and true (= v_4 false) (= v_5 true) (= v_6 true))
      )
      (hanoi v_4 v_5 v_6 A B C D)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (v_4 Bool) (v_5 Bool) (v_6 Bool) ) 
    (=>
      (and
        (and true (= v_4 false) (= v_5 false) (= v_6 false))
      )
      (hanoi v_4 v_5 v_6 A B C D)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (v_4 Bool) (v_5 Bool) (v_6 Bool) ) 
    (=>
      (and
        (hanoi@UnifiedReturnBlock.split A B D C)
        (and (= v_4 true) (= v_5 false) (= v_6 false))
      )
      (hanoi v_4 v_5 v_6 A B C D)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) ) 
    (=>
      (and
        true
      )
      (hanoi@_1 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F (Array Int Int)) (G Int) (H (Array Int Int)) (I Bool) (J Int) (K (Array Int Int)) (L Bool) (M Int) (N Bool) (O Bool) (P (Array Int Int)) (Q (Array Int Int)) (R Int) (S Int) (v_19 Bool) (v_20 Bool) ) 
    (=>
      (and
        (hanoi@_1 P S)
        (hanoi L v_19 v_20 P F A B)
        (and (= v_19 false)
     (= v_20 false)
     (or (not I) E (not D))
     (or (not L) (not E) (not D))
     (or (not N) (and N L) (and N I))
     (or (not N) (not I) (= H P))
     (or (not N) (not I) (= Q H))
     (or (not N) (not I) (= J 1))
     (or (not N) (not I) (= R J))
     (or (not N) (not L) (= K F))
     (or (not N) (not L) (= Q K))
     (or (not N) (not L) (= M G))
     (or (not N) (not L) (= R M))
     (or (not O) (and N O))
     (or (not I) (and I D))
     (or (not L) (= A (+ (- 1) S)))
     (or (not L) (= G (+ 1 C)))
     (or (not L) (= C (* 2 B)))
     (or (not L) (and L D))
     (= O true)
     (= E (= S 1)))
      )
      (hanoi@UnifiedReturnBlock.split P Q R S)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) ) 
    (=>
      (and
        true
      )
      (main@entry A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Bool) (D (Array Int Int)) (E (Array Int Int)) (F (Array Int Int)) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (v_14 Bool) (v_15 Bool) (v_16 Bool) (v_17 Bool) (v_18 Bool) (v_19 Bool) ) 
    (=>
      (and
        (main@entry A)
        (applyHanoi v_14 v_15 v_16 E F G I)
        (hanoi v_17 v_18 v_19 F H G J)
        (let ((a!1 (= C (or (not (<= B 30)) (not (>= B 0))))))
  (and (= v_14 true)
       (= v_15 false)
       (= v_16 false)
       (= v_17 true)
       (= v_18 false)
       (= v_19 false)
       (= D (store A I 0))
       (= L (= J K))
       a!1
       (= K (select H I))
       (= B (+ (- 1) G))
       (or (not N) (and N M))
       (not L)
       (= N true)
       (not C)
       (= E (store D I 0))))
      )
      main@entry.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@entry.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
";
        match parse_wrapped_content(&content) {
            Ok(expr) => {
                println!("解析成功: {:?}", expr);
            }
            Err(err) => {
                println!("解析失败: {}", err);
                panic!("解析失败");
            }
        }
    }

    #[test]
    fn test_one_normal_file_with_pipe_wrapped_symbol() {
        let content = "
(assert (forall ((main@__VERIFIER_assert.split_0 Bool)
        (main@__VERIFIER_assert_0 Bool)
        (main@%_12_0 Bool)
        (main@%_11_0 Bool)
        (main@%.0.in_2 Bool)
        (main@%.0.in_1 Bool)
        (main@orig.main.exit_0 Bool)
        (main@%.0.in_0 Bool)
        (main@precall_0 Bool)
        (main@%_9_0 Bool)
        (main@%_7_0 Bool)
        (main@%_10_0 Bool)
        (main@%.0..0..0.3.i_0 Int)
        (main@%_0_0 Int)
        (main@%shadow.mem.1.0_2 (Array Int Int))
        (main@%shadow.mem.1.0_1 (Array Int Int))
        (|tuple(main@entry_0, main@orig.main.exit_0)| Bool)
        (main@%shadow.mem.1.0_0 (Array Int Int))
        (main@postcall_0 Bool)
        (main@%sm1_0 (Array Int Int))
        (main@%sm2_0 (Array Int Int))
        (main@%_3_0 Bool)
        (main@entry_0 Bool)
        (main@%_6_0 Bool)
        (main@_4_0 Bool)
        (main@%_8_0 Bool)
        (main@%.0..0..0.2.i_0 Int)
        (main@%_5_0 Int)
        (main@%.0..0..0.1.i_0 Int)
        (main@%.0..0..0..i_0 Int)
        (main@%_1_0 Int)
        (@my_jump_buffer_0 Int)
        (main@%sm4_0 (Array Int Int))
        (main@%.0.sroa_cast2_0 Int)
        (main@%sm3_0 (Array Int Int))
        (main@%sm_0 (Array Int Int)))
 (let ((a!1 (=> main@precall_0
                (= main@%_7_0
                   (ite (>= main@%.0..0..0.2.i_0 0)
                        (< main@%.0..0..0.2.i_0 6)
                        false)))))
 (let ((a!2 (and (main@entry main@%sm3_0)
                 (= main@%sm_0 main@%sm3_0)
                 (> main@%_0_0 0)
                 (= main@%.0.sroa_cast2_0 main@%_0_0)
                 (= main@%sm1_0 (store main@%sm4_0 main@%_0_0 0))
                 (= main@%_1_0 (+ @my_jump_buffer_0 (* 0 164) (* 0 164)))
                 (or (<= @my_jump_buffer_0 0) (> main@%_1_0 0))
                 (= main@%.0..0..0..i_0 (select main@%sm1_0 main@%_0_0))
                 (= main@%_3_0 (< main@%.0..0..0..i_0 5))
                 (=> main@_4_0 (and main@_4_0 main@entry_0))
                 (=> (and main@_4_0 main@entry_0) main@%_3_0)
                 (=> main@_4_0
                     (= main@%.0..0..0.1.i_0 (select main@%sm1_0 main@%_0_0)))
                 (=> main@_4_0 (= main@%_5_0 (+ main@%.0..0..0.1.i_0 1)))
                 (=> main@_4_0
                     (= main@%sm2_0 (store main@%sm1_0 main@%_0_0 main@%_5_0)))
                 (=> main@_4_0
                     (= main@%.0..0..0.2.i_0 (select main@%sm2_0 main@%_0_0)))
                 (=> main@precall_0 (and main@precall_0 main@_4_0))
                 (=> (and main@precall_0 main@_4_0) (not main@%_6_0))
                 a!1
                 (=> main@precall_0 (not main@%_8_0))
                 (=> main@postcall_0 (and main@postcall_0 main@_4_0))
                 (=> (and main@postcall_0 main@_4_0) main@%_6_0)
                 (=> |tuple(main@entry_0, main@orig.main.exit_0)| main@entry_0)
                 (=> main@orig.main.exit_0
                     (or (and main@orig.main.exit_0 main@postcall_0)
                         |tuple(main@entry_0, main@orig.main.exit_0)|))
                 (=> |tuple(main@entry_0, main@orig.main.exit_0)|
                     (not main@%_3_0))
                 (=> (and main@orig.main.exit_0 main@postcall_0)
                     (= main@%shadow.mem.1.0_0 main@%sm2_0))
                 (=> |tuple(main@entry_0, main@orig.main.exit_0)|
                     (= main@%shadow.mem.1.0_1 main@%sm1_0))
                 (=> (and main@orig.main.exit_0 main@postcall_0)
                     (= main@%shadow.mem.1.0_2 main@%shadow.mem.1.0_0))
                 (=> |tuple(main@entry_0, main@orig.main.exit_0)|
                     (= main@%shadow.mem.1.0_2 main@%shadow.mem.1.0_1))
                 (=> main@orig.main.exit_0
                     (= main@%.0..0..0.3.i_0
                        (select main@%shadow.mem.1.0_2 main@%_0_0)))
                 (=> main@orig.main.exit_0
                     (= main@%_9_0 (= main@%.0..0..0.3.i_0 5)))
                 (=> main@orig.main.exit_0 (not main@%_10_0))
                 (=> main@__VERIFIER_assert_0
                     (or (and main@__VERIFIER_assert_0 main@precall_0)
                         (and main@__VERIFIER_assert_0 main@orig.main.exit_0)))
                 (=> (and main@__VERIFIER_assert_0 main@precall_0)
                     (= main@%.0.in_0 main@%_7_0))
                 (=> (and main@__VERIFIER_assert_0 main@orig.main.exit_0)
                     (= main@%.0.in_1 main@%_9_0))
                 (=> (and main@__VERIFIER_assert_0 main@precall_0)
                     (= main@%.0.in_2 main@%.0.in_0))
                 (=> (and main@__VERIFIER_assert_0 main@orig.main.exit_0)
                     (= main@%.0.in_2 main@%.0.in_1))
                 (=> main@__VERIFIER_assert_0
                     (= main@%_11_0 (xor main@%.0.in_2 true)))
                 (=> main@__VERIFIER_assert_0 main@%_11_0)
                 (=> main@__VERIFIER_assert_0 (not main@%_12_0))
                 (=> main@__VERIFIER_assert.split_0
                     (and main@__VERIFIER_assert.split_0
                          main@__VERIFIER_assert_0))
                 main@__VERIFIER_assert.split_0)))
   (=> a!2 main@__VERIFIER_assert.split)))))";
        match parse_wrapped_content(&content) {
            Ok(expr) => {
                println!("解析成功: {:?}", expr);
            }
            Err(err) => {
                println!("解析失败: {}", err);
                panic!("解析失败");
            }
        }
    }

    #[test]
    fn test_one_normal_datalog_file_with_string() {
        let expr = parse_by_filename("tests/data/4SB.smt2").map_err(|e| e);
        match expr {
            Ok(expr) => {
                println!("解析成功: {:?}", expr);
            }
            Err(err) => {
                println!("解析失败: {}", err);
                panic!("解析失败");
            }
        }
    }
    
    #[test]
    fn parse_datalog_with_string(){
      let content = r#"
(set-logic UFLIA)
(set-info :notes |datalog2chc|)
(set-info :original "/tmp/sea-b9w61hkt/jain_2-1.pp.ms.o.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(assert false)
(check-sat)

"#;
      let expr = parse_wrapped_content(&content).map_err(|e| e);
      match expr {
          Ok(expr) => {
              println!("解析成功: {:?}", expr);
          }
          Err(err) => {
              println!("解析失败: {}", err);
              panic!("解析失败");
          }
      }
    }

    fn convert_to_dst_dir_and_solve_again(filename: &str) {
        // use z3 to solve the file fist
        let src_dir = "tests/data";
        let src_filename = format!("{}/{}", src_dir, filename);
        println!("src: {}", src_filename);
        let solve_1 = Command::new("z3")
            .arg(&src_filename)
            .output()
            .expect("failed to execute process");
        let solve_1_result = String::from_utf8_lossy(&solve_1.stdout);
        // convert and write to temp dir
        let dst_dir = "tests/data/temp";
        let dst_filename = format!("{}/{}", dst_dir, filename);
        println!("env: {:?}", std::env::current_dir().unwrap());
        println!("dst: {}", dst_filename);
        let convert_result = convert_datalogchc_2_chc(&src_filename);
        match convert_result {
            Ok(chc) => {
                // create the file and write
                std::fs::create_dir_all(dst_dir).unwrap();
                std::fs::write(&dst_filename, chc).unwrap();
            }
            Err(err) => {
                panic!("Failed to convert: {}", err);
            }
        }
        // use z3 to solve the converted file
        let solve_2 = Command::new("z3")
            .arg(&dst_filename)
            .output()
            .expect("failed to execute process");
        let solve_2_result = String::from_utf8_lossy(&solve_2.stdout);
        assert_eq!(solve_1_result, solve_2_result);
    }

    fn convert_bv_to_dst_dir_and_solve_again(filename: &str) {
        // use z3 to solve the file fist
        let src_dir = "tests/data";
        let src_filename = format!("{}/{}", src_dir, filename);
        println!("src: {}", src_filename);
        let solve_1 = Command::new("z3")
            .arg(&src_filename)
            .output()
            .expect("failed to execute process");
        // convert and write to temp dir
        let dst_dir = "tests/data/temp";
        let dst_filename = format!("{}/{}", dst_dir, filename);
        let convert_result = convert_chclia_2_chcbv(&src_filename);
        match convert_result {
            Ok(chc) => {
                // create the file and write
                std::fs::create_dir_all(dst_dir).unwrap();
                std::fs::write(&dst_filename, chc).unwrap();
            }
            Err(err) => {
                panic!("Failed to convert: {:?}", filename);
            }
        }
        // use z3 to solve the converted file
        let solve_2 = Command::new("z3")
            .arg(&dst_filename)
            .output()
            .expect("failed to execute process");

    } 

    #[test]
    fn convert_datalog_file_1() {
        let filename = "s3_clnt.blast.01.i.cil-2.smt2";
        convert_to_dst_dir_and_solve_again(filename);
    }

    #[test]
    fn convert_lia_file_with_meta() {
        let filename = "meta_infos.smt2";
        convert_bv_to_dst_dir_and_solve_again(filename);
    }
}
