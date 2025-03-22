(set-logic UFBV)

(declare-const x (_ BitVec 32))  ; 假设你使用32位宽度的BitVec
(declare-const y (_ BitVec 32))  ; 假设你使用32位宽度的BitVec

(define-fun minus-two-ver-1 () (_ BitVec 32) (bvneg (_ bv2 32)))
(define-fun minus-two-ver-2 () (_ BitVec 32) #b11111111111111111111111111111110)

(assert (= x minus-two-ver-1))
(assert (= y minus-two-ver-2))


(define-fun oper0 () (_ BitVec 32) (bvadd (_ bv2 32) (_ bv2 32)))
(define-fun oper1 () (_ BitVec 32) (bvsub (_ bv2 32) (_ bv2 32)))
(define-fun oper2 () (_ BitVec 32) (bvmul (_ bv2 32) (_ bv2 32)))
(define-fun oper3 () (_ BitVec 32) (bvsmod (_ bv2 32) (_ bv2 32)))
(define-fun oper4 () (_ BitVec 32) (bvsrem (_ bv2 32) (_ bv2 32)))
(define-fun oper5 () (_ BitVec 32) (bvsdiv (_ bv2 32) (_ bv2 32)))
(define-fun oper6 () Bool (bvsge (_ bv2 32) (_ bv2 32)))
(define-fun oper7 () Bool (bvsle (_ bv2 32) (_ bv2 32)))
(define-fun oper8 () Bool (bvsgt (_ bv2 32) (_ bv2 32)))
(define-fun oper9 () Bool (bvslt (_ bv2 32) (_ bv2 32)))


(define-fun u_oper0 () (_ BitVec 32) (bvadd (_ bv2 32) (_ bv2 32)))
(define-fun u_oper1 () (_ BitVec 32) (bvsub (_ bv2 32) (_ bv2 32)))
(define-fun u_oper2 () (_ BitVec 32) (bvmul (_ bv2 32) (_ bv2 32)))
(define-fun u_oper3 () (_ BitVec 32) (bvmod (_ bv2 32) (_ bv2 32)))
(define-fun u_oper4 () (_ BitVec 32) (bvurem (_ bv2 32) (_ bv2 32)))
(define-fun u_oper5 () (_ BitVec 32) (bvudiv (_ bv2 32) (_ bv2 32)))
(define-fun u_oper6 () Bool (bvuge (_ bv2 32) (_ bv2 32)))
(define-fun u_oper7 () Bool (bvule (_ bv2 32) (_ bv2 32)))
(define-fun u_oper8 () Bool (bvugt (_ bv2 32) (_ bv2 32)))
(define-fun u_oper9 () Bool (bvult (_ bv2 32) (_ bv2 32)))

(check-sat)
(get-model)
