; y <= x or y = 0
(define-fun inv0 ((y Int) (x Int)) (Bool) (or (<= y x) (= y 0)))
; y = x or y = 0
(define-fun ps ((y Int) (x Int)) (Bool) (or (= y x) (= y 0)))


(declare-const bb2 Bool)
(declare-const arg Int)
(declare-const tmp3 Int)
(declare-const tmp5 Bool)
(declare-const tmp4 Int)
(declare-const bb9 Bool)
(declare-const bb6 Bool)
(declare-const tmp7 Int)
(declare-const tmp10 Int)
(declare-const tmp1_0 Int)
(declare-const bb Bool)



(assert (not (=> (and 

(= bb (and bb2 (inv0 0 arg))) 
(= bb2 (=> (and (and (= tmp3 tmp1_0) (= tmp5 (< tmp1_0 arg)) (= tmp4 arg)) (inv0 tmp1_0 arg)) (and bb9 bb6))) 
(= bb6 (=> (and (= tmp7 tmp1_0) (and (inv0 tmp1_0 arg) (< tmp1_0 arg))) (inv0 (+ tmp1_0 1) arg))) 
(= bb9 (=> (and (= tmp10 tmp1_0) (and (inv0 tmp1_0 arg) (not (< tmp1_0 arg)))) (ps tmp1_0 arg)))) 

bb)))

(check-sat)
(get-model)
