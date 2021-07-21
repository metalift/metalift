(define-fun inv0 ((tmp10 Int) (arg Int)) (Bool) (or (<= tmp10 arg) (= tmp10 0)))
(define-fun ps ((tmp10 Int) (arg Int)) (Bool) (or (= tmp10 arg) (= tmp10 0)))

;(declare-const arg Int)
;(declare-const tmp10 Int)
;(declare-const tmp1 Int)
;(declare-const tmp3 Int)
;(declare-const bb Bool)
;(declare-const bb2 Bool)
;(declare-const tmp4 Int)
;(declare-const tmp5 Bool)
;(declare-const bb9 Bool)
;(declare-const bb6 Bool)
;(declare-const tmp7 Int)
;
;
;(assert (not (=> 
;(and 
;(= bb (and (inv0 0 arg) bb2))
;(= bb2 (=> (and (and (= tmp3 tmp10) (= tmp5 (< tmp10 arg)) (= tmp4 arg)) (inv0 tmp10 arg)) (and bb9 bb6))) 
;(= bb6 (=> (and tmp5 (= tmp7 tmp10)) (inv0 (+ tmp10 1) arg))) 
;;(= bb6 true)
;(= bb9 (=> (and (not tmp5) (= tmp10 tmp10)) (ps tmp10 arg)))
;) 
;
;bb)))
;
;
;;(assert (not (=> (and (inv0 tmp10 arg) (not (< tmp10 arg))) (ps tmp10 arg))))
;
;(check-sat)
;(get-model)
;
