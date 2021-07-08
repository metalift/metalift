(define-fun inv0 ((x Int) (arg Int)) (Bool) (or (<= 0 x) (< arg 0)))
(define-fun ps ((x Int) (arg Int)) (Bool) (or (= x 0) (< arg 0)))

;; alternative formulation
;; 100 <= x --> 0 <= return_val
;(define-fun inv0 ((return_val Int) (x Int)) (Bool) (=> (<= 100 x) (<= 0 return_val) ))
;; 100 <= x --> return_val = 0
;(define-fun ps ((return_val Int) (x Int)) (Bool) (=> (<= 100 x) (= return_val 0)))


(declare-const arg Int)
(declare-const tmp_0 Int)
(declare-const tmp2 Int)
(declare-const bb Bool)
(declare-const tmp3 Bool)
(declare-const bb7 Bool)
(declare-const bb4 Bool)
(declare-const tmp5 Int)
(declare-const tmp8 Int)
(declare-const bb1 Bool)



(assert (not (=> (and 

(= bb (and bb1 (inv0 arg arg))) 

(= bb1 (=> (and (and (= tmp2 tmp_0) (= tmp3 (< 0 tmp_0))) (inv0 tmp_0 arg)) (and bb7 bb4))) 

(= bb4 (=> (and (= tmp5 tmp_0) (and (inv0 tmp_0 arg) (< 0 tmp_0))) (inv0 (- tmp_0 1) arg))) 

(= bb7 (=> (and (= tmp8 tmp_0) (and (inv0 tmp_0 arg) (not (< 0 tmp_0)))) (ps tmp_0 arg)))

) bb)))

(check-sat)
(get-model)
