(define-fun ps ((tmp7 Int) (arg Int)) Bool
(and (=> (> arg 10) (= tmp7 1)) 
     (=> (<= arg 10) (= tmp7 2))) 
)


(declare-const tmp3 Bool)
(declare-const tmp2 Int)
(declare-const bb4 Bool)
(declare-const bb5 Bool)
(declare-const arg Int)
(declare-const bb Bool)
(declare-const bb6 Bool)
(declare-const tmp7 Int)



(assert (not (=> (and (= bb (=> (and (= tmp2 arg) (= tmp3 (< 10 arg))) (and bb5 bb4))) (= bb4 (=> (< 10 arg) bb6)) (= bb5 (=> (not (< 10 arg)) bb6)) (= bb6 (=> (and (= tmp7 (ite (not (< 10 arg)) 2 1)) (or (< 10 arg) (not (< 10 arg)))) (ps tmp7 arg)))) bb)))

(check-sat)
(get-model)
