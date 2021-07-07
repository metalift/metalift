(define-fun ps ((tmp12 Int) (arg Int)) (Bool) 
(and (=> (= arg 1) (= tmp12 10)) 
     (=> (= arg 2) (= tmp12 10)) 
     (=> (= arg 3) (= tmp12 20))
     (=> (not (or (= arg 1) (= arg 2) (= arg 3))) (= tmp12 20))
))


(declare-const tmp2 Int)
(declare-const arg Int)
(declare-const bb3 Bool)
(declare-const bb6 Bool)
(declare-const bb4 Bool)
(declare-const bb5 Bool)
(declare-const bb Bool)
(declare-const bb7 Bool)
(declare-const tmp8 Int)



(assert (not (=> (and (= bb (=> (= tmp2 arg) (and bb6 bb3 bb4 bb5))) (= bb3 (=> (= arg 1) bb7)) (= bb4 (=> (= arg 2) bb7)) (= bb5 (=> (= arg 3) bb7)) (= bb6 (=> (not (or (= arg 1) (= arg 2) (= arg 3))) bb7)) (= bb7 (=> (and (= tmp8 (ite (or (= arg 3) (not (or (= arg 1) (= arg 2) (= arg 3)))) 20 10)) (or (= arg 1) (= arg 2) (= arg 3) (not (or (= arg 1) (= arg 2) (= arg 3))))) (ps tmp8 arg)))) bb)))

(check-sat)
(get-model)