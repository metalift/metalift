(define-fun ps ((a Int) (i Int)) Bool 
(=> (> i 10) (= a 1) (= a 0))
)


(declare-const tmp3 Bool)
(declare-const bb5 Bool)
(declare-const arg Int)
(declare-const tmp2 Int)
(declare-const bb Bool)
(declare-const tmp6 Int)
(declare-const bb4 Bool)


(assert (not 
(=> (&& 

(= bb (=> (&& (&& (= tmp2 arg) (= tmp3 (< 10 arg))) true) (&& bb5 bb4))) 

(= bb4 (=> (&& true (< 10 arg)) bb5)) 

(= bb5 (=> (&& (= tmp6 (ite (&& true (< 10 arg)) 1 0)) (&& (or true (&& true (< 10 arg))) (not (ite (&& true (< 10 arg)) (< 10 arg) (< 10 arg))))) 
       (ps (ite (&& true (< 10 arg)) 1 0) (ite (&& true (< 10 arg)) arg arg))))

) bb)))

(check-sat)
(get-model)
