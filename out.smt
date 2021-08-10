(define-fun-rec sum_n ((x Int)) Int
                  (ite (>= x 1)
                       (+ x (sum_n (- x 1)))
                       0))

; ps : x = sum_n(2)
(define-fun ps ( (x Int) ) Bool 
  (= x (sum_n 2)))

; invariant : (x = sum_n(y-1) and y>=1 and y <= 3)
(define-fun inv0 ((x Int) (y Int) ) Bool
  (and (= x (sum_n (- y 1))) (>= y 1) (<= y 3) ))



(declare-const bb Bool)
(declare-const bb2 Bool)
(declare-const tmp3 Int)
(declare-const tmp_0 Int)
(declare-const tmp4 Bool)
(declare-const bb11 Bool)
(declare-const bb5 Bool)
(declare-const tmp6 Int)
(declare-const tmp9 Int)
(declare-const tmp7 Int)
(declare-const tmp1_1 Int)
(declare-const tmp12 Int)



(assert (not (=> (and (= bb (and bb2 (inv0 0 1))) (= bb2 (=> (and (and (= tmp3 tmp1_1) (= tmp4 (< tmp1_1 3))) (inv0 tmp_0 tmp1_1)) (and bb11 bb5))) (= bb5 (=> (and (and (= tmp6 tmp_0) (= tmp9 tmp1_1) (= tmp7 tmp1_1)) (and (inv0 tmp_0 tmp1_1) (< tmp1_1 3))) (inv0 (+ tmp_0 tmp1_1) (+ tmp1_1 1)))) (= bb11 (=> (and (= tmp12 tmp_0) (and (inv0 tmp_0 tmp1_1) (not (< tmp1_1 3)))) (ps tmp_0)))) bb)))

(check-sat)
(get-model)