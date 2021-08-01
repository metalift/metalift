(define-fun-rec sum_n ((x Int)) Int
                  (ite (>= x 1)
                       (+ x (sum_n (- x 1)))
                       0))
                       
(define-fun ps ( (x Int) ) Bool 
  (= x 30))

; inner loop invariant
(define-fun inv0 ( (dummy Int) (x Int) (y Int) (x2 Int) (y Int)) Bool
  (and (= x (sum_n (- y 1))) (>= y 1) (<= y 3) ))

; outer loop invariant
(define-fun inv1 ( (dummy Int) (x Int) (z Int) ) Bool
  (and (= x (+ (sum_n 2) (sum_n (- z 1)))) (>= z 1) (<= z 4) ))


(declare-const bb3 Bool)
(declare-const tmp2_0 Int)
(declare-const tmp1_3 Int)
(declare-const tmp4 Int)
(declare-const tmp5 Bool)
(declare-const bb18 Bool)
(declare-const bb6 Bool)
(declare-const bb7 Bool)
(declare-const tmp_1 Int)
(declare-const tmp16 Int)
(declare-const tmp19 Int)
(declare-const tmp13 Int)
(declare-const tmp_4 Int)
(declare-const tmp2_5 Int)
(declare-const tmp8 Int)
(declare-const tmp9 Bool)
(declare-const bb15 Bool)
(declare-const bb10 Bool)
(declare-const tmp11 Int)
(declare-const bb Bool)
(declare-const tmp2_2 Int)



(assert (not (=> (and (= bb (and bb3 (inv0 4 0 0 0 0))) (= bb3 (=> (and (and (= tmp4 tmp1_3) (= tmp5 (< tmp1_3 3))) (inv0 4 tmp2_2 tmp_1 tmp2_2 tmp1_3)) (and bb18 bb6))) (= bb6 (=> (and (inv0 4 tmp2_2 tmp_1 tmp2_2 tmp1_3) (< tmp1_3 3)) (and bb7 (inv1 2 tmp_1 0)))) (= bb7 (=> (and (and (= tmp8 tmp2_5) (= tmp9 (< tmp2_5 5))) (and (inv0 4 tmp2_2 tmp_1 tmp2_2 tmp1_3) (< tmp1_3 3) (inv1 2 tmp_4 tmp2_5))) (and bb15 bb10))) (= bb10 (=> (and (and (= tmp11 tmp_4) (= tmp13 tmp2_5)) (and (inv0 4 tmp2_2 tmp_1 tmp2_2 tmp1_3) (< tmp1_3 3) (inv1 2 tmp_4 tmp2_5) (< tmp2_5 5))) (inv1 2 (+ tmp_4 2) (+ tmp2_5 1)))) (= bb15 (=> (and (= tmp16 tmp1_3) (and (inv0 4 tmp2_2 tmp_1 tmp2_2 tmp1_3) (< tmp1_3 3) (inv1 2 tmp_4 tmp2_5) (not (< tmp2_5 5)))) (inv0 4 tmp2_5 tmp_4 tmp2_5 (+ tmp1_3 1)))) (= bb18 (=> (and (= tmp19 tmp_1) (and (inv0 4 tmp2_2 tmp_1 tmp2_2 tmp1_3) (not (< tmp1_3 3)))) (ps tmp_1)))) bb)))

(check-sat)
(get-model)