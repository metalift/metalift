(define-fun-rec sum_n ((x Int)) Int
                  (ite (>= x 1)
                       (+ x (sum_n (- x 1)))
                       0))

; ps : x = sum_n(2) + sum_n(3)
(define-fun ps ( (x Int) ) Bool
  (= x (+ (sum_n 2) (sum_n 3))))

; first invariant : (x = sum_n(y-1) and y>=1 and y <= 3)
(define-fun inv1 ( (x Int) (y Int) ) Bool
  (and (= x (sum_n (- y 1))) (>= y 1) (<= y 3) ))

; second invariant : (x = sum_n(z-1) + sum_n(2) and z>=1 and z <= 4)
(define-fun inv0 ( (x Int) (z Int) ) Bool
  (and (= x (+ (sum_n 2) (sum_n (- z 1)))) (>= z 1) (<= z 4) ))


(declare-const tmp20 Int)
(declare-const tmp23 Int)
(declare-const bb Bool)
(declare-const bb3 Bool)
(declare-const tmp_0 Int)
(declare-const tmp4 Int)
(declare-const tmp5 Bool)
(declare-const bb12 Bool)
(declare-const bb6 Bool)
(declare-const tmp7 Int)
(declare-const tmp10 Int)
(declare-const tmp18 Int)
(declare-const tmp8 Int)
(declare-const bb13 Bool)
(declare-const tmp_2 Int)
(declare-const tmp2_3 Int)
(declare-const tmp14 Int)
(declare-const tmp15 Bool)
(declare-const bb22 Bool)
(declare-const bb16 Bool)
(declare-const tmp17 Int)
(declare-const tmp1_1 Int)



(assert (not (=> (and 

(= bb (and bb3 (inv1 0 1))) 

(= bb3 (=> (and (and (= tmp4 tmp1_1) (= tmp5 (< tmp1_1 3))) (inv1 tmp_0 tmp1_1)) (and bb12 bb6))) 

(= bb6 (=> (and (and (= tmp7 tmp_0) (= tmp10 tmp1_1) (= tmp8 tmp1_1)) (and (inv1 tmp_0 tmp1_1) (< tmp1_1 3))) (inv1 (+ tmp_0 tmp1_1) (+ tmp1_1 1)))) 

(= bb12 (=> (and (inv1 tmp_0 tmp1_1) (not (< tmp1_1 3))) (and bb13 (inv0 tmp_0 1)))) 

(= bb13 (=> (and (and (= tmp14 tmp2_3) (= tmp15 (< tmp2_3 4))) (and (inv1 tmp_0 tmp1_1) (not (< tmp1_1 3)) (inv0 tmp_2 tmp2_3))) (and bb22 bb16))) 

(= bb16 (=> (and (and (= tmp17 tmp_2) (= tmp18 tmp2_3) (= tmp20 tmp2_3)) (and (inv1 tmp_0 tmp1_1) (not (< tmp1_1 3)) (inv0 tmp_2 tmp2_3) (< tmp2_3 4))) (inv0 (+ tmp_2 tmp2_3) (+ tmp2_3 1)))) 

(= bb22 (=> (and (= tmp23 tmp_2) (and (inv1 tmp_0 tmp1_1) (not (< tmp1_1 3)) (inv0 tmp_2 tmp2_3) (not (< tmp2_3 4)))) (ps tmp_2)))

) bb)))

(check-sat)
(get-model)
