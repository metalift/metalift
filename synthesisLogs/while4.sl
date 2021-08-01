(define-fun-rec sum_n ((x Int)) Int
                  (ite (>= x 1)
                       (+ x (sum_n (- x 1)))
                       0))

(synth-fun ps ( (x Int) ) Bool
 ((B Bool) (C Int) (D Int))
 ((B Bool ((= C (sum_n D))))
 (C Int (x))
 (D Int (1 2))))
       
(synth-fun inv0 ( (dummy Int) (x Int) (y Int) ) Bool
   ((B Bool) (C Bool) (D Bool) (E Int) (F Int))
   ((B Bool ((and C D)))
   (C Bool ((= E (sum_n (- E F)))))
   (D Bool ((and (>= E F) (<= E F))))
   (E Int (x y))
   (F Int (1 2 3))))

(declare-const tmp3 Int)
(declare-const tmp_0 Int)
(declare-const bb2 Bool)
(declare-const tmp1_1 Int)
(declare-const bb Bool)
(declare-const tmp4 Bool)
(declare-const bb11 Bool)
(declare-const bb5 Bool)
(declare-const tmp6 Int)
(declare-const tmp9 Int)
(declare-const tmp7 Int)
(declare-const tmp12 Int)



(constraint (=> (and (= bb (and bb2 (inv0 2 0 1))) (= bb2 (=> (and (and (= tmp3 tmp1_1) (= tmp4 (< tmp1_1 3))) (inv0 2 tmp_0 tmp1_1)) (and bb11 bb5))) (= bb5 (=> (and (and (= tmp6 tmp_0) (= tmp9 tmp1_1) (= tmp7 tmp1_1)) (and (inv0 2 tmp_0 tmp1_1) (< tmp1_1 3))) (inv0 2 (+ tmp_0 tmp1_1) (+ tmp1_1 1)))) (= bb11 (=> (and (= tmp12 tmp_0) (and (inv0 2 tmp_0 tmp1_1) (not (< tmp1_1 3)))) (ps tmp_0)))) bb))

(check-synth)