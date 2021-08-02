(define-fun-rec sum_n ((x Int)) Int
                  (ite (>= x 1)
                       (+ x (sum_n (- x 1)))
                       0))

(synth-fun ps ( (x Int) (arg Int) ) Bool
 ((B Bool) (C Bool) (D Bool) (E Int) (F Int))
 ((B Bool ((or C D)))
 (C Bool ((>= F arg)))
 (D Bool ((= E (sum_n (- arg F)))))
 (E Int (x))
 (F Int (1))))
       
(synth-fun inv0 ((x Int) (y Int) (arg Int) ) Bool
   ((B Bool) (C Bool) (D Bool) (E Int) (F Int))
   ((B Bool ((or C D)))
   (C Bool ((>= 1 arg) ))
   (D Bool ((and (>= E 1) (<= E arg) (= E (sum_n (- E F))))))
   (E Int (x y))
   (F Int (1))))

(declare-const bb Bool)
(declare-const bb3 Bool)
(declare-const arg Int)
(declare-const tmp2_1 Int)
(declare-const tmp1_0 Int)
(declare-const tmp4 Int)
(declare-const tmp6 Bool)
(declare-const tmp5 Int)
(declare-const bb13 Bool)
(declare-const bb7 Bool)
(declare-const tmp8 Int)
(declare-const tmp9 Int)
(declare-const tmp11 Int)
(declare-const tmp14 Int)



(constraint (=> (and (= bb (and bb3 (inv0 0 1 arg))) (= bb3 (=> (and (and (= tmp4 tmp2_1) (= tmp6 (< tmp2_1 arg)) (= tmp5 arg)) (inv0 tmp1_0 tmp2_1 arg)) (and bb13 bb7))) (= bb7 (=> (and (and (= tmp8 tmp1_0) (= tmp9 tmp2_1) (= tmp11 tmp2_1)) (and (inv0 tmp1_0 tmp2_1 arg) (< tmp2_1 arg))) (inv0 (+ tmp1_0 tmp2_1) (+ tmp2_1 1) arg))) (= bb13 (=> (and (= tmp14 tmp1_0) (and (inv0 tmp1_0 tmp2_1 arg) (not (< tmp2_1 arg)))) (ps tmp1_0 arg)))) bb))

(check-synth)