(define-fun-rec sum_n ((x Int)) Int
                  (ite (>= x 1)
                       (+ x (sum_n (- x 1)))
                       0))

(synth-fun ps ( (tmp12 Int) ) Bool
 ((B Bool) (C Int) (D Int))
 ((B Bool ((= C (sum_n D))))
 (C Int (tmp12))
 (D Int (1 2))))
       
(synth-fun inv0 ((tmp Int) (tmp1 Int) ) Bool
   ((B Bool) (C Bool) (D Bool) (E Int) (F Int))
   ((B Bool ((and C D)))
   (C Bool ((= E (sum_n (- E F)))))
   (D Bool ((and (>= E F) (<= E F))))
   (E Int (tmp tmp1))
   (F Int (1 2 3))))