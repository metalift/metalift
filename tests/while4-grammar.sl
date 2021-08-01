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