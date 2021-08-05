(define-fun-rec sum_n ((x Int)) Int
                  (ite (>= x 1)
                       (+ x (sum_n (- x 1)))
                       0))

(synth-fun ps ( (tmp14 Int) (arg Int) ) Bool
 ((B Bool) (C Bool) (D Bool) (E Int) (F Int))
 ((B Bool ((or C D)))
 (C Bool ((>= F arg)))
 (D Bool ((= E (sum_n (- arg F)))))
 (E Int (tmp14))
 (F Int (1))))
       
(synth-fun inv0 ((tmp1 Int) (tmp2 Int) (arg Int) ) Bool
   ((B Bool) (C Bool) (D Bool) (E Int) (F Int))
   ((B Bool ((or C D)))
   (C Bool ((>= 1 arg) ))
   (D Bool ((and (>= E 1) (<= E arg) (= E (sum_n (- E F))))))
   (E Int (tmp1 tmp2))
   (F Int (1))))