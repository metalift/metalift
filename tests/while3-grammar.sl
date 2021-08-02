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