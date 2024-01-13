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
