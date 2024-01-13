(define-fun-rec sum_n ((x Int)) Int
                  (ite (>= x 1)
                       (+ x (sum_n (- x 1)))
                       0))

(define-fun ps ( (x Int) (arg Int) ) Bool
  (or (>= 1 arg) (= x (sum_n (- arg 1)))))

(define-fun inv0 ( (x Int) (y Int) (arg Int) ) Bool
  (or (>= 1 arg) (and (<= y arg) (= x (sum_n (- y 1))) (>= y 1))))
