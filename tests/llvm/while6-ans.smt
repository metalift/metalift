(define-fun-rec sum_n ((x Int)) Int
                  (ite (>= x 1)
                       (+ x (sum_n (- x 1)))
                       0))

(define-fun ps ( (x Int) ) Bool
  (= x 30))

; inner loop invariant
(define-fun inv0 ((x Int) (y Int) (x2 Int) (y Int)) Bool
  (and (= x (sum_n (- y 1))) (>= y 1) (<= y 3) ))

; outer loop invariant
(define-fun inv1 ((x Int) (z Int) ) Bool
  (and (= x (+ (sum_n 2) (sum_n (- z 1)))) (>= z 1) (<= z 4) ))
