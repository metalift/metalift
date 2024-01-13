(define-fun-rec sum_n ((x Int)) Int
                  (ite (>= x 1)
                       (+ x (sum_n (- x 1)))
                       0))

; ps : x = sum_n(2) + sum_n(3)
(define-fun ps ( (x Int) ) Bool
  (= x (+ (sum_n 2) (sum_n 3))))

; first invariant : (x = sum_n(y-1) and y>=1 and y <= 3)
(define-fun inv1 ((x Int) (y Int) ) Bool
  (and (= x (sum_n (- y 1))) (>= y 1) (<= y 3) ))

; second invariant : (x = sum_n(z-1) + sum_n(2) and z>=1 and z <= 4)
(define-fun inv0 ((x Int) (z Int) ) Bool
  (and (= x (+ (sum_n 2) (sum_n (- z 1)))) (>= z 1) (<= z 4) ))
