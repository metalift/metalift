; begin integer functions
; TODO: fix
(define-fun-rec integer_exp ((n Int)) Int
(ite (<= n 0) 1 (mod (* (integer_exp (- n 1)) 3) 64)))

(define-fun-rec integer_sqrt_helper ((n Int) (guess Int)) Int
(ite (or (or (= guess 0) (= guess 1)) (> guess 64)) 1 (ite (= guess (div n guess)) guess (integer_sqrt_helper n (div (+ guess (div n guess)) 2)))))

(define-fun integer_sqrt ((n Int)) Int
(integer_sqrt_helper (div n 2) n))

; end integer functions
