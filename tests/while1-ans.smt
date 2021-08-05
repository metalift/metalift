; y <= x or y = 0
(define-fun inv0 ((y Int) (x Int)) Bool (or (<= y x) (= y 0)))
; y = x or y = 0
(define-fun ps ((y Int) (x Int)) Bool (or (= y x) (= y 0)))
