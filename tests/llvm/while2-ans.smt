(define-fun inv0 ((x Int) (arg Int)) Bool (or (<= 0 x) (< arg 0)))
(define-fun ps ((x Int) (arg Int)) Bool (or (= x 0) (< arg 0)))

;; alternative formulation
;; 100 <= x --> 0 <= return_val
;(define-fun inv0 ((return_val Int) (x Int)) Bool (=> (<= 100 x) (<= 0 return_val) ))
;; 100 <= x --> return_val = 0
;(define-fun ps ((return_val Int) (x Int)) Bool (=> (<= 100 x) (= return_val 0)))
