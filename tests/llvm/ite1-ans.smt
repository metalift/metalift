(define-fun ps ((tmp7 Int) (arg Int)) Bool
(and (=> (> arg 10) (= tmp7 1))
     (=> (<= arg 10) (= tmp7 2)))
)
