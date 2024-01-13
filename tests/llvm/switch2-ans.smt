(define-fun ps ((tmp12 Int) (arg Int)) Bool
(and (=> (= arg 1) (= tmp12 10))
     (=> (= arg 2) (= tmp12 10))
     (=> (= arg 3) (= tmp12 20))
     (=> (not (or (= arg 1) (= arg 2) (= arg 3))) (= tmp12 20))
))
