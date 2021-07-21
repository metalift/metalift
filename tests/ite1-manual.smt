(declare-const b1 Bool)
(declare-const b6 Bool)
(declare-const b7 Bool)
(declare-const b8 Bool)

(declare-const r0 Int)
(declare-const r4 Int)
(declare-const r5 Bool)
(declare-const r9 Int)

(define-fun iff ( (c1 Bool) (c2 Bool) ) (Bool) (and (=> c1 c2) (=> c2 c1)))

(define-fun ps ( (r0 Int) (r9 Int) ) (Bool) (or (= 1 r9) (= 2 r9)))

(assert (not (=> 

(and 
(iff b1 (=> (and (= r4 r0) (= r5 (< r4 10))) (and b6 b7)))

(iff b6 b8)

(iff b7 b8)

(iff b8 (=> (= r9 (ite b6 1 2)) (ps r0 r9)))
)

b1)))


(check-sat)
(get-model)
