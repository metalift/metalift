(declare-sort VectorClock 0)
(declare-const vector_clock_bottom VectorClock)
(declare-fun vc_lt ( VectorClock VectorClock ) Bool)

(assert (forall ((vc VectorClock))
(=> (not (= vc vector_clock_bottom)) (vc_lt vector_clock_bottom vc))
))

(assert (forall ((vc VectorClock))
(= false (vc_lt vc vc))
))

(assert (forall ((vc VectorClock))
(= false (vc_lt vc vc))
))

(assert (forall ((vc1 VectorClock) (vc2 VectorClock))
(=> (vc_lt vc1 vc2) (not (vc_lt vc2 vc1)))
))

(assert (forall ((vc1 VectorClock) (vc2 VectorClock) (vc3 VectorClock))
(=> (and (vc_lt vc1 vc2) (vc_lt vc2 vc3)) (vc_lt vc1 vc3))
))

(define-fun vc_gt ((vc1 VectorClock) (vc2 VectorClock)) Bool
(vc_lt vc2 vc1))

(define-fun vc_ge ((vc1 VectorClock) (vc2 VectorClock)) Bool
(not (vc_lt vc1 vc2)))

(define-fun vc_le ((vc1 VectorClock) (vc2 VectorClock)) Bool
(not (vc_gt vc1 vc2)))
