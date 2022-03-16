(define-sort VectorClock () (Tuple3 Int Int Int))
(define-fun vector_clock_bottom () VectorClock
(tuple3 0 0 0))

(define-fun vc_lt ( (vc1 VectorClock) (vc2 VectorClock) ) Bool
(and
  (<= (tuple3_get0 vc1) (tuple3_get0 vc2))
  (<= (tuple3_get1 vc1) (tuple3_get1 vc2))
  (<= (tuple3_get2 vc1) (tuple3_get2 vc2))
  (or
    (< (tuple3_get0 vc1) (tuple3_get0 vc2))
    (< (tuple3_get1 vc1) (tuple3_get1 vc2))
    (< (tuple3_get2 vc1) (tuple3_get2 vc2))
  )
))

(define-fun vc_gt ((vc1 VectorClock) (vc2 VectorClock)) Bool
(vc_lt vc2 vc1))

(define-fun vc_ge ((vc1 VectorClock) (vc2 VectorClock)) Bool
(not (vc_lt vc1 vc2)))

(define-fun vc_le ((vc1 VectorClock) (vc2 VectorClock)) Bool
(not (vc_gt vc1 vc2)))

(define-fun max ((a Int) (b Int)) Int
(ite (> a b) a b))

(define-fun vector_clock_merge ( (vc1 VectorClock) (vc2 VectorClock) ) VectorClock
(tuple3
  (max (tuple3_get0 vc1) (tuple3_get0 vc2))
  (max (tuple3_get1 vc1) (tuple3_get1 vc2))
  (max (tuple3_get2 vc1) (tuple3_get2 vc2))
))

(assert (vc_lt vector_clock_bottom (tuple2_get0 (tuple2_get0 arg_for_state_transition))))
(assert (vc_lt vector_clock_bottom test_next_state_state_transition_arg2))
(assert (vc_lt vector_clock_bottom init_op_arg_1))
(assert (vc_lt vector_clock_bottom (tuple2_get0 (tuple2_get0 synth_init_state))))
(assert (vc_lt vector_clock_bottom state_transition_arg_1))
(assert (vc_lt vector_clock_bottom (tuple2_get0 (tuple2_get0 i11_for_state_transition))))
(assert (vc_lt vector_clock_bottom (tuple2_get0 (tuple2_get0 arg_for_query))))
