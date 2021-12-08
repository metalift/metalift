; tuple definitions

(declare-datatypes ((Tuple2 2)) ((par (T1 T2) ((tuple2 (first T1) (second T2))))))
(declare-datatypes ((Tuple3 3)) ((par (T1 T2 T3) ((tuple2 (first T1) (second T2) (third T3))))))
(declare-datatypes ((Tuple4 4)) ((par (T1 T2 T3 T4) ((tuple2 (first T1) (second T2) (third T3) (fourth T4))))))

