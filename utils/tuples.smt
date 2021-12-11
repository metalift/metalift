; tuple definitions

(declare-datatypes ((Tuple2 2)) ((par (T0 T1)          ((tuple2 (tupleGet0 T0) (tupleGet1 T1))))))
(declare-datatypes ((Tuple3 3)) ((par (T0 T1 T2)       ((tuple3 (tupleGet0 T0) (tupleGet1 T1) (tupleGet2 T2))))))
(declare-datatypes ((Tuple4 4)) ((par (T0 T1 T2 T3)    ((tuple4 (tupleGet0 T0) (tupleGet1 T1) (tupleGet2 T2) (tupleGet3 T3))))))
(declare-datatypes ((Tuple5 5)) ((par (T0 T1 T2 T3 T4) ((tuple5 (tupleGet0 T0) (tupleGet1 T1) (tupleGet2 T2) (tupleGet3 T3) (tupleGet4 T4))))))

