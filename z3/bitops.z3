; bitwise operators

(declare-fun bitwise-and ( (Int) (Int) ) Int)
(declare-fun bitwise-ior ( (Int) (Int) ) Int)
(declare-fun bitwise-not ( (Int) ) Int)

; first argument is the input, second is the amount to shift
(declare-fun lshl ( (Int) (Int) ) Int)
(declare-fun lshr ( (Int) (Int) ) Int)
