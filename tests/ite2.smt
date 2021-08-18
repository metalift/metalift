(define-fun ps ((tmp12 Int) (arg Int)) Bool 
(and (=> (= arg 1) (= tmp12 10)) 
     (=> (= arg 2) (= tmp12 20)) 
     (=> (= arg 3) (= tmp12 30))
     (=> (not (or (= arg 1) (= arg 2) (= arg 3))) (= tmp12 40))
))


(declare-const NodeBlock3 Bool)
(declare-const bb Bool)
(declare-const arg Int)
(declare-const Pivot4 Bool)
(declare-const tmp6 Int)
(declare-const NodeBlock Bool)
(declare-const LeafBlock Bool)
(declare-const Pivot Bool)
(declare-const LeafBlock1 Bool)
(declare-const bb8 Bool)
(declare-const SwitchLeaf2 Bool)
(declare-const NewDefault Bool)
(declare-const bb9 Bool)
(declare-const SwitchLeaf Bool)
(declare-const bb7 Bool)
(declare-const bb11 Bool)
(declare-const bb10 Bool)
(declare-const tmp12 Int)



(assert (not (=> (and (= bb (=> (= tmp6 arg) NodeBlock3)) (= NodeBlock3 (=> (= Pivot4 (< arg 2)) (and NodeBlock LeafBlock))) (= NodeBlock (=> (and (= Pivot (< arg 3)) (not (< arg 2))) (and LeafBlock1 bb8))) (= LeafBlock1 (=> (and (= SwitchLeaf2 (= 3 arg)) (and (not (< arg 2)) (not (< arg 3)))) (and NewDefault bb9))) (= LeafBlock (=> (and (= SwitchLeaf (= 1 arg)) (< arg 2)) (and NewDefault bb7))) (= bb7 (=> (and (< arg 2) (= 1 arg)) bb11)) (= bb8 (=> (and (not (< arg 2)) (< arg 3)) bb11)) (= bb9 (=> (and (not (< arg 2)) (not (< arg 3)) (= 3 arg)) bb11)) (= NewDefault (=> (and (or (and (not (< arg 2)) (not (< arg 3))) (< arg 2)) (not (= 1 arg)) (not (= 3 arg))) bb10)) (= bb10 (=> (and (or (and (not (< arg 2)) (not (< arg 3))) (< arg 2)) (not (= 1 arg)) (not (= 3 arg))) bb11)) (= bb11 (=> (and (= tmp12 (ite (and (or (and (not (< arg 2)) (not (< arg 3))) (< arg 2)) (not (= 1 arg)) (not (= 3 arg))) 40 (ite (and (not (< arg 2)) (not (< arg 3)) (= 3 arg)) 30 (ite (and (not (< arg 2)) (< arg 3)) 20 10)))) (or (and (< arg 2) (= 1 arg)) (and (not (< arg 2)) (< arg 3)) (and (not (< arg 2)) (not (< arg 3)) (= 3 arg)) (and (or (and (not (< arg 2)) (not (< arg 3))) (< arg 2)) (not (= 1 arg)) (not (= 3 arg))))) (ps tmp12 arg)))) bb)))

(check-sat)
(get-model)
