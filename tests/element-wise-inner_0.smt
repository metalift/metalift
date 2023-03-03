; tuple definitions

(declare-datatypes ((Tuple1 1)) ((par (T0)             ((tuple1 (tuple1_get0 T0))))))
(declare-datatypes ((Tuple2 2)) ((par (T0 T1)          ((tuple2 (tuple2_get0 T0) (tuple2_get1 T1))))))
(declare-datatypes ((Tuple3 3)) ((par (T0 T1 T2)       ((tuple3 (tuple3_get0 T0) (tuple3_get1 T1) (tuple3_get2 T2))))))
(declare-datatypes ((Tuple4 4)) ((par (T0 T1 T2 T3)    ((tuple4 (tuple4_get0 T0) (tuple4_get1 T1) (tuple4_get2 T2) (tuple4_get3 T3))))))
(declare-datatypes ((Tuple5 5)) ((par (T0 T1 T2 T3 T4) ((tuple5 (tuple5_get0 T0) (tuple5_get1 T1) (tuple5_get2 T2) (tuple5_get3 T3) (tuple5_get4 T4))))))

; list definitions
(declare-datatypes ((MLList 1))
                   ((par (T) ((cons (head T) (tail (MLList T))) (nil)))))

(define-sort List_T1 () Int)


;(define-fun-rec list_length ((l (MLList List_T1))) Int
  ;(ite (= l nil) 0 (+ 1 (list_length (tail l))))
;)
(declare-fun list_length ( (MLList List_T1) ) Int)

(assert (= (list_length (as nil (MLList List_T1))) 0))
(assert (forall ( (val List_T1) (l (MLList List_T1)) )
                (= (list_length (cons val l)) (+ 1 (list_length l)))))
(assert (forall ( (l (MLList List_T1)) )
                (<= 0 (list_length l))))


(define-fun list_prepend ( (val List_T1) (l (MLList List_T1)) ) (MLList List_T1) (cons val l))


(declare-fun list_append ( (MLList List_T1) List_T1 ) (MLList List_T1))

(assert (forall ( (val List_T1) )
                (= (list_append (as nil (MLList List_T1)) val) (cons val (as nil (MLList List_T1))))))
(assert (forall ( (h List_T1) (t (MLList List_T1)) (val List_T1) )
                (= (list_append (cons h t) val) (cons h (list_append t val)))))


(declare-fun list_get_helper ( (MLList List_T1) Int ) List_T1)
(define-fun list_get ( (l (MLList List_T1)) (i Int) ) List_T1 (list_get_helper l i))

(assert (forall ( (h List_T1) (t (MLList List_T1)) (i Int) )
                (ite (<= i 0)
                     (= (list_get_helper (cons h t) i) h)
                     (= (list_get_helper (cons h t) i) (list_get_helper t (- i 1))))))


(define-fun list_empty ( ) (MLList List_T1) (as nil (MLList List_T1)))


(define-fun-rec list_tail ((l (MLList List_T1) ) (n Int)) (MLList List_T1)
  (ite (<= n 0)  l (list_tail (tail l) (- n 1))))


(assert (forall ( (start Int) (h List_T1) (t (MLList List_T1)) )
                (ite (<= start 0)
                     (= (list_tail (cons h t) start) (cons h t))
                     (= (list_tail (cons h t) start) (list_tail t (- start 1))))))
(assert (forall ( (start Int) )
                (= (list_tail (as nil (MLList List_T1)) start) (as nil (MLList List_T1)))))
(assert (forall ( (start Int) (l (MLList List_T1)) )
                (=> (>= start (list_length l))
                    (= (list_tail l start) (as nil (MLList List_T1))))))


(declare-fun list_take ( (MLList List_T1) Int ) (MLList List_T1))

(assert (forall ( (end Int) (h List_T1) (t (MLList List_T1)) )
                (ite (<= end 0)
                     (= (list_take (cons h t) end) (as nil (MLList List_T1)))
                     (= (list_take (cons h t) end) (cons h (list_take t (- end 1)))))))
(assert (forall ( (end Int) )
                (= (list_take (as nil (MLList List_T1)) end) (as nil (MLList List_T1)))))
(assert (forall ( (end Int) (l (MLList List_T1)) )
                (=> (>= end (list_length l))
                    (= (list_take l end) l))))

(assert (forall ( (l (MLList List_T1)) ) (= (list_take l 0) (as nil (MLList List_T1)))))

;(declare-fun list_concat ( (MLList List_T1) (MLList List_T1) ) (MLList List_T1))
;(assert (forall ((xs (MLList List_T1)) (ys (MLList List_T1)) (x List_T1))
;            (ite (= (as nil (MLList List_T1)) xs)
;                 (= (list_concat xs ys) ys)
;                 (= (list_concat (cons x xs) ys) (cons x (list_concat xs ys))))))

(define-fun-rec list_concat ((xs (MLList List_T1)) (ys (MLList List_T1))) (MLList List_T1)
    (ite (= (as nil (MLList List_T1)) xs)
         ys
         (cons (head xs) (list_concat (tail xs) ys))))

(define-fun-rec list_contains ((l (MLList List_T1)) (val List_T1)) Bool
  (ite (= (list_length l) 0)
       false
       (ite (= (head l) val)
            true
            (list_contains (tail l) val))))

; list axioms

; l :: nil = l
(assert (forall ( (l (MLList List_T1)) )
                (= (list_concat l (as nil (MLList List_T1))) l)))


; l[i:] = l[i] : l[i+1:]
(assert (forall ( (l (MLList List_T1)) (i Int) (out (MLList List_T1)) )
                (=> (and (>= i 0) (< i (list_length l)))
                    (= (list_tail l i)
                       (cons (list_get l i) (list_tail l (+ i 1)))))))

; xs :: (y : ys) = (xs : y) :: ys
(assert (forall ( (xs (MLList List_T1)) (y List_T1) (ys (MLList List_T1)) )
                (= (list_concat xs (cons y ys))
                   (list_concat (list_append xs y) ys))))


; end of list definition

(define-fun-rec multiply ((arg1 (MLList Int)) (arg2 (MLList Int))) (MLList Int)
(ite (= (list_length arg1) 0) list_empty (list_prepend (* (list_get arg1 0) (list_get arg2 0)) (multiply (list_tail arg1 1) (list_tail arg2 1)))))


(define-fun-rec inv0 ((i3 (MLList Int)) (i4 Int) (arg (MLList Int)) (arg1 (MLList Int))) Bool
(and (= i3 (multiply (list_take arg i4) (list_take arg1 i4))) (and (<= i4 (list_length arg)) (>= i4 0))))



(define-fun-rec test ((i25 (MLList Int)) (arg (MLList Int)) (arg1 (MLList Int))) Bool
(= i25 (multiply arg arg1)))

(assert (forall ( (data  (MLList Int) ) (data2  (MLList Int) )  (index Int)  )
(=> (and (>= index 0) (< index (list_length data)) ) 
(= (multiply (list_take data index) (list_take data2 index)) (list_prepend (* (list_get data 0) (list_get data2 0)) (multiply (list_tail data index) (list_tail data2 index))  )))))

(declare-const test_bb21 Bool)
(declare-const test_i22 Int)
(declare-const test_i25 (MLList Int))
(declare-const test_bb26 Bool)
(declare-const test_bb11 Bool)
(declare-const test_bb24 Bool)
(declare-const test_i12 (MLList Int))
(declare-const test_i13 (MLList Int))
(declare-const test_i14 Int)
(declare-const test_i15 Int)
(declare-const test_arg (MLList Int))
(declare-const test_i5 (MLList Int))
(declare-const test_bb Bool)
(declare-const test_i3_0 (MLList Int))
(declare-const test_i4_1 Int)
(declare-const test_i10 Bool)
(declare-const test_i7 Int)
(declare-const test_i8 (MLList Int))
(declare-const test_i9 Int)
(declare-const test_bb27 Bool)
(declare-const test_bb6 Bool)
(declare-const test_arg1 (MLList Int))
(declare-const test_i16 (MLList Int))
(declare-const test_i17 Int)
(declare-const test_i18 Int)
(declare-const test_i20 (MLList Int))



(assert (not (=> (and (= test_bb (=> (= test_i5 list_empty) (and test_bb6 (inv0 list_empty 0 test_arg test_arg1)))) (= test_bb11 (=> (and (and (= test_i12 test_i3_0) (= test_i13 test_arg) (= test_i14 test_i4_1) (= test_i15 (list_get test_arg test_i4_1)) (= test_i16 test_arg1) (= test_i17 test_i4_1) (= test_i18 (list_get test_arg1 test_i4_1)) (= test_i20 (list_append test_i3_0 (* (list_get test_arg test_i4_1) (list_get test_arg1 test_i4_1))))) (and (inv0 test_i3_0 test_i4_1 test_arg test_arg1) (< test_i4_1 (list_length test_arg)))) test_bb21)) (= test_bb21 (=> (and (= test_i22 test_i4_1) (and (inv0 test_i3_0 test_i4_1 test_arg test_arg1) (< test_i4_1 (list_length test_arg)))) (inv0 (list_append test_i3_0 (* (list_get test_arg test_i4_1) (list_get test_arg1 test_i4_1))) (+ test_i4_1 1) test_arg test_arg1))) (= test_bb24 (=> (and (= test_i25 test_i3_0) (and (inv0 test_i3_0 test_i4_1 test_arg test_arg1) (not (< test_i4_1 (list_length test_arg))))) (test test_i3_0 test_arg test_arg1))) (= test_bb26 (=> (and (inv0 test_i3_0 test_i4_1 test_arg test_arg1) (< test_i4_1 (list_length test_arg))) test_bb11)) (= test_bb27 (=> (and (inv0 test_i3_0 test_i4_1 test_arg test_arg1) (not (< test_i4_1 (list_length test_arg)))) test_bb24)) (= test_bb6 (=> (and (and (= test_i10 (< test_i4_1 (list_length test_arg))) (= test_i7 test_i4_1) (= test_i8 test_arg) (= test_i9 (list_length test_arg))) (inv0 test_i3_0 test_i4_1 test_arg test_arg1)) (and test_bb27 test_bb26)))) test_bb)))

(check-sat)
(get-model)