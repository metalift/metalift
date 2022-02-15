; tuple definitions

(declare-datatypes ((Tuple2 2)) ((par (T0 T1)          ((tuple2 (tuple2_get0 T0) (tuple2_get1 T1))))))
(declare-datatypes ((Tuple3 3)) ((par (T0 T1 T2)       ((tuple3 (tuple3_get0 T0) (tuple3_get1 T1) (tuple3_get2 T2))))))
(declare-datatypes ((Tuple4 4)) ((par (T0 T1 T2 T3)    ((tuple4 (tuple4_get0 T0) (tuple4_get1 T1) (tuple4_get2 T2) (tuple4_get3 T3))))))
(declare-datatypes ((Tuple5 5)) ((par (T0 T1 T2 T3 T4) ((tuple5 (tuple5_get0 T0) (tuple5_get1 T1) (tuple5_get2 T2) (tuple5_get3 T3) (tuple5_get4 T4))))))

; list definitions
(declare-datatypes ((MLList 1))
                   ((par (T) ((cons (head T) (tail (MLList T))) (nil)))))

(define-sort T1 () Int)


;(define-fun-rec list_length ((l (MLList T1))) Int
  ;(ite (= l nil) 0 (+ 1 (list_length (tail l))))
;)
(declare-fun list_length ( (MLList T1) ) Int)

(assert (= (list_length (as nil (MLList T1))) 0))
(assert (forall ( (val T1) (l (MLList T1)) )
                (= (list_length (cons val l)) (+ 1 (list_length l)))))
(assert (forall ( (l (MLList T1)) )
                (<= 0 (list_length l))))


(define-fun list_prepend ( (val T1) (l (MLList T1)) ) (MLList T1) (cons val l))


(declare-fun list_append ( (MLList T1) T1 ) (MLList T1))

(assert (forall ( (val T1) )
                (= (list_append (as nil (MLList T1)) val) (cons val (as nil (MLList T1))))))
(assert (forall ( (h T1) (t (MLList T1)) (val T1) )
                (= (list_append (cons h t) val) (cons h (list_append t val)))))


(declare-fun list_get_helper ( (MLList T1) Int ) T1)
(define-fun list_get ( (l (MLList T1)) (i Int) ) T1 (list_get_helper l i))

(assert (forall ( (h T1) (t (MLList T1)) (i Int) )
                (ite (<= i 0)
                     (= (list_get_helper (cons h t) i) h)
                     (= (list_get_helper (cons h t) i) (list_get_helper t (- i 1))))))


(define-fun list_empty ( ) (MLList T1) (as nil (MLList T1)))


(define-fun-rec list_tail ((l (MLList T1) ) (n Int)) (MLList T1)
  (ite (<= n 0)  l (list_tail (tail l) (- n 1))))


(assert (forall ( (start Int) (h T1) (t (MLList T1)) )
                (ite (<= start 0)
                     (= (list_tail (cons h t) start) (cons h t))
                     (= (list_tail (cons h t) start) (list_tail t (- start 1))))))
(assert (forall ( (start Int) )
                (= (list_tail (as nil (MLList T1)) start) (as nil (MLList T1)))))
(assert (forall ( (start Int) (l (MLList T1)) )
                (=> (>= start (list_length l))
                    (= (list_tail l start) (as nil (MLList T1))))))


(declare-fun list_take ( (MLList T1) Int ) (MLList T1))

(assert (forall ( (end Int) (h T1) (t (MLList T1)) )
                (ite (<= end 0)
                     (= (list_take (cons h t) end) (as nil (MLList T1)))
                     (= (list_take (cons h t) end) (cons h (list_take t (- end 1)))))))
(assert (forall ( (end Int) )
                (= (list_take (as nil (MLList T1)) end) (as nil (MLList T1)))))
(assert (forall ( (end Int) (l (MLList T1)) )
                (=> (>= end (list_length l))
                    (= (list_take l end) l))))

(assert (forall ( (l (MLList Int)) ) (= (list_take l 0) (as nil (MLList Int)))))

;(declare-fun list_concat ( (MLList T1) (MLList T1) ) (MLList T1))
;(assert (forall ((xs (MLList T1)) (ys (MLList T1)) (x T1))
;            (ite (= (as nil (MLList T1)) xs)
;                 (= (list_concat xs ys) ys)
;                 (= (list_concat (cons x xs) ys) (cons x (list_concat xs ys))))))

(define-fun-rec list_concat ((xs (MLList Int)) (ys (MLList Int))) (MLList Int)
    (ite (= (as nil (MLList Int)) xs)
         ys
         (cons (head xs) (list_concat (tail xs) ys))))


; list axioms

; l :: nil = l
(assert (forall ( (l (MLList Int)) )
                (= (list_concat l (as nil (MLList Int))) l)))


; l[i:] = l[i] : l[i+1:]
(assert (forall ( (l (MLList Int)) (i Int) (out (MLList Int)) )
                (=> (and (>= i 0) (< i (list_length l)))
                    (= (list_tail l i)
                       (cons (list_get l i) (list_tail l (+ i 1)))))))

; xs :: (y : ys) = (xs : y) :: ys
(assert (forall ( (xs (MLList Int)) (y Int) (ys (MLList Int)) )
                (= (list_concat xs (cons y ys))
                   (list_concat (list_append xs y) ys))))


; end of list definition

(declare-fun uninterp ((Int) (Int)) Int)
(define-fun-rec test ((tmp9 Int) (arg Int) (arg1 Int)) Bool
(= tmp9 (+ (uninterp arg arg) (uninterp arg1 arg1))))

(declare-const test_tmp4 Int)
(declare-const test_tmp3 Int)
(declare-const test_tmp6 Int)
(declare-const test_arg Int)
(declare-const test_tmp8 Int)
(declare-const test_tmp7 Int)
(declare-const test_tmp5 Int)
(declare-const test_arg1 Int)
(declare-const test_bb Bool)



(assert (not (=> (and (= test_bb (=> (and (and (= test_tmp3 test_arg) (= test_tmp4 test_arg) (= test_tmp6 test_arg1) (= test_tmp8 (uninterp test_arg1 test_arg1)) (= test_tmp7 test_arg1) (= test_tmp5 (uninterp test_arg test_arg))) (and true true true)) (test (+ (uninterp test_arg test_arg) (uninterp test_arg1 test_arg1)) test_arg test_arg1)))) test_bb)))

(check-sat)
(get-model)