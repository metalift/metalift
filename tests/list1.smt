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


(declare-fun list_tail ( (MLList T1) Int ) (MLList T1))

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


(define-fun inv0 ((out (MLList Int)) (i Int) (l (MLList Int))) (Bool) 
  (and (>= i 0) (<= i (list_length l)) (= (list_concat out (list_tail l i)) l))
)

(define-fun ps ((out (MLList Int)) (l (MLList Int))) (Bool) 
  (= out l)
)




(declare-const bb9 Bool)
(declare-const tmp11 (MLList Int))
(declare-const tmp12 Int)
(declare-const tmp13 Int)
(declare-const tmp14 (MLList Int))
(declare-const tmp10 (MLList Int))
(declare-const bb15 Bool)
(declare-const tmp1_0 (MLList Int))
(declare-const arg (MLList Int))
(declare-const tmp3 (MLList Int))
(declare-const bb Bool)
(declare-const tmp2_1 Int)
(declare-const tmp5 Int)
(declare-const tmp6 (MLList Int))
(declare-const tmp8 Bool)
(declare-const tmp7 Int)
(declare-const bb18 Bool)
(declare-const bb4 Bool)
(declare-const tmp19 (MLList Int))
(declare-const tmp16 Int)



(assert (not (=> (and (= bb (=> (= tmp3 list_empty) (and bb4 (inv0 list_empty 0 arg)))) (= bb4 (=> (and (and (= tmp5 tmp2_1) (= tmp6 arg) (= tmp8 (< tmp2_1 (list_length arg))) (= tmp7 (list_length arg))) (inv0 tmp1_0 tmp2_1 arg)) (and bb18 bb9))) (= bb9 (=> (and (and (= tmp11 arg) (= tmp12 tmp2_1) (= tmp13 (list_get arg tmp2_1)) (= tmp14 (list_append tmp1_0 (list_get arg tmp2_1))) (= tmp10 tmp1_0)) (and (inv0 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg)))) bb15)) (= bb15 (=> (and (= tmp16 tmp2_1) (and (inv0 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg)))) (inv0 (list_append tmp1_0 (list_get arg tmp2_1)) (+ tmp2_1 1) arg))) (= bb18 (=> (and (= tmp19 tmp1_0) (and (inv0 tmp1_0 tmp2_1 arg) (not (< tmp2_1 (list_length arg))))) (ps tmp1_0 arg)))) bb)))

(check-sat)
(get-model)