; post condition that sets output to be one select, but requires an axiom that states
; that two selects can be composed

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

; i < len(l) --> l[i] : tail(l, i+1) == tail(l, i)
(assert (forall ( (i Int) (l (MLList Int)) )
                (=> (< i (list_length l))
                  (= (cons (list_get l i) (list_tail l (+ i 1)))
                    (list_tail l i)))))

; end of list definitions


(define-funs-rec
(
(ps ( (out (MLList Int)) (l (MLList Int)) ) Bool)

; inv1 - first loop
(inv1 ( (out (MLList Int)) (i Int) (l (MLList Int)) ) Bool)
(select_p1 ( (n Int) ) Bool)
(Select_select_p1 ( (data (MLList Int)) ) (MLList Int))

; inv0 - second loop
(inv0 ( (out (MLList Int)) (i Int) (l (MLList Int)) ) Bool)
(select_p0 ( (n Int) ) Bool)
(Select_select_p0 ( (data (MLList Int)) ) (MLList Int))

(select_combined ( (n Int) ) Bool)
(Select_combined ( (data (MLList Int)) ) (MLList Int))

)
(
; ps
;(= out (Select_select_p0 (Select_select_p1 l)))
(= out (Select_combined l))

; inv1
(and (>= i 0) (<= i (list_length l)) (= (list_concat out (Select_select_p1 (list_tail l i))) (Select_select_p1 l)))

; select_p1
(> n 2)

; Select_select_p1
(ite (= (list_length data) 0) list_empty
     (ite (select_p1 (list_get data 0))
          (list_concat (cons (list_get data 0) (as nil (MLList Int))) (Select_select_p1 (list_tail data 1)))
          (Select_select_p1 (list_tail data 1))))

; inv0 - second loop
(and (>= i 0) (<= i (list_length (Select_select_p1 l)))
     (= (list_concat out (Select_select_p0 (list_tail (Select_select_p1 l) i)))
        ;(Select_select_p0   (Select_select_p1 l))))
        (Select_combined l)))


; select_p0
(< n 10)

; Select_select_p0
(ite (= (list_length data) 0) list_empty
     (ite (select_p0 (list_get data 0))
          (list_concat (cons (list_get data 0) (as nil (MLList Int))) (Select_select_p0 (list_tail data 1)))
          (Select_select_p0 (list_tail data 1))))

; select_combined
(and (> n 2) (< n 10))

; Select_combined
(ite (= (list_length data) 0) list_empty
     (ite (select_combined (list_get data 0))
          (list_concat (cons (list_get data 0) (as nil (MLList Int))) (Select_combined (list_tail data 1)))
          (Select_combined (list_tail data 1))))

))

; selects can be composed
(assert (forall ( (l (MLList Int)) )
  (= (Select_select_p0 (Select_select_p1 l)) (Select_combined l))))
