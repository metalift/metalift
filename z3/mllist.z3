; list operations

(declare-datatypes ((MLList 1)) 
                   ((par (T) ((cons (head T) (tail (MLList T))) (nil)))))

(define-sort T1 () Int)

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
(define-fun list_get ( (l (MLList T1)) (i Int) ) T1 (list_get_helper l i)); (- (- (list_length l) 1) i)))

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

(declare-fun list_concat ( (MLList T1) (MLList T1) ) (MLList T1))
(assert (forall ((xs (MLList T1)) (ys (MLList T1)))
            (ite (= (as nil (MLList T1)) xs)
                 (= (list_concat xs ys) ys)
                 ;(= (list_concat xs ys) (list_prepend (list_get xs 0) (list_concat (list_tail xs 1) ys))))))
                 (= (list_concat xs ys) ys))))

(define-fun list_equal ( (l1 (MLList T1)) (l2 (MLList T1)) ) Bool (= l1 l2))

(assert (forall ( (l (MLList T1)) )
                (list_equal (list_take l 0) list_empty)))


; additional axioms

(assert (forall ( (i Int) (l (MLList T1)) )
                (=> (and (>= i 0) (< i (list_length l)))
                    (= (list_take l (+ i 1)) (list_append (list_take l i) (list_get l i))))))

;(assert (forall ( (l (MLList T1)) )
;                (= (list_prepend (list_get l 0) (list_tail l 1)) l)))

