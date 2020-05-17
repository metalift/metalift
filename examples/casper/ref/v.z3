; begin list axioms
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

(declare-fun list_concat ( (MLList T1) (MLList T1) ) (MLList T1))
(assert (forall ((xs (MLList T1)) (ys (MLList T1)))
            (ite (= (as nil (MLList T1)) xs)
                 (= (list_concat xs ys) ys)
                 (= (list_concat xs ys) ys))))

; end of list axioms


(define-funs-rec
(
(input_ps ( (i Int) (sum Int) (l (MLList Int)) (rv Int) ) Bool)
(inv_0 ( (i Int) (sum Int) (l (MLList Int)) ) Bool)
(lambda_mapper ( (n Int) ) Int)
(lambda_reducer ( (v1 Int) (v2 Int) ) Int)
(mapper_lambda_mapper ( (data (MLList Int)) ) (MLList Int))
(reducer_lambda_reducer ( (data (MLList Int)) (init Int) ) Int)
)
(
(and (= sum (reducer_lambda_reducer (mapper_lambda_mapper l) 0)) (= rv sum))
(and (>= i 0) (<= i (list_length l)) (= sum (reducer_lambda_reducer (mapper_lambda_mapper (list_take l i)) 0)))
(* n 2)
(+ v1 v2)
(ite (= (list_length data) 0) (as nil (MLList Int)) (list_concat (cons (lambda_mapper (list_get data 0)) (as nil (MLList Int))) (mapper_lambda_mapper (list_tail data 1))))
(ite (= (list_length data) 0) init (lambda_reducer (list_get data 0) (reducer_lambda_reducer (list_tail data 1) init)))
))

(assert (forall ( (data (MLList Int)) (index Int) (init Int))
                (=> (and (>= index 0) (< index (list_length data)))
                    (= (reducer_lambda_reducer (mapper_lambda_mapper (list_take data (+ index 1))) init)
                       (lambda_reducer (reducer_lambda_reducer (mapper_lambda_mapper (list_take data index)) init)
                                       (lambda_mapper (list_get data index)))))))


(declare-const sum_0 Int)
(declare-const l (MLList Int))
(declare-const i_1 Int)

(push)
(assert (not (inv_0 0 0 l)))
(check-sat)
(pop)


(push)
(assert (not (or (not (and (inv_0 i_1 sum_0 l) (< i_1 (list_length l)))) (inv_0 (+ i_1 1) (+ sum_0 (* (list_get l i_1) 2)) l))))
(check-sat)
(pop)


(push)
(assert (not (or (not (and (inv_0 i_1 sum_0 l) (not (< i_1 (list_length l))))) (input_ps i_1 sum_0 l sum_0))))
(check-sat)
(pop)



