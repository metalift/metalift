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

; map definitions
(declare-datatypes ((Map 2)) ((par (K V) ((make_map (map_internal_keys (Set K)) (map_internal_array (Array K V)))))))
;(define-sort Map (K V) (make_map (Set K) (Array K V)))

(define-sort K_Map () Int)
(define-sort V_Map () Int)

(define-fun map_create ( ) (Map K_Map V_Map)
  (make_map (as set.empty (Set K_Map)) ((as const (Array K_Map V_Map)) 0)))

(define-fun map_contains ( (m (Map K_Map V_Map)) (K_Map K_Map) ) Bool
  (set.member K_Map (map_internal_keys m)))

(declare-fun map_values ( (Map K_Map V_Map) ) (MLList V_Map))
(assert (forall ( (m (Map K_Map V_Map)) )
  (= (set.card (map_internal_keys m)) (list_length (map_values m)))))
(assert (forall ( (m (Map K_Map V_Map)) (K_Map K_Map) )
  (=> (set.member K_Map (map_internal_keys m)) (list_contains (map_values m) (select (map_internal_array m) K_Map)))))

(define-fun map_get ( (m (Map K_Map V_Map)) (K_Map K_Map) (d V_Map) ) V_Map (ite
  (set.member K_Map (map_internal_keys m))
  (select (map_internal_array m) K_Map)
  d
))

(define-fun map_get_direct ( (m (Map K_Map V_Map)) (K_Map K_Map) (d V_Map) ) V_Map (select (map_internal_array m) K_Map))
(define-fun-rec reduce_sum ((x (MLList Int))) Int
(ite (< (list_length x) 1) 0 (+ (list_get x 0) (reduce_sum (list_tail x 1)))))


(define-fun-rec softmax_part3_inv0 ((i Int) (max_pos Int) (output (MLList Int)) (sum Int)) Bool
(and (and (>= i 0) (<= i max_pos)) (= sum (reduce_sum (list_take output i)))))



(define-fun-rec softmax_part3_ps ((output (MLList Int)) (max_pos Int) (softmax_part3_rv Int)) Bool
(= softmax_part3_rv (reduce_sum (list_take output max_pos))))

(declare-const sum Int)
(declare-const i Int)
(declare-const max_pos Int)
(declare-const softmax_part3_rv Int)
(declare-const output (MLList Int))



(assert (not (and (and (=> (and (and (> (list_length output) 0) (<= max_pos (list_length output))) (>= max_pos 1)) (softmax_part3_inv0 0 max_pos output 0)) (=> (and (and (and (and (< i max_pos) (> (list_length output) 0)) (<= max_pos (list_length output))) (>= max_pos 1)) (softmax_part3_inv0 i max_pos output sum)) (softmax_part3_inv0 (+ i 1) max_pos output (+ sum (list_get output i))))) (=> (and (and (and (and (not (< i max_pos)) (> (list_length output) 0)) (<= max_pos (list_length output))) (>= max_pos 1)) (softmax_part3_inv0 i max_pos output sum)) (softmax_part3_ps output max_pos sum)))))

(check-sat)
(get-model)