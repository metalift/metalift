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




(declare-const tmp1_0 (MLList Int))
(declare-const bb Bool)
(declare-const bb6 Bool)
(declare-const arg (MLList Int))
(declare-const tmp5 (MLList Int))
(declare-const tmp2_1 Int)
(declare-const tmp7 Int)
(declare-const tmp8 (MLList Int))
(declare-const tmp10 Bool)
(declare-const tmp9 Int)
(declare-const tmp30 (MLList Int))
(declare-const tmp31 Int)
(declare-const tmp32 Bool)
(declare-const bb48 Bool)
(declare-const bb33 Bool)
(declare-const tmp34 (MLList Int))
(declare-const tmp36 Int)
(declare-const tmp35 Int)
(declare-const tmp37 Bool)
(declare-const bb44 Bool)
(declare-const bb38 Bool)
(declare-const tmp43 (MLList Int))
(declare-const tmp42 Int)
(declare-const tmp40 (MLList Int))
(declare-const tmp39 (MLList Int))
(declare-const tmp41 Int)
(declare-const bb45 Bool)
(declare-const tmp46 Int)
(declare-const tmp49 (MLList Int))
(declare-const bb11 Bool)
(declare-const tmp12 (MLList Int))
(declare-const tmp14 Int)
(declare-const tmp13 Int)
(declare-const tmp15 Bool)
(declare-const bb22 Bool)
(declare-const bb16 Bool)
(declare-const tmp17 (MLList Int))
(declare-const bb26 Bool)
(declare-const tmp19 Int)
(declare-const tmp18 (MLList Int))
(declare-const tmp20 Int)
(declare-const tmp21 (MLList Int))
(declare-const bb23 Bool)
(declare-const tmp24 Int)
(declare-const tmp27 (MLList Int))
(declare-const bb28 Bool)
(declare-const tmp3_2 (MLList Int))
(declare-const tmp4_3 Int)
(declare-const tmp29 Int)



(assert (not (=> (and 

(= bb (=> (= tmp5 list_empty) (and bb6 (inv1 list_empty 0 arg)))) 

(= bb6 (=> (and (and (= tmp7 tmp2_1) (= tmp8 arg) (= tmp10 (< tmp2_1 (list_length arg))) (= tmp9 (list_length arg))) (inv1 tmp1_0 tmp2_1 arg)) (and bb26 bb11))) 

(= bb11 (=> (and (and (= tmp12 arg) (= tmp14 (list_get arg tmp2_1)) (= tmp13 tmp2_1) (= tmp15 (< 2 (list_get arg tmp2_1)))) (and (inv1 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg)))) (and bb22 bb16))) 

(= bb16 (=> (and (and (= tmp17 tmp1_0) (= tmp19 tmp2_1) (= tmp18 arg) (= tmp20 (list_get arg tmp2_1)) (= tmp21 (list_append tmp1_0 (list_get arg tmp2_1)))) (and (inv1 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg)) (< 2 (list_get arg tmp2_1)))) bb22)) 

(= bb22 (=> (and (or (and (inv1 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg))) (and (inv1 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg)) (< 2 (list_get arg tmp2_1)))) (not (< 2 (list_get arg tmp2_1)))) bb23)) 

(= bb23 (=> (and (= tmp24 tmp2_1) (and (or (and (inv1 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg))) (and (inv1 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg)) (< 2 (list_get arg tmp2_1)))) (not (< 2 (list_get arg tmp2_1))))) (inv1 (ite (and (inv1 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg)) (< 2 (list_get arg tmp2_1))) (list_append tmp1_0 (list_get arg tmp2_1)) tmp1_0) (+ tmp2_1 1) arg))) 

(= bb26 (=> (and (= tmp27 list_empty) (and (inv1 tmp1_0 tmp2_1 arg) (not (< tmp2_1 (list_length arg))))) (and bb28 (inv0 list_empty 0 arg)))) 

(= bb28 (=> (and (and (= tmp29 tmp4_3) (= tmp30 tmp1_0) (= tmp31 (list_length tmp1_0)) (= tmp32 (< tmp4_3 (list_length tmp1_0)))) (and (inv1 tmp1_0 tmp2_1 arg) (not (< tmp2_1 (list_length arg))) (inv0 tmp3_2 tmp4_3 arg))) (and bb48 bb33))) 

(= bb33 (=> (and (and (= tmp34 tmp1_0) (= tmp36 (list_get tmp1_0 tmp4_3)) (= tmp35 tmp4_3) (= tmp37 (< (list_get tmp1_0 tmp4_3) 10))) (and (inv1 tmp1_0 tmp2_1 arg) (not (< tmp2_1 (list_length arg))) (inv0 tmp3_2 tmp4_3 arg) (< tmp4_3 (list_length tmp1_0)))) (and bb44 bb38))) 

(= bb38 (=> (and (and (= tmp43 (list_append tmp3_2 (list_get tmp1_0 tmp4_3))) (= tmp42 (list_get tmp1_0 tmp4_3)) (= tmp40 tmp1_0) (= tmp39 tmp3_2) (= tmp41 tmp4_3)) (and (inv1 tmp1_0 tmp2_1 arg) (not (< tmp2_1 (list_length arg))) (inv0 tmp3_2 tmp4_3 arg) (< tmp4_3 (list_length tmp1_0)) (< (list_get tmp1_0 tmp4_3) 10))) bb44)) 

(= bb44 (=> (and (or (and (inv1 tmp1_0 tmp2_1 arg) (not (< tmp2_1 (list_length arg))) (inv0 tmp3_2 tmp4_3 arg) (< tmp4_3 (list_length tmp1_0))) (and (inv1 tmp1_0 tmp2_1 arg) (not (< tmp2_1 (list_length arg))) (inv0 tmp3_2 tmp4_3 arg) (< tmp4_3 (list_length tmp1_0)) (< (list_get tmp1_0 tmp4_3) 10))) (not (< (list_get tmp1_0 tmp4_3) 10))) bb45)) 

(= bb45 (=> (and (= tmp46 tmp4_3) (and (or (and (inv1 tmp1_0 tmp2_1 arg) (not (< tmp2_1 (list_length arg))) (inv0 tmp3_2 tmp4_3 arg) (< tmp4_3 (list_length tmp1_0))) (and (inv1 tmp1_0 tmp2_1 arg) (not (< tmp2_1 (list_length arg))) (inv0 tmp3_2 tmp4_3 arg) (< tmp4_3 (list_length tmp1_0)) (< (list_get tmp1_0 tmp4_3) 10))) (not (< (list_get tmp1_0 tmp4_3) 10)))) (inv0 (ite (and (inv1 tmp1_0 tmp2_1 arg) (not (< tmp2_1 (list_length arg))) (inv0 tmp3_2 tmp4_3 arg) (< tmp4_3 (list_length tmp1_0)) (< (list_get tmp1_0 tmp4_3) 10)) (list_append tmp3_2 (list_get tmp1_0 tmp4_3)) tmp3_2) (+ tmp4_3 1) arg))) 

(= bb48 (=> (and (= tmp49 tmp3_2) (and (inv1 tmp1_0 tmp2_1 arg) (not (< tmp2_1 (list_length arg))) (inv0 tmp3_2 tmp4_3 arg) (not (< tmp4_3 (list_length tmp1_0))))) (ps tmp3_2 arg)))

) bb)))

(check-sat)
(get-model)
