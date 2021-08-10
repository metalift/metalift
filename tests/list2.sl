; list definitions
(declare-datatypes ((MLList 1))
                   ((par (T) ((cons (head T) (tail (MLList T))) (nil)))))

(define-sort T1 () Int)


;(define-fun-rec list_length ((l (MLList T1))) Int
  ;(ite (= l nil) 0 (+ 1 (list_length (tail l))))
;)

(define-fun-rec list_length ((l (MLList T1))) Int
  (ite (= l (as nil (MLList T1))) 0 (+ 1 (list_length (tail l))))
)


(define-fun list_prepend ( (val T1) (l (MLList T1)) ) (MLList T1) (cons val l))


(define-fun-rec list_append ( (l (MLList T1)) (n Int)) (MLList T1)

  (ite ( = l (as nil (MLList T1))) (cons n l) (cons (head l) (list_append (tail l) n)))

)


(define-fun-rec list_get((l (MLList T1)) (i Int)) Int
  (ite (<= i 0) (head l) (list_get (tail l) (- i 1)))
)


(define-fun list_empty ( ) (MLList T1) (as nil (MLList T1)))


(define-fun-rec list_tail ((l (MLList T1) ) (n Int)) (MLList T1)
  (ite (<= n 0)  l (list_tail (tail l) (- n 1))))



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

; end of list definition



(define-fun-rec select_p0 ( (n Int) ) Bool 
    (> n 2))

(define-fun-rec select_p1 ( (n Int) ) Bool 
    (< n 10))
; Select_select_p1
(define-fun-rec Select_select_p1 ( (data (MLList Int)) ) (MLList Int)
(ite (= (list_length data) 0) list_empty
     (ite (select_p1 (list_get data 0))
          (list_concat (cons (list_get data 0) (as nil (MLList Int))) (Select_select_p1 (list_tail data 1)))
          (Select_select_p1 (list_tail data 1)))))


; Select_select_p0
(define-fun-rec Select_select_p0 ( (data (MLList Int)) ) (MLList Int)
(ite (= (list_length data) 0) list_empty
     (ite (select_p0 (list_get data 0))
          (list_concat (cons (list_get data 0) (as nil (MLList Int))) (Select_select_p0 (list_tail data 1)))
          (Select_select_p0 (list_tail data 1)))))

; select_combined
(define-fun-rec select_combined ( (n Int) ) Bool 
    (and (> n 2) (< n 10)))

; Select_combined
(define-fun-rec Select_combined ( (data (MLList Int)) ) (MLList Int)
    (ite (= (list_length data) 0) list_empty
     (ite (select_combined (list_get data 0))
          (list_concat (cons (list_get data 0) (as nil (MLList Int))) (Select_combined (list_tail data 1)))
          (Select_combined (list_tail data 1)))))

(synth-fun inv0 ((out (MLList Int)) (i Int) (l (MLList Int))) Bool 
  ;(and (>= i 0) (<= i (list_length l)) (= (list_concat out (list_tail l i)) l))

    ((A Bool) (B Bool) (C Bool) ( D Bool) (E Int) (F (MLList Int)) (I Int) )
    ((A Bool ((and B C D)))
    (B Bool ((>= E I) (<= E I) (> E I) (< E I) (= E I)))
    (C Bool ((>= E (list_length F)) (<= E (list_length F)) (> E (list_length F)) (<= E (list_length F)) (= E (list_length F))))
    (D Bool ((= (list_concat F (list_tail F E)) F) (= (list_concat F (Select_select_p0 (list_tail F E))) F) (= (list_concat F (Select_select_p1 (list_tail F E))) F)))
    (E Int (i))
    (F (MLList Int) (out l (Select_select_p0 l) (Select_select_p1 l) (Select_combined l)))
    (I Int (0 1))))

(synth-fun ps ((out (MLList Int)) (l (MLList Int))) Bool 
  ;(= out l)
  ((A Bool) (B (MLList Int)) (C (MLList Int)))
  ((A Bool ((= B C)))
  (B (MLList Int) (out))
  (C (MLList Int) (l (Select_select_p0 l) (Select_select_p1 l) (Select_combined l) ))))





(declare-const tmp10 (MLList Int))
(declare-const tmp13 Bool)
(declare-const tmp12 Int)
(declare-const tmp11 Int)
(declare-const bb20 Bool)
(declare-const bb14 Bool)
(declare-const tmp15 (MLList Int))
(declare-const tmp3 (MLList Int))
(declare-const bb9 Bool)
(declare-const tmp17 Int)
(declare-const tmp1_0 (MLList Int))
(declare-const bb Bool)
(declare-const arg (MLList Int))
(declare-const bb4 Bool)
(declare-const tmp2_1 Int)
(declare-const tmp5 Int)
(declare-const tmp7 Int)
(declare-const tmp6 (MLList Int))
(declare-const tmp8 Bool)
(declare-const bb24 Bool)
(declare-const tmp19 (MLList Int))
(declare-const tmp16 (MLList Int))
(declare-const tmp18 Int)
(declare-const bb21 Bool)
(declare-const tmp22 Int)
(declare-const tmp25 (MLList Int))



(constraint (=> (and 
(= bb (=> (= tmp3 list_empty) (and bb4 (inv0 list_empty 0 arg)))) 

(= bb4 (=> (and (and (= tmp5 tmp2_1) (= tmp7 (list_length arg)) (= tmp6 arg) (= tmp8 (< tmp2_1 (list_length arg)))) (inv0 tmp1_0 tmp2_1 arg)) (and bb24 bb9))) 

(= bb9 (=> (and (and (= tmp10 arg) (= tmp13 (< 2 (list_get arg tmp2_1))) (= tmp12 (list_get arg tmp2_1)) (= tmp11 tmp2_1)) (and (inv0 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg)))) (and bb20 bb14))) 

(= bb14 (=> (and (and (= tmp15 tmp1_0) (= tmp17 tmp2_1) (= tmp19 (list_append tmp1_0 (list_get arg tmp2_1))) (= tmp16 arg) (= tmp18 (list_get arg tmp2_1))) (and (inv0 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg)) (< 2 (list_get arg tmp2_1)))) bb20)) 

(= bb20 (=> (and (or (and (inv0 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg))) (and (inv0 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg)) (< 2 (list_get arg tmp2_1)))) (not (< 2 (list_get arg tmp2_1)))) bb21)) 

(= bb21 (=> (and (= tmp22 tmp2_1) (and (or (and (inv0 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg))) (and (inv0 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg)) (< 2 (list_get arg tmp2_1)))) (not (< 2 (list_get arg tmp2_1))))) (inv0 (ite (and (inv0 tmp1_0 tmp2_1 arg) (< tmp2_1 (list_length arg)) (< 2 (list_get arg tmp2_1))) (list_append tmp1_0 (list_get arg tmp2_1)) tmp1_0) (+ tmp2_1 1) arg))) 

(= bb24 (=> (and (= tmp25 tmp1_0) (and (inv0 tmp1_0 tmp2_1 arg) (not (< tmp2_1 (list_length arg))))) (ps tmp1_0 arg)))

) bb))

(check-synth)

