; begin integer functions

(define-fun-rec integer_exp ((n Int)) Int
(ite (<= n 0) 1 (mod (* (integer_exp (- n 1)) 3) 64)))

(define-fun-rec integer_sqrt_helper ((n Int) (guess Int)) Int
(ite (or (or (= guess 0) (= guess 1)) (> guess 64)) 1 (ite (= guess (div n guess)) guess (integer_sqrt_helper n (div (+ guess (div n guess)) 2)))))

(define-fun integer_sqrt ((n Int)) Int
(integer_sqrt_helper (div n 2) n))

; end integer functions
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

; list of lists definition

(declare-fun list_list_length ( (MLList (MLList Int) ) ) Int)
(assert (= (list_list_length (as nil (MLList (MLList Int) ))) 0))
(assert (forall ( (val (MLList Int) ) (l (MLList (MLList Int) )) )
                (= (list_list_length (cons val l)) (+ 1 (list_list_length l)))))
(assert (forall ( (l (MLList (MLList Int) )) )
                (<= 0 (list_list_length l))))

;end of list length

(define-fun list_list_prepend ( (val (MLList Int) ) (l (MLList (MLList Int) ) )) (MLList (MLList Int) ) (cons val l))
; end of list prepend


(declare-fun list_list_append ( (MLList (MLList Int)  ) (MLList Int) ) (MLList (MLList Int) ))
(assert (forall ( (val (MLList Int)) )
                (= (list_list_append (as nil (MLList (MLList Int))) val) (cons val (as nil (MLList (MLList Int)))))))
(assert (forall ( (h (MLList Int)) (t (MLList (MLList Int))) (val (MLList Int)) )
                (= (list_list_append (cons h t) val) (cons h (list_list_append t val)))))
;end of list append

(declare-fun list_list_get_helper ( (MLList (MLList Int) ) Int ) (MLList Int) )
(define-fun list_list_get ( (l (MLList (MLList Int) )) (i Int) ) (MLList Int) (list_list_get_helper l i))
(assert (forall ( (h (MLList Int) ) (t (MLList (MLList Int) )) (i Int) )
                (ite (<= i 0)
                     (= (list_list_get_helper (cons h t) i) h)
                     (= (list_list_get_helper (cons h t) i) (list_list_get_helper t (- i 1))))))
;end of list get

(define-fun list_list_empty ( ) (MLList (MLList Int)) (as nil (MLList (MLList Int) )))
;end of empty list



(define-fun-rec list_list_tail ((l (MLList (MLList Int) ) ) (n Int)) (MLList (MLList Int) )
  (ite (<= n 0)  l (list_list_tail (tail l) (- n 1))))
(assert (forall ( (start Int) (h (MLList Int) ) (t (MLList (MLList Int) )) )
                (ite (<= start 0)
                     (= (list_list_tail (cons h t) start) (cons h t))
                     (= (list_list_tail (cons h t) start) (list_list_tail t (- start 1))))))
(assert (forall ( (start Int) )
                (= (list_list_tail (as nil (MLList (MLList Int) )) start) (as nil (MLList (MLList Int)) ))))
(assert (forall ( (start Int) (l (MLList (MLList Int) )) )
                (=> (>= start (list_list_length l))
                    (= (list_list_tail l start) (as nil (MLList (MLList Int) ))))))

; end of list tail

(declare-fun list_list_take ( (MLList (MLList Int)) Int ) (MLList (MLList Int)))

(assert (forall ( (end Int) (h (MLList Int)) (t (MLList (MLList Int))) )
                (ite (<= end 0)
                     (= (list_list_take (cons h t) end) (as nil (MLList (MLList Int))))
                     (= (list_list_take (cons h t) end) (cons h (list_list_take t (- end 1)))))))
(assert (forall ( (end Int) )
                (= (list_list_take (as nil (MLList (MLList Int))) end) (as nil (MLList (MLList Int))))))
(assert (forall ( (end Int) (l (MLList (MLList Int))) )
                (=> (>= end (list_list_length l))
                    (= (list_list_take l end) l))))

(assert (forall ( (l (MLList (MLList Int))) ) (= (list_list_take l 0) (as nil (MLList (MLList Int))))))
; end of list take

; end of list of lists definition

(define-fun list_slice ((lst (MLList Int)) (start Int) (end Int)) (MLList Int)
(list_take (list_take lst end) start))

(define-fun list_slice_with_length ((lst (MLList Int)) (start Int) (lst_length Int)) (MLList Int)
(list_slice lst start (+ start lst_length)))

(define-fun list_list_slice ((matrix (MLList (MLList Int))) (start Int) (end Int)) (MLList (MLList Int))
(list_list_take (list_list_take matrix end) start))

(define-fun list_list_slice_with_length ((matrix (MLList (MLList Int))) (start Int) (lst_length Int)) (MLList (MLList Int))
(list_list_slice matrix start (+ start lst_length)))

(define-fun-rec list_list_col_slice ((matrix (MLList (MLList Int))) (start Int) (end Int)) (MLList (MLList Int))
(ite (< (list_list_length matrix) 1) list_list_empty (list_list_prepend (list_slice (list_list_get matrix 0) start end) (list_list_col_slice (list_list_tail matrix 1) start end))))

(define-fun-rec list_list_col_slice_with_length ((matrix (MLList (MLList Int))) (start Int) (lst_length Int)) (MLList (MLList Int))
(list_list_col_slice matrix start (+ start lst_length)))

(define-fun-rec firsts ((matrix (MLList (MLList Int)))) (MLList Int)
(ite (< (list_list_length matrix) 1) list_empty (list_prepend (list_get (list_list_get matrix 0) 0) (firsts (list_list_tail matrix 1)))))

(define-fun-rec rests ((matrix (MLList (MLList Int)))) (MLList (MLList Int))
(ite (< (list_list_length matrix) 1) list_list_empty (list_list_col_slice matrix 1 (list_length (list_list_get matrix 0)))))

(define-fun-rec matrix_transpose ((matrix (MLList (MLList Int)))) (MLList (MLList Int))
(ite (< (list_list_length matrix) 1) list_list_empty (list_list_prepend (firsts matrix) (matrix_transpose (rests matrix)))))

(define-fun-rec vec_elemwise_mul ((x (MLList Int)) (y (MLList Int))) (MLList Int)
(ite (or (< (list_length x) 1) (not (= (list_length x) (list_length y)))) list_empty (list_prepend (* (list_get x 0) (list_get y 0)) (vec_elemwise_mul (list_tail x 1) (list_tail y 1)))))

(define-fun-rec reduce_sum ((x (MLList Int))) Int
(ite (< (list_length x) 1) 0 (+ (list_get x 0) (reduce_sum (list_tail x 1)))))

(define-fun-rec rmsnorm_part1_inv0 ((i Int) (input (MLList Int)) (ss Int) (weight (MLList Int))) Bool
(and (and (>= i 0) (<= i (list_length input))) (= ss (reduce_sum (vec_elemwise_mul (list_take input i) (list_take input i))))))



(define-fun-rec rmsnorm_part1_ps ((input (MLList Int)) (weight (MLList Int)) (rmsnorm_part1_rv Int)) Bool
(= rmsnorm_part1_rv (reduce_sum (vec_elemwise_mul input input))))

(declare-const rmsnorm_part1_rv Int)
(declare-const ss Int)
(declare-const weight (MLList Int))
(declare-const i Int)
(declare-const input (MLList Int))



(assert (not (and (and (=> (and (= (list_length input) (list_length weight)) (> (list_length input) 0)) (rmsnorm_part1_inv0 0 input 0 weight)) (=> (and (and (and (< i (list_length input)) (= (list_length input) (list_length weight))) (> (list_length input) 0)) (rmsnorm_part1_inv0 i input ss weight)) (rmsnorm_part1_inv0 (+ i 1) input (+ ss (* (list_get input i) (list_get input i))) weight))) (=> (and (and (and (not (< i (list_length input))) (= (list_length input) (list_length weight))) (> (list_length input) 0)) (rmsnorm_part1_inv0 i input ss weight)) (rmsnorm_part1_ps input weight ss)))))

(check-sat)
(get-model)
