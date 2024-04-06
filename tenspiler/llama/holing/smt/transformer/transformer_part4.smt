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

(declare-fun matrix_length ( (MLList (MLList Int) ) ) Int)
(assert (= (matrix_length (as nil (MLList (MLList Int) ))) 0))
(assert (forall ( (val (MLList Int) ) (l (MLList (MLList Int) )) )
                (= (matrix_length (cons val l)) (+ 1 (matrix_length l)))))
(assert (forall ( (l (MLList (MLList Int) )) )
                (<= 0 (matrix_length l))))

;end of list length

(define-fun matrix_prepend ( (val (MLList Int) ) (l (MLList (MLList Int) ) )) (MLList (MLList Int) ) (cons val l))
; end of list prepend


(declare-fun matrix_append ( (MLList (MLList Int)  ) (MLList Int) ) (MLList (MLList Int) ))
(assert (forall ( (val (MLList Int)) )
                (= (matrix_append (as nil (MLList (MLList Int))) val) (cons val (as nil (MLList (MLList Int)))))))
(assert (forall ( (h (MLList Int)) (t (MLList (MLList Int))) (val (MLList Int)) )
                (= (matrix_append (cons h t) val) (cons h (matrix_append t val)))))
;end of list append

(declare-fun matrix_get_helper ( (MLList (MLList Int) ) Int ) (MLList Int) )
(define-fun matrix_get ( (l (MLList (MLList Int) )) (i Int) ) (MLList Int) (matrix_get_helper l i))
(assert (forall ( (h (MLList Int) ) (t (MLList (MLList Int) )) (i Int) )
                (ite (<= i 0)
                     (= (matrix_get_helper (cons h t) i) h)
                     (= (matrix_get_helper (cons h t) i) (matrix_get_helper t (- i 1))))))
;end of list get

(define-fun matrix_empty ( ) (MLList (MLList Int)) (as nil (MLList (MLList Int) )))
;end of empty list



(define-fun-rec matrix_tail ((l (MLList (MLList Int) ) ) (n Int)) (MLList (MLList Int) )
  (ite (<= n 0)  l (matrix_tail (tail l) (- n 1))))
(assert (forall ( (start Int) (h (MLList Int) ) (t (MLList (MLList Int) )) )
                (ite (<= start 0)
                     (= (matrix_tail (cons h t) start) (cons h t))
                     (= (matrix_tail (cons h t) start) (matrix_tail t (- start 1))))))
(assert (forall ( (start Int) )
                (= (matrix_tail (as nil (MLList (MLList Int) )) start) (as nil (MLList (MLList Int)) ))))
(assert (forall ( (start Int) (l (MLList (MLList Int) )) )
                (=> (>= start (matrix_length l))
                    (= (matrix_tail l start) (as nil (MLList (MLList Int) ))))))

; end of list tail

(declare-fun matrix_take ( (MLList (MLList Int)) Int ) (MLList (MLList Int)))

(assert (forall ( (end Int) (h (MLList Int)) (t (MLList (MLList Int))) )
                (ite (<= end 0)
                     (= (matrix_take (cons h t) end) (as nil (MLList (MLList Int))))
                     (= (matrix_take (cons h t) end) (cons h (matrix_take t (- end 1)))))))
(assert (forall ( (end Int) )
                (= (matrix_take (as nil (MLList (MLList Int))) end) (as nil (MLList (MLList Int))))))
(assert (forall ( (end Int) (l (MLList (MLList Int))) )
                (=> (>= end (matrix_length l))
                    (= (matrix_take l end) l))))

(assert (forall ( (l (MLList (MLList Int))) ) (= (matrix_take l 0) (as nil (MLList (MLList Int))))))
; end of list take

; end of list of lists definition

(define-fun vec_slice ((lst (MLList Int)) (start Int) (end Int)) (MLList Int)
(list_take (list_take lst end) start))

(define-fun list_slice_with_length ((lst (MLList Int)) (start Int) (lst_length Int)) (MLList Int)
(vec_slice lst start (+ start lst_length)))

(define-fun matrix_row_slice ((matrix (MLList (MLList Int))) (start Int) (end Int)) (MLList (MLList Int))
(matrix_take (matrix_take matrix end) start))

(define-fun matrix_slice_with_length ((matrix (MLList (MLList Int))) (start Int) (lst_length Int)) (MLList (MLList Int))
(matrix_row_slice matrix start (+ start lst_length)))

(define-fun-rec matrix_col_slice ((matrix (MLList (MLList Int))) (start Int) (end Int)) (MLList (MLList Int))
(ite (< (matrix_length matrix) 1) matrix_empty (matrix_prepend (vec_slice (matrix_get matrix 0) start end) (matrix_col_slice (matrix_tail matrix 1) start end))))

(define-fun-rec matrix_col_slice_with_length ((matrix (MLList (MLList Int))) (start Int) (lst_length Int)) (MLList (MLList Int))
(matrix_col_slice matrix start (+ start lst_length)))

(define-fun-rec firsts ((matrix (MLList (MLList Int)))) (MLList Int)
(ite (< (matrix_length matrix) 1) list_empty (list_prepend (list_get (matrix_get matrix 0) 0) (firsts (matrix_tail matrix 1)))))

(define-fun-rec rests ((matrix (MLList (MLList Int)))) (MLList (MLList Int))
(ite (< (matrix_length matrix) 1) matrix_empty (matrix_col_slice matrix 1 (list_length (matrix_get matrix 0)))))

(define-fun-rec matrix_transpose ((matrix (MLList (MLList Int)))) (MLList (MLList Int))
(ite (< (matrix_length matrix) 1) matrix_empty (matrix_prepend (firsts matrix) (matrix_transpose (rests matrix)))))

(define-fun-rec vec_elemwise_mul ((x (MLList Int)) (y (MLList Int))) (MLList Int)
(ite (or (< (list_length x) 1) (not (= (list_length x) (list_length y)))) list_empty (list_prepend (* (list_get x 0) (list_get y 0)) (vec_elemwise_mul (list_tail x 1) (list_tail y 1)))))

(define-fun-rec transformer_part4_inv0 ((agg.result (MLList Int)) (hidden_dim Int) (i Int) (input1 (MLList Int)) (input2 (MLList Int)) (ref.tmp Int)) Bool
(and (and (>= i 0) (<= i hidden_dim)) (= agg.result (vec_elemwise_mul (list_take input1 i) (list_take input2 i)))))



(define-fun-rec transformer_part4_ps ((input1 (MLList Int)) (input2 (MLList Int)) (hidden_dim Int) (transformer_part4_rv (MLList Int))) Bool
(= transformer_part4_rv (vec_elemwise_mul (list_take input1 hidden_dim) (list_take input2 hidden_dim))))

(declare-const input1 (MLList Int))
(declare-const input2 (MLList Int))
(declare-const hidden_dim Int)
(declare-const agg.result (MLList Int))
(declare-const i Int)
(declare-const ref.tmp Int)
(declare-const transformer_part4_rv (MLList Int))



(assert (not (and (and (=> (and (and (>= hidden_dim 0) (>= (list_length input1) hidden_dim)) (>= (list_length input2) hidden_dim)) (transformer_part4_inv0 list_empty hidden_dim 0 input1 input2 0)) (=> (and (and (and (and (< i hidden_dim) (>= hidden_dim 0)) (>= (list_length input1) hidden_dim)) (>= (list_length input2) hidden_dim)) (transformer_part4_inv0 agg.result hidden_dim i input1 input2 ref.tmp)) (transformer_part4_inv0 (list_append agg.result (* (list_get input1 i) (list_get input2 i))) hidden_dim (+ i 1) input1 input2 (* (list_get input1 i) (list_get input2 i))))) (=> (or (and (and (and (and (not (< i hidden_dim)) (>= hidden_dim 0)) (>= (list_length input1) hidden_dim)) (>= (list_length input2) hidden_dim)) (transformer_part4_inv0 agg.result hidden_dim i input1 input2 ref.tmp)) (and (and (and (and (and (not true) (not (< i hidden_dim))) (>= hidden_dim 0)) (>= (list_length input1) hidden_dim)) (>= (list_length input2) hidden_dim)) (transformer_part4_inv0 agg.result hidden_dim i input1 input2 ref.tmp))) (transformer_part4_ps input1 input2 hidden_dim agg.result)))))

(check-sat)
(get-model)
