; tuple definitions
(declare-datatypes ((Tuple1 1)) ((par (T0)             ((tuple1 (tuple1_get0 T0))))))
(declare-datatypes ((Tuple2 2)) ((par (T0 T1)          ((tuple2 (tuple2_get0 T0) (tuple2_get1 T1))))))
(declare-datatypes ((Tuple3 3)) ((par (T0 T1 T2)       ((tuple3 (tuple3_get0 T0) (tuple3_get1 T1) (tuple3_get2 T2))))))
(declare-datatypes ((Tuple4 4)) ((par (T0 T1 T2 T3)    ((tuple4 (tuple4_get0 T0) (tuple4_get1 T1) (tuple4_get2 T2) (tuple4_get3 T3))))))
(declare-datatypes ((Tuple5 5)) ((par (T0 T1 T2 T3 T4) ((tuple5 (tuple5_get0 T0) (tuple5_get1 T1) (tuple5_get2 T2) (tuple5_get3 T3) (tuple5_get4 T4))))))
; begin integer functions
; TODO(jie): fix
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
(list_tail (list_take lst end) start))
;(define-fun vec_slice ((lst (MLList Int)) (start Int) (end Int)) (MLList Int)
;(list_take (list_tail lst start) (- end start)))
(define-fun vec_slice_with_length ((lst (MLList Int)) (start Int) (lst_length Int)) (MLList Int)
(vec_slice lst start (+ start lst_length)))
(define-fun matrix_row_slice ((matrix (MLList (MLList Int))) (start Int) (end Int)) (MLList (MLList Int))
(matrix_tail (matrix_take matrix end) start))
(define-fun matrix_row_slice_with_length ((matrix (MLList (MLList Int))) (start Int) (lst_length Int)) (MLList (MLList Int))
(matrix_row_slice matrix start (+ start lst_length)))
(define-fun-rec matrix_col_slice ((matrix (MLList (MLList Int))) (start Int) (end Int)) (MLList (MLList Int))
(ite (or
       (< (matrix_length matrix) 1)
       (= (list_length (vec_slice (matrix_get matrix 0) start end)) 0)
     ) matrix_empty (matrix_prepend (vec_slice (matrix_get matrix 0) start end) (matrix_col_slice (matrix_tail matrix 1) start end))))
(define-fun-rec matrix_col_slice_with_length ((matrix (MLList (MLList Int))) (start Int) (lst_length Int)) (MLList (MLList Int))
(matrix_col_slice matrix start (+ start lst_length)))

(define-fun-rec firsts ((matrix (MLList (MLList Int)))) (MLList Int)
(ite (< (matrix_length matrix) 1) list_empty (list_prepend (list_get (matrix_get matrix 0) 0) (firsts (matrix_tail matrix 1)))))

; axioms for firsts
(assert (forall ((matrix (MLList (MLList Int))) (i Int))
  (=> (and (>= i 0) (< i (matrix_length matrix)))
      (= (list_get (firsts matrix) i) (list_get (matrix_get matrix i) 0)))))
(assert (forall ((matrix (MLList (MLList Int))))
 (= (list_length (firsts matrix)) (matrix_length matrix))))

(define-fun-rec rests ((matrix (MLList (MLList Int)))) (MLList (MLList Int))
(ite (< (matrix_length matrix) 1)
     matrix_empty
     (matrix_col_slice matrix 1 (list_length (matrix_get matrix 0)))
)
)

(define-fun-rec matrix_transpose ((matrix (MLList (MLList Int)))) (MLList (MLList Int))
(ite (< (matrix_length matrix) 1) matrix_empty (matrix_prepend (firsts matrix) (matrix_transpose (ite (< (matrix_length matrix) 1)
     matrix_empty
     (matrix_col_slice matrix 1 (list_length (matrix_get matrix 0)))
)))))

; axioms for matrix transpose
(assert (forall ((matrix (MLList (MLList Int))))
  (= (matrix_length (matrix_transpose matrix))
     (ite (= (matrix_length matrix) 0)
          0
          (list_length (matrix_get matrix 0))))))

(define-fun-rec vec_elemwise_add ((x (MLList Int)) (y (MLList Int))) (MLList Int)
(ite (or (< (list_length x) 1) (not (= (list_length x) (list_length y)))) list_empty (list_prepend (+ (list_get x 0) (list_get y 0)) (vec_elemwise_add (list_tail x 1) (list_tail y 1)))))
(define-fun-rec vadd_ps ((a (MLList Int)) (b (MLList Int)) (n Int) (vadd_rv (MLList Int))) Bool
(= vadd_rv (vec_elemwise_add (list_take a n) (list_take b n))))
(define-fun-rec vadd_inv0 ((a (MLList Int)) (agg.result (MLList Int)) (b (MLList Int)) (i Int) (n Int) (ref.tmp Int)) Bool
(and (and (>= i 0) (<= i n)) (= agg.result (vec_elemwise_add (list_take a i) (list_take b i)))))
; (assert (forall ((a Int)) (= (matrix_transpose (rests (cons (cons a (as nil (MLList Int))) (as nil (MLList (MLList Int)))))) matrix_empty)))

;(declare-const a (MLList Int))
;(declare-const agg.result (MLList Int))
;(declare-const i Int)
;(declare-const n Int)
;(declare-const b (MLList Int))
;(declare-const ref.tmp Int)
;(declare-const vadd_rv (MLList Int))
;
;(assert (forall ( (data  (MLList Int) ) (data2  (MLList Int) )  (index Int)  )
;(=> (and (>= index 0) (< index (list_length data)) )
;(= (vec_elemwise_add (list_take data index) (list_take data2 index)) (list_prepend (+ (list_get data 0) (list_get data2 0)) (vec_elemwise_add (list_tail (list_take data index) 1)  (list_tail (list_take data2 index) 1))  )))))
;
;(assert (not (and (and (=> (and (and (>= n 1) (>= (list_length a) n)) (>= (list_length b) n)) (vadd_inv0 a list_empty b 0 n 0)) (=> (and (and (and (and (< i n) (>= n 1)) (>= (list_length a) n)) (>= (list_length b) n)) (vadd_inv0 a agg.result b i n ref.tmp)) (vadd_inv0 a (list_append agg.result (+ (list_get a i) (list_get b i))) b (+ i 1) n (+ (list_get a i) (list_get b i))))) (=> (or (and (and (and (and (not (< i n)) (>= n 1)) (>= (list_length a) n)) (>= (list_length b) n)) (vadd_inv0 a agg.result b i n ref.tmp)) (and (and (and (and (and (not true) (not (< i n))) (>= n 1)) (>= (list_length a) n)) (>= (list_length b) n)) (vadd_inv0 a agg.result b i n ref.tmp))) (vadd_ps a b n agg.result)))))
;
;(check-sat)
;(get-model)
;matrix equal axiom
;(assert (forall ((matrix (MLList (MLList Int))) (matrix2 (MLList (MLList Int))) (i Int) (j Int))
;(=> (= matrix matrix2) (= (matrix_get matrix i) (matrix_get matrix2 i)))))
;
;writing test cases for matrix transpose
;(declare-const matrix_a (MLList (MLList Int)))
;(assert (= matrix_a (cons (cons 1 (as nil (MLList Int))) (as nil (MLList (MLList Int))))) )
;
;empty matrix transpose is empty
;(push)
;(assert (not (= (matrix_transpose (as nil (MLList (MLList Int)))) (as nil (MLList (MLList Int))))))
;(check-sat)
;(pop)
;unsat
;empty list vec slice
;(push)
;(assert (not (= (vec_slice (cons 1 (as nil (MLList Int))) 1 1) (as nil (MLList Int)))))
;(check-sat)

;(pop)
;unsat
;Single element list
;(declare-const single_element_list (MLList Int))
;(assert (= single_element_list (cons 1 (as nil (MLList Int)))))
;(push)
;(assert (not (= (vec_slice single_element_list 0 1) single_element_list)))
;(check-sat)
;(pop)
;unsat
;Multiple elements list
;(declare-const multiple_elements_list (MLList Int))
;(assert (= multiple_elements_list (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 (as nil (MLList Int)))))))))
;(push)
;(assert (not (= (vec_slice multiple_elements_list 0 3) (cons 1 (cons 2 (cons 3 (as nil (MLList Int))))))))
;(check-sat)
;(pop)
 ;Empty matrix col slice
;(push)
;(assert (not (= (matrix_col_slice (as nil (MLList (MLList Int))) 0 2) (as nil (MLList (MLList Int))))))
;(check-sat)
;(pop)
;unsat
;single row matrix col slice
; Matrix with rows of different lengths
;(declare-const diff_length_matrix (MLList (MLList Int)))
;(assert (= diff_length_matrix (cons (cons 1 (cons 2 (as nil (MLList Int))))
;                                    (cons (cons 3 (cons 4 (cons 5 (as nil (MLList Int)))))
;                                          (cons (cons 6 (as nil (MLList Int)))
;                                                (as nil (MLList (MLList Int))))))))
;(declare-const diff_length_matrix_rests (MLList (MLList Int)))
;(assert (= diff_length_matrix_rests (cons (cons 2 (as nil (MLList Int)))
;                                          (cons (cons 4 (cons 5 (as nil (MLList Int))))
;                                                (cons (as nil (MLList Int))
;                                                      (as nil (MLList (MLList Int))))))))
;(push)
;(assert (not (= (rests diff_length_matrix) diff_length_matrix_rests)))
;(check-sat)
;(pop)
;check if smt can prove square matrix equality
;(declare-const square_matrix1 (MLList (MLList Int)))
;(assert (= square_matrix1 (cons (cons 1 (cons 2 (as nil (MLList Int))))
;                               (cons (cons 3 (cons 4 (as nil (MLList Int))))
;                                     (as nil (MLList (MLList Int)))))))
;
;(declare-const square_matrix2 (MLList (MLList Int)))
;(assert (= square_matrix2 (cons (cons 1 (cons 2 (as nil (MLList Int))))
;                               (cons (cons 3 (cons 4 (as nil (MLList Int))))
;                                     (as nil (MLList (MLList Int)))))))
;
;(push)
;(assert (not (= (matrix_transpose square_matrix1) (matrix_transpose square_matrix2))))
;(check-sat)
;(pop)
;
;first
;Single row matrix 3 element
(declare-const single_row_matrix3 (MLList (MLList Int)))
(assert (= single_row_matrix3 (cons (cons 3 (cons 2 (cons 1 (as nil (MLList Int))))) (as nil (MLList (MLList Int))))))
(push)
(assert (not (=
     (matrix_transpose single_row_matrix3)
     (cons
          (cons 3 (as nil (MLList Int)))
          (cons
               (cons 2 (as nil (MLList Int)))
               (cons
                    (cons 1 (as nil (MLList Int)))
                    (as nil (MLList (MLList Int)))
               )
          )
     )
)))
(check-sat)
(pop)
; (assert (not (= (firsts single_row_matrix3) (cons 1 (as nil (MLList Int))))))

; (assert (not (= (list_length (matrix_get single_row_matrix3 0)) 3)))
; (push)

;Single row matrix 2 element
; (declare-const single_row_matrix2 (MLList (MLList Int)))
; (assert (= single_row_matrix2 (cons (cons 1 (cons 2 (as nil (MLList Int)))) (as nil (MLList (MLList Int))))))
; (push)
;(assert (not (= (firsts single_row_matrix2) (cons 1 (as nil (MLList Int))))))
;(push)
;(assert (not (= (list_length (matrix_get single_row_matrix2 0)) 3)))
;(push)
; (assert (not (=
;      (matrix_transpose single_row_matrix2)
;      (cons
;           (cons 1 (as nil (MLList Int)))
;           (cons
;                (cons 2 (as nil (MLList Int)))
;                (as nil (MLList (MLList Int)))
;           )
;      ))))
; (push)
; (assert (not (= (matrix_transpose single_row_matrix2)
;           (cons
;           (cons 1 (as nil (MLList Int)))
;           (cons
;                (cons 2 (as nil (MLList Int)))
;                (as nil (MLList (MLList Int)))
;           )
;      )
; )))
; (assert (not (= (rests single_row_matrix2)
;                (cons (cons 2 (as nil (MLList Int)))
;                (as nil (MLList (MLList Int))))
;                )))
; (check-sat)
; (pop)

;(assert (not (= (rests single_row_matrix3) (cons (cons 2 (as nil (MLList Int))) (cons (cons 3 (as nil (MLList Int))) (as nil (MLList (MLList Int))))))))
;(check-sat)
;(pop)

;(declare-const single_list (MLList Int))
;(assert (= single_list (cons 1 (cons 2 (cons 3 (as nil (MLList Int)))))))
;(push)
;(assert (not (= (vec_slice single_list 0 3) single_list)))
;(push)
;(check-sat)
;(pop)

;
;; Multiple rows matrix
;(declare-const multiple_rows_matrix3 (MLList (MLList Int)))
;(assert (= multiple_rows_matrix3 (cons (cons 1 (cons 2 (cons 3 (as nil (MLList Int)))))
;                                      (cons (cons 4 (cons 5 (cons 6 (as nil (MLList Int)))))
;                                            (as nil (MLList (MLList Int)))))))
;(push)
;(assert (not (= (firsts multiple_rows_matrix3) (cons 1 (cons 4 (as nil (MLList Int)))))))
;(check-sat)
;(pop)
;(assert (not (= (rests single_element_matrix) (as nil (MLList (MLList Int))))))
;(assert (forall ((a Int)) (= (matrix_transpose (rests (cons (cons a (as nil (MLList Int))) (as nil (MLList (MLList Int)))))) matrix_empty)))
; (declare-const single_element_matrix (MLList (MLList Int)))
; (assert (= single_element_matrix (cons (cons 1 (as nil (MLList Int))) (as nil (MLList (MLList Int))))))
; (assert (not (= (rests single_element_matrix) (as nil (MLList (MLList Int))))))
; (push)
; (check-sat)
; (pop)
;(assert (not (= (matrix_col_slice single_element_matrix 1 (list_length (matrix_get single_element_matrix 0))) matrix_empty)))
;(assert (not (= (matrix_transpose single_element_matrix) single_element_matrix)))
;(assert (not (= (firsts single_element_matrix) (cons 1 (as nil (MLList Int))))))
;(assert (not (= (rests single_element_matrix) matrix_empty)))
;(assert (not (= (matrix_transpose (rests single_element_matrix)) matrix_empty)))
;(assert (not (= (list_length (matrix_get single_element_matrix 0)) 1)))
;(assert (not (= (list_length (vec_slice (matrix_get single_element_matrix 0) 1 1)) 0)))
;(assert (not (= (rests ))))
;(push)
;(check-sat)
; (declare-const single_element_matrix (MLList (MLList Int)))
; (assert (= single_element_matrix (cons (cons 1 (as nil (MLList Int))) (as nil (MLList (MLList Int))))))
; (push)
; ; (assert (not (= (firsts single_element_matrix) (cons 1 (as nil (MLList Int))))))
; ; (push)
; (assert (not (= (matrix_prepend (cons 1 (as nil (MLList Int))) matrix_empty) single_element_matrix)))
; (push)
; (check-sat)
; (pop)
;;(assert (not (= (matrix_col_slice single_element_matrix 1 1) (as nil (MLList (MLList Int))))))
;;(assert (not (= (matrix_prepend (vec_slice (matrix_get single_element_matrix 0) 1 1) (matrix_col_slice (matrix_tail single_element_matrix 1)1 1)) matrix_empty))
;;)
;(check-sat)
;(pop)
;transpose of single element matrix
;(declare-const single_element_matrix (MLList (MLList Int)))
;(assert (= single_element_matrix (cons (cons 1 (as nil (MLList Int))) (as nil (MLList (MLList Int))))))
;(push)
;(assert (not (= (matrix_transpose single_element_matrix) single_element_matrix)))
;(check-sat)
;(pop)
;
;
;;transpose of square matrix
;(declare-const square_matrix (MLList (MLList Int)))
;(assert (= square_matrix (cons (cons 1 (cons 2 (as nil (MLList Int))))
;                               (cons (cons 3 (cons 4 (as nil (MLList Int))))
;                                     (as nil (MLList (MLList Int)))))))
;(declare-const square_matrix_transposed (MLList (MLList Int)))
;(push)
;(assert (forall ((matrix (MLList (MLList Int))) (matrix2 (MLList (MLList Int))) (i Int) (j Int))
;(=> (= matrix matrix2) (= (matrix_get matrix i) (matrix_get matrix2 i)))))
;(assert (= square_matrix_transposed (cons (cons 1 (cons 3 (as nil (MLList Int))))
;                                          (cons (cons 2 (cons 4 (as nil (MLList Int))))
;                                                (as nil (MLList (MLList Int)))))))
;
;(assert (not (= (matrix_transpose square_matrix) square_matrix_transposed)))
;(check-sat)
;(pop)
;
