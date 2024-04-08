#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (matrix_vec_mul matrix_x x)
(if (or (or (< (matrix-length matrix_x ) 1 ) (< (length (matrix-ref-noerr matrix_x 0 ) ) 1 ) ) (! (equal? (length (matrix-ref-noerr matrix_x 0 ) ) (length x ) ) ) ) (list-empty ) (list-prepend (reduce_sum (vec_elemwise_mul (matrix-ref-noerr matrix_x 0 ) x)) (matrix_vec_mul (matrix-tail-noerr matrix_x 1 ) x ) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 )) ) ))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))

(define-grammar (mat1x3_inv0_gram N agg.result f h i sum x)
 [rv (choose (&& (&& (>= i 0 ) (<= i N ) ) (equal? agg.result (matrix_vec_mul (v0) (if (VECTOR_OUTER_LOOP_INDEX) (list-take-noerr x i ) (list-take-noerr x N ) ) ) ) ))]
[v0 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr h i ) 0 N ) (matrix-col-slice-noerr (matrix-take-noerr h N ) 0 i ) ) (matrix-transpose-noerr (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr h i ) 0 N ) (matrix-col-slice-noerr (matrix-take-noerr h N ) 0 i ) ) ))]
)

(define-grammar (mat1x3_inv1_gram N f h sum x agg.result i)
 [rv (choose (&& (&& (&& (&& (&& (>= i 0 ) (< i N ) ) (>= f 0 ) ) (<= f N ) ) (equal? sum (reduce_sum (if (VECTOR_OUTER_LOOP_INDEX) (vec_scalar_mul (list-ref-noerr x i ) (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-take-noerr (matrix-ref-noerr h i ) f ) (matrix-ref-noerr (matrix-transpose-noerr (matrix-col-slice-with-length-noerr (matrix-take-noerr h f ) i 1 ) ) 0 ) )) (vec_elemwise_mul (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-take-noerr (matrix-ref-noerr h i ) f ) (matrix-ref-noerr (matrix-transpose-noerr (matrix-col-slice-with-length-noerr (matrix-take-noerr h f ) i 1 ) ) 0 ) ) (list-take-noerr x f )) )) ) ) (equal? agg.result (matrix_vec_mul (v0) (if (VECTOR_OUTER_LOOP_INDEX) (list-take-noerr x i ) (list-take-noerr x N ) ) ) ) ))]
[v0 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr h i ) 0 N ) (matrix-col-slice-noerr (matrix-take-noerr h N ) 0 i ) ) (matrix-transpose-noerr (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr h i ) 0 N ) (matrix-col-slice-noerr (matrix-take-noerr h N ) 0 i ) ) ))]
)

(define-grammar (mat1x3_ps_gram N h x mat1x3_rv)
 [rv (choose (equal? mat1x3_rv (matrix_vec_mul (v0) (list-take-noerr x N ) ) ))]
[v0 (choose (matrix-col-slice-noerr (matrix-take-noerr h N ) 0 N ) (matrix-transpose-noerr (matrix-col-slice-noerr (matrix-take-noerr h N ) 0 N ) ))]
)

(define-grammar (MATRIX_OUTER_LOOP_INDEX_FIRST_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
)

(define-grammar (VECTOR_OUTER_LOOP_INDEX_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
)

(define (mat1x3_inv0 N agg.result f h i sum x) (mat1x3_inv0_gram N agg.result f h i sum x #:depth 10))
(define (mat1x3_inv1 N f h sum x agg.result i) (mat1x3_inv1_gram N f h sum x agg.result i #:depth 10))
(define (mat1x3_ps N h x mat1x3_rv) (mat1x3_ps_gram N h x mat1x3_rv #:depth 10))

(define (MATRIX_OUTER_LOOP_INDEX_FIRST ) (MATRIX_OUTER_LOOP_INDEX_FIRST_gram  #:depth 10))
(define (VECTOR_OUTER_LOOP_INDEX ) (VECTOR_OUTER_LOOP_INDEX_gram  #:depth 10))

(define-symbolic N integer?)
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic f integer?)
(define-symbolic h_BOUNDEDSET-len integer?)
(define-symbolic h_BOUNDEDSET-0 integer?)
(define-symbolic h_BOUNDEDSET-1 integer?)
(define-symbolic h_BOUNDEDSET-2 integer?)
(define-symbolic h_BOUNDEDSET-3 integer?)
(define h (take (list (list h_BOUNDEDSET-0 h_BOUNDEDSET-1) (list h_BOUNDEDSET-2 h_BOUNDEDSET-3)) h_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic mat1x3_rv_BOUNDEDSET-len integer?)
(define-symbolic mat1x3_rv_BOUNDEDSET-0 integer?)
(define-symbolic mat1x3_rv_BOUNDEDSET-1 integer?)
(define mat1x3_rv (take (list mat1x3_rv_BOUNDEDSET-0 mat1x3_rv_BOUNDEDSET-1) mat1x3_rv_BOUNDEDSET-len))
(define-symbolic sum integer?)
(define-symbolic x_BOUNDEDSET-len integer?)
(define-symbolic x_BOUNDEDSET-0 integer?)
(define-symbolic x_BOUNDEDSET-1 integer?)
(define x (take (list x_BOUNDEDSET-0 x_BOUNDEDSET-1) x_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (&& (>= N 1 ) (>= (matrix-length h ) N ) ) (>= (length (matrix-ref-noerr h 0 ) ) N ) ) (>= (length x ) N ) ) (mat1x3_inv0 N (list-empty ) 0 h 0 0 x) ) (=> (&& (&& (&& (&& (&& (< i N ) (>= N 1 ) ) (>= (matrix-length h ) N ) ) (>= (length (matrix-ref-noerr h 0 ) ) N ) ) (>= (length x ) N ) ) (mat1x3_inv0 N agg.result f h i sum x) ) (mat1x3_inv1 N 0 h 0 x agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (< f N ) (< i N ) ) (>= N 1 ) ) (>= (matrix-length h ) N ) ) (>= (length (matrix-ref-noerr h 0 ) ) N ) ) (>= (length x ) N ) ) (mat1x3_inv0 N agg.result f h i sum x) ) (mat1x3_inv1 N f h sum x agg.result i) ) (mat1x3_inv1 N (+ f 1 ) h (+ sum (* (list-ref-noerr (matrix-ref-noerr h i ) f ) (list-ref-noerr x f ) ) ) x agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (! (< f N ) ) (< i N ) ) (>= N 1 ) ) (>= (matrix-length h ) N ) ) (>= (length (matrix-ref-noerr h 0 ) ) N ) ) (>= (length x ) N ) ) (mat1x3_inv0 N agg.result f h i sum x) ) (mat1x3_inv1 N f h sum x agg.result i) ) (mat1x3_inv0 N (list-append agg.result sum ) f h (+ i 1 ) sum x) ) ) (=> (or (&& (&& (&& (&& (&& (! (< i N ) ) (>= N 1 ) ) (>= (matrix-length h ) N ) ) (>= (length (matrix-ref-noerr h 0 ) ) N ) ) (>= (length x ) N ) ) (mat1x3_inv0 N agg.result f h i sum x) ) (&& (&& (&& (&& (&& (&& (! true ) (! (< i N ) ) ) (>= N 1 ) ) (>= (matrix-length h ) N ) ) (>= (length (matrix-ref-noerr h 0 ) ) N ) ) (>= (length x ) N ) ) (mat1x3_inv0 N agg.result f h i sum x) ) ) (mat1x3_ps N h x agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list N agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 f h_BOUNDEDSET-len h_BOUNDEDSET-0 h_BOUNDEDSET-1 h_BOUNDEDSET-2 h_BOUNDEDSET-3 i mat1x3_rv_BOUNDEDSET-len mat1x3_rv_BOUNDEDSET-0 mat1x3_rv_BOUNDEDSET-1 sum x_BOUNDEDSET-len x_BOUNDEDSET-0 x_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
