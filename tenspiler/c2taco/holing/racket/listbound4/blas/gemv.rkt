#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


 (define-bounded (matrix_vec_mul matrix_x x)
(if (or (or (< (matrix-length matrix_x ) 1 ) (< (length (matrix-ref-noerr matrix_x 0 ) ) 1 ) ) (! (equal? (length (matrix-ref-noerr matrix_x 0 ) ) (length x ) ) ) ) (list-empty ) (list-prepend (reduce_sum (vec_elemwise_mul (matrix-ref-noerr matrix_x 0 ) x )) (matrix_vec_mul (matrix-tail-noerr matrix_x 1 ) x ) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))


 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 ) ) ) ))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))

(define-grammar (gemv_inv0_gram A M N agg.result i j sum x)
 [rv (choose (&& (&& (>= i 0 ) (<= i M ) ) (equal? agg.result (matrix_vec_mul (v0) (if (VECTOR_OUTER_LOOP_INDEX) (list-take-noerr x i ) (list-take-noerr x N ) ) ) ) ))]
[v0 (choose (v1) (matrix-transpose-noerr (v1) ))]
[v1 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr A i ) 0 N ) (matrix-col-slice-noerr (matrix-take-noerr A N ) 0 i ) ))]
)

(define-grammar (gemv_inv1_gram A M N j sum x agg.result i)
 [rv (choose (&& (&& (&& (&& (&& (>= i 0 ) (< i M ) ) (>= j 0 ) ) (<= j N ) ) (equal? sum (reduce_sum (v0)) ) ) (equal? agg.result (matrix_vec_mul (v2) (v4) ) ) ))]
[v0 (choose (if (VECTOR_OUTER_LOOP_INDEX) (vec_scalar_mul (list-ref-noerr x i ) (v1) ) (vec_elemwise_mul (v1) (list-take-noerr x j ) ) ))]
[v1 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-take-noerr (matrix-ref-noerr A i ) j ) (matrix-ref-noerr (matrix-transpose-noerr (matrix-col-slice-with-length-noerr (matrix-take-noerr A j ) i 1 ) ) 0 ) ))]
[v2 (choose (v3) (matrix-transpose-noerr (v3) ))]
[v3 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr A i ) 0 N ) (matrix-col-slice-noerr (matrix-take-noerr A N ) 0 i ) ))]
[v4 (choose (if (VECTOR_OUTER_LOOP_INDEX) (list-take-noerr x i ) (list-take-noerr x N ) ))]
)

(define-grammar (gemv_ps_gram M N A x gemv_rv)
 [rv (choose (equal? gemv_rv (matrix_vec_mul (v0) (v2) ) ))]
[v0 (choose (v1) (matrix-transpose-noerr (v1) ))]
[v1 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr A M ) 0 N ) (matrix-col-slice-noerr (matrix-take-noerr A N ) 0 M ) ))]
[v2 (choose (if (VECTOR_OUTER_LOOP_INDEX) (list-take-noerr x M ) (list-take-noerr x N ) ))]
)

(define-grammar (MATRIX_OUTER_LOOP_INDEX_FIRST_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
)

(define-grammar (VECTOR_OUTER_LOOP_INDEX_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
)

(define (gemv_inv0 A M N agg.result i j sum x) (gemv_inv0_gram A M N agg.result i j sum x #:depth 10))
(define (gemv_inv1 A M N j sum x agg.result i) (gemv_inv1_gram A M N j sum x agg.result i #:depth 10))
(define (gemv_ps M N A x gemv_rv) (gemv_ps_gram M N A x gemv_rv #:depth 10))

(define (MATRIX_OUTER_LOOP_INDEX_FIRST ) (MATRIX_OUTER_LOOP_INDEX_FIRST_gram  #:depth 10))
(define (VECTOR_OUTER_LOOP_INDEX ) (VECTOR_OUTER_LOOP_INDEX_gram  #:depth 10))

(define-symbolic A_BOUNDEDSET-len integer?)
(define-symbolic A_BOUNDEDSET-0 integer?)
(define-symbolic A_BOUNDEDSET-1 integer?)
(define-symbolic A_BOUNDEDSET-2 integer?)
(define-symbolic A_BOUNDEDSET-3 integer?)
(define-symbolic A_BOUNDEDSET-4 integer?)
(define-symbolic A_BOUNDEDSET-5 integer?)
(define-symbolic A_BOUNDEDSET-6 integer?)
(define-symbolic A_BOUNDEDSET-7 integer?)
(define-symbolic A_BOUNDEDSET-8 integer?)
(define-symbolic A_BOUNDEDSET-9 integer?)
(define-symbolic A_BOUNDEDSET-10 integer?)
(define-symbolic A_BOUNDEDSET-11 integer?)
(define-symbolic A_BOUNDEDSET-12 integer?)
(define-symbolic A_BOUNDEDSET-13 integer?)
(define-symbolic A_BOUNDEDSET-14 integer?)
(define-symbolic A_BOUNDEDSET-15 integer?)
(define A (take (list (list A_BOUNDEDSET-0 A_BOUNDEDSET-1 A_BOUNDEDSET-2 A_BOUNDEDSET-3) (list A_BOUNDEDSET-4 A_BOUNDEDSET-5 A_BOUNDEDSET-6 A_BOUNDEDSET-7) (list A_BOUNDEDSET-8 A_BOUNDEDSET-9 A_BOUNDEDSET-10 A_BOUNDEDSET-11) (list A_BOUNDEDSET-12 A_BOUNDEDSET-13 A_BOUNDEDSET-14 A_BOUNDEDSET-15)) A_BOUNDEDSET-len))
(define-symbolic M integer?)
(define-symbolic N integer?)
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3) agg.result_BOUNDEDSET-len))
(define-symbolic gemv_rv_BOUNDEDSET-len integer?)
(define-symbolic gemv_rv_BOUNDEDSET-0 integer?)
(define-symbolic gemv_rv_BOUNDEDSET-1 integer?)
(define-symbolic gemv_rv_BOUNDEDSET-2 integer?)
(define-symbolic gemv_rv_BOUNDEDSET-3 integer?)
(define gemv_rv (take (list gemv_rv_BOUNDEDSET-0 gemv_rv_BOUNDEDSET-1 gemv_rv_BOUNDEDSET-2 gemv_rv_BOUNDEDSET-3) gemv_rv_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic j integer?)
(define-symbolic sum integer?)
(define-symbolic x_BOUNDEDSET-len integer?)
(define-symbolic x_BOUNDEDSET-0 integer?)
(define-symbolic x_BOUNDEDSET-1 integer?)
(define-symbolic x_BOUNDEDSET-2 integer?)
(define-symbolic x_BOUNDEDSET-3 integer?)
(define x (take (list x_BOUNDEDSET-0 x_BOUNDEDSET-1 x_BOUNDEDSET-2 x_BOUNDEDSET-3) x_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (&& (&& (>= M 1 ) (>= N 1 ) ) (>= (matrix-length A ) M ) ) (>= (length (matrix-ref-noerr A 0 ) ) N ) ) (>= (length x ) N ) ) (gemv_inv0 A M N (list-empty ) 0 0 0 x) ) (=> (&& (&& (&& (&& (&& (&& (< i M ) (>= M 1 ) ) (>= N 1 ) ) (>= (matrix-length A ) M ) ) (>= (length (matrix-ref-noerr A 0 ) ) N ) ) (>= (length x ) N ) ) (gemv_inv0 A M N agg.result i j sum x) ) (gemv_inv1 A M N 0 0 x agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (< j N ) (< i M ) ) (>= M 1 ) ) (>= N 1 ) ) (>= (matrix-length A ) M ) ) (>= (length (matrix-ref-noerr A 0 ) ) N ) ) (>= (length x ) N ) ) (gemv_inv0 A M N agg.result i j sum x) ) (gemv_inv1 A M N j sum x agg.result i) ) (gemv_inv1 A M N (+ j 1 ) (+ sum (* (list-ref-noerr (matrix-ref-noerr A i ) j ) (list-ref-noerr x j ) ) ) x agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (! (< j N ) ) (< i M ) ) (>= M 1 ) ) (>= N 1 ) ) (>= (matrix-length A ) M ) ) (>= (length (matrix-ref-noerr A 0 ) ) N ) ) (>= (length x ) N ) ) (gemv_inv0 A M N agg.result i j sum x) ) (gemv_inv1 A M N j sum x agg.result i) ) (gemv_inv0 A M N (list-append agg.result sum ) (+ i 1 ) j sum x) ) ) (=> (or (&& (&& (&& (&& (&& (&& (! (< i M ) ) (>= M 1 ) ) (>= N 1 ) ) (>= (matrix-length A ) M ) ) (>= (length (matrix-ref-noerr A 0 ) ) N ) ) (>= (length x ) N ) ) (gemv_inv0 A M N agg.result i j sum x) ) (&& (&& (&& (&& (&& (&& (&& (! true ) (! (< i M ) ) ) (>= M 1 ) ) (>= N 1 ) ) (>= (matrix-length A ) M ) ) (>= (length (matrix-ref-noerr A 0 ) ) N ) ) (>= (length x ) N ) ) (gemv_inv0 A M N agg.result i j sum x) ) ) (gemv_ps M N A x agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list A_BOUNDEDSET-len A_BOUNDEDSET-0 A_BOUNDEDSET-1 A_BOUNDEDSET-2 A_BOUNDEDSET-3 A_BOUNDEDSET-4 A_BOUNDEDSET-5 A_BOUNDEDSET-6 A_BOUNDEDSET-7 A_BOUNDEDSET-8 A_BOUNDEDSET-9 A_BOUNDEDSET-10 A_BOUNDEDSET-11 A_BOUNDEDSET-12 A_BOUNDEDSET-13 A_BOUNDEDSET-14 A_BOUNDEDSET-15 M N agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 gemv_rv_BOUNDEDSET-len gemv_rv_BOUNDEDSET-0 gemv_rv_BOUNDEDSET-1 gemv_rv_BOUNDEDSET-2 gemv_rv_BOUNDEDSET-3 i j sum x_BOUNDEDSET-len x_BOUNDEDSET-0 x_BOUNDEDSET-1 x_BOUNDEDSET-2 x_BOUNDEDSET-3)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
