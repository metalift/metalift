#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_elemwise_add x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (+ (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_add (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (matrix_elemwise_add matrix_x matrix_y)
(if (or (< (matrix-length matrix_x ) 1 ) (! (equal? (matrix-length matrix_x ) (matrix-length matrix_y ) ) ) ) (matrix-empty ) (matrix-prepend (vec_elemwise_add (matrix-ref-noerr matrix_x 0 ) (matrix-ref-noerr matrix_y 0 )) (matrix_elemwise_add (matrix-tail-noerr matrix_x 1 ) (matrix-tail-noerr matrix_y 1 ) ) ) ))

(define-grammar (matrix_add_matrix_inv0_gram agg.result from_matrix i j ref.tmp row_vec to_matrix)
 [rv (choose (&& (&& (>= i 0 ) (<= i (matrix-length from_matrix ) ) ) (equal? agg.result (matrix_elemwise_add (v0) (v0) ) ) ))]
[v0 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-take-noerr (v1) i ) (matrix-col-slice-noerr (v1) 0 i ) ) (matrix-transpose-noerr (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-take-noerr (v1) i ) (matrix-col-slice-noerr (v1) 0 i ) ) ))]
[v1 (choose from_matrix to_matrix)]
)

(define-grammar (matrix_add_matrix_inv1_gram from_matrix j ref.tmp row_vec to_matrix agg.result i)
 [rv (choose (&& (&& (&& (&& (&& (>= i 0 ) (< i (matrix-length from_matrix ) ) ) (>= j 0 ) ) (<= j (length (matrix-ref-noerr from_matrix 0 ) ) ) ) (equal? row_vec (vec_elemwise_add (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-take-noerr (matrix-ref-noerr (v0) i ) j ) (matrix-ref-noerr (matrix-transpose-noerr (matrix-col-slice-with-length-noerr (matrix-take-noerr (v0) j ) i 1 ) ) 0 ) ) (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-take-noerr (matrix-ref-noerr (v0) i ) j ) (matrix-ref-noerr (matrix-transpose-noerr (matrix-col-slice-with-length-noerr (matrix-take-noerr (v0) j ) i 1 ) ) 0 ) )) ) ) (equal? agg.result (matrix_elemwise_add (v1) (v1) ) ) ))]
[v0 (choose from_matrix to_matrix)]
[v1 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-take-noerr (v0) i ) (matrix-col-slice-noerr (v0) 0 i ) ) (matrix-transpose-noerr (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-take-noerr (v0) i ) (matrix-col-slice-noerr (v0) 0 i ) ) ))]
)

(define-grammar (matrix_add_matrix_ps_gram from_matrix to_matrix matrix_add_matrix_rv)
 [rv (choose (equal? matrix_add_matrix_rv (matrix_elemwise_add (v0) (v0) ) ))]
[v0 (choose (v1) (matrix-transpose-noerr (v1) ))]
[v1 (choose from_matrix to_matrix)]
)

(define-grammar (MATRIX_OUTER_LOOP_INDEX_FIRST_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
)

(define (matrix_add_matrix_inv0 agg.result from_matrix i j ref.tmp row_vec to_matrix) (matrix_add_matrix_inv0_gram agg.result from_matrix i j ref.tmp row_vec to_matrix #:depth 10))
(define (matrix_add_matrix_inv1 from_matrix j ref.tmp row_vec to_matrix agg.result i) (matrix_add_matrix_inv1_gram from_matrix j ref.tmp row_vec to_matrix agg.result i #:depth 10))
(define (matrix_add_matrix_ps from_matrix to_matrix matrix_add_matrix_rv) (matrix_add_matrix_ps_gram from_matrix to_matrix matrix_add_matrix_rv #:depth 10))

(define (MATRIX_OUTER_LOOP_INDEX_FIRST ) (MATRIX_OUTER_LOOP_INDEX_FIRST_gram  #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define agg.result (take (list (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) (list agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3)) agg.result_BOUNDEDSET-len))
(define-symbolic from_matrix_BOUNDEDSET-len integer?)
(define-symbolic from_matrix_BOUNDEDSET-0 integer?)
(define-symbolic from_matrix_BOUNDEDSET-1 integer?)
(define-symbolic from_matrix_BOUNDEDSET-2 integer?)
(define-symbolic from_matrix_BOUNDEDSET-3 integer?)
(define from_matrix (take (list (list from_matrix_BOUNDEDSET-0 from_matrix_BOUNDEDSET-1) (list from_matrix_BOUNDEDSET-2 from_matrix_BOUNDEDSET-3)) from_matrix_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic j integer?)
(define-symbolic matrix_add_matrix_rv_BOUNDEDSET-len integer?)
(define-symbolic matrix_add_matrix_rv_BOUNDEDSET-0 integer?)
(define-symbolic matrix_add_matrix_rv_BOUNDEDSET-1 integer?)
(define-symbolic matrix_add_matrix_rv_BOUNDEDSET-2 integer?)
(define-symbolic matrix_add_matrix_rv_BOUNDEDSET-3 integer?)
(define matrix_add_matrix_rv (take (list (list matrix_add_matrix_rv_BOUNDEDSET-0 matrix_add_matrix_rv_BOUNDEDSET-1) (list matrix_add_matrix_rv_BOUNDEDSET-2 matrix_add_matrix_rv_BOUNDEDSET-3)) matrix_add_matrix_rv_BOUNDEDSET-len))
(define-symbolic ref.tmp integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1) row_vec_BOUNDEDSET-len))
(define-symbolic to_matrix_BOUNDEDSET-len integer?)
(define-symbolic to_matrix_BOUNDEDSET-0 integer?)
(define-symbolic to_matrix_BOUNDEDSET-1 integer?)
(define-symbolic to_matrix_BOUNDEDSET-2 integer?)
(define-symbolic to_matrix_BOUNDEDSET-3 integer?)
(define to_matrix (take (list (list to_matrix_BOUNDEDSET-0 to_matrix_BOUNDEDSET-1) (list to_matrix_BOUNDEDSET-2 to_matrix_BOUNDEDSET-3)) to_matrix_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (> (matrix-length from_matrix ) 1 ) (equal? (matrix-length from_matrix ) (matrix-length to_matrix ) ) ) (equal? (length (matrix-ref-noerr from_matrix 0 ) ) (length (matrix-ref-noerr to_matrix 0 ) ) ) ) (matrix_add_matrix_inv0 (matrix-empty ) from_matrix 0 0 0 (list-empty ) to_matrix ) ) (=> (&& (&& (&& (&& (< i (matrix-length from_matrix ) ) (> (matrix-length from_matrix ) 1 ) ) (equal? (matrix-length from_matrix ) (matrix-length to_matrix ) ) ) (equal? (length (matrix-ref-noerr from_matrix 0 ) ) (length (matrix-ref-noerr to_matrix 0 ) ) ) ) (matrix_add_matrix_inv0 agg.result from_matrix i j ref.tmp row_vec to_matrix ) ) (matrix_add_matrix_inv1 from_matrix 0 ref.tmp (list-empty ) to_matrix agg.result i ) ) ) (=> (&& (&& (&& (&& (&& (&& (< j (length (matrix-ref-noerr from_matrix 0 ) ) ) (< i (matrix-length from_matrix ) ) ) (> (matrix-length from_matrix ) 1 ) ) (equal? (matrix-length from_matrix ) (matrix-length to_matrix ) ) ) (equal? (length (matrix-ref-noerr from_matrix 0 ) ) (length (matrix-ref-noerr to_matrix 0 ) ) ) ) (matrix_add_matrix_inv0 agg.result from_matrix i j ref.tmp row_vec to_matrix ) ) (matrix_add_matrix_inv1 from_matrix j ref.tmp row_vec to_matrix agg.result i ) ) (matrix_add_matrix_inv1 from_matrix (+ j 1 ) (+ (list-ref-noerr (matrix-ref-noerr from_matrix i ) j ) (list-ref-noerr (matrix-ref-noerr to_matrix i ) j ) ) (list-append row_vec (+ (list-ref-noerr (matrix-ref-noerr from_matrix i ) j ) (list-ref-noerr (matrix-ref-noerr to_matrix i ) j ) ) ) to_matrix agg.result i ) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< j (length (matrix-ref-noerr from_matrix 0 ) ) ) ) (< i (matrix-length from_matrix ) ) ) (> (matrix-length from_matrix ) 1 ) ) (equal? (matrix-length from_matrix ) (matrix-length to_matrix ) ) ) (equal? (length (matrix-ref-noerr from_matrix 0 ) ) (length (matrix-ref-noerr to_matrix 0 ) ) ) ) (matrix_add_matrix_inv0 agg.result from_matrix i j ref.tmp row_vec to_matrix ) ) (matrix_add_matrix_inv1 from_matrix j ref.tmp row_vec to_matrix agg.result i ) ) (matrix_add_matrix_inv0 (matrix-append agg.result row_vec ) from_matrix (+ i 1 ) j ref.tmp row_vec to_matrix ) ) ) (=> (or (&& (&& (&& (&& (! (< i (matrix-length from_matrix ) ) ) (> (matrix-length from_matrix ) 1 ) ) (equal? (matrix-length from_matrix ) (matrix-length to_matrix ) ) ) (equal? (length (matrix-ref-noerr from_matrix 0 ) ) (length (matrix-ref-noerr to_matrix 0 ) ) ) ) (matrix_add_matrix_inv0 agg.result from_matrix i j ref.tmp row_vec to_matrix ) ) (&& (&& (&& (&& (&& (! true ) (! (< i (matrix-length from_matrix ) ) ) ) (> (matrix-length from_matrix ) 1 ) ) (equal? (matrix-length from_matrix ) (matrix-length to_matrix ) ) ) (equal? (length (matrix-ref-noerr from_matrix 0 ) ) (length (matrix-ref-noerr to_matrix 0 ) ) ) ) (matrix_add_matrix_inv0 agg.result from_matrix i j ref.tmp row_vec to_matrix ) ) ) (matrix_add_matrix_ps from_matrix to_matrix agg.result ) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 from_matrix_BOUNDEDSET-len from_matrix_BOUNDEDSET-0 from_matrix_BOUNDEDSET-1 from_matrix_BOUNDEDSET-2 from_matrix_BOUNDEDSET-3 i j matrix_add_matrix_rv_BOUNDEDSET-len matrix_add_matrix_rv_BOUNDEDSET-0 matrix_add_matrix_rv_BOUNDEDSET-1 matrix_add_matrix_rv_BOUNDEDSET-2 matrix_add_matrix_rv_BOUNDEDSET-3 ref.tmp row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 to_matrix_BOUNDEDSET-len to_matrix_BOUNDEDSET-0 to_matrix_BOUNDEDSET-1 to_matrix_BOUNDEDSET-2 to_matrix_BOUNDEDSET-3)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
