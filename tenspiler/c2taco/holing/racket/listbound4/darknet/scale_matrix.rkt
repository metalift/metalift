#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 ) ) ) ))


 (define-bounded (matrix_scalar_mul a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (vec_scalar_mul a (matrix-ref-noerr matrix_x 0 ) ) (matrix_scalar_mul a (matrix-tail-noerr matrix_x 1 ) ) ) ))

(define-grammar (scale_matrix_inv0_gram agg.result i j m ref.tmp row_vec scale)
 [rv (choose (&& (&& (>= i 0 ) (<= i (matrix-length m ) ) ) (equal? agg.result (matrix_scalar_mul (v0) (v1) ) ) ))]
[v0 (choose scale)]
[v1 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-take-noerr (v2) i ) (matrix-col-slice-noerr (v2) 0 i ) ) (matrix-transpose-noerr (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-take-noerr (v2) i ) (matrix-col-slice-noerr (v2) 0 i ) ) ))]
[v2 (choose m)]
)

(define-grammar (scale_matrix_inv1_gram j m ref.tmp row_vec scale agg.result i)
 [rv (choose (&& (&& (&& (&& (&& (>= i 0 ) (< i (matrix-length m ) ) ) (>= j 0 ) ) (<= j (length (matrix-ref-noerr m 0 ) ) ) ) (equal? row_vec (vec_scalar_mul (v0) (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-take-noerr (matrix-ref-noerr (v1) i ) j ) (matrix-ref-noerr (matrix-transpose-noerr (matrix-col-slice-with-length-noerr (matrix-take-noerr (v1) j ) i 1 ) ) 0 ) ) ) ) ) (equal? agg.result (matrix_scalar_mul (v0) (v2) ) ) ))]
[v0 (choose scale)]
[v1 (choose m)]
[v2 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-take-noerr (v1) i ) (matrix-col-slice-noerr (v1) 0 i ) ) (matrix-transpose-noerr (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (matrix-take-noerr (v1) i ) (matrix-col-slice-noerr (v1) 0 i ) ) ))]
)

(define-grammar (scale_matrix_ps_gram m scale scale_matrix_rv)
 [rv (choose (equal? scale_matrix_rv (matrix_scalar_mul (v0) (v1) ) ))]
[v0 (choose scale)]
[v1 (choose (v2) (matrix-transpose-noerr (v2) ))]
[v2 (choose m)]
)

(define-grammar (MATRIX_OUTER_LOOP_INDEX_FIRST_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
)

(define (scale_matrix_inv0 agg.result i j m ref.tmp row_vec scale) (scale_matrix_inv0_gram agg.result i j m ref.tmp row_vec scale #:depth 10))
(define (scale_matrix_inv1 j m ref.tmp row_vec scale agg.result i) (scale_matrix_inv1_gram j m ref.tmp row_vec scale agg.result i #:depth 10))
(define (scale_matrix_ps m scale scale_matrix_rv) (scale_matrix_ps_gram m scale scale_matrix_rv #:depth 10))

(define (MATRIX_OUTER_LOOP_INDEX_FIRST ) (MATRIX_OUTER_LOOP_INDEX_FIRST_gram  #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define-symbolic agg.result_BOUNDEDSET-4 integer?)
(define-symbolic agg.result_BOUNDEDSET-5 integer?)
(define-symbolic agg.result_BOUNDEDSET-6 integer?)
(define-symbolic agg.result_BOUNDEDSET-7 integer?)
(define-symbolic agg.result_BOUNDEDSET-8 integer?)
(define-symbolic agg.result_BOUNDEDSET-9 integer?)
(define-symbolic agg.result_BOUNDEDSET-10 integer?)
(define-symbolic agg.result_BOUNDEDSET-11 integer?)
(define-symbolic agg.result_BOUNDEDSET-12 integer?)
(define-symbolic agg.result_BOUNDEDSET-13 integer?)
(define-symbolic agg.result_BOUNDEDSET-14 integer?)
(define-symbolic agg.result_BOUNDEDSET-15 integer?)
(define agg.result (take (list (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3) (list agg.result_BOUNDEDSET-4 agg.result_BOUNDEDSET-5 agg.result_BOUNDEDSET-6 agg.result_BOUNDEDSET-7) (list agg.result_BOUNDEDSET-8 agg.result_BOUNDEDSET-9 agg.result_BOUNDEDSET-10 agg.result_BOUNDEDSET-11) (list agg.result_BOUNDEDSET-12 agg.result_BOUNDEDSET-13 agg.result_BOUNDEDSET-14 agg.result_BOUNDEDSET-15)) agg.result_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic j integer?)
(define-symbolic m_BOUNDEDSET-len integer?)
(define-symbolic m_BOUNDEDSET-0 integer?)
(define-symbolic m_BOUNDEDSET-1 integer?)
(define-symbolic m_BOUNDEDSET-2 integer?)
(define-symbolic m_BOUNDEDSET-3 integer?)
(define-symbolic m_BOUNDEDSET-4 integer?)
(define-symbolic m_BOUNDEDSET-5 integer?)
(define-symbolic m_BOUNDEDSET-6 integer?)
(define-symbolic m_BOUNDEDSET-7 integer?)
(define-symbolic m_BOUNDEDSET-8 integer?)
(define-symbolic m_BOUNDEDSET-9 integer?)
(define-symbolic m_BOUNDEDSET-10 integer?)
(define-symbolic m_BOUNDEDSET-11 integer?)
(define-symbolic m_BOUNDEDSET-12 integer?)
(define-symbolic m_BOUNDEDSET-13 integer?)
(define-symbolic m_BOUNDEDSET-14 integer?)
(define-symbolic m_BOUNDEDSET-15 integer?)
(define m (take (list (list m_BOUNDEDSET-0 m_BOUNDEDSET-1 m_BOUNDEDSET-2 m_BOUNDEDSET-3) (list m_BOUNDEDSET-4 m_BOUNDEDSET-5 m_BOUNDEDSET-6 m_BOUNDEDSET-7) (list m_BOUNDEDSET-8 m_BOUNDEDSET-9 m_BOUNDEDSET-10 m_BOUNDEDSET-11) (list m_BOUNDEDSET-12 m_BOUNDEDSET-13 m_BOUNDEDSET-14 m_BOUNDEDSET-15)) m_BOUNDEDSET-len))
(define-symbolic ref.tmp integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define-symbolic row_vec_BOUNDEDSET-2 integer?)
(define-symbolic row_vec_BOUNDEDSET-3 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 row_vec_BOUNDEDSET-2 row_vec_BOUNDEDSET-3) row_vec_BOUNDEDSET-len))
(define-symbolic scale integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-len integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-0 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-1 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-2 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-3 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-4 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-5 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-6 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-7 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-8 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-9 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-10 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-11 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-12 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-13 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-14 integer?)
(define-symbolic scale_matrix_rv_BOUNDEDSET-15 integer?)
(define scale_matrix_rv (take (list (list scale_matrix_rv_BOUNDEDSET-0 scale_matrix_rv_BOUNDEDSET-1 scale_matrix_rv_BOUNDEDSET-2 scale_matrix_rv_BOUNDEDSET-3) (list scale_matrix_rv_BOUNDEDSET-4 scale_matrix_rv_BOUNDEDSET-5 scale_matrix_rv_BOUNDEDSET-6 scale_matrix_rv_BOUNDEDSET-7) (list scale_matrix_rv_BOUNDEDSET-8 scale_matrix_rv_BOUNDEDSET-9 scale_matrix_rv_BOUNDEDSET-10 scale_matrix_rv_BOUNDEDSET-11) (list scale_matrix_rv_BOUNDEDSET-12 scale_matrix_rv_BOUNDEDSET-13 scale_matrix_rv_BOUNDEDSET-14 scale_matrix_rv_BOUNDEDSET-15)) scale_matrix_rv_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (>= (matrix-length m ) 1 ) (>= (length (matrix-ref-noerr m 0 ) ) 1 ) ) (scale_matrix_inv0 (matrix-empty ) 0 0 m 0 (list-empty ) scale) ) (=> (&& (&& (&& (< i (matrix-length m ) ) (>= (matrix-length m ) 1 ) ) (>= (length (matrix-ref-noerr m 0 ) ) 1 ) ) (scale_matrix_inv0 agg.result i j m ref.tmp row_vec scale) ) (scale_matrix_inv1 0 m ref.tmp (list-empty ) scale agg.result i) ) ) (=> (&& (&& (&& (&& (&& (< j (length (matrix-ref-noerr m 0 ) ) ) (< i (matrix-length m ) ) ) (>= (matrix-length m ) 1 ) ) (>= (length (matrix-ref-noerr m 0 ) ) 1 ) ) (scale_matrix_inv0 agg.result i j m ref.tmp row_vec scale) ) (scale_matrix_inv1 j m ref.tmp row_vec scale agg.result i) ) (scale_matrix_inv1 (+ j 1 ) m (* (list-ref-noerr (matrix-ref-noerr m i ) j ) scale ) (list-append row_vec (* (list-ref-noerr (matrix-ref-noerr m i ) j ) scale ) ) scale agg.result i) ) ) (=> (&& (&& (&& (&& (&& (! (< j (length (matrix-ref-noerr m 0 ) ) ) ) (< i (matrix-length m ) ) ) (>= (matrix-length m ) 1 ) ) (>= (length (matrix-ref-noerr m 0 ) ) 1 ) ) (scale_matrix_inv0 agg.result i j m ref.tmp row_vec scale) ) (scale_matrix_inv1 j m ref.tmp row_vec scale agg.result i) ) (scale_matrix_inv0 (matrix-append agg.result row_vec ) (+ i 1 ) j m ref.tmp row_vec scale) ) ) (=> (or (&& (&& (&& (! (< i (matrix-length m ) ) ) (>= (matrix-length m ) 1 ) ) (>= (length (matrix-ref-noerr m 0 ) ) 1 ) ) (scale_matrix_inv0 agg.result i j m ref.tmp row_vec scale) ) (&& (&& (&& (&& (! true ) (! (< i (matrix-length m ) ) ) ) (>= (matrix-length m ) 1 ) ) (>= (length (matrix-ref-noerr m 0 ) ) 1 ) ) (scale_matrix_inv0 agg.result i j m ref.tmp row_vec scale) ) ) (scale_matrix_ps m scale agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4 agg.result_BOUNDEDSET-5 agg.result_BOUNDEDSET-6 agg.result_BOUNDEDSET-7 agg.result_BOUNDEDSET-8 agg.result_BOUNDEDSET-9 agg.result_BOUNDEDSET-10 agg.result_BOUNDEDSET-11 agg.result_BOUNDEDSET-12 agg.result_BOUNDEDSET-13 agg.result_BOUNDEDSET-14 agg.result_BOUNDEDSET-15 i j m_BOUNDEDSET-len m_BOUNDEDSET-0 m_BOUNDEDSET-1 m_BOUNDEDSET-2 m_BOUNDEDSET-3 m_BOUNDEDSET-4 m_BOUNDEDSET-5 m_BOUNDEDSET-6 m_BOUNDEDSET-7 m_BOUNDEDSET-8 m_BOUNDEDSET-9 m_BOUNDEDSET-10 m_BOUNDEDSET-11 m_BOUNDEDSET-12 m_BOUNDEDSET-13 m_BOUNDEDSET-14 m_BOUNDEDSET-15 ref.tmp row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 row_vec_BOUNDEDSET-2 row_vec_BOUNDEDSET-3 scale scale_matrix_rv_BOUNDEDSET-len scale_matrix_rv_BOUNDEDSET-0 scale_matrix_rv_BOUNDEDSET-1 scale_matrix_rv_BOUNDEDSET-2 scale_matrix_rv_BOUNDEDSET-3 scale_matrix_rv_BOUNDEDSET-4 scale_matrix_rv_BOUNDEDSET-5 scale_matrix_rv_BOUNDEDSET-6 scale_matrix_rv_BOUNDEDSET-7 scale_matrix_rv_BOUNDEDSET-8 scale_matrix_rv_BOUNDEDSET-9 scale_matrix_rv_BOUNDEDSET-10 scale_matrix_rv_BOUNDEDSET-11 scale_matrix_rv_BOUNDEDSET-12 scale_matrix_rv_BOUNDEDSET-13 scale_matrix_rv_BOUNDEDSET-14 scale_matrix_rv_BOUNDEDSET-15)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
