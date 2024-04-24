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

(define-grammar (matscal_inv0_gram agg.result i j m mat n ref.tmp row_vec val)
 [rv (choose (&& (&& (>= i 0 ) (<= i m ) ) (equal? agg.result (matrix_scalar_mul (v0) (v1) ) ) ))]
[v0 (choose val)]
[v1 (choose (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v2) i ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v2) n ) 0 i ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v2) i ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v2) n ) 0 i ) ) ))]
[v2 (choose mat)]
)

(define-grammar (matscal_inv1_gram j m mat n ref.tmp row_vec val agg.result i)
 [rv (choose (&& (&& (&& (&& (&& (>= i 0 ) (< i m ) ) (>= j 0 ) ) (<= j n ) ) (equal? row_vec (vec_scalar_mul (v0) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (matrix-ref-noerr (v1) i ) j ) (matrix-ref-noerr (matrix-transpose-noerr (matrix-col-slice-with-length-noerr (matrix-take-noerr (v1) j ) i 1 ) ) 0 ) ) ) ) ) (equal? agg.result (matrix_scalar_mul (v0) (v2) ) ) ))]
[v0 (choose val)]
[v1 (choose mat)]
[v2 (choose (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v1) i ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v1) n ) 0 i ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v1) i ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v1) n ) 0 i ) ) ))]
)

(define-grammar (matscal_ps_gram mat val m n matscal_rv)
 [rv (choose (equal? matscal_rv (matrix_scalar_mul (v0) (v1) ) ))]
[v0 (choose val)]
[v1 (choose (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v2) m ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v2) n ) 0 m ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v2) m ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v2) n ) 0 m ) ) ))]
[v2 (choose mat)]
)

(define-grammar (OUTER_LOOP_INDEX_FIRST_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
)

(define (matscal_inv0 agg.result i j m mat n ref.tmp row_vec val) (matscal_inv0_gram agg.result i j m mat n ref.tmp row_vec val #:depth 10))
(define (matscal_inv1 j m mat n ref.tmp row_vec val agg.result i) (matscal_inv1_gram j m mat n ref.tmp row_vec val agg.result i #:depth 10))
(define (matscal_ps mat val m n matscal_rv) (matscal_ps_gram mat val m n matscal_rv #:depth 10))

(define (OUTER_LOOP_INDEX_FIRST ) (OUTER_LOOP_INDEX_FIRST_gram  #:depth 10))

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
(define-symbolic m integer?)
(define-symbolic mat_BOUNDEDSET-len integer?)
(define-symbolic mat_BOUNDEDSET-0 integer?)
(define-symbolic mat_BOUNDEDSET-1 integer?)
(define-symbolic mat_BOUNDEDSET-2 integer?)
(define-symbolic mat_BOUNDEDSET-3 integer?)
(define-symbolic mat_BOUNDEDSET-4 integer?)
(define-symbolic mat_BOUNDEDSET-5 integer?)
(define-symbolic mat_BOUNDEDSET-6 integer?)
(define-symbolic mat_BOUNDEDSET-7 integer?)
(define-symbolic mat_BOUNDEDSET-8 integer?)
(define-symbolic mat_BOUNDEDSET-9 integer?)
(define-symbolic mat_BOUNDEDSET-10 integer?)
(define-symbolic mat_BOUNDEDSET-11 integer?)
(define-symbolic mat_BOUNDEDSET-12 integer?)
(define-symbolic mat_BOUNDEDSET-13 integer?)
(define-symbolic mat_BOUNDEDSET-14 integer?)
(define-symbolic mat_BOUNDEDSET-15 integer?)
(define mat (take (list (list mat_BOUNDEDSET-0 mat_BOUNDEDSET-1 mat_BOUNDEDSET-2 mat_BOUNDEDSET-3) (list mat_BOUNDEDSET-4 mat_BOUNDEDSET-5 mat_BOUNDEDSET-6 mat_BOUNDEDSET-7) (list mat_BOUNDEDSET-8 mat_BOUNDEDSET-9 mat_BOUNDEDSET-10 mat_BOUNDEDSET-11) (list mat_BOUNDEDSET-12 mat_BOUNDEDSET-13 mat_BOUNDEDSET-14 mat_BOUNDEDSET-15)) mat_BOUNDEDSET-len))
(define-symbolic matscal_rv_BOUNDEDSET-len integer?)
(define-symbolic matscal_rv_BOUNDEDSET-0 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-1 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-2 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-3 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-4 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-5 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-6 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-7 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-8 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-9 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-10 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-11 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-12 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-13 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-14 integer?)
(define-symbolic matscal_rv_BOUNDEDSET-15 integer?)
(define matscal_rv (take (list (list matscal_rv_BOUNDEDSET-0 matscal_rv_BOUNDEDSET-1 matscal_rv_BOUNDEDSET-2 matscal_rv_BOUNDEDSET-3) (list matscal_rv_BOUNDEDSET-4 matscal_rv_BOUNDEDSET-5 matscal_rv_BOUNDEDSET-6 matscal_rv_BOUNDEDSET-7) (list matscal_rv_BOUNDEDSET-8 matscal_rv_BOUNDEDSET-9 matscal_rv_BOUNDEDSET-10 matscal_rv_BOUNDEDSET-11) (list matscal_rv_BOUNDEDSET-12 matscal_rv_BOUNDEDSET-13 matscal_rv_BOUNDEDSET-14 matscal_rv_BOUNDEDSET-15)) matscal_rv_BOUNDEDSET-len))
(define-symbolic n integer?)
(define-symbolic ref.tmp integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define-symbolic row_vec_BOUNDEDSET-2 integer?)
(define-symbolic row_vec_BOUNDEDSET-3 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 row_vec_BOUNDEDSET-2 row_vec_BOUNDEDSET-3) row_vec_BOUNDEDSET-len))
(define-symbolic val integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (&& (>= m 1 ) (>= n 1 ) ) (>= (matrix-length mat ) m ) ) (>= (length (matrix-ref-noerr mat 0 ) ) n ) ) (matscal_inv0 (matrix-empty ) 0 0 m mat n 0 (list-empty ) val) ) (=> (&& (&& (&& (&& (&& (< i m ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length mat ) m ) ) (>= (length (matrix-ref-noerr mat 0 ) ) n ) ) (matscal_inv0 agg.result i j m mat n ref.tmp row_vec val) ) (matscal_inv1 0 m mat n ref.tmp (list-empty ) val agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (< j n ) (< i m ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length mat ) m ) ) (>= (length (matrix-ref-noerr mat 0 ) ) n ) ) (matscal_inv0 agg.result i j m mat n ref.tmp row_vec val) ) (matscal_inv1 j m mat n ref.tmp row_vec val agg.result i) ) (matscal_inv1 (+ j 1 ) m mat n (* (list-ref-noerr (matrix-ref-noerr mat i ) j ) val ) (list-append row_vec (* (list-ref-noerr (matrix-ref-noerr mat i ) j ) val ) ) val agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (! (< j n ) ) (< i m ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length mat ) m ) ) (>= (length (matrix-ref-noerr mat 0 ) ) n ) ) (matscal_inv0 agg.result i j m mat n ref.tmp row_vec val) ) (matscal_inv1 j m mat n ref.tmp row_vec val agg.result i) ) (matscal_inv0 (matrix-append agg.result row_vec ) (+ i 1 ) j m mat n ref.tmp row_vec val) ) ) (=> (or (&& (&& (&& (&& (&& (! (< i m ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length mat ) m ) ) (>= (length (matrix-ref-noerr mat 0 ) ) n ) ) (matscal_inv0 agg.result i j m mat n ref.tmp row_vec val) ) (&& (&& (&& (&& (&& (&& (! true ) (! (< i m ) ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length mat ) m ) ) (>= (length (matrix-ref-noerr mat 0 ) ) n ) ) (matscal_inv0 agg.result i j m mat n ref.tmp row_vec val) ) ) (matscal_ps mat val m n agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4 agg.result_BOUNDEDSET-5 agg.result_BOUNDEDSET-6 agg.result_BOUNDEDSET-7 agg.result_BOUNDEDSET-8 agg.result_BOUNDEDSET-9 agg.result_BOUNDEDSET-10 agg.result_BOUNDEDSET-11 agg.result_BOUNDEDSET-12 agg.result_BOUNDEDSET-13 agg.result_BOUNDEDSET-14 agg.result_BOUNDEDSET-15 i j m mat_BOUNDEDSET-len mat_BOUNDEDSET-0 mat_BOUNDEDSET-1 mat_BOUNDEDSET-2 mat_BOUNDEDSET-3 mat_BOUNDEDSET-4 mat_BOUNDEDSET-5 mat_BOUNDEDSET-6 mat_BOUNDEDSET-7 mat_BOUNDEDSET-8 mat_BOUNDEDSET-9 mat_BOUNDEDSET-10 mat_BOUNDEDSET-11 mat_BOUNDEDSET-12 mat_BOUNDEDSET-13 mat_BOUNDEDSET-14 mat_BOUNDEDSET-15 matscal_rv_BOUNDEDSET-len matscal_rv_BOUNDEDSET-0 matscal_rv_BOUNDEDSET-1 matscal_rv_BOUNDEDSET-2 matscal_rv_BOUNDEDSET-3 matscal_rv_BOUNDEDSET-4 matscal_rv_BOUNDEDSET-5 matscal_rv_BOUNDEDSET-6 matscal_rv_BOUNDEDSET-7 matscal_rv_BOUNDEDSET-8 matscal_rv_BOUNDEDSET-9 matscal_rv_BOUNDEDSET-10 matscal_rv_BOUNDEDSET-11 matscal_rv_BOUNDEDSET-12 matscal_rv_BOUNDEDSET-13 matscal_rv_BOUNDEDSET-14 matscal_rv_BOUNDEDSET-15 n ref.tmp row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 row_vec_BOUNDEDSET-2 row_vec_BOUNDEDSET-3 val)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
