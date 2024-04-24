#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 )) ) ))


 (define-bounded (matrix_scalar_mul a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (vec_scalar_mul a (matrix-ref-noerr matrix_x 0 )) (matrix_scalar_mul a (matrix-tail-noerr matrix_x 1 ) ) ) ))

(define-grammar (matmul_sca_inv0_gram agg.result i j m matA n ref.tmp row_vec val)
 [rv (choose (&& (&& (>= i 0 ) (<= i m ) ) (equal? agg.result (matrix_scalar_mul (v0) (v1) ) ) ))]
[v0 (choose val)]
[v1 (choose (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v2) i ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v2) n ) 0 i ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v2) i ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v2) n ) 0 i ) ) ))]
[v2 (choose matA)]
)

(define-grammar (matmul_sca_inv1_gram j m matA n ref.tmp row_vec val agg.result i)
 [rv (choose (&& (&& (&& (&& (&& (>= i 0 ) (< i m ) ) (>= j 0 ) ) (<= j n ) ) (equal? row_vec (vec_scalar_mul (v0) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (matrix-ref-noerr (v1) i ) j ) (matrix-ref-noerr (matrix-transpose-noerr (matrix-col-slice-with-length-noerr (matrix-take-noerr (v1) j ) i 1 ) ) 0 ) )) ) ) (equal? agg.result (matrix_scalar_mul (v0) (v2) ) ) ))]
[v0 (choose val)]
[v1 (choose matA)]
[v2 (choose (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v1) i ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v1) n ) 0 i ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v1) i ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v1) n ) 0 i ) ) ))]
)

(define-grammar (matmul_sca_ps_gram matA val m n matmul_sca_rv)
 [rv (choose (equal? matmul_sca_rv (matrix_scalar_mul (v0) (v1) ) ))]
[v0 (choose val)]
[v1 (choose (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v2) m ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v2) n ) 0 m ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v2) m ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v2) n ) 0 m ) ) ))]
[v2 (choose matA)]
)

(define-grammar (OUTER_LOOP_INDEX_FIRST_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
)

(define (matmul_sca_inv0 agg.result i j m matA n ref.tmp row_vec val) (matmul_sca_inv0_gram agg.result i j m matA n ref.tmp row_vec val #:depth 10))
(define (matmul_sca_inv1 j m matA n ref.tmp row_vec val agg.result i) (matmul_sca_inv1_gram j m matA n ref.tmp row_vec val agg.result i #:depth 10))
(define (matmul_sca_ps matA val m n matmul_sca_rv) (matmul_sca_ps_gram matA val m n matmul_sca_rv #:depth 10))

(define (OUTER_LOOP_INDEX_FIRST ) (OUTER_LOOP_INDEX_FIRST_gram  #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define agg.result (take (list (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) (list agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3)) agg.result_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic j integer?)
(define-symbolic m integer?)
(define-symbolic matA_BOUNDEDSET-len integer?)
(define-symbolic matA_BOUNDEDSET-0 integer?)
(define-symbolic matA_BOUNDEDSET-1 integer?)
(define-symbolic matA_BOUNDEDSET-2 integer?)
(define-symbolic matA_BOUNDEDSET-3 integer?)
(define matA (take (list (list matA_BOUNDEDSET-0 matA_BOUNDEDSET-1) (list matA_BOUNDEDSET-2 matA_BOUNDEDSET-3)) matA_BOUNDEDSET-len))
(define-symbolic matmul_sca_rv_BOUNDEDSET-len integer?)
(define-symbolic matmul_sca_rv_BOUNDEDSET-0 integer?)
(define-symbolic matmul_sca_rv_BOUNDEDSET-1 integer?)
(define-symbolic matmul_sca_rv_BOUNDEDSET-2 integer?)
(define-symbolic matmul_sca_rv_BOUNDEDSET-3 integer?)
(define matmul_sca_rv (take (list (list matmul_sca_rv_BOUNDEDSET-0 matmul_sca_rv_BOUNDEDSET-1) (list matmul_sca_rv_BOUNDEDSET-2 matmul_sca_rv_BOUNDEDSET-3)) matmul_sca_rv_BOUNDEDSET-len))
(define-symbolic n integer?)
(define-symbolic ref.tmp integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1) row_vec_BOUNDEDSET-len))
(define-symbolic val integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (&& (>= m 1 ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (matmul_sca_inv0 (matrix-empty ) 0 0 m matA n 0 (list-empty ) val) ) (=> (&& (&& (&& (&& (&& (< i m ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (matmul_sca_inv0 agg.result i j m matA n ref.tmp row_vec val) ) (matmul_sca_inv1 0 m matA n ref.tmp (list-empty ) val agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (< j n ) (< i m ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (matmul_sca_inv0 agg.result i j m matA n ref.tmp row_vec val) ) (matmul_sca_inv1 j m matA n ref.tmp row_vec val agg.result i) ) (matmul_sca_inv1 (+ j 1 ) m matA n (* (list-ref-noerr (matrix-ref-noerr matA i ) j ) val ) (list-append row_vec (* (list-ref-noerr (matrix-ref-noerr matA i ) j ) val ) ) val agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (! (< j n ) ) (< i m ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (matmul_sca_inv0 agg.result i j m matA n ref.tmp row_vec val) ) (matmul_sca_inv1 j m matA n ref.tmp row_vec val agg.result i) ) (matmul_sca_inv0 (matrix-append agg.result row_vec ) (+ i 1 ) j m matA n ref.tmp row_vec val) ) ) (=> (or (&& (&& (&& (&& (&& (! (< i m ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (matmul_sca_inv0 agg.result i j m matA n ref.tmp row_vec val) ) (&& (&& (&& (&& (&& (&& (! true ) (! (< i m ) ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (matmul_sca_inv0 agg.result i j m matA n ref.tmp row_vec val) ) ) (matmul_sca_ps matA val m n agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 i j m matA_BOUNDEDSET-len matA_BOUNDEDSET-0 matA_BOUNDEDSET-1 matA_BOUNDEDSET-2 matA_BOUNDEDSET-3 matmul_sca_rv_BOUNDEDSET-len matmul_sca_rv_BOUNDEDSET-0 matmul_sca_rv_BOUNDEDSET-1 matmul_sca_rv_BOUNDEDSET-2 matmul_sca_rv_BOUNDEDSET-3 n ref.tmp row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 val)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
