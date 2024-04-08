#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_elemwise_sub x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_sub (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (matrix_elemwise_sub matrix_x matrix_y)
(if (or (< (matrix-length matrix_x ) 1 ) (! (equal? (matrix-length matrix_x ) (matrix-length matrix_y ) ) ) ) (matrix-empty ) (matrix-prepend (vec_elemwise_sub (matrix-ref-noerr matrix_x 0 ) (matrix-ref-noerr matrix_y 0 )) (matrix_elemwise_sub (matrix-tail-noerr matrix_x 1 ) (matrix-tail-noerr matrix_y 1 ) ) ) ))

(define-grammar (matsub_inv0_gram agg.result i j m matA matB n ref.tmp row_vec)
 [rv (choose (&& (&& (>= i 0 ) (<= i m ) ) (equal? agg.result (matrix_elemwise_sub (v0) (v0) ) ) ))]
[v0 (choose (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v1) i ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v1) n ) 0 i ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v1) i ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v1) n ) 0 i ) ) ))]
[v1 (choose matA matB)]
)

(define-grammar (matsub_inv1_gram j m matA matB n ref.tmp row_vec agg.result i)
 [rv (choose (&& (&& (&& (&& (&& (>= i 0 ) (< i m ) ) (>= j 0 ) ) (<= j n ) ) (equal? row_vec (vec_elemwise_sub (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (matrix-ref-noerr (v0) i ) j ) (matrix-ref-noerr (matrix-transpose-noerr (matrix-col-slice-with-length-noerr (matrix-take-noerr (v0) j ) i 1 ) ) 0 ) ) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (matrix-ref-noerr (v0) i ) j ) (matrix-ref-noerr (matrix-transpose-noerr (matrix-col-slice-with-length-noerr (matrix-take-noerr (v0) j ) i 1 ) ) 0 ) )) ) ) (equal? agg.result (matrix_elemwise_sub (v1) (v1) ) ) ))]
[v0 (choose matA matB)]
[v1 (choose (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v0) i ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v0) n ) 0 i ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v0) i ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v0) n ) 0 i ) ) ))]
)

(define-grammar (matsub_ps_gram matA matB m n matsub_rv)
 [rv (choose (equal? matsub_rv (matrix_elemwise_sub (v0) (v0) ) ))]
[v0 (choose (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v1) m ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v1) n ) 0 m ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (matrix-col-slice-noerr (matrix-take-noerr (v1) m ) 0 n ) (matrix-col-slice-noerr (matrix-take-noerr (v1) n ) 0 m ) ) ))]
[v1 (choose matA matB)]
)

(define-grammar (OUTER_LOOP_INDEX_FIRST_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
)

(define (matsub_inv0 agg.result i j m matA matB n ref.tmp row_vec) (matsub_inv0_gram agg.result i j m matA matB n ref.tmp row_vec #:depth 10))
(define (matsub_inv1 j m matA matB n ref.tmp row_vec agg.result i) (matsub_inv1_gram j m matA matB n ref.tmp row_vec agg.result i #:depth 10))
(define (matsub_ps matA matB m n matsub_rv) (matsub_ps_gram matA matB m n matsub_rv #:depth 10))

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
(define-symbolic matB_BOUNDEDSET-len integer?)
(define-symbolic matB_BOUNDEDSET-0 integer?)
(define-symbolic matB_BOUNDEDSET-1 integer?)
(define-symbolic matB_BOUNDEDSET-2 integer?)
(define-symbolic matB_BOUNDEDSET-3 integer?)
(define matB (take (list (list matB_BOUNDEDSET-0 matB_BOUNDEDSET-1) (list matB_BOUNDEDSET-2 matB_BOUNDEDSET-3)) matB_BOUNDEDSET-len))
(define-symbolic matsub_rv_BOUNDEDSET-len integer?)
(define-symbolic matsub_rv_BOUNDEDSET-0 integer?)
(define-symbolic matsub_rv_BOUNDEDSET-1 integer?)
(define-symbolic matsub_rv_BOUNDEDSET-2 integer?)
(define-symbolic matsub_rv_BOUNDEDSET-3 integer?)
(define matsub_rv (take (list (list matsub_rv_BOUNDEDSET-0 matsub_rv_BOUNDEDSET-1) (list matsub_rv_BOUNDEDSET-2 matsub_rv_BOUNDEDSET-3)) matsub_rv_BOUNDEDSET-len))
(define-symbolic n integer?)
(define-symbolic ref.tmp integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1) row_vec_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (&& (&& (&& (>= m 1 ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (matrix-length matB ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (>= (length (matrix-ref-noerr matB 0 ) ) n ) ) (matsub_inv0 (matrix-empty ) 0 0 m matA matB n 0 (list-empty )) ) (=> (&& (&& (&& (&& (&& (&& (&& (< i m ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (matrix-length matB ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (>= (length (matrix-ref-noerr matB 0 ) ) n ) ) (matsub_inv0 agg.result i j m matA matB n ref.tmp row_vec) ) (matsub_inv1 0 m matA matB n ref.tmp (list-empty ) agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (&& (< j n ) (< i m ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (matrix-length matB ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (>= (length (matrix-ref-noerr matB 0 ) ) n ) ) (matsub_inv0 agg.result i j m matA matB n ref.tmp row_vec) ) (matsub_inv1 j m matA matB n ref.tmp row_vec agg.result i) ) (matsub_inv1 (+ j 1 ) m matA matB n (- (list-ref-noerr (matrix-ref-noerr matA i ) j ) (list-ref-noerr (matrix-ref-noerr matB i ) j ) ) (list-append row_vec (- (list-ref-noerr (matrix-ref-noerr matA i ) j ) (list-ref-noerr (matrix-ref-noerr matB i ) j ) ) ) agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (&& (! (< j n ) ) (< i m ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (matrix-length matB ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (>= (length (matrix-ref-noerr matB 0 ) ) n ) ) (matsub_inv0 agg.result i j m matA matB n ref.tmp row_vec) ) (matsub_inv1 j m matA matB n ref.tmp row_vec agg.result i) ) (matsub_inv0 (matrix-append agg.result row_vec ) (+ i 1 ) j m matA matB n ref.tmp row_vec) ) ) (=> (or (&& (&& (&& (&& (&& (&& (&& (! (< i m ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (matrix-length matB ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (>= (length (matrix-ref-noerr matB 0 ) ) n ) ) (matsub_inv0 agg.result i j m matA matB n ref.tmp row_vec) ) (&& (&& (&& (&& (&& (&& (&& (&& (! true ) (! (< i m ) ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (matrix-length matB ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (>= (length (matrix-ref-noerr matB 0 ) ) n ) ) (matsub_inv0 agg.result i j m matA matB n ref.tmp row_vec) ) ) (matsub_ps matA matB m n agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 i j m matA_BOUNDEDSET-len matA_BOUNDEDSET-0 matA_BOUNDEDSET-1 matA_BOUNDEDSET-2 matA_BOUNDEDSET-3 matB_BOUNDEDSET-len matB_BOUNDEDSET-0 matB_BOUNDEDSET-1 matB_BOUNDEDSET-2 matB_BOUNDEDSET-3 matsub_rv_BOUNDEDSET-len matsub_rv_BOUNDEDSET-0 matsub_rv_BOUNDEDSET-1 matsub_rv_BOUNDEDSET-2 matsub_rv_BOUNDEDSET-3 n ref.tmp row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
