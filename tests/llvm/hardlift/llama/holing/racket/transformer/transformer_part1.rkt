#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_scalar_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) a ) (vec_scalar_div a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_div x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_div (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))


 (define-bounded (matrix_vec_mul matrix_x x)
(if (or (or (< (list-list-length matrix_x ) 1 ) (< (length (list-list-ref-noerr matrix_x 0 ) ) 1 ) ) (! (equal? (length (list-list-ref-noerr matrix_x 0 ) ) (length x ) ) ) ) (list-empty ) (list-prepend (reduce_sum (vec_elemwise_mul (list-list-ref-noerr matrix_x 0 ) x)) (matrix_vec_mul (list-list-tail-noerr matrix_x 1 ) x ) ) ))

(define-grammar (transformer_part1_inv0_gram agg.result head head_size i key_cache_layer q score timestep token_position)
 [rv (choose (&& (&& (>= timestep 0 ) (<= timestep token_position ) ) (equal? agg.result (vec_scalar_div (SQRT_ARG_FN token_position head head_size) (v0)) ) ))]
[v0 (choose (if (VECTOR_OUTER_LOOP_INDEX) (list-slice-noerr q (VEC_COMPOSED_INDEX_FN token_position head head_size) (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) timestep ) ) (list-slice-noerr q (VEC_COMPOSED_INDEX_FN token_position head head_size) (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) ) (matrix_vec_mul (v1) (if (VECTOR_OUTER_LOOP_INDEX) (list-slice-noerr q (VEC_COMPOSED_INDEX_FN token_position head head_size) (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) timestep ) ) (list-slice-noerr q (VEC_COMPOSED_INDEX_FN token_position head head_size) (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) ) ))]
[v1 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 timestep ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 head_size ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) timestep ) ) ) (matrix-transpose-noerr (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 timestep ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 head_size ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) timestep ) ) ) ))]
)

(define-grammar (transformer_part1_inv1_gram head head_size i key_cache_layer q score token_position agg.result timestep)
 [rv (choose (&& (&& (&& (&& (&& (>= timestep 0 ) (< timestep token_position ) ) (>= i 0 ) ) (<= i head_size ) ) (equal? score (reduce_sum (if (VECTOR_OUTER_LOOP_INDEX) (vec_scalar_mul (list-ref-noerr q (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) timestep ) ) (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-slice-noerr (list-list-ref-noerr key_cache_layer timestep ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) i ) ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-slice-noerr key_cache_layer 0 i ) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) timestep ) 1 ) ) 0 ) )) (vec_elemwise_mul (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-slice-noerr (list-list-ref-noerr key_cache_layer timestep ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) i ) ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-slice-noerr key_cache_layer 0 i ) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) timestep ) 1 ) ) 0 ) ) (list-slice-noerr q (VEC_COMPOSED_INDEX_FN token_position head head_size) (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) i ) )) )) ) ) (equal? agg.result (vec_scalar_div (SQRT_ARG_FN token_position head head_size) (v0)) ) ))]
[v0 (choose (if (VECTOR_OUTER_LOOP_INDEX) (list-slice-noerr q (VEC_COMPOSED_INDEX_FN token_position head head_size) (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) timestep ) ) (list-slice-noerr q (VEC_COMPOSED_INDEX_FN token_position head head_size) (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) ) (v1))]
[v1 (choose (matrix_vec_mul (v2) (if (VECTOR_OUTER_LOOP_INDEX) (list-slice-noerr q (VEC_COMPOSED_INDEX_FN token_position head head_size) (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) timestep ) ) (list-slice-noerr q (VEC_COMPOSED_INDEX_FN token_position head head_size) (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) ) ))]
[v2 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 timestep ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 head_size ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) timestep ) ) ) (matrix-transpose-noerr (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 timestep ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 head_size ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) timestep ) ) ) ))]
)

(define-grammar (transformer_part1_ps_gram token_position head head_size key_cache_layer q transformer_part1_rv)
 [rv (choose (equal? transformer_part1_rv (vec_scalar_div (SQRT_ARG_FN token_position head head_size) (v0)) ))]
[v0 (choose (if (VECTOR_OUTER_LOOP_INDEX) (list-slice-noerr q (VEC_COMPOSED_INDEX_FN token_position head head_size) (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) token_position ) ) (list-slice-noerr q (VEC_COMPOSED_INDEX_FN token_position head head_size) (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) ) (matrix_vec_mul (v1) (if (VECTOR_OUTER_LOOP_INDEX) (list-slice-noerr q (VEC_COMPOSED_INDEX_FN token_position head head_size) (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) token_position ) ) (list-slice-noerr q (VEC_COMPOSED_INDEX_FN token_position head head_size) (+ (VEC_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) ) ))]
[v1 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 token_position ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 head_size ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) token_position ) ) ) (matrix-transpose-noerr (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 token_position ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 head_size ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) token_position ) ) ) ))]
)

(define-grammar (VEC_COMPOSED_INDEX_FN_gram token_position head head_size)
 [rv (choose (v0))]
[v0 (choose (* token_position token_position ) (* head token_position ) (* head head ) (* head_size token_position ) (* head_size head ) (* head_size head_size ))]
)

(define-grammar (SQRT_ARG_FN_gram token_position head head_size)
 [rv (choose (* (v0) (v1) ))]
[v0 (choose 0 1)]
[v1 (choose token_position head head_size)]
)

(define-grammar (MATRIX_COMPOSED_INDEX_FN_gram token_position head head_size)
 [rv (choose (v0))]
[v0 (choose (* token_position token_position ) (* head token_position ) (* head head ) (* head_size token_position ) (* head_size head ) (* head_size head_size ))]
)

(define-grammar (MATRIX_OUTER_LOOP_INDEX_FIRST_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
)

(define-grammar (VECTOR_OUTER_LOOP_INDEX_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
)

(define (transformer_part1_inv0 agg.result head head_size i key_cache_layer q score timestep token_position) (transformer_part1_inv0_gram agg.result head head_size i key_cache_layer q score timestep token_position #:depth 10))
(define (transformer_part1_inv1 head head_size i key_cache_layer q score token_position agg.result timestep) (transformer_part1_inv1_gram head head_size i key_cache_layer q score token_position agg.result timestep #:depth 10))
(define (transformer_part1_ps token_position head head_size key_cache_layer q transformer_part1_rv) (transformer_part1_ps_gram token_position head head_size key_cache_layer q transformer_part1_rv #:depth 10))

(define (VEC_COMPOSED_INDEX_FN token_position head head_size) (VEC_COMPOSED_INDEX_FN_gram token_position head head_size #:depth 10))
(define (SQRT_ARG_FN token_position head head_size) (SQRT_ARG_FN_gram token_position head head_size #:depth 10))
(define (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (MATRIX_COMPOSED_INDEX_FN_gram token_position head head_size #:depth 10))
(define (MATRIX_OUTER_LOOP_INDEX_FIRST ) (MATRIX_OUTER_LOOP_INDEX_FIRST_gram  #:depth 10))
(define (VECTOR_OUTER_LOOP_INDEX ) (VECTOR_OUTER_LOOP_INDEX_gram  #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2) agg.result_BOUNDEDSET-len))
(define-symbolic head integer?)
(define-symbolic head_size integer?)
(define-symbolic i integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-len integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-0 integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-1 integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-2 integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-3 integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-4 integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-5 integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-6 integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-7 integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-8 integer?)
(define key_cache_layer (take (list (list key_cache_layer_BOUNDEDSET-0 key_cache_layer_BOUNDEDSET-1 key_cache_layer_BOUNDEDSET-2) (list key_cache_layer_BOUNDEDSET-3 key_cache_layer_BOUNDEDSET-4 key_cache_layer_BOUNDEDSET-5) (list key_cache_layer_BOUNDEDSET-6 key_cache_layer_BOUNDEDSET-7 key_cache_layer_BOUNDEDSET-8)) key_cache_layer_BOUNDEDSET-len))
(define-symbolic q_BOUNDEDSET-len integer?)
(define-symbolic q_BOUNDEDSET-0 integer?)
(define-symbolic q_BOUNDEDSET-1 integer?)
(define-symbolic q_BOUNDEDSET-2 integer?)
(define q (take (list q_BOUNDEDSET-0 q_BOUNDEDSET-1 q_BOUNDEDSET-2) q_BOUNDEDSET-len))
(define-symbolic score integer?)
(define-symbolic timestep integer?)
(define-symbolic token_position integer?)
(define-symbolic transformer_part1_rv_BOUNDEDSET-len integer?)
(define-symbolic transformer_part1_rv_BOUNDEDSET-0 integer?)
(define-symbolic transformer_part1_rv_BOUNDEDSET-1 integer?)
(define-symbolic transformer_part1_rv_BOUNDEDSET-2 integer?)
(define transformer_part1_rv (take (list transformer_part1_rv_BOUNDEDSET-0 transformer_part1_rv_BOUNDEDSET-1 transformer_part1_rv_BOUNDEDSET-2) transformer_part1_rv_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (&& (&& (&& (&& (&& (&& (&& (> token_position 0 ) (> (list-list-length key_cache_layer ) token_position ) ) (>= head 0 ) ) (<= head (length q ) ) ) (<= head (list-list-length key_cache_layer ) ) ) (> head_size 0 ) ) (<= head_size (length q ) ) ) (<= head_size (list-list-length key_cache_layer ) ) ) (< (+ (* head head_size ) head_size ) (length (list-list-ref-noerr key_cache_layer 0 ) ) ) ) (< (+ (* head head_size ) head_size ) (length q ) ) ) (transformer_part1_inv0 (list-empty ) head head_size 0 key_cache_layer q 0 0 token_position) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (< timestep token_position ) (> token_position 0 ) ) (> (list-list-length key_cache_layer ) token_position ) ) (>= head 0 ) ) (<= head (length q ) ) ) (<= head (list-list-length key_cache_layer ) ) ) (> head_size 0 ) ) (<= head_size (length q ) ) ) (<= head_size (list-list-length key_cache_layer ) ) ) (< (+ (* head head_size ) head_size ) (length (list-list-ref-noerr key_cache_layer 0 ) ) ) ) (< (+ (* head head_size ) head_size ) (length q ) ) ) (transformer_part1_inv0 agg.result head head_size i key_cache_layer q score timestep token_position) ) (transformer_part1_inv1 head head_size 0 key_cache_layer q 0 token_position agg.result timestep) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (< i head_size ) (< timestep token_position ) ) (> token_position 0 ) ) (> (list-list-length key_cache_layer ) token_position ) ) (>= head 0 ) ) (<= head (length q ) ) ) (<= head (list-list-length key_cache_layer ) ) ) (> head_size 0 ) ) (<= head_size (length q ) ) ) (<= head_size (list-list-length key_cache_layer ) ) ) (< (+ (* head head_size ) head_size ) (length (list-list-ref-noerr key_cache_layer 0 ) ) ) ) (< (+ (* head head_size ) head_size ) (length q ) ) ) (transformer_part1_inv0 agg.result head head_size i key_cache_layer q score timestep token_position) ) (transformer_part1_inv1 head head_size i key_cache_layer q score token_position agg.result timestep) ) (transformer_part1_inv1 head head_size (+ i 1 ) key_cache_layer q (+ score (* (list-ref-noerr q (+ (* head head_size ) i ) ) (list-ref-noerr (list-list-ref-noerr key_cache_layer timestep ) (+ (* head head_size ) i ) ) ) ) token_position agg.result timestep) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (! (< i head_size ) ) (< timestep token_position ) ) (> token_position 0 ) ) (> (list-list-length key_cache_layer ) token_position ) ) (>= head 0 ) ) (<= head (length q ) ) ) (<= head (list-list-length key_cache_layer ) ) ) (> head_size 0 ) ) (<= head_size (length q ) ) ) (<= head_size (list-list-length key_cache_layer ) ) ) (< (+ (* head head_size ) head_size ) (length (list-list-ref-noerr key_cache_layer 0 ) ) ) ) (< (+ (* head head_size ) head_size ) (length q ) ) ) (transformer_part1_inv0 agg.result head head_size i key_cache_layer q score timestep token_position) ) (transformer_part1_inv1 head head_size i key_cache_layer q score token_position agg.result timestep) ) (transformer_part1_inv0 (list-append agg.result (quotient-noerr score (integer-sqrt-noerr (* head_size 1 ) ) ) ) head head_size i key_cache_layer q (quotient-noerr score (integer-sqrt-noerr (* head_size 1 ) ) ) (+ timestep 1 ) token_position) ) ) (=> (or (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (! (< timestep token_position ) ) (> token_position 0 ) ) (> (list-list-length key_cache_layer ) token_position ) ) (>= head 0 ) ) (<= head (length q ) ) ) (<= head (list-list-length key_cache_layer ) ) ) (> head_size 0 ) ) (<= head_size (length q ) ) ) (<= head_size (list-list-length key_cache_layer ) ) ) (< (+ (* head head_size ) head_size ) (length (list-list-ref-noerr key_cache_layer 0 ) ) ) ) (< (+ (* head head_size ) head_size ) (length q ) ) ) (transformer_part1_inv0 agg.result head head_size i key_cache_layer q score timestep token_position) ) (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (! true ) (! (< timestep token_position ) ) ) (> token_position 0 ) ) (> (list-list-length key_cache_layer ) token_position ) ) (>= head 0 ) ) (<= head (length q ) ) ) (<= head (list-list-length key_cache_layer ) ) ) (> head_size 0 ) ) (<= head_size (length q ) ) ) (<= head_size (list-list-length key_cache_layer ) ) ) (< (+ (* head head_size ) head_size ) (length (list-list-ref-noerr key_cache_layer 0 ) ) ) ) (< (+ (* head head_size ) head_size ) (length q ) ) ) (transformer_part1_inv0 agg.result head head_size i key_cache_layer q score timestep token_position) ) ) (transformer_part1_ps token_position head head_size key_cache_layer q agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 head head_size i key_cache_layer_BOUNDEDSET-len key_cache_layer_BOUNDEDSET-0 key_cache_layer_BOUNDEDSET-1 key_cache_layer_BOUNDEDSET-2 key_cache_layer_BOUNDEDSET-3 key_cache_layer_BOUNDEDSET-4 key_cache_layer_BOUNDEDSET-5 key_cache_layer_BOUNDEDSET-6 key_cache_layer_BOUNDEDSET-7 key_cache_layer_BOUNDEDSET-8 q_BOUNDEDSET-len q_BOUNDEDSET-0 q_BOUNDEDSET-1 q_BOUNDEDSET-2 score timestep token_position transformer_part1_rv_BOUNDEDSET-len transformer_part1_rv_BOUNDEDSET-0 transformer_part1_rv_BOUNDEDSET-1 transformer_part1_rv_BOUNDEDSET-2)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)


        (define sol1
            (synthesize
                #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 head head_size i key_cache_layer_BOUNDEDSET-len key_cache_layer_BOUNDEDSET-0 key_cache_layer_BOUNDEDSET-1 key_cache_layer_BOUNDEDSET-2 key_cache_layer_BOUNDEDSET-3 key_cache_layer_BOUNDEDSET-4 key_cache_layer_BOUNDEDSET-5 key_cache_layer_BOUNDEDSET-6 key_cache_layer_BOUNDEDSET-7 key_cache_layer_BOUNDEDSET-8 q_BOUNDEDSET-len q_BOUNDEDSET-0 q_BOUNDEDSET-1 q_BOUNDEDSET-2 score timestep token_position transformer_part1_rv_BOUNDEDSET-len transformer_part1_rv_BOUNDEDSET-0 transformer_part1_rv_BOUNDEDSET-1 transformer_part1_rv_BOUNDEDSET-2)
                #:guarantee (begin
                    (assume (|| (! (eq? (transformer_part1_inv0 agg.result head head_size i key_cache_layer q score timestep token_position) (evaluate (transformer_part1_inv0 agg.result head head_size i key_cache_layer q score timestep token_position) sol0))) (! (eq? (transformer_part1_inv1 head head_size i key_cache_layer q score token_position agg.result timestep) (evaluate (transformer_part1_inv1 head head_size i key_cache_layer q score token_position agg.result timestep) sol0))) (! (eq? (transformer_part1_ps token_position head head_size key_cache_layer q transformer_part1_rv) (evaluate (transformer_part1_ps token_position head head_size key_cache_layer q transformer_part1_rv) sol0)))))
                    (assertions)
                )
            )
        )
        (sat? sol1)
        (print-forms sol1)


        (define sol2
            (synthesize
                #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 head head_size i key_cache_layer_BOUNDEDSET-len key_cache_layer_BOUNDEDSET-0 key_cache_layer_BOUNDEDSET-1 key_cache_layer_BOUNDEDSET-2 key_cache_layer_BOUNDEDSET-3 key_cache_layer_BOUNDEDSET-4 key_cache_layer_BOUNDEDSET-5 key_cache_layer_BOUNDEDSET-6 key_cache_layer_BOUNDEDSET-7 key_cache_layer_BOUNDEDSET-8 q_BOUNDEDSET-len q_BOUNDEDSET-0 q_BOUNDEDSET-1 q_BOUNDEDSET-2 score timestep token_position transformer_part1_rv_BOUNDEDSET-len transformer_part1_rv_BOUNDEDSET-0 transformer_part1_rv_BOUNDEDSET-1 transformer_part1_rv_BOUNDEDSET-2)
                #:guarantee (begin
                    (assume (|| (! (eq? (transformer_part1_inv0 agg.result head head_size i key_cache_layer q score timestep token_position) (evaluate (transformer_part1_inv0 agg.result head head_size i key_cache_layer q score timestep token_position) sol0))) (! (eq? (transformer_part1_inv1 head head_size i key_cache_layer q score token_position agg.result timestep) (evaluate (transformer_part1_inv1 head head_size i key_cache_layer q score token_position agg.result timestep) sol0))) (! (eq? (transformer_part1_ps token_position head head_size key_cache_layer q transformer_part1_rv) (evaluate (transformer_part1_ps token_position head head_size key_cache_layer q transformer_part1_rv) sol0))))) (assume (|| (! (eq? (transformer_part1_inv0 agg.result head head_size i key_cache_layer q score timestep token_position) (evaluate (transformer_part1_inv0 agg.result head head_size i key_cache_layer q score timestep token_position) sol1))) (! (eq? (transformer_part1_inv1 head head_size i key_cache_layer q score token_position agg.result timestep) (evaluate (transformer_part1_inv1 head head_size i key_cache_layer q score token_position agg.result timestep) sol1))) (! (eq? (transformer_part1_ps token_position head head_size key_cache_layer q transformer_part1_rv) (evaluate (transformer_part1_ps token_position head head_size key_cache_layer q transformer_part1_rv) sol1)))))
                    (assertions)
                )
            )
        )
        (sat? sol2)
        (print-forms sol2)
