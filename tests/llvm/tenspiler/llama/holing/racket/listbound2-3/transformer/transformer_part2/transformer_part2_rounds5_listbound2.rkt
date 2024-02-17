#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 )) ) ))


 (define-bounded (matrix_vec_mul matrix_x x)
(if (or (or (< (list-list-length matrix_x ) 1 ) (< (length (list-list-ref-noerr matrix_x 0 ) ) 1 ) ) (! (equal? (length (list-list-ref-noerr matrix_x 0 ) ) (length x ) ) ) ) (list-empty ) (list-prepend (reduce_sum (vec_elemwise_mul (list-list-ref-noerr matrix_x 0 ) x)) (matrix_vec_mul (list-list-tail-noerr matrix_x 1 ) x ) ) ))

(define-grammar (transformer_part2_inv0_gram agg.result attention curr head head_size i key_cache_layer timestep token_position)
 [rv (choose (&& (&& (>= i 0 ) (<= i head_size ) ) (equal? agg.result (matrix_vec_mul (v0) (if (VECTOR_OUTER_LOOP_INDEX) (list-slice-noerr attention 0 i ) (list-slice-noerr attention 0 (+ token_position 1 ) ) ) ) ) ))]
[v0 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 i ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) token_position ) 1 ) ) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 (+ token_position 1 ) ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) i ) ) ) (matrix-transpose-noerr (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 i ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) token_position ) 1 ) ) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 (+ token_position 1 ) ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) i ) ) ) ))]
)

(define-grammar (transformer_part2_inv1_gram attention curr head head_size key_cache_layer timestep token_position agg.result i)
 [rv (choose (&& (&& (&& (&& (&& (>= i 0 ) (< i head_size ) ) (>= timestep 0 ) ) (<= timestep (+ token_position 1 ) ) ) (equal? curr (reduce_sum (if (VECTOR_OUTER_LOOP_INDEX) (vec_scalar_mul (list-ref-noerr attention i ) (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-slice-noerr (list-list-ref-noerr key_cache_layer i ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) timestep ) ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-slice-noerr key_cache_layer 0 timestep ) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) i ) 1 ) ) 0 ) )) (vec_elemwise_mul (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-slice-noerr (list-list-ref-noerr key_cache_layer i ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) timestep ) ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-slice-noerr key_cache_layer 0 timestep ) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) i ) 1 ) ) 0 ) ) (list-slice-noerr attention 0 timestep )) )) ) ) (equal? agg.result (matrix_vec_mul (v0) (if (VECTOR_OUTER_LOOP_INDEX) (list-slice-noerr attention 0 i ) (list-slice-noerr attention 0 (+ token_position 1 ) ) ) ) ) ))]
[v0 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 i ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) token_position ) 1 ) ) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 (+ token_position 1 ) ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) i ) ) ) (matrix-transpose-noerr (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 i ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) token_position ) 1 ) ) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 (+ token_position 1 ) ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) i ) ) ) ))]
)

(define-grammar (transformer_part2_ps_gram token_position head head_size key_cache_layer attention transformer_part2_rv)
 [rv (choose (equal? transformer_part2_rv (matrix_vec_mul (v0) (if (VECTOR_OUTER_LOOP_INDEX) (list-slice-noerr attention 0 head_size ) (list-slice-noerr attention 0 (+ token_position 1 ) ) ) ) ))]
[v0 (choose (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 head_size ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) token_position ) 1 ) ) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 (+ token_position 1 ) ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) ) (matrix-transpose-noerr (if (MATRIX_OUTER_LOOP_INDEX_FIRST) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 head_size ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) token_position ) 1 ) ) (list-list-col-slice-noerr (list-list-slice-noerr key_cache_layer 0 (+ token_position 1 ) ) (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (+ (MATRIX_COMPOSED_INDEX_FN token_position head head_size) head_size ) ) ) ))]
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

(define (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (transformer_part2_inv0_gram agg.result attention curr head head_size i key_cache_layer timestep token_position #:depth 10))
(define (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (transformer_part2_inv1_gram attention curr head head_size key_cache_layer timestep token_position agg.result i #:depth 10))
(define (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (transformer_part2_ps_gram token_position head head_size key_cache_layer attention transformer_part2_rv #:depth 10))

(define (MATRIX_COMPOSED_INDEX_FN token_position head head_size) (MATRIX_COMPOSED_INDEX_FN_gram token_position head head_size #:depth 10))
(define (MATRIX_OUTER_LOOP_INDEX_FIRST ) (MATRIX_OUTER_LOOP_INDEX_FIRST_gram  #:depth 10))
(define (VECTOR_OUTER_LOOP_INDEX ) (VECTOR_OUTER_LOOP_INDEX_gram  #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic attention_BOUNDEDSET-len integer?)
(define-symbolic attention_BOUNDEDSET-0 integer?)
(define-symbolic attention_BOUNDEDSET-1 integer?)
(define attention (take (list attention_BOUNDEDSET-0 attention_BOUNDEDSET-1) attention_BOUNDEDSET-len))
(define-symbolic curr integer?)
(define-symbolic head integer?)
(define-symbolic head_size integer?)
(define-symbolic i integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-len integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-0 integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-1 integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-2 integer?)
(define-symbolic key_cache_layer_BOUNDEDSET-3 integer?)
(define key_cache_layer (take (list (list key_cache_layer_BOUNDEDSET-0 key_cache_layer_BOUNDEDSET-1) (list key_cache_layer_BOUNDEDSET-2 key_cache_layer_BOUNDEDSET-3)) key_cache_layer_BOUNDEDSET-len))
(define-symbolic timestep integer?)
(define-symbolic token_position integer?)
(define-symbolic transformer_part2_rv_BOUNDEDSET-len integer?)
(define-symbolic transformer_part2_rv_BOUNDEDSET-0 integer?)
(define-symbolic transformer_part2_rv_BOUNDEDSET-1 integer?)
(define transformer_part2_rv (take (list transformer_part2_rv_BOUNDEDSET-0 transformer_part2_rv_BOUNDEDSET-1) transformer_part2_rv_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (> token_position 0 ) (> (list-list-length key_cache_layer ) 0 ) ) (> (length (list-list-ref-noerr key_cache_layer 0 ) ) 0 ) ) (> (length attention ) 0 ) ) (> (list-list-length key_cache_layer ) token_position ) ) (> (length (list-list-ref-noerr key_cache_layer 0 ) ) (+ (* head head_size ) head_size ) ) ) (> (length attention ) token_position ) ) (>= head 0 ) ) (<= head (length attention ) ) ) (> head_size 0 ) ) (<= head_size (length attention ) ) ) (transformer_part2_inv0 (list-empty ) attention 0 head head_size 0 key_cache_layer 0 token_position) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (< i head_size ) (> token_position 0 ) ) (> (list-list-length key_cache_layer ) 0 ) ) (> (length (list-list-ref-noerr key_cache_layer 0 ) ) 0 ) ) (> (length attention ) 0 ) ) (> (list-list-length key_cache_layer ) token_position ) ) (> (length (list-list-ref-noerr key_cache_layer 0 ) ) (+ (* head head_size ) head_size ) ) ) (> (length attention ) token_position ) ) (>= head 0 ) ) (<= head (length attention ) ) ) (> head_size 0 ) ) (<= head_size (length attention ) ) ) (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) ) (transformer_part2_inv1 attention 0 head head_size key_cache_layer 0 token_position agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (<= timestep token_position ) (< i head_size ) ) (> token_position 0 ) ) (> (list-list-length key_cache_layer ) 0 ) ) (> (length (list-list-ref-noerr key_cache_layer 0 ) ) 0 ) ) (> (length attention ) 0 ) ) (> (list-list-length key_cache_layer ) token_position ) ) (> (length (list-list-ref-noerr key_cache_layer 0 ) ) (+ (* head head_size ) head_size ) ) ) (> (length attention ) token_position ) ) (>= head 0 ) ) (<= head (length attention ) ) ) (> head_size 0 ) ) (<= head_size (length attention ) ) ) (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) ) (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) ) (transformer_part2_inv1 attention (+ curr (* (list-ref-noerr attention timestep ) (list-ref-noerr (list-list-ref-noerr key_cache_layer timestep ) (+ (* head head_size ) i ) ) ) ) head head_size key_cache_layer (+ timestep 1 ) token_position agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (! (<= timestep token_position ) ) (< i head_size ) ) (> token_position 0 ) ) (> (list-list-length key_cache_layer ) 0 ) ) (> (length (list-list-ref-noerr key_cache_layer 0 ) ) 0 ) ) (> (length attention ) 0 ) ) (> (list-list-length key_cache_layer ) token_position ) ) (> (length (list-list-ref-noerr key_cache_layer 0 ) ) (+ (* head head_size ) head_size ) ) ) (> (length attention ) token_position ) ) (>= head 0 ) ) (<= head (length attention ) ) ) (> head_size 0 ) ) (<= head_size (length attention ) ) ) (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) ) (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) ) (transformer_part2_inv0 (list-append agg.result curr ) attention curr head head_size (+ i 1 ) key_cache_layer timestep token_position) ) ) (=> (or (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (! (< i head_size ) ) (> token_position 0 ) ) (> (list-list-length key_cache_layer ) 0 ) ) (> (length (list-list-ref-noerr key_cache_layer 0 ) ) 0 ) ) (> (length attention ) 0 ) ) (> (list-list-length key_cache_layer ) token_position ) ) (> (length (list-list-ref-noerr key_cache_layer 0 ) ) (+ (* head head_size ) head_size ) ) ) (> (length attention ) token_position ) ) (>= head 0 ) ) (<= head (length attention ) ) ) (> head_size 0 ) ) (<= head_size (length attention ) ) ) (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) ) (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (&& (! true ) (! (< i head_size ) ) ) (> token_position 0 ) ) (> (list-list-length key_cache_layer ) 0 ) ) (> (length (list-list-ref-noerr key_cache_layer 0 ) ) 0 ) ) (> (length attention ) 0 ) ) (> (list-list-length key_cache_layer ) token_position ) ) (> (length (list-list-ref-noerr key_cache_layer 0 ) ) (+ (* head head_size ) head_size ) ) ) (> (length attention ) token_position ) ) (>= head 0 ) ) (<= head (length attention ) ) ) (> head_size 0 ) ) (<= head_size (length attention ) ) ) (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) ) ) (transformer_part2_ps token_position head head_size key_cache_layer attention agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 attention_BOUNDEDSET-len attention_BOUNDEDSET-0 attention_BOUNDEDSET-1 curr head head_size i key_cache_layer_BOUNDEDSET-len key_cache_layer_BOUNDEDSET-0 key_cache_layer_BOUNDEDSET-1 key_cache_layer_BOUNDEDSET-2 key_cache_layer_BOUNDEDSET-3 timestep token_position transformer_part2_rv_BOUNDEDSET-len transformer_part2_rv_BOUNDEDSET-0 transformer_part2_rv_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)


        (define sol1
            (synthesize
                #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 attention_BOUNDEDSET-len attention_BOUNDEDSET-0 attention_BOUNDEDSET-1 curr head head_size i key_cache_layer_BOUNDEDSET-len key_cache_layer_BOUNDEDSET-0 key_cache_layer_BOUNDEDSET-1 key_cache_layer_BOUNDEDSET-2 key_cache_layer_BOUNDEDSET-3 timestep token_position transformer_part2_rv_BOUNDEDSET-len transformer_part2_rv_BOUNDEDSET-0 transformer_part2_rv_BOUNDEDSET-1)
                #:guarantee (begin
                    (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol0))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol0))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol0)))))
                    (assertions)
                )
            )
        )
        (sat? sol1)
        (print-forms sol1)


        (define sol2
            (synthesize
                #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 attention_BOUNDEDSET-len attention_BOUNDEDSET-0 attention_BOUNDEDSET-1 curr head head_size i key_cache_layer_BOUNDEDSET-len key_cache_layer_BOUNDEDSET-0 key_cache_layer_BOUNDEDSET-1 key_cache_layer_BOUNDEDSET-2 key_cache_layer_BOUNDEDSET-3 timestep token_position transformer_part2_rv_BOUNDEDSET-len transformer_part2_rv_BOUNDEDSET-0 transformer_part2_rv_BOUNDEDSET-1)
                #:guarantee (begin
                    (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol0))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol0))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol0))))) (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol1))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol1))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol1)))))
                    (assertions)
                )
            )
        )
        (sat? sol2)
        (print-forms sol2)


        (define sol3
            (synthesize
                #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 attention_BOUNDEDSET-len attention_BOUNDEDSET-0 attention_BOUNDEDSET-1 curr head head_size i key_cache_layer_BOUNDEDSET-len key_cache_layer_BOUNDEDSET-0 key_cache_layer_BOUNDEDSET-1 key_cache_layer_BOUNDEDSET-2 key_cache_layer_BOUNDEDSET-3 timestep token_position transformer_part2_rv_BOUNDEDSET-len transformer_part2_rv_BOUNDEDSET-0 transformer_part2_rv_BOUNDEDSET-1)
                #:guarantee (begin
                    (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol0))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol0))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol0))))) (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol1))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol1))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol1))))) (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol2))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol2))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol2)))))
                    (assertions)
                )
            )
        )
        (sat? sol3)
        (print-forms sol3)


        (define sol4
            (synthesize
                #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 attention_BOUNDEDSET-len attention_BOUNDEDSET-0 attention_BOUNDEDSET-1 curr head head_size i key_cache_layer_BOUNDEDSET-len key_cache_layer_BOUNDEDSET-0 key_cache_layer_BOUNDEDSET-1 key_cache_layer_BOUNDEDSET-2 key_cache_layer_BOUNDEDSET-3 timestep token_position transformer_part2_rv_BOUNDEDSET-len transformer_part2_rv_BOUNDEDSET-0 transformer_part2_rv_BOUNDEDSET-1)
                #:guarantee (begin
                    (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol0))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol0))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol0))))) (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol1))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol1))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol1))))) (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol2))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol2))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol2))))) (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol3))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol3))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol3)))))
                    (assertions)
                )
            )
        )
        (sat? sol4)
        (print-forms sol4)


        (define sol5
            (synthesize
                #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 attention_BOUNDEDSET-len attention_BOUNDEDSET-0 attention_BOUNDEDSET-1 curr head head_size i key_cache_layer_BOUNDEDSET-len key_cache_layer_BOUNDEDSET-0 key_cache_layer_BOUNDEDSET-1 key_cache_layer_BOUNDEDSET-2 key_cache_layer_BOUNDEDSET-3 timestep token_position transformer_part2_rv_BOUNDEDSET-len transformer_part2_rv_BOUNDEDSET-0 transformer_part2_rv_BOUNDEDSET-1)
                #:guarantee (begin
                    (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol0))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol0))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol0))))) (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol1))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol1))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol1))))) (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol2))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol2))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol2))))) (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol3))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol3))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol3))))) (assume (|| (! (eq? (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) (evaluate (transformer_part2_inv0 agg.result attention curr head head_size i key_cache_layer timestep token_position) sol4))) (! (eq? (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) (evaluate (transformer_part2_inv1 attention curr head head_size key_cache_layer timestep token_position agg.result i) sol4))) (! (eq? (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) (evaluate (transformer_part2_ps token_position head head_size key_cache_layer attention transformer_part2_rv) sol4)))))
                    (assertions)
                )
            )
        )
        (sat? sol5)
        (print-forms sol5)
