#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_elemwise_add x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (+ (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_add (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_sub x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_sub (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_div x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_div (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_scalar_add a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (+ a (list-ref-noerr x 0 ) ) (vec_scalar_add a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_scalar_sub a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) a ) (vec_scalar_sub a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_scalar_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) a ) (vec_scalar_div a (list-tail-noerr x 1 )) ) ))


 (define-bounded (scalar_vec_sub a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (- a (list-ref-noerr x 0 ) ) (scalar_vec_sub a (list-tail-noerr x 1 )) ) ))


 (define-bounded (scalar_vec_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr a (list-ref-noerr x 0 ) ) (scalar_vec_div a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_map x map_int_to_int)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (map_int_to_int (list-ref-noerr x 0 )) (vec_map (list-tail-noerr x 1 ) map_int_to_int) ) ))

(define-grammar (softmax_part4_inv0_gram agg.result i max_pos ref.tmp sum unnormalized_output)
 [rv (choose (&& (&& (>= i (v0) ) (<= i (v1) ) ) (equal? agg.result (v2) ) ))]
[v0 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v1 (choose max_pos (- max_pos 1 ) (+ max_pos 1 ))]
[v2 (choose (list-slice-noerr unnormalized_output (v3) (v3) ))]
[v3 (choose (v4))]
[v4 (choose (v5) (- (v5) 1 ) (+ (v5) 1 ))]
[v5 (choose 0 max_pos i sum)]
)

(define-grammar (softmax_part4_ps_gram unnormalized_output max_pos sum softmax_part4_rv)
 [rv (choose (equal? softmax_part4_rv (v0) ))]
[v0 (choose (list-slice-noerr unnormalized_output (v1) (v1) ))]
[v1 (choose (v2))]
[v2 (choose (v3) (- (v3) 1 ) (+ (v3) 1 ))]
[v3 (choose 0 max_pos sum)]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (softmax_part4_inv0 agg.result i max_pos ref.tmp sum unnormalized_output) (softmax_part4_inv0_gram agg.result i max_pos ref.tmp sum unnormalized_output #:depth 10))
(define (softmax_part4_ps unnormalized_output max_pos sum softmax_part4_rv) (softmax_part4_ps_gram unnormalized_output max_pos sum softmax_part4_rv #:depth 10))

(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic max_pos integer?)
(define-symbolic ref.tmp integer?)
(define-symbolic softmax_part4_rv_BOUNDEDSET-len integer?)
(define-symbolic softmax_part4_rv_BOUNDEDSET-0 integer?)
(define-symbolic softmax_part4_rv_BOUNDEDSET-1 integer?)
(define softmax_part4_rv (take (list softmax_part4_rv_BOUNDEDSET-0 softmax_part4_rv_BOUNDEDSET-1) softmax_part4_rv_BOUNDEDSET-len))
(define-symbolic sum integer?)
(define-symbolic unnormalized_output_BOUNDEDSET-len integer?)
(define-symbolic unnormalized_output_BOUNDEDSET-0 integer?)
(define-symbolic unnormalized_output_BOUNDEDSET-1 integer?)
(define unnormalized_output (take (list unnormalized_output_BOUNDEDSET-0 unnormalized_output_BOUNDEDSET-1) unnormalized_output_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (> (length unnormalized_output ) 0 ) (<= max_pos (length unnormalized_output ) ) ) (>= max_pos 1 ) ) (softmax_part4_inv0 (list-empty ) 0 max_pos 0 sum unnormalized_output) ) (=> (&& (&& (&& (&& (< i max_pos ) (> (length unnormalized_output ) 0 ) ) (<= max_pos (length unnormalized_output ) ) ) (>= max_pos 1 ) ) (softmax_part4_inv0 agg.result i max_pos ref.tmp sum unnormalized_output) ) (softmax_part4_inv0 (list-append agg.result (quotient-noerr (list-ref-noerr unnormalized_output i ) sum ) ) (+ i 1 ) max_pos (quotient-noerr (list-ref-noerr unnormalized_output i ) sum ) sum unnormalized_output) ) ) (=> (or (&& (&& (&& (&& (! (< i max_pos ) ) (> (length unnormalized_output ) 0 ) ) (<= max_pos (length unnormalized_output ) ) ) (>= max_pos 1 ) ) (softmax_part4_inv0 agg.result i max_pos ref.tmp sum unnormalized_output) ) (&& (&& (&& (&& (&& (! true ) (! (< i max_pos ) ) ) (> (length unnormalized_output ) 0 ) ) (<= max_pos (length unnormalized_output ) ) ) (>= max_pos 1 ) ) (softmax_part4_inv0 agg.result i max_pos ref.tmp sum unnormalized_output) ) ) (softmax_part4_ps unnormalized_output max_pos sum agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 i max_pos ref.tmp softmax_part4_rv_BOUNDEDSET-len softmax_part4_rv_BOUNDEDSET-0 softmax_part4_rv_BOUNDEDSET-1 sum unnormalized_output_BOUNDEDSET-len unnormalized_output_BOUNDEDSET-0 unnormalized_output_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
