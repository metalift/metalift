#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_scalar_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) a ) (vec_scalar_div a (list-tail-noerr x 1 )) ) ))

(define-grammar (softmax_part4_inv0_gram agg.result i max_pos ref.tmp sum unnormalized_output)
 [rv (choose (&& (&& (>= i 0 ) (<= i max_pos ) ) (equal? agg.result (vec_scalar_div sum (v0)) ) ))]
[v0 (choose (list-take-noerr unnormalized_output i ))]
)

(define-grammar (softmax_part4_ps_gram unnormalized_output max_pos sum softmax_part4_rv)
 [rv (choose (equal? softmax_part4_rv (vec_scalar_div sum (v0)) ))]
[v0 (choose (list-take-noerr unnormalized_output max_pos ))]
)

(define (softmax_part4_inv0 agg.result i max_pos ref.tmp sum unnormalized_output) (softmax_part4_inv0_gram agg.result i max_pos ref.tmp sum unnormalized_output #:depth 10))
(define (softmax_part4_ps unnormalized_output max_pos sum softmax_part4_rv) (softmax_part4_ps_gram unnormalized_output max_pos sum softmax_part4_rv #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define-symbolic agg.result_BOUNDEDSET-4 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4) agg.result_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic max_pos integer?)
(define-symbolic ref.tmp integer?)
(define-symbolic softmax_part4_rv_BOUNDEDSET-len integer?)
(define-symbolic softmax_part4_rv_BOUNDEDSET-0 integer?)
(define-symbolic softmax_part4_rv_BOUNDEDSET-1 integer?)
(define-symbolic softmax_part4_rv_BOUNDEDSET-2 integer?)
(define-symbolic softmax_part4_rv_BOUNDEDSET-3 integer?)
(define-symbolic softmax_part4_rv_BOUNDEDSET-4 integer?)
(define softmax_part4_rv (take (list softmax_part4_rv_BOUNDEDSET-0 softmax_part4_rv_BOUNDEDSET-1 softmax_part4_rv_BOUNDEDSET-2 softmax_part4_rv_BOUNDEDSET-3 softmax_part4_rv_BOUNDEDSET-4) softmax_part4_rv_BOUNDEDSET-len))
(define-symbolic sum integer?)
(define-symbolic unnormalized_output_BOUNDEDSET-len integer?)
(define-symbolic unnormalized_output_BOUNDEDSET-0 integer?)
(define-symbolic unnormalized_output_BOUNDEDSET-1 integer?)
(define-symbolic unnormalized_output_BOUNDEDSET-2 integer?)
(define-symbolic unnormalized_output_BOUNDEDSET-3 integer?)
(define-symbolic unnormalized_output_BOUNDEDSET-4 integer?)
(define unnormalized_output (take (list unnormalized_output_BOUNDEDSET-0 unnormalized_output_BOUNDEDSET-1 unnormalized_output_BOUNDEDSET-2 unnormalized_output_BOUNDEDSET-3 unnormalized_output_BOUNDEDSET-4) unnormalized_output_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (> (length unnormalized_output ) 0 ) (<= max_pos (length unnormalized_output ) ) ) (>= max_pos 1 ) ) (softmax_part4_inv0 (list-empty ) 0 max_pos 0 sum unnormalized_output) ) (=> (&& (&& (&& (&& (< i max_pos ) (> (length unnormalized_output ) 0 ) ) (<= max_pos (length unnormalized_output ) ) ) (>= max_pos 1 ) ) (softmax_part4_inv0 agg.result i max_pos ref.tmp sum unnormalized_output) ) (softmax_part4_inv0 (list-append agg.result (quotient-noerr (list-ref-noerr unnormalized_output i ) sum ) ) (+ i 1 ) max_pos (quotient-noerr (list-ref-noerr unnormalized_output i ) sum ) sum unnormalized_output) ) ) (=> (or (&& (&& (&& (&& (! (< i max_pos ) ) (> (length unnormalized_output ) 0 ) ) (<= max_pos (length unnormalized_output ) ) ) (>= max_pos 1 ) ) (softmax_part4_inv0 agg.result i max_pos ref.tmp sum unnormalized_output) ) (&& (&& (&& (&& (&& (! true ) (! (< i max_pos ) ) ) (> (length unnormalized_output ) 0 ) ) (<= max_pos (length unnormalized_output ) ) ) (>= max_pos 1 ) ) (softmax_part4_inv0 agg.result i max_pos ref.tmp sum unnormalized_output) ) ) (softmax_part4_ps unnormalized_output max_pos sum agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4 i max_pos ref.tmp softmax_part4_rv_BOUNDEDSET-len softmax_part4_rv_BOUNDEDSET-0 softmax_part4_rv_BOUNDEDSET-1 softmax_part4_rv_BOUNDEDSET-2 softmax_part4_rv_BOUNDEDSET-3 softmax_part4_rv_BOUNDEDSET-4 sum unnormalized_output_BOUNDEDSET-len unnormalized_output_BOUNDEDSET-0 unnormalized_output_BOUNDEDSET-1 unnormalized_output_BOUNDEDSET-2 unnormalized_output_BOUNDEDSET-3 unnormalized_output_BOUNDEDSET-4)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
