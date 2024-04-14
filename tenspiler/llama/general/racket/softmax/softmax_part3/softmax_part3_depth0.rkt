#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


 (define-bounded (reduce_max x)
(if (<= (length x ) 1 ) (list-ref-noerr x 0 ) (if (> (list-ref-noerr x 0 ) (reduce_max (list-tail-noerr x 1 )) ) (list-ref-noerr x 0 ) (reduce_max (list-tail-noerr x 1 )) ) ))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))


 (define-bounded (reduce_mul x)
(if (< (length x ) 1 ) 1 (* (list-ref-noerr x 0 ) (reduce_mul (list-tail-noerr x 1 )) ) ))

(define-grammar (softmax_part3_inv0_gram i max_pos output sum)
 [rv (choose (&& (&& (>= i 0 ) (<= i max_pos ) ) (equal? sum (v0) ) ))]
[v0 (choose (reduce_sum (vec-slice-noerr output (v1) (v1) )) (reduce_mul (vec-slice-noerr output (v1) (v1) )) (reduce_max (vec-slice-noerr output (v1) (v1) )))]
[v1 (choose 0 max_pos i)]
)

(define-grammar (softmax_part3_ps_gram output max_pos softmax_part3_rv)
 [rv (choose (equal? softmax_part3_rv (v0) ))]
[v0 (choose (reduce_sum (vec-slice-noerr output (v1) (v1) )) (reduce_mul (vec-slice-noerr output (v1) (v1) )) (reduce_max (vec-slice-noerr output (v1) (v1) )))]
[v1 (choose 0 max_pos)]
)

(define (softmax_part3_inv0 i max_pos output sum) (softmax_part3_inv0_gram i max_pos output sum #:depth 10))
(define (softmax_part3_ps output max_pos softmax_part3_rv) (softmax_part3_ps_gram output max_pos softmax_part3_rv #:depth 10))

(define-symbolic i integer?)
(define-symbolic max_pos integer?)
(define-symbolic output_BOUNDEDSET-len integer?)
(define-symbolic output_BOUNDEDSET-0 integer?)
(define-symbolic output_BOUNDEDSET-1 integer?)
(define output (take (list output_BOUNDEDSET-0 output_BOUNDEDSET-1) output_BOUNDEDSET-len))
(define-symbolic softmax_part3_rv integer?)
(define-symbolic sum integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (> (length output ) 0 ) (<= max_pos (length output ) ) ) (>= max_pos 1 ) ) (softmax_part3_inv0 0 max_pos output 0) ) (=> (&& (&& (&& (&& (< i max_pos ) (> (length output ) 0 ) ) (<= max_pos (length output ) ) ) (>= max_pos 1 ) ) (softmax_part3_inv0 i max_pos output sum) ) (softmax_part3_inv0 (+ i 1 ) max_pos output (+ sum (list-ref-noerr output i ) )) ) ) (=> (&& (&& (&& (&& (! (< i max_pos ) ) (> (length output ) 0 ) ) (<= max_pos (length output ) ) ) (>= max_pos 1 ) ) (softmax_part3_inv0 i max_pos output sum) ) (softmax_part3_ps output max_pos sum) ) )))


    (define sol0
        (synthesize
            #:forall (list i max_pos output_BOUNDEDSET-len output_BOUNDEDSET-0 output_BOUNDEDSET-1 softmax_part3_rv sum)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
