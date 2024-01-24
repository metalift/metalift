#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (reduce_max x)
(if (<= (length x ) 1 ) (list-ref-noerr x 0 ) (if (> (list-ref-noerr x 0 ) (reduce_max (list-tail-noerr x 1 )) ) (list-ref-noerr x 0 ) (reduce_max (list-tail-noerr x 1 )) ) ))

(define-grammar (softmax_part1_inv0_gram i input max_pos max_val)
 [rv (choose (&& (&& (>= i 1 ) (<= i max_pos ) ) (equal? max_val (reduce_max (list-slice-noerr input 1 i )) ) ))]

)

(define-grammar (softmax_part1_ps_gram input max_pos softmax_part1_rv)
 [rv (choose (equal? softmax_part1_rv (reduce_max (v0)) ))]
[v0 (choose (list-slice-noerr input 1 max_pos ))]
)

(define (softmax_part1_inv0 i input max_pos max_val) (softmax_part1_inv0_gram i input max_pos max_val #:depth 10))
(define (softmax_part1_ps input max_pos softmax_part1_rv) (softmax_part1_ps_gram input max_pos softmax_part1_rv #:depth 10))

(define-symbolic i integer?)
(define-symbolic input_BOUNDEDSET-len integer?)
(define-symbolic input_BOUNDEDSET-0 integer?)
(define-symbolic input_BOUNDEDSET-1 integer?)
(define-symbolic input_BOUNDEDSET-2 integer?)
(define-symbolic input_BOUNDEDSET-3 integer?)
(define input (take (list input_BOUNDEDSET-0 input_BOUNDEDSET-1 input_BOUNDEDSET-2 input_BOUNDEDSET-3) input_BOUNDEDSET-len))
(define-symbolic max_pos integer?)
(define-symbolic max_val integer?)
(define-symbolic softmax_part1_rv integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (> (length input ) 0 ) (<= max_pos (length input ) ) ) (>= max_pos 1 ) ) (softmax_part1_inv0 1 input max_pos (list-ref-noerr input 0 )) ) (=> (or (&& (&& (&& (&& (< i max_pos ) (> (length input ) 0 ) ) (<= max_pos (length input ) ) ) (>= max_pos 1 ) ) (softmax_part1_inv0 i input max_pos max_val) ) (&& (&& (&& (&& (&& (> (list-ref-noerr input i ) max_val ) (< i max_pos ) ) (> (length input ) 0 ) ) (<= max_pos (length input ) ) ) (>= max_pos 1 ) ) (softmax_part1_inv0 i input max_pos max_val) ) ) (softmax_part1_inv0 (+ i 1 ) input max_pos (if (&& (&& (&& (&& (&& (> (list-ref-noerr input i ) max_val ) (< i max_pos ) ) (> (length input ) 0 ) ) (<= max_pos (length input ) ) ) (>= max_pos 1 ) ) (softmax_part1_inv0 i input max_pos max_val) ) (list-ref-noerr input i ) max_val )) ) ) (=> (&& (&& (&& (&& (! (< i max_pos ) ) (> (length input ) 0 ) ) (<= max_pos (length input ) ) ) (>= max_pos 1 ) ) (softmax_part1_inv0 i input max_pos max_val) ) (softmax_part1_ps input max_pos max_val) ) )))


    (define sol0
        (synthesize
            #:forall (list i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 input_BOUNDEDSET-2 input_BOUNDEDSET-3 max_pos max_val softmax_part1_rv)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
