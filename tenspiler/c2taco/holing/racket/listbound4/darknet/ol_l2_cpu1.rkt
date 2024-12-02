#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


 (define-bounded (vec_elemwise_add x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (+ (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_add (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))


 (define-bounded (vec_elemwise_sub x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_sub (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))

(define-grammar (ol_l2_cpu1_inv0_gram agg.result diff i n pred ref.tmp truth)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? agg.result (vec_elemwise_mul (v0) (v0) ) ) ))]
[v0 (choose (v1) (vec_elemwise_sub (v1) (v1) ))]
[v1 (choose (list-take-noerr truth i ) (list-take-noerr pred i ))]
)

(define-grammar (ol_l2_cpu1_ps_gram n pred truth ol_l2_cpu1_rv)
 [rv (choose (equal? ol_l2_cpu1_rv (vec_elemwise_mul (v0) (v0) ) ))]
[v0 (choose (v1) (vec_elemwise_sub (v1) (v1) ))]
[v1 (choose (list-take-noerr truth n ) (list-take-noerr pred n ))]
)

(define (ol_l2_cpu1_inv0 agg.result diff i n pred ref.tmp truth) (ol_l2_cpu1_inv0_gram agg.result diff i n pred ref.tmp truth #:depth 10))
(define (ol_l2_cpu1_ps n pred truth ol_l2_cpu1_rv) (ol_l2_cpu1_ps_gram n pred truth ol_l2_cpu1_rv #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3) agg.result_BOUNDEDSET-len))
(define-symbolic diff integer?)
(define-symbolic i integer?)
(define-symbolic n integer?)
(define-symbolic ol_l2_cpu1_rv_BOUNDEDSET-len integer?)
(define-symbolic ol_l2_cpu1_rv_BOUNDEDSET-0 integer?)
(define-symbolic ol_l2_cpu1_rv_BOUNDEDSET-1 integer?)
(define-symbolic ol_l2_cpu1_rv_BOUNDEDSET-2 integer?)
(define-symbolic ol_l2_cpu1_rv_BOUNDEDSET-3 integer?)
(define ol_l2_cpu1_rv (take (list ol_l2_cpu1_rv_BOUNDEDSET-0 ol_l2_cpu1_rv_BOUNDEDSET-1 ol_l2_cpu1_rv_BOUNDEDSET-2 ol_l2_cpu1_rv_BOUNDEDSET-3) ol_l2_cpu1_rv_BOUNDEDSET-len))
(define-symbolic pred_BOUNDEDSET-len integer?)
(define-symbolic pred_BOUNDEDSET-0 integer?)
(define-symbolic pred_BOUNDEDSET-1 integer?)
(define-symbolic pred_BOUNDEDSET-2 integer?)
(define-symbolic pred_BOUNDEDSET-3 integer?)
(define pred (take (list pred_BOUNDEDSET-0 pred_BOUNDEDSET-1 pred_BOUNDEDSET-2 pred_BOUNDEDSET-3) pred_BOUNDEDSET-len))
(define-symbolic ref.tmp integer?)
(define-symbolic truth_BOUNDEDSET-len integer?)
(define-symbolic truth_BOUNDEDSET-0 integer?)
(define-symbolic truth_BOUNDEDSET-1 integer?)
(define-symbolic truth_BOUNDEDSET-2 integer?)
(define-symbolic truth_BOUNDEDSET-3 integer?)
(define truth (take (list truth_BOUNDEDSET-0 truth_BOUNDEDSET-1 truth_BOUNDEDSET-2 truth_BOUNDEDSET-3) truth_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (>= n 1 ) (>= (length pred ) n ) ) (>= (length truth ) n ) ) (ol_l2_cpu1_inv0 (list-empty ) 0 0 n pred 0 truth) ) (=> (&& (&& (&& (&& (< i n ) (>= n 1 ) ) (>= (length pred ) n ) ) (>= (length truth ) n ) ) (ol_l2_cpu1_inv0 agg.result diff i n pred ref.tmp truth) ) (ol_l2_cpu1_inv0 (list-append agg.result (* (- (list-ref-noerr truth i ) (list-ref-noerr pred i ) ) (- (list-ref-noerr truth i ) (list-ref-noerr pred i ) ) ) ) (- (list-ref-noerr truth i ) (list-ref-noerr pred i ) ) (+ i 1 ) n pred (* (- (list-ref-noerr truth i ) (list-ref-noerr pred i ) ) (- (list-ref-noerr truth i ) (list-ref-noerr pred i ) ) ) truth) ) ) (=> (or (&& (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (>= (length pred ) n ) ) (>= (length truth ) n ) ) (ol_l2_cpu1_inv0 agg.result diff i n pred ref.tmp truth) ) (&& (&& (&& (&& (&& (! true ) (! (< i n ) ) ) (>= n 1 ) ) (>= (length pred ) n ) ) (>= (length truth ) n ) ) (ol_l2_cpu1_inv0 agg.result diff i n pred ref.tmp truth) ) ) (ol_l2_cpu1_ps n pred truth agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 diff i n ol_l2_cpu1_rv_BOUNDEDSET-len ol_l2_cpu1_rv_BOUNDEDSET-0 ol_l2_cpu1_rv_BOUNDEDSET-1 ol_l2_cpu1_rv_BOUNDEDSET-2 ol_l2_cpu1_rv_BOUNDEDSET-3 pred_BOUNDEDSET-len pred_BOUNDEDSET-0 pred_BOUNDEDSET-1 pred_BOUNDEDSET-2 pred_BOUNDEDSET-3 ref.tmp truth_BOUNDEDSET-len truth_BOUNDEDSET-0 truth_BOUNDEDSET-1 truth_BOUNDEDSET-2 truth_BOUNDEDSET-3)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
