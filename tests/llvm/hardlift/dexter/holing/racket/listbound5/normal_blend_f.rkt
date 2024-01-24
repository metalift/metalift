#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_elemwise_add x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (+ (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_add (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 )) ) ))

(define-grammar (normal_blend_f_inv0_gram active agg.result base i opacity ref.tmp)
 [rv (choose (&& (&& (>= i 0 ) (<= i (length base ) ) ) (equal? agg.result (vec_elemwise_add (vec_scalar_mul (v0) (v1)) (vec_scalar_mul (- (v2) (v0) ) (v1))) ) ))]
[v0 (choose opacity)]
[v1 (choose (list-take-noerr base i ) (list-take-noerr active i ))]
[v2 (choose 1)]
)

(define-grammar (normal_blend_f_ps_gram base active opacity normal_blend_f_rv)
 [rv (choose (equal? normal_blend_f_rv (vec_elemwise_add (vec_scalar_mul (v0) (v1)) (vec_scalar_mul (- (v2) (v0) ) (v1))) ))]
[v0 (choose opacity)]
[v1 (choose base active)]
[v2 (choose 1)]
)

(define (normal_blend_f_inv0 active agg.result base i opacity ref.tmp) (normal_blend_f_inv0_gram active agg.result base i opacity ref.tmp #:depth 10))
(define (normal_blend_f_ps base active opacity normal_blend_f_rv) (normal_blend_f_ps_gram base active opacity normal_blend_f_rv #:depth 10))

(define-symbolic active_BOUNDEDSET-len integer?)
(define-symbolic active_BOUNDEDSET-0 integer?)
(define-symbolic active_BOUNDEDSET-1 integer?)
(define-symbolic active_BOUNDEDSET-2 integer?)
(define-symbolic active_BOUNDEDSET-3 integer?)
(define-symbolic active_BOUNDEDSET-4 integer?)
(define active (take (list active_BOUNDEDSET-0 active_BOUNDEDSET-1 active_BOUNDEDSET-2 active_BOUNDEDSET-3 active_BOUNDEDSET-4) active_BOUNDEDSET-len))
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define-symbolic agg.result_BOUNDEDSET-4 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4) agg.result_BOUNDEDSET-len))
(define-symbolic base_BOUNDEDSET-len integer?)
(define-symbolic base_BOUNDEDSET-0 integer?)
(define-symbolic base_BOUNDEDSET-1 integer?)
(define-symbolic base_BOUNDEDSET-2 integer?)
(define-symbolic base_BOUNDEDSET-3 integer?)
(define-symbolic base_BOUNDEDSET-4 integer?)
(define base (take (list base_BOUNDEDSET-0 base_BOUNDEDSET-1 base_BOUNDEDSET-2 base_BOUNDEDSET-3 base_BOUNDEDSET-4) base_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic normal_blend_f_rv_BOUNDEDSET-len integer?)
(define-symbolic normal_blend_f_rv_BOUNDEDSET-0 integer?)
(define-symbolic normal_blend_f_rv_BOUNDEDSET-1 integer?)
(define-symbolic normal_blend_f_rv_BOUNDEDSET-2 integer?)
(define-symbolic normal_blend_f_rv_BOUNDEDSET-3 integer?)
(define-symbolic normal_blend_f_rv_BOUNDEDSET-4 integer?)
(define normal_blend_f_rv (take (list normal_blend_f_rv_BOUNDEDSET-0 normal_blend_f_rv_BOUNDEDSET-1 normal_blend_f_rv_BOUNDEDSET-2 normal_blend_f_rv_BOUNDEDSET-3 normal_blend_f_rv_BOUNDEDSET-4) normal_blend_f_rv_BOUNDEDSET-len))
(define-symbolic opacity integer?)
(define-symbolic ref.tmp integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (equal? (length base ) (length active ) ) (> (length base ) 0 ) ) (normal_blend_f_inv0 active (list-empty ) base 0 opacity 0) ) (=> (&& (&& (&& (< i (length base ) ) (equal? (length base ) (length active ) ) ) (> (length base ) 0 ) ) (normal_blend_f_inv0 active agg.result base i opacity ref.tmp) ) (normal_blend_f_inv0 active (list-append agg.result (+ (* opacity (list-ref-noerr active i ) ) (* (- 1 opacity ) (list-ref-noerr base i ) ) ) ) base (+ i 1 ) opacity (+ (* opacity (list-ref-noerr active i ) ) (* (- 1 opacity ) (list-ref-noerr base i ) ) )) ) ) (=> (or (&& (&& (&& (! (< i (length base ) ) ) (equal? (length base ) (length active ) ) ) (> (length base ) 0 ) ) (normal_blend_f_inv0 active agg.result base i opacity ref.tmp) ) (&& (&& (&& (&& (! true ) (! (< i (length base ) ) ) ) (equal? (length base ) (length active ) ) ) (> (length base ) 0 ) ) (normal_blend_f_inv0 active agg.result base i opacity ref.tmp) ) ) (normal_blend_f_ps base active opacity agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list active_BOUNDEDSET-len active_BOUNDEDSET-0 active_BOUNDEDSET-1 active_BOUNDEDSET-2 active_BOUNDEDSET-3 active_BOUNDEDSET-4 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4 base_BOUNDEDSET-len base_BOUNDEDSET-0 base_BOUNDEDSET-1 base_BOUNDEDSET-2 base_BOUNDEDSET-3 base_BOUNDEDSET-4 i normal_blend_f_rv_BOUNDEDSET-len normal_blend_f_rv_BOUNDEDSET-0 normal_blend_f_rv_BOUNDEDSET-1 normal_blend_f_rv_BOUNDEDSET-2 normal_blend_f_rv_BOUNDEDSET-3 normal_blend_f_rv_BOUNDEDSET-4 opacity ref.tmp)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
