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

(define-grammar (normal_blend_8_inv0_gram active agg.result base i opacity ref.tmp)
 [rv (choose (&& (&& (>= i 0 ) (<= i (length base ) ) ) (equal? agg.result (v0) ) ))]
[v0 (choose (v1) (v2) (v4) (v6))]
[v1 (choose (list-take-noerr base i ) (list-take-noerr active i ))]
[v2 (choose (vec_elemwise_add (v1) (v1)) (vec_elemwise_sub (v1) (v1)) (vec_elemwise_mul (v1) (v1)) (vec_elemwise_div (v1) (v1)) (vec_scalar_add (v3) (v1)) (vec_scalar_sub (v3) (v1)) (vec_scalar_mul (v3) (v1)) (vec_scalar_div (v3) (v1)) (scalar_vec_sub (v3) (v1)) (scalar_vec_div (v3) (v1)))]
[v3 (choose opacity 255)]
[v4 (choose (vec_elemwise_add (v2) (v1)) (vec_elemwise_sub (v2) (v1)) (vec_elemwise_mul (v2) (v1)) (vec_elemwise_div (v2) (v1)) (vec_scalar_add (v3) (v2)) (vec_scalar_sub (v3) (v2)) (vec_scalar_mul (v3) (v2)) (vec_scalar_div (v3) (v2)) (scalar_vec_sub (v3) (v2)) (scalar_vec_div (v3) (v2)) (vec_elemwise_sub (v1) (v2)) (vec_elemwise_div (v1) (v2)) (vec_scalar_add (v5) (v1)) (vec_scalar_sub (v5) (v1)) (vec_scalar_mul (v5) (v1)) (vec_scalar_div (v5) (v1)) (scalar_vec_sub (v5) (v1)) (scalar_vec_div (v5) (v1)) (vec_elemwise_add (v2) (v2)) (vec_elemwise_sub (v2) (v2)) (vec_elemwise_mul (v2) (v2)) (vec_elemwise_div (v2) (v2)) (vec_scalar_add (v5) (v2)) (vec_scalar_sub (v5) (v2)) (vec_scalar_mul (v5) (v2)) (vec_scalar_div (v5) (v2)) (scalar_vec_sub (v5) (v2)) (scalar_vec_div (v5) (v2)))]
[v5 (choose (+ (v3) (v3) ) (- (v3) (v3) ) (* (v3) (v3) ) (quotient-noerr (v3) (v3) ))]
[v6 (choose (vec_elemwise_add (v4) (v1)) (vec_elemwise_sub (v4) (v1)) (vec_elemwise_mul (v4) (v1)) (vec_elemwise_div (v4) (v1)) (vec_scalar_add (v3) (v4)) (vec_scalar_sub (v3) (v4)) (vec_scalar_mul (v3) (v4)) (vec_scalar_div (v3) (v4)) (scalar_vec_sub (v3) (v4)) (scalar_vec_div (v3) (v4)) (vec_elemwise_sub (v1) (v4)) (vec_elemwise_div (v1) (v4)) (vec_scalar_add (v7) (v1)) (vec_scalar_sub (v7) (v1)) (vec_scalar_mul (v7) (v1)) (vec_scalar_div (v7) (v1)) (scalar_vec_sub (v7) (v1)) (scalar_vec_div (v7) (v1)) (vec_elemwise_add (v4) (v2)) (vec_elemwise_sub (v4) (v2)) (vec_elemwise_mul (v4) (v2)) (vec_elemwise_div (v4) (v2)) (vec_scalar_add (v5) (v4)) (vec_scalar_sub (v5) (v4)) (vec_scalar_mul (v5) (v4)) (vec_scalar_div (v5) (v4)) (scalar_vec_sub (v5) (v4)) (scalar_vec_div (v5) (v4)) (vec_elemwise_sub (v2) (v4)) (vec_elemwise_div (v2) (v4)) (vec_scalar_add (v7) (v2)) (vec_scalar_sub (v7) (v2)) (vec_scalar_mul (v7) (v2)) (vec_scalar_div (v7) (v2)) (scalar_vec_sub (v7) (v2)) (scalar_vec_div (v7) (v2)) (vec_elemwise_add (v4) (v4)) (vec_elemwise_sub (v4) (v4)) (vec_elemwise_mul (v4) (v4)) (vec_elemwise_div (v4) (v4)) (vec_scalar_add (v7) (v4)) (vec_scalar_sub (v7) (v4)) (vec_scalar_mul (v7) (v4)) (vec_scalar_div (v7) (v4)) (scalar_vec_sub (v7) (v4)) (scalar_vec_div (v7) (v4)))]
[v7 (choose (+ (v5) (v3) ) (- (v5) (v3) ) (* (v5) (v3) ) (quotient-noerr (v5) (v3) ) (- (v3) (v5) ) (quotient-noerr (v3) (v5) ) (+ (v5) (v5) ) (- (v5) (v5) ) (* (v5) (v5) ) (quotient-noerr (v5) (v5) ))]
)

(define-grammar (normal_blend_8_ps_gram base active opacity normal_blend_8_rv)
 [rv (choose (equal? normal_blend_8_rv (v0) ))]
[v0 (choose (v1) (v2) (v4) (v6))]
[v1 (choose base active)]
[v2 (choose (vec_elemwise_add (v1) (v1)) (vec_elemwise_sub (v1) (v1)) (vec_elemwise_mul (v1) (v1)) (vec_elemwise_div (v1) (v1)) (vec_scalar_add (v3) (v1)) (vec_scalar_sub (v3) (v1)) (vec_scalar_mul (v3) (v1)) (vec_scalar_div (v3) (v1)) (scalar_vec_sub (v3) (v1)) (scalar_vec_div (v3) (v1)))]
[v3 (choose opacity 255)]
[v4 (choose (vec_elemwise_add (v2) (v1)) (vec_elemwise_sub (v2) (v1)) (vec_elemwise_mul (v2) (v1)) (vec_elemwise_div (v2) (v1)) (vec_scalar_add (v3) (v2)) (vec_scalar_sub (v3) (v2)) (vec_scalar_mul (v3) (v2)) (vec_scalar_div (v3) (v2)) (scalar_vec_sub (v3) (v2)) (scalar_vec_div (v3) (v2)) (vec_elemwise_sub (v1) (v2)) (vec_elemwise_div (v1) (v2)) (vec_scalar_add (v5) (v1)) (vec_scalar_sub (v5) (v1)) (vec_scalar_mul (v5) (v1)) (vec_scalar_div (v5) (v1)) (scalar_vec_sub (v5) (v1)) (scalar_vec_div (v5) (v1)) (vec_elemwise_add (v2) (v2)) (vec_elemwise_sub (v2) (v2)) (vec_elemwise_mul (v2) (v2)) (vec_elemwise_div (v2) (v2)) (vec_scalar_add (v5) (v2)) (vec_scalar_sub (v5) (v2)) (vec_scalar_mul (v5) (v2)) (vec_scalar_div (v5) (v2)) (scalar_vec_sub (v5) (v2)) (scalar_vec_div (v5) (v2)))]
[v5 (choose (+ (v3) (v3) ) (- (v3) (v3) ) (* (v3) (v3) ) (quotient-noerr (v3) (v3) ))]
[v6 (choose (vec_elemwise_add (v4) (v1)) (vec_elemwise_sub (v4) (v1)) (vec_elemwise_mul (v4) (v1)) (vec_elemwise_div (v4) (v1)) (vec_scalar_add (v3) (v4)) (vec_scalar_sub (v3) (v4)) (vec_scalar_mul (v3) (v4)) (vec_scalar_div (v3) (v4)) (scalar_vec_sub (v3) (v4)) (scalar_vec_div (v3) (v4)) (vec_elemwise_sub (v1) (v4)) (vec_elemwise_div (v1) (v4)) (vec_scalar_add (v7) (v1)) (vec_scalar_sub (v7) (v1)) (vec_scalar_mul (v7) (v1)) (vec_scalar_div (v7) (v1)) (scalar_vec_sub (v7) (v1)) (scalar_vec_div (v7) (v1)) (vec_elemwise_add (v4) (v2)) (vec_elemwise_sub (v4) (v2)) (vec_elemwise_mul (v4) (v2)) (vec_elemwise_div (v4) (v2)) (vec_scalar_add (v5) (v4)) (vec_scalar_sub (v5) (v4)) (vec_scalar_mul (v5) (v4)) (vec_scalar_div (v5) (v4)) (scalar_vec_sub (v5) (v4)) (scalar_vec_div (v5) (v4)) (vec_elemwise_sub (v2) (v4)) (vec_elemwise_div (v2) (v4)) (vec_scalar_add (v7) (v2)) (vec_scalar_sub (v7) (v2)) (vec_scalar_mul (v7) (v2)) (vec_scalar_div (v7) (v2)) (scalar_vec_sub (v7) (v2)) (scalar_vec_div (v7) (v2)) (vec_elemwise_add (v4) (v4)) (vec_elemwise_sub (v4) (v4)) (vec_elemwise_mul (v4) (v4)) (vec_elemwise_div (v4) (v4)) (vec_scalar_add (v7) (v4)) (vec_scalar_sub (v7) (v4)) (vec_scalar_mul (v7) (v4)) (vec_scalar_div (v7) (v4)) (scalar_vec_sub (v7) (v4)) (scalar_vec_div (v7) (v4)))]
[v7 (choose (+ (v5) (v3) ) (- (v5) (v3) ) (* (v5) (v3) ) (quotient-noerr (v5) (v3) ) (- (v3) (v5) ) (quotient-noerr (v3) (v5) ) (+ (v5) (v5) ) (- (v5) (v5) ) (* (v5) (v5) ) (quotient-noerr (v5) (v5) ))]
)

(define (normal_blend_8_inv0 active agg.result base i opacity ref.tmp) (normal_blend_8_inv0_gram active agg.result base i opacity ref.tmp #:depth 10))
(define (normal_blend_8_ps base active opacity normal_blend_8_rv) (normal_blend_8_ps_gram base active opacity normal_blend_8_rv #:depth 10))

(define-symbolic active_BOUNDEDSET-len integer?)
(define-symbolic active_BOUNDEDSET-0 integer?)
(define-symbolic active_BOUNDEDSET-1 integer?)
(define active (take (list active_BOUNDEDSET-0 active_BOUNDEDSET-1) active_BOUNDEDSET-len))
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic base_BOUNDEDSET-len integer?)
(define-symbolic base_BOUNDEDSET-0 integer?)
(define-symbolic base_BOUNDEDSET-1 integer?)
(define base (take (list base_BOUNDEDSET-0 base_BOUNDEDSET-1) base_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic normal_blend_8_rv_BOUNDEDSET-len integer?)
(define-symbolic normal_blend_8_rv_BOUNDEDSET-0 integer?)
(define-symbolic normal_blend_8_rv_BOUNDEDSET-1 integer?)
(define normal_blend_8_rv (take (list normal_blend_8_rv_BOUNDEDSET-0 normal_blend_8_rv_BOUNDEDSET-1) normal_blend_8_rv_BOUNDEDSET-len))
(define-symbolic opacity integer?)
(define-symbolic ref.tmp integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (equal? (length base ) (length active ) ) (> (length base ) 0 ) ) (normal_blend_8_inv0 active (list-empty ) base 0 opacity 0) ) (=> (&& (&& (&& (< i (length base ) ) (equal? (length base ) (length active ) ) ) (> (length base ) 0 ) ) (normal_blend_8_inv0 active agg.result base i opacity ref.tmp) ) (normal_blend_8_inv0 active (list-append agg.result (+ (* opacity (list-ref-noerr active i ) ) (* (- 255 opacity ) (list-ref-noerr base i ) ) ) ) base (+ i 1 ) opacity (+ (* opacity (list-ref-noerr active i ) ) (* (- 255 opacity ) (list-ref-noerr base i ) ) )) ) ) (=> (or (&& (&& (&& (! (< i (length base ) ) ) (equal? (length base ) (length active ) ) ) (> (length base ) 0 ) ) (normal_blend_8_inv0 active agg.result base i opacity ref.tmp) ) (&& (&& (&& (&& (! true ) (! (< i (length base ) ) ) ) (equal? (length base ) (length active ) ) ) (> (length base ) 0 ) ) (normal_blend_8_inv0 active agg.result base i opacity ref.tmp) ) ) (normal_blend_8_ps base active opacity agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list active_BOUNDEDSET-len active_BOUNDEDSET-0 active_BOUNDEDSET-1 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 base_BOUNDEDSET-len base_BOUNDEDSET-0 base_BOUNDEDSET-1 i normal_blend_8_rv_BOUNDEDSET-len normal_blend_8_rv_BOUNDEDSET-0 normal_blend_8_rv_BOUNDEDSET-1 opacity ref.tmp)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
