#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic
         rosette/lib/match
         rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla"
                          #:options (hash ':seed 0)))
(current-solver)

(define-bounded (selection_two_args x y select_two_args_arg)
                (if (or (< (length x) 1) (! (equal? (length x) (length y))))
                    (list-empty)
                    (list-prepend (select_two_args_arg (list-ref-noerr x 0) (list-ref-noerr y 0))
                                  (selection_two_args (list-tail-noerr x 1)
                                                      (list-tail-noerr y 1)
                                                      select_two_args_arg))))

(define-bounded (nested_selection_two_args nested_x nested_y select_two_args_arg)
                (if (or (< (length nested_x) 1) (! (equal? (length nested_x) (length nested_y))))
                    (list-empty)
                    (list-prepend (selection_two_args (list-list-ref-noerr nested_x 0)
                                                      (list-list-ref-noerr nested_y 0)
                                                      select_two_args_arg)
                                  (nested_selection_two_args (list-tail-noerr nested_x 1)
                                                             (list-tail-noerr nested_y 1)
                                                             select_two_args_arg))))

(define-grammar
 (overlay_blend_8_inv0_gram active agg.result base col div32 double_base pixel row row_vec)
 [rv
  (choose (&& (&& (v0) (v2))
              (equal? agg.result (nested_selection_two_args (v4) (v4) select_two_args))))]
 [v0 (choose (>= row (v1)))]
 [v1 (choose 0 1)]
 [v2 (choose (<= row (v3)))]
 [v3
  (choose (length base)
          (length (list-list-ref-noerr base 0))
          (length active)
          (length (list-list-ref-noerr active 0)))]
 [v4
  (choose base
          (list-take-noerr base row)
          (list-take-noerr base col)
          active
          (list-take-noerr active row)
          (list-take-noerr active col))])

(define-grammar
 (overlay_blend_8_inv1_gram active base col div32 double_base pixel row_vec agg.result row)
 [rv
  (choose (&& (&& (&& (&& (&& (v0) (v2)) (v4)) (v5))
                  (equal? row_vec (selection_two_args (v6) (v6) select_two_args)))
              (equal? agg.result (nested_selection_two_args (v7) (v7) select_two_args))))]
 [v0 (choose (>= row (v1)))]
 [v1 (choose 0 1)]
 [v2 (choose (< row (v3)))]
 [v3
  (choose (length base)
          (length (list-list-ref-noerr base 0))
          (length active)
          (length (list-list-ref-noerr active 0)))]
 [v4 (choose (>= col (v1)))]
 [v5 (choose (<= col (v3)))]
 [v6
  (choose (list-take-noerr (list-list-ref-noerr base 0) col)
          (list-take-noerr (list-list-ref-noerr base row) col)
          (list-take-noerr (list-list-ref-noerr base col) row)
          (list-take-noerr (list-list-ref-noerr base 0) row)
          (list-take-noerr (list-list-ref-noerr active 0) col)
          (list-take-noerr (list-list-ref-noerr active row) col)
          (list-take-noerr (list-list-ref-noerr active col) row)
          (list-take-noerr (list-list-ref-noerr active 0) row))]
 [v7
  (choose base
          (list-take-noerr base row)
          (list-take-noerr base col)
          active
          (list-take-noerr active row)
          (list-take-noerr active col))])

(define-grammar
 (overlay_blend_8_ps_gram base active overlay_blend_8_rv)
 [rv (choose (equal? overlay_blend_8_rv (nested_selection_two_args (v0) (v0) select_two_args)))]
 [v0 (choose base active)])

(define-grammar (select_two_args_gram int_x int_y)
                [rv (choose (if (v0) (v2) (v1)))]
                [v0 (choose (>= (v1) (v1)))]
                [v1
                 (choose int_x int_y (* 2 int_x) (quotient-noerr (* (* 2 int_x) int_x) 32) 2 16 32)]
                [v2
                 (choose (- (v3) (v1))
                         (- (v1) (v4))
                         (+ (v3) (v1))
                         (- (v4) (v1))
                         (+ (v3) (v3))
                         (- (v3) (v5))
                         (- (v5) (v3))
                         (- (v1) (v3)))]
                [v3 (choose (- (v1) (v1)))]
                [v4 (choose (- (v1) (v1)) (+ (v1) (v1)))]
                [v5 (choose (+ (v1) (v1)))])

(define (overlay_blend_8_inv0 active agg.result base col div32 double_base pixel row row_vec)
  (overlay_blend_8_inv0_gram active
                             agg.result
                             base
                             col
                             div32
                             double_base
                             pixel
                             row
                             row_vec
                             #:depth 10))
(define (overlay_blend_8_inv1 active base col div32 double_base pixel row_vec agg.result row)
  (overlay_blend_8_inv1_gram active
                             base
                             col
                             div32
                             double_base
                             pixel
                             row_vec
                             agg.result
                             row
                             #:depth 10))
(define (overlay_blend_8_ps base active overlay_blend_8_rv)
  (overlay_blend_8_ps_gram base active overlay_blend_8_rv #:depth 10))

(define (select_two_args int_x int_y)
  (select_two_args_gram int_x int_y #:depth 10))

(define-symbolic active_BOUNDEDSET-len integer?)
(define-symbolic active_BOUNDEDSET-0 integer?)
(define-symbolic active_BOUNDEDSET-1 integer?)
(define-symbolic active_BOUNDEDSET-2 integer?)
(define-symbolic active_BOUNDEDSET-3 integer?)
(define active
  (take (list (list active_BOUNDEDSET-0 active_BOUNDEDSET-1)
              (list active_BOUNDEDSET-2 active_BOUNDEDSET-3))
        active_BOUNDEDSET-len))
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define agg.result
  (take (list (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1)
              (list agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3))
        agg.result_BOUNDEDSET-len))
(define-symbolic base_BOUNDEDSET-len integer?)
(define-symbolic base_BOUNDEDSET-0 integer?)
(define-symbolic base_BOUNDEDSET-1 integer?)
(define-symbolic base_BOUNDEDSET-2 integer?)
(define-symbolic base_BOUNDEDSET-3 integer?)
(define base
  (take (list (list base_BOUNDEDSET-0 base_BOUNDEDSET-1) (list base_BOUNDEDSET-2 base_BOUNDEDSET-3))
        base_BOUNDEDSET-len))
(define-symbolic col integer?)
(define-symbolic div32 integer?)
(define-symbolic double_base integer?)
(define-symbolic overlay_blend_8_rv_BOUNDEDSET-len integer?)
(define-symbolic overlay_blend_8_rv_BOUNDEDSET-0 integer?)
(define-symbolic overlay_blend_8_rv_BOUNDEDSET-1 integer?)
(define overlay_blend_8_rv
  (take (list overlay_blend_8_rv_BOUNDEDSET-0 overlay_blend_8_rv_BOUNDEDSET-1)
        overlay_blend_8_rv_BOUNDEDSET-len))
(define-symbolic pixel integer?)
(define-symbolic row integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1) row_vec_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
  (assert
   (&&
    (&&
     (&&
      (&&
       (=> (&& (&& (> (length base) 1) (equal? (length base) (length active)))
               (equal? (length (list-list-ref-noerr base 0)) (length (list-list-ref-noerr active 0))))
           (overlay_blend_8_inv0 active (list-empty) base 0 0 0 0 0 (list-empty)))
       (=> (&& (&& (&& (&& (< row (length base)) (> (length base) 1))
                       (equal? (length base) (length active)))
                   (equal? (length (list-list-ref-noerr base 0))
                           (length (list-list-ref-noerr active 0))))
               (overlay_blend_8_inv0 active agg.result base col div32 double_base pixel row row_vec))
           (overlay_blend_8_inv1 active base 0 div32 double_base pixel (list-empty) agg.result row)))
      (=>
       (or
        (&& (&& (&& (&& (&& (&& (&& (>= (list-ref-noerr (list-list-ref-noerr base row) col) 16)
                                    (< col (length (list-list-ref-noerr base 0))))
                                (< row (length base)))
                            (> (length base) 1))
                        (equal? (length base) (length active)))
                    (equal? (length (list-list-ref-noerr base 0))
                            (length (list-list-ref-noerr active 0))))
                (overlay_blend_8_inv0 active agg.result base col div32 double_base pixel row row_vec))
            (overlay_blend_8_inv1 active base col div32 double_base pixel row_vec agg.result row))
        (&& (&& (&& (&& (&& (&& (&& (! (>= (list-ref-noerr (list-list-ref-noerr base row) col) 16))
                                    (< col (length (list-list-ref-noerr base 0))))
                                (< row (length base)))
                            (> (length base) 1))
                        (equal? (length base) (length active)))
                    (equal? (length (list-list-ref-noerr base 0))
                            (length (list-list-ref-noerr active 0))))
                (overlay_blend_8_inv0 active agg.result base col div32 double_base pixel row row_vec))
            (overlay_blend_8_inv1 active base col div32 double_base pixel row_vec agg.result row)))
       (overlay_blend_8_inv1
        active
        base
        (+ col 1)
        (quotient-noerr (* (* 2 (list-ref-noerr (list-list-ref-noerr base row) col))
                           (list-ref-noerr (list-list-ref-noerr base row) col))
                        32)
        (* 2 (list-ref-noerr (list-list-ref-noerr base row) col))
        (if (&&
             (&&
              (&& (&& (&& (&& (&& (! (>= (list-ref-noerr (list-list-ref-noerr base row) col) 16))
                                  (< col (length (list-list-ref-noerr base 0))))
                              (< row (length base)))
                          (> (length base) 1))
                      (equal? (length base) (length active)))
                  (equal? (length (list-list-ref-noerr base 0))
                          (length (list-list-ref-noerr active 0))))
              (overlay_blend_8_inv0 active agg.result base col div32 double_base pixel row row_vec))
             (overlay_blend_8_inv1 active base col div32 double_base pixel row_vec agg.result row))
            (quotient-noerr (* (* 2 (list-ref-noerr (list-list-ref-noerr base row) col))
                               (list-ref-noerr (list-list-ref-noerr base row) col))
                            32)
            (- (- (+ (* 2 (list-ref-noerr (list-list-ref-noerr base row) col))
                     (list-ref-noerr (list-list-ref-noerr base row) col))
                  (quotient-noerr (* (* 2 (list-ref-noerr (list-list-ref-noerr base row) col))
                                     (list-ref-noerr (list-list-ref-noerr base row) col))
                                  32))
               32))
        (list-list-append
         row_vec
         (if (&&
              (&&
               (&& (&& (&& (&& (&& (! (>= (list-ref-noerr (list-list-ref-noerr base row) col) 16))
                                   (< col (length (list-list-ref-noerr base 0))))
                               (< row (length base)))
                           (> (length base) 1))
                       (equal? (length base) (length active)))
                   (equal? (length (list-list-ref-noerr base 0))
                           (length (list-list-ref-noerr active 0))))
               (overlay_blend_8_inv0 active agg.result base col div32 double_base pixel row row_vec))
              (overlay_blend_8_inv1 active base col div32 double_base pixel row_vec agg.result row))
             (quotient-noerr (* (* 2 (list-ref-noerr (list-list-ref-noerr base row) col))
                                (list-ref-noerr (list-list-ref-noerr base row) col))
                             32)
             (- (- (+ (* 2 (list-ref-noerr (list-list-ref-noerr base row) col))
                      (list-ref-noerr (list-list-ref-noerr base row) col))
                   (quotient-noerr (* (* 2 (list-ref-noerr (list-list-ref-noerr base row) col))
                                      (list-ref-noerr (list-list-ref-noerr base row) col))
                                   32))
                32)))
        agg.result
        row)))
     (=>
      (&& (&& (&& (&& (&& (&& (! (< col (length (list-list-ref-noerr base 0)))) (< row (length base)))
                          (> (length base) 1))
                      (equal? (length base) (length active)))
                  (equal? (length (list-list-ref-noerr base 0))
                          (length (list-list-ref-noerr active 0))))
              (overlay_blend_8_inv0 active agg.result base col div32 double_base pixel row row_vec))
          (overlay_blend_8_inv1 active base col div32 double_base pixel row_vec agg.result row))
      (overlay_blend_8_inv0 active
                            (list-list-append agg.result row_vec)
                            base
                            col
                            div32
                            double_base
                            pixel
                            (+ row 1)
                            row_vec)))
    (=>
     (or
      (&& (&& (&& (&& (! (< row (length base))) (> (length base) 1))
                  (equal? (length base) (length active)))
              (equal? (length (list-list-ref-noerr base 0)) (length (list-list-ref-noerr active 0))))
          (overlay_blend_8_inv0 active agg.result base col div32 double_base pixel row row_vec))
      (&& (&& (&& (&& (&& (! true) (! (< row (length base)))) (> (length base) 1))
                  (equal? (length base) (length active)))
              (equal? (length (list-list-ref-noerr base 0)) (length (list-list-ref-noerr active 0))))
          (overlay_blend_8_inv0 active agg.result base col div32 double_base pixel row row_vec)))
     (overlay_blend_8_ps base active agg.result)))))

(define sol
  (synthesize #:forall (list active_BOUNDEDSET-len
                             active_BOUNDEDSET-0
                             active_BOUNDEDSET-1
                             active_BOUNDEDSET-2
                             active_BOUNDEDSET-3
                             agg.result_BOUNDEDSET-len
                             agg.result_BOUNDEDSET-0
                             agg.result_BOUNDEDSET-1
                             agg.result_BOUNDEDSET-2
                             agg.result_BOUNDEDSET-3
                             base_BOUNDEDSET-len
                             base_BOUNDEDSET-0
                             base_BOUNDEDSET-1
                             base_BOUNDEDSET-2
                             base_BOUNDEDSET-3
                             col
                             div32
                             double_base
                             overlay_blend_8_rv_BOUNDEDSET-len
                             overlay_blend_8_rv_BOUNDEDSET-0
                             overlay_blend_8_rv_BOUNDEDSET-1
                             pixel
                             row
                             row_vec_BOUNDEDSET-len
                             row_vec_BOUNDEDSET-0
                             row_vec_BOUNDEDSET-1)
              #:guarantee (assertions)))
(sat? sol)
(print-forms sol)
