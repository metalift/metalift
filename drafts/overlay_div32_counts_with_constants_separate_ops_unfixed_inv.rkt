#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic
         rosette/lib/match
         rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla
    #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla"
    #:options (hash ':seed 0)
))
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
  (choose (list-take-noerr (list-list-ref-noerr base row) col)
          (list-take-noerr (list-list-ref-noerr active row) col))]
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
                [rv (choose (if (v0) (v2) (v27)))]
                [v0 (choose (>= (v1) (v1)))]
                [v1 (choose int_x int_y 16)]
                [v2
                 (choose (* (v3) (* 2 int_x))
                         (* (v6) (* 2 int_x))
                         (* (v8) (* 2 int_x))
                         (* (v13) (* 2 int_x))
                         (* (v14) (* 2 int_x))
                         (* (v17) (* 2 int_x))
                         (* (v23) (* 2 int_x))
                         (* (v24) (* 2 int_x))
                         (quotient-noerr (v3) 32)
                         (quotient-noerr (v25) 32)
                         (- (v24) (v26))
                         (- (v26) (v24))
                         (- (v3) (v27))
                         (- (v27) (v3))
                         (- (v6) (v28))
                         (- (v28) (v6))
                         (- (v13) (v29))
                         (- (v30) 32)
                         (- (v13) 32)
                         (- (v31) 32)
                         (- (v34) 32)
                         (- (v27) 32)
                         (- (v36) 32)
                         (- (v40) 32)
                         (- (v28) 32)
                         (+ (v41) (* 2 int_x))
                         (- (v3) (v1))
                         (- (v1) (v3))
                         (- (v1) (v34))
                         (- (v43) (v1))
                         (- (v1) (v43))
                         (- (v24) (v1))
                         (- (v1) (v24))
                         (- (v25) 32)
                         (- (v44) 32)
                         (- (v32) (v6))
                         (- (v45) (v5))
                         (- (v5) (v45))
                         (- (v13) (v42))
                         (quotient-noerr (v8) 32)
                         (+ (v45) (* 2 int_x))
                         (+ (v30) (* 2 int_x))
                         (+ (v14) (* 2 int_x))
                         (+ (v6) (* 2 int_x))
                         (+ (v46) (* 2 int_x))
                         (- (v1) (v6))
                         (- (v49) (v1))
                         (- (v1) (v49))
                         (- (v45) (v1))
                         (- (v1) (v45))
                         (- (v13) (v1))
                         (- (v1) (v13))
                         (- (v34) (v1))
                         (+ (v27) (* 2 int_x))
                         (+ (v44) (* 2 int_x))
                         (quotient-noerr (v31) 32)
                         (quotient-noerr (v29) 32)
                         (quotient-noerr (v43) 32)
                         (quotient-noerr (v40) 32)
                         (quotient-noerr (v51) 32)
                         (quotient-noerr (v28) 32)
                         (quotient-noerr (v41) 32)
                         (- (v3) (v35))
                         (- (v35) (v3))
                         (- (v6) (v32))
                         (- (v42) (v13))
                         (- (v34) (v4))
                         (- (v4) (v34))
                         (- (v43) (v7))
                         (- (v7) (v43))
                         (- (v29) (v13))
                         (- (v6) (v1))
                         (quotient-noerr (v52) 32)
                         (- (v23) 32))]
                [v3 (choose (+ (v4) (* 2 int_x)) (- (v5) 32))]
                [v4 (choose (- (v1) 32))]
                [v5 (choose (+ (v1) (* 2 int_x)))]
                [v6 (choose (- (v7) 32) (quotient-noerr (v4) 32))]
                [v7 (choose (quotient-noerr (v1) 32))]
                [v8
                 (choose (- (v4) (v5))
                         (- (v5) (v1))
                         (+ (v9) (* 2 int_x))
                         (- (v10) (v1))
                         (- (v1) (v10))
                         (- (v1) (v5))
                         (+ (v11) (* 2 int_x))
                         (- (v11) 32)
                         (- (v5) 32)
                         (- (v12) 32)
                         (- (v5) (v4)))]
                [v9 (choose (- (v1) (v1)) (- (v1) 32))]
                [v10 (choose (+ (v1) (* 2 int_x)) (- (v1) 32))]
                [v11 (choose (- (v1) (v1)))]
                [v12 (choose (+ (v1) (* 2 int_x)) (- (v1) (v1)))]
                [v13 (choose (+ (v7) (* 2 int_x)) (quotient-noerr (v5) 32))]
                [v14
                 (choose (- (v4) (v7))
                         (- (v7) (v4))
                         (- (v11) 32)
                         (- (v1) (v4))
                         (- (v15) (v1))
                         (- (v1) (v15))
                         (- (v16) 32)
                         (- (v4) (v1))
                         (- (v7) 32)
                         (quotient-noerr (v11) 32)
                         (quotient-noerr (v4) 32)
                         (quotient-noerr (v9) 32))]
                [v15 (choose (- (v1) 32) (quotient-noerr (v1) 32))]
                [v16 (choose (- (v1) (v1)) (quotient-noerr (v1) 32))]
                [v17
                 (choose (- (v7) (v10))
                         (- (v15) (v5))
                         (- (v5) (v15))
                         (- (v4) (v18))
                         (- (v18) (v4))
                         (- (v1) (v15))
                         (- (v4) (v1))
                         (- (v1) (v4))
                         (quotient-noerr (v10) 32)
                         (quotient-noerr (v12) 32)
                         (quotient-noerr (v19) 32)
                         (quotient-noerr (v4) 32)
                         (quotient-noerr (v11) 32)
                         (quotient-noerr (v5) 32)
                         (quotient-noerr (v9) 32)
                         (+ (v7) (* 2 int_x))
                         (+ (v20) (* 2 int_x))
                         (- (v1) (v10))
                         (+ (v15) (* 2 int_x))
                         (- (v15) (v1))
                         (- (v1) (v21))
                         (- (v12) 32)
                         (- (v16) 32)
                         (- (v18) 32)
                         (- (v7) 32)
                         (- (v11) 32)
                         (- (v5) 32)
                         (- (v22) 32)
                         (- (v10) (v1))
                         (+ (v16) (* 2 int_x))
                         (- (v21) (v1))
                         (- (v10) (v7)))]
                [v18 (choose (+ (v1) (* 2 int_x)) (quotient-noerr (v1) 32))]
                [v19 (choose (+ (v1) (* 2 int_x)) (- (v1) (v1)) (- (v1) 32))]
                [v20 (choose (- (v1) (v1)) (- (v1) 32) (quotient-noerr (v1) 32))]
                [v21 (choose (+ (v1) (* 2 int_x)) (- (v1) 32) (quotient-noerr (v1) 32))]
                [v22 (choose (+ (v1) (* 2 int_x)) (- (v1) (v1)) (quotient-noerr (v1) 32))]
                [v23
                 (choose (- (v7) (v5))
                         (- (v18) (v1))
                         (+ (v16) (* 2 int_x))
                         (- (v5) (v1))
                         (- (v1) (v5))
                         (- (v1) (v18))
                         (+ (v11) (* 2 int_x))
                         (quotient-noerr (v11) 32)
                         (quotient-noerr (v5) 32)
                         (quotient-noerr (v12) 32)
                         (- (v5) (v7)))]
                [v24
                 (choose (- (v7) 32)
                         (+ (v15) (* 2 int_x))
                         (- (v5) 32)
                         (- (v18) 32)
                         (quotient-noerr (v10) 32)
                         (+ (v4) (* 2 int_x))
                         (quotient-noerr (v5) 32)
                         (quotient-noerr (v4) 32))]
                [v25 (choose (+ (v11) (* 2 int_x)) (- (v5) (v1)) (- (v1) (v5)))]
                [v26 (choose (* (v1) (* 2 int_x)))]
                [v27 (choose (* (v7) (* 2 int_x)) (quotient-noerr (v26) 32))]
                [v28 (choose (+ (v26) (* 2 int_x)) (* (v5) (* 2 int_x)))]
                [v29 (choose (- (v26) 32) (* (v4) (* 2 int_x)))]
                [v30 (choose (- (v7) (v1)) (- (v1) (v7)) (quotient-noerr (v11) 32))]
                [v31
                 (choose (- (v32) (v1))
                         (+ (v33) (* 2 int_x))
                         (- (v5) (v1))
                         (- (v1) (v5))
                         (- (v1) (v32))
                         (+ (v11) (* 2 int_x))
                         (* (v11) (* 2 int_x))
                         (* (v12) (* 2 int_x))
                         (- (v5) (v26))
                         (- (v26) (v5)))]
                [v32 (choose (+ (v1) (* 2 int_x)) (* (v1) (* 2 int_x)))]
                [v33 (choose (- (v1) (v1)) (* (v1) (* 2 int_x)))]
                [v34
                 (choose (quotient-noerr (v5) 32)
                         (+ (v7) (* 2 int_x))
                         (* (v5) (* 2 int_x))
                         (* (v18) (* 2 int_x))
                         (quotient-noerr (v32) 32)
                         (+ (v35) (* 2 int_x))
                         (quotient-noerr (v26) 32))]
                [v35 (choose (* (v1) (* 2 int_x)) (quotient-noerr (v1) 32))]
                [v36
                 (choose (- (v35) (v5))
                         (- (v5) (v35))
                         (- (v1) (v7))
                         (- (v37) (v1))
                         (- (v1) (v37))
                         (quotient-noerr (v33) 32)
                         (quotient-noerr (v26) 32)
                         (quotient-noerr (v5) 32)
                         (quotient-noerr (v32) 32)
                         (- (v18) (v26))
                         (- (v26) (v18))
                         (- (v7) (v32))
                         (+ (v7) (* 2 int_x))
                         (+ (v35) (* 2 int_x))
                         (- (v1) (v18))
                         (+ (v38) (* 2 int_x))
                         (- (v7) (v1))
                         (- (v1) (v35))
                         (* (v12) (* 2 int_x))
                         (* (v16) (* 2 int_x))
                         (* (v18) (* 2 int_x))
                         (* (v22) (* 2 int_x))
                         (quotient-noerr (v12) 32)
                         (quotient-noerr (v39) 32)
                         (quotient-noerr (v11) 32)
                         (- (v18) (v1))
                         (+ (v16) (* 2 int_x))
                         (- (v35) (v1))
                         (- (v32) (v7)))]
                [v37 (choose (+ (v1) (* 2 int_x)) (* (v1) (* 2 int_x)) (quotient-noerr (v1) 32))]
                [v38 (choose (- (v1) (v1)) (* (v1) (* 2 int_x)) (quotient-noerr (v1) 32))]
                [v39 (choose (+ (v1) (* 2 int_x)) (- (v1) (v1)) (* (v1) (* 2 int_x)))]
                [v40 (choose (- (v26) (v1)) (- (v1) (v26)) (* (v11) (* 2 int_x)))]
                [v41
                 (choose (- (v26) (v4))
                         (- (v11) 32)
                         (- (v1) (v4))
                         (- (v42) (v1))
                         (- (v1) (v42))
                         (- (v33) 32)
                         (- (v4) (v1))
                         (- (v26) 32)
                         (* (v11) (* 2 int_x))
                         (* (v9) (* 2 int_x))
                         (- (v4) (v26)))]
                [v42 (choose (- (v1) 32) (* (v1) (* 2 int_x)))]
                [v43
                 (choose (- (v26) 32)
                         (+ (v42) (* 2 int_x))
                         (- (v5) 32)
                         (- (v32) 32)
                         (* (v10) (* 2 int_x))
                         (+ (v4) (* 2 int_x))
                         (* (v5) (* 2 int_x)))]
                [v44
                 (choose (- (v26) (v7))
                         (* (v11) (* 2 int_x))
                         (- (v1) (v35))
                         (- (v7) (v1))
                         (- (v1) (v7))
                         (* (v16) (* 2 int_x))
                         (- (v35) (v1))
                         (quotient-noerr (v11) 32)
                         (quotient-noerr (v33) 32)
                         (quotient-noerr (v26) 32)
                         (- (v7) (v26)))]
                [v45
                 (choose (* (v15) (* 2 int_x))
                         (- (v7) 32)
                         (- (v26) 32)
                         (* (v4) (* 2 int_x))
                         (quotient-noerr (v4) 32)
                         (- (v35) 32)
                         (quotient-noerr (v42) 32)
                         (quotient-noerr (v26) 32))]
                [v46
                 (choose (- (v26) (v15))
                         (- (v4) (v35))
                         (- (v35) (v4))
                         (- (v42) (v7))
                         (- (v7) (v42))
                         (- (v1) (v42))
                         (- (v38) 32)
                         (- (v16) 32)
                         (quotient-noerr (v4) 32)
                         (quotient-noerr (v42) 32)
                         (quotient-noerr (v11) 32)
                         (quotient-noerr (v33) 32)
                         (quotient-noerr (v26) 32)
                         (quotient-noerr (v9) 32)
                         (quotient-noerr (v47) 32)
                         (- (v48) (v1))
                         (- (v1) (v48))
                         (- (v1) (v4))
                         (- (v15) (v1))
                         (- (v42) (v1))
                         (- (v35) 32)
                         (- (v11) 32)
                         (- (v33) 32)
                         (- (v26) 32)
                         (* (v15) (* 2 int_x))
                         (* (v16) (* 2 int_x))
                         (* (v7) (* 2 int_x))
                         (* (v20) (* 2 int_x))
                         (- (v4) (v1))
                         (- (v1) (v15))
                         (- (v7) 32)
                         (- (v15) (v26)))]
                [v47 (choose (- (v1) (v1)) (- (v1) 32) (* (v1) (* 2 int_x)))]
                [v48 (choose (- (v1) 32) (* (v1) (* 2 int_x)) (quotient-noerr (v1) 32))]
                [v49
                 (choose (- (v35) 32)
                         (- (v26) 32)
                         (- (v5) 32)
                         (quotient-noerr (v26) 32)
                         (quotient-noerr (v5) 32)
                         (quotient-noerr (v32) 32)
                         (+ (v4) (* 2 int_x))
                         (+ (v42) (* 2 int_x))
                         (- (v7) 32)
                         (+ (v15) (* 2 int_x))
                         (- (v37) 32)
                         (* (v10) (* 2 int_x))
                         (* (v15) (* 2 int_x))
                         (* (v4) (* 2 int_x))
                         (* (v21) (* 2 int_x))
                         (quotient-noerr (v10) 32)
                         (quotient-noerr (v4) 32)
                         (quotient-noerr (v42) 32)
                         (quotient-noerr (v50) 32)
                         (- (v18) 32)
                         (+ (v48) (* 2 int_x))
                         (- (v32) 32))]
                [v50 (choose (+ (v1) (* 2 int_x)) (- (v1) 32) (* (v1) (* 2 int_x)))]
                [v51 (choose (- (v4) (v1)) (- (v1) (v4)) (- (v11) 32))]
                [v52
                 (choose (- (v42) (v5))
                         (- (v5) (v42))
                         (- (v1) (v4))
                         (- (v42) (v1))
                         (- (v1) (v42))
                         (* (v10) (* 2 int_x))
                         (* (v12) (* 2 int_x))
                         (* (v19) (* 2 int_x))
                         (* (v5) (* 2 int_x))
                         (- (v10) (v26))
                         (- (v26) (v10))
                         (- (v4) (v32))
                         (+ (v26) (* 2 int_x))
                         (+ (v47) (* 2 int_x))
                         (- (v1) (v10))
                         (+ (v4) (* 2 int_x))
                         (- (v4) (v1))
                         (- (v1) (v50))
                         (- (v12) 32)
                         (- (v39) 32)
                         (- (v11) 32)
                         (- (v33) 32)
                         (- (v26) 32)
                         (- (v5) 32)
                         (- (v32) 32)
                         (- (v10) (v1))
                         (+ (v42) (* 2 int_x))
                         (- (v50) (v1))
                         (- (v32) (v4)))])

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
