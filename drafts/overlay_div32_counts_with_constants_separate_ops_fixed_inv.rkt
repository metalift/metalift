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
  (choose (&& (&& (>= row 0) (<= row (length base)))
              (equal? agg.result
                      (nested_selection_two_args (list-take-noerr base row)
                                                 (list-take-noerr active row)
                                                 fixed_select_two_args))))])

(define-grammar
 (overlay_blend_8_inv1_gram active base col div32 double_base pixel row_vec agg.result row)
 [rv
  (choose (&& (&& (&& (&& (&& (>= row 0) (< row (length base))) (>= col 0))
                      (<= col (length (list-list-ref-noerr base 0))))
                  (equal? row_vec
                          (selection_two_args (list-take-noerr (list-list-ref-noerr base row) col)
                                              (list-take-noerr (list-list-ref-noerr active row) col)
                                              fixed_select_two_args)))
              (equal? agg.result
                      (nested_selection_two_args (list-take-noerr base row)
                                                 (list-take-noerr active row)
                                                 fixed_select_two_args))))])

(define-grammar
 (overlay_blend_8_ps_gram base active overlay_blend_8_rv)
 [rv (choose (equal? overlay_blend_8_rv (nested_selection_two_args (v0) (v0) select_two_args)))]
 [v0 (choose base active)])

(define-grammar (select_two_args_gram int_x int_y)
                [rv (choose (if (v0) (v2) (v29)))]
                [v0 (choose (>= (v1) (v1)))]
                [v1 (choose int_x int_y (* 2 int_x) 16)]
                [v2
                 (choose (- (v1) (v3))
                         (- (v10) (v1))
                         (- (v1) (v10))
                         (- (v12) (v1))
                         (- (v1) (v12))
                         (- (v12) (v7))
                         (- (v7) (v12))
                         (- (v15) (v8))
                         (- (v8) (v15))
                         (- (v17) (v5))
                         (- (v5) (v17))
                         (quotient-noerr (v18) 32)
                         (quotient-noerr (v19) 32)
                         (* (v23) (v24))
                         (* (v10) (v25))
                         (+ (v26) (v1))
                         (+ (v23) (v21))
                         (+ (v26) (v7))
                         (+ (v3) (v20))
                         (+ (v28) (v9))
                         (+ (v29) (v22))
                         (quotient-noerr (v25) 32)
                         (+ (v23) (v1))
                         (+ (v3) (v1))
                         (+ (v29) (v1))
                         (+ (v28) (v1))
                         (- (v1) (v17))
                         (- (v24) 32)
                         (- (v26) 32)
                         (- (v30) 32)
                         (- (v28) 32)
                         (- (v23) (v1))
                         (- (v1) (v23))
                         (- (v32) (v1))
                         (- (v1) (v32))
                         (- (v3) (v1))
                         (* (v37) (v27))
                         (* (v23) (v31))
                         (* (v10) (v1))
                         (* (v38) (v1))
                         (* (v39) (v1))
                         (* (v30) (v1))
                         (* (v17) (v1))
                         (quotient-noerr (v37) 32)
                         (quotient-noerr (v24) 32)
                         (quotient-noerr (v43) 32)
                         (+ (v23) (v44))
                         (+ (v28) (v45))
                         (+ (v29) (v25))
                         (- (v37) (v29))
                         (- (v29) (v37))
                         (- (v23) (v18))
                         (- (v18) (v23))
                         (- (v10) (v45))
                         (- (v45) (v10))
                         (* (v37) (v28))
                         (- (v44) 32)
                         (- (v18) 32)
                         (* (v37) (v1))
                         (* (v23) (v1))
                         (* (v43) (v1))
                         (- (v15) (v1))
                         (- (v1) (v15))
                         (- (v17) (v1))
                         (quotient-noerr (v46) 32)
                         (quotient-noerr (v49) 32)
                         (quotient-noerr (v45) 32)
                         (quotient-noerr (v15) 32)
                         (quotient-noerr (v44) 32)
                         (- (v10) 32)
                         (- (v49) 32)
                         (- (v12) 32)
                         (- (v29) 32)
                         (- (v50) 32)
                         (+ (v38) (v1))
                         (+ (v52) (v1))
                         (+ (v19) (v1))
                         (- (v37) (v1))
                         (- (v1) (v37))
                         (+ (v38) (v5))
                         (+ (v19) (v8))
                         (- (v37) (v4))
                         (- (v4) (v37))
                         (- (v23) (v14))
                         (- (v14) (v23))
                         (- (v3) (v11))
                         (- (v11) (v3))
                         (- (v10) (v9))
                         (- (v9) (v10))
                         (* (v43) (v8))
                         (* (v10) (v22))
                         (* (v38) (v11))
                         (* (v30) (v7))
                         (* (v17) (v20)))]
                [v3
                 (choose (- (v4) 32)
                         (- (v5) 32)
                         (* (v6) (v1))
                         (* (v7) (v1))
                         (- (v8) 32)
                         (quotient-noerr (v7) 32)
                         (quotient-noerr (v9) 32)
                         (quotient-noerr (v5) 32)
                         (* (v7) (v8)))]
                [v4 (choose (* (v1) (v1)) (quotient-noerr (v1) 32))]
                [v5 (choose (* (v1) (v1)))]
                [v6 (choose (- (v1) 32) (quotient-noerr (v1) 32))]
                [v7 (choose (- (v1) 32))]
                [v8 (choose (quotient-noerr (v1) 32))]
                [v9 (choose (- (v1) 32) (* (v1) (v1)))]
                [v10 (choose (+ (v8) (v1)) (quotient-noerr (v11) 32))]
                [v11 (choose (+ (v1) (v1)))]
                [v12
                 (choose (+ (v4) (v1))
                         (* (v11) (v1))
                         (quotient-noerr (v11) 32)
                         (* (v13) (v1))
                         (+ (v8) (v1))
                         (quotient-noerr (v14) 32)
                         (quotient-noerr (v5) 32)
                         (+ (v8) (v5))
                         (* (v11) (v8)))]
                [v13 (choose (+ (v1) (v1)) (quotient-noerr (v1) 32))]
                [v14 (choose (+ (v1) (v1)) (* (v1) (v1)))]
                [v15
                 (choose (+ (v7) (v1))
                         (- (v11) 32)
                         (- (v5) 32)
                         (- (v14) 32)
                         (+ (v9) (v1))
                         (* (v16) (v1))
                         (* (v11) (v1))
                         (+ (v7) (v5))
                         (* (v11) (v7)))]
                [v16 (choose (+ (v1) (v1)) (- (v1) 32))]
                [v17
                 (choose (+ (v7) (v1))
                         (- (v11) 32)
                         (- (v8) 32)
                         (- (v13) 32)
                         (+ (v6) (v1))
                         (quotient-noerr (v16) 32)
                         (quotient-noerr (v11) 32)
                         (quotient-noerr (v7) 32)
                         (+ (v7) (v8)))]
                [v18 (choose (+ (v5) (v1)) (* (v11) (v1)))]
                [v19
                 (choose (- (v7) (v1))
                         (- (v9) (v1))
                         (- (v20) 32)
                         (- (v1) (v9))
                         (- (v1) (v7))
                         (- (v21) 32)
                         (- (v5) 32)
                         (* (v20) (v1))
                         (* (v22) (v1))
                         (- (v7) (v5))
                         (- (v5) (v7))
                         (* (v20) (v7)))]
                [v20 (choose (- (v1) (v1)))]
                [v21 (choose (- (v1) (v1)) (* (v1) (v1)))]
                [v22 (choose (- (v1) (v1)) (- (v1) 32))]
                [v23 (choose (- (v8) 32) (quotient-noerr (v7) 32))]
                [v24 (choose (+ (v20) (v1)) (- (v1) (v11)) (- (v11) (v1)))]
                [v25 (choose (- (v7) (v1)) (- (v20) 32) (- (v1) (v7)))]
                [v26
                 (choose (- (v4) (v1))
                         (- (v8) (v1))
                         (* (v20) (v1))
                         (- (v1) (v8))
                         (- (v1) (v4))
                         (* (v27) (v1))
                         (quotient-noerr (v20) 32)
                         (quotient-noerr (v21) 32)
                         (quotient-noerr (v5) 32)
                         (- (v8) (v5))
                         (- (v5) (v8))
                         (* (v20) (v8)))]
                [v27 (choose (- (v1) (v1)) (quotient-noerr (v1) 32))]
                [v28 (choose (- (v8) (v1)) (quotient-noerr (v20) 32) (- (v1) (v8)))]
                [v29 (choose (* (v8) (v1)) (quotient-noerr (v5) 32))]
                [v30
                 (choose (+ (v20) (v1))
                         (- (v11) (v1))
                         (- (v13) (v1))
                         (- (v1) (v11))
                         (+ (v27) (v1))
                         (- (v1) (v13))
                         (quotient-noerr (v20) 32)
                         (quotient-noerr (v11) 32)
                         (quotient-noerr (v31) 32)
                         (+ (v20) (v8))
                         (- (v11) (v8))
                         (- (v8) (v11)))]
                [v31 (choose (+ (v1) (v1)) (- (v1) (v1)))]
                [v32
                 (choose (quotient-noerr (v11) 32)
                         (quotient-noerr (v14) 32)
                         (+ (v6) (v5))
                         (+ (v7) (v4))
                         (+ (v9) (v8))
                         (* (v16) (v8))
                         (* (v6) (v11))
                         (* (v7) (v13))
                         (- (v14) 32)
                         (* (v16) (v1))
                         (* (v6) (v1))
                         (* (v7) (v1))
                         (* (v33) (v1))
                         (quotient-noerr (v16) 32)
                         (quotient-noerr (v7) 32)
                         (quotient-noerr (v9) 32)
                         (quotient-noerr (v34) 32)
                         (quotient-noerr (v5) 32)
                         (+ (v6) (v1))
                         (+ (v7) (v1))
                         (- (v13) 32)
                         (+ (v9) (v1))
                         (+ (v35) (v1))
                         (- (v8) 32)
                         (- (v36) 32)
                         (- (v4) 32)
                         (- (v5) 32)
                         (- (v11) 32))]
                [v33 (choose (+ (v1) (v1)) (quotient-noerr (v1) 32) (- (v1) 32))]
                [v34 (choose (+ (v1) (v1)) (* (v1) (v1)) (- (v1) 32))]
                [v35 (choose (- (v1) 32) (quotient-noerr (v1) 32) (* (v1) (v1)))]
                [v36 (choose (+ (v1) (v1)) (quotient-noerr (v1) 32) (* (v1) (v1)))]
                [v37 (choose (+ (v7) (v1)) (- (v11) 32))]
                [v38
                 (choose (- (v7) (v1))
                         (- (v6) (v1))
                         (- (v20) 32)
                         (- (v1) (v6))
                         (- (v1) (v7))
                         (- (v27) 32)
                         (- (v8) 32)
                         (quotient-noerr (v20) 32)
                         (quotient-noerr (v7) 32)
                         (quotient-noerr (v22) 32)
                         (- (v7) (v8))
                         (- (v8) (v7)))]
                [v39
                 (choose (+ (v8) (v22))
                         (- (v16) (v8))
                         (- (v8) (v16))
                         (- (v6) (v11))
                         (- (v11) (v6))
                         (- (v7) (v13))
                         (- (v13) (v7))
                         (quotient-noerr (v31) 32)
                         (quotient-noerr (v40) 32)
                         (quotient-noerr (v7) 32)
                         (quotient-noerr (v20) 32)
                         (quotient-noerr (v11) 32)
                         (quotient-noerr (v22) 32)
                         (+ (v6) (v20))
                         (+ (v27) (v7))
                         (- (v33) (v1))
                         (- (v1) (v33))
                         (- (v31) 32)
                         (- (v27) 32)
                         (- (v13) 32)
                         (- (v8) 32)
                         (- (v20) 32)
                         (- (v11) 32)
                         (- (v41) 32)
                         (quotient-noerr (v16) 32)
                         (+ (v6) (v1))
                         (+ (v8) (v1))
                         (- (v16) (v1))
                         (+ (v42) (v1))
                         (+ (v27) (v1))
                         (- (v1) (v16))
                         (- (v6) (v1))
                         (- (v1) (v6))
                         (- (v7) (v1))
                         (- (v1) (v7)))]
                [v40 (choose (+ (v1) (v1)) (- (v1) 32) (- (v1) (v1)))]
                [v41 (choose (+ (v1) (v1)) (quotient-noerr (v1) 32) (- (v1) (v1)))]
                [v42 (choose (- (v1) (v1)) (quotient-noerr (v1) 32) (- (v1) 32))]
                [v43
                 (choose (+ (v20) (v1))
                         (- (v16) (v1))
                         (- (v11) (v1))
                         (- (v1) (v16))
                         (+ (v22) (v1))
                         (- (v1) (v11))
                         (- (v20) 32)
                         (- (v11) 32)
                         (- (v31) 32)
                         (+ (v20) (v7))
                         (- (v11) (v7))
                         (- (v7) (v11)))]
                [v44 (choose (- (v5) (v1)) (* (v20) (v1)) (- (v1) (v5)))]
                [v45 (choose (- (v5) 32) (* (v7) (v1)))]
                [v46
                 (choose (- (v7) (v14))
                         (- (v14) (v7))
                         (- (v9) (v11))
                         (- (v11) (v9))
                         (* (v16) (v20))
                         (* (v31) (v7))
                         (* (v11) (v22))
                         (* (v31) (v1))
                         (* (v40) (v1))
                         (* (v11) (v1))
                         (+ (v7) (v21))
                         (+ (v9) (v20))
                         (+ (v5) (v22))
                         (- (v16) (v5))
                         (- (v5) (v16))
                         (- (v34) (v1))
                         (- (v1) (v34))
                         (- (v31) 32)
                         (- (v47) 32)
                         (- (v20) 32)
                         (- (v21) 32)
                         (- (v5) 32)
                         (- (v11) 32)
                         (- (v14) 32)
                         (* (v16) (v1))
                         (+ (v7) (v1))
                         (+ (v5) (v1))
                         (- (v16) (v1))
                         (+ (v48) (v1))
                         (+ (v9) (v1))
                         (- (v1) (v16))
                         (- (v7) (v1))
                         (- (v1) (v7))
                         (- (v9) (v1))
                         (- (v1) (v9)))]
                [v47 (choose (+ (v1) (v1)) (* (v1) (v1)) (- (v1) (v1)))]
                [v48 (choose (- (v1) (v1)) (* (v1) (v1)) (- (v1) 32))]
                [v49
                 (choose (+ (v20) (v1))
                         (- (v11) (v1))
                         (- (v14) (v1))
                         (- (v1) (v11))
                         (+ (v21) (v1))
                         (- (v1) (v14))
                         (* (v20) (v1))
                         (* (v31) (v1))
                         (+ (v20) (v5))
                         (- (v11) (v5))
                         (- (v5) (v11))
                         (* (v20) (v11)))]
                [v50
                 (choose (- (v8) (v14))
                         (- (v14) (v8))
                         (- (v4) (v11))
                         (- (v11) (v4))
                         (* (v31) (v8))
                         (* (v27) (v11))
                         (* (v13) (v20))
                         (quotient-noerr (v5) 32)
                         (quotient-noerr (v11) 32)
                         (quotient-noerr (v14) 32)
                         (+ (v27) (v5))
                         (+ (v8) (v21))
                         (+ (v4) (v20))
                         (- (v13) (v5))
                         (- (v5) (v13))
                         (- (v4) (v1))
                         (- (v1) (v4))
                         (* (v31) (v1))
                         (* (v27) (v1))
                         (* (v13) (v1))
                         (* (v41) (v1))
                         (quotient-noerr (v31) 32)
                         (quotient-noerr (v47) 32)
                         (quotient-noerr (v20) 32)
                         (quotient-noerr (v21) 32)
                         (+ (v51) (v1))
                         (+ (v8) (v1))
                         (- (v13) (v1))
                         (+ (v4) (v1))
                         (+ (v27) (v1))
                         (- (v1) (v13))
                         (- (v8) (v1))
                         (- (v1) (v8))
                         (- (v36) (v1))
                         (- (v1) (v36)))]
                [v51 (choose (- (v1) (v1)) (quotient-noerr (v1) 32) (* (v1) (v1)))]
                [v52
                 (choose (- (v7) (v4))
                         (- (v4) (v7))
                         (- (v9) (v8))
                         (- (v8) (v9))
                         (* (v6) (v20))
                         (* (v27) (v7))
                         (* (v8) (v22))
                         (quotient-noerr (v9) 32)
                         (quotient-noerr (v20) 32)
                         (quotient-noerr (v21) 32)
                         (quotient-noerr (v5) 32)
                         (quotient-noerr (v22) 32)
                         (quotient-noerr (v48) 32)
                         (- (v6) (v5))
                         (- (v5) (v6))
                         (- (v8) 32)
                         (- (v4) 32)
                         (- (v20) 32)
                         (- (v21) 32)
                         (- (v5) 32)
                         (* (v6) (v1))
                         (* (v27) (v1))
                         (* (v8) (v1))
                         (* (v42) (v1))
                         (quotient-noerr (v7) 32)
                         (- (v6) (v1))
                         (- (v35) (v1))
                         (- (v7) (v1))
                         (- (v1) (v35))
                         (- (v1) (v6))
                         (- (v1) (v7))
                         (- (v9) (v1))
                         (- (v1) (v9))
                         (- (v51) 32)
                         (- (v27) 32))])

(define-grammar (fixed_select_two_args_gram int_x int_y)
                [rv
                 (choose (if (>= int_x 16)
                             (- (- (+ (* 2 int_x) int_x) (quotient-noerr (* (* 2 int_x) int_x) 32))
                                32)
                             (quotient-noerr (* (* 2 int_x) int_x) 32)))])

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
(define (fixed_select_two_args int_x int_y)
  (fixed_select_two_args_gram int_x int_y #:depth 10))

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
