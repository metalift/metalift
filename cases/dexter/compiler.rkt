#lang racket

(require "../../lang/ir-ctor.rkt"
         "../../lang/ir.rkt"
         "../../lang/parser.rkt"
         "../../lib/vc.rkt"
         "../../lib/synthesis.rkt"
         "../../lib/codegen.rkt"
         "../../lib/analysis.rkt"
         "../../lib/z3.rkt")

(require "udos.rkt")

(define (inv-search-space fn vars vartypes)
  ; Get fn output
  (define out (ml-decl-ret-var fn))
  
  (define grammar (to-ml #'#t))

  ;(print grammar)

  ; return a type checked ML ast
  (define-values (ast _) (typecheck grammar vartypes))

  ast
  )


(define (int-vars vars)
  (for/list ([(n v) vars] #:when (equal? (ml-expr-type v) integer?)) v))

(define (int-list-vars vars)
  (for/list ([(n v) vars] #:when (equal? (ml-expr-type v) (listof integer?))) v))

(define (float-list-vars vars)
  (for/list ([(n v) vars] #:when (equal? (ml-expr-type v) (ml-listof flonum?))) v))

(define (bnd-gen vars)
  (ml-choose integer? (for/list ([v (int-vars vars)]) v)))

(define (int-expr-gen vars constants idx)
  (define l (ml-choose (listof integer?) (int-list-vars vars)))
  (define t (mk-list-ref l idx))
  ;(define c (ml-choose integer? (for/list ([c (int-consts vars)]) c))) ;; TODO: extract constants found in input code
  t)

(define (float-expr-gen vars constants idx)
  (define l (ml-choose (ml-listof flonum?) (float-list-vars vars)))
  (define t (mk-list-ref l idx))
  ;(define c (ml-choose integer? (for/list ([c (int-consts vars)]) c))) ;; TODO: extract constants found in input code
  t)

; fn is a ml-decl
(define (pc-search-space fn vars vartypes)
  
  ;; Dexter Grammar 1.0
  ;; - Only 1D assignments
  ;; - Only point stencils

  ; Get name of output variable
  (define outVar (ml-var-name (ml-decl-ret-var fn)))

  (define lower-bound-opts (bnd-gen vars))
  (define upper-bound-opts (bnd-gen vars))

  (define expr-grm (float-expr-gen vars vars (to-ml #'idx)))

  (define grammar (mk-block
                   (to-ml #'(define ret boolean? #t))
                   (ml-define integer? (to-ml #'idx) lower-bound-opts)
                   (mk-while (mk-< (to-ml #'idx) upper-bound-opts)
                             (mk-block
                              (mk-set! (to-ml #'ret) (mk-and (to-ml #'ret) (mk-= (to-ml #`(list-ref #,outVar #'idx)) expr-grm)))
                              (to-ml #'(set! idx (+ idx 1)))
                             ))
                   (to-ml #'ret)))

  ; return a type checked ML ast
  (define-values (ast _) (typecheck grammar vartypes))

  ast
  )

; Code Generator (to be implemented)
(define (cg s) ; s = sketch/z3 returned answer
  s
  )

; *** Dexter Pipeline ***

;(lift 'select-*-benchmark inv-search-space pc-search-space cg)

; Turn off print statements
(debug-parser #f)
(debug-analysis #f)
(debug-vc #f)
(debug-sk-codegen #f)

(define (dexter filename fn_name)
  ; Parse 
  (define fns (parse filename))

  ; Build AST of function
  (define ast (hash-ref fns fn_name))

  ; Run type-checker on AST
  (define-values (checked _) (typecheck ast))

  ; Build control-flow graph
  (construct-cfg checked)

  ; Run live-vars analysis
  (live-vars checked)

  ; Compute verification conditions
  (define vc (compute-vc checked))

  ; Append DSL operators
  (define udos-appended (append-udos vc))

  ; Stich search-space grammar
  (define space-defined (define-space ast udos-appended inv-search-space pc-search-space))

  ; Compile SyGuS problem to Sketch
  (define sk (to-sk space-defined))

  (printf sk)
  
  ; Write Sketch code to file
  ;(with-output-to-file "test.sk" #:exists 'replace (lambda () (printf sk)))

  ; Run sketch with --bnd-inbits 2
  ;(define choose-resolved (resolve-choose space-defined))

  (void);sk;choose-resolved

  ; should pass choose-resolved instead
  ;(define z3 (to-z3 space-defined "../../z3/mllist.z3"))
  ;(with-output-to-file "test.z3" #:exists 'replace (lambda () (printf z3)))

  ;(define final (codegen cg choose-resolved))
  )

(dexter "benchmarks/blend.rkt" 'normalBlendf)
;(dexter 'normalBlend8)
;(dexter 'darkenBlend8)