#lang racket

(require "../../lang/ir-ctor.rkt"
         "../../lang/ir.rkt"
         "../../lang/parser.rkt"
         (only-in "../../lang/base.rkt" ml-lookup-by-name)
         "../../lib/vc.rkt"
         "../../lib/synthesis.rkt"
         "../../lib/codegen.rkt"
         "../../lib/analysis.rkt"
         "../../lib/z3.rkt")

(require "udos.rkt")

(define (inv-search-space fn vars vartypes)
  ; Get fn output
  (define out (ml-decl-ret-var fn))
  
  (define grammar (to-ml #'(= out 1)))

  (print grammar)

  ; return a type checked ML ast
  (define-values (ast _) (typecheck grammar vartypes))

  ast
  )


; fn is a ml-decl
(define (pc-search-space fn vars vartypes)
  
  ; return a type checked ML ast
  (define-values (ast _) (typecheck (to-ml #'#t)))

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

(require "benchmarks/blend.rkt")

(define (dexter)
  
  ; Build AST of function
  (define ast (ml-lookup-by-name 'normalBlend8))

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
  
  ; Write Sketch code to file
  (with-output-to-file "test.sk" #:exists 'replace (lambda () (printf sk)))

  ; Run sketch with --bnd-inbits 2
  ;(define choose-resolved (resolve-choose space-defined))

  (void);sk;choose-resolved

  ; should pass choose-resolved instead
  ;(define z3 (to-z3 space-defined "../../z3/mllist.z3"))
  ;(with-output-to-file "test.z3" #:exists 'replace (lambda () (printf z3)))

  ;(define final (codegen cg choose-resolved))
  )

(dexter)