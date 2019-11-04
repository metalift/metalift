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

  ; return a type checked ML ast
  (define-values (ast _) (typecheck (to-ml #'#t)))

  ast
  )


; fn is a ml-decl
(define (pc-search-space fn vars vartypes)
  
  (define out (ml-decl-ret-var fn))

  ; postcondition for bitwise-ops
  (define-values (ast _) (typecheck (to-ml #`(= #,(ml-var-name out) (bitwise-not (arithmetic-shift (bitwise-ior i (bitwise-and i i)) 2))))
                                    vartypes))
  
  ast
  )

; code generator (to be implemented)
(define (cg s) ; s = sketch/z3 returned answer
  s
  )

; *** compiler main code below ***

(require "tests.rkt")

; ideally this would be the API we expose to users
;(lift 'select-*-benchmark inv-search-space pc-search-space cg)

; this is the current pipeline

;(define ast (ml-lookup-by-name 'blur-1x3))
(define ast (ml-lookup-by-name 'bitwise-ops))

(define-values (checked _) (typecheck ast))

(construct-cfg checked)

(live-vars checked)

(define vc (compute-vc checked))

(define udos-appended (append-udos vc))

(define space-defined (define-space ast udos-appended inv-search-space pc-search-space))

; run sketch with --bnd-inbits 2
(define sk (to-sk space-defined))
(with-output-to-file "test.sk" #:exists 'replace (lambda () (printf sk)))

;(define choose-resolved (resolve-choose space-defined))
;
;(define z3 (to-z3 choose-resolved "../../z3/mllist.z3"))
;(with-output-to-file "test.z3" #:exists 'replace (lambda () (printf z3)))
;
;(define final (codegen cg choose-resolved))