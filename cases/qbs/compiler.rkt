#lang racket

(require "../../lang/ir.rkt"
         "../../lib/vc.rkt"
         "../../lib/synthesis.rkt"
         "../../lib/codegen.rkt"
         "../../lib/analysis.rkt")

(require (only-in "../../lang/base.rkt" ml-lookup))

(require "udos.rkt")

(define (inv-search-space fn vars)

  (define in (hash-ref vars 'in)) 
  (define i (hash-ref vars 'i))
  (define out (hash-ref vars 'select-*-test-ret-val))

  (ml-and boolean?
          (list 
           (mk-list-equal out (call my-select-* (list (mk-list-take in i))))
           (mk-<= i (mk-list-length in))))
  )

; fn is a ml-decl
(define (pc-search-space fn vars)
  
  (define in (hash-ref vars 'in))

  ; choose(pc1, pc2, pc3, ...)
  (ml-choose boolean?
             (list (mk-list-equal (ml-ret-val fn) (call my-select-* (list in)))
                   (mk-list-equal (ml-ret-val fn) in)))
  )

; out = my-select-*(in) 
(define (codegen s) ; s = sketch returned answer
  (define (cg/type t)
    (match t
      [(or (== 'boolean?) (== boolean?)) "bool"]
      [(or (== 'integer?) (== integer?)) "int"]
      [(== '(ml-listof integer?)) "int []"]))
     
  (match s
     
    [(ml-call _ name arg) #:when (eq? name 'my-select-*)
                           (format "SELECT * FROM ~a" (codegen arg))]
    
    [(ml-eq _ e1 e2) (format "~a = ~a" (codegen e1) (codegen e2))]

    [(ml-if _ c e1 e2) (format "if (~a) {~n  ~a;~n} else {~n  ~a;~n}~n" (codegen c) (codegen e1) (codegen e2))]
    
    [(cons (? symbol? e) (? procedure? p)) (format "~a ~a" (cg/type p) e)]

    [(or (? number? e) (? symbol? e)) (format "~a" e)]

    [(? procedure? p) (second (regexp-match #rx"procedure:(.*)>" (format "~a" p)))]

    [(ml-list-equal t e1 e2) (format "~a = ~a" (codegen e1) (codegen e2))]
    
    ))

(require "tests.rkt")

; ideally this would be the API we expose to users
;(lift 'select-*-benchmark inv-search-space pc-search-space codegen)

(define ast (ml-lookup 'select-*-test))

(define-values (checked _) (typecheck ast))

(construct-cfg checked)

(live-vars checked)

(define vc (compute-vc checked))

(define udos-appended (append-udos vc))

(define space-defined (define-space ast udos-appended inv-search-space pc-search-space))

(define sk (to-sk space-defined))

(with-output-to-file "test.sk" #:exists 'replace (lambda () (printf sk)))

;(define choose-resolved (resolve-choose space-defined))
;
;;(to-z3 choose-resolved)
;
;;(define final (codegen qbs-codegen choose-resolved))


