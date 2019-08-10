#lang racket

(require "../../lang/ir.rkt"
         "../../lib/vc.rkt"
         "../../lib/synthesis.rkt"
         "../../lib/codegen.rkt"
         "../../lib/analysis.rkt"
         "../../lib/z3.rkt"
         (only-in "../../lang/base.rkt" ml-lookup))

(require "udos.rkt")

(define (inv-search-space fn vars)

  (define in (hash-ref vars 'in)) 
  (define i (hash-ref vars 'i))
  (define out (hash-ref vars 'select-*-test-ret-val))

  (mk-and (list-equal out (call my-select-* (list-take in i)))
          (mk-<= i (list-length in))
          (mk->= i (ml-lit integer? 0))
          )
  )

; fn is a ml-decl
(define (pc-search-space fn vars)
  
  (define in (hash-ref vars 'in))
  (define out (ml-ret-val fn))

  ; choose(pc1, pc2, pc3, ...)
  (choose (list-equal out (call my-select-* in)) ; out = my-select-*(in)
          (list-equal out in))  ; out = in
  )

; out = my-select-*(in) 
(define (cg s) ; s = sketch/z3 returned answer

  (define (cg/type t)
    (match t
      [(or (== 'boolean?) (== boolean?)) "bool"]
      [(or (== 'integer?) (== integer?)) "int"]))
    
  (match s
     
    [(ml-call _ name args)
     #:when (equal? (second (regexp-match #rx"procedure:(.*)>" (format "~a" name))) "my-select-*")     
     (format "SELECT * FROM ~a" (cg (first args)))]

    [(ml-block _ es) (format "~a" (string-join (for/list ([e es]) (cg e)) "~n"))]
    
    [(ml-eq _ e1 e2) (format "~a = ~a" (cg e1) (cg e2))]
    
    [(ml-list-equal t e1 e2) (format "~a = ~a" (cg e1) (cg e2))]
    
    [(ml-var _ n) (format "~a" n)]
    
    ;[(ml-if _ c e1 e2) (format "if (~a) {~n  ~a;~n} else {~n  ~a;~n}~n" (cg c) (cg e1) (cg e2))]    
    ;[(cons (? symbol? e) (? procedure? p)) (format "~a ~a" (cg/type p) e)]
    ;[(or (? number? e) (? symbol? e)) (format "~a" e)]
    ;[(? procedure? p) (second (regexp-match #rx"procedure:(.*)>" (format "~a" p)))]       
    ))

(require "tests.rkt")

; ideally this would be the API we expose to users
;(lift 'select-*-benchmark inv-search-space pc-search-space cg)

(define ast (ml-lookup 'select-*-test))

(define-values (checked _) (typecheck ast))

(construct-cfg checked)

(live-vars checked)

(define vc (compute-vc checked))

(define udos-appended (append-udos vc))

(define space-defined (define-space ast udos-appended inv-search-space pc-search-space))

(define sk (to-sk space-defined))
(with-output-to-file "test.sk" #:exists 'replace (lambda () (printf sk)))

(define choose-resolved (resolve-choose space-defined))

(define z3 (to-z3 choose-resolved "../../z3/mllist.z3"))
(with-output-to-file "test.z3" #:exists 'replace (lambda () (printf z3)))

(define final (codegen cg choose-resolved))