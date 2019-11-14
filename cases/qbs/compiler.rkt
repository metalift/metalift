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

(define (pred v)
  (= v 42))

(define (inv-search-space fn vars vartypes)

  (define in (hash-ref vars 'in)) 
  (define i (hash-ref vars 'i))
  (define out (ml-decl-ret-var fn))
  
  ;(mk-and (list-equal out (call my-select-* (list-take in i) pred))
  (mk-and (list-equal out (call my-select-* (list-take in i)))
          (mk-<= i (list-length in))
          (mk->= i (ml-lit integer? 0))
          )

  (define-values (ast _) (typecheck (to-ml #'(and (list-equal out (my-select-* (list-take in i)))
                           (<= i (length in))
                           (>= i 0))) vartypes))

  ast
  )


; fn is a ml-decl
(define (pc-search-space fn vars vartypes)
  
  (define in (hash-ref vars 'in))
  (define out (ml-decl-ret-var fn))

  ; choose(pc1, pc2, pc3, ...)
  (choose boolean? (list-equal out (call my-select-* in)) ; out = my-select-*(in)
                   (list-equal out in))  ; out = in
    
  ;(choose boolean? (list-equal out (call my-select-* in pred)) ; out = my-select-*(in)
  ;                 (list-equal out in))  ; out = in  
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


; *** compiler main code below ***


; ideally this would be the API we expose to users
;(lift 'select-*-benchmark inv-search-space pc-search-space cg)

(define (qbs filename fname)

  (define fns (parse filename))
 
  (define ast (hash-ref fns fname))

  (define-values (checked _) (typecheck ast))

  (construct-cfg checked)

  (live-vars checked)

  (define vc (compute-vc checked))

  (define udos-appended (append-udos vc))

  (define space-defined (define-space ast udos-appended inv-search-space pc-search-space))

  ; run sketch with --fe-custom-codegen "path to parseSketchOutput.jar" --bnd-inbits 2 
  (define sk (to-sk space-defined))
  (with-output-to-file "test-sketch.sk" #:exists 'replace (lambda () (printf sk)))
  
  (define choose-resolved (resolve-choose space-defined))
  
  ;(define z3 (to-z3 choose-resolved "../../z3/mllist.z3"))
  ;(with-output-to-file "test.z3" #:exists 'replace (lambda () (printf z3)))
  ;
  ;(define final (codegen cg choose-resolved))

  (void)  
)

; example run
;(qbs "tests.rkt" 'select-*-test)