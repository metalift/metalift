#lang racket

(require "ir.rkt"
         (only-in "base.rkt" ml-lookup-udo-by-fn))

; macros to make it easier to define UDOs

;(define-syntax-rule (mk es ...) (for ([e (list es ...)]) (printf "~a~n" e)))

(define-syntax-rule (mk-block es ...) (ml-block void? (list es ...)))
(define-syntax-rule (mk-while test body) (ml-while void? test body))
(define-syntax-rule (mk-set! v e) (ml-set! void? v e))
(define-syntax-rule (mk-and es ...) (ml-and boolean? (list es ...)))
(define-syntax-rule (mk-= e1 e2) (ml-eq boolean? e1 e2))
(define-syntax-rule (mk-< e1 e2) (ml-< boolean? e1 e2))
(define-syntax-rule (mk->= e1 e2) (ml->= boolean? e1 e2))
(define-syntax-rule (mk-<= e1 e2) (ml-<= boolean? e1 e2))
(define-syntax-rule (mk-list-ref l i) (ml-list-ref void? l i))
(define-syntax-rule (list-equal l1 l2) (ml-list-equal boolean? l1 l2))
(define-syntax-rule (list-take l n) (ml-list-take (ml-listof-type (ml-expr-type l)) l n))
(define-syntax-rule (list-length l) (ml-list-length integer? l))

(define-syntax-rule (call fn args ...)
  (let ([ret-type (ml-decl-ret-type (ml-lookup-udo-by-fn fn))])
    (ml-call ret-type fn (list args ...))))
  
(define-syntax-rule (mk-int n) (ml-lit integer? n))
(define-syntax-rule (choose t es ...) (ml-choose t (list es ...)))

(provide (all-defined-out))