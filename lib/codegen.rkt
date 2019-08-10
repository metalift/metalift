#lang racket

(require "../lang/ir.rkt")

(define (codegen cg-fn prog)  
  (for/list ([d (ml-prog-decls prog)]
             #:when (equal? (ml-decl-name d) "pc"))
    (printf "**** Start codegen on ~a ~n" (ml-decl-body d))
    (cg-fn (ml-decl-body d))))

(provide codegen)