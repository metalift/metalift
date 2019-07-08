#lang racket

(require "../lang/ir.rkt")

(define (codegen cg-fn prog)  
  (for/list ([d (ml-prog-decls prog)]
             #:when (equal? (ml-decl-name d) "pc"))
    (printf "start codegen on ~a ~n" d)
    (cg-fn d)))

(provide codegen)