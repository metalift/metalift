#lang racket

; IR used to represent the input program and VCs

; types
(struct ml-listof (type) #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "(listof ~a)" (ml-listof-type self)))]
)

;(struct expr ([type #:auto]) #:auto-value void? #:mutable #:transparent)
(struct expr (type) #:mutable #:transparent)

; return value of fn, for users to construct their search space functions
; fn is the ml-decl of the function 
;(struct ml-ret-val expr (fn) #:transparent)
(define (ml-ret-val fn)
  (ml-var (ml-decl-ret-type fn) (string->symbol (format "~a-ret-val" (ml-decl-name fn)))))

(struct ml-var expr (name) #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "(~a:~a)" (ml-var-name self) (expr-type self)))]
)
(struct ml-lit expr (val) #:transparent)

(struct ml-define expr (v e) #:transparent)
(struct ml-if expr (cond e1 e2) #:transparent)
(struct ml-for expr (test body) #:transparent)
(struct ml-block expr (body) #:transparent) ; a code block
(struct ml-set! expr (v e) #:transparent)

; binary operators
(struct ml-< expr (e1 e2) #:transparent)
(struct ml-<= expr (e1 e2) #:transparent)
(struct ml-> expr (e1 e2) #:transparent)
(struct ml->= expr (e1 e2) #:transparent)
(struct ml-eq expr (e1 e2) #:transparent)

(struct ml-and expr (exprs) #:transparent)
(struct ml-or expr (e1 e2) #:transparent)

(struct ml-+ expr (e1 e2) #:transparent)
(struct ml-- expr (e1 e2) #:transparent)
(struct ml-* expr (e1 e2) #:transparent)
(struct ml-/ expr (e1 e2) #:transparent)

; unary operators
(struct ml-not expr (e) #:transparent)

; function calls
(struct ml-call expr (name args) #:transparent
;  #:methods gen:custom-write
;  [(define (write-proc self port mode)
;     (fprintf port "(ml-call ~a ~a)" (ml-call-name self) (ml-call-args self)))]
  )

; list operations
(struct ml-list expr (es) #:transparent)
(struct ml-list-append expr (l e) #:transparent)
(struct ml-list-equal expr (l1 l2) #:transparent)
(struct ml-list-length expr (l) #:transparent)
(struct ml-list-prepend expr (e l) #:transparent)
(struct ml-list-ref expr (l e) #:transparent)
(struct ml-list-tail expr (l e) #:transparent)
(struct ml-list-take expr (l e) #:transparent)

; each formal is a pair: (name type)
(struct ml-decl (name formals body ret-type) #:transparent)

; additional expressions for VCs, not to be used for input programs
(struct ml-implies expr (e1 e2) #:transparent)
(struct ml-synth expr (out-vars in-vars) #:transparent)
(struct ml-choose expr (exprs) #:transparent)
(struct ml-assert expr (e) #:transparent)

(struct ml-prog (decls asserts)
  #:methods gen:custom-write
  [(define (write-proc self port mode)     
     (fprintf port "decls:~n~a~nasserts:~n~a~n"              
              (ml-prog-decls self) (ml-prog-asserts self)))])

; shortcut to save passing variables
;(define (make-ml-prog wp decls asserts p)
;  (ml-prog (ml-prog-out-vars p) (ml-prog-in-vars p) wp decls asserts))


;(define-syntax-rule (mk es ...) (for ([e (list es ...)]) (printf "~a~n" e)))

; macros to make it easier to define UDOs

(define-syntax-rule (mk-and es ...) (ml-and boolean? (list es ...)))
(define-syntax-rule (mk->= e1 e2) (ml->= boolean? e1 e2))
(define-syntax-rule (mk-<= e1 e2) (ml-<= boolean? e1 e2))
(define-syntax-rule (list-equal l1 l2) (ml-list-equal boolean? l1 l2))
(define-syntax-rule (list-take l n) (ml-list-take (ml-listof integer?) l n))
(define-syntax-rule (list-length l) (ml-list-length integer? l))
(define-syntax-rule (call fn args ...) (ml-call (ml-listof integer?) fn (list args ...)))
(define-syntax-rule (mk-int n) (ml-lit integer? n))
(define-syntax-rule (choose es ...) (ml-choose boolean? (list es ...)))


(provide
 (except-out (all-defined-out) expr expr-type)
 (rename-out [expr ml-expr]
             [expr-type ml-expr-type]))
 ;(all-defined-out))
;(except-out (all-defined-out) expr))