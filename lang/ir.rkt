#lang racket

; IR used to represent the input program and VCs

; types
(struct ml-listof (type) #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "(listof ~a)" (ml-listof-type self)))]
)

(struct ml-fn-type (formals ret-type) #:transparent)

; singletons for the int types
(define int8_t? (let () (struct int8_t () #:transparent) (int8_t)))
(define int16_t? (let () (struct int16_t () #:transparent) (int16_t)))
(define int32_t? (let () (struct int32_t () #:transparent) (int32_t)))
(define uint8_t? (let () (struct uint8_t () #:transparent) (uint8_t)))
(define uint16_t? (let () (struct uint16_t () #:transparent) (uint16_t)))
(define uint32_t? (let () (struct uint32_t () #:transparent) (uint32_t)))

;(struct expr ([type #:auto]) #:auto-value void? #:mutable #:transparent)
(struct expr (type) #:mutable #:transparent)

; return value of fn, for users to construct their search space functions
; fn is the ml-decl of the function 
;(define (ml-ret-val fn)
;  (ml-var (ml-decl-ret-type fn) (string->symbol (format "~a-ret-val" (ml-decl-name fn)))))

(struct ml-var expr (name) #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "(~a:~a)" (ml-var-name self) (expr-type self)))]
)
(struct ml-lit expr (val) #:transparent)

(struct ml-define expr (v e) #:transparent)
(struct ml-if expr (cond e1 e2) #:transparent)
(struct ml-while expr (test body) #:transparent)
(struct ml-block expr (body) #:transparent) ; a code block
(struct ml-set! expr (v e) #:transparent)

; binary operators
(struct ml-< expr (e1 e2) #:transparent)
(struct ml-<= expr (e1 e2) #:transparent)
(struct ml-> expr (e1 e2) #:transparent)
(struct ml->= expr (e1 e2) #:transparent)
(struct ml-eq expr (e1 e2) #:transparent)

(struct ml-and expr (exprs) #:transparent)
(struct ml-or expr (exprs) #:transparent)

(struct ml-+ expr (e1 e2) #:transparent)
(struct ml-- expr (e1 e2) #:transparent)
(struct ml-* expr (e1 e2) #:transparent)
(struct ml-/ expr (e1 e2) #:transparent)

; unary operators
(struct ml-not expr (e) #:transparent)

; bitwise operators
(struct ml-bitop expr (name exprs) #:transparent)
(define-syntax-rule (bitwise-or e1 e2) (ml-bitop integer? 'ior (list e1 e2)))
(define-syntax-rule (bitwise-and e1 e2) (ml-bitop integer? 'and (list e1 e2)))
(define-syntax-rule (bitwise-not e) (ml-bitop integer? 'not (list e)))
(define-syntax-rule (lshl e1 e2) (ml-bitop integer? 'lshl (list e1 e2)))
(define-syntax-rule (lshr e1 e2) (ml-bitop integer? 'lshr (list e1 e2)))


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
(struct ml-list-set expr (l index e) #:transparent)
(struct ml-list-tail expr (l e) #:transparent)
(struct ml-list-take expr (l e) #:transparent)

; each formal is a ml-var
(struct ml-decl expr (name formals ret-var body) #:transparent)
; convenience function to get the return type of a function
(define (ml-decl-ret-type decl)
  (ml-fn-type-ret-type (expr-type decl)))
        
(struct ml-axiom (formals body) #:transparent)

; additional expressions for VCs, not to be used for input programs
(struct ml-implies expr (e1 e2) #:transparent)
(struct ml-synth expr (out-vars in-vars) #:transparent)
(struct ml-choose expr (exprs) #:transparent)
(struct ml-assert expr (e) #:transparent)

(struct ml-prog (decls asserts axioms)
  #:methods gen:custom-write
  [(define (write-proc self port mode)     
     (fprintf port "decls:~n~a~nasserts:~n~a~naxioms:~n~a~n"              
              (ml-prog-decls self) (ml-prog-asserts self) (ml-prog-axioms self)))])

; shortcut to save passing variables
;(define (make-ml-prog wp decls asserts p)
;  (ml-prog (ml-prog-out-vars p) (ml-prog-in-vars p) wp decls asserts))


(provide
 (except-out (all-defined-out) expr expr-type)
 (rename-out [expr ml-expr]
             [expr-type ml-expr-type]))
 
;(except-out (all-defined-out) expr))