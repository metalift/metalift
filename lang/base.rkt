#lang racket

; ML frontend language used to express input programs and user defined operators
; programs written in this language are executed as normal racket code

(require (for-syntax syntax/parse (only-in "../lib/util.rkt" ret-var))
         "parser.rkt")

; ML specific forms

; another form of "while" with initialization
;(define-syntax-rule (while init test incr body ...)
;  (run-ml-while (lambda () init) (lambda () test) (lambda () incr) (lambda () body ...)))
;
;(define (run-ml-while init test incr body)
;  (init)
;  (for ([i (in-naturals)])
;    #:break (not (test))
;    (body)
;    (incr)))

(define-syntax-rule (while test body ...)
  (run-ml-while (lambda () test) (lambda () body ...)))

(define (run-ml-while test body)
  (for ([i (in-naturals)])
    #:break (not (test))
    (body)))

; ML specific list functions
; append an element to the end of list
(define (ml-append l e)
  (append l (list e)))

; remove type definition
(define (ml-list-empty t)
  empty)

; stores all fns that have been defined for compute-vc
; maps function name (a datum) to ML ast representing that function
(define fns (make-hash))

(define (ml-lookup-by-name name)
  (hash-ref fns name))

(define (ml-lookup-by-fn fn)
  (let ([name (string->symbol (second (regexp-match #rx"procedure:(.*)>" (format "~a" fn))))])
  (ml-lookup-by-name name)))

; define the function and also store its def in the fns hash
(define-syntax (ml-define stx)
  (syntax-parse stx 
    [(ml-define (name formals ...) type body ...)
     (define rv (ret-var #'type))
     (define translated (if (eq? rv null)
                            #'(define (name formals ...) body ...)
                            #`(define (name formals ...) (begin (define #,rv 0) body ... #,rv))))        
     #`(begin
         (hash-set! fns (syntax->datum #'name) (to-ml #'(ml-define (name formals ...) type body ...)))         
         #,translated)]
         
    [(ml-define name:id type:expr e:expr) #'(define name e)]))


; store user defined operators (udos)
(define udos (make-hash))

(define (ml-udos)
  (hash-values udos))

(define (ml-lookup-udo-by-name name)
  (hash-ref udos name))

(define (ml-lookup-udo-by-fn fn)
  (let ([name (string->symbol (second (regexp-match #rx"procedure:(.*)>" (format "~a" fn))))])
    (ml-lookup-udo-by-name name)))


(define axioms (list))
(define (add-axiom ax)
  (set! axioms (cons ax axioms)))

(define (ml-axioms) axioms)

(define-syntax (define-udo stx)
  (syntax-parse stx 
    [(ml-define (name formals ...) type body ...)
     #'(begin
         (hash-set! udos (syntax->datum #'name) (to-ml #'(ml-define (name formals ...) type body ...)))
         (define (name formals ...) body ...))]
         
    [(ml-define name:id type:expr e:expr) #'(define name e)]))


(define-syntax (define-axiom stx)
  (syntax-parse stx
    [(_ (fs ...) ts body ...)
     #'(add-axiom (to-ml #'(define-axiom (fs ...) ts body ...)))]))


; list of functions supported by metalift
(provide

 ml-lookup-by-name
 ml-lookup-by-fn
 ml-lookup-udo-by-name
 ml-lookup-udo-by-fn
 ml-udos
 ml-axioms

 ; racket base functions
 syntax
 require
 provide
 (rename-out [ml-define define])
 define-udo
 define-axiom

 ; statements
 if
 while         
 set!

 ; binary operators
 < <= > >= =
 and or
 + - * /
 true false

 ; unary operators
 not

 ; bitwise operators 
 bitwise-ior
 bitwise-and
 bitwise-not
 arithmetic-shift ; both left and right shifts
 
 ; racket functions
 printf
 for/list

 ; list operations 
 cons
 length
 list
 list-ref
 list-set
 list-tail
 ml-append
 (rename-out [ml-list-empty empty])

 ; type declarations
 ->
 integer?
 boolean?
 listof
 )