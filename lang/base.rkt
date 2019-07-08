#lang racket

; ML frontend language used to express input programs and user defined operators
; programs written in this language are executed as normal racket code

(require (for-syntax syntax/parse))
(require "../lib/util.rkt")

; ML specific forms

; another form of "for" with initialization
;(define-syntax-rule (ml-for init test incr body ...)
;  (run-ml-for (lambda () init) (lambda () test) (lambda () incr) (lambda () body ...)))
;
;(define (run-ml-for init test incr body)
;  (init)
;  (for ([i (in-naturals)])
;    #:break (not (test))
;    (body)
;    (incr)))

(define-syntax-rule (ml-for test body ...)
  (run-ml-for (lambda () test) (lambda () body ...)))

(define (run-ml-for test body)
  (for ([i (in-naturals)])
    #:break (not (test))
    (body)))


; ML specific list functions
; append an element to the end of list
(define (ml-append l e)
  (append l (list e)))


; stores all fns that have been defined for compute-vc
(define fns (make-hash))

(define (ml-lookup fn)
  (hash-ref fns fn))

; define the function and also store its def in the fns hash
(define-syntax (ml-define stx)
  (syntax-parse stx 
    [(ml-define (name formals ...) type body ...)
     #'(begin
         ;(hash-set! fns (syntax->datum #'name)
         ;           (cons (parse-types (syntax->datum #'(formals ...)) (syntax->datum #'type))
         ;                 (list #'body ...)))
         ;(printf "setting to ~a~n" (to-ml #'(ml-define (name formals ...) type body ...)))
         (hash-set! fns (syntax->datum #'name) (to-ml #'(ml-define (name formals ...) type body ...)))
         (define (name formals ...) body ...))]
         
    [(ml-define name:id type:expr e:expr) #'(define name e)]))


; store user defined operators (udos)
; XXX determine whether this needs to be a hash or just a list
(define udos (make-hash))

(define (ml-udos)
  (hash-values udos))

(define-syntax (define-udo stx)
  (syntax-parse stx 
    [(ml-define (name formals ...) type body ...)
     #'(begin
         (hash-set! udos (syntax->datum #'name) (to-ml #'(ml-define (name formals ...) type body ...)))
         (define (name formals ...) body ...))]
         
    [(ml-define name:id type:expr e:expr) #'(define name e)]))


; list of functions supported by metalift
(provide

 ml-lookup
 ml-udos

 ; racket base functions
 syntax
 require
 provide
 (rename-out [ml-define define])
 define-udo

 ; statements
 if
 ml-for         
 ;ml-lookup
 set!

 ; binary operators
 < <= > >= =
 and or
 + - * /
 true false

 ; unary operators
 not
 
 ; racket functions
 printf

 ; list operations 
 cons
 empty
 length
 list
 list-ref
 list-tail
 ml-append 

 ; type declarations
 ->
 integer?
 boolean?
 listof
 )