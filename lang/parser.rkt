#lang racket

; translates ML concrete syntax to IR

(require syntax/parse
         "../lib/util.rkt"
         "ir.rkt")

(define debug #f)

(define (debug-parser (v boolean?))
  (set! debug v))

(define (to-ml/fn name fs ts body)
  (letrec ([formals (syntax->datum fs)]
           [translated-body (ml-block void? (map to-ml (syntax->list body)))]
           [type (to-ml ts)]
           [formal-types (ml-fn-type-formals type)]
           [ret-type (ml-fn-type-ret-type type)]
           [rv-name (syntax->datum (ret-var ts))]
           [rv (if (eq? rv-name null) null (ml-var ret-type rv-name))]
           [decl (ml-decl type (syntax->datum name)
                          (map (lambda (name type) (ml-var type name)) formals formal-types)
                          rv translated-body)])
    (cond [debug (printf "~n**** Translation to ML ****~n~a~n~n" decl)])
    decl))

(define (to-ml/axiom fs ts body)
  (letrec ([formals (syntax->datum fs)]
           [translated-body (ml-block void? (map to-ml (syntax->list body)))]
           [formal-types (for/list ([t (syntax->list ts)]) (to-ml t))])

    (ml-axiom (map (lambda (name type) (ml-var type name)) formals formal-types) translated-body)))

; convert the input ML language into the ML IR represented using structs
(define (to-ml stx)  ;[fns known-fns])
  (syntax-parse stx
    #:datum-literals (require define define-udo define-axiom
                      block if while set!
                      < <= > >= =
                      and or
                      + - * /
                      not
                      bitwise-ior bitwise-and bitwise-not arithmetic-shift 
                      printf
                      cons empty length list list-ref list-set list-tail list-take list-equal ml-append                   
                      -> boolean? listof integer? flonum? uint8_t? uint16_t? uint32_t? int8_t? int16_t? int32_t?)

    ; racket base functions

    
    ; require  XXX need to import   
    [(define-udo (name fs ...) ts body ...)
     (to-ml/fn #'name #'(fs ...) #'ts #'(body ...))]

    [(define-axiom (fs ...) ts body ...)
     (to-ml/axiom #'(fs ...) #'ts #'(body ...))]
    
    [(define (name fs ...) ts body ...)
     ;(letrec ([formals (map to-ml (syntax->list #'(fs ...)))]
     ;         [types (to-ml #'ts)]
     ;         [formal-types (drop-right types 1)]
     ;         [ret-type (last types)])                             
     ;(ml-decl (to-ml #'name) (zip formals formal-types) (map to-ml (syntax->list #'(body ...)))
     ;         ret-type))]
     (to-ml/fn #'name #'(fs ...) #'ts #'(body ...))]
    
    [(define n t v) (ml-define (to-ml #'t) (to-ml #'n) (to-ml #'v))]

    ; statements
    [(block stmt ...) (ml-block void? (map to-ml (syntax->list #'(stmt ...))))]
    [(if c e1 e2) (ml-if void? (to-ml #'c) (to-ml #'e1) (to-ml #'e2))]
    [(while test body ...) (ml-while void? (to-ml #'test)
                                    (ml-block void? (map to-ml (syntax->list #'(body ...)))))]
    [(set! v e) (ml-set! void? (to-ml #'v) (to-ml #'e))]

    ; binary operators
    [(< e1 e2) (ml-< void? (to-ml #'e1) (to-ml #'e2))]
    [(<= e1 e2) (ml-<= void? (to-ml #'e1) (to-ml #'e2))]
    [(> e1 e2) (ml-> void? (to-ml #'e1) (to-ml #'e2))]
    [(>= e1 e2) (ml->= void? (to-ml #'e1) (to-ml #'e2))]
    [(= e1 e2) (ml-eq void? (to-ml #'e1) (to-ml #'e2))]
    
    [(and es ...) (ml-and void? (for/list ([e (syntax->list #'(es ...))]) (to-ml e)))]
    [(or es ...) (ml-or void? (for/list ([e (syntax->list #'(es ...))]) (to-ml e)))]    

    [(+ e1 e2) (ml-+ integer? (to-ml #'e1) (to-ml #'e2))]
    [(- e1 e2) (ml-- integer? (to-ml #'e1) (to-ml #'e2))]
    [(* e1 e2) (ml-* integer? (to-ml #'e1) (to-ml #'e2))]
    [(/ e1 e2) (ml-/ integer? (to-ml #'e1) (to-ml #'e2))]
    
    ; unary operators
    [(not e)  (ml-not boolean? (to-ml #'e))]

    ; bitwise operators
    [(bitwise-ior e1 e2) (bitwise-or (to-ml #'e1) (to-ml #'e2))]
    [(bitwise-and e1 e2) (bitwise-and (to-ml #'e1) (to-ml #'e2))]
    [(bitwise-not e) (bitwise-not (to-ml #'e))]
    [(arithmetic-shift e1 e2) (bitwise-shift (to-ml #'e1) (to-ml #'e2))]

    ; list operations 
    [(cons e l) (ml-list-prepend (ml-listof void?) (to-ml #'e) (to-ml #'l))]
    [(empty t) (ml-list (ml-listof (to-ml #'t)) empty)]
    [(length e) (ml-list-length integer? (to-ml #'e))]
    [(list es ...) (ml-list (ml-listof void?)
                            (for/list ([e (syntax->list #'(es ...))]) (to-ml e)))]
    [(list-ref l e) (ml-list-ref void? (to-ml #'l) (to-ml #'e))]
    [(list-set l i e) (ml-list-set void? (to-ml #'l) (to-ml #'i) (to-ml #'e))]
    [(list-tail l e) (ml-list-tail (ml-listof void?) (to-ml #'l) (to-ml #'e))]
    [(list-take l e) (ml-list-take void? (to-ml #'l) (to-ml #'e))]
    [(list-equal l1 l2) (ml-list-equal boolean? (to-ml #'l1) (to-ml #'l2))]
    [(ml-append l e) (ml-list-append (ml-listof void?) (to-ml #'l) (to-ml #'e))]
            
    ; type declarations
    ;[(-> ts ...) (map to-ml (syntax->list #'(ts ...)))]
    [(-> ts ...)
     (let ([types (for/list ([t (syntax->list #'(ts ...))]) (to-ml t))])
       ; check that the types are indeed types
       (for ([t types]) (cond [(not (is-type? t)) (error (format "~a is not a type in ~a~n" t stx))]))
       (ml-fn-type (drop-right types 1) (last types)))]

    [(listof t) (ml-listof (to-ml #'t))]
    [(name:id t:expr) (to-ml #'t)] ; drop the name
    
    [boolean? boolean?]
    [flonum? flonum?]
    [integer? integer?]
    [int8_t? int8_t?]
    [int16_t? int16_t?]
    [int32_t? int32_t?]
    [uint8_t? uint8_t?]
    [uint16_t? uint16_t?]
    [uint32_t? uint32_t?]
    
    ; bare vars are translated to void? types
    [e #:when (ml-var? #'e) #'e]
    [e #:when (identifier? #'e) (ml-var void? (syntax->datum #'e))]
    
    ; literals
    [e #:when (exact-integer? (syntax->datum #'e)) (ml-lit integer? (syntax->datum #'e))]
    [e #:when (flonum? (syntax->datum #'e)) (ml-lit flonum? (syntax->datum #'e))]
    [e #:when (boolean? (syntax->datum #'e)) (ml-lit boolean? (syntax->datum #'e))]
    ;[e #:when (or (number? (syntax->datum #'e)) (identifier? #'e) (boolean? (syntax->datum #'e)))
    ;  (syntax->datum #'e)]
    
    ; parsed as function call last, after everything more specific has been matched
    [(name args ...) ;#:when (set-member? known-fns (syntax->datum #'name))
                     (ml-call boolean? (syntax->datum #'name) (map to-ml (syntax->list #'(args ...))))]
    
    [e (error (format "to-ml NYI: ~a" #'e))]

    ))

(provide to-ml debug-parser)