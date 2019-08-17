#lang racket

; various util functions including conversion from frontend language to
; ML IR

(require syntax/parse
         "../lang/ir.rkt")

(define (parse-types formals types)
  (let* ([types-list types] ;(contract-name types)]
         [ret-type (eval-type (last types-list))]
         ; types-list has the form (-> t1 t2 ... ret-type)
         [formal-types (drop (take types-list (- (length types-list) 1)) 1)]
         [r (for/list ([f formals] [t formal-types]) (cons f (eval-type t)))])
    ;(printf "parsed: ~a~n" (append r (list ret-type)))
    (append r (list ret-type))))

; convert a type datum into type function 
(define (eval-type t)
  ;(parameterize ([current-namespace (make-base-namespace)])
  ;  (namespace-require 'racket)
  ;  (eval t)))
  t)

(define-syntax and-&&
  (syntax-rules ()
    [(_) #t]
    [(_ (list v0 v ...)) (let ([t0 v0]) (and (and-&& v ...) t0))]
    [(_ v0) v0]
    [(_ v0 v ...) (let ([t0 v0]) (and (and-&& v ...) t0))]))
    ;[(_ v0 #:rest (r ...)) (let ([t0 v0]) (and t0 (@&& r ... t0)))]
    ;[(_ v0 v ... #:rest (r ...)) (let ([t0 v0]) (and t0 (and-&& v ... #:rest (r ... t0))))]
    ;[(_ v0 v ...) (let ([t0 v0]) (and t0 (and-&& v ... #:rest (t0))))]))

;(define-syntax or-||
;  (syntax-rules ()
;    [(_) #t]
;    [(_ (list v0 v ...)) (let ([t0 v0]) (or (or-|| v ...) t0))]
;    [(_ v0) v0]
;    [(_ v0 v ...) (let ([t0 v0]) (or (or-|| v ...) t0))]
;    ))


;(or-|| (for/list ([e '(#t #t)]) e))
;(or-|| #t (f) (f) )

(define (or-|| . vs)
  (or-||/list vs))

(define (or-||/list l)
  (for/fold ([r #f]) ([e l]) (or r e)))

;(or-||/list (list #t (f) (f) ))

;(define known-fns (mutable-set))

;(define known-fns (mutable-set 'my-select-* 'my-select 'my-sum))
;(define (add-known-fns name)
;  (set-add! known-fns name))


(define (zip . lists) (apply map cons lists))

; zip multiple lists together
; (define (zip . lists) (apply map list lists))

; return the set of ml-vars that are used in code
(define (used-vars code)
  (match code

    [(ml-if _ c e1 e2) (set-union (used-vars c) (used-vars e1) (used-vars e2))]
    
    [(ml-< _ e1 e2) (set-union (used-vars e1) (used-vars e2))]
    [(ml-<= _ e1 e2) (set-union (used-vars e1) (used-vars e2))]
    [(ml-> _ e1 e2) (set-union (used-vars e1) (used-vars e2))]
    [(ml->= _ e1 e2) (set-union (used-vars e1) (used-vars e2))]
    [(ml-eq _ e1 e2) (set-union (used-vars e1) (used-vars e2))]
      
    [(ml-and _ es) (for/fold ([vs (set)]) ([e es]) (set-union vs (used-vars e)))]
    [(ml-or _ e1 e2) (set-union (used-vars e1) (used-vars e2))]

    [(ml-+ _ e1 e2) (set-union (used-vars e1) (used-vars e2))]
    [(ml-- _ e1 e2) (set-union (used-vars e1) (used-vars e2))]
    [(ml-* _ e1 e2) (set-union (used-vars e1) (used-vars e2))]
    [(ml-/ _ e1 e2) (set-union (used-vars e1) (used-vars e2))]
    [(ml-not _ e) (used-vars e)]

    [(ml-list _ es)
     (let ([r (for/list ([e es]) (used-vars e))])
       (if (empty? r) (set) (apply set-union r)))]
    [(ml-list-append _ l e) (set-union (used-vars l) (used-vars e))]
    [(ml-list-length _ l) (used-vars l)]
    [(ml-list-equal _ l1 l2) (set-union (used-vars l1) (used-vars l2))]
    [(ml-list-ref _ l e) (set-union (used-vars l) (used-vars e))]
    [(ml-list-prepend _ e l) (set-union (used-vars e) (used-vars l))]
    [(ml-list-take _ l e) (set-union (used-vars l) (used-vars e))]
    [(ml-list-tail _ l e) (set-union (used-vars l) (used-vars e))]
      
    [(ml-var _ v) (set code)]
    [(ml-lit _ v) (set)]

    [(ml-assert _ e) (used-vars e)]
    [(ml-call _ n args) (for/fold ([vs (set)]) ([a args]) (set-union vs (used-vars a)))]
    [(ml-implies _ e1 e2) (set-union (used-vars e1) (used-vars e2))]
      
    [e (error (format "used-vars NYI: ~a" e))]))


(define (to-ml/fn name fs ts body)
  (letrec ([formals (syntax->datum fs)]
           [translated-body (ml-block void? (map to-ml (syntax->list body)))]
           [type (to-ml ts)]
           [formal-types (ml-fn-type-formals type)]
           [ret-type (ml-fn-type-ret-type type)])                             
    (printf "~n**** Translation to ML ****~n~a~n~n" (ml-decl (syntax->datum name) (map (lambda (name type) (ml-var type name)) formals formal-types) translated-body
                                                             ret-type))

    (ml-decl type (syntax->datum name) (map (lambda (name type) (ml-var type name)) formals formal-types) translated-body)))

(define (to-ml/axiom fs ts body)
  (letrec ([formals (syntax->datum fs)]
           [translated-body (ml-block void? (map to-ml (syntax->list body)))]
           [formal-types (for/list ([t (syntax->list ts)]) (to-ml t))])

    (ml-axiom (map (lambda (name type) (ml-var type name)) formals formal-types) translated-body)))


; convert the input ML language into the ML IR represented using structs
(define (to-ml stx)  ;[fns known-fns])
  ;(printf "converting ~a~n" (syntax->datum stx))
  
  (syntax-parse stx
    #:datum-literals (require define define-udo define-axiom
                      if ml-for set!
                      < <= > >= =
                      and or
                      + - * /
                      not
                      printf
                      cons empty length list list-ref list-tail list-equal ml-append                   
                      -> integer? boolean? listof)

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
    [(if c e1 e2) (ml-if void? (to-ml #'c) (to-ml #'e1) (to-ml #'e2))]
    [(ml-for test body ...) (ml-for void? (to-ml #'test)
                                    (ml-block void? (map to-ml (syntax->list #'(body ...)))))]
    [(set! v e) (ml-set! void? (to-ml #'v) (to-ml #'e))]

    ; binary operators
    [(< e1 e2) (ml-< void? (to-ml #'e1) (to-ml #'e2))]
    [(<= e1 e2) (ml-<= void? (to-ml #'e1) (to-ml #'e2))]
    [(> e1 e2) (ml-> void? (to-ml #'e1) (to-ml #'e2))]
    [(>= e1 e2) (ml->= void? (to-ml #'e1) (to-ml #'e2))]
    [(= e1 e2) (ml-eq void? (to-ml #'e1) (to-ml #'e2))]
    [(and e1 e2) (ml-and void? (to-ml #'e1) (to-ml #'e2))]
    [(or e1 e2) (ml-or void? (to-ml #'e1) (to-ml #'e2))]
    [(+ e1 e2) (ml-+ integer? (to-ml #'e1) (to-ml #'e2))]
    [(- e1 e2)  (ml-- integer? (to-ml #'e1) (to-ml #'e2))]
    [(* e1 e2) (ml-* integer? (to-ml #'e1) (to-ml #'e2))]
    [(/ e1 e2) (ml-/ integer? (to-ml #'e1) (to-ml #'e2))]
    
    ; unary operators
    [(not e)  (ml-not boolean? (to-ml #'e))]

    ; list operations 
    [(cons e l) (ml-list-prepend (ml-listof integer?) (to-ml #'e) (to-ml #'l))]
    [(empty t) (ml-list (ml-listof (to-ml #'t)) empty)]
    [(length e) (ml-list-length integer? (to-ml #'e))]
    [(list es ...) (ml-list (ml-listof integer?)
                            (for/list ([e (syntax->list #'(es ...))]) (to-ml e)))]
    [(list-ref l e) (ml-list-ref integer? (to-ml #'l) (to-ml #'e))]
    [(list-tail l e) (ml-list-tail (ml-listof integer?) (to-ml #'l) (to-ml #'e))]
    [(list-equal l1 l2) (ml-list-equal boolean? (to-ml #'l1) (to-ml #'l2))]
    [(ml-append l e) (ml-list-append (ml-listof integer?) (to-ml #'l) (to-ml #'e))]
            
    ; type declarations
    ;[(-> ts ...) (map to-ml (syntax->list #'(ts ...)))]
    [(-> ts ...)
     (let ([types (for/list ([t (syntax->list #'(ts ...))]) (to-ml t))])
       (ml-fn-type (drop-right types 1) (last types)))]

    [(listof t) (ml-listof (to-ml #'t))]
    [boolean? boolean?]
    [integer? integer?]        

    ; bare vars are translated to void? types
    [e #:when (identifier? #'e) (ml-var void? (syntax->datum #'e))]
    
    ; literals
    [e #:when (integer? (syntax->datum #'e)) (ml-lit integer? (syntax->datum #'e))]
    [e #:when (boolean? (syntax->datum #'e)) (ml-lit boolean? (syntax->datum #'e))]
    ;[e #:when (or (number? (syntax->datum #'e)) (identifier? #'e) (boolean? (syntax->datum #'e)))
    ;  (syntax->datum #'e)]

    ; parsed as function call last, after everything more specific has been matched
    [(name args ...) ;#:when (set-member? known-fns (syntax->datum #'name))
                     (ml-call boolean? (syntax->datum #'name) (map to-ml (syntax->list #'(args ...))))]
    
    [e (error (format "to-ml NYI: ~a" #'e))]

    ))

(provide parse-types
         eval-type
         to-ml
         used-vars
         ;add-known-fns
         and-&& or-|| or-||/list)