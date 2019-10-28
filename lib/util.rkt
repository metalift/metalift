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
    [(ml-or _ es) (for/fold ([vs (set)]) ([e es]) (set-union vs (used-vars e)))]

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
    [(ml-list-set _ l i e) (set-union (used-vars l) (used-vars i) (used-vars e))]
    [(ml-list-prepend _ e l) (set-union (used-vars e) (used-vars l))]
    [(ml-list-take _ l e) (set-union (used-vars l) (used-vars e))]
    [(ml-list-tail _ l e) (set-union (used-vars l) (used-vars e))]
      
    [(ml-var _ v) (set code)]
    [(ml-lit _ v) (set)]

    [(ml-assert _ e) (used-vars e)]
    [(ml-call _ n args) (for/fold ([vs (set)]) ([a args]) (set-union vs (used-vars a)))]
    [(ml-implies _ e1 e2) (set-union (used-vars e1) (used-vars e2))]
      
    [e (error (format "used-vars NYI: ~a" e))]))

(define (ret-var type)
  (syntax-parse type
    [(-> ts ...)
     (define ret-type (last (syntax->list #'(ts ...))))
     (syntax-parse ret-type
       [(name t) #'name]
       [_ null])] ; no return value
    [e (error (format "not a type: ~a" (syntax->datum #'e)))]))  


(provide parse-types
         eval-type
         used-vars
         ret-var
         and-&& or-|| or-||/list)