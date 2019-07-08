#lang racket

(require (except-in "../lang/ir.rkt" expr))
(require "../lib/util.rkt")
(require "../qbsTest2.rkt")
(require (only-in "../lang/base.rkt" ml-lookup ml-udos))

; implementation of CFG construction, type checker, and live variable analysis

;; CFG 

(define succ (make-hash))
(define pred (make-hash))
(define (succs c) (hash-ref succ c))
(define (preds c) (hash-ref pred c))

; debug print
(define (print-hash h)
  (for ([(k v) h]) (printf "k: ~a~nv: ~a~n~n" k v)))

; return the exit exprs for the given function
(define (exits)
  (for/list ([(k v) succ]
    #:when (null? v))
    k))


; returns the first expression evaluated in an expression
(define (first-e e)
  (match e
    [(list es ...) (first-e (first es))]
    [(ml-if _ c e1 e2) (first-e c)]
    [(ml-for _ test body) (first-e test)]
    [_ e]))

; returns the last evaluated in an expression 
(define (last-e e)
  (match e
    [(list es ...) (last-e (last es))]
    [(ml-if _ c e1 e2)
     (let ([last-e1 (last-e e1)] [last-e2 (last-e e2)])
       (append (if (list? last-e1) last-e1 (list last-e1)) (if (list? last-e2) last-e2 (list last-e2))))]
    [(ml-block _ es) (last-e es)]
    [(ml-for _ test body) (last-e test)]
    [_ e]))

; construct the cfg for code, where p is the predecessor to code and s is its successor
(define (construct-cfg code [p null] [s null])

  ; update pred and succ 
  (define (update code p s)
    (hash-set! pred code (append (hash-ref! pred code null) (flatten (list p))))
    (hash-set! succ code (append (hash-ref! succ code null) (flatten (list s)))))
         
  ;(printf "running on ~a~n" code)
  (match code
    [(ml-decl name formals body rt) (construct-cfg body p s)]
    
    [(list es ...)
     (define l (length es)) 
     (for ([i (range l)] [e es])
       (define curr-p p) (define curr-s s)
       (cond [(and (> l 1) (equal? e (first es))) (set! curr-s (first-e (second es)))] ; first e in list of length > 1
             [(and (> l 1) (equal? e (last es))) (set! curr-p (last-e (list-ref es (- l 2))))] ; last e in list of length > 1
             [(> l 1) (set! curr-p (last-e (list-ref es (- i 1))))
                      (set! curr-s (first-e (list-ref es (+ i 1))))]) ; e in the middle of a list of length > 1
       (construct-cfg e curr-p curr-s))]

    [(ml-block _ body) (construct-cfg body p s)]

    ; cfg for if:
    ; p -> if -> c -> {e1, e2} -> s
    [(ml-if _ c e1 e2)
     (update code p c)       
     (construct-cfg c code (list (first-e e1) (first-e e2)))
     (construct-cfg e1 c s)
     (construct-cfg e2 c s)]

    ; cfg for for:
    ; p -> for -> test -> {body, s} and body -> s
    [(ml-for _ test body)
     (update code p test)
     (construct-cfg test code (list (first-e body) s))
     (construct-cfg body test test)]

    ; cfg for set:
    ; p -> e -> ml-set! -> s
    [(ml-set! _ v e)
     (update code (last-e e) s)
     (construct-cfg e p code)]
         
    [_ (update code p s)]
    
    ))


;; Live variable analysis

; maps expr to list of live vars
(define live-out (make-hash)) ; a mutable hash
(define live-in (make-hash))

(define (lookup-live-in e) (hash-ref live-in e))

(define (live-vars code)

  (printf "run live vars on ~a~n" code)

  (define (vars code)
    (match code
      [(ml-< _ e1 e2) (set-union (vars e1) (vars e2))]
      [(ml-<= _ e1 e2) (set-union (vars e1) (vars e2))]
      [(ml-> _ e1 e2) (set-union (vars e1) (vars e2))]
      [(ml->= _ e1 e2) (set-union (vars e1) (vars e2))]
      [(ml-eq _ e1 e2) (set-union (vars e1) (vars e2))]
      [(ml-and _ e1 e2) (set-union (vars e1) (vars e2))]
      [(ml-or _ e1 e2) (set-union (vars e1) (vars e2))]
      [(ml-+ _ e1 e2) (set-union (vars e1) (vars e2))]
      [(ml-- _ e1 e2) (set-union (vars e1) (vars e2))]
      [(ml-* _ e1 e2) (set-union (vars e1) (vars e2))]
      [(ml-/ _ e1 e2) (set-union (vars e1) (vars e2))]
      [(ml-not _ e) (vars e)]

      [(ml-list _ es)
       (let ([r (for/list ([e es]) (vars e))])
         (if (empty? r) (set) (apply set-union r)))]
      [(ml-list-append _ l e) (set-union (vars l) (vars e))]
      [(ml-list-length _ l) (vars l)]
      [(ml-list-equal _ l1 l2) (set-union (vars l1) (vars l2))]
      [(ml-list-ref _ l e) (set-union (vars l) (vars e))]
      [(ml-list-prepend _ e l) (set-union (vars e) (vars l))]
      [(ml-list-take _ l e) (set-union (vars l) (vars e))]
      [(ml-list-tail _ l e) (set-union (vars l) (vars e))]
      
      [(ml-var _ v) (set code)]
      [(ml-lit _ v) (set)]
      
      [e (error (format "vc NYI: ~a" e))]))


  (define (hash-check-set h k v)
    (if (hash-has-key? h k)
        (if (not (equal? (hash-ref h k) v))
            (begin (hash-set! h k v) #t)
            #f)
        (begin (hash-set! h k v) #t)))
  
  (define (lv code gen kill)
    ; update live-out
    (define out-changed
      (if (member code (exits))
          (hash-check-set live-out code (set))
          (hash-check-set live-out code
                          (apply set-union (for/list ([s (succs code)])
                                             (hash-ref live-in s (set)))))))   
    ; update live-in
    (define in-changed      
      (hash-check-set live-in code
                      (set-union gen (set-subtract (hash-ref live-out code (set)) kill))))
        
    (or out-changed in-changed))

  ; returns whether live-in or live-out is changed
  (match code
    [(ml-decl name formals body rt) (live-vars body)]

    [(list es ...) ;(for ([e (reverse es)]) (live-vars e))]
     (or-||/list (for/list ([e (reverse es)]) (live-vars e)))]

    [(ml-if _ c e1 e2) ;(live-vars e1) (live-vars e2) (lv c (vars c) (set))]
     (or-|| (live-vars e1) (live-vars e2) (lv c (vars c) (set)))]

    [(ml-for _ test body) ;(live-vars body) (lv test (vars test) (set))]
     ; live vars for ml-for is same as those of the test condition
     (printf "succ is ~a~n" (succs code))
     (or-|| (live-vars body) (lv test (vars test) (set)) (lv code (vars test) (set)))]

    [(ml-set! _ v e) (lv code (vars e) (vars v))]

    [(ml-var _ v) (lv code (set code) (set))]

    [(ml-lit _ v) (lv code (set) (set))]

    [(ml-block _ es) (live-vars es)]

    [e (error (format "live-vars NYI: ~a" e))]
    )
  )

;; Typechecker    

(define (typecheck code [ctx null])
  (printf "~n**** Type inference on ~a ctx is ~a****~n" code ctx)
  (match code

    [(ml-lit t v) (values code ctx)]
    
    [(ml-var _ n) (let ([type (hash-ref ctx n)])
                    (values (ml-var type n) (hash-set ctx n type)))]

    ;(struct ml-define expr (v e) #:transparent)
    ;(struct ml-if expr (cond e1 e2) #:transparent)

    [(ml-for _ test body) (letrec-values ([(new-test test-ctx) (typecheck test ctx)]
                                          [(new-body body-ctx) (typecheck body test-ctx)])                            
                            (values (ml-for (expr-type new-body) new-test new-body) body-ctx))]

    [(ml-block _ es)  (let-values ([(new-es new-ctx)
                                    (for/fold ([checked-es null] [ct ctx]) ([e es])
                                      (let-values ([(checked-e new-ctx) (typecheck e ct)])
                                        (values (append checked-es (list checked-e)) new-ctx)))])
                        (values (ml-block (expr-type (last-e new-es)) new-es) new-ctx))]
                                       
    [(ml-set! _ v e) (letrec-values ([(new-e e-ctx) (typecheck e ctx)]
                                     [(new-v v-ctx) (typecheck v e-ctx)]
                                     [(type-e type-v) (values (expr-type new-e) (expr-type new-v))])
                       (if (equal? type-v type-e)
                           (values (ml-set! void? new-v new-e) v-ctx)
                           (error (format "type doesn't match for ~a: ~a and ~a~n" code type-v type-e))))]   

    ; binary operators
    [(ml-< _ e1 e2) (letrec-values ([(new-e1 e1-ctx) (typecheck e1 ctx)]
                                    [(new-e2 e2-ctx) (typecheck e2 e1-ctx)])
                      (if (and (equal? (expr-type new-e1) integer?) (equal? (expr-type new-e2) integer?))
                          (values (ml-< boolean? new-e1 new-e2) e2-ctx)
                          (error (format "types don't match: got ~a and ~a~n" (expr-type new-e1) (expr-type new-e2)))))]
    ;(struct ml-<= expr (e1 e2) #:transparent)
    ;(struct ml-> expr (e1 e2) #:transparent)
    ;(struct ml->= expr (e1 e2) #:transparent)
    ;(struct ml-eq expr (e1 e2) #:transparent)
    ;(struct ml-and expr (e1 e2) #:transparent)
    ;(struct ml-or expr (e1 e2) #:transparent)
    [(ml-+ _ e1 e2) (letrec-values ([(new-e1 e1-ctx) (typecheck e1 ctx)]
                                    [(new-e2 e2-ctx) (typecheck e2 e1-ctx)])
                      (if (and (equal? (expr-type new-e1) integer?) (equal? (expr-type new-e2) integer?))
                          (values (ml-+ integer? new-e1 new-e2) e2-ctx)
                          (error (format "types don't match: got ~a and ~a~n" (expr-type new-e1) (expr-type new-e2)))))]
    ;(struct ml-- expr (e1 e2) #:transparent)
    ;(struct ml-* expr (e1 e2) #:transparent)
    ;(struct ml-/ expr (e1 e2) #:transparent)

  
    ; list operations
    [(ml-list t es)
       (if (empty? es)
           (if (not (equal? t void?)) (values (ml-list t es) ctx)
               (error (format "must declare list type for ~a~n" (ml-list t es))))
       
           (let-values ([(checked final-ctx) (typecheck es ctx)])             
             (let ([type (expr-type (first checked))])
               (for ([c checked]
                     #:when (not (equal? (expr-type c) type)))
                 (error (format "type doesn't match for ~a. Expected ~a~n" c type)))
               (values (ml-list (ml-listof type) checked) final-ctx))))]
                                  
    [(ml-list-append _ l e) (letrec-values ([(new-e e-ctx) (typecheck e ctx)]
                                            [(new-l l-ctx) (typecheck l e-ctx)]
                                            [(new-l-type new-e-type) (values (expr-type new-l) (expr-type new-e))])
                              (if (ml-listof? new-l-type)
                                  (if (equal? (ml-listof-type new-l-type) new-e-type)
                                      (values (ml-list-append new-l-type new-l new-e) l-ctx)
                                      (error "types don't match: got ~a and ~a~n" new-l-type new-e-type))
                                  (error "value passed to list append is not a list: ~a~n" new-l-type)))]
                                            
                                                          
    [(ml-list-length _ l) (let-values ([(new-l l-ctx) (typecheck l ctx)])
                            (if (ml-listof? (expr-type new-l))
                                (values (ml-list-length integer? new-l) l-ctx)
                                (error (format "type doesn't match: got ~a~n" (expr-type new-l)))))]

    ;(struct ml-list-equal expr (l1 l2) #:transparent)
    [(ml-list-ref _ l e) (letrec-values ([(new-e e-ctx) (typecheck e ctx)]
                                         [(new-l l-ctx) (typecheck l e-ctx)]
                                         [(new-l-type new-e-type) (values (expr-type new-l) (expr-type new-e))])
                           (if (and (equal? new-e-type integer?) (ml-listof? new-l-type))
                               (values (ml-list-ref (ml-listof-type new-l-type) new-l new-e) l-ctx)
                               (error (format "types don't match: got ~a and ~a~n" new-l-type new-e-type))))]
                                             
    [(ml-decl name formals body ret-type)
     (letrec-values ([(c) (for/hash ([f formals]) (values (ml-var-name f) (expr-type f)))]
                     [(checked final-ctx) (typecheck body c)])                     
       (values (ml-decl name formals checked ret-type) final-ctx))]
    
    [e (error (format "vc NYI: ~a" e))]    
    ))


; test code below

;(define ast (ml-lookup 'select-*-test))
;(define ast (ml-lookup 'for-test))
;(construct-cfg ast)

;(define-values (checked _) (typecheck ast))

;(construct-cfg checked)

;(live-vars checked)

;(print-hash succ)


(provide live-vars lookup-live-in typecheck construct-cfg)
