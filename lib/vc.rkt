#lang racket

; compute verification conditions on programs written in ML, and
; express VCs using ML's IR
;
; this pass requires the type checker and live variables to have run

(require syntax/parse
         "../lang/ir.rkt" "util.rkt"
         (only-in "../lang/base.rkt" ml-udos ml-axioms))

(require "analysis.rkt")

; data structure to store the current VC being computed
(struct state (vc decls asserts) #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (printf "VC state:~ndecls:~n")
     (for ([d (state-decls self)]) (fprintf port "~a~n~n" d))
     (printf "~nasserts:~n")
     (for ([a (state-asserts self)]) (fprintf port "~a~n~n" a)))]
)

(define (vc code state)
  (printf "computing vc on ~a~ncurrent vc is ~a ~n~n" code state)
  (match code

    ; base ML statements
    [(ml-define _ v e) (vc/define v e state)]
      
    [(ml-if t test then else) (vc/ite t test (vc then state) (vc else state))]

    [(ml-for t test body)
     ; use results from live var analysis to determine the parameters of the invariant function
     ; live vars is returned as a set, we need a list for ml-call
     (vc/for t test body (set->list (lookup-live-in code))
                                  ;(list (ml-var (ml-listof integer?) 'in) (ml-var integer? 'i)
                                  ;      (ml-var (ml-listof integer?) 'out))
                          state)]
    [(ml-set! _ v e) (vc/define v e state)]
    
    [(ml-decl _ name formals body) (vc body state)]

    [(ml-block t body) (for/fold ([s state]) ([c (reverse body)]) (vc c s))]

    ; list functions
    ;[(ml-append (list l e) type)  (vc/define #'l #`(ml-append (list #,#'l #,#'e) #,#'type) prog)]
    [(ml-list-append t l e) (vc/define l (ml-list-append t (list l e)) state)]

    ; expressions
    [e #:when (or (ml-lit? e) (ml-var? e)) state]
    ;[e #:when (or (number? e) (symbol? e) (boolean? e)) state]
    
    [e (error (format "vc NYI: ~a" e))]    
    ))

(define (vc/define var expr s)
  (let ([new-vc (replace var expr (state-vc s))])
    (state new-vc (state-decls s) (state-asserts s))))
      

(define (vc/ite type test then-state else-state)
  (let ([new-vc (ml-if type test (state-vc then-state) (state-vc else-state))])
    (state new-vc         
           (remove-duplicates (append (state-decls then-state) (state-decls else-state)))
           (remove-duplicates (append (state-asserts then-state) (state-asserts else-state))))))
             
;; equivalent to
;; init
;; (for (true) #:break test (body incr))
;                
(define (vc/for type test body vars st)
  (define formal-types (for/list ([v vars]) (ml-expr-type v)))
  (define inv-decl (ml-decl (ml-fn-type formal-types boolean?) "inv" vars (ml-block void? (list (ml-synth boolean? vars vars)))))
  ;[inv (ml-call boolean? "inv" (for/list ([v vars]) (car v)))]

  (define inv (ml-call boolean? "inv" vars))

  (define body-vc 
    (for/fold ([s (state inv (state-decls st) (state-asserts st))])
              ([c (reverse (ml-block-body body))]) (vc c s)))
         
  (define new-decls (cons inv-decl (state-decls body-vc)))
  (define inv-implies-wp (ml-assert boolean? (ml-implies boolean? (ml-and boolean? (list (ml-not boolean? test) inv)) (ml-assert-e (state-vc st)))))
  (define inv-preserved (ml-assert boolean? (ml-implies boolean? (ml-and boolean? (list test inv)) (state-vc body-vc))))
         
  (define new-asserts (cons inv-implies-wp (cons inv-preserved (state-asserts st))))         

  (state
   (ml-assert boolean? (ml-eq boolean? inv (ml-lit boolean? true)))
   new-decls new-asserts))

    
; replace v with e in vc
(define (replace v e vc)
  (printf "replace ~a with ~a in ~a~n~n" v e vc)
  
  (match vc
    [(ml-assert type ex) (ml-assert type (replace v e ex))]
    [(ml-call type decl args) (ml-call type decl (replace v e args))]
    [(ml-eq type e1 e2) (ml-eq type (replace v e e1) (replace v e e2))]
    [(ml-+ type e1 e2) (ml-+ type (replace v e e1) (replace v e e2))]

    ; a function parameter
    [(cons arg t) #:when (procedure? t) (if (equal? arg v) e arg)]
    [(list args ...) (for/list [(a args)] (replace v e a))]

    ; list functions
    [(ml-list type elems) (ml-list type (for/list ([elem elems]) (replace v e elem)))]
    [(ml-list-append type l elem) (ml-list-append type (replace v e l) (replace v e elem))]
    
    ;[arg (if (equal? arg v) e arg)]))

    ;[(ml-ret-val t fn) vc]

    ; a single var expression    
    ;[(? symbol? s) (if (equal? s v) e s)]
    [(? ml-var? s) (if (and (equal? (ml-var-name s) (ml-var-name v)) (equal? (ml-expr-type s) (ml-expr-type v))) e s)]    

    ;[s #:when (or (number? s) (boolean? s)) s]
    ;[s #:when (ml-lit? s) s]
    [(ml-lit t v) vc]
    ))


; take in a ml-decl instead as the input needs to have type checked
;(define (compute-vc fn)
(define (compute-vc fndecl) 

  (printf "~n**** Begin VC computation on ~a ****~n" (ml-decl-name fndecl))

  ; (struct ml-decl expr (name formals body))
  (define decl (ml-decl (ml-expr-type fndecl) (ml-decl-name fndecl)
                        (append (ml-decl-formals fndecl) (list (ml-ret-val fndecl)))
                        (ml-decl-body fndecl)))

  (define vars-types (ml-decl-formals decl))
  (define vars vars-types) ;(for/list ([vt vars-types]) (car vt))] ; extract the var name

  (define pc-decl (ml-decl (ml-fn-type vars-types boolean?) "pc" vars (ml-block void? (list (ml-synth boolean? vars vars)))))
  (define pc (ml-assert boolean? (ml-eq boolean? (ml-call boolean? "pc" vars) (ml-lit boolean? true))))

  (define result (vc decl (state pc (list pc-decl) empty)))

  (ml-prog (state-decls result) (append (state-asserts result) (list (state-vc result))) (ml-axioms)))


(define (append-udos p)
  (ml-prog (append (ml-prog-decls p) (ml-udos)) (ml-prog-asserts p) (ml-prog-axioms p)))

(provide compute-vc append-udos)