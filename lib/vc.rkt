#lang racket

; compute verification conditions on programs written in ML, and
; express VCs using ML's IR
;
; this pass requires the type checker and live variables to have run

(require syntax/parse)
(require (except-in "../lang/ir.rkt" expr) "util.rkt")
(require (only-in "../lang/base.rkt" ml-lookup ml-udos))

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
    
    [(ml-decl name formals body ret-type) (vc body state)]

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
  (let* ([inv-decl (ml-decl "inv" vars (list (ml-synth boolean? vars vars)) boolean?)]
         ;[inv (ml-call boolean? "inv" (for/list ([v vars]) (car v)))]
         [inv (ml-call boolean? "inv" vars)]

         [body-vc 
          (for/fold ([s (state inv (state-decls st) (state-asserts st))])
                    ([c (reverse (ml-block-body body))]) (vc c s))]
         
         [new-decls (cons inv-decl (state-decls body-vc))]
         [inv-implies-wp (ml-assert boolean? (ml-implies boolean? (ml-and boolean? (list (ml-not boolean? test) inv)) (ml-assert-e (state-vc st))))]
         [inv-preserved (ml-assert boolean? (ml-implies boolean? (ml-and boolean? (list test inv)) (state-vc body-vc)))]
         
         [new-asserts (cons inv-implies-wp (cons inv-preserved (state-asserts st)))]
         )

    (state
     (ml-assert boolean? (ml-eq boolean? inv (ml-lit boolean? true)))
     new-decls new-asserts)))

    
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

    ; a single var expression
    ;[(? symbol? s) (if (equal? s v) e s)]
    [(? ml-var? s) (if (and (equal? (ml-var-name s) (ml-var-name v)) (equal? (expr-type s) (expr-type v))) e s)]    

    ;[s #:when (or (number? s) (boolean? s)) s]
    [s #:when (ml-lit? s) s]
    ))


; take in a ml-decl instead as the input needs to have type checked
;(define (compute-vc fn)
(define (compute-vc decl) 
  (printf "~n**** Begin VC computation on ~a ****~n" (ml-decl-name decl))
  (letrec (;[decl (ml-lookup fn)] ; a ml-decl
           [vars-types (ml-decl-formals decl)]
           [vars vars-types] ;(for/list ([vt vars-types]) (car vt))] ; extract the var name
           [pc-decl (ml-decl "pc" vars-types (list (ml-synth boolean? vars vars)) boolean?)]
           [pc (ml-assert boolean? (ml-eq boolean? (ml-call boolean? "pc" vars) (ml-lit boolean? true)))]

           [result (vc decl (state pc (list pc-decl) empty))])

    (ml-prog (state-decls result) (append (state-asserts result) (list (state-vc result))))))


(define (append-udos p)
  (ml-prog (append (ml-prog-decls p) (ml-udos)) (ml-prog-asserts p)))

(provide compute-vc append-udos)