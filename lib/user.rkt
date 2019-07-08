#lang racket

; DEPRECATED

(require syntax/parse (except-in "../lang/ir.rkt" expr) "util.rkt")

(define udos (make-hash))
; cannot directly mutate vars outside of module

(define (add-udo name type-args-body)
  (hash-set! udos name type-args-body))

;(define (lookup-udo name)
;  (hash-ref udos name))

(require (for-syntax syntax/parse (except-in "../lang/ir.rkt" expr)))


;(define-syntax (udo stx)
;  (printf "procesing udo ~a~n" stx)
;  (syntax-parse stx
;    [(_ (name arg ...) type body)
;     ; (name formals body ret-type)
;     #`(begin (struct name ml-decl () #:transparent)
;              (add-udo (syntax->datum #'name) (list (syntax->datum #'type) (syntax->datum #'(arg ...)) #'body)))]))

(define-syntax-rule (udo (name formals ...) type body)
  (begin
    (add-udo (syntax->datum #'name) (list (syntax->datum #'(formals ...)) (eval-type (syntax->datum #'type)) #'body))
    (check-fn-formals (syntax->datum #'(formals ...)) (syntax->datum #'type))
    (define (name arg . args)
      (ml-call integer? name (cons arg args)))))

(define (check-fn-formals formals types)
  ; decl has type (-> formalType1 formalType2 ...)
  ; if formalType is of the form (-> ...) then it is a function
  (for ([f formals]
        [t (list-tail types 1)] ; get rid of the first ->
        #:when (and (list? t) (equal? (first t) '->)))
    (printf "adding ~a to known functions~n" f)
    (add-known-fns f)    
    ))
       

(define (translate-udos prog)
;  (define (proc stx)
;    (printf "procesing udo ~a~n" (syntax->datum stx))
;    (syntax-parse stx
;      #:literals (if < <= + - and not)
;      
;      ;[(udo (name arg ...) body ...)
;      ;[(udo (name arg ...) body)
;      ; #`(begin (struct name ml-user (arg ...) #:transparent)
;      ;          ;(add-udo (ml-decl (syntax->datum #'name) (syntax->datum #'(arg ...)) #,(proc #'(body ...)) boolean?)))
;      ;          (add-udo (syntax->datum #'name) (ml-decl (syntax->datum #'name) (syntax->datum #'(arg ...)) #,(proc #'body) boolean?)))
;      ;]   
;
;      ; XXX need to add type
;      ;[(ml-define id e) #:when (identifier? #'id)  #`(ml-define boolean? (syntax->datum #'id) #,(proc #'e))]
;      ;[(ml-set! id e) #:when (identifier? #'id)    #`(ml-set! boolean? (syntax->datum #'id) #,(proc #'e))]
;
;      ;[(ml-if c e1 e2) #`(ml-if boolean? #,(proc #'c) #,(proc #'e1) #,(proc #'e2))]
;
;      ;[(ml-< e1 e2) #`(ml-< boolean? #,(proc #'e1) #,(proc #'e2))]
;
;      ;[(ml-not type e)  #`(ml-not type #,(proc #'e))]
;      ;[(ml-and type e1 e2) #`(ml-and type #,(proc #'e1) #,(proc #'e2))]
;      
;      ;[e #:when (or (number? (syntax->datum #'e)) (identifier? #'e))  #'(syntax->datum #'e)]
;
;      ; function call
;      ;(struct ml-call expr (decl args) #:transparent
;      ;[(name args ...) #`(ml-call boolean? (lookup-udo (syntax->datum #'name)) (list #,@(map proc (syntax->list #'(args ...)))))]
;      ;[(e ...) #`(list #,@(map proc (syntax->list #'(e ...))))]
;
;      [(if c e1 e2) (ml-if boolean? (proc #'c) (proc #'e1) (proc #'e2))]
;
;      [(< e1 e2) (ml-< boolean? (proc #'e1) (proc #'e2))]
;      [(<= e1 e2) (ml-<= boolean? (proc #'e1) (proc #'e2))]
;      [(+ e1 e2) (ml-+ integer? (proc #'e1) (proc #'e2))]
;      [(- e1 e2) (ml-- integer? (proc #'e1) (proc #'e2))]
;
;      [(not e)  (ml-not boolean? (proc #'e))]
;      [(and e1 e2) (ml-and boolean? (proc #'e1) (proc #'e2))]
;      
;      [e #:when (or (number? (syntax->datum #'e)) (identifier? #'e)) (syntax->datum #'e)]
;
;      ; XXX check if name exists
;      [(name args ...) (ml-call boolean? (syntax->datum #'name) (map proc (syntax->list #'(args ...))))]
;
;      ))
                                       
  (let ([udos (for/list ([udo (hash->list udos)])
                (let* ([name (car udo)]
                       [args (first (cdr udo))]
                       [type (second (cdr udo))]
                       [body (third (cdr udo))]
                       [parsed (parse-types args type)]
                       [arg-types (take parsed (- (length parsed) 1))]
                       [ret-type (last parsed)])
                  (printf "translating ~a~n" name)
                  (ml-decl name arg-types (to-ml body) ret-type)
                  ))])
    (make-ml-prog (ml-prog-wp prog) (append udos (ml-prog-decls prog)) (ml-prog-asserts prog) prog)))

(provide udo
         translate-udos)
