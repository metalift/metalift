#lang racket

; translates ML IR to Sketch

(require "../lang/ir.rkt"
         "../lib/util.rkt"
         syntax/parse)

(define (to-sk p)
  (printf "**** Converting to sketch~n")

  (define out (open-output-string))        
  (define decls (for/list ([d (ml-prog-decls p)]) (sk/decl d)))
  (define harness-vars (for/fold ([vars (set)]) ([a (ml-prog-asserts p)]) (set-union vars (used-vars a))))         
  (define asserts (for/list ([a (ml-prog-asserts p)]) (format "  ~a; ~n" (sk/expr a))))
  (define-values (harness-args harness-inits) (parse-harness harness-vars))
    
  ; includes    
  (fprintf out "include \"../../sketch/mllist.sk\";~n~n")
  
  ; decls
  (fprintf out (string-join decls "~n"))
  
  ; chooses
  (fprintf out (string-join (sk/choose-impls) "~n"))
  
  ; harness
  
  (fprintf out (format "harness void main(~a) {~n~a~n~a ~n}" harness-args harness-inits (string-join asserts "~n")))
  
  (get-output-string out)
)


(define (parse-harness vars)
  
  (define (init-decl v)
    (let ([name (ml-var-name v)] [type (ml-expr-type v)])
      (match type
        ; XXX get rid of 'integer?
        [(or (== integer?) (== boolean?) (== 'integer?) (== 'boolean?)) (format "~a ~a" (sk/type type) (sk/name name))]
        [(ml-listof integer?) 
        ;[(list 'listof 'integer?)
         (let ([size (format "~a_sz" (sk/name name))]
               [vals (format "~a_vals" (sk/name name))])
           (format "int ~a, int[~a] ~a" size size vals))]
      )))
  
  (define (init-expr v)
    (let ([name (ml-var-name v)] [type (ml-expr-type v)])
      (match type
        ; XXX get rid of 'integer?
        [(or (== integer?) (== boolean?) (== 'integer?) (== 'boolean?)) ""]
        [(ml-listof integer?) 
        ;[(list 'listof 'integer?)
         (format "  ~a ~a = make_MLList(~a_sz, ~a_vals);" (sk/type type) (sk/name name) (sk/name name) (sk/name name))]
      )))
  
  (let ([decls empty] [inits empty])    
    (for ([v vars])
      (let ([name (ml-var-name v)] [type (ml-expr-type v)])
        (set! decls (cons (init-decl v) decls))
        (set! inits (cons (init-expr v) inits))
        ))
               
    ;(cons (sk/arg-list revised-vars #t) "")))
    (values (string-join decls ", ") (string-join inits "~n"))))
    

(define (sk/decl decl)
  (match decl
    [(ml-decl type name formals ret-var body)   
     (let ([translated-body (open-output-string)]
           [rtype (ml-decl-ret-type decl)])
       (for ([e (ml-block-body body)])
         (write-string (sk/expr e) translated-body))
       
       (format "~a ~a (~a) { ~a ~a; }~n~n" (sk/type rtype) (sk/name name) (sk/arg-list formals #t)
               (if (equal? rtype void?) "" "return")
               (get-output-string translated-body)))]))


(define choose-fns empty)

(define (sk/choose-impls)
  (define template #<<eos
~a choose~a (~a) {
  int chosen~a = ??(~a);
  if (chosen~a == 0) return v0;
~a
  else assert false;
}


eos
)
  (for/list ([fn choose-fns] [n (in-naturals)])
    (let* ([type (first fn)] [num-args (second fn)] [arg-str (third fn)]
           [arg-str (string-join (for/list ([n (in-range num-args)]) (format "~a v~a" (sk/type type) n)) ", ")])
      (format template (sk/type type) n arg-str n (exact-ceiling (log num-args 2)) n
              (string-join (for/list ([m (in-range 1 num-args)])
                             (format "  else if (chosen~a == ~a) return v~a;~n" n m m)) "~n")))))
 

(define (sk/expr e)

  (printf "**** Parsing to sk: ~a~n~n" e)
  (match e

    [(ml-assert type e) (format "assert(~a)" (sk/expr e))]
    [(ml-call type name args) (format "~a(~a)" (sk/name name) (sk/arg-list args #f #f))]    
    [(ml-choose type (list es ...)) (sk/choose type es)]        
    [(ml-implies type e1 e2) (format "(!(~a) || (~a))" (sk/expr e1) (sk/expr e2))]
    [(ml-if type c e1 e2) (format "(~a) ? ~a : ~a" (sk/expr c) (sk/expr e1) (sk/expr e2))]

    [(ml-and type es) (string-join (for/list ([e es]) (format "~a" (sk/expr e))) " && "
                                   #:before-first "( "
                                   #:after-last " )")]
                        
    
    [(ml-eq type e1 e2) (format "~a == ~a" (sk/expr e1) (sk/expr e2))]
    [(ml-not type e) (format "!(~a)" (sk/expr e))]
    [(ml-< type e1 e2) (format "(~a < ~a)" (sk/expr e1) (sk/expr e2))]
    [(ml-> type e1 e2) (format "(~a > ~a)" (sk/expr e1) (sk/expr e2))]
    [(ml-<= type e1 e2) (format "(~a <= ~a)" (sk/expr e1) (sk/expr e2))]
    [(ml->= type e1 e2) (format "(~a >= ~a)" (sk/expr e1) (sk/expr e2))]

    [(ml-+ type e1 e2) (format "(~a + ~a)" (sk/expr e1) (sk/expr e2))]
    [(ml-- type e1 e2) (format "(~a - ~a)" (sk/expr e1) (sk/expr e2))]    
    [(ml-* type e1 e2) (format "(~a * ~a)" (sk/expr e1) (sk/expr e2))]
    [(ml-/ type e1 e2) (format "(~a / ~a)" (sk/expr e1) (sk/expr e2))]    

    ; list functions   
    [(ml-list-append type l e) (format "list_append(~a, ~a)" (sk/expr l) (sk/expr e))]
    [(ml-list-equal type l1 l2) (format "list_equal(~a, ~a)" (sk/expr l1) (sk/expr l2))]
    [(ml-list-length type e) (format "list_length(~a)" (sk/expr e))]
    [(ml-list-prepend type e l) (format "list_prepend(~a, ~a)" (sk/expr e) (sk/expr l))]
    [(ml-list-ref type l e) (format "list_get(~a, ~a)" (sk/expr l) (sk/expr e))]
    [(ml-list-set type l i e) (format "list_set(~a, ~a, ~a)" (sk/expr l) (sk/expr i) (sk/expr e))]
    [(ml-list-tail type l e) (format "list_tail(~a, ~a)" (sk/expr l) (sk/expr e))]
    [(ml-list-take type l e) (format "list_take(~a, ~a)" (sk/expr l) (sk/expr e))]    
    [(ml-list type es)  (if (= (length es) 0) "list_empty()"     
                            (format "make_MLList(~a, ~a)" (length es) (sk/arg-list es #f #f)))]

    [(ml-var type n) (format "~a" (sk/name n))]
    ;[(ml-ret-val type fn) (format "~a_retval" (sk/name (ml-decl-name fn)))]
     
    ;[(? symbol? sym) (format "~a" (sk/name sym))]
    ;[(? number? n) (format "~a" n)]
    ;[(? boolean? n) (if (equal? n #t) "true" "false")]
    
    [e #:when (and (ml-lit? e) (equal? integer? (ml-expr-type e))) (ml-lit-val e)]
    [e #:when (and (ml-lit? e) (equal? boolean? (ml-expr-type e))) (if (equal? (ml-lit-val e) #t) "true" "false")]
    
    [(? procedure? n) (sk/name (second (regexp-match #rx"procedure:(.*)>" (format "~a" n))))]

    ;[e #:when (ml-user? e) (sk/udo e)]
    ))


(define (sk/choose type as)
  (let ([num (length choose-fns)]
        [args (sk/arg-list as #f #f)])
    (set! choose-fns (append (list (list type (length as) args)) choose-fns))
    (format "choose~a(~a)" num args)))

(define (sk/udo e)
  (printf "parse udo: ~a ~n" (struct->vector e))
  (match (struct->vector e)
    [(vector name type es ...) (format "~a(~a)" (sk/name (second (regexp-match #rx"struct:(.*)" (format "~a" name))))
                                       (sk/arg-list es #f))]))


(define (sk/arg-list args need-type [has-type #t])
  (let ([params (for/list ([a args])
                  (if need-type
                      (format "~a ~a" (sk/type (ml-expr-type a)) (sk/name (ml-var-name a)))
                      (if has-type
                          (format "~a" (sk/expr (ml-var-name a)))
                          (format "~a" (sk/expr a))
                          )))])
    (string-join params ", ")))


(define (sk/type t)
  (match t
    ['integer? "int"]
    ['boolean? "bit"]
    [(== boolean?) "bit"] ; vc.rkt uses boolean? explicitly
    [(== integer?) "int"] ; vc.rkt uses boolean? explicitly
    [(ml-listof type) (format "MLList<~a>" (sk/type type))]
    ;[(list 'listof 'integer?) "MLList<int>"]
    ;[(list 'listof type) (printf "MLList<~a>" (sk/type type))]
    [(list '-> args ...) "fun"]
    ))
  
;  (match t
;    [(== boolean?) "bit"]
;    [(== integer?) "int"]    
;    [flat-contract?
;     (let [(n (datum->syntax #f t))]
;       (printf "n is ~a and ~a~n" (flat-contract-predicate t) n)
;       (syntax-parse n
;         #:datum-literals (listof flat-contract)
;         [(flat-contract (listof e)) (format "got ~a" #'e)]))]     
;    ))

; escape sketch's reserved characters for names
(define (sk/name n)
  (let ([name (string-replace (string-replace (format "~a" n) "-" "_") "*" "_star")])
    ; procedure is printed as #<procedure:[name]>
    (if (procedure? n) (second (regexp-match #rx"procedure:(.*)>" name)) name)))



(provide to-sk)