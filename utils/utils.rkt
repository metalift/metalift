
(struct _lte (arg1 arg2) #:transparent)
(struct _gte (arg1 arg2) #:transparent)
(struct _gt (arg1 arg2) #:transparent)
(struct _lt (arg1 arg2) #:transparent)
(struct _eq (arg1 arg2) #:transparent)
(struct _and (arg1 arg2) #:transparent)
(struct _or (arg1 arg2) #:transparent)
(struct _implies (arg1 arg2) #:transparent)
(struct _if (arg1 arg2 arg3) #:transparent)
(struct _add (arg1 arg2) #:transparent)
(struct _sub (arg1 arg2) #:transparent)
(struct _mul (arg1 arg2) #:transparent)
(struct _list_append (arg1 arg2) #:transparent)
(struct _list_concat (arg1 arg2) #:transparent)
(struct _list_tail (arg1 arg2) #:transparent)
(struct _list_eq (arg1 arg2) #:transparent)
(struct _list_take (arg1 arg2) #:transparent)
(struct _list_length (arg1) #:transparent)
(struct loc (id) #:transparent)
(define (interpret e env)
  (match e
    [(_lte a1 a2)  (<= (interpret a1 env) (interpret a2 env))]
    [(_gte a1 a2)  (>= (interpret a1 env) (interpret a2 env))]
    [(_gt a1 a2)  (> (interpret a1 env) (interpret a2 env))]
    [(_lt a1 a2)  (< (interpret a1 env) (interpret a2 env))]
    [(_eq a1 a2)  (= (interpret a1 env) (interpret a2 env))]
    [(_or a1 a2) (|| (interpret a1 env) (interpret a2 env))]
    [(_and a1 a2) (&& (interpret a1 env) (interpret a2 env))]
    [(_implies a1 a2) (=> (interpret a1 env) (interpret a2 env))]
    [(_if a1 a2 a3) (if (interpret a1 env) (interpret a2 env) (interpret a3 env))]
    [(_add a1 a2) (+ (interpret a1 env) (interpret a2 env))]
    [(_sub a1 a2) (- (interpret a1 env) (interpret a2 env))]
    [(_mul a1 a2) (* (interpret a1 env) (interpret a2 env))]
    [(_list_append a1 a2)  (append (interpret a1 env) (interpret a2 env))]
    [(_list_concat a1 a2)  (append (interpret a1 env) (interpret a2 env))]
    [(_list_tail a1 a2)  (list-tail-noerr (interpret a1 env) (interpret a2 env))]
    [(_list_eq a1 a2)  (equal? (interpret a1 env) (interpret a2 env))] ; not eq?
    [(_list_take a1 a2)  (take (interpret a1 env) (interpret a2 env)) ]
    [(_list_length a1)  (length (interpret a1 env))]
    [(loc i) (vector-ref env i)]
    [_ (interpret2 e env)]))

(define (list-ref-noerr l i)
  (if (&&  (>= i 0) (< i (length l))) (list-ref l i)
      0))
(define (list-tail-noerr l i)
  (if (&& (>= i 0) (<= i (length l))) (list-tail l i)
      (list)))
(define (list-append l i)
  (append l (list i)))
(define (list-empty)
  (list))
