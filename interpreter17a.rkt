#lang racket

(require "../chez-init.rkt")
(provide eval-one-exp reset-global-env)

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

; parsed expression.  You'll probably want to replace this 
; code with your expression datatype from A11b
(define lit?
  (lambda (x)
    (cond [(list? x) (eqv? (car x) 'quote)]
          [else (ormap 
                 (lambda (pred) (pred x))
                 (list number? boolean? string? null?))])))

(define display-exp
  (lambda (exp)
    (cases expression exp
      [var-exp (id)
               (display "var-exp: ")
               (newline)
               (display "id: ")
               (display id)
               (newline)]
      [lit-exp (datum)
               (display "lit-exp: ")
               (newline)
               (display "datum: ")
               (display datum)
               (newline)]
      [let-exp (func args bodies)
               (display "let-exp: ")
               (newline)
               (display "func: ")
               (display func)
               (newline)
               (display "args: ")
               (display args)
               (newline)
               (display "bodies ")
               (display bodies)
               (newline)]
      [app-exp (rator rands)
               (display "app-exp ")
               (newline)
               (display "rator: ")
               (display rator)
               (newline)
               (display "rands: ")
               (display rands)
               (newline)]
      [if-exp (cond-exp then-exp else-exp)
              (display "if-exp ")
               (newline)
               (display "cond-exp: ")
               (display cond-exp)
               (newline)
               (display "then-exp: ")
               (display then-exp)
               (newline)
               (display "else-exp: ")
               (display else-exp)
               (newline)]
      [else 'tba])))

(define-datatype expression expression?  
  [var-exp        ; variable references
   (id symbol?)]
  [lit-exp        ; "Normal" data.  Did I leave out any types?
   (datum
    (lambda (x)
      (ormap 
       (lambda (pred) (pred x))
       (list number? vector? boolean? symbol? string? pair? null?))))]
  [let-exp
   (func symbol?)
   (args (list-of? list?))
   (bodies (list-of? expression?))]
  [name-let-exp
   (name symbol?)
   (args (list-of? two-e-list?))
   (bodies (list-of? expression?))]
  [letrec-exp
   (proc-names (list-of? symbol?))
   (idss (list-of? (list-of? symbol?)))
   (bodiess (list-of? (list-of? expression?)))
   (letrec-bodies (list-of? expression?))]
  [if-exp
   (cond-exp expression?)
   (then-exp expression?)
   (else-exp (lambda(x) (or (null? x)
                            (expression? x))))]
  [lambda-exp
   (ids (lambda(x) (or ((list-of? symbol?) x)
                        (symbol? x)
                        (pair? x)))) 
   (bodies (list-of? expression?))]
  [while-exp
   (test-exp expression?)
   (bodies (list-of? expression?))]
  [set-exp
   (name symbol?)
   (value expression?)]
  [define-exp
    (name symbol?)
    (value expression?)]
  [app-exp        ; applications
   (rator expression?)
   (rands (list-of? expression?))])
	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals vector?)
   (env environment?)])


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
   (ids (lambda (x) (or ((list-of? symbol?) x)
                        (symbol? x)
                        (pair? x))))
   (bodies (list-of? expression?))
   (env environment?)])

  
;-------------------+
;                   |
;    sec:PARSER     |
;                   |
;-------------------+

; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Helper procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

; Again, you'll probably want to use your code from A11b

(define two-e-list?
  (lambda (x)
    (not (or (not (list? x))
             (null? x)
             (not (symbol? (car x)))
             (null? (cdr x))
             (not (null? (cddr x)))))))

(define lam-arg?
  (lambda (x)
    (cond [(null? x) #t]
          [else (or (pair? x) 
                    (symbol? x))])))

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]
      [(lit? datum) (if (list? datum)
                        (lit-exp (cadr datum))
                        (lit-exp datum))]
      [(pair? datum)
       (cond
         [(eqv? (car datum) 'if); if
          (if (or (null? (cdr datum))
                  (null? (cddr datum)))
              (error 'parse-exp "bad expression: ~s" datum)
              (if (null? (cdddr datum));without else
                  (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) '())
                  (if (not (null? (cddddr datum)));with else
                      (error 'parse-exp "bad expression: ~s" datum)
                      (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (cadddr datum))))))]
         [(eqv? (car datum) 'lambda); lambda
          (if (or (null? (cddr datum));no expression
                  (not (lam-arg? (2nd datum))))
              (error 'parse-exp "bad expression: ~s" datum)
              (lambda-exp (2nd datum)
                          (parse-bodies (cddr datum))))]
         [(or (eqv? (car datum) 'let);let
              (eqv? (car datum) 'let*))
          (cond [(list? (2nd datum)); not named let
                 (if (or (null? (cddr datum))
                         (not ((list-of? two-e-list?) (2nd datum))))
                     (error 'parse-exp "bad expression: ~s" datum)
                     (let-exp (car datum) (map (lambda (e)
                                                 (list (car e)
                                                       (parse-exp (cadr e)))) (2nd datum)) (parse-bodies (cddr datum))))]
                [(symbol? (2nd datum))
                 (if (or (null? (cdddr datum));name let
                         (not ((list-of? two-e-list?) (3rd datum))))
                     (error 'parse-exp "bad expression: ~s" datum)
                     (name-let-exp (2nd datum) (map (lambda (e)
                                                 (list (car e)
                                                       (parse-exp (cadr e)))) (3rd datum)) (parse-bodies (cdddr datum))))]
                [else (error 'parse-exp "bad expression: ~s" datum)])]
         [(eqv? (car datum) 'letrec);letrec
          (letrec-exp (map car (2nd datum))
                      (map cadadr (2nd datum))
                      (map parse-bodies (map cddadr (2nd datum)))
                      (parse-bodies (cddr datum)))]
         [(eqv? (car datum) 'while);while
          (while-exp (parse-exp (cadr datum))
                     (parse-bodies (cddr datum)))]
         [(eqv? (car datum) 'set!);set!
          (set-exp (cadr datum)
                   (parse-exp (caddr datum)))]
          [(eqv? (car datum) 'define);define
           (define-exp (cadr datum)
             (parse-exp (caddr datum)))]
         [else (app-exp (parse-exp (1st datum))
                        (map parse-exp (cdr datum)))])]
      [else (error 'parse-exp "bad expression: ~s" datum)])))

(define parse-bodies
  (lambda (exp)
    (if (null? (cdr exp))
        (list (parse-exp (car exp)))
        (cons (parse-exp (car exp))
              (parse-bodies (cdr exp))))))
              
;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+


; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (list->vector (map box (vector->list vals))) env)))

(define iota
  (lambda (n)
    (if (zero? n)
        '()
        (append (iota (- n 1)) (list (- n 1))))))

(define extend-env-recursively
  (lambda (proc-names idss bodiess old-env)
    (let ([len (length proc-names)])
      (let ([vec (make-vector len)])
        (let ([env (extended-env-record
                    proc-names vec old-env)])
          (for-each
           (lambda (pos ids bodies)
             (vector-set! vec pos (box (closure ids bodies env))))
             (iota len)
             idss
             bodiess)
           env)))))

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
            [(eq? sym (car los)) pos]
            [else (loop (cdr los) (add1 pos))]))))



(define apply-global-env
  (lambda (env sym)
    (cases environment env
      [extended-env-record (syms vals env)
                           (let ([pos (list-find-position sym syms)])
                             (if (number? pos)
                                 (vector-ref vals pos)
                                 (apply-global-env env sym)))]
      [empty-env-record ()
                        (error 'global-env "variable not define in global")])))

(define apply-env
  (lambda (env sym) 
    (cases environment env 
      [empty-env-record ()      
                        (apply-global-env global-env sym)]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (vector-ref vals pos)
                                 (apply-env env sym)))])))


;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

; To be added in assignment 14.


(define get-id
  (lambda (exp)
    (cases expression exp
      [var-exp (id) id]
      [else 'n])))

(define get-rator
  (lambda (exp)
    (cases expression exp
      [app-exp (rator rands) rator]
      [else 'n])))

(define get-rands
  (lambda (exp)
    (cases expression exp
      [app-exp (rator rands) rands]
      [else 'n])))

(define var-exp?
  (lambda (exp)
    (cases expression exp
      [var-exp (id) #t]
      [else #f])))

(define syntax-expand
  (lambda (exp)
    (cases expression exp
      [let-exp (func args bodies)
               (cond [(equal? func 'let)
                      (app-exp (lambda-exp (map car args) (map syntax-expand bodies)) (map syntax-expand (map cadr args)))]
                     [(equal? func 'let*)
                      (if (null? (cdr args));only one
                          (syntax-expand (let-exp 'let args bodies))
                          (app-exp (lambda-exp (list (caar args)) (list (syntax-expand (let-exp 'let* (cdr args) (map syntax-expand bodies))))) (list (cadar args))))]
                     [else (let-exp args (syntax-expand bodies))])]
      [var-exp (id) exp]
      [app-exp (rator rands)
               (cond [(equal? 'begin (get-id rator)) ;begin
                      (expand-bodies rands)]
                     [(equal? 'cond (get-id rator)) ;cond
                      (cond [(var-exp? (get-rator (car rands)));this is the else
                             (expand-bodies (get-rands (car rands)))]
                            [(null? (cdr rands))
                             (if-exp (syntax-expand (get-rator (car rands)))
                                     (expand-bodies (get-rands (car rands)))
                                     '())]
                            [else (if-exp (syntax-expand (get-rator (car rands)))
                                          (expand-bodies (get-rands (car rands)))
                                          (syntax-expand (app-exp (var-exp 'cond) (cdr rands))))])]
                     [(equal? 'and (get-id rator)); and
                      (cond [(null? rands) (lit-exp #t)]
                            [(null? (cdr rands))
                             (syntax-expand (car rands))]
                            [else (if-exp (syntax-expand (car rands))
                                          (syntax-expand (app-exp (var-exp 'and) (cdr rands)))
                                          (lit-exp #f))])]
                     [(equal? 'or (get-id rator));or
                      (cond [(null? rands) (lit-exp #f)]
                            [(null? (cdr rands))
                             (syntax-expand (car rands))]
;                            [else
;                             (let-exp 'let (list (list 'qwertyb (syntax-expand (car rands))));TODO: correct, define the rest as a closure in the let
;                                      (list (if-exp (var-exp 'qwertyb)
;                                                    (var-exp 'qwertyb)
;                                                    (syntax-expand (app-exp (var-exp 'or) (cdr rands))))))])]
                            [else
                             (syntax-expand (let-exp 'let (list (list 'rest (lambda-exp '() (list (syntax-expand (app-exp (var-exp 'or) (cdr rands))))))
                                                                (list 'a (syntax-expand (car rands))));TODO: correct, define the rest as a closure in the let
                                                     (list (if-exp (var-exp 'a)
                                                                   (var-exp 'a)
                                                                   (app-exp (var-exp 'rest)'())))))])]
                     [else (app-exp rator (map syntax-expand rands))])]
      [lit-exp (datum) exp]
      [if-exp (cond-exp then-exp else-exp)
              (if (null? else-exp)
                  (if-exp (syntax-expand cond-exp) (syntax-expand then-exp) else-exp)
                  (if-exp (syntax-expand cond-exp) (syntax-expand then-exp) (syntax-expand else-exp)))]
      [lambda-exp (args bodies) (lambda-exp args (map syntax-expand bodies))]
     
      [while-exp (test-exp bodies)
                 (while-exp (syntax-expand test-exp)
                            (map syntax-expand bodies))]
      [letrec-exp (proc-names idss bodiess letrec-bodies)
                  (letrec-exp proc-names idss (map (lambda(x) (map syntax-expand x)) bodiess) (map syntax-expand letrec-bodies))]
      [name-let-exp (name args bodies)
                    (letrec-exp (list name)
                                (list (map car args))
                                (list (map syntax-expand bodies))
                                (list (app-exp (var-exp name) (map syntax-expand (map cadr args)))))]
      [set-exp (name value)
               (set-exp name (syntax-expand value))]
      [define-exp (name value)
        (define-exp name (syntax-expand value))]
      [else (error 'eval-exp "Bad abstract syntax in syntax-expand: ~a" exp)])))
                           
(define expand-bodies
  (lambda (exps)
    (app-exp (lambda-exp '() (map syntax-expand exps)) '())))
;---------------------------------------+
;                                       |
; sec:CONTINUATION DATATYPE and APPLY-K |
;                                       |
;---------------------------------------+

; To be added in assignment 18a.


;-------------------+
;                   |
;  sec:INTERPRETER  |
;                   |
;-------------------+
(define eval-bodies
  (lambda (bodies env)
    (if (null? (cdr bodies))
        (eval-exp (car bodies) env)
        (begin
          (eval-exp (car bodies) env)
          (eval-bodies (cdr bodies) env)))))
                      
                       
; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
               (unbox (apply-env env id))]
      [letrec-exp (proc-names idss bodiess letrec-bodies)
                  (eval-bodies letrec-bodies
                               (extend-env-recursively
                                             proc-names idss bodiess env))]
      [lambda-exp (ids bodies)
        (closure ids bodies env)]
      [if-exp (cond-exp then-exp else-exp)
              (if (null? else-exp)
                  (if (eval-exp cond-exp env)
                      (eval-exp then-exp env)
                      (void))
                  (if (eval-exp cond-exp env)
                      (eval-exp then-exp env)
                      (eval-exp else-exp env)))]
      [while-exp (test-exp bodies)
                 (letrec ([h (lambda ()
                               (if (eval-exp test-exp env)
                                   (begin (eval-bodies bodies env) (h))
                                   "while terminate"))])
                   (h))]
      [set-exp (name value)
               (let ([ref (apply-env env name)]
                     [val (eval-exp value env)])
                 (set-box! ref val))]
      [define-exp (name value)
        (let ([value (eval-exp value env)]
              [ref (val-in-global? global-env name)])
              (if ref
                  (set-box! ref value)
                  (set! global-env (extend-env (list name) (vector value) global-env))))]                     
      [app-exp (rator rands)
               (let ([proc-value (eval-exp rator env)]
                     [args (eval-rands rands env)])
                 (apply-proc proc-value args))]
      [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))

(define val-in-global?
  (lambda (env sym)
    (cases environment env
      [extended-env-record (syms vals env)
                           (let ([pos (list-find-position sym syms)])
                             (if (number? pos)
                                 (vector-ref vals pos)
                                 (val-in-global? env sym)))]
      [empty-env-record ()
                        #f])))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (e) (eval-exp e env)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.
; a little helper for running lambda with (x y.z)
(define parse-ids-and-args
  (lambda (ls args)
    (if (symbol? ls)
        (values (list ls) (list args))
        (call-with-values
         (lambda () (parse-ids-and-args (cdr ls) (cdr args)))
         (lambda (ids rargs)
           (values (cons (car ls) ids)
                   (cons (car args) rargs)))))))
        


(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      ; You will add other cases
      [closure (ids bodies env) (cond [(list? ids) (eval-bodies bodies (extend-env ids (list->vector args) env))]
                                      [(symbol? ids) (eval-bodies bodies (extend-env (list ids) (list->vector (list args)) env))]
                                      [else (let ([output (call-with-values (lambda () (parse-ids-and-args ids args)) list)])
                                              (eval-bodies bodies (extend-env (car output) (list->vector (cadr output)) env)))])]
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))

(define *prim-proc-names* '(+ - * add1 sub1 cons = / zero? not < > <= >= car cdr list null? assq eq? equal? atom? length list->vector list? pair? procedure? vector->list vector make-vector vector-ref vector? number? symbol? vector-set! display newline caar cadr cdar cddr caaar caadr cadar caddr cdaar cdadr cddar cdddr map apply quotient negative? positive? eqv? append list-tail))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
   *prim-proc-names*   ;  a value (not an expression) with an identifier.
   (list->vector (map prim-proc      
        *prim-proc-names*))
   (empty-env)))

(define global-env init-env)

(define reset-global-env
  (lambda ()
    (set! global-env init-env)))

; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form
              (empty-env))))


; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    
    (case prim-proc
      
      [(-) (apply - args)] ;[(-) (- (1st args) (2nd args))]
      [(+) (apply + args)] ;[(+) (+ (1st args) (2nd args))]
      [(*) (apply * args)] ;[(*) (* (1st args) (2nd args))]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (apply = args)] ;[(=) (= (1st args) (2nd args))]
      [(/) (apply / args)]
      [(zero?) (zero? (1st args))]
      [(not) (not (1st args))]
      [(<) (apply < args)]
      [(>) (apply > args)]
      [(<=) (apply <= args)]
      [(>=) (apply >= args)]
      [(car) (car (1st args))]
      [(cdr) (cdr (1st args))]
      [(list) (apply list args)]
      [(null?) (null? (1st args))]
      [(assq) (assq (1st args) (2nd args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(atom?) (ormap
                (lambda (pred) (pred (1st args)))
                (list boolean? number? string? bytes? char? symbol? regexp? pregexp? byte-regexp? byte-pregexp? keyword? null? procedure? void? set?))]
      [(length) (length (1st args))]
      [(list->vector) (list->vector (1st args))]
      [(list?) (list? (1st args))]
      [(pair?) (pair? (1st args))]
      [(procedure?) (proc-val? (1st args))];note that here we have a list of symbols
      [(vector->list) (vector->list (1st args))]
      [(vector) (apply vector args)]
      [(make-vector) (apply make-vector args)];it takes one or two
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector?) (vector? (1st args))]
      [(number?) (number? (1st args))]
      [(symbol?) (symbol? (1st args))]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(display) (display (1st args))]
      [(newline) (newline)]
      [(map) (map (lambda (x)
                    (apply-proc (1st args) (list x))) (cadr args))]
      [(apply) (letrec ([h (lambda (lst result)
                             (if (null? lst)
                                 result
                                 (h (cdr lst) (apply-proc (1st args) (car lst) result))))])
                 (h (cddr args) (apply-proc (1st args) (2nd args))))]
      [(quotient) (quotient (1st args) (2nd args))]
      [(negative?) (negative? (1st args))]
      [(positive?) (positive? (1st args))]
      [(eqv?) (eqv? (1st args) (2nd args))]
      [(append) (apply append args)]
      [(list-tail) (list-tail (1st args) (2nd args))]
      [else (let ([il (string->list (symbol->string prim-proc))])
              (if (not (eq? #\c (car il)))
                  (error 'apply-prim-proc "Bad primitive procedure name: ~s" prim-proc)
                  (list->proc (cdr il) (1st args))))])))

(define list->proc
  (lambda (lst arg)
    (cond [(eq? #\r (car lst)) arg]
          [(eq? #\a (car lst)) (car (list->proc (cdr lst) arg))]
          [(eq? #\d (car lst)) (cdr (list->proc (cdr lst) arg))]
          [else (error 'apply-prim-proc "Error c**r instruction: ~s" lst)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))


;(eval-one-exp '(let ((r 2) (ls '(3)) (count 7)) ls))
;(eval-one-exp '(let ((r 2) (ls '(3)) (count 7)) (let loop () (if (> count 0) (begin (set! ls (cons r ls)) (set! r (+ r count)) (set! count (- count 1)) (loop)))) (list r ls count)))
;(begin (reset-global-env) (eval-one-exp '(define fib-memo (let ((max 2) (sofar '((1 . 1) (0 . 1)))) (lambda (n) (if (< n max) (cdr (assq n sofar)) (let* ((v1 (fib-memo (- n 1))) (v2 (fib-memo (- n 2))) (v3 (+ v2 v1))) (set! max (+ n 1)) (set! sofar (cons (cons n v3) sofar)) v3)))))) (eval-one-exp '(fib-memo 15)))
;(begin (reset-global-env) (eval-one-exp '(define rotate-linear (letrec ((reverse (lambda (lyst revlist) (if (null? lyst) revlist (reverse (cdr lyst) (cons (car lyst) revlist)))))) (lambda (los) (let loop ((los los) (sofar '())) (cond ((null? los) los) ((null? (cdr los)) (cons (car los) (reverse sofar '()))) (else (loop (cdr los) (cons (car los) sofar))))))))) (eval-one-exp '(rotate-linear '(1 2 3 4 5 6 7 8))))
;(begin (reset-global-env) (eval-one-exp '(define ns-list-recur (lambda (seed item-proc list-proc) (letrec ((helper (lambda (ls) (if (null? ls) seed (let ((c (car ls))) (if (or (pair? c) (null? c)) (list-proc (helper c) (helper (cdr ls))) (item-proc c (helper (cdr ls))))))))) helper)))) (eval-one-exp '(define append (lambda (s t) (if (null? s) t (cons (car s) (append (cdr s) t)))))) (eval-one-exp '(define reverse* (let ((snoc (lambda (x y) (append y (list x))))) (ns-list-recur '() snoc snoc)))) (eval-one-exp '(reverse* '(1 (2 3) (((4))) () 5))))