#lang typed/racket

(require typed/rackunit)

(struct bind ([name : Symbol][val : Real]))
(define-type Env (Listof bind))

(define-type ExprC (U numC binopC idC appC ifleq0?))
(struct numC ([n : Real]) #:transparent)
(struct binopC ([s : Symbol][l : ExprC][r : ExprC]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct appC ([fun : Symbol][args : (Listof ExprC)]) #:transparent)
(struct ifleq0? ([test : ExprC] [if : ExprC] [else : ExprC]) #:transparent)

(struct fundefC ([name : Symbol][args : (Listof Symbol)][body : ExprC]) #:transparent)

(define-type Binop (U '+ '- '* '/))
(define-type InvalidId (U Binop 'func 'ifleq0? 'else))

; parse Sexp to ExprC
(: parse (-> Sexp ExprC))
(define (parse exp)
  (match exp
    [(list (? (make-predicate Binop) op) l r) (binopC op (parse l) (parse r))]
    [(list 'ifleq0? test if else) (ifleq0? (parse test) (parse if) (parse else))]
    [(? real? n) (numC n)]
    [(? symbol? s) (if ((make-predicate InvalidId) s) (error "OAZO invalid id") (idC s))]
    [(list (? symbol? fun) args ...) (if ((make-predicate Binop) fun) (error "OAZO incorrect binop arg number")
                                         (appC fun (map (lambda (arg) (parse arg)) args)))]
    [else (error "OAZO parse failure")]))

(check-equal? (parse '{+ x 14}) (binopC '+ (idC 'x) (numC 14)))
(check-equal? (parse '{- x 14}) (binopC '- (idC 'x) (numC 14)))
(check-equal? (parse '{* x 14}) (binopC '* (idC 'x) (numC 14)))
(check-equal? (parse '{/ x 14}) (binopC '/ (idC 'x) (numC 14)))
(check-equal? (parse '{f 2}) (appC 'f (list (numC 2))))
(check-equal? (parse '{f 1 2 3}) (appC 'f (list (numC 1) (numC 2) (numC 3))))
(check-equal? (parse '{f}) (appC 'f '()))
(check-equal? (parse '{ifleq0? 1 1 0}) (ifleq0? (numC 1) (numC 1) (numC 0)))
(check-exn (regexp (regexp-quote "OAZO parse failure")) (lambda () (parse '("test fail"))))
(check-exn (regexp (regexp-quote "OAZO invalid id")) (lambda () (parse '(+ / 3))))
(check-exn (regexp (regexp-quote "OAZO incorrect binop arg number")) (lambda () (parse '(+ 1))))

; parse Sexp into fundefC
(: parse-fundef (-> Sexp fundefC))
(define (parse-fundef exp)
  (match exp
    [(list 'func (list(? symbol? name) (? symbol? args) ...) ': body)
     (if (or ((make-predicate InvalidId) name) ((make-predicate InvalidId) args))
         (error "OAZO invalid func name")
         (fundefC name (cast args (Listof Symbol)) (parse body)))]
    [else (error "OAZO parse-fundef failure")]))

(check-equal? (parse-fundef '{func {f x} : {+ x 14}}) (fundefC 'f '(x) (binopC '+ (idC 'x) (numC 14))))
(check-equal? (parse-fundef '{func {f a b c} : {+ {+ a b} c}})
              (fundefC 'f '(a b c) (binopC '+ (binopC '+ (idC 'a) (idC 'b)) (idC 'c))))
(check-exn (regexp (regexp-quote "OAZO parse-fundef failure")) (lambda () (parse-fundef '(k "test" "failure"))))
(check-exn (regexp (regexp-quote "OAZO invalid func name")) (lambda () (parse-fundef '{func {+ l} : {+ 1 1}})))

; parses Sexp into list of fundefC
(: parse-prog (-> Sexp (Listof fundefC)))
(define (parse-prog exp)
  (match exp
    [(cons f r) (cons (parse-fundef f) (parse-prog r))]
    ['() '()]
    [else (error "OAZO parse-prog failure")]))

(check-equal? (parse-prog '{{func {f x} : {+ x 14}}
                            {func {main init} : {f 2}}})
              (list (fundefC 'f '(x) (binopC '+ (idC 'x) (numC 14))) (fundefC 'main '(init) (appC 'f (list (numC 2))))))
(check-exn (regexp (regexp-quote "OAZO parse-prog failure")) (lambda () (parse-prog "")))

; gets fundef body given name of fundef and list of fundefs
(: get-fundef (-> Symbol (Listof fundefC) fundefC))
(define (get-fundef name fds)
  (match fds
    [(cons f r) (cond
                  [(eq? (fundefC-name f) name) f]
                  [else (get-fundef name r)])]
    [else (error "OAZO get-fundef failure")]))

(check-equal? (get-fundef 'name (list (fundefC 'name '(arg) (binopC '+ (numC 1) (numC 2)))))
              (fundefC 'name '(arg) (binopC '+ (numC 1) (numC 2))))
(check-exn (regexp (regexp-quote "OAZO get-fundef failure"))
           (lambda () (get-fundef 'f (list (fundefC 'name '(arg) (numC 4))))))

; lookup
(: lookup (-> Symbol Env Real))
(define (lookup for env)
  (cond
    [(empty? env) (error "OAZO lookup: name not found")]
    [else (cond
            [(eq? for (bind-name (first env)))
             (bind-val (first env))]
            [else (lookup for (rest env))])]))

; interprets exprC using a given list of fundefs to return the result of the interpretation as a Real
(: interp (-> ExprC Env (Listof fundefC) Real))
(define (interp exprc env fds)
  (match exprc
    [(numC n) n]
    [(binopC op l r) (match op
                       ['+ (+ (interp l env fds) (interp r env fds))]
                       ['- (- (interp l env fds) (interp r env fds))]
                       ['* (* (interp l env fds) (interp r env fds))]
                       ['/ (let ([denominator (interp r env fds)])
                             (if (eq? denominator 0) (error "OAZO /0") (/ (interp l env fds) denominator)))]
                       [else (error "OAZO invalid op")])]
    [(appC fun args) (let ([fd (get-fundef fun fds)])
                       (if (eq? (length args) (length (fundefC-args fd)))
                           (interp (fundefC-body fd) (cast (map (lambda (arg param) (bind (cast arg Symbol) (interp (cast param ExprC) env fds))) (fundefC-args fd) args) Env) fds)
                           (error "OAZO incorrect number of arguments")))]
    [(idC n) (lookup n env)]))


(check-exn (regexp (regexp-quote "OAZO incorrect number of arguments"))
           (lambda () (interp (appC 'f '()) '() (list (fundefC 'f '(a b) (numC 0))))))
(check-exn (regexp (regexp-quote "OAZO incorrect number of arguments"))
           (lambda () (interp (appC 'f (list (numC 1) (numC 2))) '() (list (fundefC 'f '(a) (numC 0))))))
(check-= (interp (appC 'f (list (numC 1) (numC 2))) '() (list (fundefC 'f '(a b) (binopC '+ (idC 'a) (idC 'b))))) 3 0)
(check-exn (regexp (regexp-quote "OAZO /0"))
           (lambda () (interp (binopC '/ (numC 5) (numC 0)) '() '())))
(check-exn (regexp (regexp-quote "OAZO /0"))
           (lambda () (interp (binopC '/ (numC 5) (binopC '+ (numC 0) (numC 0))) '() '())))
(check-equal? (interp (binopC '+ (numC 1) (numC 2)) '() '()) 3)
(check-equal? (interp (binopC '- (numC 7) (numC 3)) '() '()) 4)
(check-equal? (interp (binopC '* (numC 7) (numC 3)) '() '()) 21)
(check-equal? (interp (binopC '/ (numC 9) (numC 3)) '() '()) 3)
(check-exn (regexp (regexp-quote "OAZO invalid op"))
           (lambda () (interp (binopC 'fail (numC 1) (numC 2)) '() '())))
(check-equal? (interp (appC 'f (list (numC 2))) '() (list (fundefC 'f '(x) (binopC '+ (idC 'x) (numC 14))))) 16)
(check-exn (regexp (regexp-quote "OAZO lookup: name not found"))
           (lambda () (interp (idC 'fail) '() '())))
#|

; interprets the function named main using the list of function definitions
(: interp-fns (-> (Listof fundefC) Real))
(define (interp-fns fds)
  (cond
    [(empty? fds) (error "OAZO main is empty")]
    [else (interp (subst 0 'init (fundefC-body (get-fundef 'main fds))) fds)]))

(check-equal? (interp-fns (list (fundefC 'main '(init) (binopC '+ (numC 2) (numC 2))))) 4)
(check-exn (regexp (regexp-quote "OAZO main is empty"))
           (lambda () (interp-fns '())))

; parses and interprets an OAZO program 
(: top-interp (-> Sexp Real))
(define (top-interp fun-sexps)
  (interp-fns (parse-prog fun-sexps)))

(check-= (top-interp '{{func {f x} : {+ x 14}}
                       {func {main init} : {f 2}}}) 16 0)
(check-= (top-interp '{{func {f x} : {ifleq0? x {+ x 14} {+ x 2}}}
                       {func {main init} : {f -1}}}) 13 0)
(check-= (top-interp '{{func {f x} : {ifleq0? x {+ x 14} {+ x 2}}}
                       {func {main init} : {f 1}}}) 3 0)
(check-= (top-interp '((func (minus-five x) : (+ x (* -1 5)))
                       (func (main init) : (minus-five (+ 8 init))))) 3 0)
(check-= (top-interp '{{func {f x y} : {+ x y}}
                       {func {main} : {f 1 2}}}) 3 0)
|#