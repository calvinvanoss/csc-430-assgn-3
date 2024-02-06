#lang typed/racket

(require typed/rackunit)

(define-type ExprC (U numC binopC idC appC ifleq0?))
(struct numC ([n : Real]) #:transparent)
(struct binopC ([s : Symbol][l : ExprC][r : ExprC]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct appC ([fun : Symbol][arg : ExprC]) #:transparent)
(struct ifleq0? ([test : ExprC] [if : ExprC] [else : ExprC]) #:transparent)

(struct fundefC ([name : Symbol][arg : Symbol][body : ExprC]) #:transparent)

; parse Sexp to ExprC
(: parse (-> Sexp ExprC))
(define (parse exp)
  (match exp
    [(list (? symbol? op) l r) (binopC op (parse l) (parse r))]
    [(list 'ifleq0? test if else) (ifleq0? (parse test) (parse if) (parse else))]
    [(? real? n) (numC n)]
    [(? symbol? s) (idC s)]
    [(list (? symbol? fun) (? real? arg)) (appC fun (parse arg))]
    [else (error "OAZO parse failure")]))

(check-equal? (parse '{+ x 14}) (binopC '+ (idC 'x) (numC 14)))
(check-equal? (parse '{- x 14}) (binopC '- (idC 'x) (numC 14)))
(check-equal? (parse '{* x 14}) (binopC '* (idC 'x) (numC 14)))
(check-equal? (parse '{/ x 14}) (binopC '/ (idC 'x) (numC 14)))
(check-equal? (parse '{f 2}) (appC 'f (numC 2)))
(check-equal? (parse '{ifleq0? 1 1 0}) (ifleq0? (numC 1) (numC 1) (numC 0)))
(check-exn (regexp (regexp-quote "OAZO parse failure")) (lambda () (parse '("test fail"))))

; parse Sexp into fundefC
(: parse-fundef (-> Sexp fundefC))
(define (parse-fundef exp)
  (match exp
    [(list 'func (list(? symbol? name) (? symbol? arg)) ': body) (fundefC name arg (parse body))]
    [else (error "OAZO parse-fundef failure")]))

(check-equal? (parse-fundef '{func {f x} : {+ x 14}}) (fundefC 'f 'x (binopC '+ (idC 'x) (numC 14))))
(check-exn (regexp (regexp-quote "OAZO parse-fundef failure")) (lambda () (parse-fundef '(k "test" "failure"))))

; parses Sexp into list of fundefC
(: parse-prog (-> Sexp (Listof fundefC)))
(define (parse-prog exp)
  (match exp
    [(cons f r) (cons (parse-fundef f) (parse-prog r))]
    ['() '()]
    [else (error "OAZO parse-prog failure")]))

(check-equal? (parse-prog '{{func {f x} : {+ x 14}}
                             {func {main init} : {f 2}}})
              (list (fundefC 'f 'x (binopC '+ (idC 'x) (numC 14))) (fundefC 'main 'init (appC 'f (numC 2)))))
(check-exn (regexp (regexp-quote "OAZO parse-prog failure")) (lambda () (parse-prog "")))

; replace 'for' with 'what' inside the expression 'in'
(: subst (-> ExprC Symbol ExprC ExprC))
(define (subst what for in)
  (match in
    [(numC n) in]
    [(idC s) (cond
               [(eq? s for) what]
               [else in])]
    [(appC fun arg) (appC fun (subst what for arg))]
    [(binopC op l r) (binopC op (subst what for l) (subst what for r))]
    [(ifleq0? test then else) (ifleq0? (subst what for test) (subst what for then) (subst what for else))]))

(check-equal? (subst (numC 4) 'this (binopC '+ (numC 3) (idC 'this))) (binopC '+ (numC 3) (numC 4)))
(check-equal? (subst (numC 3) 'this (binopC '+ (numC 3) (idC 'notthis))) (binopC '+ (numC 3) (idC 'notthis)))
(check-equal? (subst (numC 3) 'f (numC 4)) (numC 4))
(check-equal? (subst (numC 3) 'f (appC 'g (idC 'f))) (appC 'g (numC 3))) 
(check-equal? (subst (numC 3) 'f (binopC '- (numC 1) (numC 2))) (binopC '- (numC 1) (numC 2)))
(check-equal? (subst (numC 3) 'f (binopC '* (numC 1) (numC 2))) (binopC '* (numC 1) (numC 2)))
(check-equal? (subst (numC 3) 'f (binopC '/ (numC 1) (numC 2))) (binopC '/ (numC 1) (numC 2)))

; gets fundef body given name of fundef and list of fundefs
(: get-fundef (-> Symbol (Listof fundefC) ExprC))
(define (get-fundef name fds)
  (match fds
    [(cons f r) (cond
                  [(eq? (fundefC-name f) name) (fundefC-body f)]
                  [else (get-fundef name r)])]
    [else (error "OAZO get-fundef failure")]))

(check-equal? (get-fundef 'name (list (fundefC 'name 'arg (binopC '+ (numC 1) (numC 2)))))
              (binopC '+ (numC 1) (numC 2)))
(check-exn (regexp (regexp-quote "OAZO get-fundef failure"))
           (lambda () (get-fundef 'f (list (fundefC 'name 'arg (numC 4))))))

; gets fundef arg given name of fundef and list of fundefs
(: get-fundef-arg (-> Symbol (Listof fundefC) Symbol))
(define (get-fundef-arg name fds)
  (match fds
    [(cons f r) (cond
                  [(eq? (fundefC-name f) name) (fundefC-arg f)]
                  [else (get-fundef-arg name r)])]
    [else (error "OAZO get-fundef-arg failure")]))

(check-equal? (get-fundef-arg 'name (list (fundefC 'name 'arg (binopC '+ (numC 1) (numC 2))))) 'arg)
(check-exn (regexp (regexp-quote "OAZO get-fundef-arg failure"))
           (lambda () (get-fundef-arg 'f (list (fundefC 'name 'arg (numC 4))))))

; interprets exprC using a given list of fundefs to return the result of the interpretation as a Real
(: interp (-> ExprC (Listof fundefC) Real))
(define (interp exprc fds)
  (match exprc
    [(numC n) n]
    [(binopC op l r) (match op
                       ['+ (+ (interp l fds) (interp r fds))]
                       ['- (- (interp l fds) (interp r fds))]
                       ['* (* (interp l fds) (interp r fds))]
                       ['/ (/ (interp l fds) (interp r fds))]
                       [else (error "OAZO invalid op")])]
    [(appC fun arg) (interp (subst arg (get-fundef-arg fun fds) (get-fundef fun fds)) fds)]
    [(ifleq0? test then else) (if (<= 0 (interp test fds)) (interp then fds) (interp else fds))]))

(check-equal? (interp (binopC '+ (numC 1) (numC 2)) '()) 3)
(check-equal? (interp (binopC '- (numC 7) (numC 3)) '()) 4)
(check-equal? (interp (binopC '* (numC 7) (numC 3)) '()) 21)
(check-equal? (interp (binopC '/ (numC 9) (numC 3)) '()) 3)
(check-exn (regexp (regexp-quote "OAZO invalid op"))
           (lambda () (interp (binopC 'fail (numC 1) (numC 2)) '())))
(check-equal? (interp (appC 'f (numC 2)) (list (fundefC 'f 'x (binopC '+ (idC 'x) (numC 14))))) 16)

; interprets the function named main using the list of function definitions
(: interp-fns (-> (Listof fundefC) Real))
(define (interp-fns fds)
  (cond
    [(empty? fds) (error "OAZO main is empty")]
    [else (interp (get-fundef 'main fds) fds)]))

(check-equal? (interp-fns (list (fundefC 'main 'init (binopC '+ (numC 2) (numC 2))))) 4)
(check-exn (regexp (regexp-quote "OAZO main is empty"))
           (lambda () (interp-fns '())))

; parses and interprets an OAZO program 
(: top-interp (-> Sexp Real))
(define (top-interp fun-sexps)
  (interp-fns (parse-prog fun-sexps)))

(check-= (top-interp '{{func {f x} : {+ x 14}}
                       {func {main init} : {f 2}}}) 16 0)
(check-= (top-interp '{{func {f x} : {ifleq0? x {+ x 14} {+ x 2}}}
                       {func {main init} : {f -1}}}) 1 0)
(check-= (top-interp '{{func {f x} : {ifleq0? x {+ x 14} {+ x 2}}}
                       {func {main init} : {f 1}}}) 15 0)
; test case that consists of OAZO3 program which rounds numbers to the nearest integer
