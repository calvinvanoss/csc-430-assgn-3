#lang typed/racket

(require typed/rackunit)

(define-type ExprC (U numC plusC subC multC divC idC appC))
(struct numC ([n : Real]) #:transparent)
(struct plusC ([l : ExprC][r : ExprC]) #:transparent)
(struct subC ([l : ExprC][r : ExprC]) #:transparent)
(struct multC ([l : ExprC][r : ExprC]) #:transparent)
(struct divC ([l : ExprC][r : ExprC]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct appC ([fun : Symbol][arg : ExprC]) #:transparent)

(struct fundefC ([name : Symbol][arg : Symbol][body : ExprC]) #:transparent)

; parse Sexp to ExprC
(: parse (-> Sexp ExprC))
(define (parse exp)
  ; parse binop into ExprC
  (: parse-binop (-> Symbol Sexp Sexp ExprC))
  (define (parse-binop op l r)
    (match op
      ['+ (plusC (parse l) (parse r))]
      ['- (subC (parse l) (parse r))]
      ['* (multC (parse l) (parse r))]
      ['/ (divC (parse l) (parse r))]
      [else (error "OAZO parse-binop failure")]))
  (match exp
    [(list (? symbol? op) l r) (parse-binop op l r)]
    [(? real? n) (numC n)]
    [(? symbol? s) (idC s)]
    [(list (? symbol? fun) (? real? arg)) (appC fun (parse arg))]
    [else (error "OAZO parse failure")]))

(check-equal? (parse '{+ x 14}) (plusC (idC 'x) (numC 14)))
(check-equal? (parse '{- x 14}) (subC (idC 'x) (numC 14)))
(check-equal? (parse '{* x 14}) (multC (idC 'x) (numC 14)))
(check-equal? (parse '{/ x 14}) (divC (idC 'x) (numC 14)))
(check-equal? (parse '{f 2}) (appC 'f (numC 2)))
(check-exn (regexp (regexp-quote "OAZO parse failure")) (lambda () (parse '("test fail"))))
(check-exn (regexp (regexp-quote "OAZO parse-binop failure")) (lambda () (parse '(k "test" "failure"))))

; parse Sexp into fundefC
(: parse-fundef (-> Sexp fundefC))
(define (parse-fundef exp)
  (match exp
    [(list 'func (list(? symbol? name) (? symbol? arg)) ': body) (fundefC name arg (parse body))]
    [else (error "OAZO parse-fundef failure")]))

(check-equal? (parse-fundef '{func {f x} : {+ x 14}}) (fundefC 'f 'x (plusC (idC 'x) (numC 14))))
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
              (list (fundefC 'f 'x (plusC (idC 'x) (numC 14))) (fundefC 'main 'init (appC 'f (numC 2)))))
(check-exn (regexp (regexp-quote "OAZO parse-prog failure")) (lambda () (parse-prog "")))

; replace 'in' with 'what' at symbol 'for'
(: subst (-> ExprC Symbol ExprC ExprC))
(define (subst what for in)
  (match in
    [(numC n) in]
    [(idC s) (cond
               [(eq? s for) what]
               [else in])]
    [(appC fun arg) (appC fun (subst what for arg))]
    [(plusC l r) (plusC (subst what for l) (subst what for r))]
    [(subC l r) (subC (subst what for l) (subst what for r))]
    [(multC l r) (multC (subst what for l) (subst what for r))]
    [(divC l r) (divC (subst what for l) (subst what for r))]))

(check-equal? (subst (numC 4) 'this (plusC (numC 3) (idC 'this))) (plusC (numC 3) (numC 4)))
(check-equal? (subst (numC 3) 'this (plusC (numC 3) (idC 'notthis))) (plusC (numC 3) (idC 'notthis)))
(check-equal? (subst (numC 3) 'f (numC 4)) (numC 4))
(check-equal? (subst (numC 3) 'f (appC 'g (idC 'f))) (appC 'g (numC 3))) 
(check-equal? (subst (numC 3) 'f (subC (numC 1) (numC 2))) (subC (numC 1) (numC 2)))
(check-equal? (subst (numC 3) 'f (multC (numC 1) (numC 2))) (multC (numC 1) (numC 2)))
(check-equal? (subst (numC 3) 'f (divC (numC 1) (numC 2))) (divC (numC 1) (numC 2)))

; gets fundef given name of fundef and list of fundefs
(: get-fundef (-> Symbol (Listof fundefC) ExprC))
(define (get-fundef name fds)
  (match fds
    [(cons f r) (cond
                  [(eq? (fundefC-name f) name) (fundefC-body f)]
                  [else (get-fundef name r)])]
    [else (error "OAZO get-fundef failure")]))

(check-equal? (get-fundef 'name (list (fundefC 'name 'arg (plusC (numC 1) (numC 2))))) (plusC (numC 1) (numC 2)))
(check-exn (regexp (regexp-quote "OAZO get-fundef failure"))
           (lambda () (get-fundef 'f (list (fundefC 'name 'arg (numC 4))))))

; interprets exprC using a given list of fundefs to return the result of the interpretation as a Real
(: interp (-> ExprC (Listof fundefC) Real))
(define (interp exprc fds)
  (match exprc
    [(numC n) n]
    [(plusC l r) (+ (interp l fds) (interp r fds))]
    [(subC l r) (- (interp l fds) (interp r fds))]
    [(multC l r) (* (interp l fds) (interp r fds))]
    [(divC l r) (/ (interp l fds) (interp r fds))]
    [(appC fun arg) (let ([fd (get-fundef fun fds)]) (interp (subst arg fun fd) fds))]
    [(idC _) (error "OAZO interp shouldn't get here")]))

(check-equal? (interp (plusC (numC 1) (numC 2)) '()) 3)
(check-equal? (interp (subC (numC 7) (numC 3)) '()) 4)
(check-equal? (interp (multC (numC 7) (numC 3)) '()) 21)
(check-equal? (interp (divC (numC 9) (numC 3)) '()) 3)
; needs appC case
(check-exn (regexp (regexp-quote "OAZO interp shouldn't get here"))
           (lambda () (interp (appC 'name (numC 2)) (list (fundefC 'name 'arg (plusC (numC 4) (idC 'arg)))))))

; interprets the function named main using the list of function definitions
(: interp-fns (-> (Listof fundefC) Real))
(define (interp-fns funs)
  (cond
    [(empty? funs) (error "OAZO main is empty")]
    [else (interp (get-fundef 'main funs) funs)]))

(check-equal? (interp-fns (list (fundefC 'main 'init (plusC (numC 2) (numC 2))))) 4)
(check-exn (regexp (regexp-quote "OAZO main is empty"))
           (lambda () (interp-fns '())))

; parses and interprets an OAZO program 
(: top-interp (-> Sexp Real))
(define (top-interp fun-sexps)
  (interp-fns (parse-prog fun-sexps)))

; test case that consists of OAZO3 program which rounds numbers to the nearest integer
