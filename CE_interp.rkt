#lang racket

; C machine (C = control expression)
; CE machine ( C, E = lazy substitution "environment")
(require print-debug/print-dbg)
(define (meta-interpCE exp [env (hash)])
  (match exp
    [(? symbol? x) (hash-ref env x)]
    [`(λ (,x) ,eb) (λ (argv) (meta-interpCE eb (hash-set env x argv)))]
    [`(,ef ,ea)
     (define vf (meta-interpCE ef env))
     (define va (meta-interpCE ea env))
     (vf va)]))

(define x (meta-interpCE `(λ (x) x)))

; Closure-creating CE interp
(define (interpCE exp [env (hash)])
  (match exp
    [(? symbol? x)
     (hash-ref env x)]
    [`(λ (,x) ,eb)
     `(closure `(λ (,x) ,eb) ,env)]
    [`(,ef ,ea)
     (define vf (p-dbg (interpCE ef env)))
     (define va (p-dbg (interpCE ea env)))
     (match vf
       [`(closure (λ (,x) ,eb) ,envlam)
        (interpCE (p-dbg eb) (hash-set envlam x va))]
       )]
    ))
;; (define y (interpCE `((λ (x) x) (λ (x) x))))
; CEK interp, K=Continuations
; (interpCEK `((λ (y) (λ (y) y)) (λ (y) ((λ (x) x) y))))
; (interpCEK `((λ (x) x) (λ (y) y))
(define (interpCEK state)
  (match state
    [`(,(? symbol? x) ,env ,kont)
     (interpCEK (p-dbg `(,(cadr (hash-ref env x)) ,(caddr (hash-ref env x)) ,kont)))]
    [`((,ef ,eb) ,env ,kont)
     (interpCEK (p-dbg `(,ef ,env (ar ,eb ,env ,kont))))]
    [`(,v ,env (ar ,eb ,(? hash? env-prime) ,kont))
     (interpCEK (p-dbg `(,eb ,env-prime (fn ,v ,env ,kont))))]
    [`(,v ,env (fn (λ (,x) ,eb) ,(? hash? env-prime) ,kont))
     (interpCEK (p-dbg `(,eb ,(hash-set env-prime x `(clo ,v ,env)) ,kont)))]
    [`(,v ,env halt)
     `(clo ,v ,env)]
    )
  )
;; #;(interpCEK `(((λ (x) x) (λ (y) x)) ,(hash `x `(clo 0 ,(hash)) `y `(clo 1 ,(hash))) halt))
;; #;(interpCEK `(((λ (x) x) (λ (y) x)) ,(hash) halt))
;; #;(interpCEK `(((λ (y) (λ (y) y)) (λ (y) ((λ (x) x) y))) ,(hash) halt))

;; CESK interp, S = Store.
(define (interpCESK state)
  (match state
    [`(,(? symbol? x) ,env ,store ,kont)
     (define x-val-clo (hash-ref store (hash-ref env x)))
     (interpCESK `(,(cadr x-val-clo) ,(caddr x-val-clo) ,store ,kont))]
    [`((,ef ,eb) ,env ,store ,kont)
     (interpCESK (p-dbg `(,ef ,env ,store (ar ,eb ,env ,kont))))]
    [`(,v ,env ,store (ar ,eb ,env-prime ,kont))
     (interpCESK (p-dbg `(,eb ,env-prime ,store (fn ,v ,env ,kont))))]
    [`(,v ,env ,store (fn (λ (,x) ,eb) ,env-prime ,kont))
     (define addr (gensym))
     (interpCESK `(,eb ,(hash-set env-prime x addr) ,(hash-set store addr `(clo ,v ,env)) ,kont))]
    [`(,v ,env ,store halt)
     `(clo ,v ,env ,store)]
    )
  )

;; (interpCESK `(((λ (x) x) (λ (y) y)) ,(hash `x `x_addr) ,(hash `x_addr `(clo 0 (hash))) halt))
;; (interpCESK `(((λ (y) (λ (y) y)) (λ (y) ((λ (x) x) y))) ,(hash) ,(hash) halt))

;; CESK* Control Environment Store Kont-Pointer
(define (interpCESK* state)
  (match state
    [`(,(? symbol? x) ,env ,store ,kont-ptr)
     (define x-val-clo (hash-ref store (hash-ref env x)))
     (interpCESK* `(,(cadr x-val-clo) ,(caddr x-val-clo) ,store ,kont-ptr))]
    [`((,ef ,eb) ,env ,store ,kont-ptr)
     (define kont-addr (gensym "kont"))
     (interpCESK* (p-dbg `(,ef ,env ,(hash-set store kont-addr `(ar ,eb ,env ,kont-ptr)) ,kont-addr)))]
    [`(,v ,env ,store ,kont-ptr)
     (match (hash-ref store kont-ptr)
       [`(ar ,eb ,env-prime ,kont-ptr-prime)
        (define kont-addr (gensym "kont"))
        (interpCESK* (p-dbg `(,eb ,env-prime ,(hash-set store kont-addr `(fn ,v ,env ,kont-ptr-prime)) ,kont-addr)))]
       [`(fn (λ (,x) ,eb) ,env-prime ,kont-ptr-prime)
        (define var-addr (gensym "var"))
        (interpCESK* `(,eb ,(hash-set env-prime x var-addr) ,(hash-set store var-addr `(clo ,v ,env))  ,kont-ptr-prime))]
       [`halt
        `((clo ,v ,env) ,store)])]
    )
  )

(interpCESK* `( ((λ (x) (x (λ (z) z))) (λ (y) y)),(hash `x `x_addr) ,(hash `x_addr `(clo 0 (hash)) `halt-ptr `halt) halt-ptr))
;; (interpCESK* `( (λ (x) x),(hash) ,(hash `halt-ptr `halt) halt-ptr))


; extended to support if and other prims
(define (extendedCESK* state)
  (match state
    [`(,(? symbol? x) ,env ,store ,kont-ptr)
     (define x-val-clo (hash-ref store (hash-ref env x)))
     (extendedCESK* `(,(cadr x-val-clo) ,(caddr x-val-clo) ,store ,kont-ptr))]
    [`((,ef ,eb) ,env ,store ,kont-ptr)
     (define kont-addr (gensym "kont"))
     (extendedCESK* (p-dbg `(,ef ,env ,(hash-set store kont-addr `(ar ,eb ,env ,kont-ptr)) ,kont-addr)))]
    [`(,v ,env ,store ,kont-ptr)
     (match (hash-ref store kont-ptr)
       [`(ar ,eb ,env-prime ,kont-ptr-prime)
        (define kont-addr (gensym "kont"))
        (extendedCESK* (p-dbg `(,eb ,env-prime ,(hash-set store kont-addr `(fn ,v ,env ,kont-ptr-prime)) ,kont-addr)))]
       [`(fn (λ (,x) ,eb) ,env-prime ,kont-ptr-prime)
        (define var-addr (gensym "var"))
        (extendedCESK* `(,eb ,(hash-set env-prime x var-addr) ,(hash-set store var-addr `(clo ,v ,env))  ,kont-ptr-prime))]
       [`halt
        `((clo ,v ,env) ,store)])]))
