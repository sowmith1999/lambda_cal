#lang racket
(require racket/hash)
(require print-debug/print-dbg)
;; 0 CFA for λ call

(define (alloc x store)
  ;; (match state
  ;;   [`(,expr ,env ,store ,kont-ptr)
  (cons x (hash-count store))
  ;; ])
  )
(define (interpCESK* state)
  (match state
    [`(,(? symbol? x) ,env ,store ,kont-ptr)
     (define x-val-clo (hash-ref store (hash-ref env x)))
     (interpCESK* `(,(cadr x-val-clo) ,(caddr x-val-clo) ,store ,kont-ptr))]
    [`((,ef ,eb) ,env ,store ,kont-ptr)
     (define kont-addr (alloc `kont store))
     (interpCESK* (p-dbg `(,ef ,env ,(hash-set store kont-addr `(ar ,eb ,env ,kont-ptr)) ,kont-addr)))]
    [`(,v ,env ,store ,kont-ptr)
     (match (hash-ref store kont-ptr)
       [`(ar ,eb ,env-prime ,kont-ptr-prime)
        (define kont-addr (alloc `kont store))
        (interpCESK* (p-dbg `(,eb ,env-prime ,(hash-set store kont-addr `(fn ,v ,env ,kont-ptr-prime)) ,kont-addr)))]
       [`(fn (λ (,x) ,eb) ,env-prime ,kont-ptr-prime)
        (define var-addr (alloc v store))
        (interpCESK* `(,eb ,(hash-set env-prime x var-addr) ,(hash-set store var-addr `(clo ,v ,env))  ,kont-ptr-prime))]
       [`halt
        ;; `((clo ,v ,env) ,store)])]))
        ;; store])]))
        `(,v ,store)])]))
;; (define store (hash `x `(clo 0 ,(hash)) `y `(clo 1 ,(hash)) `halt `halt))
;; (define env (hash `x `x `y `y `halt `halt))
;; (interpCESK* `((((λ (x) x) (λ (y) y)) (λ (z) x)) ,env ,store halt))
;; (define env (hash `halt `halt))
;; (define store (hash `halt `halt))
;; (interpCESK* `(((λ (z) z)((( (λ (p)(λ (a) (λ (b) ((p a) b)))) (λ (x) (λ (y) y))) 0) 1)) ,env ,store halt))
;; (interpCESK* `((((λ (x) x) (λ (y) x)) 1) ,env ,store halt))

;; The 0-CFA
;; What makes a 0-CFA 0-CFA,
;; I can't seem to get intuitively how to write this so I will go ahead and just follow the rules

;; Store operations to support
;;      Pulling out an value(closure -- as every value is a closure)
;;      Adding a new value, i.e, creating a new store with the value and then joining them both
(define (make-store key value)
  (hash key (set value)))

(define (join-store store1 store2)
  (hash-union store1 store2 #:combine/key (λ (k v1 v2) (set-union v1 v2))))

;; In basic case, we should only have one element in for each addr in store
(define (store-ref store addr)
  (car (set->list (hash-ref store addr)))) ;; returns a set, not sure how that works yet

;; Time stuff
;; I don't see how exactly time should work
;; I will just use a counter in place that increments every instance time is made
(define (time-init)
  (define time 0)
  (define (increment-time)
    (set! time (+ time 1))
    time)
  increment-time)

(define get-time (time-init))

;; Address allocation
;; I think this needs to be bounded, do I just bound the number of addresses that
;; can be allocated, for now directly using gen-sym




;; Here we don't do context so, we don't give a time-stamp and return null for that.
(define (alloc-0cfa x state)
  (match state
    [`(,expr ,env ,store ,kont-ptr)
     (cons x kont-ptr)
     ])
  )

(define (abstractCESK* state)
  (match state
    [`(,(? symbol? x) ,env ,store ,kont-ptr)
     (define x-val-clo (hash-ref store (hash-ref env x)))
     (abstractCESK* `(,(cadr x-val-clo) ,(caddr x-val-clo) ,store ,kont-ptr))]
    [`((,ef ,eb) ,env ,store ,kont-ptr)
     (define kont-addr (alloc-0cfa `kont state))
     (abstractCESK* (p-dbg `(,ef ,env ,(hash-set store kont-addr `(ar ,eb ,env ,kont-ptr)) ,kont-addr)))]
    [`(,v ,env ,store ,kont-ptr)
     (match (hash-ref store kont-ptr)
       [`(ar ,eb ,env-prime ,kont-ptr-prime)
        (define kont-addr (alloc-0cfa `kont state))
        (abstractCESK* (p-dbg `(,eb ,env-prime ,(hash-set store kont-addr `(fn ,v ,env ,kont-ptr-prime)) ,kont-addr)))]
       [`(fn (λ (,x) ,eb) ,env-prime ,kont-ptr-prime)
        (define var-addr (alloc-0cfa v state))
        (abstractCESK* (p-dbg `(,eb ,(hash-set env-prime x var-addr) ,(hash-set store var-addr `(clo ,v ,env))  ,kont-ptr-prime)))]
       [`halt
        ;; `((clo ,v ,env) ,store)])]))
        ;; store])]))
        `(,v ,store)])]))
;; (define store (hash `x `(clo 0 ,(hash)) `y `(clo 1 ,(hash)) `halt `halt))
;; (define env (hash `x `x `y `y `halt `halt))
;; (interpCESK* `((((λ (x) x) (λ (y) y)) (λ (z) x)) ,env ,store halt))
(define env (hash `halt `halt `x `x))
(define store (hash `halt `halt `x `(clo 2 ())))
;; (abstractCESK* `(((λ (x) x) (λ (y) x)) ,env ,store halt))
;; (abstractCESK* `((((λ (x) x) (λ (y) x)) 1) ,env ,store halt))
;; (abstractCESK* `(((λ (x) x) (λ (y) y))
(abstractCESK* `(((λ (z) z)((( (λ (p)(λ (a) (λ (b) ((p a) b)))) (λ (x) (λ (y) x))) 0) 1)) ,env ,store halt))
;; (define store (hash `halt `halt (cons `y `()) 2))
;; (define env (hash `halt `halt `y (cons `y `())))
;; (zero-cfa `(((λ (x) x) (λ (y) y)) ,env ,store halt))
;; (abstractCESK* `((λ (x) x),(hash) ,(hash `halt-ptr `halt) halt-ptr ,(get-time)))
;; (abstractCESK* `(((λ (x) (x (λ (z) z))) (λ (y) y)),(hash) ,(hash `halt-ptr `halt) halt-ptr ,(get-time)))
;; (abstractCESK* `(((λ (x) (x (λ (z) z))) (λ (y) y)),(hash) ,(hash `halt-ptr (set `halt)) halt-ptr ,(get-time)))

