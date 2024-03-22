#lang racket
(require racket/hash)
(require print-debug/print-dbg)
;; 0 CFA for λ call
;; Write the interp and then change the store behaviour for a CFA, Yikes, No idea

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
        `((clo ,v ,env) ,store)])]))

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


;; Only store is abstract
;; Here the simple rule is, store(addr) -> {values..}, consider all of them as possibility
;; We need to fold over all the values in store when dereferencing an address
;; Question: How to figure out when to reuse addresses?
(define (abstractCESK* state)
  (match state
    [`(,(? symbol? x) ,env ,store ,kont-ptr ,time)
     (define x-val-clo (store-ref store (hash-ref env x)))
     (abstractCESK* (p-dbg `(,(cadr x-val-clo) ,(caddr x-val-clo)
                                               ,store ,kont-ptr ,(get-time))))]
    [`((,ef ,ea) ,env ,store ,kont-ptr ,time)
     (define kont-addr (gensym "kont"))
     (abstractCESK* (p-dbg `(,ef ,env ,(join-store store
                                                   (make-store kont-addr
                                                               `(ar ,ea ,env ,kont-ptr)))
                                 ,kont-addr ,(get-time))))]
    [`(,v ,env ,store ,kont-ptr ,time)
     (match (store-ref store kont-ptr)
       [`(ar ,ea ,env-prime ,kont-ptr-prime)
        (define kont-addr (gensym "kont"))
        (abstractCESK* (p-dbg `(,ea ,env-prime
                                    ,(join-store store
                                                 (make-store kont-addr
                                                             `(fn ,v ,env ,kont-ptr-prime)))
                                    ,kont-addr ,(get-time))))]
       [`(fn (λ (,x) ,eb) ,env-prime ,kont-ptr-prime)
        (define var-addr (gensym "var"))
        (abstractCESK* (p-dbg `(,eb ,(hash-set env-prime x var-addr)
                                    ,(join-store store (make-store var-addr `(clo ,v ,env)))
                                    ,kont-ptr-prime
                                    ,(get-time))))]
       [`halt
        state])]))

;; (abstractCESK* `((λ (x) x),(hash) ,(hash `halt-ptr `halt) halt-ptr ,(get-time)))
;; (abstractCESK* `(((λ (x) (x (λ (z) z))) (λ (y) y)),(hash) ,(hash `halt-ptr `halt) halt-ptr ,(get-time)))
;; (abstractCESK* `(((λ (x) (x (λ (z) z))) (λ (y) y)),(hash) ,(hash `halt-ptr (set `halt)) halt-ptr ,(get-time)))

(define (alloc x state)
  (match state
    [`(,expr ,env ,store ,kont-ptr)
     (cons x (hash-count store))]
    )
  )
;; Here we don't do context so, we don't give a time-stamp and return null for that.
(define (alloc-0cfa x state)
  (match state
    [`(,expr ,env ,store ,kont-ptr)
     (cons x '())]
    )
  )
;; zero-cfa doesn't need time
(define (zero-cfa state)
  (match state
    [`(,(? number? x) ,env ,store ,kont-ptr)
      `,x]
    [`(,(? symbol? x) ,env ,store ,kont-ptr)
     (define x-val-clo (store-ref store (hash-ref env x)))
     (zero-cfa (p-dbg `(,(cadr x-val-clo) ,(caddr x-val-clo)
                                          ,store ,kont-ptr)))]
    [`((,ef ,ea) ,env ,store ,kont-ptr)
     (define kont-addr (gensym "kont"))
     (zero-cfa (p-dbg `(,ef ,env ,(join-store store
                                              (make-store kont-addr
                                                          `(ar ,ea ,env ,kont-ptr)))
                            ,kont-addr)))]
    [`(,v ,env ,store ,kont-ptr)
     (match (store-ref store kont-ptr)
       [`(ar ,ea ,env-prime ,kont-ptr-prime)
        (define kont-addr (gensym "kont"))
        (zero-cfa (p-dbg `(,ea ,env-prime
                               ,(join-store store
                                            (make-store kont-addr
                                                        `(fn ,v ,env ,kont-ptr-prime)))
                               ,kont-addr)))]
       [`(fn (λ (,x) ,eb) ,env-prime ,kont-ptr-prime)
        (define var-addr (gensym "var"))
        (zero-cfa (p-dbg `(,eb ,(hash-set env-prime x var-addr)
                               ,(join-store store (make-store var-addr `(clo ,v ,env)))
                               ,kont-ptr-prime)))]
       [`halt
        state])]))
(define store (hash `halt `halt (cons `y `()) 2))
(define env (hash `halt `halt `y (cons `y `())))
(zero-cfa `(((λ (x) x) (λ (y) y)) ,env ,store halt))
