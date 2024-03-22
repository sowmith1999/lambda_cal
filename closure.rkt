#lang racket
(define (time-init)
  (define time 0)
  (define (increment-time)
    (set! time (+ time 1))
    time)
  increment-time)

; Usage:
(define get-time (time-init))

; Now every time you call `get-time`, it will return the incremented value
(get-time) ; => 1
(get-time) ; => 2
(get-time) ; => 3
