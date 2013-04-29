#lang racket
(require redex)
(require "dota.ss")

;(require rackunit)
; redefining these so that redex includes them in the summary
(define (check-true e)
  (test-equal e #t))
(define (check-false e)
  (test-equal e #f))
(define (check-not-false e)
  (test-equal (not (not e)) #t))

;(trace-dot (term (val x = (new (Top)) in x)))
;(trace-dot (term (val x = (new ((rfn Top x (: (cv l) Top)) ((cv l) x))) in (sel x (cv l)))))
;(trace-dot (term (val x = (new ((rfn Top x (: (cm m) Top Top)) ((cm m) y y))) in (val r = (snd x (cm m) x) in r))))