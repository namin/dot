#lang racket
(require redex)
(require "dot.rkt")

;(require rackunit)
; redefining these so that redex includes them in the summary
(define (check-true e)
  (test-equal e #t))
(define (check-false e)
  (test-equal e #f))
(define (check-not-false e)
  (test-equal (not (not e)) #t))

;(trace-dot (term (val x = (new (Top)) in x)))
;(trace-dot (term (val x = (new ((rfn Top x (:: (cv l) Top)) ((cv l) x))) in (sel x (cv l)))))
;(trace-dot (term (val x = (new ((rfn Top x (:: (cm m) Top Top)) ((cm m) y y))) in (val r = (snd x (cm m) x) in r))))

(test-predicate preservation (term (val u = (new (Top)) in u)))
(test-predicate preservation (term (val u = (new ((rfn Top u (:: (cm l) Top Top)) [(cm l) x u])) in (val r = (snd u (cm l) u) in r))))

(test-predicate
 preservation
 (term
  (val b = (new ((rfn Top b
                      (:: (ca X) (rfn Top z (:: (cv l) Top)) (rfn Top z (:: (cv l) Top)))
                      (:: (cv l) (sel b (ca X)))
                      (:: (cm m) (sel b (ca X)) Top))
                 [(cv l) b] [(cm m) x (sel x (cv l))])) in
  (val a = (new ((rfn Top a
                      (:: (cv b) (rfn Top b
                                      (:: (ca X) Bot Top)
                                      (:: (cv l) (sel b (ca X)))
                                      (:: (cm m) (sel b (ca X)) Top))))
                 [(cv b) b])) in
  (val r = (snd (sel a (cv b)) (cm m) (sel (sel a (cv b)) (cv l))) in
  r)))))

(test-results)