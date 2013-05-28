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

(test-predicate
 preservation-in
 (term (
  (((rfn Top b (:: (ca X) (rfn Top z (:: (cv l) Top)) (rfn Top z (:: (cv l) Top))) (:: (cv l) (sel b (ca X))) (:: (cm m) (sel b (ca X)) Top)) ((cv l) (location 0)) ((cm m) x1 (sel x1 (cv l))))
   ((rfn Top a1 (:: (cv b) (rfn Top b (:: (ca X) Bot Top) (:: (cv l) (sel b (ca X))) (:: (cm m) (sel b (ca X)) Top)))) ((cv b) (location 0))))
  (val d = (new (Top)) in
  (val f = (new ((rfn Top f
                      (:: (cm e) Top (sel (sel (location 1) (cv b)) (ca X))))
                 [(cm e) d (sel (sel (location 1) (cv b)) (cv l))])) in
  (val c = (new ((rfn Top c
                      (:: (cm c)
                          (rfn Top f
                               (:: (cm e) Top (sel (sel (location 1) (cv b)) (ca X))))
                          (rfn Top f
                               (:: (cm e) Top (sel (location 0) (ca X))))))
                 [(cm c) x x])) in
  (val g = (snd c (cm c) f) in
  (val r = (snd g (cm e) d) in
  (sel r (cv l))))))))))


(test-predicate
 preservation
 (term
  (val b = (new ((rfn Top b
                      (:: (ca X) Bot (rfn Top z (:: (ca Y) Top Top)))))) in
  (val a = (new ((rfn Top a
                      (:: (cv b) (rfn Top b (:: (ca X) Bot Top))))
                 [(cv b) b])) in
  (val g = (new ((rfn Top g
                      (:: (cm c) (rfn Top b (:: (ca X) Bot Top)) (rfn Top b (:: (ca X) Bot Top))))
                 [(cm c) x x])) in
  (val c = (snd g (cm c) (sel a (cv b))) in
  (val f = (new ((rfn Top f
                      (:: (cm e)
                          (rfn (sel c (ca X)) x
                               (:: (ca Y) (rfn Top z (:: (cv l) Top)) (rfn Top z (:: (cv l) Top))))
                          Top))
                 [(cm e) x (val g = (new ((rfn Top g
                                               (:: (cm e) (sel x (ca Y)) Top))
                                          [(cm e) y (sel y (cv l))])) in
                           (val y = (new ((rfn Top z
                                               (:: (cv l) Top))
                                          [(cv l) y])) in
                           (val r = (snd g (cm e) y) in
                           r)))])) in
  f)))))))

(test-predicate
 typechecks
 (term
  (val a = (new ((rfn Top a
                      (:: (cc C) Bot (rfn Top c
                                          (:: (ca M) (sel (sel c (cv f)) (ca M)) (sel (sel c (cv f)) (ca M)))
                                          (:: (cv f) (sel a (cc C)))))))) in
  (val c = (new ((sel a (cc C)) [(cv f) c])) in
  a))))

;; Infinite derivation during expansion :(
'(judgment-holds
  (expansion
   (((a (rfn Top a
             (:: (cc C) Bot (rfn Top c
                                 (:: (ca M) (sel (sel c (cv f)) (ca M)) (sel (sel c (cv f)) (ca M)))
                                 (:: (cv f) (sel a (cc C)))))))
     (b (sel a (cc C))))
    ())
   z
   (sel b (ca M))
   any))

(test-results)