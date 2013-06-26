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

;; preservation counterexample
(test-predicate
 preservation
 (term
  (val b = (new ((rfn Top b
                      (:: (cm m) Bot (rfn Top z
                                          (:: (ca X) Top Bot)
                                          (:: (cv l) Top))))
                 [(cm m) bot bot])) in
  (val a = (new ((rfn Top a
                      (:: (cv b) (rfn Top b
                                      (:: (cm m) Bot (rfn Top z
                                                          (:: (ca X) Top Bot)
                                                          (:: (cv l) (sel z (ca X))))))))
                 [(cv b) b])) in
  (val r = (new ((rfn Top r
                      (:: (cm err) Top Bot)
                      (:: (cm ab) Top (rfn Top b
                                           (:: (cm m) Bot (rfn Top z
                                                               (:: (ca X) Top Bot)
                                                               (:: (cv l) (sel z (ca X))))))))
                 [(cm err) d (val e = (snd r (cm err) d) in e)]
                 [(cm ab) d (sel a (cv b))])) in
  (val w = (snd r (cm ab) r) in
  (val c = (snd r (cm err) r) in
  (val x = (snd w (cm m) c) in
  (sel (sel x (cv l)) (cv whatever))))))))))

(test-predicate
 typechecks
 (term
  (val a = (new ((rfn Top a
                      (:: (cc C) Bot (rfn Top c
                                          (:: (ca M) (sel (sel c (cv f)) (ca M)) (sel (sel c (cv f)) (ca M)))
                                          (:: (cv f) (sel a (cc C)))))))) in
  (val c = (new ((sel a (cc C)) [(cv f) c])) in
  a))))

(check-true (judgment-holds
  (expansion #t
   (((a (rfn Top a
             (:: (cc C) Bot (rfn Top c
                                 (:: (ca M) (sel (sel c (cv f)) (ca M)) (sel (sel c (cv f)) (ca M)))
                                 (:: (cv f) (sel a (cc C)))))))
     (b (sel a (cc C))))
    ())
   z
   (sel b (ca M))
   any)))

;;; Examples from
;;;   On Decidability of Nominal Subtyping with Variance
;;;   http://research.microsoft.com/en-us/um/people/akenn/generics/FOOL2007.pdf
;;;
;;; N<-Z> <::
;;; C <:: NNC
;;;
;;; 1. C <: NC
;;;
;;; class N<Z> { }
;;; class C extends N<N<? super C>> {
;;;   N<? super C> cast(C c) { return c; }
;;; }
;;;
(test-predicate
 preservation
 (term
  (val r = (new ((rfn Top r
                      (:: (cc N) Bot (rfn Top n (:: (ca Z) Bot Top)))
                      (:: (cc C) Bot (rfn (sel r (cc N)) c
                                          (:: (ca Z)
                                              (rfn (sel r (cc N)) n (:: (ca Z) (sel r (cc C)) Top))
                                              (rfn (sel r (cc N)) n (:: (ca Z) (sel r (cc C)) Top)))
                                          (:: (cm cast)
                                              (sel r (cc C))
                                              (rfn (sel r (cc N)) n (:: (ca Z) (sel r (cc C)) Top)))))))) in
  (val c = (new ((sel r (cc C))
                 [(cm cast) x x])) in
  c))))

;;; 2. CX <:: NNCCX
;;;
;;; class T { }
;;; class N<Z> { }
;;; class C<X> extends N<N<? super C<C<X>>>> {
;;;   N<? super C<T>> cast(C<T> c) { return c; }
;;; }
;;;
;;; expansively hangs
'(test-predicate
 preservation
 (term
  (val r = (new ((rfn Top r
                      (:: (cc T) Bot Top)
                      (:: (cc N) Bot (rfn Top n (:: (ca Z) Bot Top)))
                      (:: (cc C) Bot (rfn (sel r (cc N)) c0
                                          (:= (ca Z) (rfn (sel r (cc N)) n
                                                               (:: (ca Z)
                                                                   (rfn (sel r (cc C)) c
                                                                        (:= (ca X) (rfn (sel r (cc C)) c
                                                                                        (:= (ca X) (sel c0 (ca X))))))
                                                                   Top)))
                                          (:: (ca X) Bot Top)
                                          (:: (cm cast)
                                              (rfn (sel r (cc C)) c (:= (ca X) (sel r (cc T))))
                                              (rfn (sel r (cc N)) n (:: (ca Z) (rfn (sel r (cc C)) c (:= (ca X) (sel r (cc T)))) Top)))))))) in
  (val c = (new ((sel r (cc C))
                 [(cm cast) x x])) in
  c))))

(check-false ;; why concrete types must be declared only once --
             ;; their expansion needs to be static
(preservation
 (term
  (val a = (new ((rfn Top a
                      (:: (cc C) Bot (rfn Top c (:: (cv l) Top)))
                      (:: (cm go) (sel a (cc C)) Top)
                      (:: (cm cast)
                          (rfn Top a
                               (:: (cc C) Bot (rfn Top c (:: (cv l) Top)))
                               (:: (cm go) (sel a (cc C)) Top))
                          (rfn Top a
                               (:: (cc C) Bot Top)
                               (:: (cm go) (sel a (cc C)) Top))))
                 [(cm go) c (sel c (cv l))] [(cm cast) x x])) in
  (val b = (snd a (cm cast) a) in
  (val c = (new ((sel b (cc C)))) in
  (val x = (snd b (cm go) c) in
  x)))))))

;;; An essential use of path-dependent types, which should but does not typecheck.
(typechecks
(term
(val cell = (new ((rfn Top c (:: (ca V) Bot Top)))) in
(val copy = (new ((rfn Top f (:: (cm apply) (rfn Top c (:= (ca V) (sel cell (ca V)))) Top))
                  [(cm apply) x x])) in
(val r = (snd copy (cm apply) cell) in
 cell)))))

(test-results)