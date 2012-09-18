#lang racket
(require redex)
(require "dotf.ss")
(require "dotf_typesetting.ss")

(typeset-just-terms-from-now-on)

(define-metafunction dot
  alias : Lt T -> DLt
  [(alias Lt T) (: Lt T T)])

(check-render-dot "exs" all
 ([[pets (rfn Top z
              (: (cc Pet) Bot Top)
              (: (cc Dog) Bot (sel z (cc Pet)))
              (: (cc Cat) Bot (sel z (cc Pet)))
              (: (cc Poodle) Bot (sel z (cc Dog)))
              (: (cc Dalmatian) Bot (sel z (cc Dog))))]
   [kitty (sel pets (cc Cat))]
   [pif (sel pets (cc Dog))]
   [potty (sel pets (cc Poodle))]
   [dotty (sel pets (cc Dalmatian))]]
  [[pairs (rfn Top z
               (: (cc Pair) Bot (rfn Top p
                                     (: (ca A) Bot Top)
                                     (: (ca B) Bot Top)
                                     (: (cv fst) (sel p (ca A)))
                                     (: (cv snd) (sel p (ca B))))))]
   [couple (rfn (sel pairs (cc Pair)) p
                (: (ca A) (sel pets (cc Poodle)) (sel pets (cc Poodle)))
                (: (ca B) (sel pets (cc Dalmatian)) (sel pets (cc Dalmatian))))
           [(cv fst) potty] [(cv snd) dotty]]]
  [[lists (rfn Top z
               (: (cc List) Bot (rfn Top l
                                     (: (ca Elem) Bot Top)
                                     (alias (ca ListOfElem) (rfn (sel z (cc List)) l2 (alias (ca Elem) (sel l (ca Elem)))))))
               (: (cc Cons) Bot (rfn ((sel z (cc List)) ∧ (sel pairs (cc Pair))) l
                                     (alias (ca A) (sel l (ca Elem)))
                                     (alias (ca B) (sel l (ca ListOfElem)))))
               (: (cc Nil) Bot (rfn (sel z (cc List)) l
                                    (: (ca Elem) Bot Bot))))]
   [nil (sel lists (cc Nil))]])
 (["pets_sub1" #t (e-subtype (sel pets (cc Dog)) (sel pets (cc Pet)))]
  ["pets_sub2" #t (e-subtype (sel pets (cc Poodle)) (sel pets (cc Dog)))])
 ([#f #t (cast Top pairs)])
 ([#f #t (cast Top lists)]
  [#f #t (cast Top (cast (sel lists (cc List)) nil))])
)