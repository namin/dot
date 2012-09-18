#lang racket
(require redex)
(require "dotf.ss")
(require "dotf_typesetting.ss")

(typeset-just-terms-from-now-on)

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
           [(cv fst) potty] [(cv snd) dotty]]])
 (["pets_sub1" #t (e-subtype (sel pets (cc Dog)) (sel pets (cc Pet)))]
  ["pets_sub2" #t (e-subtype (sel pets (cc Poodle)) (sel pets (cc Dog)))])
 ([#f #t (cast Top pairs)])
)