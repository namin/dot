#lang racket
(require redex)
(require "dotf.ss")
(require "dotf_typesetting.ss")

;; encoding specific polymorphic methods

(define-metafunction dot
  val-pickLast : x T T T e -> e
  [(val-pickLast x_alt T_C T_A T_B e)
   (val x_alt = new ((rfn T_alt x_alt (: (cm choose) (sel x_alt (ca A)) (arrow (sel x_alt (ca B)) (sel x_alt (ca B)))))
                     [(cm choose) a (fun b (sel x_alt (ca B)) (sel x_alt (ca B)) b)]) in
    e)                                                                          
   (where T_alt (rfn (sel choices (cc Alt)) x_alt (: (ca C) T_C T_C) (: (ca A) T_A T_A) (: (ca B) T_B T_B)))])

(check-render-dot "encoding"
 ([pets (rfn Top z
             (: (cc Pet) Bot Top)
             (: (cc Dog) Bot (sel z (cc Pet)))
             (: (cc Cat) Bot (sel z (cc Pet)))
             (: (cc Poodle) Bot (sel z (cc Dog)))
             (: (cc Dalmatian) Bot (sel z (cc Dog))))]
  [kitty (sel pets (cc Cat))]
  [pif (sel pets (cc Dog))]
  [potty (sel pets (cc Poodle))]
  [dotty (sel pets (cc Dalmatian))]
  [choices (rfn Top z
                (: (cc Alt) Bot (rfn Top alt
                                     (: (ca C) Bot Top)
                                     (: (ca A) Bot (sel alt (ca C)))
                                     (: (ca B) Bot (sel alt (ca C)))
                                     (: (cm choose) (sel alt (ca A)) (arrow (sel alt (ca B)) ((sel alt (ca A)) ∨ (sel alt (ca B))))))))]
  [favorites (rfn Top z
                  (: (cv dog) (sel pets (cc Dog)))
                  (: (cv cat) (sel pets (cc Cat))))
             [(cv dog) dotty]
             [(cv cat) kitty]])
 [#f #t (cast Top pets)]
 [#f #t (e-subtype (sel pets (cc Dog)) (sel pets (cc Pet)))]
 [#f #t (e-subtype (sel pets (cc Poodle)) (sel pets (cc Dog)))]
 [#f #t (e-subtype (rfn (sel choices (cc Alt)) alt (: (ca C) (sel pets (cc Dog)) (sel pets (cc Dog)))) (sel choices (cc Alt)))]
 [#f #t (e-subtype (rfn (sel choices (cc Alt)) alt (: (ca C) Bot (sel pets (cc Dog)))) (rfn (sel choices (cc Alt)) alt (: (ca C) Bot (sel pets (cc Pet)))))]
 ["leafs_no_subtp" #f
  (e-subtype
   (rfn (sel choices (cc Alt)) alt (: (ca C) (sel pets (cc Dog)) (sel pets (cc Dog))))
   (rfn (sel choices (cc Alt)) alt (: (ca C) (sel pets (cc Pet)) (sel pets (cc Pet)))))]
 ["abs_c_subtp" #t
  (e-subtype
   (rfn (sel choices (cc Alt)) alt (: (ca C) Bot (sel pets (cc Dog))) (: (ca A) (sel alt (ca C)) (sel alt (ca C))) (: (ca B) (sel alt (ca C)) (sel alt (ca C))))
   (rfn (sel choices (cc Alt)) alt (: (ca C) Bot (sel pets (cc Pet))) (: (ca A) (sel alt (ca C)) (sel alt (ca C))) (: (ca B) (sel alt (ca C)) (sel alt (ca C)))))]
 ["alt_covariant" #t
  (val-pickLast alt (sel pets (cc Dog)) (sel pets (cc Poodle)) (sel pets (cc Dalmatian))
                (cast Top
                (cast (rfn (sel choices (cc Alt)) alt (: (ca C) Bot (sel pets (cc Dog))))
                      alt)))]
 ["dotty" #t
  (cast Top (val-pickLast alt (sel pets (cc Dog)) (sel pets (cc Poodle)) (sel pets (cc Dalmatian))
                          (cast (sel pets (cc Dalmatian)) (app (sel alt (cm choose) potty) dotty))))]
)