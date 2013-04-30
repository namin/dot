#lang racket

(require redex redex/pict slideshow/pict "../../src/redex/dot.rkt")
(provide with-rewriters dot-term dot-term/val dot-reduction dot-metafunction dot-metafunctions dot-judgment-form)

(define-syntax-rule (dot-term t)
  (with-rewriters
   (λ () (dot-term dot t))))
(define-syntax-rule (dot-term/val t)
  (with-rewriters
   (λ () (term->pict/pretty-write dot t))))
(define-syntax-rule (dot-reduction)
  (with-rewriters
   (lambda () (render-reduction-relation red-rr #:style 'compact-vertical))))
(define-syntax-rule (dot-metafunction name cases)
  (with-rewriters
    (lambda ()
      (parameterize
        [(metafunction-cases (if cases cases (metafunction-cases)))
         (metafunction-pict-style 'left-right/compact-side-conditions)
         (metafunction-font-size 11)]
        (render-metafunction name)))))
(define-syntax-rule (dot-metafunctions name ... cases)
  (with-rewriters
    (lambda ()
      (parameterize
        [(metafunction-cases (if cases cases (metafunction-cases)))
         (metafunction-pict-style 'left-right/compact-side-conditions)
         (metafunction-font-size 11)]
        (render-metafunctions name ...)))))
(define-syntax-rule (dot-judgment-form name cases)
  (with-rewriters
    (lambda ()
      (parameterize
        [(judgment-form-cases (if cases cases (judgment-form-cases)))
         (metafunction-pict-style 'left-right/compact-side-conditions)
         (metafunction-font-size 11)]
        (render-judgment-form name)))))
(label-font-size 11)
(default-font-size 11)
(literal-style "Inconsolata")
(paren-style "Inconsolata")
(default-style "Inconsolata")
(non-terminal-style (cons 'italic "Helvetica"))
(metafunction-font-size 11)

(define (with-rewriters thnk)
  (thnk))

