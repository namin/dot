#lang racket
(require redex)

(define-language dot
  ((x y z) variable-not-otherwise-mentioned)
  (l (label-value variable-not-otherwise-mentioned))
  (i natural)
  (loc (location i))
  (v loc (λ (x T) e))
  (vx v x)
  (e vx (e e) (valnew (x c) e) (sel e l))
  (p x loc (sel p l))
  (c (Tc (l vx) ...))
  (Gamma ([x T] ...))
  (store (c ...))
  (env (Gamma store))
  (Lt Lc La)
  (Lc (label-class variable-not-otherwise-mentioned))
  (La (label-abstract-type variable-not-otherwise-mentioned))
  ((S T U V) (sel p Lt) (refinement T z D ...) (-> T T) (/\ T T) (\/ T T) Top Bottom)
  ((Sc Tc) (sel p Lc) (refinement Tc z D ...) (/\ Tc Tc) Top)
  (D (: Lt S U) (: l T))
  (ec hole (ec e) (v ec) (sel ec l))
  (bool #t #f)
  (Lany Lt l))

(redex-match dot e (term (λ (x Top) x)))
(redex-match dot e (term (valnew (u (Top)) u)))
(redex-match dot e (term (valnew (u ((refinement Top self (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l)))))

(define-metafunction dot
  subst : any x any -> any
  ;; 1. x_1 bound, so don't continue in the λ body
  [(subst (λ (x_1 T_1) any_1) x_1 any_2)
   (λ (x_1 T_1) any_1)]
  [(subst (valnew (x_1 c_1) any_1) x_1 any_2)
   (valnew (x_1 c_1) any_1)]
  
  ;; 2. do capture avoiding substitution by generating a fresh name
  [(subst (λ (x_1 T_1) any_1) x_2 any_2)
   (λ (x_3 T_1)
     (subst (subst-var any_1 x_1 x_3) x_2 any_2))
   (where x_3 ,(variable-not-in (term (x_2 any_1 any_2))
                                (term x_1)))]
  [(subst (valnew (x_1 c_1) any_1) x_2 any_2)
   (valnew (x_3 (subst (subst-var c_1 x_1 x_3) x_2 any_2))
           (subst (subst-var any_1 x_1 x_3) x_2 any_2))
   (where x_3 ,(variable-not-in (term (x_2 c_1 any_1 any_2))
                                (term x_1)))]

    
  ;; do not treat labels as variables
  [(subst (label-value variable_1) x_1 any_1) (label-value variable_1)]
  [(subst (label-class variable_1) x_1 any_1) (label-class variable_1)]
  [(subst (label-abstract-type variable_1) x_1 any_1) (label-abstract-type variable_1)]

  ;; 3. replace X_1 with any_1
  [(subst x_1 x_1 any_1) any_1]
  
  ;; the last two cases just recur on the tree structure of the term
  [(subst (any_2 ...) x_1 any_1)
   ((subst any_2 x_1 any_1) ...)]
  [(subst any_2 x_1 any_1) any_2])

(define-metafunction dot
  subst-var : any x x -> any
  [(subst-var (any_1 ...) x_1 x_2)
   ((subst-var any_1 x_1 x_2) ...)]
  [(subst-var x_1 x_1 x_2) x_2]
  [(subst-var any_1 x_1 x_2) any_1])

(term (subst (λ (x Top) x) x y))
(term (subst (λ (y Top) x) x y))
(term (subst (λ (z Top) (z x)) x y))
(term (subst (valnew (u (Top)) x) x y))
(term (subst (valnew (u (Top)) x) x u))
(term (subst (valnew (u ((refinement Top self (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l))) l x))

(define-metafunction dot
  store-extend : store c -> store
  [(store-extend (c_before ...) c_new)
   (c_before ... c_new)])

(define-metafunction dot
  store-lookup : store i -> c or #f
  [(store-lookup (c ...) i)
   ,(if (< (term i) (length (term (c ...))))
        (list-ref (term (c ...)) (term i))
        #f)])

(define-metafunction dot
  store-fresh-location : store -> loc
  [(store-fresh-location (c ...))
   (location ,(length (term (c ...))))])

(define-metafunction dot
  value-label-lookup : c l -> v or #f
  [(value-label-lookup (Tc (l_req v_req) (l_after v_after) ...) l_req) v_req]
  [(value-label-lookup (Tc (l_first v_first) (l_after v_after) ...) l_req) (value-label-lookup (Tc (l_after v_after) ...) l_req)]
  [(value-label-lookup (Tc) l_req) #f])

(define-judgment-form dot
  #:mode (found I O)
  #:contract (found any bool)
  [(found #f #f)]
  [(found any #t)])

(define-judgment-form dot
  #:mode (red I I O O)
  #:contract (red store e e store)
  [(red store (in-hole ec ((λ (x T) e) v)) (in-hole ec (subst e x v)) store)] ;; (βv)
  [(red store (in-hole ec (valnew (x c) e)) (in-hole ec (subst e x loc_new)) (store-extend store (subst c x loc_new)))
   (where loc_new (store-fresh-location store))] ;; (New)
  [(red store (in-hole ec (sel (location i) l)) (in-hole ec v) store) ;; (Sel)
   (where c (store-lookup store i))
   (found c #t)
   (where v (value-label-lookup c l))
   (found v #t)])

(define red-rr
  (reduction-relation
   dot
   (--> (store_1 e_1) (store_2 e_2)
        (judgment-holds (red store_1 e_1 e_2 store_2)))))

(define (trace-dot expr)
  (traces red-rr (term (() ,expr))))

(trace-dot (term ((λ (x Top) x) (λ (x Top) x))))
(trace-dot (term (valnew (u (Top)) u)))
(trace-dot (term (valnew (u (Top)) ((λ (x Top) x) (λ (x Top) x)))))
(trace-dot (term (valnew (u ((refinement Top self (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l)))))

(define value? (redex-match dot v))
(define (single-step? e)
  (= (length (apply-reduction-relation red-rr (term (() ,e))))
     1))
(define (steps-to e)
  (match (apply-reduction-relation red-rr (term (() ,e)))
    [(list) #f]
    [(list any) any]
    [_ (error 'steps-to
              "multiple derivations for term ~a"
              e)]))

(define-metafunction dot
  gamma-extend : Gamma x T -> Gamma
  [(gamma-extend ((x_before T_before) ...) x_new T_new)
   ((x_before T_before) ... (x_new T_new))])

(define-metafunction dot
  gamma-lookup : Gamma x -> T or #f
  [(gamma-lookup ((x_before T_before) ... (x_req T_req)) x_req) T_req]
  [(gamma-lookup ((x_before T_before) ... (x_last T_last)) x_req) (gamma-lookup ((x_before T_before) ...) x_req)]
  [(gamma-lookup () x_req) #f])

(define-metafunction dot
  constructor-type-lookup : c -> Tc
  [(constructor-type-lookup (Tc any ...)) Tc])

(define-judgment-form dot
  #:mode (typeof I I O)
  #:contract (typeof env e T)
  [(typeof (Gamma store) x T)
   (where T (gamma-lookup Gamma x))
   (found T #t)]
  [(typeof (Gamma store) (valnew (x (Top)) e) T)
   (typeof ((gamma-extend Gamma x Top) store) e T)]
  [(typeof (Gamma store) (location i) Tc)
   (where c (store-lookup store i))
   (found c #t)
   (where Tc (constructor-type-lookup c))])

(define (typecheck env e)
  (match (judgment-holds (typeof ,env ,e T) T)
    [(list) #f]
    [(list T) T]
    [_ (error 'typecheck
              "multiple typing derivations for term ~a in environment ~a"
              e env)]))

(typecheck (term (() ())) (term (valnew (u (Top)) u)))
(typecheck (term (() ())) (term (valnew (o (Top)) (valnew (o (Top)) o))))

(define (progress e)
  (if (typecheck (term (() ())) e)
      (begin
        (printf "progress: trying ~a\n" e)
        (or (value? e)
            (single-step? e)))
      #t))

(define (preservation e)
  (if (and (typecheck (term (() ())) e) (single-step? e))
      (begin
        (printf "preservation: trying ~a\n" e)
        (let loop ((e e) (store (term ())))
          (or (value? e)
              (match (steps-to e)
                [(list store_to e_to)
                 (and (equal? (typecheck (term (() ,store)) e) (typecheck (term (() ,store_to)) e_to))
                      (loop e_to store_to))]
                [_ (error 'preservation "expect match")]))))
      #t))

(preservation (term (valnew (u (Top)) u)))

(redex-check dot e (progress (term e)))
(redex-check dot e (preservation (term e)))