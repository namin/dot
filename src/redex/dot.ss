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
  ((S T U V) (sel p Lt) (refinement T z DLt ... Dl ...) (-> T T) (intersection T T) (union T T) Top Bottom)
  ((Sc Tc) (sel p Lc) (refinement Tc z DLt ... Dl ...) (intersection Tc Tc) Top)
  (DLt (: Lt S U))
  (Dl (: l T))
  (D DLt Dl)
  (ec hole (ec e) (v ec) (sel ec l))
  (bool #t #f)
  (Lany Lt l))

(define-extended-language mini-dot dot
  ((S T U V) (-> T T) Top)
  ((Sc Tc) (refinement Tc z Dl ...) Top))

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
  [(subst (refinement Tc_1 x_1 D_1 ...) x_1 any_2)
   (refinement Tc_1 x_1 D_1 ...)]
  
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
  [(subst (refinement Tc_1 x_1 D_1 ...) x_2 any_2)
   (refinement (subst (subst-var Tc_1 x_1 x_3) x_2 any_2) x_3 (subst (subst-var D_1 x_1 x_3) x_2 any_2) ...)
   (where x_3 ,(variable-not-in (term (Tc_1 D_1 ... x_2 any_2))
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
  [(subst-var (label-value variable_1) x_1 x_2) (label-value variable_1)]
  [(subst-var (label-class variable_1) x_1 x_2) (label-class variable_1)]
  [(subst-var (label-abstract-type variable_1) x_1 x_2) (label-abstract-type variable_1)]

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

;(trace-dot (term ((λ (x Top) x) (λ (x Top) x))))
;(trace-dot (term (valnew (u (Top)) u)))
;(trace-dot (term (valnew (u (Top)) ((λ (x Top) x) (λ (x Top) x)))))
;(trace-dot (term (valnew (u ((refinement Top self (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l)))))

(define value? (redex-match dot v))
(define (single-step? e)
  (= (length (apply-reduction-relation red-rr (term (() ,e))))
     1))
(define (steps-to store e)
  (match (apply-reduction-relation red-rr (term (,store ,e)))
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
  #:mode (wf-decl I I)
  #:contract (wf-decl env D)
  [(wf-decl env (: l T))
   (wf-type env T)])

(define-judgment-form dot
  #:mode (wf-type I I)
  #:contract (wf-type env T)
  [(wf-type env Top)]
  [(wf-type env (-> T_1 T_2))
   (wf-type env T_1)
   (wf-type env T_2)]
  [(wf-type (Gamma store) (refinement Tc z Dl ...))
   (where env_extended ((gamma-extend Gamma z (refinement Tc z Dl ...)) store))
   (wf-decl env_extended Dl) ...])

(define (sort-decls ds)
  (sort ds #:key (lambda (x) (symbol->string (cadr (cadr x)))) string<?))
(define-metafunction dot
  sorted-decls : (D ...) -> (D ...)
  [(sorted-decls (D_1 ...)) ,(sort-decls (term (D_1 ...)))])
  
(define (sort-assigns as)
  (sort as #:key (lambda (x) (symbol->string (cadr (car x)))) string<?))
(define-metafunction dot
  sorted-assigns : ((l vx) ...) -> ((l vx) ...)
  [(sorted-assigns ((l_1 vx_1) ...)) ,(sort-assigns (term ((l_1 vx_1) ...)))])

(define-metafunction dot
  decl-intersection : (D ...) (D ...) -> (D ...)
  [(decl-intersection (D_1 ...) (D_2 ...)) (D_1 ... D_2 ...)])

(define-metafunction dot
  membership-lookup : env e l -> T or #f
  [(membership-lookup env_1 e_1 l_1)
   T_1
   (judgment-holds (typeof env_1 e_1 T_e))
   (judgment-holds (expansion env_1 T_e (D_before ... (: l_1 T_1) D_after ...)))]
  [(membership-lookup env_1 e_1 l_1)
   #f])
                                     
(define-judgment-form dot
  #:mode (expansion I I O)
  #:contract (expansion env T (D ...))
  [(expansion env Top ())]
  [(expansion env (-> S T) ())]
  [(expansion env (refinement T_1 z_1 Dl_1 ...) (decl-intersection (Dl_1 ...) (D_2 ...)))
   (expansion env T_1 (D_2 ...))])
  
(define-judgment-form dot
  #:mode (subdecl I I I)
  #:contract (subdecl env D D)
  [(subdecl env (: l_1 T_1) (: l_1 T_2))
   (subtype env T_1 T_2)])

(define-judgment-form dot
  #:mode (subdecls I I I)
  #:contract (subdecls env (D ...) (D ...))
  [(subdecls env (D_first D_rest ...) ())]
  [(subdecls env ((: l T_1) D_1 ...) ((: l T_2) D_2 ...))
   (subtype env T_1 T_2)
   (subdecls env (D_1 ...) (D_2 ...))]
  [(subdecls env ((: l_1 T_1) D_1 ...) ((: (side-condition l_2 (not (equal? (term l_1) (term l_2)))) T_2) D_2 ...))
   (subdecls env (D_1 ...) (D_2 ...))])

(define-judgment-form dot
  #:mode (subtype I I I)
  #:contract (subtype env S T)
  [(subtype env T T)]
  [(subtype env (side-condition T (not (equal? (term T) (term Top)))) Top)]
  [(subtype env (-> S_1 S_2) (-> T_1 T_2))
   (subtype env T_1 S_1)
   (subtype env S_2 T_2)]
  [(subtype env S (side-condition (refinement T z DLt ... Dl ...) (not (equal? (term S) (term (refinement T z DLt ... Dl ...))))))
   (subtype env S T)
   (expansion env S (Dl_s ...))
   (expansion env T (Dl_t ...))
   (subdecls env (sorted-decls (Dl_s ...)) (sorted-decls (Dl_t ...)))]
  [(subtype env (refinement T_1 z DLt ... Dl ...) (side-condition T_2 (not (equal? (term T_2) (term Top)))))
   (subtype env T_1 T_2)])

(define-judgment-form dot
  #:mode (typeof I I O)
  #:contract (typeof env e T)
  [(typeof (Gamma store) x T)
   (where T (gamma-lookup Gamma x))
   (found T #t)]
  [(typeof (Gamma store) (valnew (x (Tc (l vx) ...)) e) T)
   (wf-type (Gamma store) Tc)
   (expansion (Gamma store) Tc (Dl ...))
   (where ((l_s vx_s) ...) (sorted-assigns ((l vx) ...)))
   (where ((: l_s V_d) ...) (sorted-decls (Dl ...)))
   (typeof ((gamma-extend Gamma x Tc) store) vx_s V_s) ...
   (subtype ((gamma-extend Gamma x Tc) store) V_s V_d) ...
   (typeof ((gamma-extend Gamma x Tc) store) e T)]
  [(typeof (Gamma store) (location i) Tc)
   (where c (store-lookup store i))
   (found c #t)
   (where Tc (constructor-type-lookup c))]
  [(typeof (Gamma store) (λ (x S) e) (-> S T))
   (wf-type (Gamma store) S)
   (typeof ((gamma-extend Gamma x S) store) e T)]
  [(typeof env (e_1 e_2) T)
   (typeof env e_1 (-> S T))
   (typeof env e_2 T_2)
   (subtype env T_2 S)]
  [(typeof env (sel e_1 l_1) T_1)
   (where T_1 (membership-lookup env e_1 l_1))
   (found T_1 #t)])

(define (typecheck env e)
  (match (judgment-holds (typeof ,env ,e T) T)
    [(list) #f]
    [(list T) T]
    [_ (error 'typecheck
              "multiple typing derivations for term ~a in environment ~a"
              e env)]))

(typecheck (term (() ())) (term (valnew (u (Top)) u)))
(typecheck (term (() ())) (term (valnew (o (Top)) (valnew (o (Top)) o))))
(typecheck (term (() ())) (term (λ (x Top) x)))
(typecheck (term (() ())) (term ((λ (x Top) x) (λ (x Top) x))))
(typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l)))))

(define (progress e)
  (if (typecheck (term (() ())) e)
      (begin
        ;(printf "progress: trying ~a\n" e)
        (or (value? e)
            (single-step? e)))
      #t))

(define (preservation e)
  (if (and (typecheck (term (() ())) e) (single-step? e))
      (begin
        ;(printf "preservation: trying ~a\n" e)
        (let loop ((e e) (store (term ())) (t (typecheck (term (() ())) e)))
          (or (and (value? e) t)
              (match (steps-to store e)
                [(list store_to e_to)
                 (and (judgment-holds (subtype (() ,store_to) ,(typecheck (term (() ,store_to)) e_to) ,t))
                      (loop e_to store_to (typecheck (term (() ,store_to)) e_to)))]
                [_ (error 'preservation "expect match")]))))
      #t))

(preservation (term (valnew (u (Top)) u)))
(preservation (term ((λ (x Top) x) (λ (x Top) x))))
(preservation (term (valnew (u ((refinement Top u (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l)))))

(define-metafunction dot
  vars : any -> (x ...)
  [(vars (label-value variable_1)) ()]
  [(vars (label-class variable_1)) ()]
  [(vars (label-abstract-type variable_1)) ()]
  [(vars x_1) (x_1)]
  [(vars (any_1 ...)) ,(apply append (term ((vars any_1) ...)))]
  [(vars any_1) ()])

(define (close e)
  (let loop ((e e) (vs (term (vars ,e))))
    (if (null? vs)
        e
        (loop (term (subst ,e ,(car vs) (λ (x Top) x))) (cdr vs)))))

(define (pick-random lst def)
  (if (null? lst)
      def
      (list-ref lst (random (length lst)))))

(define-metafunction dot
  massage : (x ...) (l ...) any -> any
  [(massage (x_b ...) (l_b ...) (valnew (x_1 (Tc_1 (l_1 vx_1) ...)) e_1))
   (valnew (x_1 (Tc_1 (l_e ,(pick-random (term (x_b ... x_1)) (term (λ (x Top) x)))) ...)) (massage (x_b ... x_1) (l_b ... l_e ...) e_1))
   (judgment-holds (expansion (() ()) Tc_1 ((: l_e T_le) ...)))]
  [(massage (x_b ...) (l_b ...) (λ (x_1 T_1) e_2))
   (λ (x_1 T_1) (massage (x_b ... x_1) (l_b ...) e_2))]
  [(massage (x_b ...) (l_b ...) (sel e_1 l_1)) (sel (massage (x_b ...) (l_b ...) e_1) ,(pick-random (term (l_b ...)) (term l_1)))]
  [(massage (x_b ...) (l_b ...) x_1)
   ,(let ((res (pick-random (term (x_b ... )) (term (λ (x Top) x)))))
      (if (or (null? (term (l_b ...))) (= 0 (random 1)))
          res
          (term (sel ,res ,(pick-random (term (l_b ...)) #f)))))]
  [(massage (x_b ...) (l_b ...) (refinement Tc_1 z_1 D_1 ...)) (refinement Tc_1 z_1 D_1 ...)]
  [(massage (x_b ...) (l_b ...) (any_1 ...)) ((massage (x_b ...) (l_b ...) any_1) ...)]
  [(massage (x_b ...) (l_b ...) any_1) any_1])

(define (prepare e)
  (term (massage () () ,e)))

(redex-check mini-dot e (progress (term e)) #:prepare close)
(redex-check mini-dot e (preservation (term e)) #:prepare close)

(let ([R (reduction-relation mini-dot
  [--> (valnew (x ((refinement Top z (: l_1 Top) Dl ...) (l vx) ...)) e) (valnew (x ((refinement Top z (: l_1 Top) Dl ...) (l vx) ...)) e)])])
  (redex-check mini-dot e (progress (term e)) #:source R #:prepare prepare)
  (redex-check mini-dot e (preservation (term e)) #:source R #:prepare prepare))