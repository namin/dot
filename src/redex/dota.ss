#lang racket
(require redex)
(provide (all-defined-out))

(define-language dot
  ((x y z) variable-not-otherwise-mentioned)
  (l (cv variable-not-otherwise-mentioned))
  (m (cm variable-not-otherwise-mentioned))
  (i natural)
  (loc (location i))
  (v loc)
  (vx v x)
  (b (new c) (snd p m p) (exe v m s))
  (s p (val x = b in s))
  (p x loc (sel p l))
  (c (Tc (l vx) ... (m x s) ...))
  (Gamma ([x T] ...))
  (store (c ...))
  (env (Gamma store))
  (Lt Lc La)
  (Lc (cc variable-not-otherwise-mentioned))
  (La (ca variable-not-otherwise-mentioned))
  ((S T U V W) (sel p Lt) (rfn T z DLt ... Dl ... Dm ...) (T ∧ T) (T ∨ T) Top Bot)
  ((Sc Tc) (sel p Lc) (rfn Tc z DLt ... Dl ... Dm ...) (Tc ∧ Tc) Top)
  (DLt (: Lt S U))
  (Dl (: l T))
  (Dm (: m S U))
  (D DLt Dl Dm)
  (bool #t #f)
  (DLm DLt Dm)
  (Lm Lt m)
  (Lany Lt l m)
  (Ds ((DLt ...) (Dl ...) (Dm ...))))

(define-metafunction dot
  intersection : T T -> T
  [(intersection T_1 Bot) Bot]
  [(intersection Bot T_2) Bot]
  [(intersection T_1 Top) T_1]
  [(intersection Top T_2) T_2]
  [(intersection T_1 T_2) (T_1 ∧ T_2)])

(define-metafunction dot
  union : T T -> T
  [(union T_1 Bot) T_1]
  [(union Bot T_2) T_2]
  [(union T_1 Top) Top]
  [(union Top T_2) Top]
  [(union T_1 T_2) (T_1 ∨ T_2)])

(define-metafunction dot
  subst : any x any -> any
  ;; 1. x_1 bound
  [(subst (m_1 x_1 any_1) x_1 any_2)
   (m_1 x_1 any_1)]
  [(subst (val x_1 = b_1 in any_1) x_1 any_2)
   (val x_1 = b_1 in any_1)]
  [(subst (rfn T_1 x_1 D_1 ...) x_1 any_2)
   (rfn (subst T_1 x_1 any_2) x_1 D_1 ...)]
  
  ;; 2. do capture avoiding substitution by generating a fresh name
  [(subst (m_1 x_1 any_1) x_2 any_2)
   (m_1 x_3
        (subst (subst-var any_1 x_1 x_3) x_2 any_2))
   (where x_3 ,(variable-not-in (term (x_2 any_1 any_2))
                                (term x_1)))]
  [(subst (val x_1 = b_1 in any_1) x_2 any_2)
   (val x_3 = (subst (subst-var b_1 x_1 x_3) x_2 any_2) in
        (subst (subst-var any_1 x_1 x_3) x_2 any_2))
   (where x_3 ,(variable-not-in (term (x_2 b_1 any_1 any_2))
                                (term x_1)))]
  [(subst (rfn T_1 x_1 D_1 ...) x_2 any_2)
   (rfn (subst T_1 x_2 any_2) x_3 (subst (subst-var D_1 x_1 x_3) x_2 any_2) ...)
   (where x_3 ,(variable-not-in (term (D_1 ... x_2 any_2))
                                (term x_1)))]

  ;; do not treat labels as variables
  [(subst (cv variable_1) x_1 any_1) (cv variable_1)]
  [(subst (cm variable_1) x_1 any_1) (cm variable_1)]
  [(subst (cc variable_1) x_1 any_1) (cc variable_1)]
  [(subst (ca variable_1) x_1 any_1) (ca variable_1)]

  ;; 3. replace x_1 with any_1
  [(subst x_1 x_1 any_1) any_1]
  
  ;; the last two cases just recur on the tree structure of the term
  [(subst (any_2 ...) x_1 any_1)
   ((subst any_2 x_1 any_1) ...)]
  [(subst any_2 x_1 any_1) any_2])

(define-metafunction dot
  subst-var : any x x -> any
  [(subst-var (cv variable_1) x_1 x_2) (cv variable_1)]
  [(subst-var (cm variable_1) x_1 x_2) (cm variable_1)]
  [(subst-var (cc variable_1) x_1 x_2) (cc variable_1)]
  [(subst-var (ca variable_1) x_1 x_2) (ca variable_1)]

  [(subst-var (any_1 ...) x_1 x_2)
   ((subst-var any_1 x_1 x_2) ...)]
  [(subst-var x_1 x_1 x_2) x_2]
  [(subst-var any_1 x_1 x_2) any_1])

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
  value-label-lookup : c l -> vx or #f
  [(value-label-lookup (Tc (l_req vx_req) (l_after vx_after) ... (m_ignore x_ignore s_ignore) ...) l_req) vx_req]
  [(value-label-lookup (Tc (l_first vx_first) (l_after vx_after) ... (m_ignore x_ignore s_ignore) ...) l_req)
   (value-label-lookup (Tc (l_after vx_after) ...) l_req)]
  [(value-label-lookup (Tc (m_ignore x_ignore s_ignore) ...) l_req) #f])

(define-metafunction dot
  method-label-lookup : c m -> (x s) or #f
  [(method-label-lookup (Tc (l_ignore vx_ignore) ... (m_req x_req s_req) (m_after x_after s_after) ...) m_req) (x_req s_req)]
  [(method-label-lookup (Tc (l_ignore vx_ignore) ... (m_first x_first s_first) (m_after x_after s_after) ...) m_req)
   (method-label-lookup (Tc (m_after x_after s_after) ...) m_req)]
  [(method-label-lookup (Tc (l_ignore vx_ignore) ...) m_req) #f])

(define-judgment-form dot
  #:mode (found I O)
  #:contract (found any bool)
  [(found #f #f)]
  [(found (side-condition any (term any)) #t)])

(define-metafunction dot
  fn : any x -> bool
  ;; x_1 bound
  [(fn (m_1 x_1 any_1) x_1) #f]
  [(fn (val x_1 = new c_1 in any_1) x_1) #f]
  [(fn (rfn T_1 x_1 D_1 ...) x_1) (fn T_1 x_1)]

  ;; x_1 free
  [(fn x_1 x_1) #t]

  ;; do not treat labels as variables
  [(fn Lany x) #f]

  ;; the last two cases just recur on the tree structure of the term
  [(fn (any_1 ...) x_1)
   ,(ormap (lambda (x) x) (term ((fn any_1 x_1) ...)))]
  [(fn any_1 x_1) #f])

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
   (wf-type env T)]
  [(wf-decl env (: Lm S U))
   (wf-type env S)
   (wf-type env U)])

(define-metafunction dot
  is_wfe-type : env T -> bool
  [(is_wfe-type env T) #t
   (side-condition (term (is_wf-type env T)))
   (judgment-holds (expansion env z T ((DLt ...) (Dl ...) (Dm ...))))]
  [(is_wfe-type env T) #f])

(define-metafunction dot
  is_wf-type : env T -> bool
  [(is_wf-type env Top) #t]
  [(is_wf-type env (-> T_1 T_2)) #t
   (side-condition (term (is_wf-type env T_1)))
   (side-condition (term (is_wf-type env T_2)))]
  [(is_wf-type (Gamma store) (rfn T z D ...)) #t
   (side-condition (term (is_wf-type (Gamma store) T)))
   (where env_extended ((gamma-extend Gamma z (rfn T z D ...)) store))
   (side-condition (andmap (lambda (d) (judgment-holds (wf-decl env_extended ,d))) (term (D ...))))]
  [(is_wf-type env (sel p Lt)) #t
   (where any_bound (membership-type-lookup env p Lt))
   (judgment-holds (found any_bound #t))]
  [(is_wf-type env (T_1 ∧ T_2)) #t
   (side-condition (term (is_wf-type env T_1)))
   (side-condition (term (is_wf-type env T_2)))]
  [(is_wf-type env (T_1 ∨ T_2)) #t
   (side-condition (term (is_wf-type env T_1)))
   (side-condition (term (is_wf-type env T_2)))]
  [(is_wf-type env Bot) #t]
  [(is_wf-type env T) #f])

(define-judgment-form dot
  #:mode (wfe-type I I)
  #:contract (wfe-type env T)
  [(wfe-type env T) (found (is_wfe-type env T) #t)])

(define-judgment-form dot
  #:mode (wf-type I I)
  #:contract (wf-type env T)
  [(wf-type env T) (found (is_wf-type env T) #t)])
 
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
  sorted-method-assigns : ((m x s) ...) -> ((m x s) ...)
  [(sorted-method-assigns ((m_1 x_1 s_1) ...)) ,(sort-assigns (term ((m_1 x_1 s_1) ...)))])

(define-metafunction dot
  decl-intersection : (D ...) (D ...) -> (D ...)
  [(decl-intersection ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))
   ,(cons (term (: l (T_1 ∧ T_2)))
          (term (decl-intersection (Dl_1 ...) (Dl_2 ...))))]
  [(decl-intersection ((: l T_1) Dl_1 ...) (Dl_before ... (: l T_2) Dl_2 ...))
   ,(append (term (Dl_before ...))
            (term (decl-intersection ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))))]
  [(decl-intersection (Dl_before ... (: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))
   ,(append (term (Dl_before ...))
            (term (decl-intersection ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))))]
  [(decl-intersection ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))
   ,(cons (term (: Lm (union S_1 S_2) (intersection U_1 U_2)))
          (term (decl-intersection (DLm_1 ...) (DLm_2 ...))))]
  [(decl-intersection ((: Lm S_1 U_1) DLm_1 ...) (DLm_before ... (: Lm S_2 U_2) DLm_2 ...))
   ,(append (term (DLm_before ...))
            (term (decl-intersection ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))))]
  [(decl-intersection (DLm_before ... (: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))
   ,(append (term (DLm_before ...))
            (term (decl-intersection ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))))]
  [(decl-intersection (Dl_1 ...) (Dl_2 ...))
   (Dl_1 ... Dl_2 ...)]
  [(decl-intersection (DLm_1 ...) (DLm_2 ...))
   (DLm_1 ... DLm_2 ...)])

(define-metafunction dot
  decl-union : (D ...) (D ...) -> (D ...)
  [(decl-union ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))
   ,(cons (term (: l (T_1 ∨ T_2)))
          (term (decl-union (Dl_1 ...) (Dl_2 ...))))]
  [(decl-union ((: l T_1) Dl_1 ...) (Dl_before ... (: l T_2) Dl_2 ...))
   (decl-union ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))]
  [(decl-union (Dl_before ... (: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))
   (decl-union ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))]
  [(decl-union ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))
   ,(cons (term (: Lm (intersection S_1 S_2) (union U_1 U_2)))
          (term (decl-union (DLm_1 ...) (DLm_2 ...))))]
  [(decl-union ((: Lm S_1 U_1) DLm_1 ...) (DLm_before ... (: Lm S_2 U_2) DLm_2 ...))
   (decl-union ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))]
  [(decl-union (DLm_before ... (: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))
   (decl-union ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))]
  [(decl-union (Dl_1 ...) (Dl_2 ...))
   ()]
  [(decl-union (DLm_1 ...) (DLm_2 ...))
   ()])

(define-metafunction dot
  membership-type-lookup : env p Lt -> (S U) or #f
  [(membership-type-lookup env_1 p_1 Lt_1)
   (subst (S_1 U_1) z_1 p_1)
   (judgment-holds (typeof env_1 p_1 T_e))
   (where z_1 ,(variable-not-in (term (env_1 p_1 T_e)) 'z))
   (judgment-holds (expansion env_1 z_1 T_e ((D_before ... (: Lt_1 S_1 U_1) D_after ...) (Dl ...) (Dm ...))))]
  [(membership-type-lookup env_1 p_1 Lt_1)
   (Top Bot)
   (judgment-holds (typeof env_1 p_1 T_e))
   (judgment-holds (subtype env_1 T_e Bot))]  
  [(membership-type-lookup env_1 p_1 Lt_1)
   #f])

(define-metafunction dot
  membership-value-lookup : env p l -> T or #f
  [(membership-value-lookup env_1 p_1 l_1)
   (subst T_1 z_1 p_1)
   (where z_1 ,(variable-not-in (term (env_1 p_1 T_e)) 'z))
   (judgment-holds (typeof env_1 p_1 T_e))
   (judgment-holds (expansion env_1 z_1 T_e ((DLt ...) (D_before ... (: l_1 T_1) D_after ...) (Dm ...))))]
  [(membership-value-lookup env_1 p_1 l_1)
   Bot
   (judgment-holds (typeof env_1 p_1 T_e))
   (judgment-holds (subtype env_1 T_e Bot))]
  [(membership-value-lookup env_1 p_1 l_1)
   #f])

(define-metafunction dot
  membership-method-lookup : env p m -> (S U) or #f
  [(membership-method-lookup env_1 p_1 m_1)
   (subst (S_1 U_1) z_1 p_1)
   (where z_1 ,(variable-not-in (term (env_1 p_1 T_e)) 'z))
   (judgment-holds (typeof env_1 p_1 T_e))
   (judgment-holds (expansion env_1 z_1 T_e ((DLt ...) (Dl ...) (D_before ... (: m_1 S_1 U_1) D_after ...))))]
  [(membership-method-lookup env_1 p_1 m_1)
   (Top Bot)
   (judgment-holds (typeof env_1 p_1 T_e))
   (judgment-holds (subtype env_1 T_e Bot))]
  [(membership-method-lookup env_1 p_1 m_1)
   #f])

(define max-iter 100)

(define-metafunction dot
  member : any (any ...) -> #t or #f
  [(member any_1 (any_0 ... any_1 any_2 ...)) #t]
  [(member any_1 (any_0 ...)) #f])

(define-judgment-form dot
  #:mode (expansion-fix I I I I I I O)
  #:contract (expansion-fix (sel p Lt) Ds (((sel p Lt) Ds) ...) env z T Ds)
  [(expansion-fix (sel p_w Lt_w) Ds_w (((sel p_0 Lt_0) Ds_0) ...) env z T Ds_w)
   (expansion-iter (((sel p_w Lt_w) Ds_w) ((sel p_0 Lt_0) Ds_0) ...) env z T Ds_w)]
  [(expansion-fix (sel p_w Lt_w) Ds_w (((sel p_0 Lt_0) Ds_0) ...) env z T Ds_o)
   (expansion-iter (((sel p_w Lt_w) Ds_w) ((sel p_0 Lt_0) Ds_0) ...) env z T Ds_a)
   (found (member Ds_a (Ds_w)) #f)
   (expansion-fix (sel p_w Lt_w) Ds_a (((sel p_0 Lt_0) Ds_0) ...) env z T Ds_o)])

(define-judgment-form dot
  #:mode (expansion-iter I I I I O)
  #:contract (expansion-iter (((sel p Lt) Ds) ...) env z T Ds)
  [(expansion-iter (((sel p Lt) Ds) ...) env z Top (() () ()))]
  [(expansion-iter (((sel p Lt) Ds) ...) env z_1 (rfn T_1 z_2 DLt_1 ... Dl_1 ... Dm_1 ...)
                   ((decl-intersection (sorted-decls (subst (DLt_1 ...) z_2 z_1)) (sorted-decls (DLt_2 ...)))
                    (decl-intersection (sorted-decls (subst (Dl_1 ...) z_2 z_1)) (sorted-decls (Dl_2 ...)))
                    (decl-intersection (sorted-decls (subst (Dm_1  ...) z_2 z_1)) (sorted-decls (Dm_2  ...)))))
   (expansion-iter (((sel p Lt) Ds) ...) env z_1 T_1 ((DLt_2 ...) (Dl_2 ...) (Dm_2 ...)))]
  [(expansion-iter (((sel p_0 Lt_0) Ds_0) ...) env z (T_1 ∧ T_2)
                   ((decl-intersection (sorted-decls (DLt_1 ...)) (sorted-decls (DLt_2 ...)))
                    (decl-intersection (sorted-decls (Dl_1  ...)) (sorted-decls (Dl_2  ...)))
                    (decl-intersection (sorted-decls (Dm_1  ...)) (sorted-decls (Dm_2  ...)))))
   (expansion-iter (((sel p_0 Lt_0) Ds_0) ...) env z T_1 ((DLt_1 ...) (Dl_1 ...) (Dm_1 ...)))
   (expansion-iter (((sel p_0 Lt_0) Ds_0) ...) env z T_2 ((DLt_2 ...) (Dl_2 ...) (Dm_2 ...)))]
  [(expansion-iter (((sel p_0 Lt_0) Ds_0) ...) env z (T_1 ∨ T_2)
                   ((decl-union (sorted-decls (DLt_1 ...)) (sorted-decls (DLt_2 ...)))
                    (decl-union (sorted-decls (Dl_1  ...)) (sorted-decls (Dl_2  ...)))
                    (decl-union (sorted-decls (Dm_1  ...)) (sorted-decls (Dm_2  ...)))))
   (expansion-iter (((sel p_0 Lt_0) Ds_0) ...) env z T_1 ((DLt_1 ...) (Dl_1 ...) (Dm_1 ...)))
   (expansion-iter (((sel p_0 Lt_0) Ds_0) ...) env z T_2 ((DLt_2 ...) (Dl_2 ...) (Dm_2 ...)))]
  [(expansion-iter (((sel p_0 Lt_0) Ds_0) ... ((sel p_w Lt_w) Ds_w) ((sel p_2 Lt_2) Ds_2) ...) env z (sel p_w Lt_w) Ds_w)]
  [(expansion-iter (((sel p_0 Lt_0) Ds_0) ...) env z (sel p_w Lt_w) Ds_u)
   (found (member (sel p_w Lt_w) ((sel p_0 Lt_0) ...)) #f)
   (where any_bound (membership-type-lookup env p_w Lt_w))
   (found any_bound #t)
   (where (S_p U_p) any_bound)
   (expansion-fix (sel p_w Lt_w) (()()()) (((sel p_0 Lt_0) Ds_0) ...) env z U_p Ds_u)]
  [(expansion-iter (((sel p Lt) Ds) ...) env z Bot (((: (ca kludge) Top Bot)) () ()))]) ;; kludge

(define-judgment-form dot
  #:mode (expansion I I I O)
  #:contract (expansion env z T Ds)
  [(expansion env z T Ds)
   (expansion-iter () env z T Ds)])

(define-judgment-form dot
  #:mode (subdecl I I I)
  #:contract (subdecl env D D)
  [(subdecl env (: Lm_1 S_1 T_1) (: Lm_1 S_2 T_2))
   (subtype env S_2 S_1)
   (subtype env T_1 T_2)]
  [(subdecl env (: l_1 T_1) (: l_1 T_2))
   (subtype env T_1 T_2)])

(define-judgment-form dot
  #:mode (subdecls I I I)
  #:contract (subdecls env (D ...) (D ...))
  [(subdecls env (D ...) ())]
  [(subdecls env (D_1 D_rest1 ...) (D_2 D_rest2 ...))
   (subdecl env D_1 D_2)
   (subdecls env (D_rest1 ...) (D_rest2 ...))]
  [(subdecls env (D_1 D_rest1 ...) (D_2 D_rest2 ...))
   (subdecls env (D_rest1 ...) (D_2 D_rest2 ...))])

(define-judgment-form dot
  #:mode (path-red I I O)
  #:contract (path-red env p p)
  [(path-red (Gamma store) (sel (location i_1) l) (location i_2))
   (where c (store-lookup store i_1))
   (found c #t)
   (where (location i_2) (value-label-lookup c l))]
  [(path-red env (sel p_1 l) (sel p_2 l))
   (path-red env p_1 p_2)])

(define-metafunction dot
  is_subtype : ((T T) ...) env S T -> bool
  [(is_subtype ((T_a T_b) ...) env S T) #f
   (judgment-holds (found (member (S T) ((T_a T_b) ...)) #t))]
  [(is_subtype ((T_a T_b) ...) env T T) #t
   (judgment-holds (wfe-type env T))]
  [(is_subtype ((T_a T_b) ...) env T Top) #t
   (judgment-holds (wfe-type env T))]
  [(is_subtype ((T_a T_b) ...) env Bot T) #t
   (judgment-holds (wfe-type env T))]
  [(is_subtype ((T_a T_b) ...) env S (rfn T z DLt ... Dl ... Dm ...)) #t
   (judgment-holds (wfe-type env (rfn T z DLt ... Dl ... Dm ...)))
   (side-condition (term (is_subtype ((T_a T_b) ... (S (rfn T z DLt ... Dl ... Dm ...))) env S T)))
   (judgment-holds (expansion env z S ((DLt_s ...) (Dl_s ...) (Dm_s ...))))
   (where (Gamma store) env)
   (where Gamma_z (gamma-extend Gamma z S))
   (judgment-holds (subdecls (Gamma_z store) (sorted-decls (DLt_s ...)) (sorted-decls (DLt ...))))
   (judgment-holds (subdecls (Gamma_z store) (sorted-decls (Dl_s ...)) (sorted-decls (Dl ...))))
   (judgment-holds (subdecls (Gamma_z store) (sorted-decls (Dm_s ...)) (sorted-decls (Dm ...))))]
  [(is_subtype ((T_a T_b) ...) env (rfn T_1 z DLt ... Dl ... Dm ...) T_2) #t
   (judgment-holds (wfe-type env (rfn T_1 z DLt ... Dl ... Dm ...)))
   (side-condition (term (is_subtype ((T_a T_b) ... ((rfn T_1 z DLt ... Dl ... Dm ...) T_2)) env T_1 T_2)))]
  [(is_subtype ((T_a T_b) ...) env S_1 (sel p Lt)) #t
   (where any_bound (membership-type-lookup env p Lt))
   (judgment-holds (found any_bound #t))
   (where (S_p U_p) any_bound)
   (side-condition (term (is_subtype ((T_a T_b) ... (S_1 (sel p Lt))) env S_p U_p)))
   (side-condition (term (is_subtype ((T_a T_b) ... (S_1 (sel p Lt))) env S_1 S_p)))]
  [(is_subtype ((T_a T_b) ...) env (sel p Lt) U_1) #t
   (where any_bound (membership-type-lookup env p Lt))
   (judgment-holds (found any_bound #t))
   (where (S_p U_p) any_bound)
   (side-condition (term (is_subtype ((T_a T_b) ... ((sel p Lt) U_1)) env S_p U_p)))
   (side-condition (term (is_subtype ((T_a T_b) ... ((sel p Lt) U_1)) env U_p U_1)))]
  [(is_subtype ((T_a T_b) ...) env T_o (T_1 ∧ T_2)) #t
   (side-condition (term (is_subtype ((T_a T_b) ... (T_o (T_1 ∧ T_2))) env T_o T_1)))
   (side-condition (term (is_subtype ((T_a T_b) ... (T_o (T_1 ∧ T_2))) env T_o T_2)))]
  [(is_subtype ((T_a T_b) ...) env (T_1 ∧ T_2) T_o) #t
   (judgment-holds (wfe-type env T_2))
   (side-condition (term (is_subtype ((T_a T_b) ... ((T_1 ∧ T_2) T_o)) env T_1 T_o)))]
  [(is_subtype ((T_a T_b) ...) env (T_1 ∧ T_2) T_o) #t
   (judgment-holds (wfe-type env T_1))
   (side-condition (term (is_subtype ((T_a T_b) ... ((T_1 ∧ T_2) T_o)) env T_2 T_o)))]
  [(is_subtype ((T_a T_b) ...) env (T_1 ∨ T_2) T_o) #t
   (side-condition (term (is_subtype ((T_a T_b) ... ((T_1 ∨ T_2) T_o)) env T_1 T_o)))
   (side-condition (term (is_subtype ((T_a T_b) ... ((T_1 ∨ T_2) T_o)) env T_2 T_o)))]
  [(is_subtype ((T_a T_b) ...) env T_o (T_1 ∨ T_2)) #t
   (judgment-holds (wfe-type env T_2))
   (side-condition (term (is_subtype ((T_a T_b) ... (T_o (T_1 ∨ T_2))) env T_o T_1)))]
  [(is_subtype ((T_a T_b) ...) env T_o (T_1 ∨ T_2)) #t
   (judgment-holds (wfe-type env T_1))
   (side-condition (term (is_subtype ((T_a T_b) ... (T_o (T_1 ∨ T_2))) env T_o T_2)))]
  [(is_subtype ((T_a T_b) ...) env T (sel p_1 Lt)) #t
   (judgment-holds (path-red env p_1 p_2))
   (judgment-holds (wfe-type env (sel p_1 Lt)))
   (side-condition (term (is_subtype ((T_a T_b) ... (T (sel p_1 Lt))) env T (sel p_2 Lt))))]
  [(is_subtype ((T_a T_b) ...) env S T) #f])

(define-judgment-form dot
  #:mode (subtype I I I)
  #:contract (subtype env S T)
  [(subtype env S T) (found (is_subtype () env S T) #t)])

(define-judgment-form dot
  #:mode (typeof I I O)
  #:contract (typeof env p T)
  [(typeof (Gamma store) x T)
   (where T (gamma-lookup Gamma x))
   (found T #t)]
  [(typeof (Gamma store) (location i) Tc)
   (where c (store-lookup store i))
   (found c #t)
   (where Tc (constructor-type-lookup c))]
  [(typeof env (sel p_1 l_1) T_1)
   (where T_1 (membership-value-lookup env p_1 l_1))
   (found T_1 #t)])

(define (subtyping-transitive env s t u)
  (if (and (judgment-holds (wfe-type ,env ,s)) (judgment-holds (wfe-type ,env ,t)) (judgment-holds (wfe-type ,env ,u))
           (judgment-holds (subtype ,env ,s ,t)) (judgment-holds (subtype ,env ,t ,u)))
      (begin
        ;(printf "trying ~a ~a ~a ~a\n" env s t u)
        (judgment-holds (subtype ,env ,s ,u)))
      #t))
