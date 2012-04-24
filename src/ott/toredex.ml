open Dot

let rec
toredex_tm t = match t with
  | (Tm_var x) -> x
  | (Tm_new (x,Constr_any(tyTc, lst),t)) ->
    "(valnew ("^x^" ("^(toredex_tp tyTc)^" "^(String.concat " " (List.map (fun (li,xi,tyTi,ti) -> "("^(toredex_vlabel li)^" ("^xi^" "^(toredex_tp tyTi)^")"^(toredex_tm ti)^")") lst))^")) "^(toredex_tm t)^")"
  | (Tm_sel (t,l,t')) ->
    "("^(toredex_tm t)^" "^(toredex_vlabel l)^" "^(toredex_tm t')^")"
  | (Tm_lam (x,tyT,tyT',t)) ->
    "(fun ("^x^" "^(toredex_tp tyT)^") "^(toredex_tp tyT')^" "^(toredex_tm t)^")"
  | (Tm_app (t,t')) ->
    "(app "^(toredex_tm t)^" "^(toredex_tm t')^")"
  | (Tm_cast (tyT,t)) ->
    "(cast "^(toredex_tp tyT)^" "^(toredex_tm t)^")"
and
toredex_tp ty = match ty with
  | (Tp_tsel (p,tL)) ->
    "(sel "^(toredex_tm p)^" "^(toredex_tlabel tL)^")"
  | (Tp_rfn (tyT,z,Decls_seq(seqD))) ->
    "(refinement "^(toredex_tp tyT)^" "^z^" "^(String.concat " " (List.map toredex_decl seqD))^")"
  | (Tp_and (tyT,tyT')) ->
    "(intersection "^(toredex_tp tyT)^" "^(toredex_tp tyT')^")"
  | (Tp_or (tyT,tyT')) ->
    "(union "^(toredex_tp tyT)^" "^(toredex_tp tyT')^")"
  | Tp_top -> "Top"
  | Tp_bot -> "Bottom"
and
toredex_decl aD = match aD with
  | (Decl_tp (tL,tyS,tyU)) ->
    "(: "^(toredex_tlabel tL)^" "^(toredex_tp tyS)^" "^(toredex_tp tyU)^")"
  | (Decl_tm (l,tyS,tyT)) ->
    "(: "^(toredex_vlabel l)^" "^(toredex_tp tyS)^" "^(toredex_tp tyT)^")"
and
toredex_vlabel l = match l with
  | (Vlabel_any label) -> "(label-value "^label^")"
and
toredex_tlabel tL = match tL with
  | (Tlabel_class label) -> "(label-class "^label^")"
  | (Tlabel_abstract label) -> "(label-abstract-type "^label^")"

let toredex_preservation t = "(preservation (term "^(toredex_tm t)^"))\n"
