(* Intersection Types *)

From Stdlib Require Import Bool PeanoNat Lia CMorphisms.
From OLlibs Require Import Logic_Datatypes_more funtheory List_more SubListT dectype.
From InterPT Require lformulas.
Import EqNotations LogicNotations.
Export ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * Definition *)
(* if [Atom] is in [Set] then proof types as well and then setoid_rewriting has troubles *)
Definition Atom : Type := nat.

Inductive form := var (_ : Atom) | omega | inter (_ _ : form) | arrow (_ _ : form).
Notation Ω := omega.
Infix "∩" := inter (at level 35).
Infix "→" := arrow (right associativity, at level 39).
Coercion var : Atom >-> form.


(** * Decidable Equality *)
Scheme Equality for form.
Definition form_dectype := se_dectype form_beq internal_form_dec_bl internal_form_dec_lb.


(** * Size *)
Fixpoint fsize a := S
  match a with
  | var _ | Ω => 0
  | c ∩ d | c → d => fsize c + fsize d
  end.


(** * Arrow Lists *)

Notation "⟦ l , a ⟧" := (fold_right arrow a l) (format "⟦ l ,  a ⟧").

Lemma list2form_last l a b : ⟦l · b, a⟧ = ⟦l, b → a⟧.
Proof. apply fold_right_app. Qed.


(** * Formula decomposition *)

(* maps a formula to a big intersection (list) of pairs of function arguments (list) and rightmost atom *)
Fixpoint form_decomposition a :=
  match a with
  | var x => [([], x)]
  | Ω => []
  | a ∩ b => form_decomposition a ++ form_decomposition b
  | a → b => map (fun '(t, h) => (a :: t, h)) (form_decomposition b)
  end.

Lemma form_decomposition_list t h : form_decomposition ⟦t, var h⟧ = [(t, h)].
Proof. induction t as [|a t IH] in h |- *; [ | cbn; rewrite IH ]; reflexivity. Qed.

Lemma form_decomposition_fsize a :
  ForallT (fun '(t, _) => ForallT (fun d => fsize d < fsize a) t) (form_decomposition a).
Proof.
induction a as [ x | | a1 H1 a2 H2 | a1 H1 a2 H2 ]; cbn.
- do 2 constructor.
- constructor.
- apply ForallT_app.
  + refine (ForallT_arrow _ _ H1).
    intros (t, h).
    clear. induction t; intro H; constructor; inversion H.
    * lia.
    * apply IHt. assumption.
  + refine (ForallT_arrow _ _ H2).
    intros (t, h).
    clear. induction t; intro H; constructor; inversion H.
    * lia.
    * apply IHt. assumption.
- induction H2; constructor.
  + destruct x. constructor.
    * lia.
    * refine (ForallT_arrow _ _ p).
      intro. lia.
  + assumption.
Qed.

Definition form_recomposition s := fold_right_unit inter Ω (map (fun '(t, h) => ⟦t, var h⟧) s).

Lemma simpl_form_recomposition t h p s :
  form_recomposition ((t, h) :: p :: s) = ⟦t, h⟧ ∩ (form_recomposition (p :: s)).
Proof. reflexivity. Qed.

Lemma form_recomposition_list t h : form_recomposition [(t, h)] = ⟦t, h⟧.
Proof. destruct t; reflexivity. Qed.

Lemma form_derecomposition s : form_decomposition (form_recomposition s) = s.
Proof.
induction s as [ | (t, h) [ | p s ] IH ]; [ reflexivity | .. ].
- apply form_decomposition_list.
- rewrite simpl_form_recomposition. simpl form_decomposition. rewrite IH, form_decomposition_list. reflexivity.
Qed.

(** ** Formula hereditary decomposition *)

Inductive hdcp_tree :=
| hdcmp_constr : list (list hdcp_tree * Atom) -> hdcp_tree.

Fixpoint hrect P (IH : forall l, ForallT (fun '(z, _) => ForallT P z) l -> P (hdcmp_constr l)) s : P s :=
match s with
| hdcmp_constr l => IH _ ((fix hrect_list l0 : ForallT (fun '(z, _) => ForallT P z) l0 :=
                             match l0 with
                             | [] => ForallT_nil _
                             | (t, h) :: l' => ForallT_cons _
                                  ((fix hrect_int t0 : (fun '(z, _) => ForallT P z) (t0, h) :=
                                      match t0 with
                                      | [] => ForallT_nil _
                                      | a :: u => ForallT_cons a (hrect P IH a) (hrect_int u)
                                     end) t) (hrect_list l')
                             end) l)
end.

Fixpoint hdcp_size s := S
match s with hdcmp_constr l => list_sum ((map (fun '(t, _) => list_sum (map hdcp_size t)) l)) end.

Notation "s1 +++ s2" := (hdcmp_constr (match s1 with
                                       | hdcmp_constr l1 => match s2 with
                                                            | hdcmp_constr l2 => l1 ++ l2
                                                            end
                                       end)) (at level 60).
Notation "s1 ::: s2" := (hdcmp_constr (match s2 with
                                       | hdcmp_constr l2 => map (fun '(t, h) => (s1 :: t, h)) l2
                                       end)) (at level 60).

Fixpoint form_hdecomposition a :=
match a with
| var x => hdcmp_constr [([], x)]
| Ω => hdcmp_constr []
| a ∩ b => form_hdecomposition a +++ form_hdecomposition b
| a → b => form_hdecomposition a ::: form_hdecomposition b
end.

Lemma simpl_form_hdecomposition_inter a b :
  form_hdecomposition (a ∩ b) = form_hdecomposition a +++ form_hdecomposition b.
Proof. reflexivity. Qed.

Lemma form_hdecomposition_decomposition a :
form_hdecomposition a = hdcmp_constr (map (fun '(t, h) => (map form_hdecomposition t, h)) (form_decomposition a)).
Proof.
induction a as [ x | | a1 IH1 a2 IH2 | a1 IH1 a2 IH2 ]; cbn; try now repeat constructor.
- rewrite IH1, IH2, map_app. reflexivity.
- rewrite IH2, !map_map.
  f_equal. apply map_ext. intros (t, h). reflexivity.
Qed.

Lemma form_hdecomposition_list t h :
  form_hdecomposition ⟦t, var h⟧ = hdcmp_constr [(map form_hdecomposition t, h)].
Proof. induction t as [|a t IH] in h |- *; [ | cbn; rewrite IH ]; reflexivity. Qed.

Fixpoint form_hrecomposition s :=
match s with
| hdcmp_constr l => fold_right_unit inter Ω (map (fun '(t, h) => ⟦map form_hrecomposition t, var h⟧) l)
end.

Lemma simpl_form_hrecomposition t h p s :
  form_hrecomposition (hdcmp_constr ((t, h) :: p :: s)) =
  ⟦map form_hrecomposition t, h⟧ ∩ (form_hrecomposition (hdcmp_constr (p :: s))).
Proof. reflexivity. Qed.

Lemma form_hrecomposition_recomposition_list l :
form_hrecomposition (hdcmp_constr l) = form_recomposition (map (fun '(t, h) => (map form_hrecomposition t, h)) l).
Proof. induction l as [ | (t1, h1) [ | (t2, h2) l ] IH ]; cbn; [ reflexivity .. | f_equal; assumption ]. Qed.

Lemma form_hrecomposition_recomposition s :
  form_hrecomposition s =
  form_recomposition (map (fun '(t, h) => (map form_hrecomposition t, h)) match s with hdcmp_constr l => l end).
Proof. destruct s. apply form_hrecomposition_recomposition_list. Qed.

Lemma form_hderecomposition s : form_hdecomposition (form_hrecomposition s) = s.
Proof.
induction s as [[ | (t, h) [ | (t', h') s ] ] IH ] using hrect.
- reflexivity.
- cbn. rewrite form_hdecomposition_list.
  f_equal. f_equal. f_equal.
  inversion_clear IH.
  clear - X. induction t in X |- *; [ reflexivity | ]. inversion_clear X.
  cbn. f_equal.
  + assumption.
  + apply IHt. assumption.
- remember ((t, h) :: (t', h') :: s) as l. clear - IH.
  induction l as [ | (t, h) l IHl ] in IH |- *.
  + reflexivity.
  + inversion_clear IH.
    assert (map form_hdecomposition (map form_hrecomposition t) = t) as Ht.
    { clear - X. induction t in X |- *; [ reflexivity | ]. inversion_clear X.
      cbn. f_equal.
      - assumption.
      - apply IHt. assumption. }
    destruct l as [ | (t', h') l ].
    * cbn. rewrite form_hdecomposition_list, Ht. reflexivity.
    * rewrite simpl_form_hrecomposition, simpl_form_hdecomposition_inter, form_hdecomposition_list, IHl, Ht.
      -- reflexivity.
      -- assumption.
Qed.

(* not structural, because of exchange of parameters, use sum of sizes for example

Fixpoint form_hdecomposition_le s1 s2 :=
  match s1, s2 with
  | hdcmp_constr l1, hdcmp_constr l2 => 
      (fix hdcmp_le_list l0 : Type :=
                       match l0 with
                       | [] => unit
                       | (t2, h) :: l' => ({ t1 & Forall2T form_hdecomposition_le t2 t1 & InT (t1, h) l1 }
                                          * (hdcmp_le_list l'))%type
                       end
      ) l2
  end.
*)


(** ** Beta and Eta Conditions *)

Definition arrow_hd (s : list (list form * Atom)) := map (fun '(x, y) => (tl x, y)) s.

Definition arrow_tl (s : list (list form * Atom)) := map (fun '(x, _) => hd Ω x) s.

Section ProofRelation.

Variable R : crelation form.

Definition beta_condition := forall s a b, ForallT (fun z => fst z <> nil) s ->
  R (form_recomposition s) (a → b) ->
  { s0 & sublistT s0 s & (ForallT (R a) (arrow_tl s0) * R (form_recomposition (arrow_hd s0)) b)%type }.

Definition eta_condition := forall a,
  { s & ForallT (fun z => fst z <> nil) s & R (form_recomposition s) a }.

Definition weak_eta_condition := forall x,
  { s & ForallT (fun z => fst z <> nil) s & R (form_recomposition s) (var x) }.

Lemma stronger_eta_condition : eta_condition -> weak_eta_condition.
Proof. intros He x. exact (He x). Qed.

Variable R_preorder : PreOrder R.
Variable R_inter_compat : forall a1 b1 a2 b2, R a1 b1 -> R a2 b2 -> R (a1 ∩ a2) (b1 ∩ b2).
Variable R_inter_assoc : forall a b c, R (a ∩ (b ∩ c)) ((a ∩ b) ∩ c).
Variable R_inter_unit_l : forall a, R a (Ω ∩ a).
Variable R_inter_unit_r : forall a, R a (a ∩ Ω).
Variable R_arrow_compat_r : forall c a b, R a b -> R (c → a) (c → b).
Variable R_arrow_omega : forall a, R Ω (a → Ω).
Variable R_arrow_inter : forall c a b, R ((c → a) ∩ (c → b)) (c → a ∩ b).

Lemma form_recomposition_inter s1 s2 :
  R (form_recomposition (s1 ++ s2)) ((form_recomposition s1) ∩ (form_recomposition s2)).
Proof using R_preorder R_inter_compat R_inter_assoc R_inter_unit_l R_inter_unit_r.
induction s1 as [ | (t, h) [ | (t1, h1) s1 ] IH ].
- apply R_inter_unit_l.
- destruct s2 as [ | (t2, h2) s2 ].
  + apply R_inter_unit_r.
  + reflexivity.
- transitivity (⟦t, h⟧ ∩ (form_recomposition ((t1, h1) :: s1) ∩ form_recomposition s2)).
  * apply R_inter_compat; [ reflexivity | assumption ].
  * apply R_inter_assoc.
Qed.

Lemma form_recomposition_arrow a s :
  R (form_recomposition (map (fun '(t, h) => (a :: t, h)) s)) (a → form_recomposition s).
Proof using R_preorder R_inter_compat R_arrow_compat_r R_arrow_omega R_arrow_inter.
induction s as [ | (t, h) [ | p s ] IH ].
- apply R_arrow_omega.
- apply R_arrow_compat_r. reflexivity.
- transitivity ((a → ⟦t, h⟧) ∩ (a → form_recomposition (p :: s))).
  + apply R_inter_compat; [ reflexivity | assumption ].
  + apply R_arrow_inter.
Qed.

Lemma form_redecomposition a : R (form_recomposition (form_decomposition a)) a.
Proof using R_preorder R_inter_compat R_inter_assoc R_inter_unit_l R_inter_unit_r
            R_arrow_compat_r R_arrow_omega R_arrow_inter.
induction a as [ x | | a1 IH1 a2 IH2 | a1 IH1 a2 IH2 ]; cbn; try now repeat constructor.
- transitivity (form_recomposition (form_decomposition a1)
              ∩ form_recomposition (form_decomposition a2)).
  + apply form_recomposition_inter.
  + apply R_inter_compat; assumption.
- transitivity (a1 → form_recomposition (form_decomposition a2)).
  + apply form_recomposition_arrow.
  + apply R_arrow_compat_r. assumption.
Qed.

Lemma weaker_eta_condition : weak_eta_condition -> eta_condition.
Proof using R_preorder R_inter_compat R_inter_assoc R_inter_unit_l R_inter_unit_r
            R_arrow_compat_r R_arrow_omega R_arrow_inter.
intros Hw a. induction a as [ x | | a IHa b IHb | a IHa b IHb ].
- apply (Hw x).
- exists nil; [ constructor | reflexivity ].
- destruct IHa as [sa HFa Ha], IHb as [sb HFb Hb].
  exists (sa ++ sb).
  + apply ForallT_app; assumption.
  + transitivity ((form_recomposition sa) ∩ (form_recomposition sb)).
    * apply form_recomposition_inter.
    * apply R_inter_compat; assumption.
- destruct IHb as [sb HFb Hb].
  exists (map (fun '(t, h) => (a :: t, h)) sb).
  + clear - HFb. induction sb as [ | (t, h) l IHl ]; [ constructor | ].
    inversion_clear HFb. constructor.
    * intros [=].
    * apply IHl. assumption.
  + transitivity (a → (form_recomposition sb)).
    * apply form_recomposition_arrow.
    * apply R_arrow_compat_r. assumption.
Qed.

Lemma form_hrecomposition_inter s1 s2 :
  R (form_hrecomposition (s1 +++ s2)) ((form_hrecomposition s1) ∩ (form_hrecomposition s2)).
Proof using R_preorder R_inter_compat R_inter_assoc R_inter_unit_l R_inter_unit_r.
destruct s1 as [l1], s2 as [l2].
induction l1 as [ | (t, h) [ | (t1, h1) l1 ] IH ].
- apply R_inter_unit_l.
- destruct l2 as [ | (t2, h2) l2 ].
  + apply R_inter_unit_r.
  + reflexivity.
- transitivity (⟦map form_hrecomposition t, h⟧ ∩ (form_hrecomposition (hdcmp_constr ((t1, h1) :: l1))
                                                   ∩ form_hrecomposition (hdcmp_constr l2))).
  * apply R_inter_compat; [ reflexivity | assumption ].
  * apply R_inter_assoc.
Qed.

Lemma form_hrecomposition_arrow s1 s2 :
  R (form_hrecomposition (s1 ::: s2)) (form_hrecomposition s1 → form_hrecomposition s2).
Proof using R_preorder R_inter_compat R_arrow_compat_r R_arrow_omega R_arrow_inter.
destruct s2 as [l2].
induction l2 as [ | (t, h) [ | p l2 ] IH ].
- apply R_arrow_omega.
- apply R_arrow_compat_r. reflexivity.
- transitivity ((form_hrecomposition s1 → ⟦map form_hrecomposition t, h⟧)
                   ∩ (form_hrecomposition s1 → form_hrecomposition (hdcmp_constr (p :: l2)))).
  + apply R_inter_compat; [ reflexivity | assumption ].
  + apply R_arrow_inter.
Qed.

Variable R_arrow_compat_cov_l : forall c a b, R a b -> R (a → c) (b → c).

Lemma form_hredecomposition a : R (form_hrecomposition (form_hdecomposition a)) a.
Proof using R_preorder R_inter_compat R_inter_assoc R_inter_unit_l R_inter_unit_r
            R_arrow_compat_r R_arrow_omega R_arrow_inter R_arrow_compat_cov_l.
induction a as [ x | | a1 IH1 a2 IH2 | a1 IH1 a2 IH2 ]; [ repeat constructor; reflexivity .. | | ].
- transitivity (form_hrecomposition (form_hdecomposition a1)
              ∩ form_hrecomposition (form_hdecomposition a2)).
  + apply form_hrecomposition_inter.
  + apply R_inter_compat; assumption.
- transitivity (form_hrecomposition (form_hdecomposition a1) → form_hrecomposition (form_hdecomposition a2)).
  + apply form_hrecomposition_arrow.
  + transitivity (form_hrecomposition (form_hdecomposition a1) → a2).
    * apply R_arrow_compat_r. assumption.
    * apply R_arrow_compat_cov_l. assumption.
Qed.

Variable R_dec : forall a b, R a b + notT (R a b).

Definition Rb a b := if R_dec a b then true else false.

Definition beta'_condition := forall s a b, ForallT (fun z => fst z <> nil) s ->
  R (form_recomposition s) (a → b) ->
  R (form_recomposition (arrow_hd (filter (fun '(z, _) => Rb a (hd Ω z)) s))) b.

Variable R_arrow_compat_l : forall c a b, R b a -> R (a → c) (b → c).
Variable R_omega : forall a : form, R a Ω.
Variable R_inter_left_1 : forall a b, R (a ∩ b) a.
Variable R_inter_left_2 : forall a b, R (a ∩ b) b.

Lemma beta'_condition_inv s a b : ForallT (fun z => fst z <> nil) s ->
  R (form_recomposition (arrow_hd (filter (fun '(z, _) => Rb a (hd Ω z)) s))) b ->
  R (form_recomposition s) (a → b).
Proof using R_preorder R_dec R_omega R_arrow_compat_l R_arrow_compat_r R_arrow_omega
            R_inter_compat R_arrow_inter R_inter_left_1 R_inter_left_2.
intro Hnil. revert a b. induction s as [ | (t, h) [ | p s ] IH ] in Hnil |- *; intros a b HR.
- cbn in *. transitivity (a → Ω).
  + apply R_arrow_omega.
  + apply R_arrow_compat_r. assumption.
- inversion_clear Hnil. cbn in H. destruct t as [ | c t ]; [ now contradiction H | cbn ].
  cbn in HR. case_eq (Rb a c); intro Hac; rewrite Hac in HR; cbn in HR.
  + transitivity (c → b).
    * apply R_arrow_compat_r. assumption.
    * apply R_arrow_compat_l. unfold Rb in Hac. destruct (R_dec a c); [ assumption | discriminate Hac ].
  + transitivity (a → Ω).
    * transitivity Ω; [ apply R_omega | apply R_arrow_omega ].
    * apply R_arrow_compat_r. assumption.
- inversion_clear Hnil. cbn in H. destruct t as [ | c t ]; [ now contradiction H | ].
  case_eq (Rb a c); intro Hac.
  + specialize (IH X a).
    replace (arrow_hd (filter (fun '(z, _) => Rb a (hd Ω z)) ((c :: t, h) :: p :: s)))
        with ((t, h) :: arrow_hd (filter (fun '(z, _) => Rb a (hd Ω z)) (p :: s))) in HR
        by (cbn; rewrite Hac; reflexivity).
    destruct (arrow_hd (filter (fun '(z, _) => Rb a (hd Ω z)) (p :: s))).
    * transitivity (c → ⟦t, h⟧).
      -- apply R_inter_left_1.
      -- transitivity (a → ⟦t, h⟧).
         ++ apply R_arrow_compat_l.
            unfold Rb in Hac. destruct (R_dec a c); [ assumption | discriminate ].
         ++ apply R_arrow_compat_r. assumption.
    * transitivity (a → (⟦t, h⟧ ∩ form_recomposition (p0 :: l))).
      -- etransitivity; [ | apply R_arrow_inter ].
         apply R_inter_compat.
         ++ simpl. apply R_arrow_compat_l.
            unfold Rb in Hac. destruct (R_dec a c); [ assumption | discriminate ].
         ++ apply IH. reflexivity.
      -- apply R_arrow_compat_r, HR.
  + transitivity (form_recomposition (p :: s)).
    * apply R_inter_left_2.
    * apply IH; [ assumption | ].
      cbn in HR. rewrite Hac in HR. assumption.
Qed.

Lemma beta_beta'_condition s a b : ForallT (fun z => fst z <> nil) s ->
  { s0 & sublistT s0 s & (ForallT (R a) (arrow_tl s0) * R (form_recomposition (arrow_hd s0)) b)%type } ->
  R (form_recomposition (arrow_hd (filter (fun '(z, _) => Rb a (hd Ω z)) s))) b.
Proof using R_preorder R_dec R_omega R_inter_compat R_inter_left_1 R_inter_left_2 R_inter_unit_r.
intros Hnil [s0 Hsub0 [HRa HRb]].
assert (sublistT s0 (filter (fun '(z, _) => Rb a (hd Ω z)) s)).
{ clear - Hnil Hsub0 HRa. induction s as [ | (t, h) s IH ] in Hnil, s0, Hsub0, HRa |- *; [ assumption | ].
  inversion_clear Hnil. destruct t as [ | c t ]; [ now contradiction H | cbn ].
  case_eq (Rb a c); intro Hac.
  - inversion Hsub0; subst.
    + constructor. apply IH; [ assumption .. | ].
      now inversion HRa.
    + constructor. apply IH; assumption.
  - inversion Hsub0; subst.
    + exfalso. inversion_clear HRa. unfold Rb in Hac. destruct (R_dec a c); [ discriminate Hac | contradiction ].
    + apply IH; assumption. }
transitivity (form_recomposition (arrow_hd s0)); [ | assumption ].
unfold arrow_hd. apply (sublistT_map (fun '(x, y) => (tl x, y))) in X.
remember (map (fun '(x, y) => (tl x, y)) s0) as t0.
remember (map (fun '(x, y) => (tl x, y)) (filter (fun '(z, _) => Rb a (hd Ω z)) s)) as t1.
clear - R_preorder R_omega R_inter_compat R_inter_left_1 R_inter_left_2 R_inter_unit_r X. induction X.
- reflexivity.
- destruct l1 as [ | (t1, h1) l1 ], l2 as [ | (t2, h2) l2 ].
  + reflexivity.
  + apply R_inter_left_1.
  + transitivity (form_recomposition [a] ∩ Ω).
    * apply R_inter_unit_r.
    * now apply R_inter_compat.
  + now apply R_inter_compat.
- transitivity (form_recomposition l2); [ | assumption ].
  destruct l2 as [ | (t, h) l2 ].
  + apply R_omega.
  + apply R_inter_left_2.
Qed.

Lemma beta'_beta_condition s a b : ForallT (fun z => fst z <> nil) s ->
  R (form_recomposition (arrow_hd (filter (fun '(z, _) => Rb a (hd Ω z)) s))) b ->
  { s0 & sublistT s0 s & (ForallT (R a) (arrow_tl s0) * R (form_recomposition (arrow_hd s0)) b)%type }.
Proof using R_dec.
intros Hnil HR. exists (filter (fun '(z, _) => Rb a (hd Ω z)) s); [ | split ].
- apply sublistT_filter.
- clear - Hnil.
  induction s as [ | (t, h) s IH ] in Hnil |- *.
  + constructor.
  + inversion_clear Hnil. destruct t as [ | c t ]; [ now contradiction H | ].
    simpl. case_eq (Rb a c); intro Hac.
    * constructor; [ | apply IH; assumption ].
      unfold Rb in Hac. destruct (R_dec a c); [ assumption | discriminate ].
    * apply IH. assumption.
- assumption.
Qed.

End ProofRelation.


(** * Sub-formulas *)

Inductive subformula : crelation form :=
| sf_id a : subformula a a
| sf_interl d c a : subformula (c ∩ d) a -> subformula c a
| sf_interr d c a : subformula (d ∩ c) a -> subformula c a
| sf_arrowl d c a : subformula (c → d) a -> subformula c a
| sf_arrowr d c a : subformula (d → c) a -> subformula c a.

(* polarity of the subformula c in a, i.e. parity of number of times on the left of an arrow *)
(* [true] for positivie, [false] for negative *)
Fixpoint subformula_sign c a (s : subformula c a) :=
match s with
| sf_id _ => true
| sf_interl t | sf_interr t | sf_arrowr t => subformula_sign t
| sf_arrowl t => negb (subformula_sign t)
end.

(* computes the list of subformulas l which provides a potential left context l <= c from _ <= a *)
Fixpoint sub_ctx_full c a (s : subformula c a) :=
match s with
| sf_id _ | sf_arrowl _ => []
| sf_interl t | sf_interr t => sub_ctx_full t
| @sf_arrowr d _ _ t => sub_ctx_full t · (existT _ d (sf_arrowl t))
end.

Lemma sub_ctx_full_arrowl c a (s : subformula c a) x : In x (sub_ctx_full s) ->
  exists e f (H : e = projT1 x) (t : subformula (e → f) a),
    projT2 x = rew [fun z => subformula z a] H in sf_arrowl t.
Proof.
induction s in x |- *; cbn; (try now intros []); try now intro Hx; apply (IHs _ Hx).
intros [ Hx | [<- | []] ]%in_app_or; cbn.
- apply (IHs _ Hx).
- exists d, c, eq_refl, s. reflexivity.
Qed.

Lemma sub_ctx_full_sub_ctx_full c a (s : subformula c a) x :
  In x (sub_ctx_full s) -> sub_ctx_full (projT2 x) = [].
Proof. intros [e [f [-> [t ->]]]]%sub_ctx_full_arrowl. reflexivity. Qed.

(* all subformulas in sub_ctx_full of c have opposite polarity w.r.t. s *)
Lemma sub_ctx_sign c a (s : subformula c a) x :
  In x (sub_ctx_full s) -> subformula_sign (projT2 x) = negb (subformula_sign s).
Proof.
induction s in x |- *; cbn; (try now intros []); try now intro Hx; apply (IHs _ Hx).
intros [ Hx | [<- | []] ]%in_app_or; cbn.
- apply (IHs _ Hx).
- reflexivity.
Qed.

Definition sub_ctx_sf a b c d (s : subformula a b) (t : subformula c d) :=
  skipn (length (sub_ctx_full s)) (sub_ctx_full t).

(* context l appearing in a | l <= c in a derivation of b | <= d *)
Definition sub_ctx a b c d (s : subformula a b) (t : subformula c d) :=
  map (@projT1 _ _) (sub_ctx_sf s t).

(* ordered pairs of subformulas such that a | l1 <= c may appear in a derivation of b | l2 <= d
     with n the number of elements of l2 not in l1 *)
Inductive sub_coh : forall a b c d n, subformula a b -> subformula c d -> Type :=
| scoh_id_id a c : sub_coh 0 (sf_id a) (sf_id c)
| scoh__iln n a b c d e (s : subformula a b) (t : subformula (c ∩ e) d) :
    sub_coh n s t -> sub_coh n s (sf_interl t)
| scoh__ir n a b c d e (s : subformula a b) (t : subformula (e ∩ c) d) :
    sub_coh n s t -> sub_coh n s (sf_interr t)
| scoh_il_ n a b c d e (s : subformula (a ∩ e) b) (t : subformula c d) :
    sub_coh n s t -> sub_coh n (sf_interl s) t
| scoh_ir_ n a b c d e (s : subformula (e ∩ a) b) (t : subformula c d) :
    sub_coh n s t -> sub_coh n (sf_interr s) t
| scoh_t__ar n a b c d e (s : subformula a b) (t : subformula (e → c) d) :
    sub_coh n s t -> sub_coh (S n) s (sf_arrowr t)
| scoh_t_ar_ n a b c d e (s : subformula (e → a) b) (t : subformula c d) :
    sub_coh (S n) s t -> sub_coh n (sf_arrowr s) t
| scoh_al n a b c d e (s : subformula (a → e) b) (t : subformula c d) :
    sub_coh (S n) s t -> sub_coh 0 (projT2 (hd (existT _ d (sf_id d)) (sub_ctx_sf s t))) (sf_arrowl s).

Lemma sub_coh_correct a b c d n (s : subformula a b) (t : subformula c d) (ch : sub_coh n s t) :
  n + length (sub_ctx_full s) = length (sub_ctx_full t).
Proof.
induction ch; try intros ->; cbn; rewrite ?length_app; cbn; try lia.
rewrite (sub_ctx_full_sub_ctx_full t); [ reflexivity | ].
unfold sub_ctx_sf. remember (length (sub_ctx_full s)) as k eqn:Hk. clear Hk.
remember (sub_ctx_full t) as L eqn:HeqL. clear HeqL.
rewrite <- (firstn_skipn k L) at 2. apply in_or_app. right.
assert (Hlen := length_skipn k L).
destruct (skipn k L) as [ | A L' ].
- exfalso. cbn in Hlen. lia.
- apply in_eq.
Qed.

(* parameter n of [sub_coh] is uniquely determined *)
Lemma sub_coh_index a b c d (s : subformula a b) (t : subformula c d) n1 n2
  (ch1 : sub_coh n1 s t) (ch2 : sub_coh n2 s t) : n1 = n2.
Proof. apply sub_coh_correct in ch1, ch2. lia. Qed.

Lemma sub_coh_sign a b c d n (s : subformula a b) (t : subformula c d) (ch : sub_coh n s t) :
  subformula_sign s = subformula_sign t.
Proof.
induction ch; cbn; auto.
rewrite (sub_ctx_sign t).
- f_equal. symmetry. assumption.
- apply sub_coh_correct in ch.
  unfold sub_ctx_sf. remember (length (sub_ctx_full s)) as k eqn:Hk. clear Hk.
  remember (sub_ctx_full t) as L eqn:HeqL. clear HeqL.
  rewrite <- (firstn_skipn k L) at 2. apply in_or_app. right.
  assert (Hlen := length_skipn k L).
  destruct (skipn k L) as [ | A L' ].
  + exfalso. cbn in Hlen. lia.
  + apply in_eq.
Qed.


(** * Simple types *)
(** inter-free omega-free formulas *)

Fixpoint omega_free a :=
match a with
| var _ => true
| Ω => false
| c → d  | c ∩ d => (omega_free c) && (omega_free d)
end.

Lemma omega_free_list2form l a : omega_free ⟦l, a⟧ = (forallb omega_free l) && (omega_free a).
Proof. induction l as [ | b l IH ]; cbn; [ | rewrite IH, andb_assoc ]; reflexivity. Qed.

Fixpoint inter_free a :=
match a with
| var _ | Ω => true
| _ ∩ _ => false
| c → d => (inter_free c) && (inter_free d)
end.

Definition inter_omega_free a := (inter_free a) && (omega_free a).

Lemma inter_omega_free_arrow a b :
  inter_omega_free (a → b) = true <-> inter_omega_free a = true /\ inter_omega_free b = true.
Proof.
unfold inter_omega_free. cbn.
remember (inter_free a). remember (omega_free a).
remember (inter_free b). remember (omega_free b).
split; [ intro | intros []]; destr_bool. repeat split.
Qed.

Lemma form_decomposition_ia_free_rec a : inter_omega_free a = true ->
  ForallT (fun '(t, _) => ForallT (fun d => inter_omega_free d = true) t) (form_decomposition a).
Proof.
induction a as [ x | | a1 H1 a2 H2 | a1 H1 a2 H2 ]; cbn; intro Ha.
- do 2 constructor.
- constructor.
- discriminate Ha.
- apply inter_omega_free_arrow in Ha as [Ha1 Ha2].
  apply H2 in Ha2.
  clear H1 H2.
  induction Ha2; constructor.
  + destruct x as (t, h).
    constructor; assumption.
  + assumption.
Qed.

Lemma form_decomposition_ia_free a : inter_omega_free a = true -> {'(t, h) | a = ⟦t, var h⟧ }.
Proof.
induction a as [ x | | a1 H1 a2 H2 | a1 H1 a2 H2 ]; cbn; intro Ha; try discriminate Ha.
- exists ([], x). reflexivity.
- apply inter_omega_free_arrow in Ha as [_ Ha2].
  apply H2 in Ha2 as [(t, h) ->].
  exists (a1 :: t, h). reflexivity.
Qed.

Lemma ia_free_form_decomposition t h : Forall (fun z => inter_omega_free z = true ) t ->
  inter_omega_free ⟦t, var h⟧ = true.
Proof.
induction t as [ | a t IH ]; intro HF; [ reflexivity | cbn ].
inversion_clear HF.
apply inter_omega_free_arrow.
split; [ | apply IH]; assumption.
Qed.

Lemma form_decomposition_ia_free_sgt a : inter_omega_free a = true -> length (form_decomposition a) = 1.
Proof.
intros [(t, h) ->]%form_decomposition_ia_free.
induction t as [ | ? ? IH ]; cbn; [ | rewrite length_map, IH ]; reflexivity.
Qed.

Lemma form_redecomposition_ia_free a : inter_omega_free a = true -> form_recomposition (form_decomposition a) = a.
Proof.
intros [(t, h) ->]%form_decomposition_ia_free.
rewrite form_decomposition_list. apply form_recomposition_list.
Qed.


(** * Embedding into general formulas *)

Fixpoint ilform a :=
match a with
| var x => lformulas.lvar Lt x
| Ω => lformulas.ltop
| c ∩ d => lformulas.lwith (ilform c) (ilform d)
| c → d => lformulas.lmap (ilform c) (ilform d)
end.
Coercion ilform : form >-> lformulas.lform.

Lemma ilform_inj : injective ilform.
Proof.
intro a. induction a; intros [] Heq; cbn in Heq; destr_eq Heq; subst.
- reflexivity.
- reflexivity.
- apply IHa1 in Heq. apply IHa2 in H. subst. reflexivity.
- apply IHa1 in Heq. apply IHa2 in H. subst. reflexivity.
Qed.
