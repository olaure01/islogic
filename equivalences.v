(* Equivalences: BCD, IS and Lambek *)

From Stdlib Require Import PeanoNat Lia Wf_nat.
From OLlibs Require Import Logic_Datatypes_more funtheory List_more.
From InterPT Require Import bcd ilambek iis1.
Import LogicNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * Girard's Style Embedding of ∩IS₁ into Lambek *)

Notation nn a := (lvar 0 / (lvar 1 / a)).

Fixpoint gtrans a :=
  match a with
  | var x => lvar (S (S x))
  | Ω => 𝖳
  | b ∩ c => gtrans b ∧ gtrans c
  | b → c => gtrans c / nn (gtrans b)
  end.

Lemma gtrans_inj : injective gtrans.
Proof.
intro a. induction a as [ | | a1 IH1 a2 IH2 | a1 IH1 a2 IH2 ]; intros [] [=]; subst; [ reflexivity .. | | ].
- erewrite IH1; [ | eassumption ]. erewrite IH2; [ | eassumption ]. reflexivity.
- erewrite IH1; [ | eassumption ]. erewrite IH2; [ | eassumption ]. reflexivity.
Qed.

(* Proposition 21 *)
Lemma correct_gtrans a l b : a ❘ l ⊦ b -> gtrans a :: map (fun z => nn (gtrans z)) l ⊦ gtrans b.
Proof.
intro H. induction_sub H a b c d l pi1 pi2 IH1 IH2; cbn; try now (rewrite <- app_nil_l at 1; constructor).
- apply lidentity_gen.
- rewrite <- app_nil_l at 1.
  change (nn (gtrans c) :: map (fun z => nn (gtrans z)) l)
    with ([nn (gtrans c)] ++ map (fun z => nn (gtrans z)) l).
  apply lmap_left; [ apply lmap_right | assumption ].
  cbn. change ([nn (gtrans c); lvar 1 / gtrans a])
         with ([] ++ nn (gtrans c) :: [lvar 1 / gtrans a] ++ []).
  apply lmap_left, lidentity. apply lmap_right.
  cbn. change ([lvar 1 / gtrans a ; gtrans c])
         with ([] ++ lvar 1 / gtrans a :: [gtrans c] ++ []).
  apply lmap_left, lidentity. assumption.
- rewrite map_last in IH1. apply lmap_right. assumption.
Qed.


(* Lemma 23 *)
Lemma unprov_trans_var v l1 l2 :
  map (fun z => nn (gtrans z)) l1 ++ map gtrans l2 ⊦ lvar v -> l1 = [] /\ 1 < v.
Proof.
intro pi.
remember (lweight pi) as q eqn:Hq.
induction q as [q IHq] using (well_founded_induction lt_wf) in v, l1, l2, pi, Hq |- *. subst q.
assert (forall v' l1' l2' (pi' : map (fun z => nn (gtrans z)) l1' ++ map gtrans l2' ⊦ lvar v'),
        lweight pi' < lweight pi -> l1' = [] /\ 1 < v') as IH.
{ intros v' l1' l2' pi' Hs. apply (IHq _ Hs _ _ _ pi' eq_refl). } clear IHq.
remember (map (fun z => nn (gtrans z)) l1 ++ map gtrans l2) as l eqn: Hl. remember (lvar v) as c eqn : Hc.
destruct pi; try now destr_eq Hl; cbn in IH.
- destruct l1 as [|A l1], l2 as [|B l2]; destr_eq Hl. destruct B; destr_eq Hl.
  injection Hc as ->. subst. split; [ reflexivity | lia ].
- decomp_list_eq Hl; decomp_map_eq Hl.
  + discriminate Heq.
  + destruct x; destr_eq Heq. subst.
    revert pi IH. list_simpl. rewrite <- map_cons, <- map_app. intros pi IH.
    apply (IH _ _ _ pi). cbn. lia.
- decomp_list_eq Hl; decomp_list_eq Hl.
  + discriminate Heq.
  + destruct x; destr_eq Heq. subst.
    revert pi IH. list_simpl. rewrite <- map_cons, <- map_app. intros pi IH.
    apply (IH _ _ _ pi). cbn. lia.
- decomp_list_eq Hl; decomp_map_eq Hl.
  + exfalso.
    injection Heq as [= <- <-]. subst.
    destruct (inv_lmap_right_weight pi1) as [pi'1 Hs1].
    assert ({'(l31, l32) | l3 = map (fun z => nn (gtrans z)) l31 ++ map gtrans l32 }) as [[l31 l32] ->].
    { decomp_app_eq_app Hl0.
      - decomp_map_eq Hl1. exists (l3, nil). list_simpl. reflexivity.
      - decomp_map_eq Hl2. exists (l, l1). assumption. }
    revert pi'1 Hs1. list_simpl. rewrite <- map_last. intros pi1' Hs1.
    destruct (IH _ _ _ pi1') as []; cbn; lia.
  + destruct x; destr_eq Heq. subst.
    revert pi2 IH. list_simpl. rewrite <- map_cons, <- map_app. intros pi2 IH.
    apply (IH _ _ _ pi2). cbn. lia.
Qed.


Lemma unprov_trans_var_var l1 l2 v0 v :
  map (fun z => nn z) l1 ++ lvar v0 :: l2 ⊦ lvar v -> l1 = [] /\ l2 = [] /\ v = v0.
Proof.
intro pi.
remember (lweight pi) as q eqn:Hq.
induction q as [q IHq] using (well_founded_induction lt_wf) in v, v0, l1, l2, pi, Hq |- *. subst q.
assert (forall l1' l2' v0' v'
        (pi' : map (fun z => nn z) l1' ++ lvar v0' :: l2' ⊦ lvar v'),
        lweight pi' < lweight pi -> l1' = [] /\ l2' = [] /\ v' = v0') as IH.
{ intros l1' l2' v0' v' pi' Hs. apply (IHq _ Hs _ _ _ _ pi' eq_refl). } clear IHq.
remember (map (fun z => nn z) l1 ++ lvar v0 :: l2) as l eqn: Hl.
remember (lvar v) as c eqn : Hc.
destruct pi; try now destr_eq Hl; cbn in IH.
- decomp_list_eq Hl. decomp_list_eq Hl0. injection Hc as ->. injection Hl as ->. now subst.
- exfalso.
  decomp_list_eq Hl.
  + decomp_map_eq Hl0. discriminate.
  + subst.
    revert pi IH. list_simpl. intros pi IH.
    destruct (IH _ _ _ _ pi) as [_ [Heq _]]; [ lia | ]. decomp_list_eq Heq.
- exfalso.
  decomp_list_eq Hl.
  + decomp_map_eq Hl0. discriminate.
  + subst.
    revert pi IH. list_simpl. intros pi IH.
    destruct (IH _ _ _ _ pi) as [_ [Heq _]]; [ lia | decomp_list_eq Heq ].
- exfalso.
  decomp_list_eq Hl.
  + decomp_map_eq Hl0. injection Heq as [= <- <-]. subst.
    decomp_list_eq Hl1; subst; destruct (inv_lmap_right_weight pi1) as [pi1' Hs].
    * revert pi1' Hs. list_simpl. intros pi1' Hs.
      destruct (IH _ _ _ _ pi1') as [_ [Heq _]]; [ cbn; lia | decomp_list_eq Heq ].
    * destruct (IH _ _ _ _ pi2) as [_ [Heq _]]; [ cbn; lia | decomp_list_eq Heq ].
  + subst.
    revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ pi2) as [_ [Heq _]]; [ lia | decomp_list_eq Heq ].
Qed.

(* Lemma 22 *)
Lemma unprov_trans_n v l1 l2 a
  (pi : map (fun z => nn z) l1 ++ lvar 1 / a :: l2 ⊦ lvar v) :
    (v = 0 -> { B | l1 = [B] }) * (v = 1 -> l1 = [])
  * { pi0 : l2 ++ l1 ⊦ a | lweight pi0 < lweight pi }.
Proof.
remember (lweight pi) as q eqn:Hq.
induction q as [q IHq] using (well_founded_induction_type lt_wf) in v, l1, l2, a, pi, Hq |- *. subst q.
assert (forall v' l1' l2' a'
        (pi' : map (fun z => nn z) l1' ++ lvar 1 / a' :: l2' ⊦ lvar v'),
        lweight pi' < lweight pi ->
          (v' = 0 -> { B | l1' = [B] }) * (v' = 1 -> l1' = [])
        * { pi0 : l2' ++ l1' ⊦ a' | lweight pi0 < lweight pi' }) as IH.
{ intros v' l1' l2' a' pi' Hs. apply (IHq _ Hs _ _ _ _ pi' eq_refl). } clear IHq.
remember (map (fun z => nn z) l1 ++ lvar 1 / a :: l2) as l eqn: Hl.
remember (lvar v) as c eqn : Hc.
destruct pi; try now destr_eq Hl; cbn in IH.
- exfalso. decomp_list_eq Hl.
- decomp_list_eq Hl.
  + exfalso. decomp_map_eq Hl0. discriminate.
  + subst.
    revert pi IH. list_simpl. intros pi IH.
    destruct (IH _ _ _ _ pi) as [[H1 H2] [pi' Hs]]; [ lia | repeat split; try assumption ]. clear IH.
    revert pi pi' Hs. list_simpl. intros pi pi' Hs.
    exists (lwith_left1 _ _ _ _ pi'). cbn. lia.
- decomp_list_eq Hl.
  + exfalso. decomp_map_eq Hl0. discriminate.
  + subst.
    revert pi IH. list_simpl. intros pi IH.
    destruct (IH _ _ _ _ pi) as [[H1 H2] [pi' Hs]]; [ lia | repeat split; try assumption ]. clear IH.
    revert pi pi' Hs. list_simpl. intros pi pi' Hs.
    exists (lwith_left2 _ _ _ _ pi'). cbn. lia.
- decomp_list_eq Hl.
  + decomp_map_eq Hl0. injection Heq as [= <- <-].
    destruct (inv_lmap_right_weight pi1) as [pi1' Hs'].
    decomp_elt_eq_app Hl1; subst.
    * destruct (unprov_trans_var_var _ _ _ pi2) as [ -> [-> ->]].
      revert pi1' Hs'. list_simpl. intros pi1' Hs'.
      destruct (IH _ _ _ _ pi1') as [[H1' H2'] [pi Hs]]; [ cbn; lia | ].
      specialize (H2' eq_refl) as ->. repeat split.
      -- intros _. exists x. reflexivity.
      -- intros [=].
      -- revert pi Hs. list_simpl. intros pi Hs.
         exists pi. cbn in *. lia.
    * exfalso.
      destruct (unprov_trans_var_var _ _ _ pi2) as [_ [Heq _]]. decomp_list_eq Heq.
  + injection Hl as [= -> ->]. subst.
    destruct (unprov_trans_var_var _ _ _ pi2) as [ -> [-> ->]].
    list_simpl. repeat split.
    * intros [=].
    * exists pi1. lia.
  + subst.
    revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ pi2) as [[H1' H2'] [pi2' Hs']]; [ lia | ].
    repeat split; [ assumption .. | ].
    revert pi2' Hs'. list_simpl. intros pi2' Hs'.
    exists (lmap_left _ _ _ pi1 pi2'). cbn. lia.
Qed.

(* Proposition 24 *)
Lemma complete_gtrans a l b : gtrans a :: map (fun z => nn (gtrans z)) l ⊦ gtrans b -> a ❘ l ⊦ b.
Proof.
intro pi.
remember (lweight pi) as q eqn:Hq.
induction q as [q IHq] using (well_founded_induction_type lt_wf) in a, l, b, pi, Hq |- *. subst q.
assert (forall a' l' b' (pi' : gtrans a' :: map (fun z => nn (gtrans z)) l' ⊦ gtrans b'),
        lweight pi' < lweight pi -> a' ❘ l' ⊦ b') as IH.
{ intros a' l' b' pi' Hs. apply (IHq _ Hs _ _ _ pi' eq_refl). } clear IHq.
remember (gtrans a :: map (fun z => nn (gtrans z)) l) as l' eqn: Hl'.
remember (gtrans b) as c eqn : Hc.
destruct pi; cbn in IH.
- destruct a; destr_eq Hl'. destruct b; destr_eq Hc. decomp_map_eq H. subst.
  injection Hc as [= ->]. apply identity.
- destruct b; destr_eq Hc. apply omega_right.
- decomp_list_eq Hl'; subst.
  + decomp_map_eq Hl'0. discriminate Heq.
  + destruct a; destr_eq Hl'. subst.
    apply inter_left1.
    apply (IH _ _ _ pi). cbn. lia.
- decomp_list_eq Hl'; subst.
  + decomp_map_eq Hl'0. discriminate Heq.
  + destruct a; destr_eq Hl'. subst.
    apply inter_left2.
    apply (IH _ _ _ pi). cbn. lia.
- destruct b; destr_eq Hc. subst.
  apply inter_right; [ apply (IH _ _ _ pi1) | apply (IH _ _ _ pi2) ]; lia.
- decomp_list_eq Hl'; subst.
  + exfalso.
    decomp_map_eq Hl'0. injection Heq as [= <- <-]. subst.
    destruct (inv_lmap_right_weight pi1) as [pi1' Hs'].
    revert pi1' Hs'. change ([gtrans x]) with (map gtrans [x]). intros pi1' Hs'.
    destruct (unprov_trans_var _ _ pi1') as [_ ?]. lia.
  + destruct a; destr_eq Hl'. decomp_map_eq H0. subst.
    destruct (inv_lmap_right_weight pi1) as [pi1' Hs'].
    remember (map (fun z => nn (gtrans z)) l2) as l eqn:Heql.
    replace (map (fun z => nn (gtrans z)) l2) with (map (fun z => nn z) (map gtrans l2)) in Heql by apply map_map.
    subst l.
    destruct (unprov_trans_n _ _ _ pi1') as [[[a Ha]%(fun x => x eq_refl) _] [pi Hs]].
    decomp_list_eq Ha. subst.
    apply arrow_left.
    * cbn in *. change nil with (map (fun z => nn (gtrans z)) nil) in pi.
      apply (IH _ _ _ pi). cbn. lia.
    * apply (IH _ _ _ pi2). cbn. lia.
- destruct b; destr_eq Hc. subst.
  apply arrow_right.
  revert pi IH. list_simpl. change (nn (gtrans b1)) with ((fun z => nn (gtrans z)) b1). rewrite <- map_last.
  intros pi IH.
  apply (IH _ _ _ pi). lia.
Qed.

(** ** Transitivity of IS from Lambek cut elimination *)

Lemma sub_subst_lambek a b c d l1 l2 : a ❘ ⊦ b -> c ❘ l1 ++ b :: l2 ⊦ d -> c ❘ l1 ++ a :: l2 ⊦ d.
Proof.
intros pi1%correct_gtrans pi2%correct_gtrans.
apply complete_gtrans.
list_simpl in *. rewrite app_comm_cons in *. cons2app. refine (ltrans _ _ _ pi2).
constructor.
replace ([nn (gtrans a)] · lvar 1 / gtrans b) with ([] ++ nn (gtrans a) :: [lvar 1 / gtrans b] ++ nil)
  by list_reflexivity.
constructor; constructor.
replace ([lvar 1 / gtrans b] · gtrans a) with ([] ++ lvar 1 / gtrans b :: [gtrans a] ++ nil)
  by list_reflexivity.
now constructor; [ | constructor ].
Qed.

Lemma sub_trans_lambek a b c l1 l2 : a ❘ l1 ⊦ b -> b ❘ l2 ⊦ c -> a ❘ l1 ++ l2 ⊦ c.
Proof.
intros pi1%correct_gtrans pi2%correct_gtrans.
apply complete_gtrans.
rewrite <- (app_nil_l _) in pi2. rewrite <- (app_nil_l _), map_app.
apply (ltrans _ _ pi1 pi2).
Qed.


(** * Equivalence between BCD and IS *)

Notation "a ⩽ b " := (@bcd_sub [] a b) (at level 70).

Lemma is_bcd a l b : a ❘ l ⊦ b -> a ⩽ ⟦l, b⟧.
Proof.
intro pi. induction_sub pi a b c d l pi1 pi2 IH1 IH2.
- reflexivity.
- induction l as [ | ? l IHl ] using rev_rect; cbn.
  + apply bcd_omega_right.
  + rewrite list2form_last. etransitivity; [ apply IHl | ].
    apply bcd_arrow_list.
    apply bcd_arrow_omega_distr.
- etransitivity; [ | eassumption ]. apply bcd_inter_left1.
- etransitivity; [ | eassumption ]. apply bcd_inter_left2.
- apply bcd_arrow_inter_list; assumption.
- apply bcd_arrow; assumption.
- rewrite list2form_last in IH1. assumption.
Qed.

(* Theorem 19 *)
Theorem is_bcd_equiv a b : a ⩽ b <=> a ❘ ⊦ b.
Proof.
split; intro H.
- induction H; try (repeat constructor; fail).
  + rewrite <- (app_nil_l nil). eapply sub_trans_lambek; eassumption.
  + apply inter_right; now constructor.
  + constructor. constructor; assumption.
  + inversion i.
- change b with ⟦[], b⟧. apply is_bcd. assumption.
Qed.

Theorem lambek_bcd_equiv a b : a ⩽ b <=> [gtrans a] ⊦ gtrans b.
Proof.
split; intro H; [ apply is_bcd_equiv in H | apply is_bcd_equiv ].
- change nil with (map (fun z => nn (gtrans z)) nil). apply correct_gtrans. assumption.
- apply complete_gtrans. assumption.
Qed.
