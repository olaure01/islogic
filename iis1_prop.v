(* Properties of System ∩IS₁ *)

From Stdlib Require Import PeanoNat Wf_nat Lia CRelationClasses.
From OLlibs Require Import List_more SubListT.
From InterPT Require Export iis1.
From InterPT Require lambek_is.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * Transitivity *)

Lemma omega_left_rev_weight a l (pi : Ω ❘ l ⊦ a) b l0 : { pi' : b ❘ l0 ⊦ a | weight pi' = weight pi }.
Proof.
remember Ω as c eqn:Ho. induction pi in Ho, l0 |- *; destr_eq Ho; subst.
- exists omega_right. reflexivity.
- exists omega_right. reflexivity.
- cbn. destruct (IHpi1 eq_refl l0) as [pi'1 <-], (IHpi2 eq_refl l0) as [pi'2 <-].
  exists (inter_right pi'1 pi'2). reflexivity.
- cbn. destruct (IHpi eq_refl (l0 · a)) as [pi' <-].
  exists (arrow_right pi'). reflexivity.
Qed.

(** ** Direct Proof of Transitivity (not used) *)
Module Type IS_Transitivity.

  Parameter sub_subst : forall a b c d l1 l2, a ❘ ⊦ b -> c ❘ l1 ++ b :: l2 ⊦ d -> c ❘ l1 ++ a :: l2 ⊦ d.
  Parameter sub_trans : forall a b c l1 l2, a ❘ l1 ⊦ b -> b ❘ l2 ⊦ c -> a ❘ l1 ++ l2 ⊦ c.

End IS_Transitivity.


Module Direct_Transitivity : IS_Transitivity.

Lemma sub_trans_rules s :
  ((forall a b c d l1 l2 (pi1 : a ❘ ⊦ b) (pi2 : c ❘ l1 ++ b :: l2 ⊦ d),
      s = weight pi1 + weight pi2 -> { pi : c ❘ l1 ++ a :: l2 ⊦ d | weight pi <= s })
 * (forall a b c l1 l2 (pi1 : a ❘ l1 ⊦ b) (pi2 : b ❘ l2 ⊦ c),
      s = weight pi1 + weight pi2 -> { pi : a ❘ l1 ++ l2 ⊦ c | weight pi <= s })).
Proof.
induction s as [s IH] using (well_founded_induction_type lt_wf).
assert ((forall a b c d l1 l2 (pi1 : a ❘ ⊦ b) (pi2 : c ❘ l1 ++ b :: l2 ⊦ d), weight pi1 + weight pi2 < s ->
         { pi : c ❘ l1 ++ a :: l2 ⊦ d | weight pi <= weight pi1 + weight pi2 }) *
        (forall a b c l1 l2 (pi1 : a ❘ l1 ⊦ b) (pi2 : b ❘ l2 ⊦ c), weight pi1 + weight pi2 < s ->
         { pi : a ❘ l1 ++ l2 ⊦ c | weight pi <= weight pi1 + weight pi2 }))
  as [IH1 IH2].
{ split.
  - intros a b c d l1 l2 pi1 pi2 Hs. refine (fst (IH _ Hs) _ _ _ _ _ _ _ _ eq_refl).
  - intros a b c l1 l2 pi1 pi2 Hs. refine (snd (IH _ Hs) _ _ _ _ _ _ _ eq_refl). }
clear IH. split.
- intros a b c d l1 l2 pi1 pi2 ->.
  remember (l1 ++ b :: l2) as l0 eqn:Heql0. destruct pi2; try decomp_list_eq Heql0; subst.
  + exists omega_right. cbn. lia.
  + destruct (IH1 _ _ _ _ _ _ pi1 pi2) as [pi Hspi]; [ cbn; lia | ].
    exists (inter_left1 pi). cbn. lia.
  + destruct (IH1 _ _ _ _ _ _ pi1 pi2) as [pi Hspi]; [ cbn; lia | ].
    exists (inter_left2 pi). cbn. lia.
  + destruct (IH1 _ _ _ _ _ _ pi1 pi2_1) as [pi_1 Hspi1]; [ cbn; lia | ].
    destruct (IH1 _ _ _ _ _ _ pi1 pi2_2) as [pi_2 Hspi2]; [ cbn; lia | ].
    exists (inter_right pi_1 pi_2). cbn. lia.
  + destruct (IH1 _ _ _ _ _ _ pi1 pi2_2) as [pi Hspi]; [ cbn; lia | ].
    exists (arrow_left pi2_1 pi). cbn. lia.
  + destruct (IH2 _ _ _ _ _ pi1 pi2_1) as [pi Hspi]; [ cbn; lia | ].
    exists (arrow_left pi pi2_2). cbn in *. lia.
  + clear IH2. revert pi2 IH1. list_simpl. intros pi2 IH1.
    destruct (IH1 _ _ _ _ _ _ pi1 pi2) as [pi Hspi]; [ cbn; lia | ].
    revert pi Hspi. rewrite app_comm_cons, app_assoc. intros pi Hspi.
    exists (arrow_right pi). cbn. lia.
- intros a b c l1 l2 pi1 pi2 ->.
  destruct pi1.
  + exists pi2. cbn. lia.
  + destruct (omega_left_rev_weight pi2 a (l ++ l2)) as [pi <-]. exists pi. cbn. lia.
  + destruct (IH2 _ _ _ _ _ pi1 pi2) as [pi Hs]; [ | exists (inter_left1 pi) ]; cbn; lia.
  + destruct (IH2 _ _ _ _ _ pi1 pi2) as [pi Hs]; [ | exists (inter_left2 pi) ]; cbn; lia.
  + cbn in IH1, IH2. cbn. remember (a ∩ b) as e eqn:He. destruct pi2; destr_eq He; subst.
    * list_simpl. exists (inter_right pi1_1 pi1_2). cbn. lia.
    * exists omega_right. cbn. lia.
    * destruct (IH2 _ _ _ _ _ pi1_1 pi2) as [pi Hs]; [ | exists pi ]; cbn; lia.
    * destruct (IH2 _ _ _ _ _ pi1_2 pi2) as [pi Hs]; [ | exists pi ]; cbn; lia.
    * pose (pi1 := inter_right pi1_1 pi1_2).
      destruct (IH2 _ _ _ _ _ pi1 pi2_1) as [pi_1 Hs1]; [ cbn; lia | ].
      destruct (IH2 _ _ _ _ _ pi1 pi2_2) as [pi_2 Hs2]; [ cbn; lia | ].
      exists (inter_right pi_1 pi_2). cbn in *. lia.
    * pose (pi1 := inter_right pi1_1 pi1_2).
      destruct (IH2 _ _ _ _ _ pi1 pi2) as [pi Hs]; [ cbn; lia | ].
      revert pi Hs. clear. rewrite app_assoc. cbn. intros pi Hs.
      exists (arrow_right pi). cbn. lia.
  + destruct (IH2 _ _ _ _ _ pi1_2 pi2) as [pi Hs]; [ | exists (arrow_left pi1_1 pi) ]; cbn; lia.
  + cbn in IH1, IH2. cbn. remember (a → b) as e eqn:He. destruct pi2; destr_eq He; subst.
    * list_simpl. exists (arrow_right pi1). cbn. lia.
    * exists omega_right. cbn. lia.
    * pose (pi := arrow_right pi1).
      destruct (IH2 _ _ _ _ _ pi pi2_1) as [pi_1 Hs1]; [ cbn; lia | ].
      destruct (IH2 _ _ _ _ _ pi pi2_2) as [pi_2 Hs2]; [ cbn; lia | ].
      exists (inter_right pi_1 pi_2). cbn in *. lia.
    * destruct (IH1 _ _ _ _ _ _ pi2_1 pi1) as [pi Hs]; [ cbn; lia | ].
      destruct (IH2 _ _ _ _ _ pi pi2_2) as [pi' Hs']; [ cbn; lia | ].
      revert pi' Hs'. list_simpl. intros pi' Hs'.
      exists pi'. lia.
    * pose (pi := arrow_right pi1).
      destruct (IH2 _ _ _ _ _ pi pi2) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. clear. rewrite app_assoc. cbn. intros pi' Hs.
      exists (arrow_right pi'). cbn. lia.
Qed.

Lemma sub_subst a b c d l1 l2 : a ❘ ⊦ b -> c ❘ l1 ++ b :: l2 ⊦ d -> c ❘ l1 ++ a :: l2 ⊦ d.
Proof. intros pi1 pi2. destruct (fst (sub_trans_rules _) _ _ _ _ _ _ pi1 pi2 eq_refl) as [pi _]. exact pi. Qed.

Lemma sub_trans a b c l1 l2 : a ❘ l1 ⊦ b -> b ❘ l2 ⊦ c -> a ❘ l1 ++ l2 ⊦ c.
Proof. intros pi1 pi2. destruct (snd (sub_trans_rules _) _ _ _ _ _ pi1 pi2 eq_refl) as [pi _]. exact pi. Qed.

End Direct_Transitivity.

From InterPT Require Import equivalences.

Module Lambek_Transitivity : IS_Transitivity.

  Definition sub_subst := sub_subst_lambek.
  Definition sub_trans := sub_trans_lambek.

End Lambek_Transitivity.

Export Lambek_Transitivity.
(* alternative proof
Export Direct_Transitivity. *)



(** * Properties *)
Implicit Type x : Atom.

#[export] Instance sub_preorder : PreOrder (sub nil).
Proof. split; intro a; [ exact identity | intros b c H1 H2; exact (sub_trans H1 H2) ]. Qed.

#[export] Instance sub_equivalence : Equivalence sub_equiv.
Proof.
split.
- intro. split; reflexivity.
- intros a b []. split; assumption.
- intros a b c [] []. split; etransitivity; eassumption.
Qed.

Lemma inter_middle1 a b c d l1 l2 : c ❘ l1 ++ a :: l2 ⊦ d -> c ❘ l1 ++ a ∩ b :: l2 ⊦ d.
Proof. intro pi. refine (sub_subst _ _ _ pi). repeat constructor. Qed.

Lemma inter_middle2 a b c d l1 l2 : c ❘ l1 ++ a :: l2 ⊦ d -> c ❘ l1 ++ b ∩ a :: l2 ⊦ d.
Proof. intro pi. refine (sub_subst _ _ _ pi). repeat constructor; fail. Qed.

Lemma omega_middle_elim a c d l1 l2 : c ❘ l1 ++ Ω :: l2 ⊦ d -> c ❘ l1 ++ a :: l2 ⊦ d.
Proof. intro pi. refine (sub_subst _ _ _ pi). constructor. Qed.


Lemma arrow_right_rev a b c l : c ❘ l ⊦ a → b -> c ❘ l · a ⊦ b.
Proof. intro pi. apply (sub_trans pi). repeat constructor. Qed.

Lemma inter_right_rev a b c l : c ❘ l ⊦ a ∩ b -> (c ❘ l ⊦ a) * (c ❘ l ⊦ b).
Proof. intro pi. rewrite <- (app_nil_r l). split; apply (sub_trans pi); repeat constructor; fail. Qed.

Lemma inter_right_rev1 a b c l : c ❘ l ⊦ a ∩ b -> c ❘ l ⊦ a.
Proof. intro pi. apply (inter_right_rev pi). Qed.

Lemma inter_right_rev2 a b c l : c ❘ l ⊦ a ∩ b -> c ❘ l ⊦ b.
Proof. intro pi. apply (inter_right_rev pi). Qed.

Lemma omega_left_rev a l b l' : Ω ❘ l ⊦ a -> b ❘ l' ⊦ a.
Proof. intro pi. apply (omega_left_rev_weight pi b l'). Qed.

Lemma not_omega_left_atom_right x l : notT (Ω ❘ l ⊦ x).
Proof. intro pi. inversion pi. Qed.

Lemma arrow_left_rev a b c d l : a → b ❘ c :: l ⊦ d -> ((c ❘ ⊦ a) + (Ω ❘ ⊦ d)) * (b ❘ l ⊦ d).
Proof.
intro pi. remember (a → b) as e eqn:Heqe. remember (c :: l) as l' eqn:Heql'.
revert a b Heqe c l Heql'. induction_sub pi a' b' c' d' l pi1 pi2 IH1 IH2;
  intros a b Heqe c l0 Heql0; destr_eq Heqe; destr_eq Heql0; subst;
  (try now constructor; apply (IH1 _ _ eq_refl _ _ eq_refl)); auto.
- destruct (IH1 _ _ eq_refl _ _ eq_refl) as [Hl1 Hr1], (IH2 _ _ eq_refl _ _ eq_refl) as [Hl2 Hr2].
  split; [ | apply inter_right; assumption ].
  destruct Hl1, Hl2; try (left; assumption). right. apply inter_right; assumption.
- list_simpl in IH1. destruct (IH1 _ _ eq_refl _ _ eq_refl) as [Hl Hr].
  split; [ | apply arrow_right; assumption ].
  destruct Hl as [|pi]; [ left; assumption | right ].
  apply arrow_right. apply (omega_left_rev _ _ pi).
Qed.

Lemma arrow_left_var_rev a b x l : a → b ❘ l ⊦ x ->
  {'(c, l0) & l = c :: l0 & ((c ❘ ⊦ a) * (b ❘ l0 ⊦ x))%type }.
Proof. intro pi. inversion_clear pi. now exists (c, l0). Qed.

Lemma inter_left_var_rev a b x l : a ∩ b ❘ l ⊦ x -> (a ❘ l ⊦ x) + (b ❘ l ⊦ x).
Proof. intro pi. inversion_clear pi; [ left | right ]; assumption. Qed.


Example inter_depth_2_bis :
  notT (forall a b c d, ((a → c) → d) ∩ ((b → c) → d) ❘ ⊦ ((b ∩ a) → c) → d).
Proof.
intro pi. specialize (pi (var 0) (var 1) (var 2) (var 3)).
apply arrow_right_rev, inter_left_var_rev in pi as [pi|pi];
  apply arrow_left_var_rev in pi as [(c, l) [= <- <-] [pi _]];
  apply arrow_right_rev, arrow_left_var_rev in pi as [(c, l) [= <- <-] [pi _]];
  [ apply inter_right_rev1 in pi | apply inter_right_rev2 in pi ]; inversion pi.
Qed.


(** * Beta Condition *)

Lemma IS_beta_list s a l b : ForallT (fun z => fst z <> nil) s -> form_recomposition s ❘ a :: l ⊦ b ->
  { s0 & sublistT s0 s & (ForallT (sub nil a) (arrow_tl s0) * (form_recomposition (arrow_hd s0) ❘ l ⊦ b))%type }.
Proof.
intros Hnil pi.
remember (form_recomposition s) as s0 eqn:Hs0.
remember (a :: l) as l0 eqn:Hl0. revert s Hs0 a l Hl0 Hnil.
induction_sub pi a' b' c' d' l' pi1 pi2 IH1 IH2; intros s Hs0 a l Hl0 Hnil; destr_eq Hl0; subst.
- exists nil; [ apply sublistT_nil_l | split ]; cbn; constructor.
- destruct s as [ | (t, h) [ | p s ] ]; inversion Hs0.
  + destruct t; inversion H0.
  + inversion Hnil. subst. cbn in H2. destruct t as [ | p' t ]; [ contradiction H2; reflexivity | ].
    cbn in pi1.
    apply arrow_left_rev in pi1 as [[pi1 | pi1] pi2].
    * exists [(p' :: t, h)]; [ | split; [ | assumption ] ].
      -- constructor. apply sublistT_nil_l.
      -- specialize (IH1 [(p' :: t, h)] eq_refl _ _ eq_refl) as [s0 H1' [H2' H3']];
           [ ForallT_solve | ].
         repeat constructor. assumption.
    * exists nil; [ | split ].
      -- apply sublistT_nil_l.
      -- repeat constructor.
      -- apply (omega_left_rev _ _ pi1).
- destruct s as [ | (t0, h0) [ | (t, h) s ] ]; inversion Hs0.
  + destruct t0; inversion H0.
  + specialize (IH1 ((t, h) :: s) H1 _ _ eq_refl) as [s0 H1' [H2' H3']]; [ ForallT_solve | ].
    exists s0; constructor; assumption.
- destruct (IH1 _ eq_refl _ _ eq_refl Hnil) as [s1 H1a [H1b H1c]].
  destruct (IH2 _ eq_refl _ _ eq_refl Hnil) as [s2 H2a [H2b H2c]].
  clear - H1a H1b H1c H2a H2b H2c.
  enough
    ({s0 & ((sublistT s0 s) * (sublistT s1 s0) * (sublistT s2 s0))%type & ForallT (sub nil a) (arrow_tl s0) })
    as [s0 [[H0 H1] H2]].
  { exists s0; [ assumption | split; [ assumption | ] ].
    clear - H1c H2c H1 H2.
    enough (forall s s', sublistT s' s ->
              form_recomposition (arrow_hd s) ❘ ⊦ form_recomposition (arrow_hd s')) as Hs.
    { apply inter_right.
      - rewrite <- (app_nil_l _). refine (sub_trans _ H1c).
        apply Hs. assumption.
      - rewrite <- (app_nil_l _). refine (sub_trans _ H2c).
        apply Hs. assumption. }
    clear. intros s s' Hs. induction Hs; [ reflexivity | | ].
    - destruct a as (t, h). destruct l1 as [|p1 l1]; cbn.
      + destruct l2 as [|p2 l2]; [ | apply inter_left1 ]; reflexivity.
      + apply inter_right.
        * destruct l2 as [|p2 l2]; [ | apply inter_left1 ]; reflexivity.
        * destruct l2 as [|p2 l2].
          -- exfalso. inversion Hs.
          -- apply inter_left2. assumption.
    - destruct a as (t, h). destruct l2 as [|p l2]; cbn.
      + rewrite <- (app_nil_l _). refine (sub_trans _ IHHs). constructor.
      + apply inter_left2. assumption. }
  clear H1c H2c. induction H1a in H1b, s2, H2a, H2b |- *.
  + exists nil; repeat split; try constructor. assumption.
  + inversion H2a; subst.
    * inversion H1b. inversion H2b. destruct (IHH1a X1 _ X X3) as [s0 [[H0s H1s] H2s] HF].
      exists (a0 :: s0); repeat split; constructor; assumption.
    * inversion H1b. destruct (IHH1a X1 _ X H2b) as [s0 [[H0s H1s] H2s] HF].
      exists (a0 :: s0); repeat split; constructor; assumption.
  + inversion H2a; subst.
    * inversion H2b. destruct (IHH1a H1b _ X X1) as [s0 [[H0s H1s] H2s] HF].
      exists (a0 :: s0); repeat split; constructor; assumption.
    * destruct (IHH1a H1b _ X H2b) as [s0 [[H0s H1s] H2s] HF].
      exists s0; repeat split; try constructor; assumption.
- destruct s as [ | (t, h) [ | p s ]]; inversion Hs0. destruct t; inversion H0. subst.
  exists [(f :: t, h)]; repeat constructor; assumption.
- list_simpl in pi1.
  destruct (IH1 _ eq_refl _ _ eq_refl Hnil) as [s0 H1 [H2 H3]].
  exists s0; [ | split; [ | apply arrow_right ] ]; assumption.
Qed.

Lemma IS_beta : beta_condition (sub nil).
Proof. intros s a b Hnil pi%arrow_right_rev. apply (IS_beta_list Hnil pi). Qed.


(** * Conservativity of IS over ∩IS₁ *)

Lemma is_nis1 a b l : @lambek_is.lprove true (map ilform (b :: l)) (ilform a) -> b ❘ l ⊦ a.
Proof.
intro pi. remember (map ilform (b :: l)) as l0 eqn:Hl. remember (ilform a) as a0 eqn:Ha.
induction pi in a, b, l, Ha, Hl |- *; decomp_list_eq Hl; subst;
  try (destruct a; destr_eq Ha); try (destruct x; destr_eq Heq); subst;
  try (destruct x0; discriminate Heq).
- destruct Heq as [->%ilform_inj ->]. decomp_list_eq Hl. constructor.
- constructor.
- decomp_list_eq Hl; subst.
  + apply inter_middle1. apply IHpi; list_simpl; reflexivity.
  + apply inter_left1. apply IHpi; list_simpl; reflexivity.
- decomp_list_eq Hl; subst.
  + apply inter_middle2. apply IHpi; list_simpl; reflexivity.
  + apply inter_left2. apply IHpi; list_simpl; reflexivity.
- constructor; [ apply IHpi1 | apply IHpi2 ]; reflexivity.
- destruct (a1 eq_refl) as [H' [d Hd]%lambek_is.length_one_iffT_sgt].
  decomp_list_eq H'. decomp_list_eq Hd. subst. list_simpl.
  decomp_list_eq Hl; subst.
  + discriminate Hl0.
  + constructor; [ apply IHpi1 | apply IHpi2 ]; reflexivity.
- constructor. apply IHpi; list_simpl; reflexivity.
Qed.
