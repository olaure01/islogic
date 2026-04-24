(* Lambek Calculus with Finite Products *)

From Stdlib Require Import PeanoNat Lia Wf_nat.
From OLlibs Require Import List_more.
From InterPT Require iformulas.
Export ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * Lambek Calculus with Finite Products *)

(** ** Formulas *)

Inductive lform := lvar (_ : iformulas.Atom) | ltop | lwith (_ _ : lform) | lmap  (_ _ : lform).

Notation 𝖳 := ltop.
Infix "∧" := lwith (at level 35).
Notation "b / a" := (lmap a b) (left associativity, at level 40, a at next level).
Coercion lvar : iformulas.Atom >-> lform.

(** ** Rules *)

Reserved Notation "l ⊦ b" (at level 65).
Inductive lprove : list lform -> lform -> Type :=
| lidentity x : [lvar x] ⊦ x
| ltop_right l : l ⊦ 𝖳
| lwith_left1 a b c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ a ∧ b :: l2 ⊦ c
| lwith_left2 a b c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ b ∧ a :: l2 ⊦ c
| lwith_right a b l : l ⊦ a -> l ⊦ b -> l ⊦ a ∧ b
| lmap_left a b c l1 l2 l3 : l2 ⊦ a -> l1 ++ b :: l3 ⊦ c -> l1 ++ b / a :: l2 ++ l3 ⊦ c
| lmap_right a b l : l · a ⊦ b -> l ⊦ b / a
where "l ⊦ a" := (lprove l a).

Lemma lidentity_gen a : [a] ⊦ a.
Proof.
induction a as [ | | a1 ? a2 | a1 ? a2 ]; constructor; try (rewrite <- (app_nil_l _); constructor; assumption).
cbn. change ([a2 / a1 ; a1]) with ([] ++ a2 / a1 :: [a1] ++ []). constructor; assumption.
Qed.

(** ** Weight *)

Fixpoint lweight l b (pi : l ⊦ b) := S
  match pi with
  | lidentity _ | ltop_right _ => 0
  | lwith_left1 _ _ _ _ pi1 | lwith_left2 _ _ _ _ pi1 | lmap_right _ _ pi1 => lweight pi1
  | lwith_right pi1 pi2 => max (lweight pi1) (lweight pi2)
  | lmap_left _ _ _ pi1 pi2 => lweight pi1 + lweight pi2
  end.

(** ** Cut Elimination *)

Lemma inv_lmap_right_weight a b l (pi : l ⊦ b / a) : { pi' : l · a ⊦ b | lweight pi' < lweight pi }.
Proof.
remember (b / a) as c eqn:Hc.
induction pi in Hc |- *; cbn; try discriminate Hc; subst.
- destruct (IHpi eq_refl) as [pi' Hs].
  revert pi' Hs. list_simpl. intros pi' Hs.
  exists (lwith_left1 _ b0 _ _ pi'). cbn. lia.
- destruct (IHpi eq_refl) as [pi' Hs].
  revert pi' Hs. list_simpl. intros pi' Hs.
  exists (lwith_left2 _ b0 _ _ pi'). cbn. lia.
- destruct (IHpi2 eq_refl) as [pi' Hs].
  revert pi' Hs. list_simpl. intros pi' Hs.
  exists (lmap_left _ _ _ pi1 pi'). cbn. lia.
- injection Hc as [= -> ->].
  exists pi. cbn. lia.
Qed.

Lemma inv_lwith_right_weight a b l (pi : l ⊦ a ∧ b) :
  {'(pi1, pi2) : (l ⊦ a) * (l ⊦ b) | lweight pi1 < lweight pi & lweight pi2 < lweight pi }.
Proof.
remember (a ∧ b) as c eqn:Hc.
induction pi in Hc |- *; cbn; try discriminate Hc; subst.
- destruct (IHpi eq_refl) as [(pi1, pi2) Hs1 Hs2].
  revert pi1 pi2 Hs1 Hs2. list_simpl. intros pi1 pi2 Hs1 Hs2.
  exists (lwith_left1 _ _ _ _ pi1, lwith_left1 _ _ _ _ pi2); cbn; lia.
- destruct (IHpi eq_refl) as [(pi1, pi2) Hs1 Hs2].
  revert pi1 pi2 Hs1 Hs2. list_simpl. intros pi1 pi2 Hs1 Hs2.
  exists (lwith_left2 _ _ _ _ pi1, lwith_left2 _ _ _ _ pi2); cbn; lia.
- injection Hc as [= -> ->].
  exists (pi1, pi2); cbn; lia.
- destruct (IHpi2 eq_refl) as [(pi1', pi2') Hs1 Hs2].
  revert pi1' pi2' Hs1 Hs2. list_simpl. intros pi1' pi2' Hs1 Hs2.
  exists (lmap_left _ _ _ pi1 pi1', lmap_left _ _ _ pi1 pi2'); cbn; lia.
Qed.

Lemma inv_lwith_right1_weight a b l (pi : l ⊦ a ∧ b) : { pi' : l ⊦ a | lweight pi' < lweight pi }.
Proof. destruct (inv_lwith_right_weight pi) as [(pi', _) Hs _]. exists pi'. assumption. Qed.

Lemma inv_lwith_right2_weight a b l (pi : l ⊦ a ∧ b) : { pi' : l ⊦ b | lweight pi' < lweight pi }.
Proof. destruct (inv_lwith_right_weight pi) as [(_, pi') _ Hs]. exists pi'. assumption. Qed.

Lemma lprove_trans_weight a b l1 l2 l3 (pi1 : l2 ⊦ a) (pi2 : l1 ++ a :: l3 ⊦ b) :
  { pi' : l1 ++ l2 ++ l3 ⊦ b | lweight pi' < lweight pi1 + lweight pi2 }.
Proof.
remember (lweight pi1 + lweight pi2) as q eqn:Hq.
induction q as [q IHq] using (well_founded_induction_type lt_wf) in a, b, l1, l2, l3, pi1, pi2, Hq |- *. subst q.
assert (forall a' b' l1' l2' l3' (pi1' : l2' ⊦ a') (pi2' : l1' ++ a' :: l3' ⊦ b'),
  lweight pi1' + lweight pi2' < lweight pi1 + lweight pi2 ->
  {pi' : l1' ++ l2' ++ l3' ⊦ b' | lweight pi' < lweight pi1' + lweight pi2'}) as IH.
{ intros a' b' l1' l2' l3' pi1' pi2' Hs. apply (IHq _ Hs _ _ _ _ _ pi1' pi2' eq_refl). } clear IHq.
remember (l1 ++ a :: l3) as l eqn:Hl.
destruct pi2; try subst l; cbn in IH.
- (* */identity *)
  decomp_list_eq Hl. list_simpl. exists pi1. lia.
- (* */ltop_right *)
  exists (ltop_right _). cbn. destruct pi1; cbn; lia.
- (* */lwith_left1 *)
  decomp_elt_eq_elt Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (lwith_left1 _ _ _ _ pi). cbn. lia.
  + destruct (inv_lwith_right1_weight pi1) as [pi1' Hs'].
    destruct (IH _ _ _ _ _ pi1' pi2) as [pi Hs]; [ lia | ].
    exists pi. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | ].
    revert pi Hs. rewrite ! app_assoc. intros pi Hs.
    exists (lwith_left1 _ _ _ _ pi). cbn. lia.
- (* */lwith_left2 *)
  decomp_elt_eq_elt Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (lwith_left2 _ _ _ _ pi). cbn. lia.
  + destruct (inv_lwith_right2_weight pi1) as [pi1' Hs'].
    destruct (IH _ _ _ _ _ pi1' pi2) as [pi Hs]; [ lia | ].
    exists pi. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | ].
    revert pi Hs. rewrite ! app_assoc. intros pi Hs.
    exists (lwith_left2 _ _ _ _ pi). cbn. lia.
- (* */lwith_right *)
  destruct (IH _ _ _ _ _ pi1 pi2_1) as [pi1' Hs1]; [ cbn; lia | ].
  destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi2' Hs2]; [ cbn; lia | ].
  exists (lwith_right pi1' pi2'). cbn. lia.
- (* */lmap_left *)
  decomp_elt_eq_elt Hl; subst.
  + decomp_elt_eq_app Hl1; subst.
    * destruct (IH _ _ _ _ _ pi1 pi2_1) as [pi1' Hs']; [ lia | ].
      revert pi2_2 IH pi1' Hs'. list_simpl.
      rewrite app_comm_cons, (app_assoc (_ / _ :: _)), (app_assoc ((_ / _ :: _) ++ _)), <- 2 app_comm_cons,
        <- app_assoc.
      intros pi2_2 IH pi1' Hs'.
      exists (lmap_left _ _ _ pi1' pi2_2). cbn. lia.
    * revert pi2_2 IH. cbn. rewrite app_comm_cons, app_assoc. intros pi2_2 IH.
      destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi1' Hs']; [ lia | ].
      revert pi2_2 IH pi1' Hs'. list_simpl. intros pi2_2 IH pi1' Hs'.
      exists (lmap_left _ _ _ pi2_1 pi1'). cbn. lia.
  + destruct (inv_lmap_right_weight pi1) as [pi1' Hs'].
    destruct (IH _ _ _ _ _ pi2_1 pi1') as [pi Hs]; [ lia | ].
    destruct (IH _ _ _ _ _ pi pi2_2) as [pi2' Hs'']; [ lia | ].
    revert pi2' Hs''. list_simpl. intros pi2' Hs''.
    exists pi2'. lia.
  + revert pi2_2 IH. cbn. rewrite <- app_assoc, <- app_comm_cons. intros pi2_2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi1' Hs']; [ lia | ].
    revert pi2_2 IH pi1' Hs'. rewrite app_comm_cons, ! app_assoc, <- (app_assoc _ l2). intros pi2_2 IH pi1' Hs'.
    exists (lmap_left _ _ _ pi2_1 pi1'). cbn. lia.
- (* */lmap_right *)
  revert pi2 IH. list_simpl. intros pi2 IH.
  destruct (IH _ _ _ _ _ pi1 pi2) as [pi' Hs]; [ cbn; lia | ].
  revert pi' Hs. clear. rewrite ? app_assoc, <- (app_assoc l1). intros pi' Hs.
  exists (lmap_right _ _ pi'). cbn. lia.
Qed.

Lemma ltrans a b l1 l2 l3 : l2 ⊦ a -> l1 ++ a :: l3 ⊦ b -> l1 ++ l2 ++ l3 ⊦ b.
Proof. intros pi1 pi2. destruct (lprove_trans_weight _ _ pi1 pi2) as [pi _]. exact pi. Qed.
