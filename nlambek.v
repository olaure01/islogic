(* Negative Lambek Calculus *)

From Stdlib Require Import PeanoNat Lia Wf_nat.
From OLlibs Require Import List_more.
From InterPT Require Export nformulas.
Export ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * Negative Lambek Calculus nL *)

(** ** Rules *)

Reserved Notation "l ⊦ a" (at level 65, format "l  ⊦  a").
Inductive lprove : list lform -> lform -> Type :=
| lidentity a : [a] ⊦ a
| ltop_right l : l ⊦ 𝖳
| lwith_left1 a b c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ a ∧ b :: l2 ⊦ c
| lwith_left2 a b c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ b ∧ a :: l2 ⊦ c
| lwith_right a b l : l ⊦ a -> l ⊦ b -> l ⊦ a ∧ b
| lmap_left a b c l1 l2 l3 : l2 ⊦ a -> l1 ++ b :: l3 ⊦ c -> l1 ++ b / a :: l2 ++ l3 ⊦ c
| lmap_right a b l : l · a ⊦ b -> l ⊦ b / a
| lfrl_left a x b c l1 l2 : closed b -> l1 ++ subs x b a :: l2 ⊦ c -> l1 ++ lfrl x a :: l2 ⊦ c
| lfrl_right a x l : map fupz l ⊦ subs x (dvar 0) (fupz a) -> l ⊦ lfrl x a
where "l ⊦ a" := (lprove l a).
Arguments lidentity {_}, _.
Arguments ltop_right {_}, _.
Arguments lwith_left1 [_ _ _ _ _] _, [_] _ [_ _] _, _ _ _ _ _ _.
Arguments lwith_left2 [_ _ _ _ _] _, [_] _ [_ _ _] _, _ _ _ _ _ _.
Arguments lwith_right [_ _ _] _ _, _ _ _ _ _.
Arguments lmap_left [_ _ _ _ _ _] _ _, [_ _ _ _ _] _ _ _, _ _ _ _ _ _ _ _.
Arguments lmap_right [_ _ _] _, _ _ _ _.
Arguments lfrl_left [_ _ _ _ _ _ _] _, [_ _ _ _ _ _] _ _, _ _ _ _ _ _ _.
Arguments lfrl_right [_ _ _] _, [_] _ [_] _, _ _ _ _.


(** *** Weight *)

Fixpoint lweight l b (pi : l ⊦ b) := S
match pi with
| lidentity | ltop_right => 0
| lwith_left1 pi1 | lwith_left2 pi1 | lmap_right pi1 | lfrl_right pi1 | lfrl_left pi1 => lweight pi1
| lwith_right pi1 pi2 => max (lweight pi1) (lweight pi2)
| lmap_left pi1 pi2 => lweight pi1 + lweight pi2
end.

(** substitutes [formula] [f] for index [k] in proof [pi] and decreases indexes above [k] *)
Lemma psubs k f (Hc : closed f) l b (pi : l ⊦ b) :
  { pi' : map (nsubs k f) l ⊦  nsubs k f b | lweight pi' = lweight pi }.
Proof.
induction pi in k, f, Hc |- *;
  try (destruct (IHpi k f Hc) as [pi' Hs]);
  try (destruct (IHpi1 k f Hc) as [pi1' Hs1]);
  try (destruct (IHpi2 k f Hc) as [pi2' Hs2]).
- now exists lidentity.
- now exists ltop_right.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (lwith_left1 pi'). cbn. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (lwith_left2 pi'). cbn. lia.
- exists (lwith_right pi1' pi2'). cbn. lia.
- revert pi2' Hs2. list_simpl. intros pi2' Hs2.
  exists (lmap_left pi1' pi2'). cbn. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (lmap_right pi'). cbn. lia.
- cbn. rewrite <- Hs. clear Hs.
  revert pi'. list_simpl. rewrite nsubs_subs_com.
  + intro pi'.
    assert (closed (nsubs k f b)) as Hc' by (rewrite freevars_nsubs; assumption).
    exists (lfrl_left Hc' pi'). cbn. lia.
  + rewrite Hc. intros [].
- clear pi' Hs.
  rewrite <- (freevars_fup 0) in Hc.
  destruct (IHpi (S k) _ Hc) as [pi' Hs].
  cbn. rewrite <- Hs. clear Hs.
  revert pi'.
  rewrite nsubs_subs_com.
  2:{ rewrite Hc. intros []. }
  cbn. rewrite map_map.
  rewrite (map_ext (fun x => nsubs (S k) (fupz f) (fupz x)) (fun x => fupz (nsubs k f x))).
  2:{ apply nsubs_fup_com. }
  rewrite nsubs_fup_com.
  rewrite <- map_map.
  intro pi'.
  exists (lfrl_right pi'). reflexivity.
Qed.

(** lift indexes above [k] in proof [pi] *)
Lemma pup k l b (pi : l ⊦ b) : { pi' : map (fup k) l ⊦ fup k b | lweight pi' = lweight pi }.
Proof.
induction pi in k |- *;
  try (destruct (IHpi k) as [pi' Hs]) ;
  try (destruct (IHpi1 k) as [pi1' Hs1]) ;
  try (destruct (IHpi2 k) as [pi2' Hs2]).
- now exists lidentity.
- now exists ltop_right.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (lwith_left1 pi'). cbn. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (lwith_left2 pi'). cbn. lia.
- exists (lwith_right pi1' pi2'). cbn. lia.
- revert pi2' Hs2. list_simpl. intros pi2' Hs2.
  exists (lmap_left pi1' pi2'). cbn. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (lmap_right pi'). cbn. lia.
- cbn. rewrite <- Hs. clear Hs.
  rewrite <- (freevars_fup k) in e.
  revert pi'. list_simpl. rewrite fup_subs_com.
  intro pi'.
  exists (lfrl_left e pi'). reflexivity.
- clear pi' Hs.
  destruct (IHpi (S k)) as [pi' Hs].
  cbn. rewrite <- Hs. clear Hs.
  revert pi'.
  rewrite fup_subs_com. cbn. rewrite fup_fup_com.
  rewrite map_map.
  rewrite (map_ext (fun x => fup (S k) (fupz x)) (fun x => fupz (fup k x))) by apply fup_fup_com.
  rewrite <- map_map.
  intro pi'.
  exists (lfrl_right pi'). reflexivity.
Qed.


(** *** Cut Elimination *)

Lemma lprove_trans_weight a b l1 l2 l3 (pi1 : l2 ⊦ a) (pi2 : l1 ++ a :: l3 ⊦ b) :
  { pi' : l1 ++ l2 ++ l3 ⊦ b | lweight pi' < lweight pi1 + lweight pi2 }.
Proof.
remember (lweight pi1 + lweight pi2) as q eqn:Hq.
induction q as [q IHq] using (well_founded_induction_type lt_wf) in a, b, l1, l2, l3, pi1, pi2, Hq |- *.
subst q.
assert (forall a' b' l1' l2' l3' (pi1' : l2' ⊦ a') (pi2' : l1' ++ a' :: l3' ⊦ b'),
  lweight pi1' + lweight pi2' < lweight pi1 + lweight pi2 ->
  {pi' : l1' ++ l2' ++ l3' ⊦ b' | lweight pi' < lweight pi1' + lweight pi2'}) as IH.
{ intros a' b' l1' l2' l3' pi1' pi2' Hs. exact (IHq _ Hs _ _ _ _ _ pi1' pi2' eq_refl). } clear IHq.
remember (l1 ++ a :: l3) as l eqn:Hl.
destruct pi2; try subst l; cbn in IH.
- (* */identity *)
  decomp_list_eq Hl. list_simpl. exists pi1. lia.
- (* */ltop_right *)
  exists (ltop_right _). cbn. destruct pi1; cbn; lia.
- (* */lwith_left1 *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (lwith_left1 pi). cbn. lia.
  + cbn. remember (a0 ∧ b) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lwith_left1 pi2). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_1 pi2) as [pi' Hs]; [ cbn; lia | ].
      exists pi'. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite 2 app_assoc. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | ].
    revert pi Hs. rewrite ! app_assoc. intros pi Hs.
    exists (lwith_left1 pi). cbn. lia.
- (* */lwith_left2 *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (lwith_left2 pi). cbn. lia.
  + cbn. remember (b ∧ a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lwith_left2 pi2). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_2 pi2) as [pi' Hs]; [ cbn; lia | ].
      exists pi'. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite 2 app_assoc. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | ].
    revert pi Hs. rewrite ! app_assoc. intros pi Hs.
    exists (lwith_left2 pi). cbn. lia.
- (* */lwith_right *)
  destruct (IH _ _ _ _ _ pi1 pi2_1) as [pi1' Hs1]; [ cbn; lia | ].
  destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi2' Hs2]; [ cbn; lia | ].
  exists (lwith_right pi1' pi2'). cbn. lia.
- (* */lmap_left *)
  decomp_list_eq Hl; subst.
  + decomp_list_eq Hl1; subst.
    * destruct (IH _ _ _ _ _ pi1 pi2_1) as [pi1' Hs']; [ lia | ].
      revert pi2_2 IH pi1' Hs'. list_simpl.
      rewrite app_comm_cons, (app_assoc (_ / _ :: _)), (app_assoc ((_ / _ :: _) ++ _)), <- 2 app_comm_cons,
        <- app_assoc.
      intros pi2_2 IH pi1' Hs'.
      exists (lmap_left pi1' pi2_2). cbn. lia.
    * revert pi2_2 IH. cbn. rewrite app_comm_cons, app_assoc. intros pi2_2 IH.
      destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi1' Hs']; [ lia | ].
      revert pi2_2 IH pi1' Hs'. list_simpl. intros pi2_2 IH pi1' Hs'.
      exists (lmap_left pi2_1 pi1'). cbn. lia.
  + cbn. remember (b / a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lmap_left pi2_1 pi2_2). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (lmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite 3 app_assoc. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi2_1 pi1) as [pi1' Hs1]; [ cbn; lia | ].
      destruct (IH _ _ _ _ _ pi1' pi2_2) as [pi2' Hs2]; [ cbn; lia | ].
      revert pi2' Hs2. list_simpl. intros pi2' Hs2.
      exists pi2'. lia.
    * destruct (IH _ _ _ _ _ pi1 (lmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
  + revert pi2_2 IH. cbn. rewrite <- app_assoc, <- app_comm_cons. intros pi2_2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi1' Hs']; [ lia | ].
    revert pi2_2 IH pi1' Hs'. rewrite app_comm_cons, ! app_assoc, <- (app_assoc _ l2). intros pi2_2 IH pi1' Hs'.
    exists (lmap_left pi2_1 pi1'). cbn. lia.
- (* */lmap_right *)
  revert pi2 IH. list_simpl. intros pi2 IH.
  destruct (IH _ _ _ _ _ pi1 pi2) as [pi' Hs]; [ cbn; lia | ].
  revert pi' Hs. clear. rewrite ? app_assoc, <- (app_assoc l1). intros pi' Hs.
  exists (lmap_right pi'). cbn. lia.
- (* */lfrl_left *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (lfrl_left e pi). cbn. lia.
  + cbn. remember (∀ x a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lfrl_left e pi2). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite 2 app_assoc. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lfrl_left e0 pi'). cbn. lia.
    * destruct (psubs 0 _ e pi1) as [pi1' Hs'].
      revert pi1' Hs'. rewrite nsubs_subs_com by (rewrite e; intros []). cbn.
      rewrite map_map. rewrite (map_ext (fun x => nsubs 0 b (fupz x)) (fun x => x)) by apply nsubs_z_fup.
      rewrite nsubs_z_fup. rewrite map_id. intros pi1' Hs'.
      destruct (IH _ _ _ _ _ pi1' pi2) as [pi1'' Hs1]; [ cbn; lia | ].
      exists pi1''. cbn in *. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | ].
    revert pi Hs. rewrite ! app_assoc. intros pi Hs.
    exists (lfrl_left e pi). cbn. lia.
- (* */lfrl_right *)
  revert pi2 IH. cbn. rewrite (map_app fupz l1 (a :: l3)). cbn. intros pi2 IH.
  destruct (pup 0 pi1) as [pi1' Hs1].
  destruct (IH _ _ _ _ _ pi1' pi2) as [pi' Hs]; [ cbn; lia | ].
  revert pi' Hs. rewrite <- !map_app. intros pi' Hs.
  exists (lfrl_right pi'). cbn. lia.
Qed.

Lemma lcut a b l1 l2 l3 : l2 ⊦ a -> l1 ++ a :: l3 ⊦ b -> l1 ++ l2 ++ l3 ⊦ b.
Proof. intros pi1 pi2. destruct (lprove_trans_weight _ _ pi1 pi2) as [pi _]. exact pi. Qed.

Lemma lsubst a b c l1 l2 : [a] ⊦ b -> l1 ++ b :: l2 ⊦ c -> l1 ++ a :: l2 ⊦ c.
Proof. intros pi1 pi2. apply (lcut _ _ pi1 pi2). Qed.

Lemma ltrans b c l1 l2 : l1 ⊦ b -> b :: l2 ⊦ c -> l1 ++ l2 ⊦ c.
Proof. intros pi1 pi2. rewrite <- (app_nil_l _) in pi2. refine (lcut _ _ pi1 pi2). Qed.


(** ** Reversed system nLʳ *)

(* Table 3 *)
Reserved Notation "l ⊦r a" (at level 65, format "l  ⊦r  a").
Inductive rlprove : list lform -> lform -> Type :=
| rlidentity v x : [lvar v x] ⊦r lvar v x
| rltop_right l : l ⊦r 𝖳
| rlwith_left1 a b v y l2 : a :: l2 ⊦r lvar v y -> a ∧ b :: l2 ⊦r lvar v y
| rlwith_left2 a b v y l2 : a :: l2 ⊦r lvar v y -> b ∧ a :: l2 ⊦r lvar v y
| rlwith_right a b l : l ⊦r a -> l ⊦r b -> l ⊦r a ∧ b
| rlmap_left a b v y l2 l3 : l2 ⊦r a -> b :: l3 ⊦r lvar v y -> b / a :: l2 ++ l3 ⊦r lvar v y
| rlmap_right a b l : l · a ⊦r b -> l ⊦r b / a
| rlfrl_left a x b v y l2 : closed b -> subs x b a :: l2 ⊦r lvar v y -> lfrl x a :: l2 ⊦r lvar v y
| rlfrl_right a x l : map fupz l ⊦r subs x (dvar 0) (fupz a) -> l ⊦r lfrl x a
where "l ⊦r a" := (rlprove l a).
Arguments rlidentity {_ _}, _ _.
Arguments rltop_right {_}, _.
Arguments rlwith_left1 [_ _ _ _ _] _, [_] _ [_ _ _] _, _ _ _ _ _ _.
Arguments rlwith_left2 [_ _ _ _ _] _, [_] _ [_ _ _] _, _ _ _ _ _ _.
Arguments rlwith_right [_ _ _] _ _, _ _ _ _ _.
Arguments rlmap_left [_ _ _ _ _ _] _ _, [_ _ _ _ _] _ _ _, _ _ _ _ _ _ _ _.
Arguments rlmap_right [_ _ _] _, _ _ _ _.
Arguments rlfrl_left [_ _ _ _ _ _] _ _, _ _ _ _ _ _ _.
Arguments rlfrl_right [_ _ _] _, [_] _ [_] _, _ _ _ _.

Fixpoint rlweight l b (pi : l ⊦r b) := S
match pi with
| rlidentity | rltop_right => 0
| rlwith_left1 pi1 | rlwith_left2 pi1 | rlmap_right pi1 | rlfrl_right pi1 | rlfrl_left _ pi1 => rlweight pi1
| rlwith_right pi1 pi2 => max (rlweight pi1) (rlweight pi2)
| rlmap_left pi1 pi2 => rlweight pi1 + rlweight pi2
end.

(** lift indexes above [k] in proof [pi] *)
Lemma rpup k l b : l ⊦r b -> map (fup k) l ⊦r fup k b.
Proof.
intro pi. induction pi in k |- *; try now constructor.
- change (map (fup k) [lvar v x]) with ([fup k (lvar v x)]). destruct (fup_lvar k v x) as [y ->].
  apply rlidentity.
- destruct (fup_lvar k v y) as [z Hz]. rewrite Hz.
  list_simpl. apply rlwith_left1.
  specialize (IHpi k). rewrite Hz in IHpi. list_simpl in IHpi. assumption.
- destruct (fup_lvar k v y) as [z Hz]. rewrite Hz.
  list_simpl. apply rlwith_left2.
  specialize (IHpi k). rewrite Hz in IHpi. list_simpl in IHpi. assumption.
- destruct (fup_lvar k v y) as [z Hz]. rewrite Hz.
  list_simpl. apply rlmap_left.
  + specialize (IHpi1 k). assumption.
  + specialize (IHpi2 k). rewrite Hz in IHpi2. list_simpl in IHpi2. assumption.
- cbn. apply rlmap_right.
  specialize (IHpi k). list_assumption.
- destruct (fup_lvar k v y) as [z Hz]. rewrite Hz.
  assert (closed (fup k b)) as e'.
  { rewrite freevars_fup. assumption. }
  list_simpl. apply (rlfrl_left e').
  specialize (IHpi k). rewrite Hz in IHpi. list_simpl in IHpi. rewrite fup_subs_com in IHpi. assumption.
- cbn. apply rlfrl_right.
  specialize (IHpi (S k)).
  rewrite fup_subs_com in IHpi. rewrite fup_fup_com in IHpi. cbn in IHpi.
  rewrite map_map in IHpi. rewrite map_map.
  rewrite (map_ext (fun x => fupz (fup k x)) (fun x => fup (S k) (fupz x))) by (symmetry; apply fup_fup_com).
  assumption.
Qed.



Lemma rlwith_left1_gen a b c l1 l2 : l1 ++ a :: l2 ⊦r c -> l1 ++ a ∧ b :: l2 ⊦r c.
Proof.
intro pi.
remember (l1 ++ a :: l2) as l eqn:Heql.
induction pi in l1, l2, a, b, Heql |- *; subst.
- decomp_list_eq Heql.
  apply rlwith_left1. constructor.
- constructor.
- decomp_list_eq Heql; subst.
  + list_simpl. apply rlwith_left1. rewrite app_comm_cons.
    apply IHpi. list_reflexivity.
  + apply rlwith_left1. apply rlwith_left1. assumption.
- decomp_list_eq Heql; subst.
  + list_simpl. apply rlwith_left2. rewrite app_comm_cons.
    apply IHpi. list_reflexivity.
  + apply rlwith_left1. apply rlwith_left2. assumption.
- apply rlwith_right.
  + apply IHpi1. reflexivity.
  + apply IHpi2. reflexivity.
- decomp_list_eq Heql; subst.
  + decomp_list_eq Heql0; subst; list_simpl.
    * cons2app. rewrite (app_assoc l), (app_assoc _ l1), <- app_comm_cons, app_nil_l.
      apply rlmap_left; [ | assumption ].
      list_simpl. apply IHpi1. reflexivity.
    * apply rlmap_left; [ assumption | ].
      rewrite app_comm_cons. apply IHpi2. reflexivity.
  + injection Heql as [= <- <-]. apply rlwith_left1. apply rlmap_left; assumption.
- apply rlmap_right.
  list_simpl. apply IHpi. list_reflexivity.
- decomp_list_eq Heql; subst.
  + list_simpl. apply (rlfrl_left e). rewrite app_comm_cons.
    apply IHpi. list_reflexivity.
  + apply rlwith_left1. apply (rlfrl_left e). assumption.
- apply rlfrl_right.
  list_simpl. apply IHpi. list_reflexivity.
Qed.

Lemma rlwith_left2_gen a b c l1 l2 : l1 ++ a :: l2 ⊦r c -> l1 ++ b ∧ a :: l2 ⊦r c.
Proof.
intro pi.
remember (l1 ++ a :: l2) as l eqn:Heql.
induction pi in l1, l2, a, b, Heql |- *; subst.
- decomp_list_eq Heql.
  apply rlwith_left2. constructor.
- constructor.
- decomp_list_eq Heql; subst.
  + list_simpl. apply rlwith_left1. rewrite app_comm_cons.
    apply IHpi. list_reflexivity.
  + apply rlwith_left2. apply rlwith_left1. assumption.
- decomp_list_eq Heql; subst.
  + list_simpl. apply rlwith_left2. rewrite app_comm_cons.
    apply IHpi. list_reflexivity.
  + apply rlwith_left2. apply rlwith_left2. assumption.
- apply rlwith_right.
  + apply IHpi1. reflexivity.
  + apply IHpi2. reflexivity.
- decomp_list_eq Heql; subst.
  + decomp_list_eq Heql0; subst; list_simpl.
    * cons2app. rewrite (app_assoc l), (app_assoc _ l1), <- app_comm_cons, app_nil_l.
      apply rlmap_left; [ | assumption ].
      list_simpl. apply IHpi1. reflexivity.
    * apply rlmap_left; [ assumption | ].
      rewrite app_comm_cons. apply IHpi2. reflexivity.
  + injection Heql as [= <- <-]. apply rlwith_left2. apply rlmap_left; assumption.
- apply rlmap_right.
  list_simpl. apply IHpi. list_reflexivity.
- decomp_list_eq Heql; subst.
  + list_simpl. apply (rlfrl_left e). rewrite app_comm_cons.
    apply IHpi. list_reflexivity.
  + apply rlwith_left2. apply (rlfrl_left e). assumption.
- apply rlfrl_right.
  list_simpl. apply IHpi. list_reflexivity.
Qed.

Lemma rlmap_left_gen a b c l1 l2 l3 : l2 ⊦r a -> l1 ++ b :: l3 ⊦r c -> l1 ++ b / a :: l2 ++ l3 ⊦r c.
Proof.
intros pi1 pi2.
remember (l1 ++ b :: l3) as l eqn:Heql.
induction pi2 in l1, l2, l3, a, b, pi1, Heql |- *; subst.
- decomp_list_eq Heql.
  apply rlmap_left; [ assumption | constructor ].
- constructor.
- decomp_list_eq Heql; subst.
  + list_simpl. apply rlwith_left1. rewrite app_comm_cons.
    apply IHpi2; [ assumption | list_reflexivity ].
  + apply (rlmap_left pi1). apply rlwith_left1. assumption.
- decomp_list_eq Heql; subst.
  + list_simpl. apply rlwith_left2. rewrite app_comm_cons.
    apply IHpi2; [ assumption | list_reflexivity ].
  + apply (rlmap_left pi1). apply rlwith_left2. assumption.
- apply rlwith_right.
  + apply IHpi2_1; [ assumption | reflexivity ].
  + apply IHpi2_2; [ assumption | reflexivity ].
- decomp_list_eq Heql; subst.
  + decomp_list_eq Heql0; subst; list_simpl.
    * cons2app. rewrite (app_assoc l), (app_assoc _ l2), (app_assoc _ l1), <- app_comm_cons, app_nil_l.
      apply rlmap_left; [ | assumption ].
      list_simpl. apply IHpi2_1; [ assumption | reflexivity ].
    * apply (rlmap_left pi2_1). rewrite app_comm_cons. now apply IHpi2_2.
  + injection Heql as [= <- <-]. apply (rlmap_left pi1). apply rlmap_left; assumption.
- apply rlmap_right.
  list_simpl. apply IHpi2; [ assumption | list_reflexivity ].
- decomp_list_eq Heql; subst.
  + list_simpl. apply (rlfrl_left e). rewrite app_comm_cons.
    apply IHpi2; [ assumption | list_reflexivity ].
  + apply (rlmap_left pi1). apply (rlfrl_left e). assumption.
- apply rlfrl_right.
  list_simpl. apply IHpi2; [ | list_reflexivity ].
  apply (rpup 0 pi1).
Qed.

Lemma rlfrl_left_gen a x b c l1 l2 : closed b ->
  l1 ++ subs x b a :: l2 ⊦r c -> l1 ++ lfrl x a :: l2 ⊦r c.
Proof.
intros Hc pi.
remember (l1 ++ subs x b a :: l2) as l eqn:Heql.
induction pi in l1, l2, a, b, Hc, Heql |- *; subst.
- decomp_list_eq Heql.
  apply (rlfrl_left Hc). rewrite Heql. constructor.
- constructor.
- decomp_list_eq Heql; subst.
  + list_simpl. apply rlwith_left1. rewrite app_comm_cons.
    apply (IHpi _ b); [ assumption | list_reflexivity ].
  + destruct a; destr_eq Heql.
    * apply (rlfrl_left Hc). rewrite <- Heql. apply rlwith_left1. assumption.
    * apply (rlfrl_left Hc). simpl subs. apply rlwith_left1. rewrite <- Heql. assumption.
- decomp_list_eq Heql; subst.
  + list_simpl. apply rlwith_left2. rewrite app_comm_cons.
    apply (IHpi _ b); [ assumption | list_reflexivity ].
  + destruct a; destr_eq Heql.
    * apply (rlfrl_left Hc). rewrite <- Heql. apply rlwith_left2. assumption.
    * apply (rlfrl_left Hc). simpl subs. apply rlwith_left2. rewrite <- H. assumption.
- apply rlwith_right.
  + apply (IHpi1 _ b); [ assumption | reflexivity ].
  + apply (IHpi2 _ b); [ assumption | reflexivity ].
- decomp_list_eq Heql; subst.
  + decomp_list_eq Heql0; subst; list_simpl.
    * cons2app. rewrite (app_assoc l), (app_assoc _ l1), <- app_comm_cons, app_nil_l.
      apply rlmap_left; [ | assumption ].
      list_simpl. apply (IHpi1 _ _ _ _ Hc). reflexivity.
    * apply (rlmap_left pi1). rewrite app_comm_cons. apply (IHpi2 _ _ _ _ Hc). reflexivity.
  + destruct a; destr_eq Heql; subst.
    * apply (rlfrl_left Hc). simpl subs; rewrite <- Heql. apply rlmap_left; assumption.
    * apply (rlfrl_left Hc). simpl subs. apply rlmap_left; assumption.
- apply rlmap_right.
  list_simpl. apply (IHpi _ b); [ assumption | list_reflexivity ].
- decomp_list_eq Heql; subst.
  + list_simpl. apply (rlfrl_left e). rewrite app_comm_cons.
    apply (IHpi _ b); [ assumption | list_reflexivity ].
  + destruct a; destr_eq Heql.
    * apply (rlfrl_left Hc). rewrite <- Heql. apply (rlfrl_left e). assumption.
    * apply (rlfrl_left Hc). simpl subs. apply (rlfrl_left e).
      rewrite <- H. subst. assumption.
- apply rlfrl_right.
  list_simpl. apply (IHpi _ (fupz b)).
  + rewrite freevars_fup. assumption.
  + list_simpl. rewrite fup_subs_com. reflexivity.
Qed.

Lemma rlidentity_gen a : [a] ⊦r a.
Proof.
remember (fsize a) as s eqn:Hs.
induction s as [s IH] in a, Hs |- * using (well_founded_induction_type lt_wf);
  destruct a as [ v x | a1 a2 | | a1 a2 | x a1 ]; inversion Hs;
  try now rewrite <- (app_nil_l _); constructor; rewrite <- (app_nil_l _); constructor; assumption.
- constructor. change ([a2 / a1] · a1) with ([] ++ a2 / a1 :: [a1] ++ []).
  cbn in Hs. apply rlmap_left_gen.
  + refine (IH _ _ _ eq_refl); lia.
  + refine (IH _ _ _ eq_refl); lia.
- constructor.
  + apply (rlwith_left1_gen _ _ nil).
    cbn in Hs. refine (IH _ _ _ eq_refl); lia.
  + apply (rlwith_left2_gen _ _ nil).
    cbn in Hs. refine (IH _ _ _ eq_refl); lia.
- apply rlfrl_right. cbn. apply (rlfrl_left_gen _ _ (dvar 0) nil).
  + reflexivity.
  + refine (IH _ _ _ eq_refl).
    cbn in Hs. rewrite fsize_subs_lvar, fsize_fup. lia.
Qed.



Lemma rlwith_left_inv a b v y l2 : a ∧ b :: l2 ⊦r lvar v y ->
  (a :: l2 ⊦r lvar v y) + (b :: l2 ⊦r lvar v y).
Proof.
intro pi. remember (a ∧ b :: l2) as l eqn:Heql. remember (lvar v y) as c eqn:Heqc.
destruct pi; (try now destr_eq Heqc); (try now decomp_list_eq Heql); subst;
  injection Heqc as [= -> ->]; injection Heql as [= -> -> <-]; [ left | right ]; assumption.
Qed.

Lemma rlmap_left_inv a b v y l1 : b / a :: l1 ⊦r lvar v y ->
  {'(l2, l3) & l1 = l2 ++ l3 & (l2 ⊦r a) * (b :: l3 ⊦r lvar v y) }.
Proof.
intro pi. remember (b / a :: l1) as l eqn:Heql. remember (lvar v y) as c eqn:Heqc.
destruct pi; (try now destr_eq Heqc); (try now decomp_list_eq Heql).
injection Heqc as [= -> ->]. injection Heql as [= -> -> <-].
exists (l2, l3); repeat split; assumption.
Qed.

Lemma rlfrl_left_inv a x v y l2 : lfrl x a :: l2 ⊦r lvar v y ->
  { b & subs x b a :: l2 ⊦r lvar v y & closed b }.
Proof.
intro pi. remember (lfrl x a :: l2) as l eqn:Heql. remember (lvar v y) as c eqn:Heqc.
destruct pi; (try now destr_eq Heqc); (try now decomp_list_eq Heql).
injection Heqc as [= -> ->]. injection Heql as [= -> -> <-].
exists b; assumption.
Qed.

Lemma lvar_left_inv l v x u y : lvar v x :: l ⊦r lvar u y -> l = [] /\ v = u /\ x = y.
Proof.
intro pi. remember (lvar v x :: l) as l0 eqn:Heql. remember (lvar u y) as c eqn:Heqc.
destruct pi; (try now destr_eq Heqc); (try now decomp_list_eq Heql).
injection Heqc as [= -> ->]. injection Heql as [= -> -> <-].
repeat split.
Qed.


(*
Lemma rlfrl_left_rev a x v y l1 l2 : l1 ++ lfrl x a :: l2 ⊦r lvar v y ->
  { b & l1 ++ subs x b a :: l2 ⊦r lvar v y & closed b }.

FALSE

[lvar v y / lfrl x (lwith a b); lfrl x (lwith b a)] ⊦r lvar v y
but not
[lvar v y / lfrl x (lwith a b); subs x d (lwith b a)] ⊦r lvar v y

*)


Lemma rlprove_lprove l a : l ⊦r a -> l ⊦ a.
Proof.
intro pi. induction pi; try now constructor.
- apply (@lwith_left1 _ _ _ nil). assumption.
- apply (@lwith_left2 _ _ _ nil). assumption.
- apply (@lmap_left _ _ _ nil); assumption.
- apply (@lfrl_left _ _ _ _ nil _ e IHpi).
Qed.

(* Proposition 9 *)
Lemma lprove_rlprove l a : l ⊦ a -> l ⊦r a.
Proof.
intro pi.
induction pi; (try now constructor).
- apply rlidentity_gen.
- apply rlwith_left1_gen. assumption.
- apply rlwith_left2_gen. assumption.
- apply rlmap_left_gen; assumption.
- apply (rlfrl_left_gen _ _ _ _ _ e IHpi).
Qed.

(* Proposition 10 *)
Lemma rlcut a b l1 l2 l3 :
  l2 ⊦r a -> l1 ++ a :: l3 ⊦r b -> l1 ++ l2 ++ l3 ⊦r b.
Proof. intros pi1%rlprove_lprove pi2%rlprove_lprove. apply lprove_rlprove, (lcut _ _ pi1 pi2). Qed.

Lemma rlsubst a b c l1 l2 : [a] ⊦r b -> l1 ++ b :: l2 ⊦r c -> l1 ++ a :: l2 ⊦r c.
Proof. intros pi1 pi2. apply (rlcut _ _ pi1 pi2). Qed.

Lemma rltrans b c l1 l2 : l1 ⊦r b -> b :: l2 ⊦r c -> l1 ++ l2 ⊦r c.
Proof. intros pi1 pi2. rewrite <- (app_nil_l _) in pi2. apply (rlcut _ _ pi1 pi2). Qed.






Section WithCut.

Variable rlcut : forall a b l1 l2 l3, l2 ⊦r a -> l1 ++ a :: l3 ⊦r b -> l1 ++ l2 ++ l3 ⊦r b.

Lemma left_gen c :
  ([c] ⊦r c)
* (forall a b l2, a :: l2 ⊦r c -> a ∧ b :: l2 ⊦r c)
* (forall a b l2, a :: l2 ⊦r c -> b ∧ a :: l2 ⊦r c)
* (forall a b l2 l3, l2 ⊦r a -> b :: l3 ⊦r c -> b / a :: l2 ++ l3 ⊦r c)
* (forall a x b l2, closed b -> subs x b a :: l2 ⊦r c -> lfrl x a :: l2 ⊦r c).
Proof using rlcut.
remember (fsize c) as s eqn:Hs.
induction s as [s IH0] in c, Hs |- * using (well_founded_induction_type lt_wf). subst.
assert (forall c', fsize c' < fsize c ->
  ([c'] ⊦r c') *
  (forall a b l2, a :: l2 ⊦r c' -> a ∧ b :: l2 ⊦r c') *
  (forall a b l2, a :: l2 ⊦r c' -> b ∧ a :: l2 ⊦r c') *
  (forall a b l2 l3, l2 ⊦r a -> b :: l3 ⊦r c' -> b / a :: l2 ++ l3 ⊦r c') *
  (forall a x b l2, closed b -> subs x b a :: l2 ⊦r c' -> ∀ x a :: l2 ⊦r c')) as IH.
{ intros. now apply (IH0 (fsize c')). }
clear IH0. destruct c as [ v x | c1 c2 | | c1 c2 | x c1 ];
  repeat split; intros; try now econstructor; try eassumption.
- constructor. change ([c2 / c1] · c1) with ([] ++ c2 / c1 :: [c1] ++ []).
  apply IH; [ | apply IH .. ]; cbn; lia.
- constructor. list_simpl.
  apply (snd (fst (fst (fst (IH c2 ltac:(cbn; lia)))))).
  apply (rlcut nil _ H).
  list_simpl. change ([c2 / c1; c1]) with ([] ++ c2 / c1 :: [c1] ++ []).
  apply IH; [ | apply IH .. ]; cbn; lia.
- constructor. list_simpl.
  apply IH; [ cbn; lia | ].
  apply (rlcut nil _ H).
  list_simpl. change ([c2 / c1; c1]) with ([] ++ c2 / c1 :: [c1] ++ []).
  apply IH; [ | apply IH .. ]; cbn; lia.
- constructor. list_simpl. apply IH; [ cbn; lia | assumption | ].
  apply (rlcut nil _ H0).
  list_simpl. change ([c2 / c1; c1]) with ([] ++ c2 / c1 :: [c1] ++ []).
  apply IH; [ | apply IH .. ]; cbn; lia.
- constructor. list_simpl. apply (snd (IH c2 ltac:(cbn; lia)) _ _ _ _ H).
  apply (rlcut nil _ H0).
  list_simpl. change ([c2 / c1; c1]) with ([] ++ c2 / c1 :: [c1] ++ []).
  apply IH; [ | apply IH .. ]; cbn; lia.
- constructor.
  + apply (snd (fst (fst (fst (IH c1 ltac:(cbn; lia)))))). apply IH. cbn. lia.
  + apply (snd (fst (fst (IH c2 ltac:(cbn; lia))))). apply IH. cbn. lia.
- constructor.
  + apply (snd (fst (fst (fst (IH c1 ltac:(cbn; lia)))))).
    rewrite <- (app_nil_r _). apply (rlcut nil nil H).
    apply (snd (fst (fst (fst (IH c1 ltac:(cbn; lia)))))). apply IH. cbn; lia.
  + apply (snd (fst (fst (fst (IH c2 ltac:(cbn; lia)))))).
    rewrite <- (app_nil_r _). apply (rlcut nil nil H).
    apply IH, IH; cbn; lia.
- constructor.
  + apply IH; [ cbn; lia | ].
    rewrite <- (app_nil_r _). apply (rlcut nil nil H).
    apply (snd (fst (fst (fst (IH c1 ltac:(cbn; lia)))))). apply IH. cbn; lia.
  + apply IH; [ cbn; lia | ].
    rewrite <- (app_nil_r _). apply (rlcut nil nil H).
    apply IH, IH; cbn; lia.
- constructor.
  + apply IH; [ cbn; lia | assumption | ].
    rewrite <- (app_nil_r _). apply (rlcut nil nil H0).
    apply (snd (fst (fst (fst (IH c1 ltac:(cbn; lia)))))). apply IH. cbn; lia.
  + apply IH; [ cbn; lia | assumption | ].
    rewrite <- (app_nil_r _). apply (rlcut nil nil H0).
    apply IH, IH; cbn; lia.
- constructor.
  + apply (snd (IH c1 ltac:(cbn; lia)) _ _ _ _ H).
    rewrite <- (app_nil_r _). apply (rlcut nil nil H0).
    apply (snd (fst (fst (fst (IH c1 ltac:(cbn; lia)))))). apply IH. cbn; lia.
  + apply (snd (IH c2 ltac:(cbn; lia)) _ _ _ _ H).
    rewrite <- (app_nil_r _). apply (rlcut nil nil H0).
    apply IH, IH; cbn; lia.
- constructor.
  apply (snd (IH (subs x (dvar 0) (fupz c1)) ltac:(cbn; rewrite fsize_subs_lvar, fsize_fup; lia))
                 _ _ (dvar 0)); [ reflexivity | apply IH ]. cbn. rewrite fsize_subs_lvar, fsize_fup. lia.
- constructor. cbn.
  apply (snd (fst (fst (fst (IH (subs x (dvar 0) (fupz c1))
           ltac:(cbn; rewrite fsize_subs_lvar, fsize_fup; lia)))))).
  rewrite <- (app_nil_r _). cons2app. eapply (rlcut nil nil).
  + apply (@rpup 0 (a :: l2)). eassumption.
  + cbn. apply (snd (IH (subs x (dvar 0) (fupz c1)) ltac:(cbn; rewrite fsize_subs_lvar, fsize_fup; lia))
                   _ _ (dvar 0)); [ reflexivity | ].
    apply IH. cbn. rewrite fsize_subs_lvar, fsize_fup. lia.
- constructor. cbn.
  apply (snd (fst (fst (IH (subs x (dvar 0) (fupz c1))
           ltac:(cbn; rewrite fsize_subs_lvar, fsize_fup; lia))))).
  rewrite <- (app_nil_r _). cons2app. eapply (rlcut nil nil).
  + apply (@rpup 0 (a :: l2)). eassumption.
  + cbn. apply (snd (IH (subs x (dvar 0) (fupz c1)) ltac:(cbn; rewrite fsize_subs_lvar, fsize_fup; lia))
                   _ _ (dvar 0)); [ reflexivity | ].
    apply IH. cbn. rewrite fsize_subs_lvar, fsize_fup. lia.
- constructor. cbn. rewrite map_app. apply IH; [ cbn; rewrite fsize_subs_lvar, fsize_fup; lia | | ].
  + apply rpup. assumption.
  + rewrite <- (app_nil_r _). cons2app. eapply (rlcut nil nil).
    * apply (@rpup 0 (b :: l3)). eassumption.
    * cbn. apply (snd (IH (subs x (dvar 0) (fupz c1)) ltac:(cbn; rewrite fsize_subs_lvar, fsize_fup; lia))
                     _ _ (dvar 0)); [ reflexivity | ].
      apply IH. cbn. rewrite fsize_subs_lvar, fsize_fup. lia.
- constructor. cbn.
  apply (snd (IH (subs x (dvar 0) (fupz c1)) ltac:(cbn; rewrite fsize_subs_lvar, fsize_fup; lia))
                     _ _ (fupz b)); [ rewrite freevars_fup; assumption | ].
  rewrite <- (app_nil_r _). cons2app. eapply (rlcut nil nil).
  + rewrite <- fup_subs_com. apply (@rpup 0 (_ :: l2)). eassumption.
  + cbn. apply (snd (IH (subs x (dvar 0) (fupz c1)) ltac:(cbn; rewrite fsize_subs_lvar, fsize_fup; lia))
                     _ _ (dvar 0)); [ reflexivity | ].
    apply IH. cbn. rewrite fsize_subs_lvar, fsize_fup. lia.
Qed.

End WithCut.






Notation nn a := (cst 0 / (cst 1 / a)).

Lemma fup_nn k a : fup k (nn a) = nn (fup k a).
Proof. induction a; auto. Qed.

Lemma notnot_left_var_inv a l v x : nn a :: l ⊦r lvar v x -> (l · a ⊦r cst 1) * (v = Lt) * (x = 0).
Proof.
intros [(l1, l2) -> [pi1 [-> [<- <-]]%lvar_left_inv]]%rlmap_left_inv.
list_simpl. split; [ split | ]; [ | repeat split .. ].
inversion pi1. subst. assumption.
Qed.

Lemma notnot_left_1_var_inv a l0 l v x : nn a :: map (fun z => nn z) l0 ++ l ⊦r lvar v x -> l0 = [].
Proof.
intros [[pi ->] ->]%notnot_left_var_inv.
destruct l0 as [ | b l0 ]; [ reflexivity | exfalso ].
apply notnot_left_var_inv in pi as [_ [=]].
Qed.

Lemma notnot_left_1_inv a l0 l b : nn a :: map (fun z => nn z) l0 ++ l ⊦r b -> (l0 = []) + ([ltop] ⊦r b).
Proof.
remember (fsize b) as n eqn:Hn.
induction n as [n IH] using (well_founded_induction_type lt_wf) in a, b, l0, l, Hn |- *. subst n. intro pi.
destruct b.
- apply notnot_left_1_var_inv in pi. left. assumption.
- inversion_clear pi.
  list_simpl in H. destruct (IH (fsize b2) ltac:(cbn; lia) _ _ _ _ eq_refl H); [ left; assumption | right ].
  constructor. list_simpl. rewrite <- (app_nil_r _). eapply rltrans; [ constructor | eassumption ].
- right. constructor.
- inversion_clear pi.
  destruct (IH (fsize b1) ltac:(cbn; lia) _ _ _ _ eq_refl H);
  destruct (IH (fsize b2) ltac:(cbn; lia) _ _ _ _ eq_refl H0); [ left; assumption .. | right ].
  now constructor.
- inversion_clear pi. list_simpl in H.
  replace (map fupz (map (fun z => nn z) l0)) with (map (fun z => nn z) (map fupz l0)) in H
    by (rewrite !map_map; apply map_ext, fup_nn).
  assert (fsize (subs n (dvar 0) (fupz b)) < fsize (∀ n b)) as Hs.
  { rewrite fsize_subs_lvar, fsize_fup. cbn. lia. }
  edestruct (IH (fsize (subs n (dvar 0) (fupz b))) Hs _ _ _ _ eq_refl H).
  + left. decomp_list_eq e. subst. reflexivity.
  + right. now constructor.
Qed.

Lemma notnot_unprov a : notT ([] ⊦r nn a).
Proof.
intro pi. inversion_clear pi.
list_simpl in H. apply rlmap_left_inv in H as [(l1, l2) Hl [pi1 pi2]].
decomp_list_eq Hl.
apply lvar_left_inv in pi2 as [_ [_ [=]]].
Qed.

Lemma ltop_notnot_unprov a : notT ([ltop] ⊦r nn a).
Proof.
intro pi. inversion_clear pi.
list_simpl in H. remember ([𝖳; cst 1 / a]) as l eqn:Hl. remember (cst 0) as S eqn:HS.
destruct H; (try now decomp_list_eq Hl); try now destr_eq HS.
Qed.

Lemma lmap_notnot_left_var_inv a b l0 v x : b / a :: map (fun z => nn z) l0 ⊦r lvar v x ->
  (([] ⊦r a) * (b :: map (fun z => nn z) l0 ⊦r lvar v x)) + ([ltop] ⊦r a) +
  {'(c, l) & l0 = c :: l & (b :: map (fun z => nn z) l ⊦r lvar v x) * ([nn c] ⊦r a) }.
Proof.
intros [(l1, l2) Hl [pi1 pi2]]%rlmap_left_inv.
decomp_list_eq Hl. subst.
destruct l1 as [ | c l1 ].
- left. left. split; assumption.
- cbn in pi1. rewrite <- (app_nil_r _), <- app_comm_cons in pi1.
  destruct (notnot_left_1_inv _ _ pi1) as [-> | pi0].
  + right. exists (c, l2); split; assumption.
  + left. right. assumption.
Qed.

Lemma notnot_notnot a b : [nn a] ⊦r nn b -> [a] ⊦r b.
Proof.
intro pi. inversion_clear pi.
apply rlmap_left_inv in H as [(l1, l2) Hl [pi1 pi2]].
decomp_list_eq Hl; subst.
- exfalso. apply lvar_left_inv in pi2 as [[=] _].
- clear pi2. inversion_clear pi1.
  apply rlmap_left_inv in H as [(l1, l2) Hl [pi1 pi2]].
  decomp_list_eq Hl; subst.
  + exfalso. apply lvar_left_inv in pi2 as [[=] _].
  + assumption.
Qed.

Lemma notnot_lmap_notnot_left_var_inv a b l0 v x : b / nn a :: map (fun z => nn z) l0 ⊦r lvar v x ->
  {'(c, l) & l0 = c :: l & (b :: map (fun z => nn z) l ⊦r lvar v x) * ([c] ⊦r a) }.
Proof.
intros [[[[]%notnot_unprov _] | []%ltop_notnot_unprov ]
       | [(c, l) -> [pi1 pi2%notnot_notnot]] ]%lmap_notnot_left_var_inv.
exists (c, l); [ reflexivity | split; assumption ].
Qed.




(** ****  WORK IN PROGRESS ****)


Inductive nn_lmap k : lform -> Type :=
| nnl_lvar v x : (v = Lt -> x <> k) -> nn_lmap k (lvar v x)
| nnl_ltop : nn_lmap k ltop
| nnl_lmap a b : (* nn_lmap a -> nn_lmap k b -> *) nn_lmap k (lmap (nn a) b)
| nnl_lwith a b : nn_lmap k a -> nn_lmap k b -> nn_lmap k (lwith a b)
| nnl_lfrl x a : nn_lmap k a -> nn_lmap k (lfrl x a).


(*
Lemma fold_subs L x a :
  fold_right (fun '(x, f) => subs x f) (∀ x a) L = ∀ x (fold_right (fun '(x, f) => subs x f) a L).
Proof.
induction L.
- reflexivity.
- cbn. destruct a0 as (y, g). rewrite IHL. reflexivity.
Qed.

Lemma nn_lmap_left k L c : nn_lmap k c -> ForallT (fun '(x, f) => closed f) L ->
  [fold_right (fun '(x, f) => subs x f) c L] ⊦r cst k ->
  { z & [fold_right (fun '(x, f) => lfrl x) c L] ⊦r lfrl z (var z) }.
Proof.
intros Hnn Hc pi.
remember (rlweight pi) as s eqn:Hs.
induction s as [s IH] using (well_founded_induction_type lt_wf) in c, L, Hnn, Hc, pi, Hs |- *. subst s.
remember [fold_right (fun '(x, f) => subs x f) c L] as l eqn:Hl.
remember (cst k) as e eqn:He.
destruct pi; destr_eq He; subst.
- clear IH Hc.
  destruct c.
  + induction L as [ | (x, f) L IHL].
    * cbn in Hl. injection Hl as [= <- <-]. inversion Hnn. now contradiction H0.
    * cbn in Hl. admit.
  + exfalso. clear - Hl.
    remember Lt as v eqn:Hv. clear Hv.
    induction L in v, k, Hl |- *; destr_eq Hl. destruct a as (x, f).
    remember (fold_right (fun '(x, f) => subs x f) (c2 / c1) L) as g.
    destruct g; try discriminate Hl.
    now eapply IHL.
  + exfalso. clear - Hl.
    remember Lt as v eqn:Hv. clear Hv.
    induction L in v, k, Hl |- *; destr_eq Hl. destruct a as (x, f).
    remember (fold_right (fun '(x, f) => subs x f) 𝖳 L) as g.
    destruct g; try discriminate Hl.
    now eapply IHL.
  + exfalso. clear - Hl.
    remember Lt as v eqn:Hv. clear Hv.
    induction L in v, k, Hl |- *; destr_eq Hl. destruct a as (x, f).
    remember (fold_right (fun '(x, f) => subs x f) (lwith c1 c2) L) as g.
    destruct g; try discriminate Hl.
    now eapply IHL.
  + exfalso. clear - Hl.
    remember Lt as v eqn:Hv. clear Hv.
    induction L in v, k, Hl |- *; destr_eq Hl. destruct a as (x, f).
    remember (fold_right (fun '(x, f) => subs x f) (lfrl n c) L) as g.
    destruct g; try discriminate Hl.
    now eapply IHL.
- decomp_list_eq Hl.
  admit.
- decomp_list_eq Hl.
  admit.
- decomp_list_eq Hl.
  admit.
- decomp_list_eq Hl.
  destruct c.
  + admit.
  + exfalso. clear - Hl. admit.
  + exfalso. clear - Hl. admit.
  + exfalso. clear - Hl. admit.
  + 



   

 cbn in Hl; try now destr_eq Hl.
  destruct c; destr_eq Hl; subst.
  + inversion Hc. contradiction H0; reflexivity.
  + destruct (Nat.eq_dec n y); destr_eq Hl. subst.
    exists y. apply rlidentity_gen.
- destruct c; cbn in Hl; try now decomp_list_eq Hl.
  + destruct c; decomp_list_eq Hl.
    destruct (Nat.eq_dec n y); destr_eq Hl. subst.
    exists y. apply rlidentity_gen.
  + decomp_list_eq Hl. injection Hl as [= -> ->].
    inversion_clear Hc.
    destruct (IH (rlweight pi) ltac:(cbn; lia) _ _ _ H Hb pi eq_refl) as [z Hz].
    exists z.
    rewrite <- (app_nil_r _). eapply rltrans; [ | eassumption ].
    apply rlfrl_right. cbn. refine (rlfrl_left_rev _ _ (dvar 0) nil _ eq_refl _).
    cbn. apply (rlwith_left1_rev _ _ nil). apply rlidentity_gen.
- destruct c; cbn in Hl; try now decomp_list_eq Hl.
  + destruct c; decomp_list_eq Hl.
    destruct (Nat.eq_dec n y); destr_eq Hl. subst.
    exists y. apply rlidentity_gen.
  + decomp_list_eq Hl. injection Hl as [= -> ->].
    inversion_clear Hc.
    destruct (IH (rlweight pi) ltac:(cbn; lia) _ _ _ H0 Hb pi eq_refl) as [z Hz].
    exists z.
    rewrite <- (app_nil_r _). eapply rltrans; [ | eassumption ].
    apply rlfrl_right. cbn. refine (rlfrl_left_rev _ _ (dvar 0) nil _ eq_refl _).
    cbn. apply (rlwith_left2_rev _ _ nil). apply rlidentity_gen.
- admit.
- destruct c; cbn in Hl; try now decomp_list_eq Hl.
  + destruct c; decomp_list_eq Hl.
    destruct (Nat.eq_dec n y); destr_eq Hl. subst.
    exists y. apply rlidentity_gen.
  + decomp_list_eq Hl. injection Hl as [= -> ->].
    inversion_clear Hc.


    destruct (Nat.eq_dec n y).
    * subst n.
      destruct (IH (rlweight pi) ltac:(cbn; lia) _ _ _ H e pi eq_refl) as [z Hz].
      exists z.
      cbn. apply (@rlfrl_left_rev _ _ (dvar 0) _ nil _ eq_refl).
      cbn. destruct (Nat.eq_dec y y); [ assumption | ].
      now contradiction n.
    * revert pi IH. cbn. rewrite (subs_subs_com y b n b0 c Hb e).
      destruct (Nat.eq_dec n y); [ now contradiction n0 | ].
      intros pi IH.

    destruct (IH (rlweight pi) ltac:(cbn; lia) _ H pi eq_refl) as [z Hz].
    exists z.
    rewrite <- (app_nil_r _). eapply rltrans; [ | eassumption ].
    apply rlfrl_right. cbn. refine (rlfrl_left_rev _ _ (dvar 0) nil _ eq_refl _).
    cbn. apply (rlwith_left1_rev _ _ nil). apply rlidentity_gen.

exfalso.
  injection Hl as [= <-].
  inversion Hc.
  apply H0; reflexivity.
- decomp_list_eq Hl.
  inversion Hc.
  destruct (IH (rlweight pi) ltac:(cbn; lia) _ H1 pi eq_refl) as [x Hx].
  exists x.
  inversion_clear Hx. apply rlfrl_right.
  cbn. cbn in H3. destruct (Nat.eq_dec x x).
  2:{ contradiction n. reflexivity. }
  rewrite <- (app_nil_l _). apply rlwith_left1. assumption.
- decomp_list_eq Hl.
  inversion Hc.
  destruct (IH (rlweight pi) ltac:(cbn; lia) _ H2 pi eq_refl) as [x Hx].
  exists x.
  inversion_clear Hx. apply rlfrl_right.
  cbn. cbn in H3. destruct (Nat.eq_dec x x).
  2:{ contradiction n. reflexivity. }
  rewrite <- (app_nil_l _). apply rlwith_left2. assumption.
- exfalso.
  decomp_list_eq Hl.
  inversion Hc. subst.
  apply (notnot_unprov pi1).
- decomp_list_eq Hl.
  inversion Hc. subst.
  destruct a.
  + destruct c; cbn in pi.
    * exfalso. clear - pi. apply lvar_left_left_inv in pi as [_ [[=] _]].
    * exfalso. clear - pi H0. apply lvar_left_left_inv in pi as [_ [_ ->]].
      inversion H0. apply H1; reflexivity.
    * cbn in *. destruct (Nat.eq_dec n x).
      -- subst n. exists x. apply rlidentity_gen.
      -- exfalso. clear - pi. apply lvar_left_left_inv in pi as [_ [[=] _]].
  + cbn in IH.
    assert (nn_lmap k (subs x b (a2 / a1))) as Hnn.
    { inversion H0. subst. constructor. }
    destruct (IH (rlweight pi) ltac:(cbn; lia) _ Hnn pi eq_refl) as [z Hz].
    exists z.
    inversion_clear Hz. apply rlfrl_right.
    cbn. cbn in H. destruct (Nat.eq_dec z z).
    2:{ contradiction n. reflexivity. }
    rewrite !fup_subs_com in H.
    rewrite <- (freevars_fup 0) in e.
    rewrite <- (app_nil_l _). apply (rlfrl_left e). assumption.
  + inversion pi; decomp_list_eq H.
  + cbn in pi. cbn in IH.
    remember [subs x b a1 ∧ subs x b a2] as f eqn:Hf.
    remember (cst k) as g eqn:Hg.
    inversion_clear H0.
    destruct pi; (try now destr_eq Hf); try now decomp_list_eq Hf.
    * decomp_list_eq Hf. injection Hf as [= -> ->]. injection Hg as [= -> ->].
      apply (nnl_lfrl x) in H.
      destruct (IH (rlweight (rlfrl_left e pi)) ltac:(cbn; lia) _ H (rlfrl_left e pi) eq_refl) as [z Hz].
      exists z.
      rewrite <- (app_nil_r _). eapply rltrans; [ | eassumption ].
      apply rlfrl_right. cbn. refine (rlfrl_left_rev _ _ (dvar 0) nil _ eq_refl _).
      cbn. apply (rlwith_left1_rev _ _ nil). apply rlidentity_gen.
    * decomp_list_eq Hf. injection Hf as [= -> ->]. injection Hg as [= -> ->].
      apply (nnl_lfrl x) in H1.
      destruct (IH (rlweight (rlfrl_left e pi)) ltac:(cbn; lia) _ H1 (rlfrl_left e pi) eq_refl) as [z Hz].
      exists z.
      rewrite <- (app_nil_r _). eapply rltrans; [ | eassumption ].
      apply rlfrl_right. cbn. refine (rlfrl_left_rev _ _ (dvar 0) nil _ eq_refl _).
      cbn. apply (rlwith_left2_rev _ _ nil). apply rlidentity_gen.
  + cbn in pi. cbn in IH.

    remember [∀ n (if Nat.eq_dec n x then a else subs x b a)] as f eqn:Hf.
    remember (cst k) as g eqn:Hg.
    inversion_clear H0.
    destruct pi; (try now destr_eq Hf); try now decomp_list_eq Hf.
    decomp_list_eq Hf. injection Hf as [= -> ->]. injection Hg as [= -> ->].

    destruct (Nat.eq_dec n x).
    * subst n.
      apply (nnl_lfrl x) in H.
      destruct (IH (rlweight (rlfrl_left e0 pi)) ltac:(cbn; lia) _ H (rlfrl_left e0 pi) eq_refl) as [z Hz].
      exists z.
      cbn. apply (@rlfrl_left_rev _ _ (dvar 0) _ nil _ eq_refl).
      cbn. destruct (Nat.eq_dec x x); [ assumption | ].
      now contradiction n.
    * revert pi IH. cbn. rewrite (subs_subs_com x b n b0 a e e0).
      destruct (Nat.eq_dec n x); [ now contradiction n0 | ].
      intros pi IH.


      apply (nnl_lfrl x) in H.
      destruct (IH (rlweight (@rlfrl_left _ _ _ _ _ nil _ e pi)) ltac:(cbn; lia) _
                   H (@rlfrl_left _ _ _ _ _ nil _ e pi) eq_refl) as [z Hz].


Qed.


Lemma nn_lmap_left k c : nn_lmap k c -> [c] ⊦r cst k -> { x & [c] ⊦r lfrl x (var x) }.
Proof.
intros Hc pi.
remember (rlweight pi) as s eqn:Hs.
induction s as [s IH] using (well_founded_induction_type lt_wf) in c, Hc, pi, Hs |- *. subst s.
remember [c] as l eqn:Hl.
remember (cst k) as b eqn:Hb.
destruct pi; destr_eq Hb; subst.
- exfalso.
  injection Hl as [= <-].
  inversion Hc.
  apply H0; reflexivity.
- decomp_list_eq Hl.
  inversion Hc.
  destruct (IH (rlweight pi) ltac:(cbn; lia) _ H1 pi eq_refl) as [x Hx].
  exists x.
  inversion_clear Hx. apply rlfrl_right.
  cbn. cbn in H3. destruct (Nat.eq_dec x x).
  2:{ contradiction n. reflexivity. }
  rewrite <- (app_nil_l _). apply rlwith_left1. assumption.
- decomp_list_eq Hl.
  inversion Hc.
  destruct (IH (rlweight pi) ltac:(cbn; lia) _ H2 pi eq_refl) as [x Hx].
  exists x.
  inversion_clear Hx. apply rlfrl_right.
  cbn. cbn in H3. destruct (Nat.eq_dec x x).
  2:{ contradiction n. reflexivity. }
  rewrite <- (app_nil_l _). apply rlwith_left2. assumption.
- exfalso.
  decomp_list_eq Hl.
  inversion Hc. subst.
  apply (notnot_unprov pi1).
- decomp_list_eq Hl.
  inversion Hc. subst.
  destruct a.
  + destruct c; cbn in pi.
    * exfalso. clear - pi. apply lvar_left_left_inv in pi as [_ [[=] _]].
    * exfalso. clear - pi H0. apply lvar_left_left_inv in pi as [_ [_ ->]].
      inversion H0. apply H1; reflexivity.
    * cbn in *. destruct (Nat.eq_dec n x).
      -- subst n. exists x. apply rlidentity_gen.
      -- exfalso. clear - pi. apply lvar_left_left_inv in pi as [_ [[=] _]].
  + cbn in IH.
    assert (nn_lmap k (subs x b (a2 / a1))) as Hnn.
    { inversion H0. subst. constructor. }
    destruct (IH (rlweight pi) ltac:(cbn; lia) _ Hnn pi eq_refl) as [z Hz].
    exists z.
    inversion_clear Hz. apply rlfrl_right.
    cbn. cbn in H. destruct (Nat.eq_dec z z).
    2:{ contradiction n. reflexivity. }
    rewrite !fup_subs_com in H.
    rewrite <- (freevars_fup 0) in e.
    rewrite <- (app_nil_l _). apply (rlfrl_left e). assumption.
  + inversion pi; decomp_list_eq H.
  + cbn in pi. cbn in IH.
    remember [subs x b a1 ∧ subs x b a2] as f eqn:Hf.
    remember (cst k) as g eqn:Hg.
    inversion_clear H0.
    destruct pi; (try now destr_eq Hf); try now decomp_list_eq Hf.
    * decomp_list_eq Hf. injection Hf as [= -> ->]. injection Hg as [= -> ->].
      apply (nnl_lfrl x) in H.
      destruct (IH (rlweight (rlfrl_left e pi)) ltac:(cbn; lia) _ H (rlfrl_left e pi) eq_refl) as [z Hz].
      exists z.
      rewrite <- (app_nil_r _). eapply rltrans; [ | eassumption ].
      apply rlfrl_right. cbn. refine (rlfrl_left_rev _ _ (dvar 0) nil _ eq_refl _).
      cbn. apply (rlwith_left1_rev _ _ nil). apply rlidentity_gen.
    * decomp_list_eq Hf. injection Hf as [= -> ->]. injection Hg as [= -> ->].
      apply (nnl_lfrl x) in H1.
      destruct (IH (rlweight (rlfrl_left e pi)) ltac:(cbn; lia) _ H1 (rlfrl_left e pi) eq_refl) as [z Hz].
      exists z.
      rewrite <- (app_nil_r _). eapply rltrans; [ | eassumption ].
      apply rlfrl_right. cbn. refine (rlfrl_left_rev _ _ (dvar 0) nil _ eq_refl _).
      cbn. apply (rlwith_left2_rev _ _ nil). apply rlidentity_gen.
  + cbn in pi. cbn in IH.

    remember [∀ n (if Nat.eq_dec n x then a else subs x b a)] as f eqn:Hf.
    remember (cst k) as g eqn:Hg.
    inversion_clear H0.
    destruct pi; (try now destr_eq Hf); try now decomp_list_eq Hf.
    decomp_list_eq Hf. injection Hf as [= -> ->]. injection Hg as [= -> ->].

    destruct (Nat.eq_dec n x).
    * subst n.
      apply (nnl_lfrl x) in H.
      destruct (IH (rlweight (rlfrl_left e0 pi)) ltac:(cbn; lia) _ H (rlfrl_left e0 pi) eq_refl) as [z Hz].
      exists z.
      cbn. apply (@rlfrl_left_rev _ _ (dvar 0) _ nil _ eq_refl).
      cbn. destruct (Nat.eq_dec x x); [ assumption | ].
      now contradiction n.
    * revert pi IH. cbn. rewrite (subs_subs_com x b n b0 a e e0).
      destruct (Nat.eq_dec n x); [ now contradiction n0 | ].
      intros pi IH.


      apply (nnl_lfrl x) in H.
      destruct (IH (rlweight (@rlfrl_left _ _ _ _ _ nil _ e pi)) ltac:(cbn; lia) _
                   H (@rlfrl_left _ _ _ _ _ nil _ e pi) eq_refl) as [z Hz].




    apply (nnl_lfrl x) in H.

cbn in pi.




    destruct (IH (rlweight (rlfrl_left e pi)) ltac:(cbn; lia) _ H (rlfrl_left e pi) eq_refl) as [z Hz].
    exists z.
    rewrite <- (app_nil_r _). eapply rltrans; [ | eassumption ].
    apply rlfrl_right. cbn. refine (rlfrl_left_rev _ _ (dvar 0) nil _ eq_refl _).
    cbn. apply (rlwith_left1_rev _ _ nil). apply rlidentity_gen.



  destruct (IH (rlweight pi) ltac:(cbn; lia) _ H0 pi eq_refl) as [x Hx].
  
apply rlfrl_left_left_inv in pi as [b pi Hb].

remember (fsize c) as n eqn:Hn.
induction n as [n IH] using (well_founded_induction_type lt_wf) in c, Hn |- *. subst n. intros Hc pi.
destruct c.
- exfalso.
  apply lvar_left_left_inv in pi as [_ [-> ->]].
  inversion Hc.
  apply H0; reflexivity.
- exfalso.
  inversion Hc. subst.
  apply rlmap_left_left_inv in pi as [(l1, l2) Hl [pi1 pi2]].
  decomp_list_eq Hl.
  apply (notnot_unprov pi1).
- exfalso. inversion pi; now decomp_list_eq H.
- inversion_clear Hc.
  apply rlwith_left_left_inv in pi as [pi | pi].
  + destruct (IH (fsize c1) ltac:(cbn; lia) _ eq_refl H pi) as [x Hx].
    exists x.
    inversion_clear Hx. apply rlfrl_right.
    cbn. cbn in H1. destruct (Nat.eq_dec x x).
    2:{ contradiction n. reflexivity. }
    rewrite <- (app_nil_l _). apply rlwith_left1. assumption.
  + destruct (IH (fsize c2) ltac:(cbn; lia) _ eq_refl H0 pi) as [x Hx].
    exists x.
    inversion_clear Hx. apply rlfrl_right.
    cbn. cbn in H1. destruct (Nat.eq_dec x x).
    2:{ contradiction n. reflexivity. }
    rewrite <- (app_nil_l _). apply rlwith_left2. assumption.
- apply rlfrl_left_left_inv in pi as [b pi Hb].

Qed.





Fixpoint rvars A :=
match A with
| lvar v x => [(v, x)]
| ltop => nil
| lmap B C => rvars C
| lwith B C => (rvars B) ++ (rvars C)
| lfrl X B => rvars B
end.

(*
Lemma notnot_left_inv a l b : nn a :: l ⊦r b -> inclT (rvars b) [(Lt, 0)].
Proof.
induction b in l |- *.
Qed.
*)

*)
