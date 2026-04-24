(* Negative Systems nIS* *)

From Stdlib Require Import PeanoNat Lia Wf_nat.
From OLlibs Require Import List_more.
From InterPT Require Export nformulas.
Export ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * nIS *)

Section nIS.

(** ** Rules *)

Reserved Notation "l ⊦ a" (at level 65, format "l  ⊦  a").
Inductive nlprove : list lform -> lform -> Type :=
| nlidentity a : [a] ⊦ a
| nltop_right l : l ⊦ 𝖳
| nlwith_left1 a b c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ a ∧ b :: l2 ⊦ c
| nlwith_left2 a b c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ b ∧ a :: l2 ⊦ c
| nlwith_right a b l : l ⊦ a -> l ⊦ b -> l ⊦ a ∧ b
| nlmap_left a b c d l3 : [d] ⊦ a -> b :: l3 ⊦ c -> b / a :: d :: l3 ⊦ c
| nlmap_right a b l : l · a ⊦ b -> l ⊦ b / a
| nlfrl_left a x b c l1 l2 : closed b -> l1 ++ subs x b a :: l2 ⊦ c -> l1 ++ lfrl x a :: l2 ⊦ c
| nlfrl_right a x l : map fupz l ⊦ subs x (dvar 0) (fupz a) -> l ⊦ lfrl x a
where "l ⊦ a" := (nlprove l a).
Arguments nlidentity {_} , _.
Arguments nltop_right {_}, _.
Arguments nlwith_left1 [_ _ _ _ _] _, [_] _ [_ _ _] _, _ _ _ _ _.
Arguments nlwith_left2 [_ _ _ _ _] _, [_] _ [_ _ _] _, _ _ _ _ _.
Arguments nlwith_right [_ _ _] _ _, _ _ _ _ _.
Arguments nlmap_left [_ _ _ _ _] _ _, _ _ _ _ _ _ _.
Arguments nlmap_right [_ _ _] _, _ _ _ _.
Arguments nlfrl_left [_ _ _ _ _ _ _] _, [_ _ _ _ _ _] _ _, _ _ _ _ _ _ _.
Arguments nlfrl_right [_ _ _] _, [_] _ [_] _, _ _ _ _.

(** *** Weight *)

Fixpoint nlweight l b (pi : l ⊦ b) := S
match pi with
| nlidentity | nltop_right => 0
| nlwith_left1 pi1 | nlwith_left2 pi1 | nlmap_right pi1 | nlfrl_right pi1 | nlfrl_left pi1 => nlweight pi1
| nlwith_right pi1 pi2 => max (nlweight pi1) (nlweight pi2)
| nlmap_left pi1 pi2 => nlweight pi1 + nlweight pi2
end.

(** substitutes [formula] [f] for index [k] in proof [pi] and decreases indexes above [k] *)
Lemma npsubs k f (Hc : closed f) l b (pi : l ⊦ b) :
  { pi' : map (nsubs k f) l ⊦  nsubs k f b | nlweight pi' = nlweight pi }.
Proof.
induction pi in k, f, Hc |- *;
  try (destruct (IHpi k f Hc) as [pi' Hs]);
  try (destruct (IHpi1 k f Hc) as [pi1' Hs1]);
  try (destruct (IHpi2 k f Hc) as [pi2' Hs2]).
- now exists nlidentity.
- now exists nltop_right.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (nlwith_left1 pi'). cbn. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (nlwith_left2 pi'). cbn. lia.
- exists (nlwith_right pi1' pi2'). cbn. lia.
- revert pi2' Hs2. list_simpl. intros pi2' Hs2.
  exists (nlmap_left pi1' pi2'). cbn in *. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (nlmap_right pi'). cbn. lia.
- cbn. rewrite <- Hs. clear Hs.
  revert pi'. list_simpl. rewrite nsubs_subs_com.
  + intro pi'.
    assert (closed (nsubs k f b)) as Hc' by (rewrite freevars_nsubs; assumption).
    exists (nlfrl_left Hc' pi'). cbn. lia.
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
  exists (nlfrl_right pi'). reflexivity.
Qed.

(** lift indexes above [k] in proof [pi] *)
Lemma npup k l b (pi : l ⊦ b) : { pi' : map (fup k) l ⊦ fup k b | nlweight pi' = nlweight pi }.
Proof.
induction pi in k |- *;
  try (destruct (IHpi k) as [pi' Hs]) ;
  try (destruct (IHpi1 k) as [pi1' Hs1]) ;
  try (destruct (IHpi2 k) as [pi2' Hs2]).
- now exists nlidentity.
- now exists nltop_right.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (nlwith_left1 pi'). cbn. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (nlwith_left2 pi'). cbn. lia.
- exists (nlwith_right pi1' pi2'). cbn. lia.
- revert pi2' Hs2. list_simpl. intros pi2' Hs2.
  exists (nlmap_left pi1' pi2'). cbn in *. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (nlmap_right pi'). cbn. lia.
- cbn. rewrite <- Hs. clear Hs.
  rewrite <- (freevars_fup k) in e.
  revert pi'. list_simpl. rewrite fup_subs_com.
  intro pi'.
  exists (nlfrl_left e pi'). reflexivity.
- clear pi' Hs.
  destruct (IHpi (S k)) as [pi' Hs].
  cbn. rewrite <- Hs. clear Hs.
  revert pi'.
  rewrite fup_subs_com. cbn. rewrite fup_fup_com.
  rewrite map_map.
  rewrite (map_ext (fun x => fup (S k) (fupz x)) (fun x => fupz (fup k x))) by apply fup_fup_com.
  rewrite <- map_map.
  intro pi'.
  exists (nlfrl_right pi'). reflexivity.
Qed.


(** ** Cut Elimination *)

#[local] Ltac solve_bp H := intros; apply H; rewrite ?length_app in *; cbn in *; lia.

#[local] Ltac solve_bp2 H :=
  let Hl := fresh in
  let d := fresh in
  let Hd := fresh in
  now intro Hl; destruct (H Hl) as [d Hd]; decomp_list_eq Hd; (try discriminate); eexists.

Lemma nlprove_trans_weight a b l1 l2 l3 (pi1 : l2 ⊦ a) (pi2 : l1 ++ a :: l3 ⊦ b) :
  (l1 <> [] -> length l2 = 1%nat) ->
  { pi' : l1 ++ l2 ++ l3 ⊦ b | nlweight pi' < nlweight pi1 + nlweight pi2 }.
Proof.
remember (nlweight pi1 + nlweight pi2) as q eqn:Hq.
intro Hbp0. assert (length l1 <> 0%nat ->  { c | l2 = [c] }) as Hbp.
{ intro H1. destruct l1 as [ | d l1 ]; [ now contradiction H1 | ].
  destruct l2 as [ | c [ | ? ? ] ]; destr_eq Hbp0; try now intros [=].
  exists c. reflexivity. } clear Hbp0.
induction q as [q IHq] using (well_founded_induction_type lt_wf) in a, b, l1, l2, l3, pi1, pi2, Hq, Hbp |- *.
subst q.
assert (forall a' b' l1' l2' l3' (pi1' : l2' ⊦ a') (pi2' : l1' ++ a' :: l3' ⊦ b'),
  nlweight pi1' + nlweight pi2' < nlweight pi1 + nlweight pi2 ->
  (length l1' <> 0%nat ->  { c | l2' = [c] }) ->
  {pi' : l1' ++ l2' ++ l3' ⊦ b' | nlweight pi' < nlweight pi1' + nlweight pi2'}) as IH.
{ intros a' b' l1' l2' l3' pi1' pi2' Hs Hbp'. exact (IHq _ Hs _ _ _ _ _ pi1' pi2' eq_refl Hbp'). } clear IHq.
remember (l1 ++ a :: l3) as l eqn:Hl.
destruct pi2; try subst l; cbn in IH.
- (* */nlidentity *)
  decomp_list_eq Hl. list_simpl. exists pi1. lia.
- (* */nltop_right *)
  exists nltop_right. cbn. destruct pi1; cbn; lia.
- (* */nlwith_left1 *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (nlwith_left1 pi). cbn. lia.
  + cbn. remember (a0 ∧ b) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (nlwith_left1 pi2). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (nlwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (nlwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (nlwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (nlwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_1 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
      exists pi'. cbn in *. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (nlwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      assert (l1 = []) as ->.
      { destruct l1; [ reflexivity | exfalso ].
        destruct Hbp; [ cbn; intro; lia | ]. discriminate. }
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (nlmap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (nlwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (nlfrl_left e pi'). cbn. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. rewrite !app_assoc. intros pi Hs.
    exists (nlwith_left1 pi). cbn. lia.
- (* */nlwith_left2 *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (nlwith_left2 pi). cbn. lia.
  + cbn. remember (b ∧ a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (nlwith_left2 pi2). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (nlwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (nlwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (nlwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (nlwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_2 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
      exists pi'. cbn in *. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (nlwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      assert (l1 = []) as ->.
      { destruct l1; [ reflexivity | exfalso ].
        destruct Hbp; [ cbn; intro; lia | ]. discriminate. }
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (nlmap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (nlwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (nlfrl_left e pi'). cbn. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. rewrite !app_assoc. intros pi Hs.
    exists (nlwith_left2 pi). cbn. lia.
- (* */nlwith_right *)
  destruct (IH _ _ _ _ _ pi1 pi2_1) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
  destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi2' Hs2]; [ cbn; lia | solve_bp Hbp | ].
  exists (nlwith_right pi1' pi2'). cbn. lia.
- (* */nlmap_left *)
  decomp_list_eq Hl; subst.
  + decomp_list_eq Hl0; subst.
    * revert pi2_2 IH. cbn. rewrite app_comm_cons, app_assoc. intros pi2_2 IH.
      destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi1' Hs']; [ lia | solve_bp Hbp | ].
      revert pi2_2 IH pi1' Hs'. list_simpl. intros pi2_2 IH pi1' Hs'.
      exists (nlmap_left pi2_1 pi1'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 pi2_1) as [pi1' Hs']; [ cbn; lia | solve_bp Hbp | ].
      revert pi2_2 IH pi1' Hs'. list_simpl. intros pi2_2 IH pi1' Hs'.
      destruct Hbp as [e ->]; [ cbn; lia | ].
      exists (nlmap_left pi1' pi2_2). cbn. lia.
  + cbn in Hl. injection Hl as [= <- <-].
    cbn. remember (b / a0) as e eqn:He.
    destruct pi1; destr_eq He; subst; cbn.
    * exists (nlmap_left pi2_1 pi2_2). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (nlmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (nlwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (nlmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (nlwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (nlmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (nlmap_left pi1_1 pi'). cbn. lia.
    * revert pi1 IH. list_simpl. intros pi1 IH.
      destruct (IH _ _ _ _ _ pi2_1 pi1) as [pi1' Hs1]; [ cbn; lia | | ].
      { intros _. exists d. reflexivity. }
      destruct (IH _ _ nil _ _ pi1' pi2_2) as [pi2' Hs2]; [ cbn in *; lia | | ].
      { intros []. reflexivity. }
      revert pi2' Hs2. list_simpl. intros pi2' Hs2.
      exists pi2'. cbn in *. lia.
    * destruct (IH _ _ nil _ _ pi1 (nlmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (nlfrl_left e pi'). cbn. lia.
- (* */nlmap_right *)
  revert pi2 IH. list_simpl. intros pi2 IH.
  destruct (IH _ _ _ _ _ pi1 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
  revert pi' Hs. clear. rewrite ? app_assoc, <- (app_assoc l1). intros pi' Hs.
  exists (nlmap_right pi'). cbn in *. lia.
- (* */nlfrl_left *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (nlfrl_left e pi). cbn. lia.
  + cbn. remember (∀ x a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (nlfrl_left e pi2). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (nlfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (nlwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (nlfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (nlwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (nlfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      assert (l1 = []) as ->.
      { destruct l1; [ reflexivity | exfalso ].
        destruct Hbp; [ cbn; intro; lia | ]. discriminate. }
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (nlmap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (nlfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (nlfrl_left e0 pi'). cbn. lia.
    * destruct (npsubs 0 _ e pi1) as [pi1' Hs'].
      revert pi1' Hs'. rewrite nsubs_subs_com by (rewrite e; intros []). cbn.
      rewrite map_map. rewrite (map_ext (fun x => nsubs 0 b (fupz x)) (fun x => x)) by apply nsubs_z_fup.
      rewrite nsubs_z_fup. rewrite map_id. intros pi1' Hs'.
      destruct (IH _ _ _ _ _ pi1' pi2) as [pi1'' Hs1]; [ cbn; lia | solve_bp Hbp | ].
      exists pi1''. cbn in *. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. rewrite !app_assoc. intros pi Hs.
    exists (nlfrl_left e pi). cbn. lia.
- (* */nlfrl_right *)
  revert pi2 IH. cbn. rewrite (map_app fupz l1 (a :: l3)). cbn. intros pi2 IH.
  destruct (npup 0 pi1) as [pi1' Hs1].
  destruct (IH _ _ _ _ _ pi1' pi2) as [pi' Hs]; [ cbn; lia | | ].
  { intro Hl1. rewrite length_map in Hl1. destruct (Hbp Hl1) as [d ->]. exists (fupz d). reflexivity. }
  revert pi' Hs. rewrite <- !map_app. intros pi' Hs.
  exists (nlfrl_right pi'). cbn. lia.
Qed.

Lemma nlcut a b l1 l2 l3 : (l1 <> [] -> length l2 = 1%nat) ->
  l2 ⊦ a -> l1 ++ a :: l3 ⊦ b -> l1 ++ l2 ++ l3 ⊦ b.
Proof. intros HS pi1 pi2. destruct (nlprove_trans_weight _ pi1 pi2 HS) as [pi _]. exact pi. Qed.

Lemma nlsubst a b c l1 l2 : [a] ⊦ b -> l1 ++ b :: l2 ⊦ c -> l1 ++ a :: l2 ⊦ c.
Proof. intros pi1 pi2. refine (nlcut _ _ pi1 pi2). intros _. reflexivity. Qed.

Lemma nltrans b c l1 l2 : l1 ⊦ b -> b :: l2 ⊦ c -> l1 ++ l2 ⊦ c.
Proof. intros pi1 pi2. rewrite <- (app_nil_l _) in pi2. refine (nlcut _ _ pi1 pi2). intros []. reflexivity. Qed.

End nIS.


(** * nISₕ *)

Section nISh.

(** ** Rules *)

Reserved Notation "l ⊦ a" (at level 65, format "l  ⊦  a").
Inductive hlprove : list lform -> lform -> Type :=
| hlidentity a : [a] ⊦ a
| hltop_right l : l ⊦ 𝖳
| hlwith_left1 a b c l2 : a :: l2 ⊦ c -> a ∧ b :: l2 ⊦ c
| hlwith_left2 a b c l2 : a :: l2 ⊦ c -> b ∧ a :: l2 ⊦ c
| hlwith_right a b l : l ⊦ a -> l ⊦ b -> l ⊦ a ∧ b
| hlmap_left a b c d l3 : [d] ⊦ a -> b :: l3 ⊦ c -> b / a :: d :: l3 ⊦ c
| hlmap_right a b l : l · a ⊦ b -> l ⊦ b / a
| hlfrl_left a x b c l2 : closed b -> subs x b a :: l2 ⊦ c -> lfrl x a :: l2 ⊦ c
| hlfrl_right a x l : map fupz l ⊦ subs x (dvar 0) (fupz a) -> l ⊦ lfrl x a
where "l ⊦ a" := (hlprove l a).
Arguments hlidentity {_} , _.
Arguments hltop_right {_}, _.
Arguments hlwith_left1 [_ _ _ _] _, [_] _ [_ _] _, _ _ _ _.
Arguments hlwith_left2 [_ _ _ _] _, [_] _ [_ _] _, _ _ _ _.
Arguments hlwith_right [_ _ _] _ _, _ _ _ _ _.
Arguments hlmap_left [_ _ _ _ _] _ _, _ _ _ _ _ _ _.
Arguments hlmap_right [_ _ _] _, _ _ _ _.
Arguments hlfrl_left [_ _ _ _ _ _] _, [_ _ _ _ _] _ _, _ _ _ _ _ _.
Arguments hlfrl_right [_ _ _] _, [_] _ [_] _, _ _ _ _.

(** *** Weight *)

Fixpoint hlweight l b (pi : l ⊦ b) := S
match pi with
| hlidentity | hltop_right => 0
| hlwith_left1 pi1 | hlwith_left2 pi1 | hlmap_right pi1 | hlfrl_right pi1 | hlfrl_left pi1 => hlweight pi1
| hlwith_right pi1 pi2 => max (hlweight pi1) (hlweight pi2)
| hlmap_left pi1 pi2 => hlweight pi1 + hlweight pi2
end.

(** substitutes [formula] [f] for index [k] in proof [pi] and decreases indexes above [k] *)
Lemma hpsubs k f (Hc : closed f) l b (pi : l ⊦ b) :
  { pi' : map (nsubs k f) l ⊦  nsubs k f b | hlweight pi' = hlweight pi }.
Proof.
induction pi in k, f, Hc |- *;
  try (destruct (IHpi k f Hc) as [pi' Hs]);
  try (destruct (IHpi1 k f Hc) as [pi1' Hs1]);
  try (destruct (IHpi2 k f Hc) as [pi2' Hs2]).
- now exists hlidentity.
- now exists hltop_right.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (hlwith_left1 pi'). cbn. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (hlwith_left2 pi'). cbn. lia.
- exists (hlwith_right pi1' pi2'). cbn. lia.
- revert pi2' Hs2. list_simpl. intros pi2' Hs2.
  exists (hlmap_left pi1' pi2'). cbn in *. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (hlmap_right pi'). cbn. lia.
- cbn. rewrite <- Hs. clear Hs.
  revert pi'. list_simpl. rewrite nsubs_subs_com.
  + intro pi'.
    assert (closed (nsubs k f b)) as Hc' by (rewrite freevars_nsubs; assumption).
    exists (hlfrl_left Hc' pi'). cbn. lia.
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
  exists (hlfrl_right pi'). reflexivity.
Qed.

(** lift indexes above [k] in proof [pi] *)
Lemma hpup k l b (pi : l ⊦ b) : { pi' : map (fup k) l ⊦ fup k b | hlweight pi' = hlweight pi }.
Proof.
induction pi in k |- *;
  try (destruct (IHpi k) as [pi' Hs]) ;
  try (destruct (IHpi1 k) as [pi1' Hs1]) ;
  try (destruct (IHpi2 k) as [pi2' Hs2]).
- now exists hlidentity.
- now exists hltop_right.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (hlwith_left1 pi'). cbn. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (hlwith_left2 pi'). cbn. lia.
- exists (hlwith_right pi1' pi2'). cbn. lia.
- revert pi2' Hs2. list_simpl. intros pi2' Hs2.
  exists (hlmap_left pi1' pi2'). cbn in *. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (hlmap_right pi'). cbn. lia.
- cbn. rewrite <- Hs. clear Hs.
  rewrite <- (freevars_fup k) in e.
  revert pi'. list_simpl. rewrite fup_subs_com.
  intro pi'.
  exists (hlfrl_left e pi'). reflexivity.
- clear pi' Hs.
  destruct (IHpi (S k)) as [pi' Hs].
  cbn. rewrite <- Hs. clear Hs.
  revert pi'.
  rewrite fup_subs_com. cbn. rewrite fup_fup_com.
  rewrite map_map.
  rewrite (map_ext (fun x => fup (S k) (fupz x)) (fun x => fupz (fup k x))) by apply fup_fup_com.
  rewrite <- map_map.
  intro pi'.
  exists (hlfrl_right pi'). reflexivity.
Qed.


(** ** Cut Elimination *)

#[local] Ltac solve_bp H := intros; apply H; rewrite ?length_app in *; cbn in *; lia.

#[local] Ltac solve_bp2 H :=
  let Hl := fresh in
  let d := fresh in
  let Hd := fresh in
  now intro Hl; destruct (H Hl) as [d Hd]; decomp_list_eq Hd; (try discriminate); eexists.

Lemma hlprove_trans_weight a b l1 l2 l3 (pi1 : l2 ⊦ a) (pi2 : l1 ++ a :: l3 ⊦ b) :
  (l1 <> [] -> length l2 = 1%nat) ->
  { pi' : l1 ++ l2 ++ l3 ⊦ b | hlweight pi' < hlweight pi1 + hlweight pi2 }.
Proof.
remember (hlweight pi1 + hlweight pi2) as q eqn:Hq.
intro Hbp0. assert (length l1 <> 0%nat ->  { c | l2 = [c] }) as Hbp.
{ intro H1. destruct l1 as [ | d l1 ]; [ now contradiction H1 | ].
  destruct l2 as [ | c [ | ? ? ] ]; destr_eq Hbp0; try now intros [=].
  exists c. reflexivity. } clear Hbp0.
induction q as [q IHq] using (well_founded_induction_type lt_wf) in a, b, l1, l2, l3, pi1, pi2, Hq, Hbp |- *.
subst q.
assert (forall a' b' l1' l2' l3' (pi1' : l2' ⊦ a') (pi2' : l1' ++ a' :: l3' ⊦ b'),
  hlweight pi1' + hlweight pi2' < hlweight pi1 + hlweight pi2 ->
  (length l1' <> 0%nat ->  { c | l2' = [c] }) ->
  {pi' : l1' ++ l2' ++ l3' ⊦ b' | hlweight pi' < hlweight pi1' + hlweight pi2'}) as IH.
{ intros a' b' l1' l2' l3' pi1' pi2' Hs Hbp'. exact (IHq _ Hs _ _ _ _ _ pi1' pi2' eq_refl Hbp'). } clear IHq.
remember (l1 ++ a :: l3) as l eqn:Hl.
destruct pi2; try subst l; cbn in IH.
- (* */hlidentity *)
  decomp_list_eq Hl. list_simpl. exists pi1. lia.
- (* */hltop_right *)
  exists hltop_right. cbn. destruct pi1; cbn; lia.
- (* */hlwith_left1 *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (hlwith_left1 pi). cbn. lia.
  + cbn. remember (a0 ∧ b) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (hlwith_left1 pi2). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (hlwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (hlwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_1 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
      exists pi'. cbn in *. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (hlwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlmap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (hlwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlfrl_left e pi'). cbn. lia.
- (* */hlwith_left2 *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (hlwith_left2 pi). cbn. lia.
  + cbn. remember (b ∧ a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (hlwith_left2 pi2). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (hlwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (hlwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_2 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
      exists pi'. cbn in *. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (hlwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlmap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (hlwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlfrl_left e pi'). cbn. lia.
- (* */hlwith_right *)
  destruct (IH _ _ _ _ _ pi1 pi2_1) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
  destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi2' Hs2]; [ cbn; lia | solve_bp Hbp | ].
  exists (hlwith_right pi1' pi2'). cbn. lia.
- (* */hlmap_left *)
  decomp_list_eq Hl; subst.
  + decomp_list_eq Hl0; subst.
    * revert pi2_2 IH. cbn. rewrite app_comm_cons, app_assoc. intros pi2_2 IH.
      destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi1' Hs']; [ lia | solve_bp Hbp | ].
      revert pi2_2 IH pi1' Hs'. list_simpl. intros pi2_2 IH pi1' Hs'.
      exists (hlmap_left pi2_1 pi1'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 pi2_1) as [pi1' Hs']; [ cbn; lia | solve_bp Hbp | ].
      revert pi2_2 IH pi1' Hs'. list_simpl. intros pi2_2 IH pi1' Hs'.
      destruct Hbp as [e ->]; [ cbn; lia | ].
      exists (hlmap_left pi1' pi2_2). cbn. lia.
  + cbn in Hl. injection Hl as [= <- <-].
    cbn. remember (b / a0) as e eqn:He.
    destruct pi1; destr_eq He; subst; cbn.
    * exists (hlmap_left pi2_1 pi2_2). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (hlmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (hlmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (hlmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlmap_left pi1_1 pi'). cbn. lia.
    * revert pi1 IH. list_simpl. intros pi1 IH.
      destruct (IH _ _ _ _ _ pi2_1 pi1) as [pi1' Hs1]; [ cbn; lia | | ].
      { intros _. exists d. reflexivity. }
      destruct (IH _ _ nil _ _ pi1' pi2_2) as [pi2' Hs2]; [ cbn in *; lia | | ].
      { intros []. reflexivity. }
      revert pi2' Hs2. list_simpl. intros pi2' Hs2.
      exists pi2'. cbn in *. lia.
    * destruct (IH _ _ nil _ _ pi1 (hlmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlfrl_left e pi'). cbn. lia.
- (* */hlmap_right *)
  revert pi2 IH. list_simpl. intros pi2 IH.
  destruct (IH _ _ _ _ _ pi1 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
  revert pi' Hs. clear. rewrite ? app_assoc, <- (app_assoc l1). intros pi' Hs.
  exists (hlmap_right pi'). cbn in *. lia.
- (* */hlfrl_left *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (hlfrl_left e pi). cbn. lia.
  + cbn. remember (∀ x a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (hlfrl_left e pi2). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (hlfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (hlfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (hlfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlmap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (hlfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (hlfrl_left e0 pi'). cbn. lia.
    * destruct (hpsubs 0 _ e pi1) as [pi1' Hs'].
      revert pi1' Hs'. rewrite nsubs_subs_com by (rewrite e; intros []). cbn.
      rewrite map_map. rewrite (map_ext (fun x => nsubs 0 b (fupz x)) (fun x => x)) by apply nsubs_z_fup.
      rewrite nsubs_z_fup. rewrite map_id. intros pi1' Hs'.
      destruct (IH _ _ nil _ _ pi1' pi2) as [pi1'' Hs1]; [ cbn; lia | solve_bp Hbp | ].
      exists pi1''. cbn in *. lia.
- (* */hlfrl_right *)
  revert pi2 IH. cbn. rewrite (map_app fupz l1 (a :: l3)). cbn. intros pi2 IH.
  destruct (hpup 0 pi1) as [pi1' Hs1].
  destruct (IH _ _ _ _ _ pi1' pi2) as [pi' Hs]; [ cbn; lia | | ].
  { intro Hl1. rewrite length_map in Hl1. destruct (Hbp Hl1) as [d ->]. exists (fupz d). reflexivity. }
  revert pi' Hs. rewrite <- !map_app. intros pi' Hs.
  exists (hlfrl_right pi'). cbn. lia.
Qed.

Lemma hlcut a b l1 l2 l3 : (l1 <> [] -> length l2 = 1%nat) ->
  l2 ⊦ a -> l1 ++ a :: l3 ⊦ b -> l1 ++ l2 ++ l3 ⊦ b.
Proof. intros HS pi1 pi2. destruct (hlprove_trans_weight _ pi1 pi2 HS) as [pi _]. exact pi. Qed.

Lemma hlsubst a b c l1 l2 : [a] ⊦ b -> l1 ++ b :: l2 ⊦ c -> l1 ++ a :: l2 ⊦ c.
Proof. intros pi1 pi2. refine (hlcut _ _ pi1 pi2). intros _. reflexivity. Qed.

Lemma hltrans b c l1 l2 : l1 ⊦ b -> b :: l2 ⊦ c -> l1 ++ l2 ⊦ c.
Proof. intros pi1 pi2. rewrite <- (app_nil_l _) in pi2. refine (hlcut _ _ pi1 pi2). intros []. reflexivity. Qed.

(** ** Admissible rules *)

Lemma hlwith_left1_gen a b c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ a ∧ b :: l2 ⊦ c.
Proof. intro pi. refine (hlsubst _ _ _ pi). apply hlwith_left1, hlidentity. Qed.

Lemma hlwith_left2_gen a b c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ b ∧ a :: l2 ⊦ c.
Proof. intro pi. refine (hlsubst _ _ _ pi). apply hlwith_left2, hlidentity. Qed.

Lemma hlfrl_left_gen a x b c l1 l2 : closed b -> l1 ++ subs x b a :: l2 ⊦ c -> l1 ++ lfrl x a :: l2 ⊦ c.
Proof. intros Hc pi. refine (hlsubst _ _ _ pi). apply (@hlfrl_left _ _ _ _ _ Hc), hlidentity. Qed.

(** ** Equivalence with nIS *)

Lemma nish_nis l a : l ⊦ a -> nlprove l a.
Proof.
intro pi. induction pi; try now constructor.
- apply (nlwith_left1 _ _ nil). assumption.
- apply (nlwith_left2 _ _ nil). assumption.
- apply (nlfrl_left _ _ _ nil _ e). assumption.
Qed.

Lemma nis_nish l a : nlprove l a -> l ⊦ a.
Proof.
intros pi. induction pi; try now constructor.
- apply hlwith_left1_gen. assumption.
- apply hlwith_left2_gen. assumption.
- apply (hlfrl_left_gen _ _ _ _ _ e). assumption.
Qed.

End nISh.


(** * nIS₁ *)

(** ** Rules *)

Reserved Notation "l ⊦ a" (at level 65, format "l  ⊦  a").
Inductive lprove : list lform -> lform -> Type :=
| lidentity a : [a] ⊦ a
| ltop_right d l : d :: l ⊦ 𝖳
| lwith_left1 a b c l2 : a :: l2 ⊦ c -> a ∧ b :: l2 ⊦ c
| lwith_left2 a b c l2 : a :: l2 ⊦ c -> b ∧ a :: l2 ⊦ c
| lwith_right a b l : l ⊦ a -> l ⊦ b -> l ⊦ a ∧ b
| lmap_left a b c d l3 : [d] ⊦ a -> b :: l3 ⊦ c -> b / a :: d :: l3 ⊦ c
| lmap_right a b d l : d :: l · a ⊦ b -> d :: l ⊦ b / a
| lfrl_left a x b c l2 : closed b -> subs x b a :: l2 ⊦ c -> lfrl x a :: l2 ⊦ c
| lfrl_right a x l : map fupz l ⊦ subs x (dvar 0) (fupz a) -> l ⊦ lfrl x a
where "l ⊦ a" := (lprove l a).
Arguments lidentity {_} , _.
Arguments ltop_right {_ _}, _ _.
Arguments lwith_left1 [_ _ _ _] _, [_] _ [_ _] _, _ _ _ _ _.
Arguments lwith_left2 [_ _ _ _] _, [_] _ [_ _] _, _ _ _ _ _.
Arguments lwith_right [_ _ _] _ _, _ _ _ _ _.
Arguments lmap_left [_ _ _ _ _] _ _, _ _ _ _ _ _ _.
Arguments lmap_right [_ _ _ _] _, _ _ _ _ _.
Arguments lfrl_left [_ _ _ _ _ _] _, [_ _ _ _ _] _ _, _ _ _ _ _ _.
Arguments lfrl_right [_ _ _] _, [_] _ [_] _, _ _ _ _.

Lemma lprove_left l a : l ⊦ a -> l <> nil.
Proof. intro pi. induction pi; try intros [=]; auto. subst. apply IHpi. reflexivity. Qed.


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
  exists (lmap_left pi1' pi2'). cbn in *. lia.
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
  exists (lmap_left pi1' pi2'). cbn in *. lia.
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


(** ** Cut Elimination *)

Ltac solve_bp H := intros; apply H; rewrite ?length_app in *; cbn in *; lia.

Ltac solve_bp2 H :=
  let Hl := fresh in
  let d := fresh in
  let Hd := fresh in
  now intro Hl; destruct (H Hl) as [d Hd]; decomp_list_eq Hd; (try discriminate); eexists.

Lemma lprove_trans_weight a b l1 l2 l3 (pi1 : l2 ⊦ a) (pi2 : l1 ++ a :: l3 ⊦ b) :
  (l1 <> [] -> length l2 = 1%nat) ->
  { pi' : l1 ++ l2 ++ l3 ⊦ b | lweight pi' < lweight pi1 + lweight pi2 }.
Proof.
remember (lweight pi1 + lweight pi2) as q eqn:Hq.
intro Hbp0. assert (length l1 <> 0%nat ->  { c | l2 = [c] }) as Hbp.
{ intro H1. destruct l1 as [ | d l1 ]; [ now contradiction H1 | ].
  destruct l2 as [ | c [ | ? ? ] ]; destr_eq Hbp0; try now intros [=].
  exists c. reflexivity. } clear Hbp0.
induction q as [q IHq] using (well_founded_induction_type lt_wf) in a, b, l1, l2, l3, pi1, pi2, Hq, Hbp |- *.
subst q.
assert (forall a' b' l1' l2' l3' (pi1' : l2' ⊦ a') (pi2' : l1' ++ a' :: l3' ⊦ b'),
  lweight pi1' + lweight pi2' < lweight pi1 + lweight pi2 ->
  (length l1' <> 0%nat ->  { c | l2' = [c] }) ->
  {pi' : l1' ++ l2' ++ l3' ⊦ b' | lweight pi' < lweight pi1' + lweight pi2'}) as IH.
{ intros a' b' l1' l2' l3' pi1' pi2' Hs Hbp'. exact (IHq _ Hs _ _ _ _ _ pi1' pi2' eq_refl Hbp'). } clear IHq.
remember (l1 ++ a :: l3) as l eqn:Hl.
destruct pi2; try subst l; cbn in IH.
- (* */identity *)
  decomp_list_eq Hl. list_simpl. exists pi1. lia.
- (* */ltop_right *)
  assert (Hl2 := lprove_left pi1).
  destruct l2 as [ | f l2 ]; [ now contradiction Hl2 | ].
  destruct l1 as [ | e l1 ].
  + exists (ltop_right f _). cbn. destruct pi1; cbn; lia.
  + exists (ltop_right e _). cbn. destruct pi1; cbn; lia.
- (* */lwith_left1 *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (lwith_left1 pi). cbn. lia.
  + cbn. remember (a0 ∧ b) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lwith_left1 pi2). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_1 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
      exists pi'. cbn in *. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
- (* */lwith_left2 *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (lwith_left2 pi). cbn. lia.
  + cbn. remember (b ∧ a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lwith_left2 pi2). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_2 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
      exists pi'. cbn in *. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
- (* */lwith_right *)
  destruct (IH _ _ _ _ _ pi1 pi2_1) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
  destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi2' Hs2]; [ cbn; lia | solve_bp Hbp | ].
  exists (lwith_right pi1' pi2'). cbn. lia.
- (* */lmap_left *)
  decomp_list_eq Hl; subst.
  + decomp_list_eq Hl0; subst.
    * revert pi2_2 IH. cbn. rewrite app_comm_cons, app_assoc. intros pi2_2 IH.
      destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi1' Hs']; [ lia | solve_bp Hbp | ].
      revert pi2_2 IH pi1' Hs'. list_simpl. intros pi2_2 IH pi1' Hs'.
      exists (lmap_left pi2_1 pi1'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 pi2_1) as [pi1' Hs']; [ cbn; lia | solve_bp Hbp | ].
      revert pi2_2 IH pi1' Hs'. list_simpl. intros pi2_2 IH pi1' Hs'.
      destruct Hbp as [e ->]; [ cbn; lia | ].
      exists (lmap_left pi1' pi2_2). cbn. lia.
  + cbn in Hl. injection Hl as [= <- <-].
    cbn. remember (b / a0) as e eqn:He.
    destruct pi1; destr_eq He; subst; cbn.
    * exists (lmap_left pi2_1 pi2_2). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (lmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * revert pi1 IH. list_simpl. rewrite app_comm_cons. intros pi1 IH.
      destruct (IH _ _ _ _ _ pi2_1 pi1) as [pi1' Hs1]; [ cbn; lia | | ].
      { intros _. exists d. reflexivity. }
      destruct (IH _ _ nil _ _ pi1' pi2_2) as [pi2' Hs2]; [ cbn in *; lia | | ].
      { intros []. reflexivity. }
      revert pi2' Hs2. list_simpl. intros pi2' Hs2.
      exists pi2'. cbn in *. lia.
    * destruct (IH _ _ nil _ _ pi1 (lmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
- (* */lmap_right *)
  revert pi2 IH. list_simpl. rewrite app_comm_cons, Hl, <- app_assoc, <- app_comm_cons. intros pi2 IH.
  destruct (IH _ _ _ _ _ pi1 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
  revert pi' Hs. clear. rewrite ? app_assoc, <- (app_assoc l1). intros pi' Hs.
  assert ({'(e, l) | l1 ++ l2 = e :: l }) as [(e, l) Hel].
  { clear - pi1. apply lprove_left in pi1.
    destruct l2 as [ | f l2 ]; [ now contradiction pi1 | ].
    destruct l1 as [ | e l1 ].
    - exists (f, l2). reflexivity.
    - exists (e, l1 ++ f :: l2). reflexivity. }
  revert pi' Hs. rewrite app_assoc, Hel, <- app_comm_cons. intros pi' Hs'.
  exists (lmap_right pi'). cbn in *. lia.
- (* */lfrl_left *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (lfrl_left e pi). cbn. lia.
  + cbn. remember (∀ x a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lfrl_left e pi2). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lfrl_left e0 pi'). cbn. lia.
    * destruct (psubs 0 _ e pi1) as [pi1' Hs'].
      revert pi1' Hs'. rewrite nsubs_subs_com by (rewrite e; intros []). cbn.
      rewrite map_map. rewrite (map_ext (fun x => nsubs 0 b (fupz x)) (fun x => x)) by apply nsubs_z_fup.
      rewrite nsubs_z_fup. rewrite map_id. intros pi1' Hs'.
      destruct (IH _ _ nil _ _ pi1' pi2) as [pi1'' Hs1]; [ cbn; lia | solve_bp Hbp | ].
      exists pi1''. cbn in *. lia.
- (* */lfrl_right *)
  revert pi2 IH. cbn. rewrite (map_app fupz l1 (a :: l3)). cbn. intros pi2 IH.
  destruct (pup 0 pi1) as [pi1' Hs1].
  destruct (IH _ _ _ _ _ pi1' pi2) as [pi' Hs]; [ cbn; lia | | ].
  { intro Hl1. rewrite length_map in Hl1. destruct (Hbp Hl1) as [d ->]. exists (fupz d). reflexivity. }
  revert pi' Hs. rewrite <- !map_app. intros pi' Hs.
  exists (lfrl_right pi'). cbn. lia.
Qed.

Lemma lcut a b l1 l2 l3 : (l1 <> [] -> length l2 = 1%nat) ->
  l2 ⊦ a -> l1 ++ a :: l3 ⊦ b -> l1 ++ l2 ++ l3 ⊦ b.
Proof. intros HS pi1 pi2. destruct (lprove_trans_weight _ pi1 pi2 HS) as [pi _]. exact pi. Qed.

Lemma lsubst a b c l1 l2 : [a] ⊦ b -> l1 ++ b :: l2 ⊦ c -> l1 ++ a :: l2 ⊦ c.
Proof. intros pi1 pi2. refine (lcut _ _ pi1 pi2). intros _. reflexivity. Qed.

Lemma ltrans b c l1 l2 : l1 ⊦ b -> b :: l2 ⊦ c -> l1 ++ l2 ⊦ c.
Proof. intros pi1 pi2. rewrite <- (app_nil_l _) in pi2. refine (lcut _ _ pi1 pi2). intros []. reflexivity. Qed.

(** ** Admissible rules *)

Lemma lwith_left1_gen a b c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ a ∧ b :: l2 ⊦ c.
Proof. intro pi. refine (lsubst _ _ _ pi). apply lwith_left1, lidentity. Qed.

Lemma lwith_left2_gen a b c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ b ∧ a :: l2 ⊦ c.
Proof. intro pi. refine (lsubst _ _ _ pi). apply lwith_left2, lidentity. Qed.

Lemma lfrl_left_gen a x b c l1 l2 : closed b -> l1 ++ subs x b a :: l2 ⊦ c -> l1 ++ lfrl x a :: l2 ⊦ c.
Proof. intros Hc pi. refine (lsubst _ _ _ pi). apply (@lfrl_left _ _ _ _ _ Hc), lidentity. Qed.

(** ** Equivalence with nIS *)

Lemma nis1_nis l a : l ⊦ a -> nlprove l a.
Proof.
intro pi. induction pi; try now constructor.
- apply (nlwith_left1 _ _ nil). assumption.
- apply (nlwith_left2 _ _ nil). assumption.
- apply (nlfrl_left _ _ _ nil _ e). assumption.
Qed.

Lemma nis_nis1 l a : l <> [] -> nlprove l a -> l ⊦ a.
Proof.
intros H1 pi. induction pi in H1 |- *.
- constructor.
- destruct l; [ contradiction H1; reflexivity | ].
  constructor.
- apply lwith_left1_gen. apply IHpi. intros Heq. decomp_list_eq Heq.
- apply lwith_left2_gen. apply IHpi. intros Heq. decomp_list_eq Heq.
- destruct l; [ contradiction H1; reflexivity | ].
  constructor; [ apply IHpi1 | apply IHpi2 ]; intros [=].
- constructor; [ apply IHpi1 | apply IHpi2 ]; intros [=].
- destruct l; [ contradiction H1; reflexivity | ].
  constructor. apply IHpi. intros [=].
- apply (lfrl_left_gen _ _ _ _ _ e). apply IHpi. intros [= Heq]. decomp_list_eq Heq.
- destruct l; [ contradiction H1; reflexivity | ].
  constructor. apply IHpi. intros [=].
Qed.


(** * Reversed system nIS₁ʳ *)

Reserved Notation "l ⊦r a" (at level 65, format "l  ⊦r  a").
Inductive rlprove : list lform -> lform -> Type :=
| rlidentity v x : [lvar v x] ⊦r lvar v x
| rltop_right d l : d :: l ⊦r 𝖳
| rlwith_left1 a b v y l2 : a :: l2 ⊦r lvar v y -> a ∧ b :: l2 ⊦r lvar v y
| rlwith_left2 a b v y l2 : a :: l2 ⊦r lvar v y -> b ∧ a :: l2 ⊦r lvar v y
| rlwith_right a b l : l ⊦r a -> l ⊦r b -> l ⊦r a ∧ b
| rlmap_left a b v y d l3 : [d] ⊦r a -> b :: l3 ⊦r lvar v y -> b / a :: d :: l3 ⊦r lvar v y
| rlmap_right a b d l : d :: l · a ⊦r b -> d :: l ⊦r b / a
| rlfrl_left a x b v y l2 : closed b -> subs x b a :: l2 ⊦r lvar v y -> lfrl x a :: l2 ⊦r lvar v y
| rlfrl_right a x l : map fupz l ⊦r subs x (dvar 0) (fupz a) -> l ⊦r lfrl x a
where "l ⊦r a" := (rlprove l a).
Arguments rlidentity {_ _}, _ _.
Arguments rltop_right {_ _}, _ _.
Arguments rlwith_left1 [_ _ _ _ _] _, [_] _ [_ _ _] _, _ _ _ _ _ _.
Arguments rlwith_left2 [_ _ _ _ _] _, [_] _ [_ _ _] _, _ _ _ _ _ _.
Arguments rlwith_right [_ _ _] _ _, _ _ _ _ _.
Arguments rlmap_left [_ _ _ _ _ _] _ _, [_ _ _ _ _] _ _ _, _ _ _ _ _ _ _ _.
Arguments rlmap_right [_ _ _ _] _, _ _ _ _ _.
Arguments rlfrl_left [_ _ _ _ _ _] _ _, _ _ _ _ _ _ _.
Arguments rlfrl_right [_ _ _] _, [_] _ [_] _, _ _ _ _.

Lemma rlprove_left l a : l ⊦r a -> l <> nil.
Proof. intro pi. induction pi; try intros [=]; auto. subst. apply IHpi. reflexivity. Qed.

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


(** ** Admissible rules *)

Lemma rlwith_left1_gen a b c l1 l2 : l1 ++ a :: l2 ⊦r c -> l1 ++ a ∧ b :: l2 ⊦r c.
Proof.
intro pi.
remember (l1 ++ a :: l2) as l eqn:Heql.
induction pi in l1, l2, a, b, Heql |- *; subst.
- decomp_list_eq Heql.
  apply rlwith_left1. constructor.
- decomp_list_eq Heql; subst; constructor.
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
    * apply rlmap_left; [ assumption | ].
      list_simpl. rewrite app_comm_cons. apply IHpi2. reflexivity.
    * cons2app. apply rlmap_left; [ | assumption ].
      rewrite <- (app_nil_l _). apply IHpi1. reflexivity.
  + injection Heql as [= <- <-]. apply rlwith_left1. apply rlmap_left; assumption.
- decomp_list_eq Heql; subst; list_simpl; constructor; list_simpl.
  + rewrite app_comm_cons. apply IHpi. list_reflexivity.
  + apply (IHpi _ _ nil _ eq_refl).
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
- decomp_list_eq Heql; subst; constructor.
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
    * apply rlmap_left; [ assumption | ].
      list_simpl. rewrite app_comm_cons. apply IHpi2. reflexivity.
    * cons2app. apply rlmap_left; [ | assumption ].
      rewrite <- (app_nil_l _). apply IHpi1. reflexivity.
  + injection Heql as [= <- <-]. apply rlwith_left2. apply rlmap_left; assumption.
- decomp_list_eq Heql; subst; list_simpl; constructor; list_simpl.
  + rewrite app_comm_cons. apply IHpi. list_reflexivity.
  + apply (IHpi _ _ nil _ eq_refl).
- decomp_list_eq Heql; subst.
  + list_simpl. apply (rlfrl_left e). rewrite app_comm_cons.
    apply IHpi. list_reflexivity.
  + apply rlwith_left2. apply (rlfrl_left e). assumption.
- apply rlfrl_right.
  list_simpl. apply IHpi. list_reflexivity.
Qed.

Lemma rlmap_left_gen a b c d l3 : [d] ⊦r a -> b :: l3 ⊦r c -> b / a :: d :: l3 ⊦r c.
Proof.
intros pi1 pi2.
remember (b :: l3) as l eqn:Heql.
induction pi2 in d, l3, a, b, pi1, Heql |- *; subst.
- decomp_list_eq Heql.
  apply rlmap_left; [ assumption | constructor ].
- constructor.
- decomp_list_eq Heql; subst.
  apply (rlmap_left pi1). apply rlwith_left1. assumption.
- decomp_list_eq Heql; subst.
  apply (rlmap_left pi1). apply rlwith_left2. assumption.
- apply rlwith_right.
  + apply IHpi2_1; [ assumption | reflexivity ].
  + apply IHpi2_2; [ assumption | reflexivity ].
- decomp_list_eq Heql; subst.
  apply (rlmap_left pi1). apply (rlmap_left pi2_1). assumption.
- apply rlmap_right.
  list_simpl. injection Heql as [= -> ->]. apply IHpi2; [ assumption | list_reflexivity ].
- decomp_list_eq Heql; subst.
  apply (rlmap_left pi1). apply (rlfrl_left e). assumption.
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
- destruct l1; constructor.
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
    * apply rlmap_left; [ assumption | ].
      list_simpl. rewrite app_comm_cons. apply (IHpi2 _ _ _ _ Hc). reflexivity.
    * cons2app. apply rlmap_left; [ | assumption ].
      rewrite <- (app_nil_l _). apply (IHpi1 _ _ _ _ Hc). reflexivity.
  + destruct a; destr_eq Heql; subst.
    * apply (rlfrl_left Hc). simpl subs; rewrite <- Heql. apply rlmap_left; assumption.
    * apply (rlfrl_left Hc). simpl subs. apply rlmap_left; assumption.
- decomp_list_eq Heql; subst; list_simpl; apply rlmap_right.
  + list_simpl. rewrite app_comm_cons. apply (IHpi _ b); [ assumption | list_reflexivity ].
  + apply (IHpi _ b nil); [ assumption | reflexivity ].
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
  {'(d, l3) & l1 = d :: l3 & ([d] ⊦r a) * (b :: l3 ⊦r lvar v y) }.
Proof.
intro pi. remember (b / a :: l1) as l eqn:Heql. remember (lvar v y) as c eqn:Heqc.
destruct pi; (try now destr_eq Heqc); (try now decomp_list_eq Heql).
injection Heqc as [= -> ->]. injection Heql as [= -> -> <-].
exists (d, l3); repeat split; assumption.
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


Lemma nis1r_nis1 l a : l ⊦r a -> l ⊦ a.
Proof. intro pi. induction pi; try now constructor. apply (lfrl_left e IHpi). Qed.

Lemma nis1_nis1r l a : l ⊦ a -> l ⊦r a.
Proof.
intro pi.
induction pi; (try now constructor).
- apply rlidentity_gen.
- apply (rlwith_left1_gen _ _ nil). assumption.
- apply (rlwith_left2_gen _ _ nil). assumption.
- apply rlmap_left_gen; assumption.
- apply (rlfrl_left_gen _ _ _ nil _ e IHpi).
Qed.

Lemma rlcut a b l1 l2 l3 : (l1 <> [] -> length l2 = 1%nat) ->
  l2 ⊦r a -> l1 ++ a :: l3 ⊦r b -> l1 ++ l2 ++ l3 ⊦r b.
Proof. intros HS pi1%nis1r_nis1 pi2%nis1r_nis1. apply nis1_nis1r, (lcut _ HS pi1 pi2). Qed.

Lemma rlsubst a b c l1 l2 : [a] ⊦r b -> l1 ++ b :: l2 ⊦r c -> l1 ++ a :: l2 ⊦r c.
Proof. intros pi1 pi2. refine (rlcut _ _ pi1 pi2). intros _. reflexivity. Qed.

Lemma rltrans b c l1 l2 : l1 ⊦r b -> b :: l2 ⊦r c -> l1 ++ l2 ⊦r c.
Proof. intros pi1 pi2. rewrite <- (app_nil_l _) in pi2. refine (rlcut _ _ pi1 pi2). intros []. reflexivity. Qed.


Lemma rlmap_right_inv a b l : l ⊦r b / a -> l · a ⊦r b.
Proof.
intro pi.
assert ([b / a; a] ⊦r b) as pi' by (apply rlmap_left_gen; apply rlidentity_gen).
exact (rltrans pi pi').
Qed.

Lemma rlwith_right_inv a b l : l ⊦r a ∧ b -> (l ⊦r a) * (l ⊦r b).
Proof.
intro pi. split.
- assert ([a ∧ b] ⊦r a) as pi1 by (apply (rlwith_left1_gen _ _ nil); apply rlidentity_gen).
  rewrite <- (app_nil_r _). exact (rltrans pi pi1).
- assert ([a ∧ b] ⊦r b) as pi2 by (apply (rlwith_left2_gen _ _ nil); apply rlidentity_gen).
  rewrite <- (app_nil_r _). exact (rltrans pi pi2).
Qed.

Lemma rlwith_right1_inv a b l : l ⊦r a ∧ b -> l ⊦r a.
Proof. apply rlwith_right_inv. Qed.

Lemma rlwith_right2_inv a b l : l ⊦r a ∧ b -> l ⊦r b.
Proof. apply rlwith_right_inv. Qed.

Lemma rlfrl_right_inv a x l : l ⊦r lfrl x a -> map fupz l ⊦r subs x (dvar 0) (fupz a).
Proof.
intro pi.
assert ([∀ x (fupz a)] ⊦r subs x (dvar 0) (fupz a)) as pi'.
{ apply (rlfrl_left_gen _ _ (dvar 0) nil), rlidentity_gen. reflexivity. }
rewrite <- (app_nil_r _). exact (rltrans (rpup 0 pi) pi').
Qed.


(** * Non conservativity of Lambek over nIS₁ʳ *)

Definition id_formula_l := var 2 / (var 1 / var 1).
Definition id_formula_r := var 2.

Lemma id_formula_not_nis1r : notT ([id_formula_l] ⊦r id_formula_r).
Proof. intros [[] [=]]%rlmap_left_inv. Qed.

Definition comp_formula_l := var 3 / var 2.
Definition comp_formula_r := (var 3 / var 1) / (var 2 / var 1).

Lemma comp_formula_not_nis1r : notT ([comp_formula_l] ⊦r comp_formula_r).
Proof.
intros pi%rlmap_right_inv%rlmap_right_inv. list_simpl in pi.
apply rlmap_left_inv in pi as [(d, l) Heq [pi1 pi2]].
decomp_list_eq Heq. subst.
apply lvar_left_inv in pi2 as [[=] _].
Qed.
