(* Systems ∀IS* *)

From Stdlib Require Import PeanoNat Lia Wf_nat CRelationClasses.
From OLlibs Require Import List_more.
From InterPT Require Export fformulas.
Export ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * ∀IS *)

Section fIS.

(** ** Rules *)

Reserved Notation "l ⊦ a" (at level 65, format "l  ⊦  a").
Inductive fisprove : list fform -> fform -> Type :=
| fisidentity a : [a] ⊦ a
| fismap_left a b c d l3 : [d] ⊦ a -> b :: l3 ⊦ c -> a → b :: d :: l3 ⊦ c
| fismap_right a b l : l · a ⊦ b -> l ⊦ a → b
| fisfrl_left a x b c l1 l2 : closed b -> l1 ++ subs x b a :: l2 ⊦ c -> l1 ++ lfrl x a :: l2 ⊦ c
| fisfrl_right a x l : map fupz l ⊦ subs x (dvar 0) (fupz a) -> l ⊦ lfrl x a
where "l ⊦ a" := (fisprove l a).
Arguments fisidentity {_} , _.
Arguments fismap_left [_ _ _ _ _] _ _, _ _ _ _ _ _ _.
Arguments fismap_right [_ _ _] _, _ _ _ _.
Arguments fisfrl_left [_ _ _ _ _ _ _] _, [_ _ _ _ _ _] _ _, _ _ _ _ _ _ _.
Arguments fisfrl_right [_ _ _] _, [_] _ [_] _, _ _ _ _.

(** *** Weight *)

Fixpoint fisweight l b (pi : l ⊦ b) := S
match pi with
| fisidentity => 0
| fismap_right pi1 | fisfrl_right pi1 | fisfrl_left pi1 => fisweight pi1
| fismap_left pi1 pi2 => fisweight pi1 + fisweight pi2
end.

(** substitutes [formula] [f] for index [k] in proof [pi] and decreases indexes above [k] *)
Lemma fispsubs k f (Hc : closed f) l b (pi : l ⊦ b) :
  { pi' : map (nsubs k f) l ⊦ nsubs k f b | fisweight pi' = fisweight pi }.
Proof.
induction pi in k, f, Hc |- *;
  try (destruct (IHpi k f Hc) as [pi' Hs]);
  try (destruct (IHpi1 k f Hc) as [pi1' Hs1]);
  try (destruct (IHpi2 k f Hc) as [pi2' Hs2]).
- now exists fisidentity.
- revert pi2' Hs2. list_simpl. intros pi2' Hs2.
  exists (fismap_left pi1' pi2'). cbn in *. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (fismap_right pi'). cbn. lia.
- cbn. rewrite <- Hs. clear Hs.
  revert pi'. list_simpl. rewrite nsubs_subs_com.
  + intro pi'.
    assert (closed (nsubs k f b)) as Hc' by (rewrite freevars_nsubs; assumption).
    exists (fisfrl_left Hc' pi'). cbn. lia.
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
  exists (fisfrl_right pi'). reflexivity.
Qed.

(** lift indexes above [k] in proof [pi] *)
Lemma fispup k l b (pi : l ⊦ b) : { pi' : map (fup k) l ⊦ fup k b | fisweight pi' = fisweight pi }.
Proof.
induction pi in k |- *;
  try (destruct (IHpi k) as [pi' Hs]) ;
  try (destruct (IHpi1 k) as [pi1' Hs1]) ;
  try (destruct (IHpi2 k) as [pi2' Hs2]).
- now exists fisidentity.
- revert pi2' Hs2. list_simpl. intros pi2' Hs2.
  exists (fismap_left pi1' pi2'). cbn in *. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (fismap_right pi'). cbn. lia.
- cbn. rewrite <- Hs. clear Hs.
  rewrite <- (freevars_fup k) in e.
  revert pi'. list_simpl. rewrite fup_subs_com.
  intro pi'.
  exists (fisfrl_left e pi'). reflexivity.
- clear pi' Hs.
  destruct (IHpi (S k)) as [pi' Hs].
  cbn. rewrite <- Hs. clear Hs.
  revert pi'.
  rewrite fup_subs_com. cbn. rewrite fup_fup_com.
  rewrite map_map.
  rewrite (map_ext (fun x => fup (S k) (fupz x)) (fun x => fupz (fup k x))) by apply fup_fup_com.
  rewrite <- map_map.
  intro pi'.
  exists (fisfrl_right pi'). reflexivity.
Qed.


(** *** Cut Elimination *)

#[local] Ltac solve_bp H := intros; apply H; rewrite ?length_app in *; cbn in *; lia.

#[local] Ltac solve_bp2 H :=
  let Hl := fresh in
  let d := fresh in
  let Hd := fresh in
  now intro Hl; destruct (H Hl) as [d Hd]; decomp_list_eq Hd; (try discriminate); eexists.

Lemma fisprove_trans_weight a b l1 l2 l3 (pi1 : l2 ⊦ a) (pi2 : l1 ++ a :: l3 ⊦ b) :
  (l1 <> [] -> length l2 = 1%nat) ->
  { pi' : l1 ++ l2 ++ l3 ⊦ b | fisweight pi' < fisweight pi1 + fisweight pi2 }.
Proof.
remember (fisweight pi1 + fisweight pi2) as q eqn:Hq.
intro Hbp0. assert (length l1 <> 0%nat ->  { c | l2 = [c] }) as Hbp.
{ intro H1. destruct l1 as [ | d l1 ]; [ now contradiction H1 | ].
  destruct l2 as [ | c [ | ? ? ] ]; destr_eq Hbp0; try now intros [=].
  exists c. reflexivity. } clear Hbp0.
induction q as [q IHq] using (well_founded_induction_type lt_wf) in a, b, l1, l2, l3, pi1, pi2, Hq, Hbp |- *.
subst q.
assert (forall a' b' l1' l2' l3' (pi1' : l2' ⊦ a') (pi2' : l1' ++ a' :: l3' ⊦ b'),
  fisweight pi1' + fisweight pi2' < fisweight pi1 + fisweight pi2 ->
  (length l1' <> 0%nat ->  { c | l2' = [c] }) ->
  {pi' : l1' ++ l2' ++ l3' ⊦ b' | fisweight pi' < fisweight pi1' + fisweight pi2'}) as IH.
{ intros a' b' l1' l2' l3' pi1' pi2' Hs Hbp'. exact (IHq _ Hs _ _ _ _ _ pi1' pi2' eq_refl Hbp'). } clear IHq.
remember (l1 ++ a :: l3) as l eqn:Hl.
destruct pi2; try subst l; cbn in IH.
- (* */identity *)
  decomp_list_eq Hl. list_simpl. exists pi1. lia.
- (* */lmap_left *)
  decomp_list_eq Hl; subst.
  + decomp_list_eq Hl0; subst.
    * revert pi2_2 IH. cbn. rewrite app_comm_cons, app_assoc. intros pi2_2 IH.
      destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi1' Hs']; [ lia | solve_bp Hbp | ].
      revert pi2_2 IH pi1' Hs'. list_simpl. intros pi2_2 IH pi1' Hs'.
      exists (fismap_left pi2_1 pi1'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 pi2_1) as [pi1' Hs']; [ cbn; lia | solve_bp Hbp | ].
      revert pi2_2 IH pi1' Hs'. list_simpl. intros pi2_2 IH pi1' Hs'.
      destruct Hbp as [e ->]; [ cbn; lia | ].
      exists (fismap_left pi1' pi2_2). cbn. lia.
  + cbn in Hl. injection Hl as [= <- <-].
    cbn. remember (a0 → b) as e eqn:He.
    destruct pi1; destr_eq He; subst; cbn.
    * exists (fismap_left pi2_1 pi2_2). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (fismap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (fismap_left pi1_1 pi'). cbn. lia.
    * revert pi1 IH. list_simpl. intros pi1 IH.
      destruct (IH _ _ _ _ _ pi2_1 pi1) as [pi1' Hs1]; [ cbn; lia | | ].
      { intros _. exists d. reflexivity. }
      destruct (IH _ _ nil _ _ pi1' pi2_2) as [pi2' Hs2]; [ cbn in *; lia | | ].
      { intros []. reflexivity. }
      revert pi2' Hs2. list_simpl. intros pi2' Hs2.
      exists pi2'. cbn in *. lia.
    * destruct (IH _ _ nil _ _ pi1 (fismap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (fisfrl_left e pi'). cbn. lia.
- (* */lmap_right *)
  revert pi2 IH. list_simpl. intros pi2 IH.
  destruct (IH _ _ _ _ _ pi1 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
  revert pi' Hs. clear. rewrite ? app_assoc, <- (app_assoc l1). intros pi' Hs.
  revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs'.
  exists (fismap_right pi'). cbn in *. lia.
- (* */lfrl_left *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (fisfrl_left e pi). cbn. lia.
  + cbn. remember (∀ x a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (fisfrl_left e pi2). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (fisfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      assert (l1 = []) as ->.
      { destruct l1; [ reflexivity | exfalso ].
        destruct Hbp; [ cbn; intro; lia | ]. discriminate. }
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (fismap_left pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (fisfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (fisfrl_left e0 pi'). cbn. lia.
    * destruct (fispsubs 0 _ e pi1) as [pi1' Hs'].
      revert pi1' Hs'. rewrite nsubs_subs_com by (rewrite e; intros []). cbn.
      rewrite map_map. rewrite (map_ext (fun x => nsubs 0 b (fupz x)) (fun x => x)) by apply nsubs_z_fup.
      rewrite nsubs_z_fup. rewrite map_id. intros pi1' Hs'.
      destruct (IH _ _ _ _ _ pi1' pi2) as [pi1'' Hs1]; [ cbn; lia | solve_bp Hbp | ].
      exists pi1''. cbn in *. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. rewrite !app_assoc. intros pi Hs.
    exists (fisfrl_left e pi). cbn. lia.
- (* */lfrl_right *)
  revert pi2 IH. cbn. rewrite (map_app fupz l1 (a :: l3)). cbn. intros pi2 IH.
  destruct (fispup 0 pi1) as [pi1' Hs1].
  destruct (IH _ _ _ _ _ pi1' pi2) as [pi' Hs]; [ cbn; lia | | ].
  { intro Hl1. rewrite length_map in Hl1. destruct (Hbp Hl1) as [d ->]. exists (fupz d). reflexivity. }
  revert pi' Hs. rewrite <- !map_app. intros pi' Hs.
  exists (fisfrl_right pi'). cbn. lia.
Qed.

Lemma fiscut a b l1 l2 l3 : (l1 <> [] -> length l2 = 1%nat) ->
  l2 ⊦ a -> l1 ++ a :: l3 ⊦ b -> l1 ++ l2 ++ l3 ⊦ b.
Proof. intros HS pi1 pi2. destruct (fisprove_trans_weight _ pi1 pi2 HS) as [pi _]. exact pi. Qed.

Lemma fissubst a b c l1 l2 : [a] ⊦ b -> l1 ++ b :: l2 ⊦ c -> l1 ++ a :: l2 ⊦ c.
Proof. intros pi1 pi2. refine (fiscut _ _ pi1 pi2). intros _. reflexivity. Qed.

Lemma fistrans b c l1 l2 : l1 ⊦ b -> b :: l2 ⊦ c -> l1 ++ l2 ⊦ c.
Proof. intros pi1 pi2. rewrite <- (app_nil_l _) in pi2. refine (fiscut _ _ pi1 pi2). intros []. reflexivity. Qed.

End fIS.



(** * ∀IS₁ *)

(** ** Rules *)

Reserved Notation "l ⊦ a" (at level 65, format "l  ⊦  a").
Inductive lprove : list fform -> fform -> Type :=
| lidentity a : [a] ⊦ a
| lmap_left a b c d l3 : [d] ⊦ a -> b :: l3 ⊦ c -> a → b :: d :: l3 ⊦ c
| lmap_right a b d l : d :: l · a ⊦ b -> d :: l ⊦ a → b
| lfrl_left a x b c l2 : closed b -> subs x b a :: l2 ⊦ c -> lfrl x a :: l2 ⊦ c
| lfrl_right a x l : map fupz l ⊦ subs x (dvar 0) (fupz a) -> l ⊦ lfrl x a
where "l ⊦ a" := (lprove l a).
Arguments lidentity {_} , _.
Arguments lmap_left [_ _ _ _ _] _ _, _ _ _ _ _ _ _.
Arguments lmap_right [_ _ _ _] _, _ _ _ _ _.
Arguments lfrl_left [_ _ _ _ _ _] _, [_ _ _ _ _] _ _, _ _ _ _ _ _.
Arguments lfrl_right [_ _ _] _, [_] _ [_] _, _ _ _ _.

Lemma lprove_left l a : l ⊦ a -> l <> nil.
Proof. intro pi. induction pi; try intros [=]; auto. subst. apply IHpi. reflexivity. Qed.


(** *** Weight *)

Fixpoint lweight l b (pi : l ⊦ b) := S
match pi with
| lidentity => 0
| lmap_right pi1 | lfrl_right pi1 | lfrl_left pi1 => lweight pi1
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

#[local] Ltac solve_bp H := intros; apply H; rewrite ?length_app in *; cbn in *; lia.

#[local] Ltac solve_bp2 H :=
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
    cbn. remember (a0 → b) as e eqn:He.
    destruct pi1; destr_eq He; subst; cbn.
    * exists (lmap_left pi2_1 pi2_2). cbn. lia.
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

Lemma lfrl_left_gen a x b c l1 l2 : closed b -> l1 ++ subs x b a :: l2 ⊦ c -> l1 ++ lfrl x a :: l2 ⊦ c.
Proof. intros Hc pi. refine (lsubst _ _ _ pi). apply (@lfrl_left _ _ _ _ _ Hc), lidentity. Qed.

Lemma lmap_right_inv a b l : l ⊦ a → b -> l · a ⊦ b.
Proof.
intro pi.
assert ([a → b; a] ⊦ b) as pi' by (apply (@lmap_left _ _ _ a); apply lidentity).
exact (ltrans pi pi').
Qed.

(** ** Equivalence with ∀IS *)

(* Theorem 13 *)
Lemma fis1_fis l a : l ⊦ a -> fisprove l a.
Proof. intro pi. induction pi; try now constructor. apply (fisfrl_left _ _ _ nil _ e). assumption. Qed.

(* Theorem 13 *)
Lemma fis_fis1 l a : l <> [] -> fisprove l a -> l ⊦ a.
Proof.
intros H1 pi. induction pi in H1 |- *.
- constructor.
- constructor; [ apply IHpi1 | apply IHpi2 ]; intros [=].
- destruct l; [ contradiction H1; reflexivity | ].
  constructor. apply IHpi. intros [=].
- apply (lfrl_left_gen _ _ _ _ _ e). apply IHpi. intros [= Heq]. decomp_list_eq Heq.
- destruct l; [ contradiction H1; reflexivity | ].
  constructor. apply IHpi. intros [=].
Qed.


(** * Reversed system ∀IS₁ʳ *)

Reserved Notation "l ⊦r a" (at level 65, format "l  ⊦r  a").
Inductive rlprove : list fform -> fform -> Type :=
| rlidentity v x : [lvar v x] ⊦r lvar v x
| rlmap_left a b v y d l3 : [d] ⊦r a -> b :: l3 ⊦r lvar v y -> a → b :: d :: l3 ⊦r lvar v y
| rlmap_right a b d l : d :: l · a ⊦r b -> d :: l ⊦r a → b
| rlfrl_left a x b v y l2 : closed b -> subs x b a :: l2 ⊦r lvar v y -> lfrl x a :: l2 ⊦r lvar v y
| rlfrl_right a x l : map fupz l ⊦r subs x (dvar 0) (fupz a) -> l ⊦r lfrl x a
where "l ⊦r a" := (rlprove l a).
Arguments rlidentity {_ _}, _ _.
Arguments rlmap_left [_ _ _ _ _ _] _ _, [_ _ _ _ _] _ _ _, _ _ _ _ _ _ _ _.
Arguments rlmap_right [_ _ _ _] _, _ _ _ _ _.
Arguments rlfrl_left [_ _ _ _ _ _] _ _, _ _ _ _ _ _ _.
Arguments rlfrl_right [_ _ _] _, [_] _ [_] _, _ _ _ _.

Lemma rlprove_left l a : l ⊦r a -> l <> nil.
Proof. intro pi. induction pi; try intros [=]; auto. subst. apply IHpi. reflexivity. Qed.

Fixpoint rlweight l b (pi : l ⊦r b) := S
match pi with
| rlidentity => 0
| rlmap_right pi1 | rlfrl_right pi1 | rlfrl_left _ pi1 => rlweight pi1
| rlmap_left pi1 pi2 => rlweight pi1 + rlweight pi2
end.

(** lift indexes above [k] in proof [pi] *)
Lemma rpup k l b : l ⊦r b -> map (fup k) l ⊦r fup k b.
Proof.
intro pi. induction pi in k |- *; try now constructor.
- change (map (fup k) [lvar v x]) with ([fup k (lvar v x)]). destruct (fup_lvar k v x) as [y ->].
  apply rlidentity.
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

Lemma rlmap_left_gen a b c d l3 : [d] ⊦r a -> b :: l3 ⊦r c -> a → b :: d :: l3 ⊦r c.
Proof.
intros pi1 pi2.
remember (b :: l3) as l eqn:Heql.
induction pi2 in d, l3, a, b, pi1, Heql |- *; subst.
- decomp_list_eq Heql.
  apply rlmap_left; [ assumption | constructor ].
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
  destruct a as [ v x | a1 a2 | x a1 ]; inversion Hs;
  try now rewrite <- (app_nil_l _); constructor; rewrite <- (app_nil_l _); constructor; assumption.
- constructor. change ([a1 → a2] · a1) with ([] ++ a1 → a2 :: [a1] ++ []).
  cbn in Hs. apply rlmap_left_gen.
  + refine (IH _ _ _ eq_refl); lia.
  + refine (IH _ _ _ eq_refl); lia.
- apply rlfrl_right. cbn. apply (rlfrl_left_gen _ _ (dvar 0) nil).
  + reflexivity.
  + refine (IH _ _ _ eq_refl).
    cbn in Hs. rewrite fsize_subs_lvar, fsize_fup. lia.
Qed.


Lemma rlmap_left_inv a b v y l1 : a → b :: l1 ⊦r lvar v y ->
  {'(d, l3) & l1 = d :: l3 & ([d] ⊦r a) * (b :: l3 ⊦r lvar v y) }.
Proof.
intro pi. remember (a → b :: l1) as l eqn:Heql. remember (lvar v y) as c eqn:Heqc.
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


(* Theorem 13 *)
Lemma fis1r_fis1 l a : l ⊦r a -> l ⊦ a.
Proof. intro pi. induction pi; try now constructor. apply (lfrl_left e IHpi). Qed.

(* Theorem 13 *)
Lemma fis1_fis1r l a : l ⊦ a -> l ⊦r a.
Proof.
intro pi.
induction pi; (try now constructor).
- apply rlidentity_gen.
- apply rlmap_left_gen; assumption.
- apply (rlfrl_left_gen _ _ _ nil _ e IHpi).
Qed.

Lemma rlcut a b l1 l2 l3 : (l1 <> [] -> length l2 = 1%nat) ->
  l2 ⊦r a -> l1 ++ a :: l3 ⊦r b -> l1 ++ l2 ++ l3 ⊦r b.
Proof. intros HS pi1%fis1r_fis1 pi2%fis1r_fis1. apply fis1_fis1r, (lcut _ HS pi1 pi2). Qed.

Lemma rlsubst a b c l1 l2 : [a] ⊦r b -> l1 ++ b :: l2 ⊦r c -> l1 ++ a :: l2 ⊦r c.
Proof. intros pi1 pi2. refine (rlcut _ _ pi1 pi2). intros _. reflexivity. Qed.

Lemma rltrans b c l1 l2 : l1 ⊦r b -> b :: l2 ⊦r c -> l1 ++ l2 ⊦r c.
Proof. intros pi1 pi2. rewrite <- (app_nil_l _) in pi2. refine (rlcut _ _ pi1 pi2). intros []. reflexivity. Qed.



(** * Mitchell's System *)

Section Mitchell.

(* Table 11 *)
(* "original": requires alpha-renaming
Reserved Notation "a ≤ b" (at level 70).
Inductive m_sub : crelation fform :=
| m_identity a : a ≤ a
| m_trans a b c : a ≤ b -> b ≤ c -> a ≤ c
| m_arrow a b c d : c ≤ a -> b ≤ d -> a → b ≤ c → d
| m_frl x a b : a ≤ b -> lfrl x a ≤ lfrl x b
| m_frl_subs x a b : lfrl x a ≤ subs x b a
| m_frl_gen x a : ~ (In x (freevars a)) -> a ≤ lfrl x a
| m_frl_arrow x a b : lfrl x (a → b) ≤ (lfrl x a) → (lfrl x b)
where "a ≤ b" := (m_sub a b).
*)
Reserved Notation "a ≤ b" (at level 70).
Inductive m_sub : crelation fform :=
| m_identity a : closed a -> a ≤ a
| m_trans a b c : closed b -> a ≤ b -> b ≤ c -> a ≤ c
| m_arrow a b c d : c ≤ a -> b ≤ d -> a → b ≤ c → d
| m_frl x a b : subs x (dvar 0) (fupz a) ≤ subs x (dvar 0) (fupz b) -> lfrl x a ≤ lfrl x b
| m_frl_subs x a b : closed (lfrl x a) -> closed b -> lfrl x a ≤ subs x b a
| m_frl_gen x a : closed a -> a ≤ lfrl x a
| m_frl_arrow x a b : closed (lfrl x (a → b)) -> lfrl x (a → b) ≤ (lfrl x a) → (lfrl x b)
where "a ≤ b" := (m_sub a b).

Lemma msub_closed a b : a ≤ b -> closed a /\ closed b.
Proof.
intro pi. induction pi.
- split; assumption.
- tauto.
- cbn. destruct IHpi1 as [-> ->], IHpi2 as [-> ->]. repeat split.
- cbn. destruct IHpi as [IH1 IH2]. split.
  + assert (Hs := freevars_subs_closed x (dvar 0) (fupz a) eq_refl).
    rewrite IH1, freevars_fup in Hs.
    symmetry. assumption.
  + assert (Hs := freevars_subs_closed x (dvar 0) (fupz b) eq_refl).
    rewrite IH2, freevars_fup in Hs.
    symmetry. assumption.
- split; [ assumption | ].
  cbn in e. assert (Hs := freevars_subs x b a).
  rewrite e0, e in Hs. cbn in Hs.
  destruct (freevars (subs x b a)) as [ | y l ]; [ reflexivity | exfalso ].
  destruct (Hs y). apply in_eq.
- split; [ assumption | ].
  cbn. rewrite e. reflexivity.
- cbn in *. split; [ assumption | ].
  rewrite remove_app in e. assumption.
Qed.

Lemma msub_fis1 a b : a ≤ b -> [a] ⊦ b.
Proof.
intro pi. induction pi.
- apply lidentity.
- exact (ltrans IHpi1 IHpi2).
- apply lmap_right. list_simpl. apply lmap_left; assumption.
- apply lfrl_right. cbn. apply (@lfrl_left _ _ (dvar 0)).
  { reflexivity. }
  assumption.
- apply (@lfrl_left _ _ _ _ _ e0). apply lidentity.
- apply lfrl_right.
  rewrite nfree_subs.
  + apply lidentity.
  + rewrite freevars_fup. rewrite e. intros [].
- apply lmap_right. apply lfrl_right. cbn. apply (@lfrl_left _ _ (dvar 0)).
  { reflexivity. }
  cbn. apply lmap_left, lidentity.
  apply (@lfrl_left _ _ (dvar 0)), lidentity. reflexivity.
Qed.

End Mitchell.


(** * Longo-Milsted-Soloviev's System *)

Section LMS.

(* Table 12 *)
Reserved Notation "a ≤ b" (at level 70).
Inductive lms_sub : crelation fform :=
| lms_identity a : a ≤ a
| lms_arrow a b c d : c ≤ a -> b ≤ d -> a → b ≤ c → d
| lms_frl_left x a c b : closed c -> subs x c a ≤ b -> lfrl x a ≤ b
| lms_frl_right x c l b :
    fupz c ≤ fold_right lmap (subs x (dvar 0) (fupz b)) (map fupz l) ->
    c ≤ fold_right lmap (lfrl x b) l
where "a ≤ b" := (lms_sub a b).

Lemma fis1_lmssub a l b : a :: l ⊦ b -> a ≤ fold_right lmap b l.
Proof.
intro pi. remember (a :: l) as l0 eqn:Hl. induction pi in a, l, Hl |- *; try decomp_list_eq Hl; subst; cbn.
- apply lms_identity.
- apply lms_arrow.
  + apply (IHpi1 _ _ eq_refl).
  + apply (IHpi2 _ _ eq_refl).
- change (a0 → b) with (fold_right lmap b [a0]).
  rewrite <- fold_right_app.
  apply (IHpi _ _ eq_refl).
- apply (lms_frl_left _ _ _ e).
  apply (IHpi _ _ eq_refl).
- apply lms_frl_right.
  apply (IHpi _ _ eq_refl).
Qed.

Lemma lmssub_msub a b : closed a -> closed b -> a ≤ b -> m_sub a b.
Proof.
intros Ha Hb pi. induction pi in Ha, Hb |- *.
- apply m_identity. assumption.
- cbn in Ha. decomp_list_eq Ha. destruct Ha.
  cbn in Hb. decomp_list_eq Hb. destruct Hb.
  apply m_arrow; [ apply IHpi1 | apply IHpi2 ]; assumption.
- assert (closed (subs x c a)) as Hs.
  { assert (Hs := freevars_subs x c a).
    cbn in Ha. rewrite Ha, e in Hs. cbn in Hs.
    destruct (freevars (subs x c a)) as [ | y l ]; [ reflexivity | exfalso ].
    destruct (Hs y). apply in_eq. }
  refine (m_trans Hs _ (IHpi Hs Hb)).
  apply m_frl_subs; assumption.
- clear pi.
  apply closed_fold_lmap in Hb. inversion_clear Hb.
  assert (closed (fold_right lmap (subs x (dvar 0) (fupz b)) (map fupz l))) as Hsl.
  { clear - H X. induction l as [ | y l IH ] in X |- *; cbn.
    - rewrite freevars_subs_closed; [ | reflexivity ]. rewrite freevars_fup. assumption.
    - inversion_clear X. rewrite freevars_fup. rewrite H0. cbn. apply IH. assumption. }
  rewrite freevars_fup in IHpi. specialize (IHpi Ha Hsl).
  apply (@m_trans _ (lfrl x c)).
  3: apply (@m_trans _ (lfrl x (fold_right lmap b l))).
  5: apply (@m_trans _ (fold_right lmap (lfrl x b) (map (lfrl x) l))).
  + cbn. rewrite Ha. reflexivity.
  + apply m_frl_gen. assumption.
  + clear - H X. induction l as [ | y l IH ] in X |- *; cbn.
    * assumption.
    * inversion_clear X. rewrite remove_app. rewrite H0. cbn. apply IH. assumption.
  + apply m_frl.
    rewrite (nfree_subs _ _ (fupz c)) by (rewrite freevars_fup, Ha; intros []).
    enough (subs x (dvar 0) (fupz (fold_right lmap b l))
         = fold_right lmap (subs x (dvar 0) (fupz b)) (map fupz l)) as -> by assumption.
    clear - X. induction l as [ | y l IH ] in X |- *; cbn.
    -- reflexivity.
    -- inversion_clear X. rewrite IH by assumption.
       f_equal.
       apply (nfree_subs _ _ (fupz y)).
       rewrite freevars_fup, H. intros [].
  + apply closed_fold_lmap. constructor.
    * assumption.
    * clear - X. induction l as [ | y l IH ] in X |- *; cbn; constructor.
      -- inversion_clear X. cbn. rewrite H. reflexivity.
      -- apply IH. inversion_clear X. assumption.
  + clear - H X. induction l as [ | y l IH ] in X |- *; cbn.
    * apply m_identity. assumption.
    * assert (closed (∀ x (fold_right lmap b l))) as Hsl.
      { inversion_clear X. clear - H X0. induction l as [ | y l IH ] in X0 |- *; cbn.
        - assumption.
        - inversion_clear X0. rewrite remove_app. rewrite H0. cbn. apply IH. assumption. }
      apply (@m_trans _ (lfrl x y → lfrl x (fold_right lmap b l))).
      -- inversion_clear X. cbn. rewrite H0. cbn. assumption.
      -- apply m_frl_arrow.
         inversion_clear X. cbn. rewrite H0. cbn. assumption.
      -- apply m_arrow; [ apply m_identity | ]; inversion_clear X.
         ++ cbn. rewrite H0. reflexivity.
         ++ apply IH. assumption.
  + clear - H X. induction l as [ | y l IH ] in X |- *; cbn.
    * apply m_identity. assumption.
    * inversion_clear X. apply m_arrow.
      -- apply m_frl_gen. assumption.
      -- apply IH. assumption.
Qed.

(* useless
Lemma lmssub_fis1 a b : closed a -> closed b -> a ≤ b -> [a] ⊦ b.
Proof. intros. apply msub_fis1, lmssub_msub; assumption. Qed.
*)
Lemma lmssub_fis1 a b : a ≤ b -> [a] ⊦ b.
Proof.
intro pi. induction pi.
- apply lidentity.
- apply lmap_right. list_simpl. apply lmap_left; assumption.
- apply (lfrl_left e IHpi).
- clear - IHpi.
  change [fupz c] with (map fupz [c]) in IHpi.
  remember nil as l0 eqn:Hc. clear Hc.
  induction l in l0, IHpi |- *; cbn in *.
  + apply lfrl_right. assumption.
  + apply lmap_right.
    apply IHl.
    list_simpl. rewrite app_comm_cons. apply lmap_right_inv. assumption.
Qed.

End LMS.
