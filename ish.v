(* System ISₕ *)

From Stdlib Require Import PeanoNat Lia Wf_nat.
From OLlibs Require Import List_more.
From InterPT Require Export lformulas.
Export ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * ISₕ *)

(** ** Rules *)

(* Table 1, black part only *)
Reserved Notation "l ⊦ a" (at level 65, format "l ⊦  a").
Inductive lprove : list lform -> lform -> Type :=
| lidentity a : [a] ⊦ a
| ltop_right l : l ⊦ 𝖳
| lwith_left1 a b c l2 : a :: l2 ⊦ c -> a ∧ b :: l2 ⊦ c
| lwith_left2 a b c l2 : a :: l2 ⊦ c -> b ∧ a :: l2 ⊦ c
| lwith_right a b l : l ⊦ a -> l ⊦ b -> l ⊦ a ∧ b
| lmap_left a b c d l3 : [d] ⊦ a -> b :: l3 ⊦ c -> b / a :: d :: l3 ⊦ c
| lmap_right a b l : l · a ⊦ b -> l ⊦ b / a
| lzero_left a l2 : 0 :: l2 ⊦ a
| lplus_left a b c l2 : a :: l2 ⊦ c -> b :: l2 ⊦ c -> a ∨ b :: l2 ⊦ c
| lplus_right1 a b l : l ⊦ a -> l ⊦ a ∨ b
| lplus_right2 a b l : l ⊦ a -> l ⊦ b ∨ a
| lone_left a l2 : l2 ⊦ a -> 1 :: l2 ⊦ a
| lone_right : nil ⊦ 1
| lfrl_left a x b c l2 : closed b -> subs x b a :: l2 ⊦ c -> lfrl x a :: l2 ⊦ c
| lfrl_right a x l : map fupz l ⊦ subs x (dvar 0) (fupz a) -> l ⊦ lfrl x a
| lexs_left a x c l2 : subs x (dvar 0) (fupz a) :: map fupz l2 ⊦ fupz c -> lexs x a :: l2 ⊦ c
| lexs_right a x b l : closed b -> l ⊦ subs x b a -> l ⊦ lexs x a
where "l ⊦ a" := (lprove l a).
Arguments lidentity {_}, _.
Arguments ltop_right {_}, _.
Arguments lwith_left1 [_ _ _ _] _, [_] _ [_ _] _, _ _ _ _ _.
Arguments lwith_left2 [_ _ _ _] _, [_] _ [_ _] _, _ _ _ _ _.
Arguments lwith_right [_ _ _] _ _, _ _ _ _ _.
Arguments lmap_left [_ _ _ _ _] _ _, _ _ _ _ _ _ _.
Arguments lmap_right [_ _ _] _, _ _ _ _.
Arguments lzero_left {_ _}, _ _.
Arguments lplus_left [_ _ _ _] _ _, _ _ _ _ _ _.
Arguments lplus_right1 [_ _ _] _, [_] _ [_] _, _ _ _ _.
Arguments lplus_right2 [_ _ _] _, [_] _ [_] _, _ _ _ _.
Arguments lone_left [_ _] _, _ _ _.
Arguments lfrl_left [_ _ _ _ _ _] _, [_ _ _ _ _] _ _, _ _ _ _ _ _.
Arguments lfrl_right [_ _ _] _, [_] _ [_] _, _ _ _ _.
Arguments lexs_left [_ _ _ _] _, [_] _ [_] _,  _ _ _ _.
Arguments lexs_right [_ _ _ _ _] _, [_ _ _ _] _ _, _ _ _ _ _ _.


(** *** Weight *)

Fixpoint lweight l b (pi : l ⊦ b) := S
match pi with
| lidentity | ltop_right | lzero_left | lone_right => 0
| lwith_left1 pi1 | lwith_left2 pi1 | lmap_right pi1 | lplus_right1 pi1 | lplus_right2 pi1
| lone_left pi1 | lfrl_left pi1 | lfrl_right pi1 | lexs_left pi1 | lexs_right pi1 => lweight pi1
| lwith_right pi1 pi2 | lplus_left pi1 pi2 => max (lweight pi1) (lweight pi2)
| lmap_left pi1 pi2 => lweight pi1 + lweight pi2
end.

(** substitutes [formula] [f] for index [k] in proof [pi] and decreases indexes above [k] *)
Theorem psubs k f (Hc : closed f) l b (pi : l ⊦ b) :
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
- list_simpl. exists lzero_left. reflexivity.
- revert pi1' Hs1 pi2' Hs2. list_simpl. intros pi1' Hs1 pi2' Hs2.
  exists (lplus_left pi1' pi2'). cbn. lia.
- exists (lplus_right1 pi'). cbn. lia.
- exists (lplus_right2 pi'). cbn. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (lone_left pi'). cbn. lia.
- exists lone_right. reflexivity.
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
- clear pi' Hs.
  rewrite <- (freevars_fup 0) in Hc.
  destruct (IHpi (S k) _ Hc) as [pi' Hs].
  cbn. rewrite <- Hs. clear Hs.
  revert pi'.
  simpl map. rewrite nsubs_subs_com.
  2:{ rewrite Hc. intros []. }
  cbn. rewrite !map_map.
  rewrite !(map_ext (fun x => nsubs (S k) (fupz f) (fupz x)) (fun x => fupz (nsubs k f x))).
  2: apply nsubs_fup_com.
  rewrite !nsubs_fup_com.
  rewrite <- map_map.
  intro pi'.
  exists (lexs_left pi'). reflexivity.
- cbn. rewrite <- Hs. clear Hs.
  revert pi'. rewrite nsubs_subs_com.
  + intro pi'.
    assert (closed (nsubs k f b)) as Hc' by (rewrite freevars_nsubs; assumption).
    exists (lexs_right Hc' pi'). cbn. lia.
  + rewrite Hc. intros [].
Qed.

(** lift indexes above [k] in proof [pi] *)
Theorem pup k l b (pi : l ⊦ b) : { pi' : map (fup k) l ⊦ fup k b | lweight pi' = lweight pi }.
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
- list_simpl. exists lzero_left. reflexivity.
- revert pi1' Hs1 pi2' Hs2. list_simpl. intros pi1' Hs1 pi2' Hs2.
  exists (lplus_left pi1' pi2'). cbn. lia.
- exists (lplus_right1 pi'). cbn. lia.
- exists (lplus_right2 pi'). cbn. lia.
- revert pi' Hs. list_simpl. intros pi' Hs.
  exists (lone_left pi'). cbn. lia.
- exists lone_right. reflexivity.
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
- clear pi' Hs.
  destruct (IHpi (S k)) as [pi' Hs].
  cbn. rewrite <- Hs. clear Hs.
  revert pi'.
  simpl map.
  rewrite !fup_subs_com. cbn. rewrite !fup_fup_com.
  rewrite !map_map.
  rewrite !(map_ext (fun x => fup (S k) (fupz x)) (fun x => fupz (fup k x))) by apply fup_fup_com.
  rewrite <- map_map.
  intro pi'.
  exists (lexs_left pi'). reflexivity.
- cbn. rewrite <- Hs. clear Hs.
  rewrite <- (freevars_fup k) in e.
  revert pi'. list_simpl. rewrite fup_subs_com.
  intro pi'.
  exists (lexs_right e pi'). reflexivity.
Qed.


(** *** Cut Elimination *)

Ltac solve_bp H := intro; apply H; rewrite ?length_app in *; cbn in *; lia.

Ltac solve_bp2 H :=
  let Hl := fresh in
  let d := fresh in
  let Hd := fresh in
  now intro Hl; destruct (H Hl) as [d Hd]; decomp_list_eq Hd; (try discriminate); eexists.

(* Theorem 5 *)
Lemma lprove_trans_weight a b l1 l2 l3 (pi1 : l2 ⊦ a) (pi2 : l1 ++ a :: l3 ⊦ b) :
  (l1 <> [] -> length l2 = 1%nat) ->
  { pi' : l1 ++ l2 ++ l3 ⊦ b | lweight pi' < lweight pi1 + lweight pi2 }.
Proof.
remember (lweight pi1 + lweight pi2) as q eqn:Hq.
intro Hbp0. assert (length l1 <> 0%nat -> { c | l2 = [c] }) as Hbp.
{ intro H1. rewrite length_zero_iff_nil in H1. specialize (Hbp0 H1).
  destruct l2 as [ | c [ | ] ]; destr_eq Hbp0. exists c. reflexivity. } clear Hbp0.
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
  exists (ltop_right _). cbn. destruct pi1; cbn; lia.
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
    * destruct (IH _ _ nil _ _ pi1_1 pi2) as [pi' Hs]; [ cbn; lia | assumption | ].
      exists pi'. cbn in *. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * list_simpl. exists lzero_left. cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_1 (lwith_left1 pi2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ nil _ _ pi1_2 (lwith_left1 pi2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * cbn in IH. destruct l2 as [ | d l ].
      -- remember nil as l eqn:Hl. remember (a0 ∧ b) as d eqn:Hd.
         destruct pi1; (try now decomp_list_eq Hl); injection Hd as [= -> ->]; subst.
         destruct (IH _ _ nil _ _ (lone_left _ nil pi1_1) pi2) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
         exists pi1'. cbn in *. lia.
      -- destruct (IH _ _ nil _ _ pi1 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'.
         revert pi' Hs. list_simpl. intros pi' Hs.
         exists (lone_left pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lwith_left1 b pi2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ nil _ _ pi1 pi2'') as [pi' Hs]; [ subst; cbn in *; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
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
    * destruct (IH _ _ nil _ _ pi1_2 pi2) as [pi' Hs]; [ cbn; lia | assumption | ].
      exists pi'. cbn in *. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * list_simpl. exists lzero_left. cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_1 (lwith_left2 pi2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ nil _ _ pi1_2 (lwith_left2 pi2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * cbn in IH. destruct l2 as [ | d l ].
      -- remember nil as l eqn:Hl. remember (b ∧ a0) as d eqn:Hd.
         destruct pi1; (try now decomp_list_eq Hl); injection Hd as [= -> ->]; subst.
         destruct (IH _ _ nil _ _ (lone_left _ nil pi1_2) pi2) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
         exists pi1'. cbn in *. lia.
      -- destruct (IH _ _ nil _ _ pi1 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'.
         revert pi' Hs. list_simpl. intros pi' Hs.
         exists (lone_left pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lwith_left2 b pi2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ nil _ _ pi1 pi2'') as [pi' Hs]; [ subst; cbn in *; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
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
    * destruct (IH _ _ _ _ _ pi2_1 pi1) as [pi1' Hs1]; [ cbn; lia | | ].
      { intros _. exists d. reflexivity. }
      destruct (IH _ _ nil _ _ pi1' pi2_2) as [pi2' Hs2]; [ cbn in *; lia | | ].
      { intros []. reflexivity. }
      revert pi2' Hs2. list_simpl. intros pi2' Hs2.
      exists pi2'. cbn in *. lia.
    * list_simpl. exists lzero_left. cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_1 (lmap_left pi2_1 pi2_2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ nil _ _ pi1_2 (lmap_left pi2_1 pi2_2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | | ].
      { intros []. reflexivity. }
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lone_left pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lmap_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lmap_left pi2_1 pi2_2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ nil _ _ pi1 pi2'') as [pi' Hs]; [ subst; cbn in *; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. change (fupz d :: map fupz l0) with (map fupz (d :: l0)). rewrite <- map_app.
      intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
- (* */lmap_right *)
  revert pi2 IH. list_simpl. intros pi2 IH.
  destruct (IH _ _ _ _ _ pi1 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
  revert pi' Hs. clear. rewrite ? app_assoc, <- (app_assoc l1). intros pi' Hs.
  exists (lmap_right pi'). cbn. lia.
- (* */lzero_left *)
  decomp_list_eq Hl; subst.
  + list_simpl. exists lzero_left. cbn. destruct pi1; cbn; lia.
  + cbn. remember 0 as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists lzero_left. cbn. lia.
    * destruct (IH _ a0 nil _ l3 pi1 lzero_left) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ a0 nil _ l3 pi1 lzero_left) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ a0 nil _ l3 pi1_2 lzero_left) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * list_simpl. exists lzero_left. cbn. lia.
    * destruct (IH _ a0 nil _ l3 pi1_1 lzero_left) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ a0 nil _ l3 pi1_2 lzero_left) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * cbn in IH. destruct l2 as [ | d l ].
      -- cbn in *.
         remember nil as l eqn:Hl. remember 0 as d eqn:Hd.
         destruct pi1; now decomp_list_eq Hl.
      -- destruct (IH _ a0 nil _ l3 pi1 lzero_left) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'.
         revert pi' Hs. list_simpl. intros pi' Hs.
         exists (lone_left pi'). cbn. lia.
    * destruct (IH _ a0 nil _ l3 pi1 lzero_left) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lzero_left a0 l3) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ nil _ _ pi1 pi2'') as [pi' Hs]; [ subst; cbn in *; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite <- map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
- (* */lplus_left *)
  decomp_list_eq Hl; subst.
  + cbn. revert pi2_1 pi2_2 IH. rewrite !app_comm_cons, !app_assoc. intros pi2_1 pi2_2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2_1) as [pi1' Hs1]; [ lia | solve_bp Hbp | ].
    destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi2' Hs2]; [ lia | solve_bp Hbp | ].
    revert pi1' pi2' Hs1 Hs2. rewrite <- !app_assoc, <- !app_comm_cons. intros pi1' pi2' Hs1 Hs2.
    list_simpl. exists (lplus_left pi1' pi2'). cbn in *. lia.
  + cbn. remember (a0 ∨ b) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lplus_left pi2_1 pi2_2). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lplus_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lplus_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (lplus_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * list_simpl. exists lzero_left. cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_1 (lplus_left pi2_1 pi2_2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ nil _ _ pi1_2 (lplus_left pi2_1 pi2_2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 pi2_1) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
      exists pi1'. cbn in *. lia.
    * destruct (IH _ _ nil _ _ pi1 pi2_2) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
      exists pi1'. cbn in *. lia.
    * cbn in IH. destruct l2 as [ | d l ].
      -- cbn in *. remember nil as l eqn:Hl. remember (a0 ∨ b) as d eqn:Hd.
         destruct pi1; (try now decomp_list_eq Hl); injection Hd as [= -> ->]; subst.
         ++ revert pi1 IH. cbn. rewrite <- (app_nil_l _). intros pi1 IH.
            destruct (IH _ _ nil _ _ (lone_left pi1) pi2_1) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
            exists pi1'. cbn in *. lia.
         ++ revert pi1 IH. cbn. rewrite <- (app_nil_l _). intros pi1 IH.
            destruct (IH _ _ nil _ _ (lone_left pi1) pi2_2) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
            exists pi1'. cbn in *. lia.
      -- destruct (IH _ _ nil _ _ pi1 (lplus_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'.
         revert pi' Hs. list_simpl. intros pi' Hs.
         exists (lone_left pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lplus_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lplus_left pi2_1 pi2_2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ nil _ _ pi1 pi2'') as [pi' Hs]; [ subst; cbn in *; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
- (* */lplus_right1 *)
  destruct (IH _ _ _ _ _ pi1 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
  exists (lplus_right1 pi'). cbn. lia.
- (* */lplus_right2 *)
  destruct (IH _ _ _ _ _ pi1 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
  exists (lplus_right2 pi'). cbn. lia.
- (* */lone_left *)
  cbn. decomp_list_eq Hl; subst.
  + revert pi2 IH. rewrite !app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (lone_left pi). cbn. lia.
  + cbn. remember 1 as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lone_left pi2). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lone_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl.  intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lone_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (lone_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * list_simpl. exists lzero_left. cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_1 (lone_left pi2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ nil _ _ pi1_2 (lone_left pi2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * cbn in IH. destruct l2 as [ | d l ].
      -- cbn in *. exists (lone_left pi2). cbn. lia.
      -- destruct (IH _ _ nil _ _ pi1 (lone_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'.
         revert pi' Hs. list_simpl. intros pi' Hs.
         exists (lone_left pi'). cbn. lia.
    * exists pi2. lia.
    * destruct (IH _ _ nil _ _ pi1 (lone_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lone_left pi2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ nil _ _ pi1 pi2'') as [pi' Hs]; [ subst; cbn in *; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
- (* */lone_right *)
  exfalso. decomp_list_eq Hl.
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
    * list_simpl. exists lzero_left. cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_1 (lfrl_left e pi2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ nil _ _ pi1_2 (lfrl_left e pi2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * cbn in IH. destruct l2 as [ | d l ].
      -- cbn in *. remember nil as l eqn:Hl. remember (∀ x a0) as d eqn:Hd.
         destruct pi1; (try now decomp_list_eq Hl); injection Hd as [= -> ->]; subst.
         destruct (psubs 0 _ e pi1) as [pi1' Hs'].
         revert pi1' Hs'. rewrite nsubs_subs_com by (rewrite e; intros []). cbn.
         rewrite nsubs_z_fup. intros pi1' Hs'.
         destruct (IH _ _ nil _ _ (lone_left pi1') pi2) as [pi1'' Hs1]; [ cbn; lia | solve_bp Hbp | ].
         exists pi1''. cbn in *. lia.
      -- destruct (IH _ _ nil _ _ pi1 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'.
         revert pi' Hs. list_simpl. intros pi' Hs.
         exists (lone_left pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lfrl_left e0 pi'). cbn. lia.
    * destruct (psubs 0 _ e pi1) as [pi1' Hs'].
      revert pi1' Hs'. rewrite nsubs_subs_com by (rewrite e; intros []). cbn.
      rewrite map_map. rewrite (map_ext (fun x => nsubs 0 b (fupz x)) (fun x => x)) by apply nsubs_z_fup.
      rewrite nsubs_z_fup. rewrite map_id. intros pi1' Hs'.
      destruct (IH _ _ nil _ _ pi1' pi2) as [pi1'' Hs1]; [ cbn; lia | solve_bp Hbp | ].
      exists pi1''. cbn in *. lia.
    * remember (lfrl_left e pi2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ nil _ _ pi1 pi2'') as [pi' Hs]; [ subst; cbn in *; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
- (* */lfrl_right *)
  revert pi2 IH. cbn. rewrite (map_app fupz l1 (a :: l3)). cbn. intros pi2 IH.
  destruct (pup 0 pi1) as [pi1' Hs1].
  destruct (IH _ _ _ _ _ pi1' pi2) as [pi' Hs]; [ cbn; lia | | ].
  { intro Hl1. rewrite length_map in Hl1. destruct (Hbp Hl1) as [d ->]. exists (fupz d). reflexivity. }
  revert pi' Hs. rewrite <- !map_app. intros pi' Hs.
  exists (lfrl_right pi'). cbn. lia.
- (* */lexs_left *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. list_simpl. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (pup 0 pi1) as [pi1' Hs1].
    destruct (IH _ _ _ _ _ pi1' pi2) as [pi Hs]; [ lia | | ].
    { list_simpl. rewrite !length_map.
      intro Hl. destruct Hbp; [ rewrite ?length_app in *; cbn in *; lia | ].
      subst. exists (fupz x0). reflexivity. }
    revert pi Hs. list_simpl. rewrite <- !map_app. intros pi Hs.
    exists (lexs_left pi). cbn. lia.
  + cbn. remember (lexs x a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lexs_left pi2). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lexs_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lexs_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_2 (lexs_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lmap_left pi1_1 pi'). cbn. lia.
    * exists lzero_left. cbn. lia.
    * destruct (IH _ _ nil _ _ pi1_1 (lexs_left pi2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ nil _ _ pi1_2 (lexs_left pi2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * cbn in IH. destruct l2 as [ | d l ].
      -- cbn in *. remember nil as l eqn:Hl. remember (lexs x a0) as d eqn:Hd.
         destruct pi1; (try now decomp_list_eq Hl); injection Hd as [= -> ->]; subst.
         destruct (psubs 0 _ e pi2) as [pi2' Hs'].
         revert pi2' Hs'. list_simpl. rewrite nsubs_subs_com by (rewrite e; intros []). cbn.
         rewrite !map_map. rewrite !(map_ext (fun x => nsubs 0 b (fupz x)) (fun x => x)) by apply nsubs_z_fup.
         rewrite !nsubs_z_fup. rewrite !map_id. intros pi2' Hs'.
         destruct (IH _ _ nil _ _ (lone_left pi1) pi2') as [pi2'' Hs2]; [ cbn; lia | solve_bp Hbp | ].
         exists pi2''. cbn in *. lia.
      -- destruct (IH _ _ nil _ _ pi1 (lexs_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'.
         revert pi' Hs. list_simpl. intros pi' Hs.
         exists (lone_left pi'). cbn. lia.
    * destruct (IH _ _ nil _ _ pi1 (lexs_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lexs_left pi2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ nil _ _ pi1 pi2'') as [pi' Hs]; [ subst; cbn in *; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
    * destruct (psubs 0 _ e pi2) as [pi2' Hs'].
      revert pi2' Hs'. list_simpl. rewrite nsubs_subs_com by (rewrite e; intros []). cbn.
      rewrite !map_map. rewrite !(map_ext (fun x => nsubs 0 b (fupz x)) (fun x => x)) by apply nsubs_z_fup.
      rewrite !nsubs_z_fup. rewrite !map_id. intros pi2' Hs'.
      destruct (IH _ _ nil _ _ pi1 pi2') as [pi2'' Hs2]; [ cbn; lia | solve_bp Hbp | ].
      exists pi2''. cbn in *. lia.
- (* */lexs_right *)
  destruct (IH _ _ _ _ _ pi1 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
  exists (lexs_right e pi'). cbn. lia.
Qed.

Lemma lcut a b l1 l2 l3 : (l1 <> [] -> length l2 = 1%nat) ->
  l2 ⊦ a -> l1 ++ a :: l3 ⊦ b -> l1 ++ l2 ++ l3 ⊦ b.
Proof. intros Hbp pi1 pi2. destruct (lprove_trans_weight _ pi1 pi2 Hbp) as [pi _]. exact pi. Qed.

Lemma lsubst a b c l1 l2 : [a] ⊦ b -> l1 ++ b :: l2 ⊦ c -> l1 ++ a :: l2 ⊦ c.
Proof. intros pi1 pi2. refine (lcut _ _ pi1 pi2). intros. reflexivity. Qed.

Lemma ltrans b c l1 l2 : l1 ⊦ b -> b :: l2 ⊦ c -> l1 ++ l2 ⊦ c.
Proof.
intros pi1 pi2. rewrite <- (app_nil_l _) in pi2. refine (lcut _ _ pi1 pi2).
intros []. reflexivity.
Qed.


(** * Admissible rules *)

Lemma lwith_left1_gen a b c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ a ∧ b :: l2 ⊦ c.
Proof. intro pi. refine (lsubst _ _ _ pi). apply lwith_left1, lidentity. Qed.

Lemma lwith_left2_gen a b c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ b ∧ a :: l2 ⊦ c.
Proof. intro pi. refine (lsubst _ _ _ pi). apply lwith_left2, lidentity. Qed.

Lemma lfrl_left_gen a x b c l1 l2 : closed b -> l1 ++ subs x b a :: l2 ⊦ c -> l1 ++ lfrl x a :: l2 ⊦ c.
Proof. intros Hc pi. refine (lsubst _ _ _ pi). apply (@lfrl_left _ _ _ _ _ Hc), lidentity. Qed.

Lemma lmap_right_inv a b l : l ⊦ b / a -> l · a ⊦ b.
Proof.
intro pi.
assert ([b / a; a] ⊦ b) as pi' by (apply lmap_left; apply lidentity).
exact (ltrans pi pi').
Qed.


(** * Non conservativity of IS over ISₕ *)

From InterPT Require lambek_is.

(* Example 6 *)
Lemma plus_formula_not_ish : notT ([lambek_is.plus_formula_l] ⊦ lambek_is.plus_formula_r).
Proof.
intros pi%lmap_right_inv.
inversion pi; subst.
- inversion H3. subst. inversion H5; inversion H4. subst. inversion H12.
- inversion H3. subst. inversion H5; inversion H4. subst. inversion H11.
Qed.
