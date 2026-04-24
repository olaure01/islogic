(* Lambek Calculus with parameterized constraint of left-rule for arrow *)

From Stdlib Require Import PeanoNat Lia Wf_nat.
From OLlibs Require Import Logic_Datatypes_more List_more.
From InterPT Require Export lformulas.
Export LogicNotations ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.

Lemma length_one_iffT_sgt A (l : list A) : (length l = 1%nat) <=> { a | l = [a] }.
Proof.
destruct l as [ | a [ | ? l ] ].
- split; [ intros [=] | intros [? [=]] ].
- split; intro; [ exists a | ]; reflexivity.
- split; [ intros [=] | intros [? [=]] ].
Qed.


(** * Lambek Calculus *)

(** ** Rules *)

Reserved Notation "l ⎹ bp ⊦ a" (at level 65, format "l ⎹ bp ⊦  a").
(** value [true] for [bp] activates the S-constraint *)
Inductive lprove {bp : bool} : list lform -> lform -> Type :=
| lidentity a : [a]⎹bp⊦ a
| ltop_right l : l⎹bp⊦ 𝖳
| lwith_left1 a b c l1 l2 : l1 ++ a :: l2⎹bp⊦ c -> l1 ++ a ∧ b :: l2⎹bp⊦ c
| lwith_left2 a b c l1 l2 : l1 ++ a :: l2⎹bp⊦ c -> l1 ++ b ∧ a :: l2⎹bp⊦ c
| lwith_right a b l : l⎹bp⊦ a -> l⎹bp⊦ b -> l⎹bp⊦ a ∧ b
| lmap_left a b c l1 l2 l3 : (bp = true -> l1 = [] /\ length l2 = 1%nat) ->
    l2⎹bp⊦ a -> l1 ++ b :: l3⎹bp⊦ c -> l1 ++ b / a :: l2 ++ l3⎹bp⊦ c
| lmap_right a b l : l · a⎹bp⊦ b -> l⎹bp⊦ b / a
| lzero_left a l1 l2 : l1 ++ 0 :: l2⎹bp⊦ a
| lplus_left a b c l1 l2 : l1 ++ a :: l2⎹bp⊦ c -> l1 ++ b :: l2⎹bp⊦ c -> l1 ++ a ∨ b :: l2⎹bp⊦ c
| lplus_right1 a b l : l⎹bp⊦ a -> l⎹bp⊦ a ∨ b
| lplus_right2 a b l : l⎹bp⊦ a -> l⎹bp⊦ b ∨ a
| lone_left a l1 l2 : l1 ++ l2⎹bp⊦ a -> l1 ++ 1 :: l2⎹bp⊦ a
| lone_right : nil⎹bp⊦ 1
| lfrl_left a x b c l1 l2 : closed b -> l1 ++ subs x b a :: l2⎹bp⊦ c -> l1 ++ lfrl x a :: l2⎹bp⊦ c
| lfrl_right a x l : map fupz l⎹bp⊦ subs x (dvar 0) (fupz a) -> l⎹bp⊦ lfrl x a
| lexs_left a x c l1 l2 : map fupz l1 ++ subs x (dvar 0) (fupz a) :: map fupz l2⎹bp⊦ fupz c ->
   l1 ++ lexs x a :: l2⎹bp⊦ c
| lexs_right a x b l : closed b -> l⎹bp⊦ subs x b a -> l⎹bp⊦ lexs x a
where "l ⎹ bp ⊦ a" := (@lprove bp l a).
Arguments lidentity {_ _}, [_] _, _ _.
Arguments ltop_right {_ _}, [_] _, _ _.
Arguments lwith_left1 [_ _ _ _ _ _] _, [_ _] _ [_ _ _] _, [_] _ _ _ _ _ _, _ _ _ _ _ _ _.
Arguments lwith_left2 [_ _ _ _ _ _] _, [_ _] _ [_ _ _] _, [_] _ _ _ _ _ _, _ _ _ _ _ _ _.
Arguments lwith_right [_ _ _ _] _ _, [_] _ _ _ _ _, _ _ _ _ _ _.
Arguments lmap_left [_ _ _ _ _ _ _ _] _ _, [_ _ _ _ _ _ _] _ _ _, [_] _ _ _ _ _ _ _ _ _, _ _ _ _ _ _ _ _ _ _.
Arguments lmap_right [_ _ _ _] _, [_] _ _ _ _, _ _ _ _ _.
Arguments lzero_left {_ _ _ _}, [_] _ _ _, _ _ _ _.
Arguments lplus_left [_ _ _ _ _ _] _ _, [_] _ _ _ _ _ _ _, _ _ _ _ _ _ _ _.
Arguments lplus_right1 [_ _ _ _] _, [_ _] _ [_] _, [_] _ _ _ _, _ _ _ _ _.
Arguments lplus_right2 [_ _ _ _] _, [_ _] _ [_] _, [_] _ _ _ _, _ _ _ _ _.
Arguments lone_left [_ _ _ _] _, [_ _] _ _ _, [_] _ _ _ _, _ _ _ _ _.
Arguments lone_right {_}, _.
Arguments lfrl_left [_ _ _ _ _ _ _ _] _, [_ _ _ _ _ _ _] _ _, _ _ _ _ _ _ _ _.
Arguments lfrl_right [_ _ _ _] _, [_ _] _ [_] _, [_] _ _ _ _, _ _ _ _ _.
Arguments lexs_left [_ _ _ _ _ _] _, [_ _] _ [_ _] _, [_] _ _ _ _ _, _ _ _ _ _ _.
Arguments lexs_right [_ _ _ _ _ _] _, [_ _ _ _ _] _ _, _ _ _ _ _ _ _.



Section WithParameter.

Variable bp : bool.

Notation lprove := (@lprove bp).
Notation "l ⊦ a" := (lprove l a) (at level 65, format "l  ⊦  a").

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
  assert (bp = true -> map (nsubs k f) l1 = [] /\ length (map (nsubs k f) l2) = 1%nat) as Hbp.
  { clear - a0. intro Hp. rewrite length_map. destruct (a0 Hp) as [-> ->]. split; reflexivity. }
  exists (lmap_left Hbp pi1' pi2'). cbn. lia.
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
  rewrite map_app. simpl map. rewrite nsubs_subs_com.
  2:{ rewrite Hc. intros []. }
  cbn. rewrite !map_map.
  rewrite !(map_ext (fun x => nsubs (S k) (fupz f) (fupz x)) (fun x => fupz (nsubs k f x))).
  2,3: apply nsubs_fup_com.
  rewrite !nsubs_fup_com.
  rewrite <- (map_map _ _ l1), <- (map_map _ _ l2).
  intro pi'.
  rewrite map_app. simpl map.
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
  assert (bp = true -> map (fup k) l1 = [] /\ length (map (fup k) l2) = 1%nat) as Hbp.
  { clear - a0. intro Hp. rewrite length_map. destruct (a0 Hp) as [-> ->]. split; reflexivity. }
  exists (lmap_left Hbp pi1' pi2'). cbn. lia.
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
  rewrite map_app. simpl map.
  rewrite !fup_subs_com. cbn. rewrite !fup_fup_com.
  rewrite !map_map.
  rewrite !(map_ext (fun x => fup (S k) (fupz x)) (fun x => fupz (fup k x))) by apply fup_fup_com.
  rewrite <- (map_map _ _ l1), <- (map_map _ _ l2).
  intro pi'.
  rewrite map_app. simpl map.
  exists (lexs_left pi'). reflexivity.
- cbn. rewrite <- Hs. clear Hs.
  rewrite <- (freevars_fup k) in e.
  revert pi'. list_simpl. rewrite fup_subs_com.
  intro pi'.
  exists (lexs_right e pi'). reflexivity.
Qed.


(** *** Cut Elimination *)

Ltac solve_bp H := intros; apply H; [ assumption | rewrite ?length_app in *; cbn in *; lia ].

Ltac solve_bp2 H :=
  let Hp := fresh in
  let Hl := fresh in
  let d := fresh in
  let Hd := fresh in
  now intros Hp Hl; destruct (H Hp Hl) as [d Hd]; decomp_list_eq Hd; (try discriminate); eexists.

Lemma lprove_trans_weight a b l1 l2 l3 (pi1 : l2 ⊦ a) (pi2 : l1 ++ a :: l3 ⊦ b) :
  (bp = true -> l1 <> [] -> length l2 = 1%nat) ->
  { pi' : l1 ++ l2 ++ l3 ⊦ b | lweight pi' < lweight pi1 + lweight pi2 }.
Proof.
remember (lweight pi1 + lweight pi2) as q eqn:Hq.
intro Hbp0. assert (bp = true -> length l1 <> 0%nat -> { c | l2 = [c] }) as Hbp.
{ intros Hp H1. rewrite length_zero_iff_nil in H1. specialize (Hbp0 Hp H1).
  apply length_one_iffT_sgt. assumption. } clear Hbp0.
induction q as [q IHq] using (well_founded_induction_type lt_wf) in a, b, l1, l2, l3, pi1, pi2, Hq, Hbp |- *.
subst q.
assert (forall a' b' l1' l2' l3' (pi1' : l2' ⊦ a') (pi2' : l1' ++ a' :: l3' ⊦ b'),
  lweight pi1' + lweight pi2' < lweight pi1 + lweight pi2 ->
  (bp = true -> length l1' <> 0%nat ->  { c | l2' = [c] }) ->
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
    * destruct (IH _ _ _ _ _ pi1 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_1 pi2) as [pi' Hs]; [ cbn; lia | assumption | ].
      exists pi'. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite 2 app_assoc. intros pi' Hs.
      assert (bp = true -> l1 ++ l0 = [] /\ length l2 = 1%nat) as Hbp'.
      { clear - a1 Hbp. intro Hp. specialize (a1 Hp) as [-> Hla]. specialize (Hbp Hp).
        split; [ | assumption ].
        destruct l1 as [ | d l1 ]; [ reflexivity | exfalso ].
        destruct Hbp as [c Hc]; [ intros [=] | ]. decomp_list_eq Hc. discriminate. }
      exists (lmap_left Hbp' pi1_1 pi'). cbn. lia.
    * list_simpl. rewrite app_assoc. exists lzero_left. cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_1 (lwith_left1 pi2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ _ _ _ pi1_2 (lwith_left1 pi2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. rewrite !app_assoc. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * cbn in IH. remember (l0 ++ l2) as l eqn:Hl. destruct l as [ | d l ].
      -- decomp_list_eq Hl. cbn in *.
         remember nil as l eqn:Hl. remember (a0 ∧ b) as d eqn:Hd.
         destruct pi1; (try now decomp_list_eq Hl); injection Hd as [= -> ->]; subst.
         destruct (IH _ _ _ _ _ (lone_left _ _ nil nil pi1_1) pi2) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
         exists pi1'. cbn in *. lia.
      -- destruct (IH _ _ _ _ _ pi1 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'. subst l'.
         revert pi' Hs. list_simpl. rewrite app_assoc. intros pi' Hs.
         rewrite app_assoc. exists (lone_left pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lwith_left1 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lwith_left1 b pi2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ _ _ _ pi1 pi2'') as [pi' Hs];
        [ subst; cbn in *; lia | rewrite length_map; solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc, <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. rewrite ! app_assoc. intros pi Hs.
    exists (lwith_left1 pi). cbn. lia.
- (* */lwith_left2 *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. list_simpl. intros pi Hs.
    exists (lwith_left2 pi). cbn. lia.
  + cbn. remember (b ∧ a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lwith_left2 pi2). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_2 pi2) as [pi' Hs]; [ cbn; lia | assumption | ].
      exists pi'. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite 2 app_assoc. intros pi' Hs.
      assert (bp = true -> l1 ++ l0 = [] /\ length l2 = 1%nat) as Hbp'.
      { clear - a1 Hbp. intro Hp. specialize (a1 Hp) as [-> Hla]. specialize (Hbp Hp).
        split; [ | assumption ].
        destruct l1 as [ | d l1 ]; [ reflexivity | exfalso ].
        destruct Hbp as [c Hc]; [ intros [=] | ]. decomp_list_eq Hc. discriminate. }
      exists (lmap_left Hbp' pi1_1 pi'). cbn. lia.
    * list_simpl. rewrite app_assoc. exists lzero_left. cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_1 (lwith_left2 pi2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ _ _ _ pi1_2 (lwith_left2 pi2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. rewrite !app_assoc. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * cbn in IH. remember (l0 ++ l2) as l eqn:Hl. destruct l as [ | d l ].
      -- decomp_list_eq Hl. cbn in *.
         remember nil as l eqn:Hl. remember (b ∧ a0) as d eqn:Hd.
         destruct pi1; (try now decomp_list_eq Hl); injection Hd as [= -> ->]; subst.
         destruct (IH _ _ _ _ _ (lone_left _ _ nil nil pi1_2) pi2) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
         exists pi1'. cbn in *. lia.
      -- destruct (IH _ _ _ _ _ pi1 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'. subst l'.
         revert pi' Hs. list_simpl. rewrite app_assoc. intros pi' Hs.
         rewrite app_assoc. exists (lone_left pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lwith_left2 pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lwith_left2 b pi2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ _ _ _ pi1 pi2'') as [pi' Hs];
        [ subst; cbn in *; lia | rewrite length_map; solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc, <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. rewrite ! app_assoc. intros pi Hs.
    exists (lwith_left2 pi). cbn. lia.
- (* */lwith_right *)
  destruct (IH _ _ _ _ _ pi1 pi2_1) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
  destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi2' Hs2]; [ cbn; lia | solve_bp Hbp | ].
  exists (lwith_right pi1' pi2'). cbn. lia.
- (* */lmap_left *)
  decomp_list_eq Hl; subst.
  + decomp_list_eq Hl1; subst.
    * destruct (IH _ _ _ _ _ pi1 pi2_1) as [pi1' Hs']; [ lia | solve_bp Hbp | ].
      revert pi2_2 IH pi1' Hs'. list_simpl.
      rewrite app_comm_cons, (app_assoc (_ / _ :: _)), (app_assoc ((_ / _ :: _) ++ _)), <- 2 app_comm_cons,
        <- app_assoc.
      intros pi2_2 IH pi1' Hs'.
      assert (bp = true -> l0 = [] /\ length (l ++ l2 ++ l1) = 1%nat) as Hbp'.
      { clear - a1 Hbp. intro Hp. specialize (a1 Hp) as [-> Hla]. specialize (Hbp Hp).
        split; [ reflexivity | ]. rewrite !length_app in *. cbn in *.
        destruct Hbp as [c ->]; [  | cbn ]; lia. }
      exists (lmap_left Hbp' pi1' pi2_2). cbn. lia.
    * revert pi2_2 IH. cbn. rewrite app_comm_cons, app_assoc. intros pi2_2 IH.
      destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi1' Hs']; [ lia | solve_bp Hbp | ].
      revert pi2_2 IH pi1' Hs'. list_simpl. intros pi2_2 IH pi1' Hs'.
      exists (lmap_left a1 pi2_1 pi1'). cbn. lia.
  + cbn. remember (b / a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lmap_left a1 pi2_1 pi2_2). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lmap_left a1 pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lmap_left a1 pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (lmap_left a1 pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite 3 app_assoc. intros pi' Hs.
      assert (bp = true -> l1 ++ l0 = [] /\ length l2 = 1%nat) as Hbp'.
      { intro Hp. destruct (a2 Hp) as [-> ->], (a1 Hp) as [-> _]. repeat split. }
      exists (lmap_left Hbp' pi1_1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi2_1 pi1) as [pi1' Hs1]; [ cbn; lia | | ].
      { intros Hp _. destruct (a1 Hp) as [_ Hl4%length_one_iffT_sgt]. assumption. }
      destruct (IH _ _ _ _ _ pi1' pi2_2) as [pi2' Hs2]; [ cbn; lia | | ].
      { intros Hp Hl1. exfalso. destruct (a1 Hp) as [-> _]. contradiction Hl1. reflexivity. }
      revert pi2' Hs2. list_simpl. intros pi2' Hs2.
      exists pi2'. lia.
    * list_simpl. rewrite app_assoc. exists lzero_left. cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_1 (lmap_left a1 pi2_1 pi2_2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ _ _ _ pi1_2 (lmap_left a1 pi2_1 pi2_2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. rewrite !app_assoc. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lmap_left a1 pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | | ].
      { intros Hp Hl1. exfalso. destruct (a1 Hp) as [-> _]. contradiction Hl1. reflexivity. }
      revert pi' Hs. list_simpl. rewrite app_assoc. intros pi' Hs.
      rewrite app_assoc. exists (lone_left pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lmap_left a1 pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lmap_left a1 pi2_1 pi2_2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ _ _ _ pi1 pi2'') as [pi' Hs];
        [ subst; cbn in *; lia | rewrite length_map; solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc, <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
  + revert pi2_2 IH. cbn. rewrite <- app_assoc, <- app_comm_cons. intros pi2_2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi1' Hs']; [ lia | solve_bp Hbp | ].
    revert pi2_2 IH pi1' Hs'. rewrite app_comm_cons, ! app_assoc, <- (app_assoc _ l2). intros pi2_2 IH pi1' Hs'.
    assert (bp = true -> l1 ++ l2 ++ l = [] /\ length l4 = 1%nat) as Hbp'.
    { intro Hp. exfalso. destruct (a1 Hp) as [Hnil _]. decomp_list_eq Hnil. }
    exists (lmap_left Hbp' pi2_1 pi1'). cbn. lia.
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
    * destruct (IH _ a0 l1 _ l3 pi1 lzero_left) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ a0 l1 _ l3 pi1 lzero_left) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ a0 l1 _ l3 pi1_2 lzero_left) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite 3 app_assoc. intros pi' Hs.
      assert (bp = true -> l1 ++ l0 = [] /\ length l2 = 1%nat) as Hbp'.
      { intro Hp. destruct (a1 Hp) as [-> ->].
        destruct l1 as [ | d l1 ]; [ repeat split | exfalso ].
        destruct (Hbp Hp) as [e He]; [ intros [=] | decomp_list_eq He ].
        destruct (a1 Hp) as [_ [=]]. }
      revert pi' Hs. list_simpl. rewrite 2 app_assoc. intros pi' Hs.
      exists (lmap_left Hbp' pi1_1 pi'). cbn. lia.
    * list_simpl. rewrite app_assoc. exists lzero_left. cbn. lia.
    * destruct (IH _ a0 l1 _ l3 pi1_1 lzero_left) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ a0 l1 _ l3 pi1_2 lzero_left) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. rewrite !app_assoc. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * cbn in IH. remember (l0 ++ l2) as l eqn:Hl. destruct l as [ | d l ].
      -- decomp_list_eq Hl. cbn in *.
         remember nil as l eqn:Hl. remember 0 as d eqn:Hd.
         destruct pi1; now decomp_list_eq Hl.
      -- destruct (IH _ a0 l1 _ l3 pi1 lzero_left) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'. subst l'.
         revert pi' Hs. list_simpl. rewrite app_assoc. intros pi' Hs.
         rewrite app_assoc. exists (lone_left pi'). cbn. lia.
    * destruct (IH _ a0 l1 _ l3 pi1 lzero_left) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lzero_left bp a0 l1 l3) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ _ _ _ pi1 pi2'') as [pi' Hs];
        [ subst; cbn in *; lia | rewrite length_map; solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc, <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
  + rewrite !app_assoc. exists lzero_left. cbn. destruct pi1; cbn; lia.
- (* */lplus_left *)
  decomp_list_eq Hl; subst.
  + cbn. revert pi2_1 pi2_2 IH. rewrite !app_comm_cons, !app_assoc. intros pi2_1 pi2_2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2_1) as [pi1' Hs1]; [ lia | solve_bp Hbp | ].
    destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi2' Hs2]; [ lia | solve_bp Hbp | ].
    revert pi1' pi2' Hs1 Hs2. rewrite <- !app_assoc, <- !app_comm_cons. intros pi1' pi2' Hs1 Hs2.
    list_simpl. exists (lplus_left pi1' pi2'). cbn. lia.
  + cbn. remember (a0 ∨ b) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lplus_left pi2_1 pi2_2). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lplus_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lplus_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (lplus_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs. rewrite <- (app_assoc l2).
      assert (bp = true -> l1 ++ l0 = [] /\ length l2 = 1%nat) as Hbp'.
      { intro Hp. destruct (a1 Hp) as [-> ->].
        destruct l1; [split; reflexivity | exfalso ].
        destruct (Hbp Hp) as [d Heq]; [ cbn; lia | ].
        decomp_list_eq Heq. destruct (a1 Hp) as [_ Hl]. discriminate Hl. }
      exists (lmap_left Hbp' pi1_1 pi'). cbn. lia.
    * list_simpl. rewrite app_assoc. exists lzero_left. cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_1 (lplus_left pi2_1 pi2_2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ _ _ _ pi1_2 (lplus_left pi2_1 pi2_2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. rewrite !app_assoc. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 pi2_1) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
      exists pi1'. lia.
    * destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
      exists pi1'. lia.
    * cbn in IH. remember (l0 ++ l2) as l eqn:Hl. destruct l as [ | d l ].
      -- decomp_list_eq Hl. cbn in *.
         remember nil as l eqn:Hl. remember (a0 ∨ b) as d eqn:Hd.
         destruct pi1; (try now decomp_list_eq Hl); injection Hd as [= -> ->]; subst.
         ++ revert pi1 IH. cbn. rewrite <- (app_nil_l _). intros pi1 IH.
            destruct (IH _ _ _ _ _ (lone_left pi1) pi2_1) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
            exists pi1'. cbn in *. lia.
         ++ revert pi1 IH. cbn. rewrite <- (app_nil_l _). intros pi1 IH.
            destruct (IH _ _ _ _ _ (lone_left pi1) pi2_2) as [pi1' Hs1]; [ cbn; lia | solve_bp Hbp | ].
            exists pi1'. cbn in *. lia.
      -- destruct (IH _ _ _ _ _ pi1 (lplus_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'. subst l'.
         revert pi' Hs. list_simpl. rewrite app_assoc. intros pi' Hs.
         rewrite app_assoc.
         exists (lone_left pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lplus_left pi2_1 pi2_2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lplus_left pi2_1 pi2_2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ _ _ _ pi1 pi2'') as [pi' Hs];
        [ subst; cbn in *; lia | rewrite length_map; solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc, <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
  + cbn. revert pi2_1 pi2_2 IH. list_simpl. intros pi2_1 pi2_2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2_1) as [pi1' Hs1]; [ lia | solve_bp Hbp | ].
    destruct (IH _ _ _ _ _ pi1 pi2_2) as [pi2' Hs2]; [ lia | solve_bp Hbp | ].
    revert pi1' pi2' Hs1 Hs2. rewrite !app_assoc. intros pi1' pi2' Hs1 Hs2.
    exists (lplus_left pi1' pi2'). cbn. lia.
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
    * destruct (IH _ _ _ _ _ pi1 (lone_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lone_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (lone_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite 2 app_assoc. intros pi' Hs.
      assert (bp = true -> l1 ++ l0 = [] /\ length l2 = 1%nat) as Hbp'.
      { clear - a1 Hbp. intro Hp. specialize (a1 Hp) as [-> Hla]. specialize (Hbp Hp).
        split; [ | assumption ].
        destruct l1 as [ | d l1 ]; [ reflexivity | exfalso ].
        destruct Hbp as [c Hc]; [ intros [=] | ].
        decomp_list_eq Hc. discriminate. }
      exists (lmap_left Hbp' pi1_1 pi'). cbn. lia.
    * list_simpl. rewrite app_assoc. exists lzero_left. cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_1 (lone_left pi2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ _ _ _ pi1_2 (lone_left pi2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. rewrite !app_assoc. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * cbn in IH. remember (l0 ++ l2) as l eqn:Hl. destruct l as [ | d l ].
      -- decomp_list_eq Hl.
         exists (lone_left pi2). cbn. lia.
      -- destruct (IH _ _ _ _ _ pi1 (lone_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'. subst l'.
         revert pi' Hs. list_simpl. rewrite app_assoc. intros pi' Hs.
         rewrite app_assoc. exists (lone_left pi'). cbn. lia.
    * exists pi2. lia.
    * destruct (IH _ _ _ _ _ pi1 (lone_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lone_left pi2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ _ _ _ pi1 pi2'') as [pi' Hs];
        [ subst; cbn in *; lia | rewrite length_map; solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc, <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. rewrite ! app_assoc. intros pi Hs.
    exists (lone_left pi). cbn. lia.
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
    * destruct (IH _ _ _ _ _ pi1 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite 2 app_assoc. intros pi' Hs.
      assert (bp = true -> l1 ++ l0 = [] /\ length l2 = 1%nat) as Hbp'.
      { clear - a1 Hbp. intro Hp. specialize (a1 Hp) as [-> Hla]. specialize (Hbp Hp).
        split; [ | assumption ].
        destruct l1 as [ | d l1 ]; [ reflexivity | exfalso ].
        destruct Hbp as [c Hc]; [ intros [=] | ]. decomp_list_eq Hc. discriminate. }
      exists (lmap_left Hbp' pi1_1 pi'). cbn. lia.
    * list_simpl. rewrite app_assoc. exists lzero_left. cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_1 (lfrl_left e pi2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ _ _ _ pi1_2 (lfrl_left e pi2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. rewrite !app_assoc. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * cbn in IH. remember (l0 ++ l2) as l eqn:Hl. destruct l as [ | d l ].
      -- decomp_list_eq Hl. cbn in *.
         remember nil as l eqn:Hl. remember (∀ x a0) as d eqn:Hd.
         destruct pi1; (try now decomp_list_eq Hl); injection Hd as [= -> ->]; subst.
         destruct (psubs 0 _ e pi1) as [pi1' Hs'].
         revert pi1' Hs'. rewrite nsubs_subs_com by (rewrite e; intros []). cbn.
         rewrite nsubs_z_fup. intros pi1' Hs'.
         destruct (IH _ _ _ _ _ (lone_left _ _ nil nil pi1') pi2) as [pi1'' Hs1];
           [ cbn; lia | solve_bp Hbp | ].
         exists pi1''. cbn in *. lia.
      -- destruct (IH _ _ _ _ _ pi1 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'. subst l'.
         revert pi' Hs. list_simpl. rewrite app_assoc. intros pi' Hs.
         rewrite app_assoc. exists (lone_left pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lfrl_left e pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lfrl_left e0 pi'). cbn. lia.
    * destruct (psubs 0 _ e pi1) as [pi1' Hs'].
      revert pi1' Hs'. rewrite nsubs_subs_com by (rewrite e; intros []). cbn.
      rewrite map_map. rewrite (map_ext (fun x => nsubs 0 b (fupz x)) (fun x => x)) by apply nsubs_z_fup.
      rewrite nsubs_z_fup. rewrite map_id. intros pi1' Hs'.
      destruct (IH _ _ _ _ _ pi1' pi2) as [pi1'' Hs1]; [ cbn; lia | solve_bp Hbp | ].
      exists pi1''. cbn in *. lia.
    * remember (lfrl_left e pi2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ _ _ _ pi1 pi2'') as [pi' Hs];
        [ subst; cbn in *; lia | rewrite length_map; solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc, <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (IH _ _ _ _ _ pi1 pi2) as [pi Hs]; [ lia | solve_bp Hbp | ].
    revert pi Hs. rewrite ! app_assoc. intros pi Hs.
    exists (lfrl_left e pi). cbn. lia.
- (* */lfrl_right *)
  revert pi2 IH. cbn. rewrite (map_app fupz l1 (a :: l3)). cbn. intros pi2 IH.
  destruct (pup 0 pi1) as [pi1' Hs1].
  destruct (IH _ _ _ _ _ pi1' pi2) as [pi' Hs]; [ cbn; lia | | ].
  { intros Hp Hl1. rewrite length_map in Hl1. destruct (Hbp Hp Hl1) as [d ->]. exists (fupz d). reflexivity. }
  revert pi' Hs. rewrite <- !map_app. intros pi' Hs.
  exists (lfrl_right pi'). cbn. lia.
- (* */lexs_left *)
  decomp_list_eq Hl; subst; cbn.
  + revert pi2 IH. list_simpl. rewrite app_comm_cons, app_assoc. intros pi2 IH.
    destruct (pup 0 pi1) as [pi1' Hs1].
    destruct (IH _ _ _ _ _ pi1' pi2) as [pi Hs]; [ lia | | ].
    { rewrite length_app. list_simpl. rewrite !length_map.
      intros Hb Hl. destruct (Hbp Hb); [ rewrite ?length_app in *; cbn in *; lia | ].
      subst. exists (fupz x0). reflexivity. }
    revert pi Hs. list_simpl. rewrite <- !map_app. intros pi Hs.
    exists (lexs_left pi). cbn. lia.
  + cbn. remember (lexs x a0) as d eqn:Hd.
    destruct pi1; destr_eq Hd; subst; cbn.
    * exists (lexs_left pi2). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lexs_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left1 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lexs_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lwith_left2 pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_2 (lexs_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite 2 app_assoc. intros pi' Hs.
      assert (bp = true -> l1 ++ l0 = [] /\ length l2 = 1%nat) as Hbp'.
      { clear - a1 Hbp. intro Hp. specialize (a1 Hp) as [-> Hla]. specialize (Hbp Hp).
        split; [ | assumption ].
        destruct l1 as [ | d l1 ]; [ reflexivity | exfalso ].
        destruct Hbp as [c Hc]; [ intros [=] | ]. decomp_list_eq Hc. discriminate. }
      exists (lmap_left Hbp' pi1_1 pi'). cbn. lia.
    * list_simpl. rewrite app_assoc. exists lzero_left. cbn. lia.
    * destruct (IH _ _ _ _ _ pi1_1 (lexs_left pi2)) as [pi1' Hs1]; [ cbn; lia | solve_bp2 Hbp | ].
      destruct (IH _ _ _ _ _ pi1_2 (lexs_left pi2)) as [pi2' Hs2]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi1' Hs1 pi2' Hs2. list_simpl. rewrite !app_assoc. intros pi1' Hs1 pi2' Hs2.
      exists (lplus_left pi1' pi2'). cbn. lia.
    * cbn in IH. remember (l0 ++ l2) as l eqn:Hl. destruct l as [ | d l ].
      -- decomp_list_eq Hl. cbn in *.
         remember nil as l eqn:Hl. remember (lexs x a0) as d eqn:Hd.
         destruct pi1; (try now decomp_list_eq Hl); injection Hd as [= -> ->]; subst.
         destruct (psubs 0 _ e pi2) as [pi2' Hs'].
         revert pi2' Hs'. list_simpl. rewrite nsubs_subs_com by (rewrite e; intros []). cbn.
         rewrite !map_map. rewrite !(map_ext (fun x => nsubs 0 b (fupz x)) (fun x => x)) by apply nsubs_z_fup.
         rewrite !nsubs_z_fup. rewrite !map_id. intros pi2' Hs'.
         destruct (IH _ _ _ _ _ (lone_left _ _ nil nil pi1) pi2') as [pi2'' Hs2]; [ cbn; lia | solve_bp Hbp | ].
         exists pi2''. cbn in *. lia.
      -- destruct (IH _ _ _ _ _ pi1 (lexs_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
         remember (d :: l) as l' eqn:Hl'. clear Hl'. subst l'.
         revert pi' Hs. list_simpl. rewrite app_assoc. intros pi' Hs.
         rewrite app_assoc. exists (lone_left pi'). cbn. lia.
    * destruct (IH _ _ _ _ _ pi1 (lexs_left pi2)) as [pi' Hs]; [ cbn; lia | solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc. intros pi' Hs.
      exists (lfrl_left e pi'). cbn. lia.
    * remember (lexs_left pi2) as pi2' eqn:Hpi2'.
      destruct (pup 0 pi2') as [pi2'' Hs2].
      revert pi2'' Hs2. list_simpl. intros pi2'' Hs2.
      destruct (IH _ _ _ _ _ pi1 pi2'') as [pi' Hs];
        [ subst; cbn in *; lia | rewrite length_map; solve_bp2 Hbp | ].
      revert pi' Hs. list_simpl. rewrite !app_assoc, <- !map_app. intros pi' Hs.
      exists (lexs_left pi'). subst. cbn in *. lia.
    * destruct (psubs 0 _ e pi2) as [pi2' Hs'].
      revert pi2' Hs'. list_simpl. rewrite nsubs_subs_com by (rewrite e; intros []). cbn.
      rewrite !map_map. rewrite !(map_ext (fun x => nsubs 0 b (fupz x)) (fun x => x)) by apply nsubs_z_fup.
      rewrite !nsubs_z_fup. rewrite !map_id. intros pi2' Hs'.
      destruct (IH _ _ _ _ _ pi1 pi2') as [pi2'' Hs2]; [ cbn; lia | solve_bp Hbp | ].
      exists pi2''. cbn in *. lia.
  + revert pi2 IH. list_simpl. intros pi2 IH.
    destruct (pup 0 pi1) as [pi1' Hs1].
    destruct (IH _ _ _ _ _ pi1' pi2) as [pi Hs]; [ lia | | ].
    { rewrite !length_map.
      intros Hb Hl. destruct (Hbp Hb); [ rewrite ?length_app in *; cbn in *; lia | ].
      subst. exists (fupz x0). reflexivity. }
    revert pi Hs. rewrite !app_assoc, <- !map_app. intros pi Hs.
    exists (lexs_left pi). cbn. lia.
- (* */lexs_right *)
  destruct (IH _ _ _ _ _ pi1 pi2) as [pi' Hs]; [ cbn; lia | solve_bp Hbp | ].
  exists (lexs_right e pi'). cbn. lia.
Qed.

Lemma lcut a b l1 l2 l3 : (bp = true -> l1 <> [] -> length l2 = 1%nat) ->
  l2 ⊦ a -> l1 ++ a :: l3 ⊦ b -> l1 ++ l2 ++ l3 ⊦ b.
Proof. intros Hbp pi1 pi2. destruct (lprove_trans_weight _ pi1 pi2 Hbp) as [pi _]. exact pi. Qed.

Lemma lsubst a b c l1 l2 : [a] ⊦ b -> l1 ++ b :: l2 ⊦ c -> l1 ++ a :: l2 ⊦ c.
Proof. intros pi1 pi2. refine (lcut _ _ pi1 pi2). intros. reflexivity. Qed.

Lemma ltrans b c l1 l2 : l1 ⊦ b -> b :: l2 ⊦ c -> l1 ++ l2 ⊦ c.
Proof.
intros pi1 pi2. rewrite <- (app_nil_l _) in pi2. refine (lcut _ _ pi1 pi2).
intros _ Hnil. now contradiction Hnil.
Qed.

Lemma lmap_right_inv a b l : l ⊦ b / a -> l · a ⊦ b.
Proof.
intro pi.
assert ([b / a; a] ⊦ b) as pi'.
{ apply (lmap_left _ _ _ nil [a]); [ | apply lidentity .. ].
  intros _. split; reflexivity. }
exact (ltrans pi pi').
Qed.

Lemma curry a b : [a] ⊦ b <=> [1] ⊦ b / a.
Proof.
split; intro pi.
- apply (lone_left [] _). apply lmap_right. assumption.
- apply (@lcut 1 _ [] []).
  + intros _ []. reflexivity.
  + apply lone_right.
  + apply (lmap_right_inv pi).
Qed.

End WithParameter.

Definition comp_formula_l := var 3 / var 2.
Definition comp_formula_r := (var 3 / var 1) / (var 2 / var 1).

Lemma comp_formula_lambek : @lprove false [comp_formula_l] comp_formula_r.
Proof.
apply lmap_right, lmap_right.
list_simpl. cons2app. rewrite <- (app_nil_r (_ ++ var 1 :: nil)). apply (@lcut _ (var 2)).
- intros [=].
- list_simpl. rewrite <- (app_nil_r _). apply (lmap_left _ _ _ nil _ nil).
  + intros _. split; reflexivity.
  + apply lidentity.
  + apply lidentity.
- list_simpl. rewrite <- (app_nil_r _). apply (lmap_left _ _ _ nil _ nil).
  + intros _. split; reflexivity.
  + apply lidentity.
  + apply lidentity.
Qed.

Lemma comp_formula_not_is : notT (@lprove true [comp_formula_l] comp_formula_r).
Proof.
intros pi%lmap_right_inv%lmap_right_inv.
inversion pi.
- decomp_list_eq H.
  + decomp_list_eq H2.
    * decomp_list_eq H3.
    * list_simpl in H2. decomp_list_eq H2.
  + list_simpl in H. decomp_list_eq H.
- decomp_list_eq H.
  + decomp_list_eq H2.
    * decomp_list_eq H3.
    * list_simpl in H2. decomp_list_eq H2.
  + list_simpl in H. decomp_list_eq H.
- destruct (H0 eq_refl) as [-> [d ->]%length_one_iffT_sgt].
  list_simpl in H. decomp_list_eq H. subst.
  list_simpl in H2.
  inversion H2.
  + decomp_list_eq H.
    * decomp_list_eq H5.
    * list_simpl in H. decomp_list_eq H.
  + decomp_list_eq H.
    * decomp_list_eq H5.
    * list_simpl in H. decomp_list_eq H.
  + decomp_list_eq H.
    * decomp_list_eq H7.
    * list_simpl in H. decomp_list_eq H.
  + decomp_list_eq H3.
    * decomp_list_eq H5.
    * list_simpl in H3. decomp_list_eq H3.
  + decomp_list_eq H.
    * decomp_list_eq H6.
    * list_simpl in H. decomp_list_eq H.
  + decomp_list_eq H.
    * decomp_list_eq H5.
    * list_simpl in H. decomp_list_eq H.
  + decomp_list_eq H.
    * decomp_list_eq H6.
    * list_simpl in H. decomp_list_eq H.
  + decomp_list_eq H.
    * decomp_list_eq H5.
    * list_simpl in H. decomp_list_eq H.
- decomp_list_eq H0.
  + decomp_list_eq H2.
    * decomp_list_eq H3.
    * list_simpl in H2. decomp_list_eq H2.
  + list_simpl in H0. decomp_list_eq H0.
- decomp_list_eq H.
  + decomp_list_eq H3.
    * decomp_list_eq H4.
    * list_simpl in H3. decomp_list_eq H3.
  + list_simpl in H. decomp_list_eq H.
- decomp_list_eq H.
  + decomp_list_eq H2.
    * decomp_list_eq H3.
    * list_simpl in H2. decomp_list_eq H2.
  + list_simpl in H. decomp_list_eq H.
- decomp_list_eq H.
  + decomp_list_eq H3.
    * decomp_list_eq H4.
    * list_simpl in H3. decomp_list_eq H3.
  + list_simpl in H. decomp_list_eq H.
- decomp_list_eq H.
  + decomp_list_eq H2.
    * decomp_list_eq H3.
    * list_simpl in H2. decomp_list_eq H2.
  + list_simpl in H. decomp_list_eq H.
Qed.

Definition plus_formula_l := (var 3 / var 1) ∧ (var 3 / var 2).
Definition plus_formula_r := var 3 / (var 1 ∨ var 2) ∧ var 4.

Lemma plus_formula_is : @lprove true [plus_formula_l] plus_formula_r.
Proof.
apply lmap_right.
apply lwith_left1.
apply lplus_left.
- apply (@lwith_left1 _ _ _ _ nil).
  list_simpl. rewrite <- (app_nil_r _). apply (lmap_left _ _ _ nil _ nil).
  + intros _. split; reflexivity.
  + apply lidentity.
  + apply lidentity.
- apply (@lwith_left2 _ _ _ _ nil).
  list_simpl. rewrite <- (app_nil_r _). apply (lmap_left _ _ _ nil _ nil).
  + intros _. split; reflexivity.
  + apply lidentity.
  + apply lidentity.
Qed.


(** ** (Weakly) Reversed system *)

Reserved Notation "l ⎹ bp ⊦r a" (at level 65, format "l ⎹ bp ⊦r  a").
Inductive rlprove {bp : bool} : list lform -> lform -> Type :=
| rlidentity v x : [lvar v x]⎹bp⊦r lvar v x
| rltop_right l : l⎹bp⊦r 𝖳
| rlwith_left1 a b c l1 l2 : l1 ++ a :: l2⎹bp⊦r c -> l1 ++ a ∧ b :: l2⎹bp⊦r c
| rlwith_left2 a b c l1 l2 : l1 ++ a :: l2⎹bp⊦r c -> l1 ++ b ∧ a :: l2⎹bp⊦r c
| rlwith_right a b l : l⎹bp⊦r a -> l⎹bp⊦r b -> l⎹bp⊦r a ∧ b
| rlmap_left a b c l1 l2 l3 : (bp = true -> l1 = [] /\ length l2 = 1%nat) ->
    l2⎹bp⊦r a -> l1 ++ b :: l3⎹bp⊦r c -> l1 ++ b / a :: l2 ++ l3⎹bp⊦r c
| rlmap_right a b l : l · a⎹bp⊦r b -> l⎹bp⊦r b / a
| rlzero_left a l1 l2 : {'(v, x) | a = lvar v x } + (a = 0) + (a = 1) -> l1 ++ 0 :: l2⎹bp⊦r a
| rlplus_left a b c l1 l2 : l1 ++ a :: l2⎹bp⊦r c -> l1 ++ b :: l2⎹bp⊦r c -> l1 ++ a ∨ b :: l2⎹bp⊦r c
| rlplus_right1 a b l : l⎹bp⊦r a -> l⎹bp⊦r a ∨ b
| rlplus_right2 a b l : l⎹bp⊦r a -> l⎹bp⊦r b ∨ a
| rlone_left a l1 l2 : l1 ++ l2⎹bp⊦r a -> l1 ++ 1 :: l2⎹bp⊦r a
| rlone_right : nil⎹bp⊦r 1
| rlfrl_left a x b c l1 l2 : closed b -> l1 ++ subs x b a :: l2⎹bp⊦r c -> l1 ++ lfrl x a :: l2⎹bp⊦r c
| rlfrl_right a x l : map fupz l⎹bp⊦r subs x (dvar 0) (fupz a) -> l⎹bp⊦r lfrl x a
| rlexs_left a x c l1 l2 : map fupz l1 ++ subs x (dvar 0) (fupz a) :: map fupz l2⎹bp⊦r fupz c ->
   l1 ++ lexs x a :: l2⎹bp⊦r c
| rlexs_right a x b l : closed b -> l⎹bp⊦r subs x b a -> l⎹bp⊦r lexs x a
where "l ⎹ bp ⊦r a" := (@rlprove bp l a).
Arguments rlidentity {_ _ _}, [_] _ _, _ _ _.
Arguments rltop_right {_ _}, [_] _, _ _.
Arguments rlwith_left1 [_ _ _ _ _ _] _, [_ _] _ [_ _ _] _, [_] _ _ _ _ _ _, _ _ _ _ _ _ _.
Arguments rlwith_left2 [_ _ _ _ _ _] _, [_ _] _ [_ _ _] _, [_] _ _ _ _ _ _, _ _ _ _ _ _ _.
Arguments rlwith_right [_ _ _ _] _ _, [_] _ _ _ _ _, _ _ _ _ _ _.
Arguments rlmap_left [_ _ _ _ _ _ _ _] _ _, [_ _ _ _ _ _ _] _ _ _, [_] _ _ _ _ _ _ _ _ _, _ _ _ _ _ _ _ _ _ _.
Arguments rlmap_right [_ _ _ _] _, [_] _ _ _ _, _ _ _ _ _.
Arguments rlzero_left {_ _ _ _ _}, [_ _ _ _] _, [_] _ _ _ _, _ _ _ _ _.
Arguments rlplus_left [_ _ _ _ _ _] _ _, [_] _ _ _ _ _ _ _, _ _ _ _ _ _ _ _.
Arguments rlplus_right1 [_ _ _ _] _, [_ _] _ [_] _, [_] _ _ _ _, _ _ _ _ _.
Arguments rlplus_right2 [_ _ _ _] _, [_ _] _ [_] _, [_] _ _ _ _, _ _ _ _ _.
Arguments rlone_left [_ _ _ _] _, [_ _] _ _ _, [_] _ _ _ _, _ _ _ _ _.
Arguments rlone_right {_}, _.
Arguments rlfrl_left [_ _ _ _ _ _ _ _] _, [_ _ _ _ _ _ _] _ _, _ _ _ _ _ _ _ _.
Arguments rlfrl_right [_ _ _ _] _, [_ _] _ [_] _, [_] _ _ _ _, _ _ _ _ _.
Arguments rlexs_left [_ _ _ _ _ _] _, [_ _] _ [_ _] _, [_] _ _ _ _ _, _ _ _ _ _ _.
Arguments rlexs_right [_ _ _ _ _ _] _, [_ _ _ _ _] _ _, _ _ _ _ _ _ _.

Lemma rlprove_lprove bp l a : l⎹bp⊦r a -> l⎹bp⊦ a.
Proof.
intro pi. induction pi; try now constructor.
- apply (lfrl_left e IHpi).
- apply (lexs_right e IHpi).
Qed.

Lemma rlidentity_gen bp a : [a]⎹bp ⊦r a.
Proof.
remember (fsize a) as s eqn:Hs.
induction s as [s IH] in a, Hs |- * using (well_founded_induction_type lt_wf);
  destruct a as [ v x | a1 a2 | | a1 a2 | | a1 a2 | | x a1 | x a1 ]; inversion Hs;
  try now rewrite <- (app_nil_l _); constructor; rewrite <- (app_nil_l _); constructor; assumption.
- constructor. change ([a2 / a1] · a1) with ([] ++ a2 / a1 :: [a1] ++ []).
  cbn in Hs. constructor.
  + intros _. split; reflexivity.
  + refine (IH _ _ _ eq_refl); lia.
  + refine (IH _ _ _ eq_refl); lia.
- constructor.
  + apply (rlwith_left1 _ _ _ nil).
    cbn in Hs. refine (IH _ _ _ eq_refl); lia.
  + apply (rlwith_left2 _ _ _ nil).
    cbn in Hs. refine (IH _ _ _ eq_refl); lia.
- rewrite <- (app_nil_l _). constructor. left. right. reflexivity.
- apply (rlplus_left _ _ _ nil).
  + apply rlplus_right1.
    cbn in Hs. refine (IH _ _ _ eq_refl); lia.
  + apply rlplus_right2.
    cbn in Hs. refine (IH _ _ _ eq_refl); lia.
- apply rlfrl_right. cbn. apply (rlfrl_left _ _ _ (dvar 0) _ nil).
  + reflexivity.
  + refine (IH _ _ _ eq_refl).
    cbn in Hs. rewrite fsize_subs_lvar, fsize_fup. lia.
- apply (@rlexs_left _ _ _ _ nil). cbn. apply (rlexs_right _ _ _ (dvar 0)).
  + reflexivity.
  + refine (IH _ _ _ eq_refl).
    cbn in Hs. rewrite fsize_subs_lvar, fsize_fup. lia.
Qed.

Lemma rlzero_left_gen bp a l1 l2 : l1 ++ 0 :: l2⎹bp⊦r a.
Proof.
remember (fsize a) as s eqn:Hs.
induction s as [s IH] in a, Hs, l1, l2 |- * using (well_founded_induction_type lt_wf);
  destruct a as [ v x | a1 a2 | | a1 a2 | | a1 a2 | | x a1 | x a1 ].
- assert ({'(w, y) | lvar v x = lvar w y} + (lvar v x = 0) + (lvar v x = 1)) as s'
    by (left; left; exists (v, x); reflexivity).
  apply (rlzero_left s').
- cbn in Hs. apply rlmap_right. list_simpl.
  refine (IH _ _ _ _ _ eq_refl). lia.
- apply rltop_right.
- cbn in Hs. apply rlwith_right.
  + refine (IH _ _ _ _ _ eq_refl). lia.
  + refine (IH _ _ _ _ _ eq_refl). lia.
- assert ({'(v, x) | 0 = lvar v x} + (0 = 0) + (0 = 1)) as s' by (left; right; reflexivity).
  apply (rlzero_left s').
- cbn in Hs. apply rlplus_right1. list_simpl.
  refine (IH _ _ _ _ _ eq_refl). lia.
- assert ({'(v, x) | 1 = lvar v x} + (1 = 0) + (1 = 1)) as s' by (right; reflexivity).
  apply (rlzero_left s').
- cbn in Hs. apply rlfrl_right.
  list_simpl. refine (IH _ _ _ _ _ eq_refl). rewrite fsize_subs_lvar, fsize_fup. lia.
- cbn in Hs. apply (rlexs_right _ _ _ (dvar 0)).
  + reflexivity.
  + refine (IH _ _ _ _ _ eq_refl). rewrite fsize_subs_lvar. lia.
Qed.

Lemma lprove_rlprove bp l a : l⎹bp⊦ a -> l⎹bp⊦r a.
Proof.
intro pi.
induction pi; (try now constructor).
- apply rlidentity_gen.
- apply rlzero_left_gen.
- apply (rlfrl_left e IHpi).
- apply (rlexs_right e IHpi).
Qed.

Lemma rlcut bp a b l1 l2 l3 : (bp = true -> l1 <> [] -> length l2 = 1%nat) ->
  l2⎹ bp⊦r a -> l1 ++ a :: l3⎹bp⊦r b -> l1 ++ l2 ++ l3⎹bp⊦r b.
Proof. intros Hbp pi1%rlprove_lprove pi2%rlprove_lprove. apply lprove_rlprove, (lcut _ Hbp pi1 pi2). Qed.

Lemma rlsubst bp a b c l1 l2 : [a]⎹bp⊦r b -> l1 ++ b :: l2⎹bp⊦r c -> l1 ++ a :: l2⎹bp⊦r c.
Proof. intros pi1 pi2. refine (rlcut _ _ pi1 pi2). intros. reflexivity. Qed.

Lemma rltrans bp b c l1 l2 : l1⎹bp⊦r b -> b :: l2⎹bp⊦r c -> l1 ++ l2⎹bp⊦r c.
Proof.
intros pi1 pi2. rewrite <- (app_nil_l _) in pi2. refine (rlcut _ _ pi1 pi2).
intros _ Hnil. now contradiction Hnil.
Qed.


(** Additional results *)

Lemma is_left_non_empty a l (pi : l⎹true⊦ a) : l <> nil -> { pi' : l⎹true⊦ a | lweight pi' <= lweight pi }.
(* the proof [pi'] we build contains no sequent with empty left-hand side *)
Proof.
remember (lweight pi) as n eqn:Hn.
induction n as [n IHn] using (well_founded_induction_type lt_wf) in l, a, pi, Hn |- *; intro Hl. subst n.
assert (forall l' a' (pi' : l'⎹true⊦ a'), lweight pi' < lweight pi -> l' <> [] ->
        {pi'' : l'⎹true⊦ a' | lweight pi'' <= lweight pi'}) as IH.
{ intros. refine (IHn _ _ _ _ pi' eq_refl H0). lia. } clear IHn.
destruct pi.
- exists lidentity. lia.
- exists ltop_right. lia.
- destruct (IH _ _ pi) as [pi' Hs]; [ cbn; lia | intro H; decomp_list_eq H | ].
  exists (lwith_left1 pi'). cbn. lia.
- destruct (IH _ _ pi) as [pi' Hs]; [ cbn; lia | intro H; decomp_list_eq H | ].
  exists (lwith_left2 pi'). cbn. lia.
- destruct (IH _ _ pi1) as [pi1' Hs1]; [ cbn; lia | assumption | ].
  destruct (IH _ _ pi2) as [pi2' Hs2]; [ cbn; lia | assumption | ].
  exists (lwith_right pi1' pi2'). cbn. lia.
- destruct (IH _ _ pi1) as [pi1' Hs1]; [ cbn; lia | | ].
  { destruct (a0 eq_refl) as [_ [f ->]%length_one_iffT_sgt]. intro H. decomp_list_eq H. }
  destruct (IH _ _ pi2) as [pi2' Hs2]; [ cbn; lia | intro H; decomp_list_eq H | ].
  exists (lmap_left a0 pi1' pi2'). cbn. lia.
- destruct (IH _ _ pi) as [pi' Hs]; [ cbn; lia | intro H; decomp_list_eq H | ].
  exists (lmap_right pi'). cbn. lia.
- exists lzero_left. lia.
- destruct (IH _ _ pi1) as [pi1' Hs1]; [ cbn; lia | intro H; decomp_list_eq H | ].
  destruct (IH _ _ pi2) as [pi2' Hs2]; [ cbn; lia | intro H; decomp_list_eq H | ].
  exists (lplus_left pi1' pi2'). cbn. lia.
- destruct (IH _ _ pi) as [pi' Hs]; [ cbn; lia | assumption | ].
  exists (lplus_right1 pi'). cbn. lia.
- destruct (IH _ _ pi) as [pi' Hs]; [ cbn; lia | assumption | ].
  exists (lplus_right2 pi'). cbn. lia.
- destruct l1 as [ | a1 l1 ], l2 as [ | a2 l2 ].
  2,3,4: destruct (IH _ _ pi) as [pi' Hs];
           [ cbn; lia | intro H; decomp_list_eq H | exists (lone_left pi'); cbn in *; lia ].
  clear Hl. cbn in *. remember nil as l eqn:Heql.
  destruct pi; decomp_list_eq Heql; cbn.
  + exists ltop_right. cbn. lia.
  + destruct (IH _ _ (@lone_left _ _ nil nil pi1)) as [pi1' Hs1]; [ cbn; lia | intro H; decomp_list_eq H | ].
    destruct (IH _ _ (@lone_left _ _ nil nil pi2)) as [pi2' Hs2]; [ cbn; lia | intro H; decomp_list_eq H | ].
    exists (lwith_right pi1' pi2'). cbn in *. lia.
  + destruct (IH _ _ pi) as [pi' Hs]; [ cbn; lia | intro H; decomp_list_eq H | ].
    exists (@lmap_right _ _ _ [1] (lone_left pi')). cbn in *. lia.
  + destruct (IH _ _ (@lone_left _ _ nil nil pi)) as [pi' Hs]; [ cbn; lia | intro H; decomp_list_eq H | ].
    exists (lplus_right1 pi'). cbn in *. lia.
  + destruct (IH _ _ (@lone_left _ _ nil nil pi)) as [pi' Hs]; [ cbn; lia | intro H; decomp_list_eq H | ].
     exists (lplus_right2 pi'). cbn in *. lia.
  + exists lidentity. cbn. lia.
  + destruct (IH _ _ (@lone_left _ _ nil nil pi)) as [pi' Hs]; [ cbn; lia | intro H; decomp_list_eq H | ].
    cbn in pi'. change [1] with (map fupz [1]) in pi'.
    exists (lfrl_right pi'). cbn in *. lia.
  + destruct (IH _ _ (@lone_left _ _ nil nil pi)) as [pi' Hs]; [ cbn; lia | intro H; decomp_list_eq H | ].
    exists (lexs_right e pi'). cbn in *. lia.
- contradiction Hl. reflexivity.
- destruct (IH _ _ pi) as [pi' Hs]; [ cbn; lia | intro H; decomp_list_eq H | ].
  exists (lfrl_left e pi'). cbn. lia.
- destruct (IH _ _ pi) as [pi' Hs];
    [ cbn; lia | intro H; decomp_list_eq H; subst; contradiction Hl; reflexivity | ].
  exists (lfrl_right pi'). cbn. lia.
- destruct (IH _ _ pi) as [pi' Hs]; [ cbn; lia | intro H; decomp_list_eq H | ].
  exists (lexs_left pi'). cbn. lia.
- destruct (IH _ _ pi) as [pi' Hs]; [ cbn; lia | assumption | ].
  exists (lexs_right e pi'). cbn. lia.
Qed.
