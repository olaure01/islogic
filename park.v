(* System IS Park for Park Model through Intersection Subtyping *)

From Stdlib Require Import Wf_nat Lia CMorphisms.
From OLlibs Require Import Logic_Datatypes_more List_more dectype SubListT.
From InterPT Require iis1.
From InterPT Require Import bcd.
Import EqNotations LogicNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(* TODO Transparent version of [ForallT_app]: add to stdlib/ollibs? *)
Definition ForallT_app_transp A (P : A -> Type) l1 l2 : ForallT P l1 -> ForallT P l2 -> ForallT P (l1 ++ l2).
Proof. intros H1 H2. induction H1 as [ | a l Ha Hl IH ]; [ exact H2 | exact (ForallT_cons _ Ha IH) ]. Defined.

Lemma ForallT_cons_decomp A (P : A -> Type) l (H : ForallT P l) : l <> nil ->
  {'(a', l') & {'(Heq, Ha, Hl) : (a' :: l' = l) * P a' * ForallT P l' | H = rew Heq in ForallT_cons _ Ha Hl } }.
Proof.
destruct H as [ | a' l' P' H' ]; [ now intro Hnil; contradiction Hnil | intros _ ].
exists (a', l'), (eq_refl, P', H'). reflexivity.
Qed.

(* TODO the assumption about decidability of equality is possibly not needed in the end
   since the decomposition results are mostly used through size properties
   which should hold up to equality *)
Lemma ForallT_cons_decomp_dec A (Hdec : forall x y : A, {x = y} + {x <> y}) (P : A -> Type)
  a l (H : ForallT P (a :: l)) :
  {'(Ha, Hl) : P a * ForallT P l | H = ForallT_cons _ Ha Hl }.
Proof.
destruct (ForallT_cons_decomp H) as [(a', l') [[[Heq' P'] H'] H'']]; [ intros [=] | ].
injection Heq' as [= <- <-].
enough (Heq' = eq_refl) as -> by (exists (P', H'); assumption).
apply Eqdep_dec.UIP_dec, List.list_eq_dec, Hdec.
Qed.

Lemma ForallT_app_decomp_dec A (Hdec : forall x y : A, {x = y} + {x <> y}) (P : A -> Type)
  l1 l2 (H : ForallT P (l1 ++ l2)) :
  {'(H1, H2) : ForallT P l1 * ForallT P l2 | H = ForallT_app_transp H1 H2 }.
Proof.
induction l1 as [ | a l1 IH ]; [ exists (ForallT_nil _, H); reflexivity | ].
cbn in H.
destruct (ForallT_cons_decomp_dec Hdec H) as [[Ha Hl] ->].
destruct (IH Hl) as [[IH1 IH2] ->].
exists (ForallT_cons _ Ha IH1, IH2). reflexivity.
Qed.


(** * System IS Park*)

Reserved Notation "a ❘ l ⊦ b" (at level 65, l at next level, b at next level).
Reserved Notation "a ❘ ⊦ b" (at level 65, b at next level).
Inductive pk_sub : list form -> crelation form :=
| pk_omega_right a l : a ❘ l ⊦ Ω
| pk_inter_left1 b a c l : a ❘ l ⊦ c -> a ∩ b ❘ l ⊦ c
| pk_inter_left2 b a c l : a ❘ l ⊦ c -> b ∩ a ❘ l ⊦ c
| pk_inter_right a b c l : c ❘ l ⊦ a -> c ❘ l ⊦ b -> c ❘ l ⊦ a ∩ b
| pk_arrow_left a b c d l : c ❘ ⊦ a -> b ❘ l ⊦ d -> a → b ❘ c :: l ⊦ d
| pk_arrow_right a b c l : c ❘ l · a ⊦ b -> c ❘ l ⊦ a → b
| pk_var_left (x : Atom) l : ForallT (fun u => u ❘ ⊦ x) l -> x ❘ l ⊦ x
| pk_var_right (x : Atom) a b l : x ❘ ⊦ a -> b ❘ ⊦ x -> ForallT (fun u => u ❘ ⊦ x) l -> a → b ❘ l ⊦ x
where "a ❘ l ⊦ b" := (pk_sub l a b)
  and "a ❘ ⊦ b" := (pk_sub nil a b).
Hint Constructors pk_sub : core.
Arguments pk_omega_right {_ _}.
Arguments pk_inter_left1 [_ _ _ _].
Arguments pk_inter_left2 [_ _ _ _].
Arguments pk_arrow_right [_ _ _ _].

Fixpoint pk_weight a l b (pi : a ❘ l ⊦ b) := S
match pi with
| pk_omega_right => 0
| pk_inter_left1 pi1 | pk_inter_left2 pi1 | pk_arrow_right pi1 => pk_weight pi1
| pk_inter_right pi1 pi2 => max (pk_weight pi1) (pk_weight pi2)
| pk_arrow_left pi1 pi2 => pk_weight pi1 + pk_weight pi2
| pk_var_left pis => (fix Fweight x l (HF : ForallT (fun u => u ❘ ⊦ x) l) :=
                       match HF with
                       | ForallT_nil _ => 0
                       | ForallT_cons u pi' HF' => pk_weight pi' + Fweight _ _ HF'
                       end) _ _ pis
| pk_var_right pi1 pi2 pis => pk_weight pi1 + pk_weight pi2 +
    (fix Fweight x l (HF : ForallT (fun u => u ❘ ⊦ x) l) :=
     match HF with
     | ForallT_nil _ => 0
     | ForallT_cons u pi' HF' => pk_weight pi' + Fweight _ _ HF'
     end) _ _ pis
end.

Fixpoint pk_Fweight x l (HF : ForallT (fun u => u ❘ ⊦ x) l) :=
match HF with
| ForallT_nil _ => 0
| ForallT_cons u pi' HF' => pk_weight pi' + pk_Fweight HF'
end.

Lemma pk_Fweight_app x l1 l2 (HF1 : ForallT (fun u => u ❘ ⊦ x) l1) (HF2 : ForallT (fun u => u ❘ ⊦ x) l2) :
  pk_Fweight (ForallT_app_transp HF1 HF2) = pk_Fweight HF1 + pk_Fweight HF2.
Proof. induction HF1; [ reflexivity | ]. simpl ForallT_app_transp. simpl pk_Fweight. rewrite IHHF1. lia. Qed.


Definition pk_sub_equiv a b := ((a ❘ ⊦ b) * (b ❘ ⊦ a))%type.
Infix "⟛" := pk_sub_equiv (at level 65).

Lemma eq_park (x : Atom) : x ⟛ x → x.
Proof. repeat constructor. Qed.

Lemma pk_identity a : a ❘ ⊦ a.
Proof. induction a; repeat constructor; assumption. Qed.

Lemma is_pk l a b : iis1.sub l a b -> a ❘ l ⊦ b.
Proof. intro pi. induction pi; [ apply pk_identity | constructor; assumption .. ]. Qed.

Lemma pk_omega_left_rev_weight c l (pi : Ω ❘ l ⊦ c) a l0 : { pi' : a ❘ l0 ⊦ c | pk_weight pi' = pk_weight pi }.
Proof.
remember Ω as q eqn:Ho. induction pi in Ho, l0 |- *; destr_eq Ho; subst.
- exists pk_omega_right. reflexivity.
- cbn. destruct (IHpi1 eq_refl l0) as [pi'1 <-], (IHpi2 eq_refl l0) as [pi'2 <-].
  exists (pk_inter_right pi'1 pi'2). reflexivity.
- cbn. destruct (IHpi eq_refl (l0 · a0)) as [pi' <-].
  exists (pk_arrow_right pi'). reflexivity.
Qed.

Lemma pk_var_right_wk_weight (x : Atom) c l (pi : c ❘ l ⊦ x) l0 (HF : ForallT (fun u => u ❘ ⊦ x) l0) :
  { pi' : c ❘ l ++ l0 ⊦ x | pk_weight pi' = pk_weight pi + pk_Fweight HF }.
Proof.
remember (var x) as q eqn:Ho. induction pi in Ho, HF |- *; destr_eq Ho; subst.
- destruct (IHpi eq_refl HF) as [pi' Hw].
  exists (pk_inter_left1 pi'). cbn. lia.
- destruct (IHpi eq_refl HF) as [pi' Hw].
  exists (pk_inter_left2 pi'). cbn. lia.
- destruct (IHpi2 eq_refl HF) as [pi' Hw].
  exists (pk_arrow_left pi1 pi'). cbn. lia.
- exists (pk_var_left (ForallT_app_transp f HF)).
  simpl pk_weight at 1. rewrite pk_Fweight_app.
  simpl pk_weight. fold pk_Fweight. lia.
- exists (pk_var_right pi1 pi2 (ForallT_app_transp f HF)).
  simpl pk_weight at 1. rewrite pk_Fweight_app.
  simpl pk_weight. fold pk_Fweight. lia.
Qed.

Lemma pk_var_left_wk_weight (x : Atom) c l (pi : x ❘ l ⊦ c) l0 (HF : ForallT (fun u => u ❘ ⊦ x) l0) :
  { pi' : x ❘ l0 ++ l ⊦ c | pk_weight pi' <= pk_Fweight HF + pk_weight pi }.
Proof.
remember (var x) as q eqn:Ho. induction pi in Ho, HF |- *; destr_eq Ho; subst.
- exists pk_omega_right. cbn. lia.
- destruct (IHpi1 eq_refl HF) as [pi1' Hw1].
  destruct (IHpi2 eq_refl HF) as [pi2' Hw2].
  exists (pk_inter_right pi1' pi2'). cbn. lia.
- destruct (IHpi eq_refl HF) as [pi' Hw].
  revert pi' Hw. rewrite app_assoc. intros pi' Hw.
  exists (pk_arrow_right pi'). cbn. lia.
- exists (pk_var_left (ForallT_app_transp HF f)).
  simpl pk_weight at 1. rewrite pk_Fweight_app.
  simpl pk_weight. fold pk_Fweight. lia.
Qed.


(** * Transitivity *)

Lemma pk_sub_trans_rules s :
  ((forall a b c d l1 l2 (pi1 : a ❘ ⊦ b) (pi2 : c ❘ l1 ++ b :: l2 ⊦ d),
      s = pk_weight pi1 + pk_weight pi2 -> { pi : c ❘ l1 ++ a :: l2 ⊦ d | pk_weight pi <= s })
 * (forall a b c l1 l2 (pi1 : a ❘ l1 ⊦ b) (pi2 : b ❘ l2 ⊦ c),
      s = pk_weight pi1 + pk_weight pi2 -> { pi : a ❘ l1 ++ l2 ⊦ c | pk_weight pi <= s })
 * (forall (x : Atom) b c l (pi1 : x ❘ ⊦ b) (pi2 : c ❘ l · b ⊦ x),
      s = pk_weight pi1 + pk_weight pi2 -> { pi : c ❘ l ⊦ x | pk_weight pi <= s })).
Proof.
induction s as [s IH] using (well_founded_induction_type lt_wf).
assert ((forall a b c d l1 l2 (pi1 : a ❘ ⊦ b) (pi2 : c ❘ l1 ++ b :: l2 ⊦ d), pk_weight pi1 + pk_weight pi2 < s ->
         { pi : c ❘ l1 ++ a :: l2 ⊦ d | pk_weight pi <= pk_weight pi1 + pk_weight pi2 }) *
        (forall a b c l1 l2 (pi1 : a ❘ l1 ⊦ b) (pi2 : b ❘ l2 ⊦ c), pk_weight pi1 + pk_weight pi2 < s ->
         { pi : a ❘ l1 ++ l2 ⊦ c | pk_weight pi <= pk_weight pi1 + pk_weight pi2 }) *
        (forall (x : Atom) b c l (pi1 : x ❘ ⊦ b) (pi2 : c ❘ l · b ⊦ x), pk_weight pi1 + pk_weight pi2 < s ->
         { pi : c ❘ l ⊦ x | pk_weight pi <= pk_weight pi1 + pk_weight pi2 }))
  as [[IH1 IH2] IH3].
{ split; [ split | ].
  - intros a b c d l1 l2 pi1 pi2 Hs. refine (fst (fst (IH _ Hs)) _ _ _ _ _ _ _ _ eq_refl).
  - intros a b c l1 l2 pi1 pi2 Hs. refine (snd (fst (IH _ Hs)) _ _ _ _ _ _ _ eq_refl).
  - intros x b c l pi1 pi2 Hs. refine (snd (IH _ Hs) _ _ _ _ _ _ eq_refl). }
clear IH. split; [ split | ].
- intros a b c d l1 l2 pi1 pi2 ->.
  remember (l1 ++ b :: l2) as l0 eqn:Heql0. destruct pi2; try decomp_list_eq Heql0; subst.
  + exists pk_omega_right. cbn. lia.
  + destruct (IH1 _ _ _ _ _ _ pi1 pi2) as [pi Hspi]; [ cbn; lia | ].
    exists (pk_inter_left1 pi). cbn. lia.
  + destruct (IH1 _ _ _ _ _ _ pi1 pi2) as [pi Hspi]; [ cbn; lia | ].
    exists (pk_inter_left2 pi). cbn. lia.
  + destruct (IH1 _ _ _ _ _ _ pi1 pi2_1) as [pi_1 Hspi1]; [ cbn; lia | ].
    destruct (IH1 _ _ _ _ _ _ pi1 pi2_2) as [pi_2 Hspi2]; [ cbn; lia | ].
    exists (pk_inter_right pi_1 pi_2). cbn. lia.
  + destruct (IH1 _ _ _ _ _ _ pi1 pi2_2) as [pi Hspi]; [ cbn; lia | ].
    rewrite <- app_comm_cons.
    exists (pk_arrow_left pi2_1 pi). cbn. lia.
  + destruct (IH2 _ _ _ _ _ pi1 pi2_1) as [pi Hspi]; [ cbn; lia | ].
    exists (pk_arrow_left pi pi2_2). cbn in *. lia.
  + clear IH2 IH3. revert pi2 IH1. list_simpl. intros pi2 IH1.
    destruct (IH1 _ _ _ _ _ _ pi1 pi2) as [pi Hspi]; [ cbn; lia | ].
    revert pi Hspi. rewrite app_comm_cons, app_assoc. intros pi Hspi.
    exists (pk_arrow_right pi). cbn. lia.
  + destruct (ForallT_app_decomp_dec (@eq_dt_dec form_dectype) _ _ f) as [[f1 f2] ->].
    destruct (ForallT_cons_decomp_dec (@eq_dt_dec form_dectype) f2) as [[Hb f2'] ->].
    destruct (IH2 _ _ _ _ _ pi1 Hb) as [pi Hs]; [ cbn; fold pk_Fweight; rewrite pk_Fweight_app; cbn; lia | ].
    cbn in pi.
    exists (pk_var_left (ForallT_app_transp f1 (ForallT_cons _ pi f2'))).
    simpl pk_weight. fold pk_Fweight. rewrite !pk_Fweight_app. simpl pk_Fweight. cbn in *. lia.
  + destruct (ForallT_app_decomp_dec (@eq_dt_dec form_dectype) _ _ f) as [[f1 f2] ->].
    destruct (ForallT_cons_decomp_dec (@eq_dt_dec form_dectype) f2) as [[Hb f2'] ->].
    destruct (IH2 _ _ _ _ _ pi1 Hb) as [pi Hs]; [ cbn; fold pk_Fweight; rewrite pk_Fweight_app; cbn; lia | ].
    cbn in pi.
    exists (pk_var_right pi2_1 pi2_2 (ForallT_app_transp f1 (ForallT_cons _ pi f2'))).
    simpl pk_weight. fold pk_Fweight. rewrite !pk_Fweight_app. simpl pk_Fweight. cbn in *. lia.
- intros a b c l1 l2 pi1 pi2 ->.
  destruct pi1.
  + destruct (pk_omega_left_rev_weight pi2 a (l ++ l2)) as [pi <-]. exists pi. cbn. lia.
  + destruct (IH2 _ _ _ _ _ pi1 pi2) as [pi Hs]; [ | exists (pk_inter_left1 pi) ]; cbn; lia.
  + destruct (IH2 _ _ _ _ _ pi1 pi2) as [pi Hs]; [ | exists (pk_inter_left2 pi) ]; cbn; lia.
  + clear IH3. cbn in IH1, IH2. cbn. remember (a ∩ b) as e eqn:He. destruct pi2; destr_eq He; subst.
    * exists pk_omega_right. cbn. lia.
    * destruct (IH2 _ _ _ _ _ pi1_1 pi2) as [pi Hs]; [ | exists pi ]; cbn; lia.
    * destruct (IH2 _ _ _ _ _ pi1_2 pi2) as [pi Hs]; [ | exists pi ]; cbn; lia.
    * destruct (IH2 _ _ _ _ _ (pk_inter_right pi1_1 pi1_2) pi2_1) as [pi_1 Hs1]; [ cbn; lia | ].
      destruct (IH2 _ _ _ _ _ (pk_inter_right pi1_1 pi1_2) pi2_2) as [pi_2 Hs2]; [ cbn; lia | ].
      exists (pk_inter_right pi_1 pi_2). cbn in *. lia.
    * destruct (IH2 _ _ _ _ _ (pk_inter_right pi1_1 pi1_2) pi2) as [pi Hs]; [ cbn; lia | ].
      revert pi Hs. clear. rewrite app_assoc. cbn. intros pi Hs.
      exists (pk_arrow_right pi). cbn. lia.
  + destruct (IH2 _ _ _ _ _ pi1_2 pi2) as [pi Hs];
      [ |  rewrite <- app_comm_cons; exists (pk_arrow_left pi1_1 pi) ]; cbn; lia.
  + cbn in IH1, IH2, IH3. cbn. remember (a → b) as e eqn:He. destruct pi2; destr_eq He; subst.
    * exists pk_omega_right. cbn. lia.
    * destruct (IH2 _ _ _ _ _ (pk_arrow_right pi1) pi2_1) as [pi_1 Hs1]; [ cbn; lia | ].
      destruct (IH2 _ _ _ _ _ (pk_arrow_right pi1) pi2_2) as [pi_2 Hs2]; [ cbn; lia | ].
      exists (pk_inter_right pi_1 pi_2). cbn in *. lia.
    * destruct (IH1 _ _ _ _ _ _ pi2_1 pi1) as [pi Hs]; [ cbn; lia | ].
      destruct (IH2 _ _ _ _ _ pi pi2_2) as [pi' Hs']; [ cbn; lia | ].
      revert pi' Hs'. list_simpl. change l0 with (nil ++ l0). list_simpl. intros pi' Hs'.
      exists pi'. lia.
    * destruct (IH2 _ _ _ _ _ (pk_arrow_right pi1) pi2) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. clear. rewrite app_assoc. cbn. intros pi' Hs.
      exists (pk_arrow_right pi'). cbn. lia.
    * destruct (IH2 _ _ _ _ _ pi1 pi2_2) as [pi' Hs']; [ cbn; lia | ].
      revert pi' Hs'. rewrite app_nil_r. intros pi' Hs'.
      destruct (IH3 _ _ _ _ pi2_1 pi') as [pi'' Hs'']; [ cbn; lia | ].
      destruct (pk_var_right_wk_weight pi'' f) as [pi''' Hs'''].
      exists pi'''. simpl pk_weight. fold pk_Fweight. lia.
  + destruct (pk_var_left_wk_weight pi2 f) as [pi' Hs].
    exists pi'. simpl pk_weight. fold pk_Fweight. lia.
  + simpl pk_weight in *. fold pk_Fweight in *.
    remember (var x) as e eqn:He. destruct pi2; destr_eq He; subst.
    * exists pk_omega_right. cbn. lia.
    * destruct (IH2 _ _ _ _ _ (pk_var_right pi1_1 pi1_2 f) pi2_1) as [pi_1 Hs1]; [ cbn; fold pk_Fweight; lia | ].
      destruct (IH2 _ _ _ _ _ (pk_var_right pi1_1 pi1_2 f) pi2_2) as [pi_2 Hs2]; [ cbn; fold pk_Fweight; lia | ].
      exists (pk_inter_right pi_1 pi_2). cbn in *. unfold pk_Fweight. lia.
    * destruct (IH2 _ _ _ _ _ (pk_var_right pi1_1 pi1_2 f) pi2) as [pi Hs]; [ cbn; fold pk_Fweight; lia | ].
      revert pi Hs. clear. rewrite app_assoc. cbn. intros pi Hs.
      exists (pk_arrow_right pi). cbn. fold pk_Fweight in Hs. lia.
    * exists (pk_var_right pi1_1 pi1_2 (ForallT_app_transp f f0)).
      simpl pk_weight. fold pk_Fweight. rewrite pk_Fweight_app. lia.
- intros x b c l pi1 pi2 ->.
  remember (var x) as a eqn:Ha. remember (l · b) as l0 eqn:Heql0.
  destruct pi2; destr_eq Ha; try decomp_list_eq Heql0; subst.
  + destruct (IH3 _ _ _ _ pi1 pi2) as [pi Hs]; [ cbn; lia | ].
    exists (pk_inter_left1 pi). cbn. lia.
  + destruct (IH3 _ _ _ _ pi1 pi2) as [pi Hs]; [ cbn; lia | ].
    exists (pk_inter_left2 pi). cbn. lia.
  + destruct (IH3 _ _ _ _ pi1 pi2_2) as [pi Hs]; [ cbn; lia | ].
    exists (pk_arrow_left pi2_1 pi). cbn. lia.
  + destruct (IH2 _ _ _ _ _ pi1 pi2_1) as [pi Hs]; [ cbn; lia | ]. cbn in pi.
    exists (pk_var_right pi pi2_2 (ForallT_nil _)). cbn in *. lia.
  + destruct (ForallT_app_decomp_dec (@eq_dt_dec form_dectype) _ _ f) as [[f1 f2] ->].
    exists (pk_var_left f1).
    simpl pk_weight. fold pk_Fweight. rewrite pk_Fweight_app. lia.
  + destruct (ForallT_app_decomp_dec (@eq_dt_dec form_dectype) _ _ f) as [[f1 f2] ->].
    exists (pk_var_right pi2_1 pi2_2 f1).
    simpl pk_weight. fold pk_Fweight. rewrite pk_Fweight_app. lia.
Qed.

Lemma pk_sub_subst a b c d l1 l2 : a ❘ ⊦ b -> c ❘ l1 ++ b :: l2 ⊦ d -> c ❘ l1 ++ a :: l2 ⊦ d.
Proof. intros pi1 pi2. apply (fst (fst (pk_sub_trans_rules _)) _ _ _ _ _ _ pi1 pi2 eq_refl). Qed.

Lemma pk_sub_trans a b c l1 l2 : a ❘ l1 ⊦ b -> b ❘ l2 ⊦ c -> a ❘ l1 ++ l2 ⊦ c.
Proof. intros pi1 pi2. apply (snd (fst (pk_sub_trans_rules _)) _ _ _ _ _ pi1 pi2 eq_refl). Qed.

Instance pk_sub_preorder : PreOrder (pk_sub nil).
Proof. split; intro a; [ exact (pk_identity _) | intros b c H1 H2; exact (pk_sub_trans H1 H2) ]. Qed.

Instance pk_sub_equivalence : Equivalence pk_sub_equiv.
Proof.
split.
- intro. split; reflexivity.
- intros a b []. split; assumption.
- intros a b c [] []. split; etransitivity; eassumption.
Qed.

Lemma pk_omega_left_rev a l b l' : Ω ❘ l ⊦ a -> b ❘ l' ⊦ a.
Proof. intro pi. apply (pk_omega_left_rev_weight pi b l'). Qed.

Lemma pk_arrow_right_rev a b c l : c ❘ l ⊦ a → b -> c ❘ l · a ⊦ b.
Proof. intro pi. apply (pk_sub_trans pi). repeat constructor; reflexivity. Qed.

Lemma pk_arrow_left_rev a b c d l : a → b ❘ c :: l ⊦ d -> ((c ❘ ⊦ a) + (Ω ❘ ⊦ d)) * (b ❘ l ⊦ d).
Proof.
intro pi. remember (a → b) as e eqn:Heqe. remember (c :: l) as l' eqn:Heql'.
revert a b Heqe c l Heql'. induction pi;
  intros a' b' Heqe c' l0 Heql0; destr_eq Heqe; destr_eq Heql0; subst;
  (try now constructor; apply (IH1 _ _ eq_refl _ _ eq_refl)); try now auto.
- destruct (IHpi1 _ _ eq_refl _ _ eq_refl) as [[Hl1 | Hl1] Hr1],
           (IHpi2 _ _ eq_refl _ _ eq_refl) as [[Hl2 | Hl2] Hr2].
  + split; [ left | apply pk_inter_right ]; assumption.
  + split; [ left | apply pk_inter_right ]; assumption.
  + split; [ left | apply pk_inter_right ]; assumption.
  + split; [ right | ]; apply pk_inter_right; assumption.
- destruct (IHpi _ _ eq_refl _ _ eq_refl) as [[Hl | Hl] Hr].
  + split; [ left | apply pk_arrow_right ]; assumption.
  + split; [ right | ]; apply pk_arrow_right, (pk_omega_left_rev _ _ Hl).
- inversion_clear f. split.
  + left. transitivity (var x); assumption.
  + apply (pk_var_right_wk_weight pi2). assumption.
Qed.


(** * Equivalence with BCD *)

Definition pk_ax := [fun x => (var x → var x, var x); fun x => (var x, var x → var x)].
Notation "a ⩽ b " := (@bcd_sub pk_ax a b) (at level 70).

Lemma bcd_pk_list (x : Atom) l : ForallT (fun u => u ⩽ x) l -> x ⩽ ⟦l, x⟧.
Proof.
induction l as [ | y l IHl ] using rev_rect; cbn; intro HF.
- apply bcd_identity.
- assert (HFl := ForallT_app_l _ _ HF).
  assert (HF2 := ForallT_app_r _ _ HF). inversion_clear HF2.
  rewrite list2form_last. etransitivity; [ apply IHl, HFl | ].
  apply bcd_arrow_list.
  transitivity (x → x).
  + apply (@bcd_axiom pk_ax _ _ (inT_cons _ _ _ (inT_eq _ _))).
  + apply bcd_arrow; [ assumption | apply bcd_identity ].
Qed.

Lemma pk_bcd a l b : a ❘ l ⊦ b -> a ⩽ ⟦l, b⟧.
Proof.
intro pi.
remember (pk_weight pi) as s eqn: Hs.
induction s as [s IHs] in a, l, b, pi, Hs |- * using (well_founded_induction_type lt_wf). subst s.
assert (forall a' l' b' (pi' : a' ❘ l' ⊦ b'), pk_weight pi' < pk_weight pi -> a' ⩽ ⟦l', b'⟧) as IH
  by (intros a' l' b' pi' Hs; apply (IHs _ Hs _ _ _ _ eq_refl)).
clear IHs. destruct pi.
- clear IH. induction l as [ | ? l IHl ] using rev_rect; cbn.
  + apply bcd_omega_right.
  + rewrite list2form_last. etransitivity; [ apply IHl | ].
    apply bcd_arrow_list.
    apply bcd_arrow_omega_distr.
- assert (H := IH _ _ _ pi ltac:(cbn; lia)).
  etransitivity; [ | eassumption ]. apply bcd_inter_left1.
- assert (H := IH _ _ _ pi ltac:(cbn; lia)).
  etransitivity; [ | eassumption ]. apply bcd_inter_left2.
- assert (H1 := IH _ _ _ pi1 ltac:(cbn; lia)).
  assert (H2 := IH _ _ _ pi2 ltac:(cbn; lia)).
  apply bcd_arrow_inter_list; assumption.
- assert (H1 := IH _ _ _ pi1 ltac:(cbn; lia)).
  assert (H2 := IH _ _ _ pi2 ltac:(cbn; lia)).
  apply bcd_arrow; assumption.
- assert (H := IH _ _ _ pi ltac:(cbn; lia)).
  rewrite list2form_last in H. assumption.
- apply bcd_pk_list.
  induction f in IH |- *; constructor.
  + apply (IH _ _ _ p ltac:(cbn; lia)).
  + apply IHf.
    intros. apply (IH _ _ _ pi' ltac:(cbn in *; lia)).
- transitivity x.
  + transitivity (x → x).
    * assert (H1 := IH _ _ _ pi1 ltac:(cbn; lia)).
      assert (H2 := IH _ _ _ pi2 ltac:(cbn; lia)).
      apply bcd_arrow; assumption.
    * apply (@bcd_axiom pk_ax _ _ (inT_eq _ _)).
  + apply bcd_pk_list.
    induction f in IH |- *; constructor.
    * apply (IH _ _ _ p ltac:(cbn; lia)).
    * apply IHf.
      intros. apply (IH _ _ _ pi' ltac:(cbn in *; lia)).
Qed.

Theorem pk_bcd_equiv a b : a ⩽ b <=> a ❘ ⊦ b.
Proof.
split; intro H.
- induction H; try (repeat constructor; try reflexivity; fail).
  + etransitivity; eassumption.
  + apply pk_inter_right; now constructor.
  + constructor. constructor; assumption.
  + inversion i as [ | ii ]; [ | inversion ii as [ | iii ]; [ | inversion iii ] ]; subst; apply eq_park.
- change b with ⟦[], b⟧. apply pk_bcd. assumption.
Qed.


(** * Beta Condition *)

Lemma pk_beta_list s a l b : ForallT (fun z => fst z <> nil) s -> form_recomposition s ❘ a :: l ⊦ b ->
  { s0 & sublistT s0 s & (ForallT (pk_sub nil a) (arrow_tl s0)
                       * (form_recomposition (arrow_hd s0) ❘ l ⊦ b))%type }.
Proof.
intros Hnil pi.
remember (form_recomposition s) as s0 eqn:Hs0. remember (a :: l) as l0 eqn:Hl0. revert s Hs0 a l Hl0 Hnil.
induction pi; intros s Hs0 a' l' Hl0 Hnil; destr_eq Hl0; subst.
- exists nil; [ apply sublistT_nil_l | split ]; cbn; constructor.
- destruct s as [ | (t, h) [ | p s ] ]; inversion Hs0.
  + destruct t; inversion H0.
  + inversion Hnil. subst. cbn in H2. destruct t as [ | p' t ]; [ contradiction H2; reflexivity | ].
    apply pk_arrow_left_rev in pi as [[pi1 | pi1] pi2].
    * exists [(p' :: t, h)]; [ | split; [ | assumption ] ].
      -- constructor. apply sublistT_nil_l.
      -- specialize (IHpi [(p' :: t, h)] eq_refl _ _ eq_refl) as [s0 H1' [H2' H3']];
           [ ForallT_solve | ].
         repeat constructor. assumption.
    * exists nil; [ | split ].
      -- apply sublistT_nil_l.
      -- repeat constructor.
      -- apply (pk_omega_left_rev _ _ pi1).
- destruct s as [ | (t0, h0) [ | (t, h) s ] ]; inversion Hs0.
  + destruct t0; inversion H0.
  + specialize (IHpi ((t, h) :: s) H1 _ _ eq_refl) as [s0 H1' [H2' H3']]; [ ForallT_solve | ].
    exists s0; constructor; assumption.
- destruct (IHpi1 _ eq_refl _ _ eq_refl Hnil) as [s1 H1a [H1b H1c]].
  destruct (IHpi2 _ eq_refl _ _ eq_refl Hnil) as [s2 H2a [H2b H2c]].
  clear - H1a H1b H1c H2a H2b H2c.
  enough
    ({s0 & ((sublistT s0 s) * (sublistT s1 s0) * (sublistT s2 s0))%type & ForallT (pk_sub nil a') (arrow_tl s0) })
    as [s0 [[H0 H1] H2]].
  { exists s0; [ assumption | split; [ assumption | ] ].
    clear - H1c H2c H1 H2.
    enough (forall s s', sublistT s' s ->
              form_recomposition (arrow_hd s) ❘ ⊦ form_recomposition (arrow_hd s')) as Hs.
    { apply pk_inter_right.
      - rewrite <- (app_nil_l _). refine (pk_sub_trans _ H1c).
        apply Hs. assumption.
      - rewrite <- (app_nil_l _). refine (pk_sub_trans _ H2c).
        apply Hs. assumption. }
    clear. intros s s' Hs. induction Hs; [ reflexivity | | ].
    - destruct a as (t, h). destruct l1 as [|p1 l1]; cbn.
      + destruct l2 as [|p2 l2]; [ | apply pk_inter_left1 ]; reflexivity.
      + apply pk_inter_right.
        * destruct l2 as [|p2 l2]; [ | apply pk_inter_left1 ]; reflexivity.
        * destruct l2 as [|p2 l2].
          -- exfalso. inversion Hs.
          -- apply pk_inter_left2. assumption.
    - destruct a as (t, h). destruct l2 as [|p l2]; cbn.
      + rewrite <- (app_nil_l _). refine (pk_sub_trans _ IHHs). constructor.
      + apply pk_inter_left2. assumption. }
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
- list_simpl in pi.
  destruct (IHpi _ eq_refl _ _ eq_refl Hnil) as [s0 H1 [H2 H3]].
  exists s0; [ | split; [ | apply pk_arrow_right ] ]; assumption.
- exfalso.
  destruct s as [ | ([ | ? t ], h) [ | p s ] ]; inversion Hs0.
  inversion_clear Hnil. contradiction.
- inversion_clear f.
  destruct s as [ | ([ | c t ], h) [ | p s ] ]; destr_eq Hs0. subst.
  exists [(c :: t, h)]; [ | split ].
  + reflexivity.
  + repeat constructor. transitivity (var x); assumption.
  + apply (pk_var_right_wk_weight pi2). assumption.
Qed.

Lemma pk_beta : beta_condition (pk_sub nil).
Proof. intros s a b Hnil pi%pk_arrow_right_rev. apply (pk_beta_list Hnil pi). Qed.


(** * Eta Condition *)

Lemma sc_eta : eta_condition pk_sub_equiv.
Proof.
apply weaker_eta_condition.
- split; apply pk_sub_equivalence.
- intros ? ? ? ? [] []. repeat constructor; assumption.
- intros. split; apply is_pk, iis1.inter_assoc.
- intros. split; apply is_pk, iis1.inter_unit_l.
- intros. split; apply is_pk, iis1.inter_unit_r.
- intros ? ? ? []. now repeat constructor.
- intro. split; apply is_pk, iis1.arrow_omega_distr.
- intros. split; apply is_pk, iis1.arrow_inter_distr.
- intro x. exists [([var x], x)].
  + constructor; [ | constructor ]. intros [=].
  + symmetry. apply eq_park.
Qed.
