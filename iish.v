(* System ∩ISₕ *)

From Stdlib Require Import Bool.
From OLlibs Require Import List_more.
From InterPT Require Export iformulas.
From InterPT Require iis1_prop ish.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * ∩ISₕ *)

(** ** Rules *)

Reserved Notation "l ⊦ a" (at level 65, a at next level).
Inductive sub : list form -> form -> Type :=
| identity a : a :: nil ⊦ a
| omega_right l : l ⊦ Ω
| inter_left1 b a c l : a :: l ⊦ c -> a ∩ b :: l ⊦ c
| inter_left2 b a c l : a :: l ⊦ c -> b ∩ a :: l ⊦ c
| inter_right a b l : l ⊦ a -> l ⊦ b -> l ⊦ a ∩ b
| arrow_left a b c d l : [c] ⊦ a -> b :: l ⊦ d -> a → b :: c :: l ⊦ d
| arrow_right a b l : l · a ⊦ b -> l ⊦ a → b
where "l ⊦ a" := (sub l a).
Notation "⊦ a" := (sub nil a) (at level 65).
Hint Constructors sub : core.
Arguments identity {_}.
Arguments omega_right {_}.
Arguments inter_left1 [_ _ _ _].
Arguments inter_left2 [_ _ _ _].
Arguments arrow_right [_ _ _].


(** ** Equivalence with ∩IS₁ *)

Lemma sub_is l a b : a :: l ⊦ b -> iis1.sub l a b.
Proof.
intros pi. remember (a :: l) as l0 eqn:Hl. induction pi in a, l, Hl |- *; destr_eq Hl; subst; try now constructor.
- apply iis1.inter_left1, IHpi. reflexivity.
- apply iis1.inter_left2, IHpi. reflexivity.
- apply iis1.inter_right; [ apply IHpi1 | apply IHpi2 ]; reflexivity.
- apply iis1.arrow_left; [ apply IHpi1 | apply IHpi2 ]; reflexivity.
- apply iis1.arrow_right, IHpi. reflexivity.
Qed.

Lemma is_sub l a b : iis1.sub l a b -> a :: l ⊦ b.
Proof. intro pi. induction pi; now constructor. Qed.

Lemma inter_middle1 b a c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ a ∩ b :: l2 ⊦ c.
Proof.
destruct l1 as [ | d  l1 ].
- apply inter_left1.
- cbn. intros pi%sub_is. apply is_sub.
  refine (iis1_prop.Direct_Transitivity.sub_subst _ _ _ pi).
  apply iis1.inter_left1, iis1.identity.
Qed.

Lemma inter_middle2 b a c l1 l2 : l1 ++ a :: l2 ⊦ c -> l1 ++ b ∩ a :: l2 ⊦ c.
Proof.
destruct l1 as [ | d  l1 ].
- apply inter_left2.
- cbn. intros pi%sub_is. apply is_sub.
  refine (iis1_prop.Direct_Transitivity.sub_subst _ _ _ pi).
  apply iis1.inter_left2, iis1.identity.
Qed.

(** ** Additionnal cut rule *)

Lemma sub_cut0 a b l2 : ⊦ a -> a :: l2 ⊦ b -> l2 ⊦ b.
Proof.
intros pi1 pi2.
remember (a :: l2) as l eqn:Heql.
induction pi2 in pi1, a, l2, Heql |- *; destr_eq Heql; subst.
- assumption.
- apply omega_right.
- inversion_clear pi1.
  refine (IHpi2 _ _ _ eq_refl). assumption.
- inversion_clear pi1.
  refine (IHpi2 _ _ _ eq_refl). assumption.
- apply inter_right.
  + refine (IHpi2_1 _ _ _ eq_refl). assumption.
  + refine (IHpi2_2 _ _ _ eq_refl). assumption.
- inversion_clear pi1.
  repeat match goal with H : _ |- _ => apply sub_is in H end. apply is_sub.
  change l with (nil ++ l). eapply iis1_prop.Direct_Transitivity.sub_trans; [ eassumption | ].
  change l with (nil ++ l). eapply iis1_prop.Direct_Transitivity.sub_trans; eassumption.
- apply arrow_right.
  refine (IHpi2 _ _ _ eq_refl). assumption.
Qed.

Lemma sub_cut a b l1 l2 : l1 ⊦ a -> a :: l2 ⊦ b -> l1 ++ l2 ⊦ b.
Proof.
intros pi1 pi2.
destruct l1 as [ | c l1 ].
- eapply sub_cut0; eassumption.
- cbn. apply sub_is in pi1, pi2. apply is_sub.
  eapply iis1_prop.Direct_Transitivity.sub_trans; eassumption.
Qed.


(** * Conservativity of ISₕ over ∩ISₕ *)

Lemma ish_iish a l : ish.lprove (map ilform l) (ilform a) -> l ⊦ a.
Proof.
intro pi. remember (map ilform l) as l0 eqn:Hl. remember (ilform a) as a0 eqn:Ha.
induction pi in a, l, Ha, Hl |- *; decomp_list_eq Hl; subst;
  try (destruct a; destr_eq Ha); try (destruct x; destr_eq Heq); subst;
  try (now destruct x0; destr_eq Heq);
  try (constructor; [ apply IHpi1 | apply IHpi2 ]; reflexivity);
  try (constructor; apply IHpi; list_simpl; reflexivity).
destruct Heq as [->%ilform_inj ->]. constructor.
Qed.
