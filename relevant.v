From Stdlib Require Import Bool.
From OLlibs Require Import Logic_Datatypes_more List_more.
From InterPT Require Export iformulas.
From InterPT Require Import iish.
Import LogicNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * System B+ *)

Inductive bp : form -> Type :=
| bp_id a : bp (a → a)
| bp_pl b a : bp (a ∩ b → a)
| bp_pr a b : bp (a ∩ b → b)
| bp_distr a b c : bp (((a → b) ∩ (a → c)) → (a → (b ∩ c)))
| bp_cancel a : bp (Ω → (a → Ω))
| bp_mp a b : bp a -> bp (a → b) -> bp b
| bp_inter a b : bp a -> bp b -> bp (a ∩ b)
| bp_omega : bp Ω
| bp_impl c a b : bp (a → b) -> bp ((b → c) → (a → c))
| bp_impr c a b : bp (a → b) -> bp ((c → a) → (c → b)).

Lemma bp_trans a b c : bp (a → b) -> bp (b → c) -> bp (a → c).
Proof. intros pi1 pi2. apply (bp_mp pi1), bp_impr, pi2. Qed.


(** * Equivalence between B+ and ISh *)

Lemma bp_is a : bp a -> ⊦ a.
Proof.
intro pi. induction pi.
- apply arrow_right, identity.
- apply arrow_right. apply inter_left1, identity.
- apply arrow_right. apply inter_left2, identity.
- do 2 apply arrow_right. cbn. apply inter_right.
  + apply inter_left1. apply arrow_left; apply identity.
  + apply inter_left2. apply arrow_left; apply identity.
- do 2 apply arrow_right. apply omega_right.
- inversion_clear IHpi2.
  rewrite <- (app_nil_l nil). eapply sub_cut; eassumption.
- apply inter_right; assumption.
- apply omega_right.
- do 2 apply arrow_right. apply arrow_left.
  + inversion_clear IHpi. assumption.
  + apply identity.
- do 2 apply arrow_right. apply arrow_left.
  + apply identity.
  + inversion_clear IHpi. assumption.
Qed.

Lemma is_bp l a : l ⊦ a -> bp ⟦l , a⟧.
Proof.
intro pi. induction pi.
- apply bp_id.
- enough (bp (Ω → ⟦l, Ω⟧)) as Hd
    by (eapply bp_mp; [ apply bp_omega | apply Hd ]).
  induction l as [ | c l IH ].
  + apply bp_id.
  + eapply bp_trans; [ apply bp_cancel | apply bp_impr, IH ].
- eapply bp_trans; [ apply bp_pl | apply IHpi ].
- eapply bp_trans; [ apply bp_pr | apply IHpi ].
- enough (bp (⟦l, a⟧ ∩ ⟦l, b⟧ → ⟦l, a ∩ b⟧)) as Hd.
  { eapply bp_mp; [ | apply Hd ]. apply bp_inter; assumption. }
  clear. induction l as [ | c l IH ].
  + apply bp_id.
  + eapply bp_trans; [ apply bp_distr | apply bp_impr, IH ].
- cbn. eapply bp_trans.
  + apply bp_impl, IHpi1.
  + apply bp_impr, IHpi2.
- rewrite <- list2form_last. assumption.
Qed.

Lemma bp_is_equiv a : bp a <=> ⊦ a.
Proof. split; [ apply bp_is | apply is_bp ]. Qed.
