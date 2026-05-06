(* BCD Subtyping Relation *)

From Stdlib Require Import CRelationClasses.
From OLlibs Require Import List_more.
From InterPT Require Export iformulas.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(* Tables 5 and 7 *)
Reserved Notation "a ≤ b" (at level 70).
Inductive bcd_sub {lax : list (Atom -> form * form)} : crelation form :=
| bcd_identity a : a ≤ a
| bcd_trans a b c : a ≤ b -> b ≤ c -> a ≤ c
| bcd_omega_right a : a ≤ Ω
| bcd_inter_left1 a b : a ∩ b ≤ a
| bcd_inter_left2 a b : a ∩ b ≤ b
| bcd_inter_right a : a ≤ a ∩ a
| bcd_inter a b c d : a ≤ c -> b ≤ d -> a ∩ b ≤ c ∩ d
| bcd_arrow a b c d : c ≤ a -> b ≤ d -> a → b ≤ c → d
| bcd_arrow_inter a b c : (a → b) ∩ (a → c) ≤ a → b ∩ c
| bcd_arrow_omega : Ω ≤ Ω → Ω
| bcd_axiom ax x : InT ax lax -> fst (ax x) ≤ snd (ax x)
where "a ≤ b" := (bcd_sub a b).


Section BCD_axioms.

Context {lax : list (Atom -> form * form)}.
Infix "⩽" := (@bcd_sub lax) (at level 70).

Definition bcd_equiv a b := ((a ⩽  b) * (b ⩽  a))%type.
Infix "≡" := bcd_equiv (at level 70).

#[export] Instance bcd_preorder : PreOrder (@bcd_sub lax).
Proof. split; intro a; [ exact (bcd_identity a) | intros b c H1 H2; exact (bcd_trans H1 H2) ]. Qed.

#[export] Instance bcd_equivalence : Equivalence bcd_equiv.
Proof.
split.
- intro a. split; reflexivity.
- intros a b [H1 H2]. split; assumption.
- intros a b c [H1 H2] [H3 H4]. split; etransitivity; eassumption.
Qed.


Example bcd_inter_comm a b : a ∩ b ≡ b ∩ a.
Proof.
enough (forall a b, a ∩ b ⩽ b ∩ a) as Hc by (split; apply Hc).
clear. intros a b. transitivity ((a ∩ b) ∩ (a ∩ b)).
- apply bcd_inter_right.
- apply bcd_inter; [ apply bcd_inter_left2 | apply bcd_inter_left1 ].
Qed.

Example bcd_inter_assoc a b c : (a ∩ b) ∩ c ≡ a ∩ (b ∩ c).
Proof.
split.
- transitivity (((a ∩ b) ∩ c) ∩ ((a ∩ b) ∩ c)); [ apply bcd_inter_right | apply bcd_inter ].
  + transitivity (a ∩ b); apply bcd_inter_left1.
  + apply bcd_inter; [ apply bcd_inter_left2 | reflexivity ].
- transitivity ((a ∩ (b ∩ c)) ∩ (a ∩ (b ∩ c))); [ apply bcd_inter_right | apply bcd_inter ].
  + apply bcd_inter; [ reflexivity | apply bcd_inter_left1 ].
  + transitivity (b ∩ c); apply bcd_inter_left2.
Qed.

Example bcd_inter_unit a : a ∩ Ω ≡ a.
Proof.
split; [ apply bcd_inter_left1 | ].
transitivity (a ∩ a); [ apply bcd_inter_right | apply bcd_inter; constructor ].
Qed.

(* Example 16 *)
Example bcd_arrow_inter_distr a b c : a → (b ∩ c) ≡ (a → b) ∩ (a → c).
Proof.
split; [ | apply bcd_arrow_inter ].
transitivity ((a → b ∩ c) ∩ (a → b ∩ c));
  [ apply bcd_inter_right | apply bcd_inter; apply bcd_arrow; constructor ].
Qed.

(* Example 16 *)
Example bcd_arrow_omega_distr a : a → Ω ≡ Ω.
Proof.
split; [ apply bcd_omega_right | ].
transitivity (Ω → Ω); [ apply bcd_arrow_omega | apply bcd_arrow; constructor ].
Qed.


Lemma bcd_arrow_list l a b : a ⩽ b -> ⟦l, a⟧ ⩽ ⟦l, b⟧.
Proof. now induction l as [ | d l IHl ]; intro; [ | apply bcd_arrow, IHl ]. Qed.

Lemma bcd_arrow_inter_list l a b c : a ⩽ ⟦l, b⟧ -> a ⩽ ⟦l, c⟧ -> a ⩽ ⟦l, b ∩ c⟧.
Proof.
induction l as [ | d l IHl ] in b, c |- * using rev_rect; intros Hl Hr.
- etransitivity; [ apply bcd_inter_right | apply bcd_inter; eassumption ].
- transitivity (⟦l,(d → b) ∩ (d → c)⟧).
  + apply IHl; rewrite <- list2form_last; assumption.
  + rewrite list2form_last. apply bcd_arrow_list, bcd_arrow_inter.
Qed.

End BCD_axioms.
