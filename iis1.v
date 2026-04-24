(* System ∩IS₁ for Intersection Subtyping *)

From Stdlib Require Import CRelationClasses.
From OLlibs Require Import List_more.
From InterPT Require Export iformulas.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * System ∩IS₁ *)

Reserved Notation "a ❘ l ⊦ b" (at level 65, l at next level, b at next level).
Reserved Notation "a ❘ ⊦ b" (at level 65, b at next level).

Inductive sub : list form -> crelation form :=
| identity a : a ❘ ⊦ a
| omega_right a l : a ❘ l ⊦ Ω
| inter_left1 b a c l : a ❘ l ⊦ c -> a ∩ b ❘ l ⊦ c
| inter_left2 b a c l : a ❘ l ⊦ c -> b ∩ a ❘ l ⊦ c
| inter_right a b c l : c ❘ l ⊦ a -> c ❘ l ⊦ b -> c ❘ l ⊦ a ∩ b
| arrow_left a b c d l : c ❘ ⊦ a -> b ❘ l ⊦ d -> a → b ❘ c :: l ⊦ d
| arrow_right a b c l : c ❘ l · a ⊦ b -> c ❘ l ⊦ a → b
where "a ❘ l ⊦ b" := (sub l a b)
  and "a ❘ ⊦ b" := (sub nil a b).
Hint Constructors sub : core.
Arguments identity {_}.
Arguments omega_right {_ _}.
Arguments inter_left1 [_ _ _ _].
Arguments inter_left2 [_ _ _ _].
Arguments arrow_right [_ _ _ _].

Ltac induction_sub H a b c d l pi1 pi2 IH1 IH2 :=
  induction H as
  [ a
  | a l
  | b a c l pi1 IH1
  | b a c l pi1 IH1
  | a b c l pi1 IH1 pi2 IH2
  | a b c d l pi1 IH1 pi2 IH2
  | a b c l pi1 IH1 ].

Fixpoint weight a l b (pi : a ❘ l ⊦ b) := S
  match pi with
  | identity | omega_right => 0
  | inter_left1 pi1 | inter_left2 pi1 | arrow_right pi1 => weight pi1
  | inter_right pi1 pi2 => max (weight pi1) (weight pi2)
  | arrow_left pi1 pi2 => weight pi1 + weight pi2
  end.

Definition sub_equiv a b := ((a ❘ ⊦ b) * (b ❘ ⊦ a))%type.
Infix "⟛" := sub_equiv (at level 65).

Example inter_compat a1 b1 a2 b2 : a1 ⟛ b1 -> a2 ⟛ b2 -> a1 ∩ a2 ⟛ b1 ∩ b2.
Proof. intros [] []. repeat constructor; assumption. Qed.

Example inter_comm a b : a ∩ b ⟛ b ∩ a.
Proof. repeat constructor; fail. Qed.

Example inter_assoc a b c : (a ∩ b) ∩ c ⟛ a ∩ (b ∩ c).
Proof. constructor; repeat apply inter_right; do 2 constructor; apply identity. Qed.

Example inter_unit_r a : a ∩ Ω ⟛ a.
Proof. repeat constructor; fail. Qed.

Example inter_unit_l a : Ω ∩ a ⟛ a.
Proof. repeat constructor; fail. Qed.

Example arrow_compat c a b : a ⟛ b -> c → a ⟛ c → b.
Proof. intros []. repeat constructor; assumption. Qed.

Example arrow_inter_distr a b c : a → (b ∩ c) ⟛ (a → b) ∩ (a → c).
Proof. repeat constructor; fail. Qed.

Example arrow_omega_distr a : a → Ω ⟛ Ω.
Proof. repeat constructor; fail. Qed.

Example inter_depth_2 a b c d : ((b ∩ a) → c) → d ❘ ⊦ ((a → c) → d) ∩ ((b → c) → d).
Proof. repeat constructor; fail. Qed.
