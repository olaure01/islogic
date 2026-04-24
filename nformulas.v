(* Negative Formulas *)

From Stdlib Require Import PeanoNat Lia Wf_nat.
From OLlibs Require Import funtheory List_more.
From InterPT Require lformulas.
Export ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** ** Formulas *)

Inductive lform :=
| lvar (_ : comparison) (_ : nat) | lmap (_ _ : lform)
| ltop | lwith (_ _ : lform)
| lfrl (_ : nat) (_ : lform).

Notation 𝖳 := ltop.
Infix "∧" := lwith (at level 35).
Notation "b / a" := (lmap a b) (left associativity, at level 40, a at next level).
Notation cst := (lvar Lt).  (* propositional constants *)
Notation dvar := (lvar Eq). (* de Bruijn indices *)
Notation var := (lvar Gt).  (* second order variables *)
Notation "∀" := lfrl.

(** Size *)
Fixpoint fsize a := S
match a with
| lvar _ _ | ltop => 0
| lmap c d | lwith c d => fsize c + fsize d
| lfrl _ c => fsize c
end.

Fixpoint freevars A :=
match A with
| var X => X :: nil
| dvar _ => nil
| cst _ => nil
| ltop => nil
| lmap B C | lwith B C => (freevars B) ++ (freevars C)
| lfrl X B => remove Nat.eq_dec X (freevars B)
end.
Notation closed A := (freevars A = nil).

(** substitutes [formula] [F] for variable [X] in [formula] [A] (capture is possible) *)
Fixpoint subs X F A :=
match A with
| dvar k => dvar k
| var Y => if Nat.eq_dec Y X then F else var Y
| cst R => cst R
| lmap B C => lmap (subs X F B) (subs X F C)
| ltop => ltop
| lwith B C => lwith (subs X F B) (subs X F C)
| lfrl Y B => lfrl Y (if Nat.eq_dec Y X then B else subs X F B)
end.

Lemma nfree_subs x f a : ~ In x (freevars a) -> subs x f a = a.
Proof.
induction a; intro Hf; auto.
- cbn. destruct c; auto.
  destruct (Nat.eq_dec n x); [ | reflexivity ].
  exfalso. subst n. apply Hf. apply in_eq.
- cbn in Hf. cbn. rewrite IHa1, IHa2; [ reflexivity | | ]; in_solve.
- cbn in Hf. cbn. rewrite IHa1, IHa2; [ reflexivity | | ]; in_solve.
- cbn in Hf. cbn. destruct (Nat.eq_dec n x); [ reflexivity | ].
  rewrite IHa; [ reflexivity | ].
  intro Hin. apply Hf.
  apply in_in_remove; [ | assumption ]. auto.
Qed.

Lemma freevars_subs x f a : incl (freevars (subs x f a)) (freevars f ++ remove Nat.eq_dec x (freevars a)).
Proof.
induction a; cbn; intros z Hz.
- destruct c; cbn in Hz; auto.
  + destruct Hz.
  + destruct Hz.
  + cbn. destruct (Nat.eq_dec n x).
    * in_solve.
    * destruct (Nat.eq_dec x n); list_simpl.
      -- contradiction n0. subst. reflexivity.
      -- in_solve.
- rewrite remove_app. apply in_app_or in Hz as [Hz|Hz].
  + specialize (IHa1 z Hz). in_solve.
  + specialize (IHa2 z Hz). in_solve.
- inT_solve.
- rewrite remove_app. apply in_app_or in Hz as [Hz|Hz].
  + specialize (IHa1 z Hz). in_solve.
  + specialize (IHa2 z Hz). in_solve.
- destruct (Nat.eq_dec n x); subst; auto.
  + rewrite remove_remove_eq. in_solve.
  + rewrite remove_remove_comm.
    apply in_remove in Hz.
    destruct Hz.
    apply IHa in H.
    apply in_or_app.
    apply in_app_or in H as [H|H].
    * left. assumption.
    * right. apply in_in_remove; assumption.
Qed.

Lemma subs_subs_com x f y g a : closed f -> closed g ->
  subs y g (subs x f a) = if (Nat.eq_dec y x) then subs x f a else subs x f (subs y g a).
Proof.
destruct (Nat.eq_dec y x); intros Hf Hg.
{ subst.
  apply nfree_subs.
  intro Hin. apply (freevars_subs x f a) in Hin.
  apply in_app_or in Hin. rewrite Hf in Hin.
  destruct Hin as [[] | Hin].
  revert Hin. apply remove_In. }
induction a; auto.
- destruct c; auto.
  cbn. destruct (Nat.eq_dec n0 x); subst; auto.
  + destruct (Nat.eq_dec x y); subst; auto.
    * contradiction n. reflexivity.
    * cbn. destruct (Nat.eq_dec x x).
      2:{ contradiction n1. reflexivity. }
      apply nfree_subs. rewrite Hf. intros [].
  + destruct (Nat.eq_dec n0 y); auto.
    * cbn. subst. destruct (Nat.eq_dec y y).
      2:{ contradiction n0. reflexivity. }
      symmetry. apply nfree_subs. rewrite Hg. intros [].
    * cbn. destruct (Nat.eq_dec n0 x); subst; auto.
      -- contradiction n1. reflexivity.
      -- destruct (Nat.eq_dec n0 y); subst; auto.
         contradiction n2. reflexivity.
- cbn. now rewrite IHa1, IHa2.
- cbn. now rewrite IHa1, IHa2.
- cbn. destruct (Nat.eq_dec n0 y), (Nat.eq_dec n0 x); subst.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + rewrite IHa. reflexivity.
Qed.

Lemma fsize_subs_lvar c x y a : fsize (subs x (lvar c y) a) = fsize a.
Proof.
induction a; auto.
- cbn. destruct c0; auto.
  destruct (Nat.eq_dec n x); auto.
- cbn. rewrite IHa1, IHa2. reflexivity.
- cbn. rewrite IHa1, IHa2. reflexivity.
- cbn. destruct (Nat.eq_dec n x); auto.
Qed.

(** substitutes [formula] [F] for index [n] in [formula] [A] and decreases indexes above [n] *)
Fixpoint nsubs n F A :=
match A with
| var X => var X
| dvar k => match n ?= k with
            | Eq => F
            | Lt => dvar (pred k)
            | Gt => dvar k
            end
| cst R => cst R
| lmap B C => lmap (nsubs n F B) (nsubs n F C)
| ltop => ltop
| lwith B C => lwith (nsubs n F B) (nsubs n F C)
| lfrl X B => lfrl X (nsubs n F B)
end.

Lemma freevars_nsubs n f (Hc : closed f) a : freevars (nsubs n f a) = freevars a.
Proof.
induction a; auto.
- destruct c; auto.
  cbn. destruct (n ?= n0); auto.
- cbn. rewrite IHa1, IHa2. reflexivity.
- cbn. rewrite IHa1, IHa2. reflexivity.
- cbn. f_equal. assumption.
Qed.

Lemma nsubs_subs_com x f n g (Hin : ~ In x (freevars g)) a :
  nsubs n g (subs x f a) = subs x (nsubs n g f) (nsubs n g a).
Proof.
induction a; auto.
- destruct c; auto.
  + cbn. destruct (n ?= n0); auto.
    now rewrite nfree_subs.
  + cbn. destruct (Nat.eq_dec n0 x); auto.
- cbn. rewrite IHa1, IHa2. reflexivity.
- cbn. rewrite IHa1, IHa2. reflexivity.
- cbn. destruct (Nat.eq_dec n0 x).
  + reflexivity.
  + rewrite IHa. reflexivity.
Qed.


(** lift indexes above [k] in [formula] [A] *)
Fixpoint fup k A :=
match A with
| var X => var X
| dvar n => if n <? k then dvar n else dvar (S n)
| cst R => cst R
| lmap B C => lmap (fup k B) (fup k C)
| ltop => ltop
| lwith B C => lwith (fup k B) (fup k C)
| lfrl X B => lfrl X (fup k B)
end.
Notation fupz := (fup 0).

Lemma fup_lvar k v x : { y & fup k (lvar v x) = lvar v y }.
Proof.
destruct v.
- destruct k.
  + exists (S x). reflexivity.
  + cbn. destruct (x <=? k).
    * exists x. reflexivity.
    * exists (S x). reflexivity.
- exists x. reflexivity.
- exists x. reflexivity.
Qed.

Lemma fup_fup_com k a : fup (S k) (fupz a) = fupz (fup k a).
Proof.
induction a; auto.
- cbn. destruct c; auto.
  destruct k; auto.
  cbn. destruct (n <=? k); auto.
- cbn. rewrite IHa1, IHa2. reflexivity.
- cbn. rewrite IHa1, IHa2. reflexivity.
- cbn. f_equal. assumption.
Qed.

Lemma fsize_fup k a : fsize (fup k a) = fsize a.
Proof.
induction a; auto; cbn.
- destruct c; auto.
  destruct k; auto.
  destruct (n <=? k); auto.
- rewrite IHa1, IHa2. reflexivity.
- rewrite IHa1, IHa2. reflexivity.
- f_equal. assumption.
Qed.

Lemma freevars_fup k a : freevars (fup k a) = freevars a.
Proof.
induction a; auto; cbn.
- destruct c; auto.
  destruct k; auto.
  destruct (n <=? k); auto.
- rewrite IHa1, IHa2. reflexivity.
- rewrite IHa1, IHa2. reflexivity.
- f_equal. assumption.
Qed.

Lemma fup_subs_com k x f a : fup k (subs x f a) = subs x (fup k f) (fup k a).
Proof.
induction a; auto; cbn.
- destruct c; auto.
  + cbn. destruct k; auto.
    destruct (n <=? k); auto.
  + destruct (Nat.eq_dec n x); auto.
    * subst. cbn. case_eq (Nat.eq_dec x x).
      -- intros. reflexivity.
      --  intros Hneq. contradiction Hneq. reflexivity.
    * cbn. case_eq (Nat.eq_dec n x).
      -- intros ->. contradiction n0. reflexivity.
      -- intros. reflexivity.
- rewrite IHa1, IHa2. reflexivity.
- rewrite IHa1, IHa2. reflexivity.
- f_equal. destruct (Nat.eq_dec n x); auto.
Qed.


Lemma nsubs_fup_com k f a : nsubs (S k) (fupz f) (fupz a) = fupz (nsubs k f a).
Proof.
induction a; auto; cbn.
- destruct c; auto.
  cbn. case_eq (k ?= n); auto.
  intros Hkn%Compare_dec.nat_compare_Lt_lt.
  cbn. f_equal. lia.
- rewrite IHa1, IHa2. reflexivity.
- rewrite IHa1, IHa2. reflexivity.
- f_equal. assumption.
Qed.

Lemma nsubs_z_fup f a : nsubs 0 f (fupz a) = a.
Proof.
induction a; auto; cbn.
- destruct c; auto.
- rewrite IHa1, IHa2. reflexivity.
- rewrite IHa1, IHa2. reflexivity.
- f_equal. assumption.
Qed.


(** * Embedding into general formulas *)

Fixpoint nlform a :=
match a with
| lvar v x => lformulas.lvar v x
| 𝖳 => lformulas.ltop
| c ∧ d => lformulas.lwith (nlform c) (nlform d)
| d / c => lformulas.lmap (nlform c) (nlform d)
| ∀ x c => lformulas.lfrl x (nlform c)
end.
Coercion nlform : lform >-> lformulas.lform.

Lemma nlform_inj : injective nlform.
Proof.
intro a. induction a; intros [] Heq; cbn in Heq; destr_eq Heq; subst; try reflexivity.
- apply IHa1 in Heq. apply IHa2 in H. subst. reflexivity.
- apply IHa1 in Heq. apply IHa2 in H. subst. reflexivity.
- apply IHa in H. subst. reflexivity.
Qed.

Lemma nlfreevars a : freevars a = lformulas.freevars a.
Proof. induction a; list_simpl; rewrite ?IHa, ?IHa1, ?IHa2; reflexivity. Qed.

Lemma nlclosed a : closed a <-> lformulas.closed a.
Proof. rewrite nlfreevars. reflexivity. Qed.
