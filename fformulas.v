(* Forall Formulas *)

From Stdlib Require Import PeanoNat Lia Wf_nat.
From OLlibs Require Import Logic_Datatypes_more List_more.
Import LogicNotations.
Export ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** ** Formulas *)

Inductive fform := lvar (_ : comparison) (_ : nat) | lmap (_ _ : fform) | lfrl (_ : nat) (_ : fform).

Infix "→" := lmap (left associativity, at level 40).
Notation cst := (lvar Lt).  (* propositional constants *)
Notation dvar := (lvar Eq). (* de Bruijn indices *)
Notation var := (lvar Gt).  (* second order variables *)
Notation "∀" := lfrl.

(** Size *)
Fixpoint fsize a := S
match a with
| lvar _ _ => 0
| lmap c d => fsize c + fsize d
| lfrl _ c => fsize c
end.

Fixpoint freevars A :=
match A with
| var X => X :: nil
| dvar _ | cst _ => nil
| lmap B C => (freevars B) ++ (freevars C)
| lfrl X B => remove Nat.eq_dec X (freevars B)
end.
Notation closed A := (freevars A = nil).

Lemma closed_fold_lmap a l : closed (fold_right lmap a l) <=> ForallT (fun u => closed u) (a :: l).
Proof.
induction l as [ | b l IH ]; cbn.
- split; intro Hc.
  + constructor; [ assumption | constructor ].
  + inversion Hc. assumption.
- destruct IH as [IH1 IH2]. split; intro Hc.
  + decomp_list_eq Hc. destruct Hc as [Hb Hl].
    apply IH1 in Hl. inversion_clear Hl.
    repeat constructor; assumption.
  + inversion_clear Hc. inversion_clear X. rewrite IH2.
    * rewrite H0. reflexivity.
    * constructor; assumption.
Qed.

(** substitutes [formula] [F] for variable [X] in [formula] [A] (capture is possible) *)
Fixpoint subs X F A :=
match A with
| dvar k => dvar k
| var Y => if Nat.eq_dec Y X then F else var Y
| cst R => cst R
| lmap B C => lmap (subs X F B) (subs X F C)
| lfrl Y B => lfrl Y (if Nat.eq_dec Y X then B else subs X F B)
end.

Lemma nfree_subs x f a : ~ In x (freevars a) -> subs x f a = a.
Proof.
induction a; intro Hf; auto.
- cbn. destruct c; auto.
  destruct (Nat.eq_dec n x); [ | reflexivity ].
  exfalso. subst n. apply Hf. apply in_eq.
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

Lemma freevars_subs_closed x f a : closed f -> freevars (subs x f a) = remove Nat.eq_dec x (freevars a).
Proof.
intro Hf. induction a.
- destruct c; cbn; [ reflexivity .. | ].
  destruct (Nat.eq_dec n x) as [He | Hn].
  + subst. destruct (Nat.eq_dec x x) as [He' | Hn']; [ assumption | ]. now contradiction Hn'.
  + cbn. destruct (Nat.eq_dec x n) as [He' | Hn']; [ | reflexivity ]. now contradiction Hn.
- cbn. symmetry. rewrite IHa1, IHa2. apply remove_app.
- cbn. rewrite remove_remove_comm.
  destruct (Nat.eq_dec n x).
  + subst. rewrite remove_remove_eq. reflexivity.
  + f_equal. assumption.
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
| lfrl X B => lfrl X (nsubs n F B)
end.

Lemma freevars_nsubs n f (Hc : closed f) a : freevars (nsubs n f a) = freevars a.
Proof.
induction a; auto.
- destruct c; auto.
  cbn. destruct (n ?= n0); auto.
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
- cbn. f_equal. assumption.
Qed.

Lemma fsize_fup k a : fsize (fup k a) = fsize a.
Proof.
induction a; auto; cbn.
- destruct c; auto.
  destruct k; auto.
  destruct (n <=? k); auto.
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
- f_equal. assumption.
Qed.

Lemma nsubs_z_fup f a : nsubs 0 f (fupz a) = a.
Proof.
induction a; auto; cbn.
- destruct c; auto.
- rewrite IHa1, IHa2. reflexivity.
- f_equal. assumption.
Qed.
