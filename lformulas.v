(* Formulas *)

From Stdlib Require Import PeanoNat Lia.
From OLlibs Require Import List_more.
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
| lzero | lplus (_ _ : lform)
| lone
| lfrl (_ : nat) (_ : lform) | lexs (_ : nat) (_ : lform).

Notation 𝖳 := ltop.
Infix "∧" := lwith (at level 35).
Notation "b / a" := (lmap a b) (left associativity, at level 40, a at next level).
Notation "0" := lzero.
Infix "∨" := lplus (at level 35).
Notation "1" := lone.
Notation cst := (lvar Lt).  (* propositional constants *)
Notation dvar := (lvar Eq). (* de Bruijn indices *)
Notation var := (lvar Gt).  (* second order variables *)
Notation "∀" := lfrl.
Notation "∃" := lexs.

(** Size *)
Fixpoint fsize a := S
match a with
| lvar _ _ | ltop | lzero | lone => 0
| lmap c d | lwith c d | lplus c d => fsize c + fsize d
| lfrl _ c | lexs _ c => fsize c
end.

(** substitutes [formula] [F] for variable [X] in [formula] [A] (capture is possible) *)
Fixpoint subs X F A :=
match A with
| dvar k => dvar k
| var Y => if Nat.eq_dec Y X then F else var Y
| cst R => cst R
| lmap B C => lmap (subs X F B) (subs X F C)
| ltop => ltop
| lwith B C => lwith (subs X F B) (subs X F C)
| lzero => lzero
| lplus B C => lplus (subs X F B) (subs X F C)
| lone => lone
| lfrl Y B => lfrl Y (if Nat.eq_dec Y X then B else subs X F B)
| lexs Y B => lexs Y (if Nat.eq_dec Y X then B else subs X F B)
end.

Lemma fsize_subs_lvar c x y a : fsize (subs x (lvar c y) a) = fsize a.
Proof.
induction a; cbn; rewrite ?IHa1, ?IHa2; try destruct (Nat.eq_dec n x); auto.
- destruct c0; auto.
- destruct c0; auto.
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
| lzero => lzero
| lplus B C => lplus (nsubs n F B) (nsubs n F C)
| lone => lone
| lfrl X B => lfrl X (nsubs n F B)
| lexs X B => lexs X (nsubs n F B)
end.

Fixpoint freevars A :=
match A with
| var X => X :: nil
| dvar _ => nil
| cst _ => nil
| ltop | lzero | lone => nil
| lmap B C | lwith B C | lplus B C => (freevars B) ++ (freevars C)
| lfrl X B | lexs X B => remove Nat.eq_dec X (freevars B)
end.
Notation closed A := (freevars A = nil).

Lemma freevars_nsubs n f (Hc : closed f) a : freevars (nsubs n f a) = freevars a.
Proof.
induction a; cbn; rewrite ?IHa1, ?IHa2, ?IHa; auto.
destruct c; auto.
now destruct (n ?= n0).
Qed.

Lemma nfree_subs x f a : ~ In x (freevars a) -> subs x f a = a.
Proof.
induction a; intro Hf; auto.
- cbn. destruct c; auto.
  destruct (Nat.eq_dec n x); [ | reflexivity ].
  exfalso. subst n. apply Hf. apply in_eq.
- cbn in Hf. cbn. rewrite IHa1, IHa2; [ reflexivity | | ]; in_solve.
- cbn in Hf. cbn. rewrite IHa1, IHa2; [ reflexivity | | ]; in_solve.
- cbn in Hf. cbn. rewrite IHa1, IHa2; [ reflexivity | | ]; in_solve.
- cbn in Hf. cbn. destruct (Nat.eq_dec n x); [ reflexivity | ].
  rewrite IHa; [ reflexivity | ].
  intro Hin. apply Hf.
  apply in_in_remove; [ | assumption ]. auto.
- cbn in Hf. cbn. destruct (Nat.eq_dec n x); [ reflexivity | ].
  rewrite IHa; [ reflexivity | ].
  intro Hin. apply Hf.
  apply in_in_remove; [ | assumption ]. auto.
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
- cbn. rewrite IHa1, IHa2. reflexivity.
- cbn. destruct (Nat.eq_dec n0 x).
  + reflexivity.
  + rewrite IHa. reflexivity.
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
| lzero => lzero
| lplus B C => lplus (fup k B) (fup k C)
| lone => lone
| lfrl X B => lfrl X (fup k B)
| lexs X B => lexs X (fup k B)
end.
Notation fupz := (fup 0).

Lemma fup_fup_com k a : fup (S k) (fupz a) = fupz (fup k a).
Proof.
induction a; cbn; rewrite ?IHa1, ?IHa2, ?IHa; auto.
destruct c, k; auto.
cbn. now destruct (n <=? k).
Qed.

Lemma fsize_fup k a : fsize (fup k a) = fsize a.
Proof.
induction a; cbn; rewrite ?IHa1, ?IHa2, ?IHa; auto.
destruct c, k; auto.
cbn. now destruct (n <=? k).
Qed.

Lemma freevars_fup k a : freevars (fup k a) = freevars a.
Proof.
induction a; cbn; rewrite ?IHa1, ?IHa2, ?IHa; auto.
destruct c, k; auto.
cbn. now destruct (n <=? k).
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
- rewrite IHa1, IHa2. reflexivity.
- f_equal. destruct (Nat.eq_dec n x); auto.
- f_equal. destruct (Nat.eq_dec n x); auto.
Qed.

Lemma nsubs_fup_com k f a : nsubs (S k) (fupz f) (fupz a) = fupz (nsubs k f a).
Proof.
induction a; cbn; rewrite ?IHa1, ?IHa2, ?IHa; auto.
destruct c; auto.
cbn. case_eq (k ?= n); auto.
intros Hkn%Compare_dec.nat_compare_Lt_lt.
cbn. f_equal. lia.
Qed.

Lemma nsubs_z_fup f a : nsubs 0 f (fupz a) = a.
Proof.
induction a; cbn; rewrite ?IHa1, ?IHa2, ?IHa; auto.
now destruct c.
Qed.
