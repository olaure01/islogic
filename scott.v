(* System IS Scott for Scott Model through Intersection Subtyping *)

From Stdlib Require Import Wf_nat Lia CMorphisms.
From OLlibs Require Import Logic_Datatypes_more List_more SubListT.
From InterPT Require iis1.
From InterPT Require Import bcd.
Import LogicNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


(** * System IS_Scott *)

Definition stoup := option form.
Coercion St := Some : form -> stoup.
Definition Fm (p : stoup) := match p with None => Ω | Some a => a end.

(* Table 9 *)
Reserved Notation "p ❘ l ⊦ b" (at level 65, l at next level, b at next level).
Inductive sc_sub : list form -> stoup -> form -> Type :=
| sc_omega_right p l : p ❘ l ⊦ Ω
| sc_inter_left1 (b a : form) c l : a ❘ l ⊦ c -> a ∩ b ❘ l ⊦ c
| sc_inter_left2 (b a c : form) l : a ❘ l ⊦ c -> b ∩ a ❘ l ⊦ c
| sc_inter_right a b p l : p ❘ l ⊦ a -> p ❘ l ⊦ b -> p ❘ l ⊦ a ∩ b
| sc_arrow_left (a b c d : form) l : c ❘ nil ⊦ a -> b ❘ l ⊦ d -> a → b ❘ c :: l ⊦ d
| sc_arrow_right a b p l : p ❘ l · a ⊦ b -> p ❘ l ⊦ a → b
| sc_var_left (x : Atom) l : x ❘ l ⊦ x
| sc_var_right (a b : form) (x : Atom) l : None ❘ nil ⊦ a -> b ❘ nil ⊦ x -> a → b ❘ l ⊦ x
where "p ❘ l ⊦ b" := (sc_sub l p b).
Hint Constructors sc_sub : core.
Arguments sc_omega_right {_ _}.
Arguments sc_inter_left1 [_ _ _ _].
Arguments sc_inter_left2 [_ _ _ _].
Arguments sc_arrow_right [_ _ _ _].
Arguments sc_var_left {_ _}.
Arguments sc_var_right [_ _ _ _].

Definition sc_sub_nil : crelation form := fun a b => a ❘ nil ⊦ b.
Notation "a ❘ ⊦ b" := (sc_sub_nil a b) (at level 65, b at next level).

Definition sc_sub_equiv : crelation form := fun a b => ((a ❘ ⊦ b) * (b ❘ ⊦ a))%type.
Infix "⟛" := sc_sub_equiv (at level 65).

Ltac induction_sc_sub H p x a b c d l pi1 pi2 IH1 IH2 :=
  induction H as
  [ p l
  | b a c l pi1 IH1
  | b a c l pi1 IH1
  | a b p l pi1 IH1 pi2 IH2
  | a b c d l pi1 IH1 pi2 IH2
  | a b p l pi1 IH1
  | x l
  | a b x l pi1 IH1 pi2 IH2 ].

Fixpoint sc_weight a l b (pi : a ❘ l ⊦ b) := S
  match pi with
  | sc_omega_right | sc_var_left => 0
  | sc_inter_left1 pi1 | sc_inter_left2 pi1 | sc_arrow_right pi1 => sc_weight pi1
  | sc_inter_right pi1 pi2 => max (sc_weight pi1) (sc_weight pi2)
  | sc_arrow_left pi1 pi2 | sc_var_right pi1 pi2 => sc_weight pi1 + sc_weight pi2
  end.

Lemma eq_scott (x : Atom) : x ⟛ Ω → x.
Proof. repeat constructor. Qed.

Lemma sc_identity a : a ❘ ⊦ a.
Proof. induction a; repeat constructor; assumption. Qed.

Lemma is_sc l a b : iis1.sub l a b -> a ❘ l ⊦ b.
Proof. intro pi. induction pi; [ apply sc_identity | constructor; assumption .. ]. Qed.

(* Lemma 28 *)
Lemma sc_None_left_rev_weight a l (pi : None ❘ l ⊦ a) p l0 : { pi' : p ❘ l0 ⊦ a | sc_weight pi' = sc_weight pi }.
Proof.
remember None as q eqn:Ho. induction pi in Ho, l0 |- *; destr_eq Ho; subst.
- exists sc_omega_right. reflexivity.
- cbn. destruct (IHpi1 eq_refl l0) as [pi'1 <-], (IHpi2 eq_refl l0) as [pi'2 <-].
  exists (sc_inter_right pi'1 pi'2). reflexivity.
- cbn. destruct (IHpi eq_refl (l0 · a)) as [pi' <-].
  exists (sc_arrow_right pi'). reflexivity.
Qed.

(* Lemma 28 *)
Lemma sc_omega_left_rev_weight a l (pi : Ω ❘ l ⊦ a) p l0 : { pi' : p ❘ l0 ⊦ a | sc_weight pi' = sc_weight pi }.
Proof.
remember (St Ω) as q eqn:Ho. induction pi in Ho, l0 |- *; destr_eq Ho; subst.
- exists sc_omega_right. reflexivity.
- cbn. destruct (IHpi1 eq_refl l0) as [pi'1 <-], (IHpi2 eq_refl l0) as [pi'2 <-].
  exists (sc_inter_right pi'1 pi'2). reflexivity.
- cbn. destruct (IHpi eq_refl (l0 · a)) as [pi' <-].
  exists (sc_arrow_right pi'). reflexivity.
Qed.

(* Lemma 29 *)
Lemma sc_var_left_wk x l c d (pi : var x ❘ l ⊦ c): { pi' : var x ❘ d :: l ⊦ c | sc_weight pi' = sc_weight pi }.
Proof.
remember (St (var x)) as q eqn:Ho. induction pi in Ho |- *; destr_eq Ho; subst.
- exists sc_omega_right. reflexivity.
- cbn. destruct (IHpi1 eq_refl) as [pi'1 <-], (IHpi2 eq_refl) as [pi'2 <-].
  exists (sc_inter_right pi'1 pi'2). reflexivity.
- cbn. destruct (IHpi eq_refl) as [pi' <-].
  revert pi'. rewrite app_comm_cons. intro pi'.
  exists (sc_arrow_right pi'). reflexivity.
- exists sc_var_left. reflexivity.
Qed.

Lemma sc_var_left_wk_gen x l c l0 (pi : var x ❘ l ⊦ c) :
  { pi' : var x ❘ l0 ++ l ⊦ c | sc_weight pi' = sc_weight pi }.
Proof.
induction l0 as [ | d l0 [IH IHs] ].
- exists pi. reflexivity.
- list_simpl.
  destruct (sc_var_left_wk d IH) as [pi' Hs].
  exists pi'. lia.
Qed.

(* Lemma 29 *)
Lemma sc_var_right_wk p l x d (pi : p ❘ l ⊦ var x) : { pi' : p ❘ l · d ⊦ var x | sc_weight pi' = sc_weight pi }.
Proof.
remember (var x) as c eqn:Ho. induction pi in Ho |- *; destr_eq Ho; subst.
- cbn. destruct (IHpi eq_refl) as [pi'1 <-].
  exists (sc_inter_left1 pi'1). reflexivity.
- cbn. destruct (IHpi eq_refl) as [pi'1 <-].
  exists (sc_inter_left2 pi'1). reflexivity.
- cbn. destruct (IHpi2 eq_refl) as [pi'2 <-].
  exists (sc_arrow_left pi1 pi'2). reflexivity.
- exists sc_var_left. reflexivity.
- cbn. exists (sc_var_right pi1 pi2). reflexivity.
Qed.

Lemma sc_var_right_wk_gen p l x l0 (pi : p ❘ l ⊦ var x) :
  { pi' : p ❘ l ++ l0 ⊦ var x | sc_weight pi' = sc_weight pi }.
Proof.
induction l0 as [ | d l0 [IH IHs] ] using rev_rect.
- rewrite app_nil_r. exists pi. reflexivity.
- rewrite app_assoc.
  destruct (sc_var_right_wk d IH) as [pi' Hs].
  exists pi'. lia.
Qed.


(** * Transitivity *)

(* Theorem 30 *)
Lemma sc_sub_trans_rules s :
  ((forall (a b : form) p d l1 l2 (pi1 : a ❘ ⊦ b) (pi2 : p ❘ l1 ++ b :: l2 ⊦ d),
      s = sc_weight pi1 + sc_weight pi2 -> { pi : p ❘ l1 ++ a :: l2 ⊦ d | sc_weight pi <= s })
 * (forall p b c l1 l2 (pi1 : p ❘ l1 ⊦ b) (pi2 : b ❘ l2 ⊦ c),
      s = sc_weight pi1 + sc_weight pi2 -> { pi : p ❘ l1 ++ l2 ⊦ c | sc_weight pi <= s })
 * (forall (x : Atom) b p l (pi1 : None ❘ nil ⊦ b) (pi2 : p ❘ l · b ⊦ x),
      s = sc_weight pi1 + sc_weight pi2 -> { pi : p ❘ l ⊦ x | sc_weight pi <= s })).
Proof.
induction s as [s IH] using (well_founded_induction_type lt_wf).
assert ((forall (a b : form) p d l1 l2 (pi1 : a ❘ ⊦ b) (pi2 : p ❘ l1 ++ b :: l2 ⊦ d),
         sc_weight pi1 + sc_weight pi2 < s ->
         { pi : p ❘ l1 ++ a :: l2 ⊦ d | sc_weight pi <= sc_weight pi1 + sc_weight pi2 }) *
        (forall p b c l1 l2 (pi1 : p ❘ l1 ⊦ b) (pi2 : b ❘ l2 ⊦ c), sc_weight pi1 + sc_weight pi2 < s ->
         { pi : p ❘ l1 ++ l2 ⊦ c | sc_weight pi <= sc_weight pi1 + sc_weight pi2 }) *
        (forall p (x : Atom) b l (pi1 : None ❘ nil ⊦ b) (pi2 : p ❘ l · b ⊦ x), sc_weight pi1 + sc_weight pi2 < s ->
         { pi : p ❘ l ⊦ x | sc_weight pi <= sc_weight pi1 + sc_weight pi2 }))
  as [[IH1 IH2] IH3].
{ split; [ split | ].
  - intros a b p d l1 l2 pi1 pi2 Hs. refine (fst (fst (IH _ Hs)) _ _ _ _ _ _ _ _ eq_refl).
  - intros p b c l1 l2 pi1 pi2 Hs. refine (snd (fst (IH _ Hs)) _ _ _ _ _ _ _ eq_refl).
  - intros p x b l pi1 pi2 Hs. refine (snd (IH _ Hs) _ _ _ _ _ _ eq_refl). }
clear IH. split; [ split | ].
- intros a b c d l1 l2 pi1 pi2 ->.
  remember (l1 ++ b :: l2) as l0 eqn:Heql0. destruct pi2; subst.
  + exists sc_omega_right. cbn. lia.
  + destruct (IH1 _ _ _ _ _ _ pi1 pi2) as [pi Hspi]; [ cbn; lia | ].
    exists (sc_inter_left1 pi). cbn. lia.
  + destruct (IH1 _ _ _ _ _ _ pi1 pi2) as [pi Hspi]; [ cbn; lia | ].
    exists (sc_inter_left2 pi). cbn. lia.
  + destruct (IH1 _ _ _ _ _ _ pi1 pi2_1) as [pi_1 Hspi1]; [ cbn; lia | ].
    destruct (IH1 _ _ _ _ _ _ pi1 pi2_2) as [pi_2 Hspi2]; [ cbn; lia | ].
    exists (sc_inter_right pi_1 pi_2). cbn. lia.
  + decomp_list_eq Heql0; subst.
    * destruct (IH1 _ _ _ _ _ _ pi1 pi2_2) as [pi Hspi]; [ cbn; lia | ].
      exists (sc_arrow_left pi2_1 pi). cbn. lia.
    * destruct (IH2 _ _ _ _ _ pi1 pi2_1) as [pi Hspi]; [ cbn; lia | ].
      exists (sc_arrow_left pi pi2_2). cbn in *. lia.
  + clear IH2 IH3. revert pi2 IH1. list_simpl. intros pi2 IH1.
    destruct (IH1 _ _ _ _ _ _ pi1 pi2) as [pi Hspi]; [ cbn; lia | ].
    revert pi Hspi. rewrite app_comm_cons, app_assoc. intros pi Hspi.
    exists (sc_arrow_right pi). cbn. lia.
  + exists sc_var_left. cbn. lia.
  + exists (sc_var_right pi2_1 pi2_2). cbn. lia.
- intros a b c l1 l2 pi1 pi2 ->. destruct pi1.
  + destruct (sc_omega_left_rev_weight pi2 p (l ++ l2)) as [pi <-]. exists pi. cbn. lia.
  + destruct (IH2 _ _ _ _ _ pi1 pi2) as [pi Hs]; [ | exists (sc_inter_left1 pi) ]; cbn; lia.
  + destruct (IH2 _ _ _ _ _ pi1 pi2) as [pi Hs]; [ | exists (sc_inter_left2 pi) ]; cbn; lia.
  + cbn in IH1, IH2. cbn. remember (St (a ∩ b)) as e eqn:He. destruct pi2; destr_eq He; subst.
    * exists sc_omega_right. cbn. lia.
    * destruct (IH2 _ _ _ _ _ pi1_1 pi2) as [pi Hs]; [ | exists pi ]; cbn; lia.
    * destruct (IH2 _ _ _ _ _ pi1_2 pi2) as [pi Hs]; [ | exists pi ]; cbn; lia.
    * destruct (IH2 _ _ _ _ _ (sc_inter_right pi1_1 pi1_2) pi2_1) as [pi_1 Hs1]; [ cbn; lia | ].
      destruct (IH2 _ _ _ _ _ (sc_inter_right pi1_1 pi1_2) pi2_2) as [pi_2 Hs2]; [ cbn; lia | ].
      exists (sc_inter_right pi_1 pi_2). cbn in *. lia.
    * destruct (IH2 _ _ _ _ _ (sc_inter_right pi1_1 pi1_2) pi2) as [pi Hs]; [ cbn; lia | ].
      revert pi Hs. clear. rewrite app_assoc. cbn. intros pi Hs.
      exists (sc_arrow_right pi). cbn. lia.
  + destruct (IH2 _ _ _ _ _ pi1_2 pi2) as [pi Hs]; [ | exists (sc_arrow_left pi1_1 pi) ]; cbn; lia.
  + cbn in IH1, IH2. cbn. remember (St (a → b)) as e eqn:He. destruct pi2; destr_eq He; subst.
    * exists sc_omega_right. cbn. lia.
    * destruct (IH2 _ _ _ _ _ (sc_arrow_right pi1) pi2_1) as [pi_1 Hs1]; [ cbn; lia | ].
      destruct (IH2 _ _ _ _ _ (sc_arrow_right pi1) pi2_2) as [pi_2 Hs2]; [ cbn; lia | ].
      exists (sc_inter_right pi_1 pi_2). cbn in *. lia.
    * destruct (IH1 _ _ _ _ _ _ pi2_1 pi1) as [pi Hs]; [ cbn; lia | ].
      destruct (IH2 _ _ _ _ _ pi pi2_2) as [pi' Hs']; [ cbn; lia | ].
      revert pi' Hs'. list_simpl. intros pi' Hs'.
      exists pi'. lia.
    * destruct (IH2 _ _ _ _ _ (sc_arrow_right pi1) pi2) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. clear. rewrite app_assoc. cbn. intros pi' Hs.
      exists (sc_arrow_right pi'). cbn. lia.
    * destruct (IH2 _ _ _ _ _ pi1 pi2_2) as [pi Hs]; [ cbn; lia | ].
      revert pi Hs. rewrite app_nil_r. intros pi Hs.
      destruct (IH3 _ _ _ _ pi2_1 pi) as [pi' Hs']; [ cbn; unfold St in *; cbn in *; lia | ].
      revert pi Hs pi' Hs'. list_simpl. intros pi Hs pi' Hs'.
      destruct (sc_var_right_wk_gen l0 pi') as [pi'' Hs''].
      exists pi''. lia.
  + destruct (sc_var_left_wk_gen l pi2) as [pi2' <-]. exists pi2'. lia.
  + cbn in IH1, IH2. cbn. remember (St (var x)) as e eqn:He. destruct pi2; destr_eq He; subst.
    * exists sc_omega_right. cbn. lia.
    * destruct (IH2 _ _ _ _ _ (@sc_var_right _ _ _ l pi1_1 pi1_2) pi2_1) as [pi_1 Hs1]; [ cbn; lia | ].
      destruct (IH2 _ _ _ _ _ (@sc_var_right _ _ _ l pi1_1 pi1_2) pi2_2) as [pi_2 Hs2]; [ cbn; lia | ].
      exists (sc_inter_right pi_1 pi_2). cbn in *. lia.
    * destruct (IH2 _ _ _ _ _ (@sc_var_right _ _ _ l pi1_1 pi1_2) pi2) as [pi' Hs]; [ cbn; lia | ].
      revert pi' Hs. clear. rewrite app_assoc. cbn. intros pi' Hs.
      exists (sc_arrow_right pi'). cbn. lia.
    * exists (sc_var_right pi1_1 pi1_2). cbn. lia.
- intros x b p l pi1 pi2 ->.
  remember (l · b) as l0 eqn:Heql0. remember (var x) as d eqn:Heqd. destruct pi2; destr_eq Heqd; subst.
  + destruct (IH3 _ _ _ _ pi1 pi2) as [pi Hspi]; [ cbn; lia | ].
    exists (sc_inter_left1 pi). cbn. lia.
  + destruct (IH3 _ _ _ _ pi1 pi2) as [pi Hspi]; [ cbn; lia | ].
    exists (sc_inter_left2 pi). cbn. lia.
  + decomp_list_eq Heql0; subst.
    * destruct (IH3 _ _ _ _ pi1 pi2_2) as [pi Hspi]; [ cbn; lia | ].
      exists (sc_arrow_left pi2_1 pi). cbn. lia.
    * destruct (IH2 _ _ _ _ _ pi1 pi2_1) as [pi Hspi]; [ cbn; lia | ].
      exists (sc_var_right pi pi2_2). cbn in *. lia.
  + exists sc_var_left. cbn. lia.
  + exists (sc_var_right pi2_1 pi2_2). cbn. lia.
Qed.

Lemma sc_sub_subst a b p d l1 l2 : a ❘ ⊦ b -> p ❘ l1 ++ b :: l2 ⊦ d -> p ❘ l1 ++ a :: l2 ⊦ d.
Proof. intros pi1 pi2. apply (fst (fst (sc_sub_trans_rules _)) _ _ _ _ _ _ pi1 pi2 eq_refl). Qed.

Lemma sc_sub_trans p b c l1 l2 : p ❘ l1 ⊦ b -> b ❘ l2 ⊦ c -> p ❘ l1 ++ l2 ⊦ c.
Proof. intros pi1 pi2. apply (snd (fst (sc_sub_trans_rules _)) _ _ _ _ _ pi1 pi2 eq_refl). Qed.

Instance sc_sub_preorder : PreOrder sc_sub_nil.
Proof. split; intro a; [ exact (sc_identity _) | intros b c H1 H2; exact (sc_sub_trans H1 H2) ]. Qed.

Instance sc_sub_equivalence : Equivalence sc_sub_equiv.
Proof.
split.
- intro. split; reflexivity.
- intros a b []. split; assumption.
- intros a b c [] []. split; etransitivity; eassumption.
Qed.

Lemma sc_None_left_rev a l b l' : None ❘ l ⊦ a -> b ❘ l' ⊦ a.
Proof. intro pi. apply (sc_None_left_rev_weight pi b l'). Qed.

Lemma sc_arrow_right_rev a b c l : c ❘ l ⊦ a → b -> c ❘ l · a ⊦ b.
Proof. intro pi. apply (sc_sub_trans pi). repeat constructor; apply sc_identity. Qed.

Lemma sc_arrow_left_rev a b c d l : a → b ❘ c :: l ⊦ d -> ((c ❘ ⊦ a) + (None ❘ nil ⊦ d)) * (b ❘ l ⊦ d).
Proof.
intro pi. remember (St (a → b)) as e eqn:Heqe. remember (c :: l) as l' eqn:Heql'.
revert a b Heqe c l Heql'. induction_sc_sub pi p x a' b' c' d' l pi1 pi2 IH1 IH2;
  intros a b Heqe c l0 Heql0; destr_eq Heqe; destr_eq Heql0; subst;
  (try now constructor; apply (IH1 _ _ eq_refl _ _ eq_refl)); try now auto.
- destruct (IH1 _ _ eq_refl _ _ eq_refl) as [[Hl1 | Hl1] Hr1],
           (IH2 _ _ eq_refl _ _ eq_refl) as [[Hl2 | Hl2] Hr2].
  + split; [ left | apply sc_inter_right ]; assumption.
  + split; [ left | apply sc_inter_right ]; assumption.
  + split; [ left | apply sc_inter_right ]; assumption.
  + split; [ right | ]; apply sc_inter_right; assumption.
- destruct (IH1 _ _ eq_refl _ _ eq_refl) as [[Hl | Hl] Hr].
  + split; [ left | apply sc_arrow_right ]; assumption.
  + split; [ right | ]; apply sc_arrow_right, (sc_None_left_rev _ _ Hl).
- split.
  + left. apply (sc_None_left_rev _ _ pi1).
  + apply (sc_var_right_wk_gen _ pi2).
Qed.


(** * Equivalence with BCD *)

Definition sc_ax := [fun x => (Ω → var x, var x); fun x => (var x, Ω → var x)].
Notation "a ⩽ b " := (@bcd_sub sc_ax a b) (at level 70).

Lemma bcd_sc_list (x : Atom) l : x ⩽ ⟦l, x⟧.
Proof.
induction l as [ | y l IHl ] using rev_rect; cbn.
- apply bcd_identity.
- rewrite list2form_last. etransitivity; [ apply IHl | ].
  apply bcd_arrow_list.
  transitivity (Ω → x).
  + apply (@bcd_axiom sc_ax _ _ (inT_cons _ _ _ (inT_eq _ _))).
  + apply bcd_arrow; [ apply bcd_omega_right | apply bcd_identity ].
Qed.

Lemma sc_bcd p l b : p ❘ l ⊦ b -> Fm p ⩽ ⟦l, b⟧.
Proof.
intro pi. induction_sc_sub pi p x a' b' c' d' l pi1 pi2 IH1 IH2.
- induction l as [ | ? l IHl ] using rev_rect; cbn.
  + apply bcd_omega_right.
  + rewrite list2form_last. etransitivity; [ apply IHl | ].
    apply bcd_arrow_list.
    apply bcd_arrow_omega_distr.
- etransitivity; [ | eassumption ]. apply bcd_inter_left1.
- etransitivity; [ | eassumption ]. apply bcd_inter_left2.
- apply bcd_arrow_inter_list; assumption.
- apply bcd_arrow; assumption.
- rewrite list2form_last in IH1. assumption.
- apply bcd_sc_list.
- cbn in *. transitivity x.
  + transitivity (Ω → x).
    * apply bcd_arrow; assumption.
    * apply (@bcd_axiom sc_ax _ _ (inT_eq _ _)).
  + apply bcd_sc_list.
Qed.

(* Proposition 31 *)
Theorem sc_bcd_equiv a b : a ⩽ b <=> a ❘ ⊦ b.
Proof.
split; intro H.
- induction H; try (repeat constructor; try apply sc_identity; fail).
  + etransitivity; eassumption.
  + apply sc_inter_right; now constructor.
  + constructor. constructor; assumption.
  + inversion i as [ | ii ]; [ | inversion ii as [ | iii ]; [ | inversion iii ] ]; subst; apply eq_scott.
- change b with ⟦[], b⟧. change a with (Fm (Some a)).
  apply sc_bcd. assumption.
Qed.


(** * Beta Condition *)

(* Lemma 32 *)
Lemma sc_beta_list s a l b : ForallT (fun z => fst z <> nil) s -> form_recomposition s ❘ a :: l ⊦ b ->
  { s0 & sublistT s0 s & (ForallT (sc_sub nil a) (arrow_tl s0)
                       * (form_recomposition (arrow_hd s0) ❘ l ⊦ b))%type }.
Proof.
intros Hnil pi.
remember (St (form_recomposition s)) as s0 eqn:Hs0.
remember (a :: l) as l0 eqn:Hl0. revert s Hs0 a l Hl0 Hnil.
induction_sc_sub pi p x a' b' c' d' l' pi1 pi2 IH1 IH2; intros s Hs0 a l Hl0 Hnil; destr_eq Hl0; subst.
- exists nil; [ apply sublistT_nil_l | split ]; cbn; constructor.
- destruct s as [ | (t, h) [ | p s ] ]; inversion Hs0.
  + destruct t; inversion H0.
  + inversion Hnil. subst. cbn in H2. destruct t as [ | p' t ]; [ contradiction H2; reflexivity | ].
    apply sc_arrow_left_rev in pi1 as [[pi1 | pi1] pi2].
    * exists [(p' :: t, h)]; [ | split; [ | assumption ] ].
      -- constructor. apply sublistT_nil_l.
      -- specialize (IH1 [(p' :: t, h)] eq_refl _ _ eq_refl) as [s0 H1' [H2' H3']];
           [ ForallT_solve | ].
         repeat constructor. assumption.
    * exists nil; [ | split ].
      -- apply sublistT_nil_l.
      -- repeat constructor.
      -- apply (sc_None_left_rev _ _ pi1).
- destruct s as [ | (t0, h0) [ | (t, h) s ] ]; inversion Hs0.
  + destruct t0; inversion H0.
  + assert (St a' = form_recomposition ((t, h) :: s)) as H by (f_equal; assumption).
    specialize (IH1 ((t, h) :: s) H _ _ eq_refl) as [s0 H1' [H2' H3']]; [ ForallT_solve | ].
    exists s0; constructor; assumption.
- destruct (IH1 _ eq_refl _ _ eq_refl Hnil) as [s1 H1a [H1b H1c]].
  destruct (IH2 _ eq_refl _ _ eq_refl Hnil) as [s2 H2a [H2b H2c]].
  clear - H1a H1b H1c H2a H2b H2c.
  enough
    ({s0 & ((sublistT s0 s) * (sublistT s1 s0) * (sublistT s2 s0))%type & ForallT (sc_sub nil a) (arrow_tl s0) })
    as [s0 [[H0 H1] H2]].
  { exists s0; [ assumption | split; [ assumption | ] ].
    clear - H1c H2c H1 H2.
    enough (forall s s', sublistT s' s ->
              form_recomposition (arrow_hd s) ❘ ⊦ form_recomposition (arrow_hd s')) as Hs.
    { apply sc_inter_right.
      - rewrite <- (app_nil_l _). refine (sc_sub_trans _ H1c).
        apply Hs. assumption.
      - rewrite <- (app_nil_l _). refine (sc_sub_trans _ H2c).
        apply Hs. assumption. }
    clear. intros s s' Hs. induction Hs; [ reflexivity | | ].
    - destruct a as (t, h). destruct l1 as [|p1 l1]; cbn.
      + destruct l2 as [|p2 l2]; [ | apply sc_inter_left1 ]; apply sc_identity.
      + apply sc_inter_right.
        * destruct l2 as [|p2 l2]; [ | apply sc_inter_left1 ]; apply sc_identity.
        * destruct l2 as [|p2 l2].
          -- exfalso. inversion Hs.
          -- apply sc_inter_left2. assumption.
    - destruct a as (t, h). destruct l2 as [|p l2]; cbn.
      + etransitivity; [ | apply IHHs ]. constructor.
      + apply sc_inter_left2. assumption. }
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
- list_simpl in pi1.
  destruct (IH1 _ eq_refl _ _ eq_refl Hnil) as [s0 H1 [H2 H3]].
  exists s0; [ | split; [ | apply sc_arrow_right ] ]; assumption.
- exfalso.
  destruct s as [ | ([ | ? t ], h) [ | p s ] ]; destr_eq Hs0.
  inversion_clear Hnil. contradiction.
- destruct s as [ | ([ | c t ], h) [ | p s ] ]; destr_eq Hs0. subst.
  exists [(c :: t, h)]; [ | split ].
  + reflexivity.
  + repeat constructor.
    apply (sc_None_left_rev _ _ pi1).
  + apply (sc_var_right_wk_gen _ pi2).
Qed.

Lemma sc_beta : beta_condition sc_sub_nil.
Proof. intros s a b Hnil pi%sc_arrow_right_rev. apply (sc_beta_list Hnil pi). Qed.


(** * Eta Condition *)

Lemma sc_eta : eta_condition sc_sub_equiv.
Proof.
apply weaker_eta_condition.
- split; apply sc_sub_equivalence.
- intros ? ? ? ? [] []. repeat constructor; assumption.
- intros. split; apply is_sc, iis1.inter_assoc.
- intros. split; apply is_sc, iis1.inter_unit_l.
- intros. split; apply is_sc, iis1.inter_unit_r.
- intros ? ? ? []. repeat constructor; try apply sc_identity; assumption.
- intro. split; apply is_sc, iis1.arrow_omega_distr.
- intros. split; apply is_sc, iis1.arrow_inter_distr.
- intro x. exists [([Ω], x)].
  + constructor; [ | constructor ]. intros [=].
  + symmetry. apply eq_scott.
Qed.
