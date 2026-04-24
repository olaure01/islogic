(* System ∩IS₁ʳ for Intersection Subtyping *)

From Stdlib Require Import Wf_nat PeanoNat Lia CMorphisms Relations Bool.
From OLlibs Require Import Logic_Datatypes_more Bool_more List_more dectype.
From InterPT Require Export iis1_prop.
Import LogicNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.

Inductive cclos_refl_trans_1n A (R : crelation A) : crelation A :=
| crt1n_refl a : cclos_refl_trans_1n R a a
| crt1n_trans (a b c:A) : R a b -> cclos_refl_trans_1n R b c -> cclos_refl_trans_1n R a c.


(** * System ∩IS₁ʳ *)

Implicit Type x : Atom.

Reserved Notation "a ❘ l ⊦° b" (at level 65, l at next level, b at next level).
Reserved Notation "a ❘ ⊦° b" (at level 65, b at next level).
Inductive sub_rev : list form -> crelation form :=
| rev_identity x : x ❘ ⊦° x
| rev_omega_right a l : a ❘ l ⊦° Ω
| rev_inter_left1 b a x l : a ❘ l ⊦° x -> a ∩ b ❘ l ⊦° x
| rev_inter_left2 b a x l : a ❘ l ⊦° x -> b ∩ a ❘ l ⊦° x
| rev_inter_right a b c l : c ❘ l ⊦° a -> c ❘ l ⊦° b -> c ❘ l ⊦° a ∩ b
| rev_arrow_left a b c x l : c ❘ ⊦° a -> b ❘ l ⊦° x -> a → b ❘ c :: l ⊦° x
| rev_arrow_right a b c l : c ❘ l · a ⊦° b -> c ❘ l ⊦° a → b
where "a ❘ l ⊦° b" := (sub_rev l a b)
  and "a ❘ ⊦° b" := (sub_rev nil a b).
Hint Constructors sub_rev : core.
Arguments rev_identity {_}.
Arguments rev_omega_right {_ _}.
Arguments rev_inter_left1 [_ _ _ _].
Arguments rev_inter_left2 [_ _ _ _].
Arguments rev_arrow_right [_ _ _ _].

Lemma rev_inter_left1_gen b a c l : a ❘ l ⊦° c -> a ∩ b ❘ l ⊦° c.
Proof. intro H. induction H; now repeat constructor. Qed.

Lemma rev_inter_left2_gen b a c l : a ❘ l ⊦° c -> b ∩ a ❘ l ⊦° c.
Proof. intro H. induction H; now repeat constructor. Qed.

Lemma rev_arrow_left_gen a b c d l : c ❘ ⊦° a -> b ❘ l ⊦° d -> a → b ❘ c :: l ⊦° d.
Proof. intros H1 H2. induction H2; now repeat constructor. Qed.

Lemma rev_identity_gen a : a ❘ ⊦° a.
Proof.
induction a as [ x | | a1 IH1 a2 IH2 | a1 IH1 a2 IH2 ]; constructor.
- apply rev_inter_left1_gen; assumption.
- apply rev_inter_left2_gen; assumption.
- apply rev_arrow_left_gen; assumption.
Qed.

Theorem iis1_iis1r l a b : a ❘ l ⊦ b <=> a ❘ l ⊦° b.
Proof.
split; intro H; induction H; try now constructor.
- apply rev_identity_gen.
- apply rev_inter_left1_gen. assumption.
- apply rev_inter_left2_gen. assumption.
- apply rev_arrow_left_gen; assumption.
Qed.

Lemma rev_scut a b c d l1 l2 : a ❘ ⊦° b -> c ❘ l1 ++ b :: l2 ⊦° d -> c ❘ l1 ++ a :: l2 ⊦° d.
Proof. intros pi1%iis1_iis1r pi2%iis1_iis1r. apply iis1_iis1r, (@sub_subst _ b); assumption. Qed.

Lemma rev_tcut a b c l1 l2 : a ❘ l1 ⊦° b -> b ❘ l2 ⊦° c -> a ❘ l1 ++ l2 ⊦° c.
Proof. intros pi1%iis1_iis1r pi2%iis1_iis1r. apply iis1_iis1r, (@sub_trans _ b); assumption. Qed.


Lemma rev_inter_right_equiv a b c l : c ❘ l ⊦° a ∩ b <=> (c ❘ l ⊦° a) * (c ❘ l ⊦° b).
Proof.
split; [ | intros []; now constructor ].
intro pi. inversion_clear pi. split; assumption.
Qed.

Lemma rev_arrow_right_equiv a b c l : c ❘ l ⊦° a → b <=> c ❘ l · a ⊦° b.
Proof.
split; [ | intros; now constructor ].
intro pi. inversion_clear pi. assumption.
Qed.

Lemma rev_identity_equiv_list (x y : Atom) l : x ❘ l ⊦° y <=> (y = x) * (l = nil).
Proof. split; [ intro pi; inversion pi; split; reflexivity | intros [-> ->]; constructor ]. Qed.

Lemma rev_identity_equiv (x y : Atom) : x ❘ ⊦° y <=> @eq form_dectype y x.
Proof.
now split; [ intros [H _]%rev_identity_equiv_list; f_equal | intros [= ->]; apply rev_identity_equiv_list ].
Qed.

Lemma rev_inter_left_var_equiv a b x l : a ∩ b ❘ l ⊦° x <=> (a ❘ l ⊦° x) + (b ❘ l ⊦° x).
Proof.
split; [ | intros []; now constructor ].
intro pi. inversion_clear pi; [ left | right ]; assumption.
Qed.


Lemma rev_arrow_left_var_equiv_list a b x l : a → b ❘ l ⊦° x <=> (hd Ω l ❘ ⊦° a) * (b ❘ tl l ⊦° x) * (l <> nil).
Proof.
split.
- intro pi. inversion_clear pi. cbn. split; [split; assumption | discriminate ].
- intros [[] Hl]. destruct l as [ | h t ]; [ contradiction Hl; reflexivity | ]. constructor; assumption.
Qed.

Lemma rev_arrow_left_var_equiv a b c x l : a → b ❘ c :: l ⊦° x <=> (c ❘ ⊦° a) * (b ❘ l ⊦°x).
Proof.
rewrite rev_arrow_left_var_equiv_list. cbn.
split; intros [p1 p2]; try destruct p1 as [? ?]; repeat split; auto. discriminate.
Qed.

Lemma rev_omega_left_equiv l a : Ω ❘ l ⊦° a <=> form_decomposition a = [].
Proof.
split.
- intro pi. remember Ω as b eqn:Hb.
  revert Hb. induction_sub pi a' b' c' d' l pi1 pi2 IH1 IH2; intros Hb; destr_eq Hb; cbn.
  + reflexivity.
  + now rewrite IH1, IH2.
  + destruct (form_decomposition b').
    * reflexivity.
    * apply IH1 in Hb. discriminate Hb.
- induction a in l |- *; cbn; intro Ha.
  + discriminate Ha.
  + constructor.
  + apply app_eq_nil in Ha as [Ha1%(IHa1 l) Ha2%(IHa2 l)].
    now constructor.
  + destruct (form_decomposition a2); [ | discriminate Ha ].
    constructor. apply IHa2. reflexivity.
Qed.

(*
Lemma rev_var_left_equiv x l a : x ❘ l ⊦° a <=> Forall (eq ([], x)) (form_decomposition a).

Lemma rev_arrow_left_equiv_list a b c l :
    a → b ❘ l ⊦° c
<=> ForallT (fun '(t, h) => ((t <> nil) * (hd Ω t ❘ ⊦° a) * (b ❘ tl l ⊦° c))%type) (form_decomposition ⟦l, c⟧).
*)


(** * Proof Search Algorithm *)

(* specification of the algorithm *)
Definition is_spec F l a b :=
match b, a, l with
| Ω, _, _ => true
| e ∩ f, _, _ => F l a e && F l a f
| e → f, _, _ => F (l · e) a f
| var x, var y, nil => form_dectype.(eqb) x y
| _, c ∩ d, _ => F l c b || F l d b
| _, c → d, h :: t => F nil h c && F t d b
| _, _, _ => false
end.

(* trel s1 s2 := s1 may appear as premise of a rule with conclusion s2 *)
Variant ctrel : crelation (list form * form * form) :=
| trel_inter_r_1 l a e f : ctrel (l, a, e) (l, a, e ∩ f)
| trel_inter_r_2 l a e f : ctrel (l, a, f) (l, a, e ∩ f)
| trel_arrow_r l a e f : ctrel (l · e, a, f) (l, a, e → f)
| trel_inter_l_1 l c d b : ctrel (l, c, b) (l, c ∩ d, b)
| trel_inter_l_2 l c d b : ctrel (l, d, b) (l, c ∩ d, b)
| trel_arrow_l_1 h l c d b : ctrel (nil, h, c) (h :: l, c → d, b)
| trel_arrow_l_2 h l c d b : ctrel (l, d, b) (h :: l, c → d, b).
Infix "≪*" := (cclos_refl_trans_1n ctrel) (at level 70).
Definition trel s1 s2 : Prop := inhabited (ctrel s1 s2).
Infix "≪" := trel (at level 70).

Lemma trel_wf : well_founded trel.
Proof.
apply (well_founded_lt_compat _ (fun '(l, a, b) => list_sum (map fsize (a :: l · b)))).
intros ? ? [[]]; simpl map; simpl list_sum; rewrite !map_app, !list_sum_app; cbn; lia.
Qed.

(* any fixpoint of the specification propagates correctness *)
Lemma is_spec_correct F (Fspec : forall l a b, F l a b = is_spec F l a b) l a b :
  (forall l' a' b', (l', a', b') ≪ (l, a, b) -> reflectT (a' ❘ l' ⊦° b') (F l' a' b')) ->
  reflectT (a ❘ l ⊦° b) (F l a b).
Proof.
intro IH. rewrite Fspec.
destruct b as [ x | | e f | e f ].
- destruct a as [ y | | c d | c d ].
  + destruct l.
    * apply (reflectT_iffT_compat (rev_identity_equiv y x) eq_refl).
      apply reflectT_reflect, eq_dt_reflect.
    * constructor. intro pi. inversion pi.
  + constructor. intros []%iis1_iis1r%not_omega_left_atom_right.
  + cbn. rewrite rev_inter_left_var_equiv.
    apply or_orb_reflectT; apply IH; constructor; constructor.
  + destruct l.
    * constructor. intro pi. inversion pi.
    * cbn. rewrite rev_arrow_left_var_equiv.
      apply and_andb_reflectT; apply IH; constructor; constructor.
- constructor. constructor.
- cbn. rewrite rev_inter_right_equiv.
  apply and_andb_reflectT; apply IH; constructor; constructor.
- cbn. rewrite rev_arrow_right_equiv.
  apply IH. constructor. constructor.
Qed.

(* specification constrained to trel (which happens to be well founded) *)
Definition is_spec_trel '(l, a ,b) : (forall s, s ≪ (l, a, b) -> bool) -> bool :=
match b, a, l with
| Ω, _, _              => fun _ => true
| e ∩ f, _, _          => fun F => F (l, a, e) ltac:(do 2 constructor) && F (l, a, f) ltac:(do 2 constructor)
| e → f, _, _          => fun F => F (l · e, a, f) ltac:(do 2 constructor)
| var x, c ∩ d, _      => fun F =>    F (l, c, var x) ltac:(do 2 constructor)
                                   || F (l, d, var x) ltac:(do 2 constructor)
| var x, c → d, h :: t => fun F =>    F (nil, h, c) ltac:(do 2 constructor)
                                   && F (t, d, var x) ltac:(do 2 constructor)
| var x, var y, nil    => fun _ => form_dectype.(eqb) x y
| var _, _, _          => fun _ => false
end.

Lemma is_spec_trel_ext z (f g : forall y, y ≪ z -> bool) (Hext : forall y p, f y p = g y p) :
  is_spec_trel f = is_spec_trel g.
Proof. now destruct z as [[[] []] []]; simpl; rewrite ?Hext. Qed.

(* algorithm as a fixpoint of the well founded specification *)
Definition is_b l a b : bool := Fix trel_wf _ is_spec_trel (l, a , b).

(* correctness *)
Lemma is_b_correct l a b : reflectT (a ❘ l ⊦° b) (is_b l a b).
Proof.
remember (l, a, b) as s eqn:Hs.
revert l a b Hs. induction s as [s IH] using (well_founded_induction_type trel_wf). intros l a b ->.
apply is_spec_correct.
- intros l' a' b'. unfold is_b. rewrite (Fix_eq trel_wf _ _ is_spec_trel_ext).
  now destruct b', a', l'.
- intros ? ? ? HR. apply (IH _ HR _ _ _ eq_refl).
Qed.


(** ** Reachable subsequents *)

(* (sub)sequents visited by the algorithm from b | <= d are of the form a | sub_ctx a c <= c
    with either a subformula of b and c subformula of d, both positive subformulas
             or a subformula of d and c subformula of b, both negative subformulas *)
Lemma trel_subsequents b d l a c : (l, a, c) ≪* ([], b, d) ->
  ({'(s, t) : subformula a b * subformula c d & sub_coh (length l) s t
                                              & (l = sub_ctx s t) * (subformula_sign t = true) }
 + {'(s, t) : subformula a d * subformula c b & sub_coh (length l) s t
                                              & (l = sub_ctx s t) * (subformula_sign t = false) })%type.
Proof.
remember (l, a, c) as S1 eqn:H1. remember ([], b, d) as S2 eqn:H2.
intro HR. induction HR as [x | [[l1 a1] c1] [[l2 a2] c2] [[l3 a3] c3] [] HRt IH] in a, b, c, d, l, H1, H2 |- *;
  [ subst x | injection H1 as [= <- -> ->] .. ]; injection H2 as [= -> -> ->].
- left. exists (sf_id b, sf_id d); [ | split ]; constructor.
- destruct (IH _ _ _ _ _ eq_refl eq_refl) as [[(s, t) IHc [IHs IHu]] | [(s, t) IHc [IHs IHu]]];
    [ left | right ]; (exists (s, sf_interl t); [ | split]); now try constructor.
- destruct (IH _ _ _ _ _ eq_refl eq_refl) as [[(s, t) IHc [IHs IHu]] | [(s, t) IHc [IHs IHu]]];
    [ left | right ]; (exists (s, sf_interr t); [ | split]); now try constructor.
- destruct (IH _ _ _ _ _ eq_refl eq_refl) as [[(s, t) IHc [IHs IHu]] | [(s, t) IHc [IHs IHu]]];
    [ left | right ].
  + exists (s, sf_arrowr t); [ | split ]; [ | subst l0 | assumption ].
    * rewrite length_app. cbn. replace (length l0 + 1) with (S (length l0)) by lia.
      now constructor.
    * assert (Hlen0 := sub_coh_correct IHc). clear - Hlen0.
      unfold sub_ctx, sub_ctx_sf in *. cbn. rewrite <- !skipn_map, map_app. cbn.
      remember (length (sub_ctx_full s)) as k eqn:Hk. clear a b s Hk.
      remember (sub_ctx_full t) as l eqn:Hl. clear c t Hl.
      assert (k <= length l) as Hlen by lia. clear Hlen0.
      induction l in k, Hlen |- *; destruct k as [|k]; cbn in Hlen; try reflexivity.
      -- exfalso. lia.
      -- simpl skipn. apply IHl. lia.
  + exists (s, sf_arrowr t); [ | split ]; [ | subst l0 | assumption ].
    * rewrite length_app. cbn. replace (length l0 + 1) with (S (length l0)) by lia.
      now constructor.
    * assert (Hlen0 := sub_coh_correct IHc). clear - Hlen0.
      unfold sub_ctx, sub_ctx_sf in *. cbn. rewrite <- !skipn_map, map_app. cbn.
      remember (length (sub_ctx_full s)) as k eqn:Hk. clear a d s Hk.
      remember (sub_ctx_full t) as l eqn:Hl. clear c t Hl.
      assert (k <= length l) as Hlen by lia. clear Hlen0.
      induction l in k, Hlen |- *; destruct k as [|k]; cbn in Hlen; try reflexivity.
      -- exfalso. lia.
      -- simpl skipn. apply IHl. lia.
- destruct (IH _ _ _ _ _ eq_refl eq_refl) as [[(s, t) IHc [IHs IHu]] | [(s, t) IHc [IHs IHu]]];
    [ left | right ]; (exists (sf_interl s, t); [ | split]); now try constructor.
- destruct (IH _ _ _ _ _ eq_refl eq_refl) as [[(s, t) IHc [IHs IHu]] | [(s, t) IHc [IHs IHu]]];
    [ left | right ]; (exists (sf_interr s, t); [ | split]); now try constructor.
- destruct (IH _ _ _ _ _ eq_refl eq_refl) as [[(s, t) IHc [IHs IHu]] | [(s, t) IHc [IHs IHu]]];
    [ right | left ].
  + assert (a = projT1 (hd (existT _ d (sf_id d)) (sub_ctx_sf s t))) as ->.
    { clear - IHc IHs. apply sub_coh_correct in IHc.
      unfold sub_ctx_sf. unfold sub_ctx, sub_ctx_sf in IHs. remember (sub_ctx_full t) as L eqn:HL. clear HL.
      cbn in IHc. remember (length (sub_ctx_full s)) as k eqn:Hk. clear Hk.
      assert (k < length L) as HL by lia. clear IHc.
      induction k as [ | k IHk ] in L, HL, IHs |- *; (destruct L as [ | A L ]; [ exfalso; cbn in HL; lia | ]).
      - cbn in *. injection IHs as [= ->]. reflexivity.
      - cbn in *. rewrite <- IHk; [ reflexivity | assumption | lia ]. }
    exists (projT2 (hd (existT _ d (sf_id d)) (sub_ctx_sf s t)), sf_arrowl s); [ | split ].
    * clear - IHc. cbn in *. econstructor. eassumption.
    * clear. unfold sub_ctx, sub_ctx_sf. rewrite <- skipn_map. cbn.
      symmetry. apply skipn_nil.
    * cbn. rewrite (sub_coh_sign IHc), IHu. reflexivity.
  + assert (a = projT1 (hd (existT _ b (sf_id b)) (sub_ctx_sf s t))) as ->.
    { clear - IHc IHs. apply sub_coh_correct in IHc.
      unfold sub_ctx_sf. unfold sub_ctx, sub_ctx_sf in IHs. remember (sub_ctx_full t) as L eqn:HL. clear HL.
      cbn in IHc. remember (length (sub_ctx_full s)) as k eqn:Hk. clear Hk.
      assert (k < length L) as HL by lia. clear IHc.
      induction k as [ | k IHk ] in L, HL, IHs |- *; (destruct L as [ | A L ]; [ exfalso; cbn in HL; lia | ]).
      - cbn in *. injection IHs as [= ->]. reflexivity.
      - cbn in *. rewrite <- IHk; [ reflexivity | assumption | lia ]. }
    exists (projT2 (hd (existT _ b (sf_id b)) (sub_ctx_sf s t)), sf_arrowl s); [ | split ].
    * clear - IHc. cbn in *. econstructor. eassumption.
    * clear. unfold sub_ctx, sub_ctx_sf. rewrite <- skipn_map. cbn.
      symmetry. apply skipn_nil.
    * cbn. rewrite (sub_coh_sign IHc), IHu. reflexivity.
- destruct (IH _ _ _ _ _ eq_refl eq_refl) as [[(s, t) IHc [IHs IHu]] | [(s, t) IHc [IHs IHu]]];
    [ left | right ].
  + exists (sf_arrowr s, t); [ | split ].
    * constructor. replace (S (length l0)) with (length (h :: l0)) by (cbn; lia).
      assumption.
    * unfold sub_ctx, sub_ctx_sf in IHs. rewrite <- skipn_map in IHs.
      unfold sub_ctx, sub_ctx_sf. rewrite <- skipn_map.
      cbn. rewrite length_app. cbn.
      replace (length (sub_ctx_full s) + 1) with (1 + (length (sub_ctx_full s))) by lia.
      rewrite <- skipn_skipn, <- IHs. reflexivity.
    * assumption.
  + exists (sf_arrowr s, t); [ | split ].
    * constructor. replace (S (length l0)) with (length (h :: l0)) by (cbn; lia).
      assumption.
    * unfold sub_ctx, sub_ctx_sf in IHs. rewrite <- skipn_map in IHs.
      unfold sub_ctx, sub_ctx_sf. rewrite <- skipn_map.
      cbn. rewrite length_app. cbn.
      replace (length (sub_ctx_full s) + 1) with (1 + (length (sub_ctx_full s))) by lia.
      rewrite <- skipn_skipn, <- IHs. reflexivity.
    * assumption.
Qed.

(* given subformulas a of b and c of d, a | sub_ctx a c <= c can be reached by the algorithm from
      b | <= d if a and c positive subformulas
   or d | <= b if a and c negative subformulas *)
Lemma subsequents_trel a b c d n (s : subformula a b) (t : subformula c d) (ch : sub_coh n s t) :
  (sub_ctx s t, a, c) ≪* if subformula_sign t then ([], b, d) else ([], d, b).
Proof.
induction ch; cbn.
- constructor.
- destruct (subformula_sign t); refine (crt1n_trans _ _ IHch); constructor.
- destruct (subformula_sign t); refine (crt1n_trans _ _ IHch); constructor.
- destruct (subformula_sign t); refine (crt1n_trans _ _ IHch); constructor.
- destruct (subformula_sign t); refine (crt1n_trans _ _ IHch); constructor.
- destruct (subformula_sign t); refine (crt1n_trans _ _ IHch).
  + unfold sub_ctx, sub_ctx_sf. cbn.
    rewrite skipn_app, map_app.
    apply sub_coh_correct in ch. assert (length (sub_ctx_full s) - length (sub_ctx_full t) = 0) as -> by lia.
    constructor.
  + unfold sub_ctx, sub_ctx_sf. cbn.
    rewrite skipn_app, map_app.
    apply sub_coh_correct in ch. assert (length (sub_ctx_full s) - length (sub_ctx_full t) = 0) as -> by lia.
    constructor.
- remember (subformula_sign t) as bb eqn:Hbb. destruct bb; cbn.
  + refine (crt1n_trans _ _ IHch).
    rewrite length_app. cbn.
    replace (length (sub_ctx_full s) + 1) with (S (length (sub_ctx_full s))) by lia.
    replace (S (length (sub_ctx_full s))) with (1 + length (sub_ctx_full s)) by lia.
    rewrite <- skipn_skipn.
    unfold sub_ctx, sub_ctx_sf.
    remember (skipn (length (sub_ctx_full s)) (sub_ctx_full t)) as L eqn:HL.
    apply sub_coh_correct in ch.
    destruct L as [ | A L ].
    * exfalso.
      assert (Hlen := f_equal (@length _) HL).
      rewrite length_skipn in Hlen. cbn in Hlen. lia.
    * constructor.
  + refine (crt1n_trans _ _ IHch).
    rewrite length_app. cbn.
    replace (length (sub_ctx_full s) + 1) with (S (length (sub_ctx_full s))) by lia.
    replace (S (length (sub_ctx_full s))) with (1 + length (sub_ctx_full s)) by lia.
    rewrite <- skipn_skipn.
    unfold sub_ctx, sub_ctx_sf.
    remember (skipn (length (sub_ctx_full s)) (sub_ctx_full t)) as L eqn:HL.
    apply sub_coh_correct in ch.
    destruct L as [ | A L ].
    * exfalso.
      assert (Hlen := f_equal (@length _) HL).
      rewrite length_skipn in Hlen. cbn in Hlen. lia.
    * constructor.
- rewrite (sub_coh_sign ch).
  remember (subformula_sign t) as bb eqn:Hbb. destruct bb; cbn.
  + refine (crt1n_trans _ _ IHch).
    unfold sub_ctx, sub_ctx_sf.
    apply sub_coh_correct in ch.
    remember (sub_ctx_full t) as L eqn:HL. remember (length (sub_ctx_full s)) as k eqn:Hk.
    assert (Hlen := length_skipn k L).
    rewrite (sub_ctx_full_sub_ctx_full t).
    * destruct (skipn k L) as [ | A L' ].
      -- exfalso. cbn in Hlen. lia.
      -- constructor.
    * rewrite <- HL. rewrite <- (firstn_skipn k L) at 2. apply in_or_app. right.
      destruct (skipn k L) as [ | A L' ].
      -- exfalso. cbn in Hlen. lia.
      -- apply in_eq.
  + refine (crt1n_trans _ _ IHch).
    unfold sub_ctx, sub_ctx_sf.
    apply sub_coh_correct in ch.
    remember (sub_ctx_full t) as L eqn:HL. remember (length (sub_ctx_full s)) as k eqn:Hk.
    assert (Hlen := length_skipn k L).
    rewrite (sub_ctx_full_sub_ctx_full t).
    * destruct (skipn k L) as [ | A L' ].
      -- exfalso. cbn in Hlen. lia.
      -- constructor.
    * rewrite <- HL. rewrite <- (firstn_skipn k L) at 2. apply in_or_app. right.
      destruct (skipn k L) as [ | A L' ].
      -- exfalso. cbn in Hlen. lia.
      -- apply in_eq.
Qed.

(* (sub)sequents reachable from b | <= d are exactly those computed with sub_ctx *)
Lemma trel_subsequents_iffT b d l a c : (l, a, c) ≪* ([], b, d) <=>
   {'(s, t) : subformula a b * subformula c d & sub_coh (length l) s t
                                              & (l = sub_ctx s t) * (subformula_sign t = true) }
 + {'(s, t) : subformula a d * subformula c b & sub_coh (length l) s t
                                              & (l = sub_ctx s t) * (subformula_sign t = false) }.
Proof.
split.
- apply trel_subsequents.
- intros [ [(s, t) Hc [-> Hs]] | [(s, t) Hc [-> Hs]] ].
  + change ([], b, d) with (if true then (@nil form, b, d) else ([], d, b)). rewrite <- Hs.
    apply (subsequents_trel Hc).
  + change ([], b, d) with (if false then (@nil form, d, b) else ([], b, d)). rewrite <- Hs.
    apply (subsequents_trel Hc).
Qed.

Definition trel_subformulas b d l a c : (l, a, c) ≪* ([], b, d) ->
  { a' & subformula a' b } * { c' & subformula c' d }.
Proof.
intros [[(s1, t1) Hc1 [-> Hs1]] | [(s1, t1) Hc1 [-> Hs1]]]%trel_subsequents; split; eexists; eassumption.
Defined.

Lemma trel_subformula_value b d l a c (Hr : (l, a, c) ≪* ([], b, d)) :
  let a' := projT1 (fst (trel_subformulas Hr)) in
  let b' := projT1 (snd (trel_subformulas Hr)) in
  ((a' = a) * (b' = c)) + ((a' = c) * (b' = a)).
Proof.
unfold trel_subformulas.
destruct (trel_subsequents Hr) as [[(s, t) Hc [-> Hs]] | [(s, t) Hc [-> Hs]]]; [ left | right ]; repeat split.
Qed.

Lemma trel_subsequents_inj b d l1 l2 a1 a2 c1 c2
  (Hr1 : (l1, a1, c1) ≪* ([], b, d)) (Hr2 : (l2, a2, c2) ≪* ([], b, d)) :
  trel_subformulas Hr1 = trel_subformulas Hr2 -> (l1, a1, c1) = (l2, a2, c2).
Proof.
unfold trel_subformulas.
destruct (trel_subsequents Hr1) as [[(s1, t1) Hc1 [-> Hs1]] | [(s1, t1) Hc1 [-> Hs1]]],
         (trel_subsequents Hr2) as [[(s2, t2) Hc2 [-> Hs2]] | [(s2, t2) Hc2 [-> Hs2]]];
  cbn; intros [= -> ->%(Eqdep_dec.inj_pair2_eq_dec _ (@eq_dt_dec form_dectype))
                 -> ->%(Eqdep_dec.inj_pair2_eq_dec _ (@eq_dt_dec form_dectype))];
  [ reflexivity | .. | reflexivity ].
all: exfalso; apply sub_coh_sign in Hc1; congruence.
Qed.

(*
Section FixPoint.

  Variable A : Type.
  Variable R : A -> A -> Prop.
  Variable P : A -> Type.
  Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.
  Variable F_ext : forall (x:A) (f g:forall y:A, R y x -> P y),
                     (forall (y:A) (p:R y x), f y p = g y p) -> F f = F g.

  Definition specF h := forall a, h a = @F a (fun y (_ : R y a) => h y).

  Lemma Fix_uniq f (fspec : specF f) g (gspec : specF g) a : Acc R a -> f a = g a.
  Proof using F_ext.
  intro Hacc. destruct Hacc using Acc_inv_dep.
  rewrite fspec, gspec. apply F_ext. assumption.
  Qed.

End FixPoint.
*)
