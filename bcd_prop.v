From Stdlib Require Import Bool Wf_nat Lia CMorphisms.
From OLlibs Require Import Logic_Datatypes_more List_more SubListT.
From InterPT Require Export bcd.
Import LogicNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Use Implicit Types.


Section BCDProp.

Implicit Type x : Atom.

Infix "⩽" := (@bcd_sub nil) (at level 70).
Infix "≡" := (@bcd_equiv nil) (at level 70).

Lemma bcd_form_redecomposition a : form_recomposition (form_decomposition a) ≡ a.
Proof.
apply form_redecomposition.
- split; apply bcd_equivalence.
- intros ? ? ? ? [] []. repeat constructor; assumption.
- intros. split; apply bcd_inter_assoc.
- intros. rewrite bcd_inter_comm. split; apply bcd_inter_unit.
- intros. split; apply bcd_inter_unit.
- intros ? ? ? []. now repeat constructor.
- intro. split; apply bcd_arrow_omega_distr.
- intros. split; apply bcd_arrow_inter_distr.
Qed.

Lemma sub_decomposition a b :
  a ⩽ b <=> form_recomposition (form_decomposition a) ⩽ form_recomposition (form_decomposition b).
Proof.
split.
- intro pi.
  transitivity a; [ apply bcd_form_redecomposition | ].
  transitivity b; [ | apply bcd_form_redecomposition ].
  assumption.
- intro pi.
  transitivity (form_recomposition (form_decomposition a)); [ apply bcd_form_redecomposition | ].
  transitivity (form_recomposition (form_decomposition b)); [ | apply bcd_form_redecomposition ].
  assumption.
Qed.

Lemma bcd_form_hredecomposition a : form_hrecomposition (form_hdecomposition a) ≡ a.
Proof.
apply form_hredecomposition.
- split; apply bcd_equivalence.
- intros ? ? ? ? [] []. repeat constructor; assumption.
- intros. split; apply bcd_inter_assoc.
- intros. rewrite bcd_inter_comm. split; apply bcd_inter_unit.
- intros. split; apply bcd_inter_unit.
- intros ? ? ? []. now repeat constructor.
- intro. split; apply bcd_arrow_omega_distr.
- intros. split; apply bcd_arrow_inter_distr.
- intros ? ? ? []. now repeat constructor.
Qed.

Lemma sub_hdecomposition a b :
  a ⩽ b <=> form_hrecomposition (form_hdecomposition a) ⩽ form_hrecomposition (form_hdecomposition b).
Proof.
split.
- intro pi.
  transitivity a; [ apply bcd_form_hredecomposition | ].
  transitivity b; [ | apply bcd_form_hredecomposition ].
  assumption.
- intro pi.
  transitivity (form_hrecomposition (form_hdecomposition a)); [ apply bcd_form_hredecomposition | ].
  transitivity (form_hrecomposition (form_hdecomposition b)); [ | apply bcd_form_hredecomposition ].
  assumption.
Qed.


(** * Order on formula decompositions *)

Definition form_decomposition_le (s1 s2 : list (list form * Atom)) :=
  ForallT (fun '(t2, h) => { t1 & Forall2T (@bcd_sub nil) t2 t1 & InT (t1, h) s1 }) s2.

Instance form_decomposition_preorder : PreOrder form_decomposition_le.
Proof.
split.
- intro s. apply forall_ForallT. intros (t, h) Hs. exists t; [ | assumption ].
  reflexivity.
- intros s1 s2 s3 T1 T2. apply forall_ForallT. intros (t, h) Hs.
  eapply ForallT_forall in T2; [ | eassumption ]. destruct T2 as [t' Hsub' Hs'].
  eapply ForallT_forall in T1; [ | eassumption ]. destruct T1 as [t'' Hsub'' Hs''].
  exists t''; [ | assumption ].
  etransitivity; eassumption.
Qed.

Lemma form_recomposition_sub s1 s2 : form_decomposition_le s1 s2 -> form_recomposition s1 ⩽ form_recomposition s2.
Proof.
induction s1 as [ | (t1, h1) [ | (t1', h1') s1 ] ] in s2 |- *; cbn; intro Hs.
- destruct s2 as [ | (t2, h2) s2 ].
  + reflexivity.
  + exfalso. eapply ForallT_forall in Hs; [ | apply inT_eq ]. destruct Hs as [? ? []].
- clear IHs1.
  induction s2 as [ | (t2, h2) s2 IHs2 ].
  + apply bcd_omega_right.
  + assert (Hs' := Hs).
    eapply ForallT_forall in Hs'; [ | apply inT_eq ]. destruct Hs' as [t Hsub Hs'].
    inversion Hs'; [ | inversion X ]. injection H as [= <- <-].
    destruct s2 as [ | (t2', h2') s2 ].
    -- cbn. clear - Hsub. induction t2 in t1, Hsub |- *; inversion Hsub.
       ++ reflexivity.
       ++ subst. apply bcd_arrow; [ assumption | ].
          apply IHt2. assumption.
    -- transitivity (⟦t1, h1⟧ ∩ ⟦t1, h1⟧); [ apply bcd_inter_right | ].
       apply bcd_inter.
       ++ cbn. clear - Hsub. induction t2 in t1, Hsub |- *; inversion Hsub.
          ** reflexivity.
          ** subst. apply bcd_arrow; [ assumption | ].
             apply IHt2. assumption.
       ++ apply IHs2.
          etransitivity; [ eassumption | ].
          apply forall_ForallT. intros (t, h) [[= -> ->]|H].
          ** exists t; [ reflexivity | ].
             apply inT_cons, inT_eq.
          ** exists t; [ reflexivity | ].
             apply inT_cons, inT_cons. assumption.
- induction s2 as [ | (t2, h2) s2 IHs2 ].
  + apply bcd_omega_right.
  + assert (Hs' := Hs).
    eapply ForallT_forall in Hs'; [ | apply inT_eq ]. destruct Hs' as [t Hsub Hs'].
    destruct s2 as [ | (t2', h2') s2 ].
    -- cbn. inversion Hs'.
       ++ injection H as [= <- <-].
          etransitivity; [ apply bcd_inter_left1 | ].
          clear - Hsub. induction t2 in t1, Hsub |- *; inversion Hsub.
          ** reflexivity.
          ** subst. apply bcd_arrow; [ assumption | ].
             apply IHt2. assumption.
       ++ etransitivity; [ apply bcd_inter_left2 | ].
          apply (IHs1 [(t2, h2)]).
          apply forall_ForallT. intros (t', h') [[= <- <-]|[]].
          exists t; assumption.
    -- etransitivity; [ apply bcd_inter_right | ].
       apply bcd_inter.
       ++ cbn. inversion Hs'.
          ** injection H as [= <- <-].
             etransitivity; [ apply bcd_inter_left1 | ].
             clear - Hsub. induction t2 in t1, Hsub |- *; inversion Hsub.
             --- reflexivity.
             --- subst. apply bcd_arrow; [ assumption | ].
                 apply IHt2. assumption.
          ** etransitivity; [ apply bcd_inter_left2 | ].
             apply (IHs1 [(t2, h2)]).
             apply forall_ForallT. intros (t', h') [[= <- <-]|[]].
             exists t; assumption.
       ++ apply IHs2.
          etransitivity; [ eassumption | ].
          apply forall_ForallT. intros (t', h') [[= -> ->]|H].
          ** exists t'; [ reflexivity | ].
             apply inT_cons, inT_eq.
          ** exists t'; [ reflexivity | ].
             apply inT_cons, inT_cons. assumption.
Qed.

Lemma sub_form_decomposition a b : a ⩽ b <=> form_decomposition_le (form_decomposition a) (form_decomposition b).
Proof.
split.
2:{ intros H%form_recomposition_sub.
    etransitivity; [ | etransitivity; [ apply H | ] ].
    - apply (bcd_form_redecomposition a).
    - apply (bcd_form_redecomposition b). }
intro pi. induction pi; cbn; [ | | apply forall_ForallT .. | | | ].
- reflexivity.
- etransitivity; eassumption.
- intros (t, h) [].
- intros (t, h) H. exists t.
  + reflexivity.
  + apply inT_app_iff. left. assumption.
- intros (t, h) H. exists t.
  + reflexivity.
  + apply inT_app_iff. right. assumption.
- intros (t, h) H. exists t.
  + reflexivity.
  + apply inT_app_iff in H as [|]; assumption.
- intros (t, h) [H|H]%inT_app_iff.
  + eapply ForallT_forall in IHpi1; [ | eassumption ]. destruct IHpi1 as [t' Hsub' Hs'].
    exists t'; [ assumption | ].
    apply inT_app_iff. left. assumption.
  + eapply ForallT_forall in IHpi2; [ | eassumption ]. destruct IHpi2 as [t' Hsub' Hs'].
    exists t'; [ assumption | ].
    apply inT_app_iff. right. assumption.
- intros (t, h) H.
  clear pi2 IHpi1.
  induction (form_decomposition d) as [ | (t', h') l' ].
  + destruct H.
  + destruct H as [[= <- <-] | H].
    * eapply ForallT_forall in IHpi2; [ | apply inT_eq ]. destruct IHpi2 as [t'' Hsub'' Hs''].
      exists (a :: t'').
      -- constructor; assumption.
      -- change (a :: t'', h') with ((fun '(t, h) => (a :: t, h)) (t'', h')).
         apply inT_map. assumption.
    * apply IHl' in H.
      -- assumption.
      -- apply forall_ForallT. intros (t'', h'') H''.
         eapply ForallT_forall in IHpi2; [ | apply (inT_cons _ _ _ H'') ]. assumption.
- rewrite map_app. reflexivity.
- reflexivity.
- destruct i.
Qed.

Lemma omega_sub a : Ω ⩽ a <=> form_decomposition a = [].
Proof.
eapply iffT_Transitive; [ apply sub_form_decomposition | ]. cbn.
split.
- intro Hle.
  destruct (form_decomposition a) as [ | b l ]; [ reflexivity | exfalso ].
  inversion_clear Hle.
  destruct b, X as [? _ []].
- intros ->. reflexivity.
Qed.

Lemma var_sub x a : x ⩽ a <=> { n | form_decomposition a = repeat ([], x) n }.
Proof.
eapply iffT_Transitive; [ apply sub_form_decomposition | ]. cbn.
split.
- intro Hle. induction Hle.
  + exists 0. reflexivity.
  + destruct IHHle as [n ->].
    exists (S n). cbn. f_equal.
    destruct x0, p. destruct i as [[= <- <-] | i]; [ | destruct i ].
    inversion_clear f.
    reflexivity.
- intros [n ->].
  apply forall_ForallT. intros (t, h) [= -> ->]%repeat_specT.
  exists []; constructor. reflexivity.
Qed.


(** * Order is equality on simple types *)

Lemma sub_ia_free a b (Ha : inter_omega_free a = true) (Hb : inter_omega_free b = true) : a ⩽ b -> a = b.
Proof.
remember (fsize a + fsize b) as n eqn:Hn.
induction n as [n IHn] using (well_founded_induction_type lt_wf) in a, Ha, b, Hb, Hn |- *.
assert (forall a' b', fsize a' + fsize b' < fsize a + fsize b ->
          inter_omega_free a' = true -> inter_omega_free b' = true -> a' ⩽ b' -> a' = b') as IH
  by (intros a' b' Hs Ha' Hb'; apply (IHn (fsize a' + fsize b')); try assumption; lia).
clear n Hn IHn.
intros Hsub%sub_form_decomposition.
rewrite <- (form_redecomposition_ia_free _ Ha), <- (form_redecomposition_ia_free _ Hb). f_equal.
assert (Hla := form_decomposition_ia_free_sgt _ Ha).
assert (Hlb := form_decomposition_ia_free_sgt _ Hb).
remember (form_decomposition a) as sa eqn:Hsa.
remember (form_decomposition b) as sb eqn:Hsb.
destruct sa as [ | (ta, ha) [ | ] ]; [ discriminate Hla | | discriminate Hla ].
destruct sb as [ | (tb, hb) [ | ] ]; [ discriminate Hlb | | discriminate Hlb ].
eapply ForallT_forall in Hsub; [ | apply inT_eq ]. destruct Hsub as [t' Hsub Hs].
inversion Hs; [ injection H as [= <- <-] | inversion X ].
f_equal. f_equal.
assert (HFta := form_decomposition_ia_free_rec _ Ha).
assert (HFtb := form_decomposition_ia_free_rec _ Hb).
assert (Hta := form_decomposition_fsize a).
assert (Htb := form_decomposition_fsize b).
rewrite <- Hsa in *. rewrite <- Hsb in *.
inversion_clear HFta as [ | ? ? HFta' H ]. clear H.
inversion_clear HFtb as [ | ? ? HFtb' H ]. clear H.
inversion_clear Hta as [ | ? ? Hta' H ]. clear H.
inversion_clear Htb as [ | ? ? Htb' H ]. clear H.
clear - IH HFta' HFtb' Hta' Htb' Hsub.
induction Hsub; [ reflexivity | f_equal ];
  inversion_clear Hta'; inversion_clear Htb'; inversion_clear HFta'; inversion_clear HFtb'.
- symmetry. apply IH; [ lia | assumption .. ].
- apply IHHsub; assumption.
Qed.


(** * Beta condition *)

(* Lemma 17 *)
Lemma bcd_beta : beta_condition (@bcd_sub nil).
Proof.
intros s a b Hnil Hsub%sub_form_decomposition.
rewrite form_derecomposition in Hsub. cbn in Hsub.
remember (form_decomposition b) as sb eqn:Hsb.
induction sb as [ | (tb1, hb1) sb IH ] in b, Hsb, Hsub |- *.
- exists nil; [ | split ].
  + apply sublistT_nil_l.
  + constructor.
  + apply omega_sub. symmetry. assumption.
- inversion_clear Hsub.
  destruct X as [t1' HFt1' Ht1'].
  specialize (IH (form_recomposition sb)).
  rewrite form_derecomposition in IH.
  apply (IH eq_refl) in X0 as [sb' HS' [HF' H']]. clear IH.
  induction s as [|(t1, h1) s1]; destruct Ht1'.
  + injection e as [= -> ->].
    inversion HS'; subst.
    * exists ((t1', hb1) :: l1); [ | split ].
      -- now constructor.
      -- assumption.
      -- transitivity (form_recomposition (form_decomposition b)).
         2:{ apply bcd_form_redecomposition. }
         rewrite <- Hsb.
         clear - H' HFt1'.
         apply form_recomposition_sub.
         constructor.
         ++ exists (tl t1').
            ** inversion HFt1'. assumption.
            ** apply inT_eq.
         ++ apply sub_form_decomposition in H'. rewrite !form_derecomposition in H'.
            assumption.
    * exists ((t1', hb1) :: sb'); [ | split ].
      -- now constructor.
      -- inversion_clear HFt1'.
         constructor; assumption.
      -- transitivity (form_recomposition (form_decomposition b)).
         2:{ apply bcd_form_redecomposition. }
         rewrite <- Hsb.
         clear - H' HFt1'.
         apply form_recomposition_sub.
         constructor.
         ++ exists (tl t1').
            ** inversion HFt1'. assumption.
            ** apply inT_eq.
         ++ apply sub_form_decomposition in H'. rewrite !form_derecomposition in H'.
            apply forall_ForallT. intros (t, h) Hinl.
            apply ForallT_forall with _ _ _ (t, h) in H'; [ | assumption ].
            destruct H' as [t' H' Hin'].
            exists t'; [ assumption | ].
            apply inT_cons. assumption.
  + inversion HS'; subst.
    * destruct (sublistT_inT_extend _ X i) as [l1' Hs1' [Hin1' Hincl1']].
      exists ((t1, h1) :: l1'); [ | split ].
      -- now constructor.
      -- inversion_clear HF'.
         cbn. constructor; [ assumption | ].
         apply (inclT_map (fun '(x, _) => hd Ω x)) in Hincl1'.
         eapply inclT_ForallT; [ apply Hincl1' | ].
         cbn. constructor.
         ++ inversion_clear HFt1'. assumption.
         ++ assumption.
      -- transitivity (form_recomposition (form_decomposition b)).
         2:{ apply bcd_form_redecomposition. }
         rewrite <- Hsb.
         clear - H' HFt1' Hin1'.
         apply form_recomposition_sub.
         constructor.
         ++ exists (tl t1').
            ** inversion HFt1'. assumption.
            ** apply (inclT_map (fun '(x, y) => (tl x, y))) in Hin1'.
               specialize (Hin1' (tl t1', hb1)).
               cbn. apply inT_cons, Hin1'. apply inT_eq.
         ++ apply sub_form_decomposition in H'. rewrite !form_derecomposition in H'.
            apply forall_ForallT. intros (t, h) Hinl.
            apply ForallT_forall with _ _ _ (t, h) in H'; [ | assumption ].
            destruct H' as [t' H' Hin'].
            exists t'; [ assumption | ].
            inversion Hin'; [ left; assumption | ].
            apply (@inclT_cons_cons _ (t1, h1)) in Hin1'.
            apply (inclT_map (fun '(x, y) => (tl x, y))) in Hin1'. apply Hin1'.
            apply inT_cons, inT_cons. assumption.
    * destruct (sublistT_inT_extend _ X i) as [l1' Hs1' [Hin1' Hincl1']].
      exists l1'; [ | split ].
      -- now constructor.
      -- apply (inclT_map (fun '(x, _) => hd Ω x)) in Hincl1'.
         eapply inclT_ForallT; [ apply Hincl1' | ].
         cbn. constructor.
         ++ inversion_clear HFt1'. assumption.
         ++ assumption.
      -- transitivity (form_recomposition (form_decomposition b)).
         2:{ apply bcd_form_redecomposition. }
         rewrite <- Hsb.
         clear - H' HFt1' Hin1'.
         apply form_recomposition_sub.
         constructor.
         ++ exists (tl t1').
            ** inversion HFt1'. assumption.
            ** apply (inclT_map (fun '(x, y) => (tl x, y))) in Hin1'.
               specialize (Hin1' (tl t1', hb1)).
               cbn. apply Hin1'. apply inT_eq.
         ++ apply sub_form_decomposition in H'. rewrite !form_derecomposition in H'.
            apply forall_ForallT. intros (t, h) Hinl.
            apply ForallT_forall with _ _ _ (t, h) in H'; [ | assumption ].
            destruct H' as [t' H' Hin'].
            exists t'; [ assumption | ].
            apply (inclT_map (fun '(x, y) => (tl x, y))) in Hin1'. apply Hin1'.
            apply inT_cons. assumption.
Qed.


(** * Eta condition fails *)

(* Lemma 18 *)
Lemma bcd_not_eta : notT (eta_condition (@bcd_equiv nil)).
Proof.
intro He. specialize (He (var 0)) as [s Hs [Hsx [n Hxs]%var_sub]].
rewrite form_derecomposition in Hxs. subst s.
destruct n as [|n].
- apply omega_sub in Hsx as [=].
- inversion_clear Hs.
  apply H. reflexivity.
Qed.

End BCDProp.
