From ch2o_compcert Require Export ch2o_safety compcertc_safety.
From ch2o Require Export stringmap types expressions statements architectures state.
(* We prove soundness for LP64 architectures. *)
From ch2o_compcert Require Export ch2o_lp64.
From compcert Require Export Cop Csyntax Ctypes Globalenvs.

From Coq Require Import Classical.

Section Program.

Local Open Scope string_scope.

Context (Γ: types.env K) (δ: funenv K) (p: Csyntax.program).

Inductive expr_equiv: expressions.expr K → Csyntax.expr → Prop :=
| expr_equiv_val_int z:
  int_typed z (sintT: int_type K) → (* TODO: Require the CH2O program to be well-typed instead? *)
  expr_equiv (EVal ∅ (inr (intV{sintT} z))) (Eval (Vint (Int.repr z)) (Tint I32 Signed noattr))
| expr_equiv_div e1 ė1 e2 ė2:
  expr_equiv e1 ė1 →
  expr_equiv e2 ė2 →
  expr_equiv (e1 / e2) (Ebinop Odiv ė1 ė2 (Tint I32 Signed noattr))
.

Inductive stmt_equiv: stmt K → statement → Prop :=
| stmt_equiv_return e ė:
  expr_equiv e ė →
  stmt_equiv (ret (cast{sintT%T} e)) (Sreturn (Some ė))
| stmt_equiv_skip:
  stmt_equiv SSkip Sskip
| stmt_equiv_sequence s1 ṡ1 s2 ṡ2:
  stmt_equiv s1 ṡ1 →
  stmt_equiv s2 ṡ2 →
  stmt_equiv (SComp s1 s2) (Ssequence ṡ1 ṡ2)
| stmt_equiv_if e ė s1 ṡ1 s2 ṡ2:
  expr_equiv e ė →
  stmt_equiv s1 ṡ1 →
  stmt_equiv s2 ṡ2 →
  stmt_equiv (SIf e s1 s2) (Sifthenelse ė ṡ1 ṡ2)
.

Inductive program_equiv: Prop :=
| program_equiv_intro s ṡ b:
  stringmap_lookup "main" δ = Some s →
  Genv.init_mem p <> None →
  let ge := globalenv p in
  Genv.find_symbol ge p.(prog_main) = Some b →
  let f := {|
    fn_return:=type_int32s;
    fn_callconv:=AST.cc_default;
    fn_params:=nil;
    fn_vars:=nil;
    fn_body:=
      Ssequence
        ṡ
        (Sreturn (Some (Eval (Vint (Int.repr 0)) (Tint I32 Signed noattr))))
  |} in
  Genv.find_funct_ptr ge b = Some (Internal f) →
  stmt_equiv s ṡ →
  program_equiv.

Fixpoint globdef_is_fun{F V}(g: AST.globdef F V): bool :=
  match g with
    AST.Gfun _ => true
  | AST.Gvar _ => false
  end.

Lemma init_mem_ok `{prog: Ctypes.program F}:
  forallb (λ gd, globdef_is_fun (gd.2)) (AST.prog_defs prog) = true →
  Genv.init_mem prog <> None.
Proof.
intros.
unfold Genv.init_mem.
assert (∀ gl ge m, (∀ g, In g gl → globdef_is_fun (snd g) = true) → Genv.alloc_globals (F:=Ctypes.fundef F) (V:=type) ge m gl <> None). {
  induction gl; intros.
  - simpl. intro; discriminate.
  - simpl.
    unfold Genv.alloc_global.
    destruct a.
    destruct g.
    + case_eq (Memory.Mem.alloc m 0 1).
      intros.
      destruct (Memory.Mem.range_perm_drop_2 m0 b 0 1 Memtype.Nonempty).
      * unfold Memory.Mem.range_perm.
        intros.
        apply Memory.Mem.perm_alloc_2 with (1:=H1) (2:=H2).
      * rewrite e.
        apply IHgl.
        intros.
        apply H0.
        right.
        assumption.
    + lapply (H0 (i, AST.Gvar v)).
      intros; discriminate. left.
      reflexivity.
}
apply H0.
rewrite -> (List.forallb_forall (A:=AST.ident * AST.globdef (Ctypes.fundef F) type)) in H.
apply H.
Qed.

Lemma int_typed_limits z:
  int_typed z (sintT%IT: int_type K) →
  (Int.min_signed ≤ z ∧ z ≤ Int.max_signed)%Z.
Proof.
intros.
unfold Int.min_signed, Int.max_signed.
unfold Int.half_modulus.
unfold Int.modulus.
unfold Int.wordsize.
unfold Wordsize_32.wordsize.
assert ((two_power_nat 32 / 2 = 2147483648)%Z). reflexivity.
rewrite H0.
destruct H.
unfold int_lower in H. unfold int_upper in H1.
simpl in *.
lia.
Qed.

Local Open Scope list_scope.

Lemma destruct_list_snoc{X}(P: list X → Prop)(xs: list X):
  P [] →
  (∀ xs0 x, P (xs0 ++ [x])) →
  P xs.
Proof.
intros.
destruct xs.
- assumption.
- destruct (exists_last (l:=x::xs)).
  + intro; discriminate.
  + destruct s.
    rewrite e.
    apply H0.
Qed.

Lemma compcertc_expr_never_stuck f a k e m:
  (∃ v ty, a = Eval v ty) ∨
  ∃ t s, Step (semantics p) (ExprState f a k e m) t s.
Proof.
destruct (classic (imm_safe (globalenv p) e RV a m)).
- inversion H; clear H; subst.
  + left.
    eexists; eexists; reflexivity.
  + right.
    eexists; eexists.
    left.
    apply step_lred; eassumption.
  + right.
    eexists; eexists.
    left.
    apply step_rred; eassumption.
  + right.
    eexists; eexists.
    left.
    apply step_call; eassumption.
- right.
  eexists; eexists.
  left.
  eapply step_stuck with (C:=λ x, x).
  + apply ctx_top.
  + eassumption.
Qed.

Lemma expr_equiv_no_LV_context e ė:
  expr_equiv e ė →
  ∀ C a,
  context LV RV C →
  ė ≠ C a.
Proof.
induction 1; intros.
- inversion H0; clear H0; subst; discriminate.
- intro.
  inversion H1; clear H1; subst; try discriminate.
  + injection H2; clear H2; intros; subst.
    eelim IHexpr_equiv1 with (1:=H3); reflexivity.
  + injection H2; clear H2; intros; subst.
    eelim IHexpr_equiv2 with (1:=H3); reflexivity.
Qed.

Notation tint := (Tint I32 Signed noattr).

Lemma sem_cast_int z m:
  sem_cast (Vint (Int.repr z)) tint tint m = Some (Vint (Int.repr z)).
Proof.
  unfold sem_cast.
  simpl.
  destruct Archi.ptr64; reflexivity.
Qed.

Lemma Int_min_signed: Int.min_signed = (-2147483648)%Z.
Proof.
reflexivity.
Qed.

Lemma Int_max_signed: Int.max_signed = 2147483647%Z.
Proof.
reflexivity.
Qed.

Lemma int_lower_sintT: int_lower (sintT%IT: int_type K) = (-2147483648)%Z.
Proof.
reflexivity.
Qed.

Lemma int_upper_sintT: int_upper (sintT%IT: int_type K) = 2147483648%Z.
Proof.
unfold int_upper.
simpl.
reflexivity.
Qed.

Lemma rred_safe e ė:
  expr_equiv e ė →
  ∀ C a ẽ ṁ t a' ṁ' ρ m,
  context RV RV C →
  ė = C a →
  rred ẽ a ṁ t a' ṁ' →
  ∃ (E: ectx K) e1 e2,
  e = subst E e1 ∧
  Γ \ ρ ⊢ₕ e1, m ⇒ e2, m ∧
  expr_equiv (subst E e2) (C a') ∧
  ṁ' = ṁ.
Proof.
induction 1; intros.
- inversion H0; clear H0; subst; try discriminate.
  subst.
  inversion H2.
- inversion H1; clear H1; subst; try discriminate.
  + subst.
    inversion H3; clear H3; subst.
    inversion H; clear H; subst.
    inversion H0; clear H0; subst.
    simpl in H10.
    unfold sem_div in H10.
    unfold sem_binarith in H10.
    simpl in H10.
    rewrite sem_cast_int in H10.
    rewrite sem_cast_int in H10.
    rewrite Int.eq_signed in H10.
    destruct (Coqlib.zeq (Int.signed (Int.repr z0)) (Int.signed Int.zero)). {
      discriminate.
    }
    rewrite Int.signed_repr in n. 2:{ apply int_typed_limits; assumption. }
    rewrite Int.signed_zero in n.
    rewrite Int.eq_signed in H10.
    rewrite Int.signed_repr in H10. 2:{ apply int_typed_limits; assumption. }
    rewrite Int.signed_repr in H10. 2:{
      split; try reflexivity.
      pose proof Int.min_signed_neg.
      pose proof Int.max_signed_pos.
      lia.
    }
    rewrite Int.eq_signed in H10.
    rewrite Int.signed_repr in H10. 2:{ apply int_typed_limits; assumption. }
    rewrite Int.signed_mone in H10.
    rewrite Int_min_signed in H10.
    assert (int_typed (z ÷ z0)%Z (sintT: int_type K) ∧ v = Vint (Int.divs (Int.repr z) (Int.repr z0))). {
      destruct (Coqlib.zeq z (-2147483648)).
      - destruct (Coqlib.zeq z0 (-1)). {
          discriminate.
        }
        simpl in H10.
        split; try congruence.
        subst.
        split.
        + rewrite int_lower_sintT.
          destruct (Z.lt_total z0 0) as [?|[?|?]].
          * assert (0 <= 2147483648 ÷ -z0)%Z. apply Z.quot_pos; lia.
            rewrite Zquot.Zquot_opp_r in H0.
            rewrite <- Zquot.Zquot_opp_l in H0.
            assert (-(2147483648) = -2147483648)%Z. reflexivity.
            rewrite H1 in H0.
            lia.
          * lia.
          * destruct (Zquot.Z_mult_quot_ge (-2147483648) z0)%Z; try lia.
            lapply (Z.mul_le_mono_nonpos_r 1 z0 (-2147483648 ÷ z0))%Z. 2:{
              assert (-2147483648 ÷ z0 = -(2147483648 ÷ z0))%Z. {
                rewrite <- Zquot.Zquot_opp_l.
                reflexivity.
              }
              rewrite H4.
              lapply (Zquot.Z_quot_pos 2147483648 z0). 2:{
                lia.
              }
              intro.
              lapply H5. 2:{
                lia.
              }
              intro.
              lia.
            }
            intro.
            lapply H4. 2:{
              lia.
            }
            intro.
            lia.
        + rewrite int_upper_sintT.
          destruct (Z.lt_total 0 z0) as [?|[?|?]].
          * assert (-2147483648 ÷ z0 = -(2147483648 ÷ z0))%Z. {
              rewrite <- Zquot.Zquot_opp_l.
              reflexivity.
            }
            rewrite H0.
            lapply (Zquot.Z_quot_pos 2147483648 z0)%Z; intros. 2:{
              lia.
            }
            lapply H1; intros. 2:{ lia. }
            lia.
          * lia.
          * assert (2147483648 ÷ -z0 < 2147483648)%Z. {
              apply Z.quot_lt; lia.
            }
            rewrite Zquot.Zquot_opp_r in H0.
            rewrite <- Zquot.Zquot_opp_l in H0.
            apply H0.
      - simpl in H10.
        split; try congruence.
        split.
        + rewrite int_lower_sintT.
          destruct (Z.lt_total 0 z0) as [?|[?|?]]; try lia.
          * destruct (Z.lt_total 0 z) as [?|[?|?]].
            -- assert (0 <= z ÷ z0)%Z. apply Zquot.Z_quot_pos; lia.
               lia.
            -- subst.
               rewrite Zquot.Zquot_0_l.
               lia.
            -- destruct H3.
               rewrite int_lower_sintT in H1.
               assert (z <= z0 * (z ÷ z0))%Z. apply Zquot.Z_mult_quot_ge. lia.
               assert (z0 * (z ÷ z0) <= 1 * (z ÷ z0))%Z. {
                 apply Z.mul_le_mono_nonpos_r.
                 - assert (0 <= -z ÷ z0)%Z. apply Zquot.Z_quot_pos; lia.
                   assert (-z ÷ z0 = -(z ÷ z0))%Z. rewrite Zquot.Zquot_opp_l; reflexivity.
                   lia.
                 - lia.
               }
               lia.
          * destruct (Z.lt_total 0 z) as [?|[?|?]].
            -- destruct H3.
               rewrite int_upper_sintT in H3.
               assert (-z <= -z0 * (-z ÷ -z0))%Z. apply Zquot.Z_mult_quot_ge. lia.
               assert (-z0 * (-z ÷ -z0) <= 1 * (-z ÷ -z0))%Z. {
                 apply Z.mul_le_mono_nonpos_r.
                 - assert (0 <= z ÷ -z0)%Z. apply Zquot.Z_quot_pos; lia.
                   assert (-z ÷ -z0 = -(z ÷ -z0))%Z. rewrite Zquot.Zquot_opp_l; reflexivity.
                   lia.
                 - lia.
               }
               assert (-z ÷ -z0 = z ÷ z0)%Z. rewrite Zquot.Zquot_opp_l. rewrite Zquot.Zquot_opp_r. lia.
               lia.
            -- subst.
               rewrite Zquot.Zquot_0_l.
               lia.
            -- assert (0 <= z ÷ z0)%Z. {
                 assert (z ÷ z0 = - -(-z ÷ -z0))%Z. rewrite Zquot.Zquot_opp_l. rewrite Zquot.Zquot_opp_r. lia.
                 assert (0 <= -z ÷ -z0)%Z. apply Zquot.Z_quot_pos; lia.
                 lia.
               }
               lia.
        + rewrite int_upper_sintT.
          destruct (Z.lt_total 0 z0) as [?|[?|?]]; try lia.
          * destruct (Z.lt_total 0 z) as [?|[?|]].
            -- destruct H3.
               rewrite int_upper_sintT in H3.
               assert (z0 * (z ÷ z0) <= z)%Z. {
                 apply Zquot.Z_mult_quot_le; lia.
               }
               assert (1 * (z ÷ z0) <= z0 * (z ÷ z0))%Z. {
                 apply Z.mul_le_mono_nonneg_r.
                 - apply Zquot.Z_quot_pos; lia.
                 - lia.
               }
               lia.
            -- subst.
               rewrite Zquot.Zquot_0_l.
               lia.
            -- assert (z ÷ z0 = -(-z ÷ z0))%Z. rewrite Zquot.Zquot_opp_l; lia.
               assert (0 <= -z ÷ z0)%Z. apply Zquot.Z_quot_pos; lia.
               lia.
          * destruct (Z.lt_total 0 z) as [?|[?|?]].
            -- assert (z ÷ z0 = -(z ÷ -z0))%Z. rewrite Zquot.Zquot_opp_r; lia.
               assert (0 <= z ÷ -z0)%Z. apply Zquot.Z_quot_pos; lia.
               lia.
            -- subst.
               rewrite Zquot.Zquot_0_l.
               lia.
            -- destruct H3.
               rewrite int_lower_sintT in H1.
               assert (-z0 * (-z ÷ -z0) <= -z)%Z. {
                 apply Zquot.Z_mult_quot_le; lia.
               }
               assert (1 * (-z ÷ -z0) <= -z0 * (-z ÷ -z0))%Z. {
                 apply Z.mul_le_mono_nonneg_r.
                 - apply Zquot.Z_quot_pos; lia.
                 - lia.
               }
               assert (z ÷ z0 = -z ÷ -z0)%Z. {
                 rewrite Zquot.Zquot_opp_l.
                 rewrite Zquot.Zquot_opp_r.
                 lia.
               }
               lia.
    }
    destruct H.
    subst.
    exists [].
    eexists; eexists.
    simpl; split; [reflexivity|].
    split. {
      constructor. constructor.
      -- assumption.
      -- apply H.
    }
    split. {
      rewrite (right_id_L _ (∪)).
      unfold Int.divs.
      rewrite Int.signed_repr. 2:{ apply int_typed_limits; assumption. }
      rewrite Int.signed_repr. 2:{ apply int_typed_limits; assumption. }
      constructor.
      assumption.
    }
    reflexivity.
  + injection H2; clear H2; intros; subst.
    destruct (IHexpr_equiv1 C0 a ẽ ṁ t a' ṁ' ρ m H4) as [E [e5 [e6 [? [? ?]]]]]; try trivial.
    exists (E ++ [CBinOpL (ArithOp DivOp) e2])%E; eexists; eexists.
    rewrite subst_snoc.
    rewrite subst_snoc.
    simpl.
    rewrite H1.
    split; try trivial.
    split. { apply H2. }
    split. { constructor; tauto. }
    destruct H5; congruence.
  + injection H2; clear H2; intros; subst.
    destruct (IHexpr_equiv2 C0 a ẽ ṁ t a' ṁ' ρ m H4) as [E [e5 [e6 [? [? [? Hṁ']]]]]]; try trivial.
    exists (E ++ [CBinOpR (ArithOp DivOp) e1])%E; eexists; eexists.
    rewrite subst_snoc.
    rewrite subst_snoc.
    simpl.
    rewrite H1.
    split; try trivial.
    split. { apply H2. }
    split. { constructor; assumption. }
    assumption.
Qed.

Lemma expr_equiv_no_call e ė:
  expr_equiv e ė →
  ∀ a m fd vargs ty C,
  callred (globalenv p) a m fd vargs ty →
  context RV RV C →
  ė ≠ C a.
Proof.
induction 1; intros.
- inversion H1; subst; try discriminate.
  intro; subst.
  inversion H0.
- inversion H2; subst; try discriminate.
  + intro; subst.
    inversion H1.
  + intro.
    injection H4; clear H4; intros; subst.
    apply IHexpr_equiv1 with (1:=H1) (2:=H3) (3:=eq_refl).
  + intro.
    injection H4; clear H4; intros; subst.
    apply IHexpr_equiv2 with (1:=H1) (2:=H3) (3:=eq_refl).
Qed.

Lemma expr_equiv_imm_safe_rred e ė:
  expr_equiv e ė →
  ∀ ρ m,
  (∀ (E: ectx K) e1, e = subst E e1 → is_redex e1 → Γ \ ρ ⊢ₕ safe e1, m) →
  (∃ v ty, ė = Eval v ty) ∨
  ∀ ṁ,
  ∃ C a t a',
  context RV RV C ∧
  ė = C a ∧ rred (globalenv p) a ṁ t a' ṁ.
Proof.
induction 1; intros.
- left. eexists; eexists; reflexivity.
- right.
  intros.
  destruct (IHexpr_equiv1 ρ m). {
    intros.
    apply H1 with (2:=H3) (E:=(E++[CBinOpL (ArithOp DivOp) e2])).
    rewrite subst_snoc.
    rewrite H2.
    reflexivity.
  }
  + destruct (IHexpr_equiv2 ρ m). {
      intros.
      apply H1 with (2:=H4) (E:=(E++[CBinOpR (ArithOp DivOp) e1])).
      rewrite subst_snoc.
      rewrite H3.
      reflexivity.
    }
    * destruct H2 as [v1 [ty1 ?]].
      destruct H3 as [v2 [ty2 ?]].
      subst.
      inversion H; clear H; subst.
      inversion H0; clear H0; subst.
      eexists; eexists; eexists; eexists.
      split. { apply ctx_top. }
      split. { simpl; reflexivity. }
      constructor.
      simpl.
      assert (Γ \ ρ ⊢ₕ safe (# intV{sintT} z / # intV{sintT} z0)%E, m). {
        apply H1 with (E:=[]).
        - reflexivity.
        - constructor; constructor.
      }
      inversion H; clear H; subst.
      inversion H0; clear H0; subst.
      inversion H11; clear H11; subst.
      assert (z0 ≠ 0)%Z. { apply H. }
      assert (int_typed (z ÷ z0) (sintT%IT: int_type K)). { apply H0. }
      clear H H0.
      unfold sem_div.
      unfold sem_binarith.
      simpl.
      rewrite sem_cast_int.
      rewrite sem_cast_int.
      rewrite Int.eq_signed.
      rewrite Int.signed_repr. 2:{ apply int_typed_limits; assumption. }
      rewrite Int.signed_zero.
      destruct (Coqlib.zeq z0 0); try lia.
      simpl.
      rewrite Int.eq_signed.
      rewrite Int.signed_repr. 2:{ apply int_typed_limits; assumption. }
      rewrite Int.signed_repr. 2:{
        split. { reflexivity. }
        pose proof Int.min_signed_neg.
        pose proof Int.max_signed_pos.
        lia.
      }
      rewrite Int_min_signed.
      rewrite Int.eq_signed.
      rewrite Int.signed_repr. 2:{ apply int_typed_limits; assumption. }
      rewrite Int.signed_mone.
      assert (
        (if Coqlib.zeq z (-2147483648) then true else false) &&
        (if Coqlib.zeq z0 (-1) then true else false)
        = false
      ). {
        destruct (Coqlib.zeq z (-2147483648)). {
          destruct (Coqlib.zeq z0 (-1)). {
            subst.
            destruct H5.
            rewrite int_upper_sintT in H0.
            discriminate.
          }
          reflexivity.
        }
        reflexivity.
      }
      rewrite H.
      reflexivity.
    * destruct (H3 ṁ) as [C [a [t [a' [HC [Hė2 Hrred]]]]]].
      subst.
      exists (λ x, Ebinop Odiv ė1 (C x) tint).
      eexists; eexists; eexists.
      split. {
        constructor.
        assumption.
      }
      split. {
        reflexivity.
      }
      eapply Hrred.
  + destruct (H2 ṁ) as [C [a [t [a' [HC [Hė1 Hrred]]]]]].
    subst.
    exists (λ x, Ebinop Odiv (C x) ė2 tint).
    eexists; eexists; eexists.
    split. {
      constructor.
      assumption.
    }
    split. {
      reflexivity.
    }
    eapply Hrred.
Qed.

Lemma expr_equiv_imm_safe e ė:
  expr_equiv e ė →
  ∀ K_ C a ρ m ẽ ṁ,
  context K_ RV C →
  ė = C a →
  (∀ (E: ectx K) e1, e = subst E e1 → is_redex e1 → Γ \ ρ ⊢ₕ safe e1, m) →
  imm_safe (globalenv p) ẽ K_ a ṁ.
Proof.
induction 1; intros.
- inversion H0; clear H0; subst; try discriminate.
  subst.
  constructor.
- inversion H1; clear H1; subst; try discriminate.
  + subst.
    edestruct (expr_equiv_imm_safe_rred (e1 / e2) (Ebinop Odiv ė1 ė2 tint))%E. {
      constructor; assumption.
    } {
      eassumption.
    }
    * destruct H1 as [? [? ?]]; discriminate.
    * destruct (H1 ṁ) as [C [a [t [a' [HC [Hė Hrred]]]]]].
      rewrite Hė.
      eapply imm_safe_rred with (C:=C) (e0:=a); eassumption.
  + injection H2; clear H2; intros; subst.
    eapply IHexpr_equiv1; try eassumption.
    * reflexivity.
    * intros.
      eapply H3 with (E:=E++[CBinOpL (ArithOp DivOp) e2]); try assumption.
      rewrite subst_snoc.
      simpl.
      congruence.
  + injection H2; clear H2; intros; subst.
    eapply IHexpr_equiv2; try eassumption.
    * reflexivity.
    * intros.
      eapply H3 with (E:=E++[CBinOpR (ArithOp DivOp) e1]); try assumption.
      rewrite subst_snoc.
      simpl.
      congruence.
Qed.

Lemma eval_soundness Q n e ė k ḳ m ṁ f:
  expr_equiv e ė →
  ch2o_safe_state Γ δ Q (State k (Expr e) m) →
  (∀ z n',
   n' ≤ n →
   int_typed z (sintT: int_type K) →
   ch2o_safe_state Γ δ Q (State k (Expr (# intV{sintT} z)) m) →
   compcertc_safe_state_n Q p n' (ExprState f (Eval (Vint (Int.repr z)) (Tint I32 Signed noattr)) ḳ empty_env ṁ)) →
  compcertc_safe_state_n Q p n (ExprState f ė ḳ empty_env ṁ).
Proof.
revert e ė.
apply well_founded_induction with (1:=lt_wf) (a:=n).
clear n.
intros n IH.
intros.
intros t s HstarN.
inversion HstarN; subst.
- (* refl *)
  destruct (compcertc_expr_never_stuck f ė ḳ empty_env ṁ).
  + destruct H2 as [v [ty H2]].
    subst.
    inversion H; clear H; subst.
    unfold compcertc_safe_state_n in H1.
    eapply H1 with (n':=0) (trace:=[]); try eauto.
  + tauto.
- case_eq (match ė with Eval _ _ => true | _ => false end); intros. {
    inversion H; clear H; subst; try discriminate.
    unfold compcertc_safe_state_n in H1.
    eapply H1 with (n':=S n0) (4:=HstarN); try eauto.
  }
  destruct H2. 2:{
    inversion H2; subst; discriminate.
  }
  inversion H2; clear H2; subst.
  + (* step_lred *)
    eapply expr_equiv_no_LV_context in H; [elim H; reflexivity | assumption].
  + (* step_rred *)
    edestruct (rred_safe _ _ H) as [E [e1 [e2 [He1 [He1e2 [Hee' Hṁ']]]]]]; try (eassumption || reflexivity).
    unfold compcertc_safe_state_n in IH.
    subst.
    eapply IH with (2:=Hee') (5:=H3).
    * lia.
    * intro S'.
      intro HS'.
      apply H0.
      eapply rtc_l; try eassumption.
      assert (∀ e, cast{sintT%T} (subst E e) = subst (E ++ [CCast (sintT%T)]) e)%E. {
        intros; rewrite subst_snoc.
        reflexivity.
      }
      apply cstep_expr_head.
      apply He1e2.
    * intros z n' Hn'.
      apply (H1 z n'); lia.
  + (* step_call *)
    apply expr_equiv_no_call with (2:=H12) (3:=H13) in H.
    elim H; reflexivity.
  + elim H13.
    eapply expr_equiv_imm_safe with (1:=H) (2:=H12). { reflexivity. }
    intros.
    destruct (classic (Γ \ locals k ⊢ₕ safe e1, m)); try eassumption.
    destruct (H0 (State k (Undef (UndefExpr E e1)) m)). {
      eapply rtc_l; [|apply rtc_refl].
      subst.
      apply cstep_expr_undef; assumption.
    }
    * inversion H7.
    * destruct H7 as [S'' H7].
      inversion H7.
Qed.

Lemma eval_soundness' Q n e ė k ḳ m ṁ f:
  expr_equiv e ė →
  ch2o_safe_state Γ δ Q (State k (Expr (cast{sintT%T} e)) m) →
  (∀ z n',
   n' ≤ n →
   int_typed z (sintT: int_type K) →
   ch2o_safe_state Γ δ Q (State k (Expr (# intV{sintT} z)) m) →
   compcertc_safe_state_n Q p n' (ExprState f (Eval (Vint (Int.repr z)) (Tint I32 Signed noattr)) ḳ empty_env ṁ)) →
  compcertc_safe_state_n Q p n (ExprState f ė ḳ empty_env ṁ).
Proof.
revert e ė.
apply well_founded_induction with (1:=lt_wf) (a:=n).
clear n.
intros n IH.
intros.
intros t s HstarN.
inversion HstarN; subst.
- (* refl *)
  destruct (compcertc_expr_never_stuck f ė ḳ empty_env ṁ).
  + destruct H2 as [v [ty H2]].
    subst.
    inversion H; clear H; subst.
    unfold compcertc_safe_state_n in H1.
    eapply H1 with (n':=0) (trace:=[]); try eauto.
    intro; intros; eapply H0.
    eapply rtc_l; try eassumption.
    apply cstep_expr_head with (E:=[]).
    constructor.
    apply H4.
  + tauto.
- case_eq (match ė with Eval _ _ => true | _ => false end); intros. {
    inversion H; clear H; subst; try discriminate.
    unfold compcertc_safe_state_n in H1.
    eapply H1 with (n':=S n0) (4:=HstarN); try eauto.
    intro; intros; eapply H0.
    eapply rtc_l; try eassumption.
    apply cstep_expr_head with (E:=[]).
    constructor.
    apply H5.
  }
  destruct H2. 2:{
    inversion H2; subst; discriminate.
  }
  inversion H2; clear H2; subst.
  + (* step_lred *)
    eapply expr_equiv_no_LV_context in H; [elim H; reflexivity | assumption].
  + (* step_rred *)
    edestruct (rred_safe _ _ H) as [E [e1 [e2 [He1 [He1e2 [Hee' Hṁ']]]]]]; try (eassumption || reflexivity).
    unfold compcertc_safe_state_n in IH.
    subst.
    eapply IH with (2:=Hee') (5:=H3).
    * lia.
    * intro S'.
      intro HS'.
      apply H0.
      eapply rtc_l; try eassumption.
      assert (∀ e, cast{sintT%T} (subst E e) = subst (E ++ [CCast (sintT%T)]) e)%E. {
        intros; rewrite subst_snoc.
        reflexivity.
      }
      rewrite 2 H2.
      apply cstep_expr_head.
      apply He1e2.
    * intros z n' Hn'.
      apply (H1 z n'); lia.
  + (* step_call *)
    apply expr_equiv_no_call with (2:=H12) (3:=H13) in H.
    elim H; reflexivity.
  + elim H13.
    eapply expr_equiv_imm_safe with (1:=H) (2:=H12). { reflexivity. }
    intros.
    destruct (classic (Γ \ locals k ⊢ₕ safe e1, m)); try eassumption.
    destruct (H0 (State k (Undef (UndefExpr (E ++ [CCast sintT]) e1)) m)). {
      eapply rtc_l; [|apply rtc_refl].
      subst.
      assert (cast{sintT%T} (subst E e1) = subst (E ++ [CCast sintT]) e1)%E. rewrite subst_snoc; reflexivity.
      rewrite H2.
      apply cstep_expr_undef; assumption.
    }
    * inversion H7.
    * destruct H7 as [S'' H7].
      inversion H7.
Qed.

Lemma stmt_soundness Q f s ṡ:
  stmt_equiv s ṡ →
  ∀ n k ḳ m ṁ,
  ch2o_safe_state Γ δ Q (State k (Stmt ↘ s) m) →
  (∀ n',
   n' ≤ n →
   ch2o_safe_state Γ δ Q (State k (Stmt ↗ s) m) →
   compcertc_safe_state_n Q p n' (Csem.State f Sskip ḳ empty_env ṁ)) →
  (∀ n' z ḳ',
   n' ≤ n →
   int_typed z (sintT: int_type K) →
   call_cont ḳ' = call_cont ḳ →
   ch2o_safe_state Γ δ Q (State k (Stmt (⇈ (intV{sintT} z)) s) m) →
   compcertc_safe_state_n Q p n' (ExprState f (Eval (Vint (Int.repr z)) tint) (Kreturn ḳ') empty_env ṁ)) →
  compcertc_safe_state_n Q p n (Csem.State f ṡ ḳ empty_env ṁ).
Proof.
(* TODO: When adding support for loops, we'll need to perform well-founded induction on n here as well. *)
induction 1.
- (* return *)
  intros.
  intro; intros.
  inversion H3; clear H3; subst. {
    right.
    eexists; eexists.
    right.
    constructor.
  }
  inversion H4; clear H4; subst; inversion H3; clear H3; subst; try intuition discriminate.
  eapply eval_soundness'; try eassumption. {
    intro; intros.
    eapply H0.
    eapply rtc_l; [|eassumption].
    apply cstep_expr with (E:=CReturnE).
  }
  intros.
  eapply H2; try eassumption.
  + lia.
  + reflexivity.
  + intro; intros.
    eapply H6.
    eapply rtc_l; [|eassumption].
    rewrite <- mem_unlock_empty at 2.
    constructor.
- (* skip *)
  intros.
  eapply H0.
  + reflexivity.
  + intro; intros.
    eapply H.
    eapply rtc_l; [|eassumption].
    constructor.
- (* sequence *)
  intros.
  intro; intros.
  inversion H4; clear H4; subst. {
    right.
    eexists; eexists.
    right.
    constructor.
  }
  inversion H5; clear H5; subst; inversion H4; clear H4; subst; try intuition discriminate.
  eapply IHstmt_equiv1; try eassumption. {
    intro; intros.
    eapply H1.
    eapply rtc_l; [|eassumption].
    constructor.
  } 2:{
    intros.
    simpl in H7.
    eapply H3; try eassumption.
    - lia.
    - intro; intros.
      eapply H8.
      eapply rtc_l; [|eassumption].
      constructor.
  }
  intros.
  intro; intros.
  inversion H7; clear H7; subst. {
    right.
    eexists; eexists.
    right.
    constructor.
  }
  inversion H8; clear H8; subst; inversion H7; clear H7; subst. 2:{
    inversion H15.
  }
  eapply IHstmt_equiv2; try eassumption. {
    intro; intros.
    eapply H5.
    eapply rtc_l; [|eassumption].
    constructor.
  } 2:{
    intros.
    intro; intros.
    eapply H3; try eassumption.
    + lia.
    + intro; intros.
      eapply H11.
      eapply rtc_l; [|eassumption].
      constructor.
  }
  intros.
  eapply H2; try eassumption.
  + lia.
  + intro; intros.
    eapply H8.
    eapply rtc_l; [|eassumption].
    constructor.
- (* if *)
  intros.
  intro; intros.
  inversion H5; clear H5; subst. {
    right.
    eexists; eexists.
    right.
    constructor.
  }
  inversion H6; clear H6; subst; inversion H5; clear H5; subst; try intuition discriminate.
  eapply eval_soundness; try eassumption. {
    intro; intros.
    eapply H2.
    eapply rtc_l; [|eassumption].
    apply cstep_expr with (E:=CIfE s1 s2).
  }
  intros.
  intro; intros.
  inversion H9; clear H9; subst. {
    right.
    eexists; eexists.
    right.
    constructor.
    unfold bool_val.
    simpl.
    reflexivity.
  }
  inversion H10; clear H10; subst; inversion H9; clear H9; subst. {
    inversion H19; clear H19; subst; try discriminate.
  } {
    inversion H19; clear H19; subst; try discriminate.
    subst.
    inversion H18; clear H18; subst.
  } {
    inversion H19; clear H19; subst; try discriminate.
    subst.
    inversion H18; clear H18; subst.
  } {
    inversion H18; clear H18; subst; try discriminate.
    subst.
    elim H19; constructor.
  }
  unfold bool_val in H21.
  simpl in H21.
  injection H21; clear H21; intros; subst.
  rewrite Int.eq_signed in H11.
  rewrite Int.signed_repr in H11. 2:{
    apply int_typed_limits; assumption.
  }
  rewrite Int.signed_zero in H11.
  destruct (Coqlib.zeq z 0); simpl in H11.
  + (* z = 0 *)
    subst.
    eapply IHstmt_equiv2; try eassumption. {
      intro; intros.
      eapply H8.
      eapply rtc_l; [|eassumption].
      constructor.
      - simpl. constructor.
      - constructor.
    } 2:{
      intros.
      eapply H4; try eassumption.
      - lia.
      - intro; intros.
        eapply H13.
        eapply rtc_l; [|eassumption].
        rewrite mem_unlock_empty.
        constructor.
    }
    intros.
    rewrite mem_unlock_empty in H10.
    intro; intros.
    eapply H3; try eassumption.
    * lia.
    * intro; intros.
      eapply H10.
      eapply rtc_l; [|eassumption].
      constructor.
  + (* z ≠ 0 *)
    eapply IHstmt_equiv1; try eassumption. {
      intro; intros.
      eapply H8.
      eapply rtc_l; [|eassumption].
      constructor.
      - constructor.
      - intro.
        elim n1.
        inversion H10; clear H10; subst.
        reflexivity.
    } 2:{
      intros.
      eapply H4; try eassumption.
      - lia.
      - intro; intros.
        eapply H13.
        eapply rtc_l; [|eassumption].
        rewrite mem_unlock_empty.
        constructor.
    }
    intros.
    rewrite mem_unlock_empty in H10.
    eapply H3; try eassumption.
    * lia.
    * intro; intros.
      eapply H10.
      eapply rtc_l; [|eassumption].
      constructor.
Qed.

Theorem soundness Q:
  program_equiv →
  ch2o_safe_program Γ δ Q →
  compcertc_safe_program Q p.
Proof.
intros Hequiv Hch2o.
destruct Hequiv.
case_eq (Genv.init_mem p); intros; try tauto. clear H0; rename H4 into H0.
econstructor. { econstructor; try eassumption. reflexivity. }
intro n; intro; intros.
(* Callstate *)
inversion H4; clear H4; subst. {
  right.
  eexists.
  eexists.
  right.
  eapply step_internal_function. {
    constructor.
  } {
    constructor.
  } {
    constructor.
  }    
}
inversion H5; clear H5; subst; inversion H4; clear H4; subst.
clear H1 H2 H12 H14.
inversion H13; clear H13; subst.
simpl in H6.
(* Ssequence *)
inversion H6 ; clear H6; subst. {
  right.
  eexists.
  eexists.
  right.
  constructor.
}
inversion H1; clear H1; subst; inversion H4; clear H4; subst.
rename H2 into H6.
(* Executing the body *)
eapply stmt_soundness; try eassumption. {
  intro; intros.
  destruct (Hch2o S'); try tauto.
  apply rtc_transitive with (2:=H1).
  (* Showing a CH2O execution *)
  (* Calling main *)
  eapply rtc_l. {
    econstructor.
    - apply H.
    - constructor.
    - reflexivity.
  }
  simpl.
  apply rtc_refl.
} {
  intros.
  destruct (H2 (State [] (Return "main" voidV) ∅)). {
    eapply rtc_l; [|apply rtc_refl].
    constructor.
  }
  - inversion H4.
  - destruct H4 as [S'' H4].
    inversion H4.
}
intros.
intro; intros.
inversion H7; clear H7; subst. {
  right.
  eexists; eexists.
  right.
  constructor.
  - simpl.
    apply sem_cast_int.
  - reflexivity.
}
inversion H8; clear H8; subst; inversion H7; clear H7; subst. {
  inversion H17; clear H17; subst; try discriminate.
} {
  inversion H17; clear H17; subst; try discriminate.
  subst.
  inversion H16.
} {
  inversion H17; clear H17; subst; try discriminate.
  subst.
  inversion H16.
} {
  inversion H16; clear H16; subst; try discriminate.
  subst.
  elim H17.
  constructor.
}
rewrite H4 in H9.
simpl in H9.
inversion H9; clear H9; subst. 2:{
  inversion H7; clear H7; subst; inversion H9; clear H9; subst.
}
left.
simpl in H17.
rewrite sem_cast_int in H17.
injection H17; clear H17; intros; subst.
constructor.
rewrite Int.signed_repr. 2:{
  apply int_typed_limits; assumption.
}
(* Proving Q z *)
destruct (H5 (state.State [] (Return "main" (intV{sintT} z)) ∅)). 2:{
  inversion H7; assumption.
} 2:{
  destruct H7.
  inversion H7.
}
(* Finishing executing ret *)
eapply rtc_l. {
  constructor.
}
simpl.
apply rtc_refl.
Qed.

End Program.
