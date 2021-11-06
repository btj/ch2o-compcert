From ch2o Require Export architectures.
From ch2o_compcert Require Export bigstep.
From ch2o_compcert Require Export stack_assertions.
From ch2o Require Export axiomatic_expressions.
From ch2o Require Export axiomatic_statements.
From ch2o Require Export axiomatic_adequate.

Section Soundness.

Context {K} {HK: Env K} {HK': EnvSpec K} (Γ: env K) (δ: funenv K).

Lemma sintT_union: (sintT ∪ sintT = sintT)%IT.
Proof.
assert (sintT%IT ∪ sintT%IT = IntType Signed (int_rank ∪ int_rank)). reflexivity.
rewrite H.
unfold union.
unfold rank_union.
rewrite decide_True.
reflexivity.
reflexivity.
Qed.

Lemma binop_ok_sound op z1 z2:
  binop_ok (ArithOp op) z1 z2 →
  int_typed (binop_value (ArithOp op) z1 z2) sintT →
  int_pre_arithop_ok op z1 z2 sintT.
Proof.
  intros.
  inversion H; clear H; subst; simpl.
  - split; assumption.
Qed.

Lemma binop_value_sound op z1 z2:
  binop_ok (ArithOp op) z1 z2 →
  int_pre_arithop op z1 z2 sintT = binop_value (ArithOp op) z1 z2.
Proof.
  intros.
  inversion H.
  - reflexivity.
Qed.

Lemma eval_sound st e z:
  eval st e z →
  (assert_stack st ⊆{Γ,δ} e ⇓ inr (intV{sintT} z))%A.
Proof.
induction 1.
- apply assert_int_typed_eval; assumption.
- apply assert_stack_load with (1:=H).
- destruct op; try (inversion H1; fail).
  eapply assert_eval_int_arithop'; try eassumption; try reflexivity.
  + rewrite int_promote_int.
    rewrite sintT_union.
    reflexivity.
  + apply binop_ok_sound with (1:=H1); assumption.
  + apply binop_value_sound with (1:=H1).
Qed.

Definition R (st: store) (O: outcome): val K -> assert K :=
  λ v,
  (∃st',
   assert_stack st' ★
   ⌜length st' = length st /\
    ∃z, O = oreturn z /\ v = intV{sintT} z⌝)%A.

Definition J: labelname -> assert K := (λ _, False%A).
Definition T: nat -> assert K := (λ _, False%A).
Definition C: option Z -> assert K := (λ _, False%A).

Lemma exec_sound_lemma st s O:
  exec st s O →
  Γ\ δ\ R st O\ J\ T\ C ⊨ₛ
  {{ assert_stack st }} s {{ ∃st', assert_stack st' ★ ⌜O = onormal st'⌝ }}.
Proof.
induction 1.
- (* exec_local_normal *)
  apply ax_local.
  apply ax_stmt_weaken with (8:=IHexec); intros.
  + unfold R.
    apply assert_exist_elim; intro st'0.
    apply assert_Prop_intro_r.
    intros.
    destruct H0.
    destruct H1.
    destruct H1.
    discriminate.
  + unfold J.
    apply assert_False_elim.
  + unfold J.
    rewrite stack_indep.
    apply @RightAbsorb_instance_2.
  + unfold T.
    apply assert_False_elim.
  + unfold C.
    rewrite stack_indep.
    apply @RightAbsorb_instance_2.
  + simpl.
    reflexivity.
  + apply assert_exist_elim. intro st'0.
    apply assert_Prop_intro_r. intro HO.
    injection HO; clear HO; intros; subst.
    simpl.
    apply assert_sep_preserving.
    * destruct mv.
      -- eapply assert_exist_intro.
         unfold var_points_to.
         reflexivity.
      -- reflexivity.
    * rewrite assert_lift_exists.
      eapply assert_exist_intro.
      rewrite assert_lift_sep.
      rewrite stack_indep.
      rewrite assert_Prop_r. 2:reflexivity.
      reflexivity.
- apply ax_local.
  apply ax_stmt_weaken with (8:=IHexec); intros.
  + unfold R.
    apply assert_exist_elim; intro st'.
    apply assert_Prop_intro_r.
    intros.
    destruct H0.
    destruct H1.
    destruct H1.
    injection H1; clear H1; intros; subst.
    destruct st' as [|mv st']; [discriminate|].
    simpl.
    apply assert_sep_preserving.
    * destruct mv.
      -- eapply assert_exist_intro.
         unfold var_points_to.
         reflexivity.
      -- reflexivity.
    * rewrite assert_lift_exists.
      apply assert_exist_intro with (x0:=st').
      rewrite assert_lift_sep.
      rewrite stack_indep.
      rewrite assert_Prop_r.
      -- reflexivity.
      -- split.
         ++ simpl in H0; congruence.
         ++ eexists; tauto.
  + unfold J.
    apply assert_False_elim.
  + unfold J.
    rewrite stack_indep.
    apply @RightAbsorb_instance_2.
  + unfold T.
    apply assert_False_elim.
  + unfold C.
    rewrite stack_indep.
    apply @RightAbsorb_instance_2.
  + simpl.
    reflexivity.
  + apply assert_exist_elim. intro st'0.
    apply assert_Prop_intro_r. intro HO.
    discriminate.
- eapply ax_stmt_weaken_post with (Q:=(assert_stack (<[i:=Some z]>st))%A). {
    apply assert_exist_intro with (x:=(<[i:=Some z]> st)).
    rewrite assert_Prop_r; reflexivity.
  }
  eapply ax_stmt_weaken_pre with (P:=((∃p, var i ⇓ inl p ∧ emp) ★ assert_stack st)%A). {
    apply assert_stack_var.
    assumption.
  }
  apply ax_do.
  apply ax_assign with
    (Q1:=λ ν, (var i ⇓ ν ∧ emp)%A)
    (Q2:=λ ν, (⌜ν = inr (intV{sintT} z)⌝ ★ assert_stack st)%A)
    (μ:=false)
    (γ:=perm_full)
    (τ:=sintT%T).
  + reflexivity.
  + intros.
    rewrite (commutative (★)%A).
    rewrite <- (associative (★)%A).
    apply assert_Prop_intro_l. intros.
    injection H1; clear H1; intros; subst.
    rewrite (commutative (★)%A).
    apply assert_exist_intro with (x:=intV{sintT} z).
    apply assert_exist_intro with (x:=intV{sintT} z).
    apply assert_and_intro.
    * clear H0.
      revert st i H.
      induction st.
      -- simpl; intros; lia.
      -- Opaque perm_full.
         rename a into mv.
         simpl; intros.
         destruct i.
         ++ clear IHst H.
            simpl.
            assert (var_points_to 0 mv ⊆{Γ,δ} var 0 ↦{false,perm_full} - : sintT%BT)%A. {
              destruct mv.
              - eapply assert_exist_intro.
                simpl. reflexivity.
              - reflexivity.
            }
            rewrite H.
            rewrite assert_singleton_l_.
            rewrite (commutative (★)%A).
            rewrite <- (associative (★)%A).
            rewrite assert_exist_sep.
            apply assert_exist_elim; intro p'.
            rewrite (associative (★)%A).
            rewrite (commutative (★)%A).
            rewrite <- (associative (★)%A).
            rewrite (associative (★)%A).
            rewrite assert_eval_functional'.
            rewrite <- (associative (★)%A).
            apply assert_Prop_intro_l. intro Hp'. injection Hp'; clear Hp'; intros; subst p'.
            rewrite (associative (★)%A).
            rewrite (commutative (★)%A).
            rewrite (associative (★)%A).
            rewrite (commutative (★)%A).
            apply assert_sep_preserving; [reflexivity|].
            rewrite (commutative (★)%A).
            apply assert_wand_intro.
            rewrite (commutative (★)%A).
            rewrite (associative (★)%A).
            rewrite <- assert_unlock_sep.
            apply assert_sep_preserving.
            ** rewrite (commutative (★)%A).
               rewrite assert_singleton_l_2.
               apply assert_unlock_singleton.
               reflexivity.
            ** apply assert_stack_unlock_indep.
         ++ simpl.
            rewrite <- assert_unlock_sep.
            rewrite <- assert_wand_sep.
            rewrite (commutative (★)%A).
            rewrite <- (associative (★)%A).
            rewrite (commutative (★)%A) with (x:=(% p ↦{false,perm_full} - : sintT%BT)%A).
            rewrite <- (associative (★)%A).
            apply assert_sep_preserving; [apply var_points_to_unlock_indep|].
            rewrite (commutative (★)%A).
            rewrite (commutative (★)%A) with (y:=(% p ↦{false,perm_full} - : sintT%BT)%A).
            assert (
              ((var (S i) ⇓ inl p ∧ emp) ★ assert_stack st↑)%A ⊆{Γ,δ}
              (((var i ⇓ inl p ∧ emp) ★ assert_stack st)↑)%A). {
              rewrite assert_lift_sep.
              rewrite assert_lift_and.
              rewrite stack_indep.
              apply assert_sep_preserving; [|reflexivity].
              apply assert_and_intro.
              - apply assert_and_elim_l.
                rewrite <- assert_lift_eval.
                reflexivity.
              - apply assert_and_elim_r; reflexivity.
            }
            rewrite H0.
            rewrite IHst.
            ** rewrite assert_lift_sep.
               rewrite assert_lift_wand.
               rewrite assert_lift_unlock.
               rewrite assert_lift_singleton.
               rewrite assert_lift_singleton_.
               reflexivity.
            ** lia.
    * apply assert_wand_intro.
      simpl.
      rewrite eval_sound with (1:=H0).
      assert (forall P Q, P ⊆{Γ,δ} Q -> P ⊆{Γ,δ} (Q ∧ Q)%A). {
        intros.
        apply assert_and_intro; assumption.
      }
      apply H1; clear H1.
      rewrite (right_id _ (★)%A).
      rewrite <- (left_id _ (★)%A) with (x:=(cast{sintT%BT} (# intV{sintT} z) ⇓ inr (intV{sintT} z))%A).
      apply assert_sep_preserving.
      -- apply assert_and_elim_r; reflexivity.
      -- rewrite assert_eval_int_typed.
         apply assert_Prop_intro_l. intro Hz.
         eapply assert_eval_int_cast'.
         ++ rewrite <- assert_int_typed_eval; trivial.
         ++ apply int_cast_ok_self; apply Hz.
         ++ apply int_cast_self; assumption.
  + apply ax_expr_exist_pre. intro p.
    apply ax_expr_base with (ν:=inl p).
    apply assert_and_intro; [reflexivity|].
    apply assert_and_elim_l; reflexivity.
  + apply ax_expr_base with (ν:=inr (intV{sintT} z)).
    rewrite assert_Prop_l; [|reflexivity].
    apply assert_and_intro; [reflexivity|].
    rewrite eval_sound with (1:=H0) at 1.
    rewrite assert_eval_int_typed'.
    rewrite assert_Prop_intro_l; [reflexivity|]. intros.
    rewrite assert_eval_int_cast with (τi:=sintT%IT) (σi:=sintT%IT).
    * rewrite int_cast_self; [|assumption]. reflexivity.
    * apply int_cast_ok_self; assumption.
- eapply ax_stmt_weaken_post with (Q:=(assert_stack (<[i:=Some z]>st))%A). {
    apply assert_exist_intro with (x:=(<[i:=Some z]> st)).
    rewrite assert_Prop_r; reflexivity.
  }
  eapply ax_stmt_weaken_pre with (P:=((∃p, var i ⇓ inl p ∧ emp) ★ assert_stack st)%A). {
    apply assert_stack_var.
    assumption.
  }
  apply ax_do.
  apply ax_cast with (Q1:=(λ v, ⌜ v = inr (intV{sintT} z) /\ int_typed z sintT%IT ⌝ ★ assert_stack (<[i:=Some z]> st) ◊)%A). {
    intros.
    apply assert_Prop_intro_l.
    intros.
    destruct H1.
    injection H1; clear H1; intros; subst.
    eapply assert_exist_intro.
    eapply assert_and_intro. { reflexivity. }
    eapply assert_wand_intro.
    unfold subseteqE.
    unfold assert_entails.
    intros.
    unfold assert_holds.
    unfold assert_expr.
    eexists.
    split. {
      econstructor.
      - econstructor.
        + apply lockset_empty_valid.
        + constructor.
          constructor.
          constructor.
          assumption.
      - constructor.
        constructor.
      - constructor.
        constructor.
    }
    simpl.
    rewrite option_guard_True; [|reflexivity].
    simpl.
    reflexivity.
  }
  eapply ax_expr_weaken_pre. {
    apply assert_sep_preserving. reflexivity.
    eapply assert_Prop_True.
    apply assert_stack_typed.
  }
  eapply ax_expr_weaken_pre. {
    apply (commutative (★)%A).
  }
  eapply ax_expr_weaken_pre. {
    rewrite <- (associative (★)%A).
    reflexivity.
  }
  apply ax_expr_Prop_pre; intros Hstore_typed.
  eapply ax_expr_weaken_pre. {
    rewrite (commutative (★)%A).
    reflexivity.
  }
  apply ax_assign with
    (Q1:=λ ν, (var i ⇓ ν ∧ emp)%A)
    (Q2:=λ ν, (⌜ν = inr (intV{sintT} z) ∧ int_typed z sintT⌝ ★ assert_stack st)%A)
    (μ:=false)
    (γ:=perm_full)
    (τ:=sintT%T).
  + reflexivity.
  + intros.
    rewrite (commutative (★)%A).
    rewrite <- (associative (★)%A).
    apply assert_Prop_intro_l. intros. destruct H1 as [H1 Hz].
    injection H1; clear H1; intros; subst.
    rewrite (commutative (★)%A).
    apply assert_exist_intro with (x:=intV{sintT} z).
    apply assert_exist_intro with (x:=intV{sintT} z).
    apply assert_and_intro.
    * clear H0 Hstore_typed.
      revert st i H.
      induction st.
      -- simpl; intros; lia.
      -- Opaque perm_full.
         rename a into mv.
         simpl; intros.
         destruct i.
         ++ clear IHst H.
            simpl.
            assert (var_points_to 0 mv ⊆{Γ,δ} var 0 ↦{false,perm_full} - : sintT%BT)%A. {
              destruct mv.
              - eapply assert_exist_intro.
                simpl. reflexivity.
              - reflexivity.
            }
            rewrite H.
            rewrite assert_singleton_l_.
            rewrite (commutative (★)%A).
            rewrite <- (associative (★)%A).
            rewrite assert_exist_sep.
            apply assert_exist_elim; intro p'.
            rewrite (associative (★)%A).
            rewrite (commutative (★)%A).
            rewrite <- (associative (★)%A).
            rewrite (associative (★)%A).
            rewrite assert_eval_functional'.
            rewrite <- (associative (★)%A).
            apply assert_Prop_intro_l. intro Hp'. injection Hp'; clear Hp'; intros; subst p'.
            rewrite (associative (★)%A).
            rewrite (commutative (★)%A).
            rewrite (associative (★)%A).
            rewrite (commutative (★)%A).
            apply assert_sep_preserving; [reflexivity|].
            rewrite (commutative (★)%A).
            apply assert_wand_intro.
            rewrite assert_Prop_l. 2:{ tauto. }
            rewrite (commutative (★)%A).
            rewrite (associative (★)%A).
            rewrite <- assert_unlock_sep.
            apply assert_sep_preserving.
            ** rewrite (commutative (★)%A).
               rewrite assert_singleton_l_2.
               apply assert_unlock_singleton.
               reflexivity.
            ** apply assert_stack_unlock_indep.
         ++ simpl.
            rewrite <- assert_unlock_sep.
            rewrite <- assert_wand_sep.
            rewrite <- assert_wand_sep.
            rewrite (commutative (★)%A).
            rewrite <- (associative (★)%A).
            rewrite (commutative (★)%A) with (x:=(% p ↦{false,perm_full} - : sintT%BT)%A).
            rewrite <- (associative (★)%A).
            rewrite assert_Prop_l. 2:{ tauto. }
            rewrite <- (associative (★)%A).
            apply assert_sep_preserving; [apply var_points_to_unlock_indep|].
            rewrite (commutative (★)%A).
            rewrite (commutative (★)%A) with (y:=(% p ↦{false,perm_full} - : sintT%BT)%A).
            assert (
              ((var (S i) ⇓ inl p ∧ emp) ★ assert_stack st↑)%A ⊆{Γ,δ}
              (((var i ⇓ inl p ∧ emp) ★ assert_stack st)↑)%A). {
              rewrite assert_lift_sep.
              rewrite assert_lift_and.
              rewrite stack_indep.
              apply assert_sep_preserving; [|reflexivity].
              apply assert_and_intro.
              - apply assert_and_elim_l.
                rewrite <- assert_lift_eval.
                reflexivity.
              - apply assert_and_elim_r; reflexivity.
            }
            rewrite H0.
            rewrite IHst.
            ** rewrite assert_lift_sep.
               rewrite assert_lift_wand.
               rewrite assert_Prop_l. 2:{ tauto. }
               rewrite assert_lift_unlock.
               rewrite assert_lift_singleton.
               rewrite assert_lift_singleton_.
               reflexivity.
            ** lia.
    * apply assert_wand_intro.
      simpl.
      rewrite eval_sound with (1:=H0).
      assert (forall P Q, P ⊆{Γ,δ} Q -> P ⊆{Γ,δ} (Q ∧ Q)%A). {
        intros.
        apply assert_and_intro; assumption.
      }
      apply H1; clear H1.
      rewrite (right_id _ (★)%A).
      rewrite <- (left_id _ (★)%A) with (x:=(cast{sintT%BT} (# intV{sintT} z) ⇓ inr (intV{sintT} z))%A).
      apply assert_sep_preserving.
      -- apply assert_and_elim_r; reflexivity.
      -- rewrite assert_eval_int_typed.
         apply assert_Prop_intro_l. intro Hz'.
         eapply assert_eval_int_cast'.
         ++ rewrite <- assert_int_typed_eval; trivial.
         ++ apply int_cast_ok_self; apply Hz'.
         ++ apply int_cast_self; assumption.
  + apply ax_expr_exist_pre. intro p.
    apply ax_expr_base with (ν:=inl p).
    apply assert_and_intro; [reflexivity|].
    apply assert_and_elim_l; reflexivity.
  + apply ax_expr_base with (ν:=inr (intV{sintT} z)).
    rewrite assert_Prop_l. 2:{ split. reflexivity. eapply eval_typed; eassumption. }
    apply assert_and_intro; [reflexivity|].
    rewrite eval_sound with (1:=H0) at 1.
    reflexivity.
- eapply ax_comp with (P':=assert_stack st').
  + eapply ax_stmt_weaken.
    Focus 8. {
      apply IHexec1.
    } Unfocus.
    * intros; unfold R.
      apply assert_exist_elim; intro st'0.
      apply assert_Prop_intro_r.
      intros.
      destruct H1 as [? [? [? ?]]].
      discriminate.
    * trivial.
    * trivial.
    * trivial.
    * trivial.
    * trivial.
    * apply assert_exist_elim; intro st'0.
      apply assert_Prop_intro_r.
      intros.
      injection H1; clear H1; intros; subst.
      reflexivity.
  + eapply ax_stmt_weaken.
    Focus 8. {
      apply IHexec2.
    } Unfocus.
    * intros.
      unfold R.
      rewrite exec_onormal_length_st with (1:=H); reflexivity.
    * trivial.
    * trivial.
    * trivial.
    * trivial.
    * trivial.
    * trivial.
- eapply ax_ret with (Q1:=fun ν =>
    (∃ st', assert_stack st' ★ ⌜ ν = inr (intV{sintT} z) ∧ length st' = length st ⌝)%A).
  + intros.
    apply assert_exist_elim; intro st'.
    unfold R.
    rewrite assert_unlock_exists.
    apply assert_exist_intro with (x:=st').
    apply assert_Prop_intro_r. intros [? ?].
    injection H0; clear H0; intros; subst.
    rewrite assert_Prop_r.
    * apply assert_stack_unlock_indep'.
    * intuition.
      eexists; tauto.
  + apply ax_expr_base with (ν:=inr (intV{sintT} z)).
    apply assert_and_intro.
    * apply assert_exist_intro with (x:=st).
      rewrite assert_Prop_r; [reflexivity|].
      tauto.
    * rewrite eval_sound with (1:=H).
      rewrite assert_eval_int_typed'.
      apply assert_Prop_intro_l. intros.
      rewrite <- assert_eval_int_cast' with (τi:=sintT%IT) (σi:=sintT%IT) at 1.
      -- reflexivity.
      -- reflexivity.
      -- apply int_cast_ok_self; assumption.
      -- apply int_cast_self; assumption.
- eapply ax_stmt_weaken_post. 2:{ apply ax_skip. }
  apply assert_exist_intro with (x:=st).
  apply assert_Prop_r.
  reflexivity.
- eapply ax_if with
    (P':=(λ ν, assert_stack st ★ ⌜ ν = inr (intV{sintT} z) ⌝)%A)
    (P1:=(assert_stack st ★ ⌜ z ≠ 0%Z ⌝)%A)
    (P2:=(assert_stack st ★ ⌜ z = 0%Z ⌝)%A).
  + intros.
    apply assert_Prop_intro_r; intros.
    injection H1; clear H1; intros; subst.
    eapply assert_exist_intro.
    eapply transitivity.
    apply assert_Prop_True.
    apply assert_stack_typed.
    apply assert_Prop_intro_l.
    intros.
    eapply assert_eval_int_unop'.
    * apply assert_int_typed_eval.
      eapply eval_typed; eassumption.
    * reflexivity.
    * constructor.
    * reflexivity.
  + intros.
    rewrite <- assert_unlock_sep.
    rewrite <- unlock_indep.
    rewrite <- assert_stack_unlock_indep'.
    apply assert_Prop_intro_r. intros.
    injection H2; clear H2; intros; subst.
    apply assert_Prop_r.
    intro.
    elim H1.
    subst.
    constructor.
  + intros.
    rewrite <- assert_unlock_sep.
    rewrite <- unlock_indep.
    rewrite <- assert_stack_unlock_indep'.
    apply assert_Prop_intro_r. intros.
    injection H2; clear H2; intros; subst.
    apply assert_Prop_r.
    inversion H1; clear H1; subst.
    reflexivity.
  + apply ax_expr_base with (ν:=inr (intV{sintT} z)).
    apply assert_and_intro.
    * apply assert_Prop_r.
      reflexivity.
    * apply eval_sound; assumption.
  + rewrite (commutative (★))%A.
    apply ax_stmt_Prop_pre; try (intros; apply assert_False_elim).
    intros.
    apply Z.eqb_neq in H1.
    rewrite H1 in IHexec.
    apply IHexec.
  + rewrite (commutative (★))%A.
    apply ax_stmt_Prop_pre; try (intros; apply assert_False_elim).
    intros.
    subst.
    rewrite Z.eqb_refl in IHexec.
    apply IHexec.
Qed.

Require Export ch2o.core_c.restricted_smallstep.

Lemma body_returns_call_returns v s f S0 S:
  Γ\ δ\ [] ⊢ₛ S0 ⇒* S →
  ∀ k ϕ m,
  S0 = State (k ++ [CParams f []]) ϕ m →
  (∀ S,
   Γ\ δ\ [] ⊢ₛ State k ϕ m ⇒* S →
   red (rcstep Γ δ []) S ∨
   ∃ m',
   S = State [] (Stmt (⇈ v) s) m') →
  red (rcstep Γ δ []) S ∨
  ∃ m',
  S = State [] (Return f v) m'.
Proof.
induction 1.
- intros; subst.
  destruct (H0 (State k ϕ m)) as [Hred|[m' Hm']].
  + constructor.
  + left.
    apply rcred_app.
    assumption.
  + injection Hm'; clear Hm'; intros; subst.
    left.
    econstructor.
    econstructor.
- intros; subst.
  destruct (H2 (State k ϕ m)) as [Hred|[m' Hm']].
  + constructor.
  + destruct y as [k'long ϕ' m'].
    assert (suffix_of [CParams f []] k'long). {
      apply cstep_app_suffix_of with (1:=Hred) (2:=H).
    }
    destruct H1 as [k' Hk']; subst.
    eapply IHrtc. reflexivity.
    intros.
    apply H2.
    apply rtc_l with (2:=H1).
    apply rcstep_app_inv with (1:=H).
  + injection Hm'; clear Hm'; intros; subst.
    simpl in H.
    inversion H; subst.
    * simpl in H0.
      inversion H0; subst.
      -- right. eexists; reflexivity.
      -- inversion H1.
    * inversion H7.
Qed.

Lemma rcsteps_csteps S0 S:
  Γ\ δ\ [] ⊢ₛ S0 ⇒* S →
  Γ\ δ ⊢ₛ S0 ⇒* S.
Proof.
induction 1.
- constructor.
- apply rtc_l with (2:=IHrtc).
  apply rcstep_cstep with (1:=H).
Qed.

Lemma cmap_empty_valid: ✓{Γ} (∅: mem K).
Proof.
split. {
  apply memenv_empty_valid.
}
split. {
  intros.
  simpl in H.
  rewrite lookup_empty in H; discriminate.
}
intros.
simpl in H.
rewrite lookup_empty in H; discriminate.
Qed.

Theorem exec_sound (s: stmt K) z S f:
  ✓ Γ →
  ✓{Γ,'{∅}} δ →
  (Γ, '{∅}, []) ⊢ s : (true, Some sintT%T) →
  exec [] s (oreturn z) →
  Γ\ δ\ [] ⊢ₛ State [CParams f []] (Stmt ↘ s) ∅ ⇒* S →
  red (rcstep Γ δ []) S ∨
  ∃ m,
  S = State [] (Return f (intV{sintT} z)) m.
Proof.
intros.
eapply body_returns_call_returns with (1:=H3) (k:=[]). reflexivity.
clear S H3.
intros.
apply rcsteps_csteps in H3.
destruct ax_stmt_adequate with (cmτ:=(true, Some sintT%T): rettype K) (Q:=λ v, (⌜ v = intV{sintT} z ⌝ ★ True)%A) (7:=H3) as [[n' [m' [? ?]]] | [[n' [m' [v [? ?]]]] | ?]]; try assumption.
- apply cmap_empty_valid.
- apply mem_locks_empty.
- eapply ax_stmt_weaken.
  8: apply exec_sound_lemma with (1:=H2).
  + intros. unfold R.
    apply assert_exist_elim; intro st'.
    apply assert_Prop_intro_r; intros.
    destruct H4 as [? [? [? ?]]].
    rewrite assert_Prop_l.
    * apply assert_True_intro.
    * congruence.
  + intros.
    reflexivity.
  + intros; reflexivity.
  + intros; reflexivity.
  + intros; reflexivity.
  + rewrite cmap_erase_empty.
    simpl.
    intro; intros.
    unfold assert_eq_mem in H10; simpl in H10.
    subst.
    unfold assert_Prop; simpl.
    tauto.
  + apply assert_exist_elim; intro st'.
    apply assert_Prop_intro_r; intros.
    discriminate.
- simpl in H5.
  destruct H5 as [? [? [? [? [[? ?] ?]]]]].
  discriminate.
- subst.
  right.
  eexists m'.
  destruct H5 as [? [? [? [? [[? ?] ?]]]]].
  subst.
  reflexivity.
- left.
  inversion H4.
  econstructor.
  apply cstep_rcstep with (1:=H5).
Qed.

End Soundness.
