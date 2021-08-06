From ch2o_compcert Require Export stores.
From ch2o_compcert Require Export assertions_lemmas.

Section Program.

Context `{EnvSpec K} (Γ: env K) (δ: funenv K).

Definition var_points_to i mv: assert K :=
  match mv with
    None =>
    var i ↦{false, perm_full} - : sintT%BT
  | Some z =>
    var i ↦{false, perm_full} (# intV{sintT} z) : sintT%BT
  end.

Lemma var_points_to_typed i mv:
  var_points_to i mv ⊆{Γ,δ} (⌜ store_value_typed mv ⌝ ★ True)%A.
Proof.
destruct mv; simpl.
- apply assert_singleton_int_typed.
- rewrite assert_Prop_l.
  + apply assert_True_intro.
  + constructor.
Qed.

Fixpoint assert_stack (st: store): assert K :=
  match st with
    [] => emp
  | mv::st =>
    var_points_to 0 mv ★ assert_stack st ↑
  end.

Lemma assert_stack_typed st:
  assert_stack st ⊆{Γ,δ} (⌜ store_typed st ⌝ ★ True)%A.
Proof.
induction st.
- rewrite assert_Prop_l.
  + apply assert_True_intro.
  + constructor.
- simpl.
  eapply transitivity.
  + apply assert_sep_preserving.
    apply var_points_to_typed.
    rewrite IHst.
    reflexivity.
  + rewrite <- (associative (★)%A).
    apply assert_Prop_intro_l.
    intro.
    rewrite assert_lift_sep.
    rewrite stack_indep.
    rewrite stack_indep.
    rewrite (commutative (★)%A).
    rewrite <- (associative (★)%A).
    apply assert_Prop_intro_l.
    intro.
    rewrite assert_Prop_l.
    * apply assert_True_intro.
    * constructor; assumption.
Qed.

Lemma assert_stack_var st i:
  i < length st ->
  assert_stack st ⊆{Γ,δ}
  ((∃p, var i ⇓ inl p ∧ emp) ★ assert_stack st)%A.
Proof.
revert i.
induction st; simpl; intros.
- lia.
- destruct i.
  + rewrite (associative (★)%A).
    apply assert_sep_preserving; [|reflexivity].
    rename a into mv.
    destruct mv.
    * simpl.
      rewrite assert_singleton_l at 1.
      apply assert_exist_elim; intro p.
      rewrite assert_exist_sep.
      apply assert_exist_intro with (x:=p).
      rewrite emp_dup at 1.
      rewrite <- (associative (★)%A).
      apply assert_sep_preserving; [reflexivity|].
      rewrite assert_singleton_l_2.
      reflexivity.
    * simpl.
      rewrite assert_singleton_l_ at 1.
      apply assert_exist_elim; intro p.
      rewrite assert_exist_sep.
      apply assert_exist_intro with (x:=p).
      rewrite emp_dup at 1.
      rewrite <- (associative (★)%A).
      apply assert_sep_preserving; [reflexivity|].
      rewrite assert_singleton_l_2_.
      reflexivity.
  + rewrite (commutative (★)%A).
    rewrite (associative (★)%A).
    apply assert_sep_preserving; [|reflexivity].
    rewrite IHst with (i:=i) at 1; [|lia].
    rewrite assert_lift_sep.
    rewrite assert_lift_exists.
    apply assert_sep_preserving; [|reflexivity].
    apply assert_exist_elim; intro p.
    apply assert_exist_intro with (x:=p).
    rewrite assert_lift_and.
    rewrite stack_indep.
    apply assert_and_intro.
    * apply assert_and_elim_l.
      rewrite <- assert_lift_eval at 1.
      reflexivity.
    * apply assert_and_elim_r; reflexivity.
Qed.

Lemma assert_stack_load st i z:
  st !! i = Some (Some z) ->
  assert_stack st ⊆{Γ,δ} (load (var i) ⇓ inr (intV{sintT} z))%A.
Proof.
revert i.
induction st.
- discriminate.
- destruct i.
  + simpl; intros.
    injection H1; clear H1; intros; subst.
    rewrite <- assert_memext_l with (P:=(load (var 0) ⇓ inr (intV{sintT} z))%A) (Q:=(assert_stack st↑)%A).
    * apply assert_sep_preserving; try reflexivity.
      apply assert_singleton_eval.
      reflexivity.
    * auto with typeclass_instances.
  + simpl; intros.
    rewrite <- assert_memext_r with (Q:=var_points_to 0 a) (P:=(load (var (S i)) ⇓ inr (intV{sintT} z))%A); [|auto with typeclass_instances].
    apply assert_sep_preserving; [reflexivity|].
    rewrite IHst with (1:=H1).
    rewrite assert_lift_expr.
    reflexivity.
Qed.

Lemma var_points_to_unlock_indep i mv:
  (var_points_to i mv ⊆{Γ,δ} var_points_to i mv ◊)%A.
Proof.
destruct mv; unfold var_points_to.
* simpl.
  apply assert_singleton_unlock_indep.
  reflexivity.
* apply assert_exist_elim; intro v.
  rewrite assert_unlock_exists.
  apply assert_exist_intro with (x:=v).
  apply assert_singleton_unlock_indep.
  reflexivity.
Qed.

Lemma assert_stack_unlock_indep' st:
  assert_stack st ⊆{Γ,δ} (assert_stack st ◊)%A.
Proof.
revert Γ δ.
induction st; simpl; intros.
- rewrite <- unlock_indep.
  reflexivity.
- rewrite <- assert_unlock_sep.
  apply assert_sep_preserving.
  + rename a into mv.
    destruct mv; unfold var_points_to.
    * simpl.
      apply assert_singleton_unlock_indep.
      reflexivity.
    * apply assert_exist_elim; intro v.
      rewrite assert_unlock_exists.
      apply assert_exist_intro with (x:=v).
      apply assert_singleton_unlock_indep.
      reflexivity.
  + assert (UnlockIndep (assert_stack st)%A). exact IHst.
    apply unlock_indep.
Qed.

Lemma assert_stack_unlock_indep st:
  (assert_stack st↑)%A ⊆{Γ,δ} ((assert_stack st↑) ◊)%A.
Proof.
revert Γ δ.
induction st; simpl; intros.
- rewrite stack_indep.
  rewrite <- unlock_indep.
  reflexivity.
- rewrite assert_lift_sep.
  rewrite <- assert_unlock_sep.
  apply assert_sep_preserving.
  + rename a into mv.
    destruct mv; unfold var_points_to.
    * rewrite assert_lift_singleton.
      simpl.
      apply assert_singleton_unlock_indep.
      reflexivity.
    * rewrite assert_lift_exists.
      apply assert_exist_elim; intro v.
      rewrite assert_unlock_exists.
      apply assert_exist_intro with (x:=v).
      rewrite assert_lift_singleton.
      apply assert_singleton_unlock_indep.
      reflexivity.
  + assert (UnlockIndep (assert_stack st↑)%A). exact IHst.
    apply unlock_indep.
Qed.

End Program.
