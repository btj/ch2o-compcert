Require Export ch2o.axiomatic.assertions.

Section Program.

Context `{EnvSpec K} (Γ: env K) (δ: funenv K).

Lemma assert_wand_sep P Q R:
  ((P ★ (Q -★ R)) ⊆{Γ,δ} (Q -★ (P ★ R)))%A.
Proof.
apply assert_wand_intro.
rewrite <- (associative (★)%A).
apply assert_sep_preserving; [reflexivity|].
apply assert_wand_elim.
Qed.

Lemma emp_dup P:
  ((P ∧ emp)%A ⊆{Γ,δ} ((P ∧ emp) ★ (P ∧ emp)))%A.
Proof.
unfold subseteqE.
unfold assert_entails.
intros.
unfold assert_and in *.
unfold assert_sep in *.
simpl in *.
destruct H7.
destruct H8.
subst.
exists ∅. exists ∅.
split.
- rewrite sep_right_id.
  + reflexivity.
  + apply sep_empty_valid.
- split.
  + rewrite sep_disjoint_list_double.
    apply sep_disjoint_empty_l.
    apply sep_empty_valid.
  + tauto.
Qed.

Lemma assert_lift_unlock P:
  (P ◊ ↑ ⊆{Γ,δ} P ↑ ◊)%A.
Proof.
unfold subseteqE.
unfold assert_entails.
unfold assert_unlock.
unfold assert_lift.
simpl.
intros.
assumption.
Qed.

Lemma assert_lift_eval e ν:
  (e↑ ⇓ ν ≡{Γ,δ} (e ⇓ ν)↑)%A.
Proof.
unfold equivE.
unfold assert_equiv.
split.
- unfold subseteqE.
  unfold assert_entails.
  unfold assert_expr.
  unfold assert_lift.
  simpl.
  intros.
  destruct H7 as [τlr [Ht He]].
  rewrite expr_eval_lift in He.
  apply expr_typed_lift in Ht.
  exists τlr.
  split; [|assumption].
  destruct ρ; assumption.
- unfold subseteqE.
  unfold assert_entails.
  unfold assert_expr.
  unfold assert_lift.
  simpl.
  intros.
  destruct H7 as [τlr [Ht He]].
  exists τlr.
  split.
  + apply expr_typed_lift.
    destruct ρ; assumption.
  + rewrite expr_eval_lift.
    destruct ρ; assumption.
Qed.

Lemma assert_eval_functional e ν1 ν2:
  (((e ⇓ ν1 ∧ emp) ★ (e ⇓ ν2 ∧ emp)) ⊆{Γ,δ} ⌜ν1 = ν2⌝)%A.
Proof.
unfold subseteqE.
unfold assert_entails.
unfold assert_sep.
unfold assert_and.
unfold assert_expr.
unfold assert_Prop.
intros.
simpl in *.
destruct H7 as [m1 [m2 [Hm [Hdisj [[[τlr1 [Ht1 He1]] [_ Hm1]] [[τlr2 [Ht2 He2]] [_ Hm2]]]]]]].
subst.
split.
- congruence.
- rewrite sep_left_id.
  reflexivity.
  apply sep_empty_valid.
Qed.

Lemma assert_eval_functional' e ν1 ν2:
  (((e ⇓ ν1 ∧ emp) ★ (e ⇓ ν2 ∧ emp)) ⊆{Γ,δ} (⌜ν1 = ν2⌝ ★ (e ⇓ ν1 ∧ emp)))%A.
Proof.
rewrite emp_dup at 1.
rewrite (commutative (★)%A).
rewrite (associative (★)%A).
apply assert_sep_preserving; [|reflexivity].
rewrite (commutative (★)%A).
apply assert_eval_functional.
Qed.

End Program.
