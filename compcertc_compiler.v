From Coq Require Export ZArith Utf8.
From compcert Require Export Integers Values Csyntax Errors Smallstep Csem Behaviors Compiler Complements.
From ch2o_compcert Require Export compcertc_safety.

Fixpoint satisfies_postcondition(Q: Z → Prop)(beh: program_behavior): Prop :=
  match beh with
  | Terminates t i => Q (Int.signed i)
  | Diverges t => True
  | Reacts t => True
  | Goes_wrong t => False
  end.

Lemma csem_initial_state_unique p s1 s2:
  Csem.initial_state p s1 →
  Csem.initial_state p s2 →
  s1 = s2.
Proof.
intros.
inversion H; clear H; subst.
inversion H0; clear H0; subst.
unfold ge, ge0 in *.
assert (b = b0). congruence. subst.
assert (f = f0). congruence. subst.
assert (m0 = m1). congruence. subst.
reflexivity.
Qed.

Lemma compcertc_safe_program_satisfies_postcondition Q p:
  compcertc_safe_program Q p →
  c_program_satisfies_spec p (satisfies_postcondition Q).
Proof.
intros.
intro beh.
intros.
destruct beh; simpl; try trivial.
- (* Terminates t i *)
  inversion H0; clear H0; subst.
  inversion H2; clear H2; subst.
  inversion H; clear H; subst.
  assert (s0 = s). apply (csem_initial_state_unique _ _ _ H0 H1). subst.
  apply star_starN in H4. destruct H4 as [n H4].
  apply H2 in H4.
  inversion H5; clear H5; subst.
  destruct H4.
  + inversion H; clear H; subst.
    assumption.
  + destruct H as [trace' [s'' H]].
    inversion H; clear H; subst.
    * inversion H3.
    * inversion H3.
- (* Goes_wrong *)
  inversion H0; clear H0; subst.
  + (* program_runs *)
    inversion H; clear H; subst.
    assert (s0 = s). apply (csem_initial_state_unique _ _ _ H0 H1). subst.
    inversion H2; clear H2; subst.
    apply star_starN in H4. destruct H4 as [n H4].
    apply H3 in H4. destruct H4.
    * inversion H; clear H; subst.
      apply (H6 i).
      constructor.
    * destruct H as [trace' [s'' H]].
      elim (H5 _ _ H).
  + (* program_goes_initialy_wrong *)
    inversion H; clear H; subst.
    elim (H2 _ H0).
Qed.

Theorem transf_c_program_safe Q p tp:
  transf_c_program p = OK tp →
  compcertc_safe_program Q p →
  asm_program_satisfies_spec tp (satisfies_postcondition Q).
Proof.
intros.
apply transf_c_program_preserves_spec with (1:=H). {
  intro; intros.
  destruct beh; try trivial.
  constructor.
}
apply compcertc_safe_program_satisfies_postcondition; assumption.
Qed.
