From ch2o_compcert Require Export return_divs_ch2o_core_c ch2o_safety bigstep_soundness.
From ch2o Require Export restricted_smallstep.

Local Open Scope string_scope.

Theorem return_divs_ch2o_safe: ch2o_safe_program Γ δ (λ z, z = 2).
Proof.
intro; intros.
apply csteps_rcsteps in H.
inv_rcsteps H. {
  right.
  eexists. econstructor.
  - apply δ_main.
  - constructor.
  - reflexivity.
}
inversion H; clear H; subst.
destruct os; simpl in H8; try discriminate H8; clear H8.
clear H7.
rewrite δ_main in H6; injection H6; clear H6; intros; subst.
simpl in H1.
destruct exec_sound with (1:=Γ_valid) (2:=δ_valid) (5:=H1) (z:=((17 ÷ 2) ÷ (15 ÷ 5))%Z). {
  apply type_check_sound.
  - simpl.
    apply Γ_valid.
  - reflexivity.
} {
  assert (17 ÷ 2 = 8)%Z. reflexivity.
  assert (15 ÷ 5 = 3)%Z. reflexivity.
  assert (8 ÷ 3 = 2)%Z. reflexivity.
  repeat constructor; try (unfold int_lower || unfold int_upper); simpl; try lia.
  rewrite H; rewrite H0; rewrite H2.
  lia.
} {
  right.
  destruct H as [S'' H].
  exists S''.
  apply rcstep_cstep.
  assumption.
}
destruct H as [m H]; subst.
left.
constructor.
reflexivity.
Qed.
