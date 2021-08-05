From ch2o_compcert Require Export ch2o_safety bigstep_soundness.

Section Program.

Context {K} {HK: Env K} {HK': EnvSpec K} (Γ: env K) (δ: funenv K).

Lemma ch2o_safe_program_bigstep s z (Q: Z → Prop):
  ✓ Γ →
  ✓{Γ,'{∅}} δ →
  δ !! ("main"%string : funname) = Some s →
  type_check (Γ, '{∅}, []) s = Some (true, Some sintT%T) →
  exec [] s (oreturn z) →
  Q z →
  ch2o_safe_program Γ δ Q.
Proof.
intros HΓ_valid Hδ_valid Hδ Hs_well_typed Hexec HQ.
intro; intros.
apply csteps_rcsteps in H.
inv_rcsteps H. {
  right.
  eexists. econstructor.
  - eassumption.
  - constructor.
  - reflexivity.
}
inversion H; clear H; subst.
destruct os; simpl in H8; try discriminate H8; clear H8.
clear H7.
rewrite Hδ in H6; injection H6; clear H6; intros; subst.
simpl in H1.
edestruct exec_sound with (1:=HΓ_valid) (2:=Hδ_valid) (5:=H1). {
  apply type_check_sound.
  - simpl.
    apply HΓ_valid.
  - assumption.
} {
  eassumption.
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
assumption.
Qed.

End Program.