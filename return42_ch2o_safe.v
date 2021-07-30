From ch2o_compcert Require Export return42_ch2o_core_c ch2o_safety.
From ch2o Require Export restricted_smallstep.

Local Open Scope string_scope.

Theorem return42_ch2o_safe: ch2o_safe_program Γ δ (λ z, z = 42).
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
inversion H1; clear H1; subst. {
  right.
  eexists.
  apply cstep_expr with (E:=CReturnE: statements.esctx_item K).
}
inv_rcstep.
inversion H0; clear H0; subst. {
  right.
  eexists.
  apply cstep_expr_head with (E:=[]).
  constructor.
  constructor; (unfold int_lower || unfold int_upper); simpl; lia.
}
inv_rcstep. 2:{
  elim H1; clear H1.
  econstructor.
  econstructor.
  constructor; (unfold int_lower || unfold int_upper); simpl; lia.
}
inv_ehstep.
clear H7.
simpl in H1.
unfold int_cast in H1. unfold arch_int_env in H1.
unfold int_pre_cast in H1. simpl in H1.
inversion H1; clear H1; subst. {
  right.
  eexists.
  econstructor.
}
Opaque mem_unlock.
inv_rcstep.
rewrite mem_unlock_empty in H0.
inversion H0; clear H0; subst. {
  right.
  eexists.
  econstructor.
}
inv_rcstep.
inversion H1; clear H1; subst. {
  left.
  constructor.
  reflexivity.
}
inv_rcstep.
Qed.
