From ch2o_compcert Require Export return42_ch2o_safe return42_csyntaxgen ch2o_compcertc_lp64 compcertc_compiler.

Lemma return42_compcertc_safe: compcertc_safe_program (λ z, z = 42) prog.
Proof.
apply soundness with (2:=return42_ch2o_safe).
econstructor.
- apply δ_main.
- apply init_mem_ok.
  reflexivity.
- reflexivity.
- reflexivity.
- constructor.
  constructor.
  constructor; (unfold int_lower || unfold int_upper); simpl; lia.
Qed.

Theorem return42_asm_safe tp:
  transf_c_program prog = OK tp →
  asm_program_satisfies_spec tp (satisfies_postcondition (λ z, z = 42)).
Proof.
intros.
apply transf_c_program_safe with (1:=H).
apply return42_compcertc_safe.
Qed.