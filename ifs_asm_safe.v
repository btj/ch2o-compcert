From ch2o_compcert Require Export ifs_ch2o_safe ifs_csyntaxgen_simplified ch2o_compcertc_lp64 compcertc_compiler.

Lemma ifs_compcertc_safe: compcertc_safe_program (λ z, z = 2) prog.
Proof.
apply soundness with (2:=ifs_ch2o_safe).
econstructor.
- apply δ_main.
- apply init_mem_ok.
  reflexivity.
- reflexivity.
- reflexivity.
- repeat constructor; (unfold int_lower || unfold int_upper); simpl; lia.
Qed.

Theorem ifs_asm_safe tp:
  transf_c_program prog = OK tp →
  asm_program_satisfies_spec tp (satisfies_postcondition (λ z, z = 2)).
Proof.
intros.
apply transf_c_program_safe with (1:=H).
apply ifs_compcertc_safe.
Qed.