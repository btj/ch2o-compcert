From ch2o_compcert Require Export locals_example_ch2o_safe locals_example_csyntaxgen_simplified ch2o_compcertc_lp64 compcertc_compiler.

Lemma locals_example_compcertc_safe: compcertc_safe_program (λ z, z = 2) prog.
Proof.
apply soundness with (3:=locals_example_ch2o_safe). apply Γ_valid.
eapply program_equiv_intro with (ê:=[_z; _y; _x]).
- apply δ_main.
- apply init_mem_ok.
  reflexivity.
- reflexivity.
- simpl.
  case_eq (Coqlib.list_norepet_dec Pos.eq_dec [_x; _y; _z]); intros.
  + assumption.
  + discriminate.
- reflexivity.
- repeat constructor; (unfold int_lower || unfold int_upper); simpl; lia.
Qed.

Theorem locals_example_asm_safe tp:
  transf_c_program prog = OK tp →
  asm_program_satisfies_spec tp (satisfies_postcondition (λ z, z = 2)).
Proof.
intros.
apply transf_c_program_safe with (1:=H).
apply locals_example_compcertc_safe.
Qed.