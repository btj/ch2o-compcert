From ch2o_compcert Require Export locals_example_ch2o_core_c ch2o_safety_bigstep.
From ch2o Require Export restricted_smallstep.

Local Open Scope string_scope.

Theorem locals_example_ch2o_safe: ch2o_safe_program Γ δ (λ z, z = 2%Z).
Proof.
eapply ch2o_safe_program_bigstep with (1:=Γ_valid) (2:=δ_valid) (3:=δ_main) (4:=eq_refl) (6:=eq_refl).
assert (17 ÷ 2 = 8)%Z. reflexivity.
assert (15 ÷ 5 = 3)%Z. reflexivity.
assert (8 ÷ 3 = 2)%Z. reflexivity.
assert (2 = (17 ÷ 2) ÷ (15 ÷ 5))%Z. reflexivity.
rewrite H2 at 2.
repeat econstructor; try (unfold int_lower || unfold int_upper); simpl; lia.
Qed.
