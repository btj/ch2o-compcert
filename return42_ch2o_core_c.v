From ch2o_compcert Require Export ch2o_lp64 return42_ch2o.
From ch2o Require Export stringmap.

Local Open Scope string_scope.

Definition alloc_program_result: frontend_state K.
Proof.
set (a:=alloc_program (K:=K) decls ∅).
assert (match a with inl _ => False | inr _ => True end). { exact I. }
destruct a. { elim H. }
destruct p.
exact f.
Defined.

Definition Γ: env K := to_env alloc_program_result.
Definition δ: funenv K := to_funenv alloc_program_result.
Definition m0: mem K := to_mem alloc_program_result.
Definition S0 := initial_state m0 "main" [].

Goal env_t Γ = ∅.
Proof.
reflexivity.
Qed.

Goal stringmap_to_list (env_f Γ) = [("main", ([], sintT%T))].
reflexivity.
Qed.

Goal stringmap_to_list δ = [("main", ret (cast{sintT%T} (# intV{sintT} 42)))].
Proof.
reflexivity.
Qed.

Lemma δ_main: δ !! ("main": funname) = Some (ret (cast{sintT%T} (# intV{sintT} 42)) : stmt K).
Proof.
reflexivity.
Qed.

Goal m0 = ∅.
Proof.
reflexivity.
Qed.

Goal S0 = State [] (Call "main" []) m0.
Proof.
reflexivity.
Qed.