From Coq Require Export String.
From ch2o Require Export smallstep.

Section Program.

Local Open Scope string_scope.

Context {K} {HK: Env K} {HK': EnvSpec K} (Γ: env K)(δ: funenv K).

Inductive ch2o_final_state(Q: Z → Prop): state K → Prop :=
  ch2o_final_state_intro z m:
  Q z →
  ch2o_final_state Q (State [] (Return "main" (intV{sintT} z)) m).

Definition ch2o_program_safe(Q: Z → Prop) :=
  ∀ S,
  Γ \ δ ⊢ₛ State [] (Call "main" []) ∅ ⇒* S →
  ch2o_final_state Q S \/
  ∃ S', Γ \ δ ⊢ₛ S ⇒ S'.