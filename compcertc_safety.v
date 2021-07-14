From Coq Require Export ZArith Utf8.
From compcert Require Export Integers Values Csyntax Smallstep Csem.

Inductive compcertc_final_state(Q: Z → Prop): state → Prop :=
  compcertc_final_state_intro i m:
  Q (Int.signed i) → compcertc_final_state Q (Returnstate (Vint i) Kstop m).

Definition compcertc_safe_state(Q: Z → Prop)(p: program)(s: state): Prop :=
  ∀ n trace s',
  starN (Smallstep.step (Csem.semantics p)) (Smallstep.globalenv (Csem.semantics p)) n s trace s' →
  compcertc_final_state Q s' ∨
  ∃ trace' s'', Step (Csem.semantics p) s' trace' s''.

Inductive compcertc_safe_program(Q: Z → Prop)(p: program): Prop :=
  compcertc_safe_program_intro s0:
  Csem.initial_state p s0 → compcertc_safe_state Q p s0 → compcertc_safe_program Q p.