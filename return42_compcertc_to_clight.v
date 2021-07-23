From Coq Require Export ZArith.
From ch2o_compcert Require Export compcert_ident_notation return42_compcertc.
From compcert Require Export Integers AST Errors Ctypes SimplExpr.
From compcert Require Import Clight.

Import List.ListNotations.

Local Open Scope Z_scope.

Definition f_main' :=
  {| fn_return := tint;
     fn_callconv := cc_default;
     fn_params := [];
     fn_vars := [];
     fn_temps := [];
     fn_body :=
       Ssequence
         Sskip
         (Sreturn (Some (Econst_int (Int.repr 42%Z) tint))) |}.

Goal transl_program prog =
  OK
  {| prog_defs := [(_main, Gfun (Internal f_main'))];
     prog_public := [_main];
     prog_main := _main;
     prog_types := [];
     prog_comp_env := prog.(prog_comp_env);
     prog_comp_env_eq := prog.(prog_comp_env_eq) |}.
Proof.
reflexivity.
Qed.