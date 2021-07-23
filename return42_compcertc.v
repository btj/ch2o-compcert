From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Values Cop Csyntax Errors.
From ch2o_compcert Require Import compcert_ident_notation.

Import List.ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition _main : ident := $"main".

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := [];
  fn_vars := [];
  fn_body := Sreturn (Some (Eval (Vint (Int.repr 42)) tint))
|}.

Definition composites: list composite_definition := [].

Definition prog : Csyntax.program.
Proof.
set (e:=build_composite_env composites).
assert (match e with OK _ => True | Error _ => False end). { exact I. }
case_eq e; intros; rewrite H0 in H; try tauto.
exact (
  {| prog_defs := [(_main, Gfun (Internal f_main))];
     prog_public := [_main];
     prog_main := _main;
     prog_types := composites;
     prog_comp_env := c;
     prog_comp_env_eq := H0 |}
).
Defined.
