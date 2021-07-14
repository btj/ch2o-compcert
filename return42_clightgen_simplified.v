From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Module Info.
  Definition version := "3.8".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "macosx".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "return42.c".
  Definition normalized := false.
End Info.

Definition _main : ident := $"main".

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
    Ssequence
      (Sreturn (Some (Econst_int (Int.repr 42) tint)))
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
|}.

Definition composites : list composite_definition := nil.

Definition global_definitions : list (ident * globdef fundef type) :=
  (_main, Gfun (Internal f_main)) :: nil.

Definition public_idents : list ident :=
  _main :: nil.

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.
