From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats Values AST Ctypes Cop Csyntax Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "macos".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "countdown.c".
End Info.

Definition _main : ident := $"main".
Definition _x : ident := $"x".

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_x, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sdo (Eassign (Evar _x tint) (Eval (Vint (Int.repr 32767)) tint) tint))
    (Ssequence
      (Swhile
        (Ebinop Olt (Eval (Vint (Int.repr 0)) tint)
          (Evalof (Evar _x tint) tint) tint)
        (Sdo (Eassign (Evar _x tint)
               (Ebinop Osub (Evalof (Evar _x tint) tint)
                 (Eval (Vint (Int.repr 1)) tint) tint) tint)))
      (Sreturn (Some (Evalof (Evar _x tint) tint)))))
  (Sreturn (Some (Eval (Vint (Int.repr 0)) tint))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: nil).

Definition prog : Csyntax.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


