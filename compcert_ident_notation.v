From compcert Require Import Clightdefs.

(*
This module cherry-picks some elements from Clightdefs that are useful
when defining CompCert C programs.
*)

Definition tint := tint.

Notation "$ s" := (ltac:(ident_of_string s))
                  (at level 1, only parsing) : string_scope.
