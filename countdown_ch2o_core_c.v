From ch2o_compcert Require Export ch2o_lp64 countdown_ch2o.
From ch2o Require Import stringmap frontend_sound.

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

(*
Compute stringmap_to_list δ.
*)

Infix "<" := (EBinOp (CompOp LtOp))
  (at level 70) : expr_scope.

Goal stringmap_to_list δ = [
  ("main",
   local{sintT} (
     var 0 ::= cast{sintT%T} (# intV{sintT} 32767) ;;
     catch (
       loop (
         if{# intV{sintT} 0 < load (var 0)} skip else throw 0 ;;
         catch (
           ! (cast{voidT%T} (var 0 ::= load (var 0) - # intV{sintT} 1))
         )
       )
     ) ;;
     ret (cast{sintT%T} (load (var 0)))
   ) : stmt K
  )
].
Proof.
reflexivity.
Qed.

Lemma δ_main: δ !! ("main": funname) = Some (
   local{sintT} (
     var 0 ::= cast{sintT%T} (# intV{sintT} 32767) ;;
     catch (
       loop (
         if{# intV{sintT} 0 < load (var 0)} skip else throw 0 ;;
         catch (
           ! (cast{voidT%T} (var 0 ::= load (var 0) - # intV{sintT} 1))
         )
       )
     ) ;;
     ret (cast{sintT%T} (load (var 0)))
   ) : stmt K).
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

Lemma alloc_program_eq: alloc_program decls empty = mret () alloc_program_result.
Proof.
reflexivity.
Qed.

Lemma Γ_valid: ✓ Γ.
Proof.
apply alloc_program_valid with (1:=alloc_program_eq).
Qed.

Lemma δ_valid: ✓{Γ,'{m0}} δ.
Proof.
apply alloc_program_valid with (1:=alloc_program_eq).
Qed.

Lemma m0_valid: ✓{Γ} m0.
apply alloc_program_valid with (1:=alloc_program_eq).
Qed.
