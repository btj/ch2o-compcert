From ch2o_compcert Require Export ch2o_safety compcertc_safety.
From ch2o Require Export stringmap types expressions statements architectures state.
(* We prove soundness for LP64 architectures. *)
From ch2o_compcert Require Export ch2o_lp64.
From compcert Require Export Csyntax Ctypes Globalenvs.

Section Program.

Local Open Scope string_scope.

Context (Γ: types.env K) (δ: funenv K) (p: Csyntax.program).

Inductive expr_equiv: expressions.expr K → Csyntax.expr → Prop :=
| expr_equiv_val_int z:
  int_typed z (sintT: int_type K) → (* TODO: Require the CH2O program to be well-typed instead? *)
  expr_equiv (EVal ∅ (inr (intV{sintT} z))) (Eval (Vint (Int.repr z)) (Tint I32 Signed noattr)).

Inductive stmt_equiv: stmt K → statement → Prop :=
| stmt_equiv_Return e ė:
  expr_equiv e ė →
  stmt_equiv (SReturn e) (Sreturn (Some ė))
.

Inductive program_equiv: Prop :=
| program_equiv_intro s ṡ m b:
  stringmap_lookup "main" δ = Some s →
  Genv.init_mem p = Some m →
  let ge := globalenv p in
  Genv.find_symbol ge p.(prog_main) = Some b →
  let f := {|
    fn_return:=type_int32s;
    fn_callconv:=AST.cc_default;
    fn_params:=nil;
    fn_vars:=nil;
    fn_body:=ṡ
  |} in
  Genv.find_funct_ptr ge b = Some (Internal f) →
  stmt_equiv s ṡ →
  program_equiv.

Theorem soundness Q:
  program_equiv →
  ch2o_safe_program Γ δ Q →
  compcertc_safe_program Q p.
Proof.
intros Hequiv Hch2o.
destruct Hequiv.
econstructor. { econstructor; try eassumption. reflexivity. }
intro; intros.
(* Callstate *)
inversion H4; clear H4; subst. {
  right.
  eexists.
  eexists.
  right.
  eapply step_internal_function. {
    constructor.
  } {
    constructor.
  } {
    constructor.
  }    
}
inversion H5; clear H5; subst; inversion H4; clear H4; subst.
clear H1 H2 H12 H14.
inversion H13; clear H13; subst.
simpl in H6.
(* Executing the body *)
inversion H3; clear H3; subst.
inversion H6; clear H6; subst. {
  right.
  eexists.
  eexists.
  right.
  constructor.
}
inversion H2; clear H2; subst; inversion H4; clear H4; subst.
(* Returning *)
inversion H1; clear H1; subst.
inversion H3; clear H3; subst. {
  right.
  eexists.
  eexists.
  right.
  constructor.
  - reflexivity.
  - reflexivity.
}
inversion H1; clear H1; subst; inversion H3; clear H3; subst; try (inversion H12; clear H12; subst; try discriminate).
{ subst; inversion H11. }
{ subst; inversion H11. }
{ inversion H11; clear H11; subst; try discriminate.
  subst.
  elim H12.
  constructor. }
(* Final state *)
assert (Cop.sem_cast (Vint (Int.repr z)) (Tint I32 Signed noattr) type_int32s m2 = Some (Vint (Int.repr z))). {
  unfold Cop.sem_cast in H4.
  simpl in H4.
  destruct Archi.ptr64; reflexivity. (* TODO: We may at some point need to make an assumption about this. *)
}
rewrite H1 in H4.
simpl in H4.
inversion H4; clear H4; subst. 2:{
  inversion H3; clear H3; subst; inversion H4.
}
left.
constructor.
rewrite Int.signed_repr. 2:{
  inversion H2.
  unfold int_lower in H3; simpl in H3.
  unfold int_upper in H4; simpl in H4.
  unfold Int.min_signed; unfold Int.max_signed.
  unfold Int.half_modulus.
  unfold Int.modulus.
  unfold Int.wordsize.
  unfold Wordsize_32.wordsize.
  split.
  - apply H3.
  - simpl. lia.
}
(* Proving Q z *)
destruct (Hch2o (state.State [] (Return "main" (intV{sintT} z)) ∅)). 2:{
  inversion H3; assumption.
} 2:{
  destruct H3.
  inversion H3.
}
(* Showing a CH2O execution *)
(* Calling main *)
eapply rtc_l. {
  econstructor.
  - apply H.
  - constructor.
  - reflexivity.
}
simpl.
(* Starting executing ret *)
eapply rtc_l. {
  apply cstep_expr with (E:=CReturnE: statements.esctx_item K) (e:=(# intV{sintT} z: expressions.expr K)%E).
}
(* Finishing executing ret *)
eapply rtc_l. {
  constructor.
}
rewrite mem_unlock_empty.
(* Returning from main *)
eapply rtc_l. {
  constructor.
}
apply rtc_refl.
Qed.

End Program.