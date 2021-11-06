Require Export ch2o.core_c.statements.
Require Export stores.

Inductive binop_ok `{Env K}: binop → Z → Z → Prop :=
| div_ok z1 z2:
  z2 ≠ 0%Z → binop_ok (ArithOp DivOp) z1 z2
.

Definition binop_value `{Env K} (op:binop)(z1 z2: Z): Z :=
  match op with
    ArithOp DivOp => z1 ÷ z2
  | _ => 0
  end.

Inductive eval `{Env K}: store -> expr K -> Z -> Prop :=
| eval_lit st z:
  int_typed z sintT ->
  eval st (# intV{sintT} z) z
| eval_load_var st i z:
  st !! i = Some (Some z) ->
  eval st (load (var i)) z
| eval_binop st e1 z1 e2 z2 op:
  eval st e1 z1 →
  eval st e2 z2 →
  binop_ok op z1 z2 →
  int_typed (binop_value op z1 z2) sintT →
  eval st (e1 .{ op } e2) (binop_value op z1 z2)
.

Lemma eval_typed `{Env K} st e z:
  eval st e z →
  store_typed st →
  int_typed z sintT.
Proof.
induction 1; try tauto.
- intros.
  apply Forall_lookup_1 with (1:=H1) (2:=H0).
Qed.

Inductive outcome := onormal(s: store) | oreturn(z: Z).

Inductive exec `{Env K}: store → stmt K → outcome → Prop :=
| exec_local_normal st s mv st':
  exec (None::st) s (onormal (mv::st')) →
  exec st (local{sintT%BT} s) (onormal st')
| exec_local_return st s z:
  exec (None::st) s (oreturn z) →
  exec st (local{sintT%BT} s) (oreturn z)
| exec_assign st i e z:
  i < length st →
  eval st e z →
  exec st (var i ::= cast{sintT%BT} e) (onormal (<[i:=Some z]>st))
| exec_assign' st i e z:
  i < length st →
  eval st e z →
  exec st (! (cast{voidT%T} (var i ::= e))) (onormal (<[i:=Some z]>st))
| exec_seq st s1 st' s2 O:
  exec st s1 (onormal st') →
  exec st' s2 O →
  exec st (s1 ;; s2) O
| exec_ret st e z:
  eval st e z →
  exec st (ret (cast{sintT%BT} e)) (oreturn z)
| exec_skip st:
  exec st skip (onormal st)
| exec_if st e z s1 s2 O:
  eval st e z →
  exec st (if Z.eqb z 0 then s2 else s1) O →
  exec st (if{e} s1 else s2) O
.

Lemma exec_onormal_length_st `{EnvSpec K} st s O:
  exec st s O →
  ∀ st',
  O = onormal st' →
  length st' = length st.
Proof.
induction 1; intros; try discriminate.
- (* exec_local_normal *)
  lapply (IHexec (mv :: st')); [|reflexivity].
  intros.
  simpl in H3; injection H3; clear H3; intros; subst.
  congruence.
- (* exec_assign *)
  injection H3; clear H3; intros; subst.
  apply insert_length.
- (* exec_assign' *)
  injection H3; clear H3; intros; subst.
  apply insert_length.
- rewrite IHexec2; [|assumption].
  apply IHexec1; reflexivity.
- injection H1; clear H1; intros; subst.
  reflexivity.
- apply IHexec in H3.
  congruence.
Qed.
