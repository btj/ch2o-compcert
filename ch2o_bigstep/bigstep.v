Require Export ch2o.core_c.statements.
Require Export stores.

Inductive eval `{Env K}: store -> expr K -> Z -> Prop :=
| eval_lit st z:
  int_typed z sintT ->
  eval st (# intV{sintT} z) z
| eval_load_var st i z:
  st !! i = Some (Some z) ->
  eval st (load (var i)) z
.

Inductive outcome := onormal(s: store) | oreturn(z: Z).

Inductive exec `{Env K}: store -> stmt K -> outcome -> Prop :=
| exec_local_normal st s mv st':
  exec (None::st) s (onormal (mv::st')) ->
  exec st (local{sintT%BT} s) (onormal st')
| exec_local_return st s z:
  exec (None::st) s (oreturn z) ->
  exec st (local{sintT%BT} s) (oreturn z)
| exec_assign st i e z:
  i < length st ->
  eval st e z ->
  exec st (var i ::= cast{sintT%BT} e) (onormal (<[i:=Some z]>st))
| exec_seq st s1 st' s2 O:
  exec st s1 (onormal st') ->
  exec st' s2 O ->
  exec st (s1 ;; s2) O
| exec_ret st e z:
  eval st e z ->
  exec st (ret (cast{sintT%BT} e)) (oreturn z)
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
- (* eval_assign *)
  injection H3; clear H3; intros; subst.
  apply insert_length.
- rewrite IHexec2; [|assumption].
  apply IHexec1; reflexivity.
Qed.
