From ch2o_compcert Require Export ch2o_safety compcertc_safety.
From ch2o Require Export stringmap types expressions statements architectures state.
(* We prove soundness for LP64 architectures. *)
From ch2o_compcert Require Export ch2o_lp64.
From compcert Require Export Cop Csyntax Ctypes Globalenvs.

From Coq Require Import Classical.

Section Program.

Local Open Scope string_scope.

Context (Γ: types.env K) (δ: funenv K) (p: Csyntax.program).

Notation tint := (Tint I32 Signed noattr).

Inductive type_ := Int | Loc.

Context (ê: list AST.ident).

Inductive expr_equiv: expressions.expr K → Csyntax.expr → type_ → Prop :=
| expr_equiv_val_int z:
  int_typed z (sintT: int_type K) → (* TODO: Require the CH2O program to be well-typed instead? *)
  expr_equiv (# intV{sintT} z) (Eval (Vint (Int.repr z)) tint) Int
| expr_equiv_div e1 ė1 e2 ė2:
  expr_equiv e1 ė1 Int →
  expr_equiv e2 ė2 Int →
  expr_equiv (e1 / e2) (Ebinop Odiv ė1 ė2 tint) Int
| expr_equiv_var i x:
  ê !! i = Some x →
  expr_equiv (var i) (Evar x tint) Loc
| expr_equiv_loc b:
  expr_equiv (%(Ptr (addr_top (Npos b) sintT))) (Eloc b Ptrofs.zero tint) Loc
| expr_equiv_load e ė:
  expr_equiv e ė Loc →
  expr_equiv (load e)%E (Evalof ė tint) Int
| expr_equiv_val_indet:
  expr_equiv (# indetV sintT) (Eval Vundef tint) Int
.

Inductive stmt_equiv: stmt K → statement → Prop :=
| stmt_equiv_return e ė:
  expr_equiv e ė Int →
  stmt_equiv (ret (cast{sintT%T} e)) (Sreturn (Some ė))
| stmt_equiv_skip:
  stmt_equiv skip Sskip
| stmt_equiv_sequence s1 ṡ1 s2 ṡ2:
  stmt_equiv s1 ṡ1 →
  stmt_equiv s2 ṡ2 →
  stmt_equiv (s1 ;; s2) (Ssequence ṡ1 ṡ2)
| stmt_equiv_if e ė s1 ṡ1 s2 ṡ2:
  expr_equiv e ė Int →
  stmt_equiv s1 ṡ1 →
  stmt_equiv s2 ṡ2 →
  stmt_equiv (if{e} s1 else s2) (Sifthenelse ė ṡ1 ṡ2)
| stmt_equiv_assign i x e ė:
  ê !! i = Some x →
  expr_equiv e ė Int →
  stmt_equiv (! (cast{voidT%T} (var i) ::= e)) (Sdo (Eassign (Evar x tint) ė tint))
.

Inductive program_equiv: Prop :=
| program_equiv_intro s ṡ b:
  stringmap_lookup "main" δ = Some (Nat.iter (length ê) (λ s, local{sintT} s) s) →
  Genv.init_mem p <> None →
  let ge := globalenv p in
  Genv.find_symbol ge p.(prog_main) = Some b →
  let f := {|
    fn_return:=type_int32s;
    fn_callconv:=AST.cc_default;
    fn_params:=nil;
    fn_vars:=foldr (λ (x: AST.ident) xs, ((x, tint)::xs)) [] ê;
    fn_body:=
      Ssequence
        ṡ 
        (Sreturn (Some (Eval (Vint (Int.repr 0)) (Tint I32 Signed noattr))))
  |} in
  Genv.find_funct_ptr ge b = Some (Internal f) →
  stmt_equiv s ṡ →
  program_equiv.

Definition globdef_is_fun{F V}(g: AST.globdef F V): bool :=
  match g with
    AST.Gfun _ => true
  | AST.Gvar _ => false
  end.

Lemma init_mem_ok `{prog: Ctypes.program F}:
  forallb (λ gd, globdef_is_fun (gd.2)) (AST.prog_defs prog) = true →
  Genv.init_mem prog <> None.
Proof.
intros.
unfold Genv.init_mem.
assert (∀ gl ge m, (∀ g, In g gl → globdef_is_fun (snd g) = true) → Genv.alloc_globals (F:=Ctypes.fundef F) (V:=type) ge m gl <> None). {
  induction gl; intros.
  - simpl. intro; discriminate.
  - simpl.
    unfold Genv.alloc_global.
    destruct a.
    destruct g.
    + case_eq (Memory.Mem.alloc m 0 1).
      intros.
      destruct (Memory.Mem.range_perm_drop_2 m0 b 0 1 Memtype.Nonempty).
      * unfold Memory.Mem.range_perm.
        intros.
        apply Memory.Mem.perm_alloc_2 with (1:=H1) (2:=H2).
      * rewrite e.
        apply IHgl.
        intros.
        apply H0.
        right.
        assumption.
    + lapply (H0 (i, AST.Gvar v)).
      intros; discriminate. left.
      reflexivity.
}
apply H0.
rewrite -> (List.forallb_forall (A:=AST.ident * AST.globdef (Ctypes.fundef F) type)) in H.
apply H.
Qed.

Lemma int_typed_limits z:
  int_typed z (sintT%IT: int_type K) →
  (Int.min_signed ≤ z ∧ z ≤ Int.max_signed)%Z.
Proof.
intros.
unfold Int.min_signed, Int.max_signed.
unfold Int.half_modulus.
unfold Int.modulus.
unfold Int.wordsize.
unfold Wordsize_32.wordsize.
assert ((two_power_nat 32 / 2 = 2147483648)%Z). reflexivity.
rewrite H0.
destruct H.
unfold int_lower in H. unfold int_upper in H1.
simpl in *.
lia.
Qed.

Local Open Scope list_scope.

Lemma destruct_list_snoc{X}(P: list X → Prop)(xs: list X):
  P [] →
  (∀ xs0 x, P (xs0 ++ [x])) →
  P xs.
Proof.
intros.
destruct xs.
- assumption.
- destruct (exists_last (l:=x::xs)).
  + intro; discriminate.
  + destruct s.
    rewrite e.
    apply H0.
Qed.

Lemma compcertc_expr_never_stuck f a k e m:
  (∃ v ty, a = Eval v ty) ∨
  ∃ t s, Step (semantics p) (ExprState f a k e m) t s.
Proof.
destruct (classic (imm_safe (globalenv p) e RV a m)).
- inversion H; clear H; subst.
  + left.
    eexists; eexists; reflexivity.
  + right.
    eexists; eexists.
    left.
    apply step_lred; eassumption.
  + right.
    eexists; eexists.
    left.
    apply step_rred; eassumption.
  + right.
    eexists; eexists.
    left.
    apply step_call; eassumption.
- right.
  eexists; eexists.
  left.
  eapply step_stuck with (C:=λ x, x).
  + apply ctx_top.
  + eassumption.
Qed.

(*
Lemma expr_equiv_no_LV_context e ė:
  expr_equiv e ė →
  ∀ C a,
  context LV RV C →
  ė ≠ C a.
Proof.
induction 1; intros.
- inversion H0; clear H0; subst; discriminate.
- intro.
  inversion H1; clear H1; subst; try discriminate.
  + injection H2; clear H2; intros; subst.
    eelim IHexpr_equiv1 with (1:=H3); reflexivity.
  + injection H2; clear H2; intros; subst.
    eelim IHexpr_equiv2 with (1:=H3); reflexivity.
Qed.
*)

Lemma sem_cast_int z m:
  sem_cast (Vint (Int.repr z)) tint tint m = Some (Vint (Int.repr z)).
Proof.
  unfold sem_cast.
  simpl.
  destruct Archi.ptr64; reflexivity.
Qed.

Lemma Int_min_signed: Int.min_signed = (-2147483648)%Z.
Proof.
reflexivity.
Qed.

Lemma Int_max_signed: Int.max_signed = 2147483647%Z.
Proof.
reflexivity.
Qed.

Lemma int_lower_sintT: int_lower (sintT%IT: int_type K) = (-2147483648)%Z.
Proof.
reflexivity.
Qed.

Lemma int_upper_sintT: int_upper (sintT%IT: int_type K) = 2147483648%Z.
Proof.
unfold int_upper.
simpl.
reflexivity.
Qed.

Definition ch2o_val_of(oz: option Z): val K :=
  match oz with
    None => indetV sintT
  | Some z => intV{sintT} z
  end.

Definition compcert_val_of(oz: option Z): Values.val :=
  match oz with
    None => Vundef
  | Some z => Vint (Int.repr z)
  end.

Inductive block_equiv(m: memory_map.mem K)(ṁ: Memory.Mem.mem)(b: Values.block): Prop :=
| block_equiv_not_alloced:
  Memory.Mem.loadv AST.Mint32 ṁ (Vptr b Ptrofs.zero) = None →
  (∀ v, Memory.Mem.storev AST.Mint32 ṁ (Vptr b Ptrofs.zero) v = None) →
  Memory.Mem.free ṁ b 0%Z 4%Z = None →
  m !!{Γ} addr_top (Npos b) sintT = None →
  ~ mem_writable Γ (addr_top (Npos b) sintT) m →
  block_equiv m ṁ b
| block_equiv_alloced oz:
  Memory.Mem.loadv AST.Mint32 ṁ (Vptr b Ptrofs.zero) = Some (compcert_val_of oz) →
  (∀ z', Memory.Mem.storev AST.Mint32 ṁ (Vptr b Ptrofs.zero) (Vint (Int.repr z')) ≠ None) →
  Memory.Mem.free ṁ b 0%Z 4%Z ≠ None →
  m !!{Γ} addr_top (Npos b) sintT = Some (ch2o_val_of oz) →
  mem_writable Γ (addr_top (Npos b) sintT) m →
  match oz with None => True | Some z => int_typed z (sintT: int_type K) end →
  block_equiv m ṁ b
.

Record mem_equiv(m: memory_map.mem K)(ṁ: Memory.Mem.mem) := {
  blocks_equiv: ∀ b, block_equiv m ṁ b;
  domains_equiv: ∀ b, (ṁ.(Memory.Mem.nextblock) ≤ b)%positive → (Npos b : index) ∉ dom indexset m
}.

Inductive env_equiv(ẽ: Csem.env): list AST.ident → list (index * types.type K) → Prop :=
| env_equiv_nil:
  env_equiv ẽ [] []
| env_equiv_cons x ê b ρ:
  Maps.PTree.get x ẽ = Some (b, tint) →
  env_equiv ẽ ê ρ →
  env_equiv ẽ (x::ê) ((Npos b, sintT%T)::ρ)
.

Lemma env_equiv_lookup:
  forall ẽ ê ρ,
  env_equiv ẽ ê ρ →
  forall i x,
  ê !! i = Some x →
  ∃ b, Maps.PTree.get x ẽ = Some (b, tint).
Proof.
  induction 1; intros.
  - discriminate.
  - destruct i.
    + simpl in H1; injection H1; clear H1; intros; subst.
      exists b.
      assumption.
    + simpl in H1.
      apply IHenv_equiv with (1:=H1).
Qed.

Inductive lrred: Csem.env → kind → expr → Memory.mem → Events.trace → expr → Memory.mem → Prop :=
| lrred_lred ẽ a ṁ a' ṁ':
  lred (globalenv p) ẽ a ṁ a' ṁ' →
  lrred ẽ LV a ṁ Events.E0 a' ṁ'
| lrred_rred ẽ a ṁ t a' ṁ':
  rred (globalenv p) a ṁ t a' ṁ' →
  lrred ẽ RV a ṁ t a' ṁ'
.

Lemma lrred_safe e ė θ:
  expr_equiv e ė θ →
  ∀ C K_ K_' a ẽ ṁ t a' ṁ' ρ m,
  context K_ K_' C →
  ė = C a →
  lrred ẽ K_ a ṁ t a' ṁ' →
  mem_equiv m ṁ →
  env_equiv ẽ ê ρ →
  ∃ (E: ectx K) e1 e2,
  e = subst E e1 ∧
  Γ \ ρ ⊢ₕ e1, m ⇒ e2, m ∧
  expr_equiv (subst E e2) (C a') θ ∧
  ṁ' = ṁ.
Proof.
induction 1; intros.
- inversion H0; clear H0; subst; try discriminate.
  subst.
  inversion H2; clear H2; subst; inversion H0.
- rename H4 into Hmem_equiv.
  rename H5 into Menv_equiv.
  inversion H1; clear H1; subst; try discriminate.
  + subst.
    inversion H3; clear H3; subst; inversion H1; clear H1; subst.
    inversion H; clear H; subst;
    inversion H0; clear H0; subst; try discriminate.
    simpl in H10.
    unfold sem_div in H10.
    unfold sem_binarith in H10.
    simpl in H10.
    rewrite sem_cast_int in H10.
    rewrite sem_cast_int in H10.
    rewrite Int.eq_signed in H10.
    destruct (Coqlib.zeq (Int.signed (Int.repr z0)) (Int.signed Int.zero)). {
      discriminate.
    }
    rewrite Int.signed_repr in n. 2:{ apply int_typed_limits; assumption. }
    rewrite Int.signed_zero in n.
    rewrite Int.eq_signed in H10.
    rewrite Int.signed_repr in H10. 2:{ apply int_typed_limits; assumption. }
    rewrite Int.signed_repr in H10. 2:{
      split; try reflexivity.
      pose proof Int.min_signed_neg.
      pose proof Int.max_signed_pos.
      lia.
    }
    rewrite Int.eq_signed in H10.
    rewrite Int.signed_repr in H10. 2:{ apply int_typed_limits; assumption. }
    rewrite Int.signed_mone in H10.
    rewrite Int_min_signed in H10.
    assert (int_typed (z ÷ z0)%Z (sintT: int_type K) ∧ v = Vint (Int.divs (Int.repr z) (Int.repr z0))). {
      destruct (Coqlib.zeq z (-2147483648)).
      - destruct (Coqlib.zeq z0 (-1)). {
          discriminate.
        }
        simpl in H10.
        split; try congruence.
        subst.
        split.
        + rewrite int_lower_sintT.
          destruct (Z.lt_total z0 0) as [?|[?|?]].
          * assert (0 <= 2147483648 ÷ -z0)%Z. apply Z.quot_pos; lia.
            rewrite Zquot.Zquot_opp_r in H0.
            rewrite <- Zquot.Zquot_opp_l in H0.
            assert (-(2147483648) = -2147483648)%Z. reflexivity.
            rewrite H1 in H0.
            lia.
          * lia.
          * destruct (Zquot.Z_mult_quot_ge (-2147483648) z0)%Z; try lia.
            lapply (Z.mul_le_mono_nonpos_r 1 z0 (-2147483648 ÷ z0))%Z. 2:{
              assert (-2147483648 ÷ z0 = -(2147483648 ÷ z0))%Z. {
                rewrite <- Zquot.Zquot_opp_l.
                reflexivity.
              }
              rewrite H4.
              lapply (Zquot.Z_quot_pos 2147483648 z0). 2:{
                lia.
              }
              intro.
              lapply H5. 2:{
                lia.
              }
              intro.
              lia.
            }
            intro.
            lapply H4. 2:{
              lia.
            }
            intro.
            lia.
        + rewrite int_upper_sintT.
          destruct (Z.lt_total 0 z0) as [?|[?|?]].
          * assert (-2147483648 ÷ z0 = -(2147483648 ÷ z0))%Z. {
              rewrite <- Zquot.Zquot_opp_l.
              reflexivity.
            }
            rewrite H0.
            lapply (Zquot.Z_quot_pos 2147483648 z0)%Z; intros. 2:{
              lia.
            }
            lapply H1; intros. 2:{ lia. }
            lia.
          * lia.
          * assert (2147483648 ÷ -z0 < 2147483648)%Z. {
              apply Z.quot_lt; lia.
            }
            rewrite Zquot.Zquot_opp_r in H0.
            rewrite <- Zquot.Zquot_opp_l in H0.
            apply H0.
      - simpl in H10.
        split; try congruence.
        split.
        + rewrite int_lower_sintT.
          destruct (Z.lt_total 0 z0) as [?|[?|?]]; try lia.
          * destruct (Z.lt_total 0 z) as [?|[?|?]].
            -- assert (0 <= z ÷ z0)%Z. apply Zquot.Z_quot_pos; lia.
               lia.
            -- subst.
               rewrite Zquot.Zquot_0_l.
               lia.
            -- destruct H3.
               rewrite int_lower_sintT in H1.
               assert (z <= z0 * (z ÷ z0))%Z. apply Zquot.Z_mult_quot_ge. lia.
               assert (z0 * (z ÷ z0) <= 1 * (z ÷ z0))%Z. {
                 apply Z.mul_le_mono_nonpos_r.
                 - assert (0 <= -z ÷ z0)%Z. apply Zquot.Z_quot_pos; lia.
                   assert (-z ÷ z0 = -(z ÷ z0))%Z. rewrite Zquot.Zquot_opp_l; reflexivity.
                   lia.
                 - lia.
               }
               lia.
          * destruct (Z.lt_total 0 z) as [?|[?|?]].
            -- destruct H3.
               rewrite int_upper_sintT in H3.
               assert (-z <= -z0 * (-z ÷ -z0))%Z. apply Zquot.Z_mult_quot_ge. lia.
               assert (-z0 * (-z ÷ -z0) <= 1 * (-z ÷ -z0))%Z. {
                 apply Z.mul_le_mono_nonpos_r.
                 - assert (0 <= z ÷ -z0)%Z. apply Zquot.Z_quot_pos; lia.
                   assert (-z ÷ -z0 = -(z ÷ -z0))%Z. rewrite Zquot.Zquot_opp_l; reflexivity.
                   lia.
                 - lia.
               }
               assert (-z ÷ -z0 = z ÷ z0)%Z. rewrite Zquot.Zquot_opp_l. rewrite Zquot.Zquot_opp_r. lia.
               lia.
            -- subst.
               rewrite Zquot.Zquot_0_l.
               lia.
            -- assert (0 <= z ÷ z0)%Z. {
                 assert (z ÷ z0 = - -(-z ÷ -z0))%Z. rewrite Zquot.Zquot_opp_l. rewrite Zquot.Zquot_opp_r. lia.
                 assert (0 <= -z ÷ -z0)%Z. apply Zquot.Z_quot_pos; lia.
                 lia.
               }
               lia.
        + rewrite int_upper_sintT.
          destruct (Z.lt_total 0 z0) as [?|[?|?]]; try lia.
          * destruct (Z.lt_total 0 z) as [?|[?|]].
            -- destruct H3.
               rewrite int_upper_sintT in H3.
               assert (z0 * (z ÷ z0) <= z)%Z. {
                 apply Zquot.Z_mult_quot_le; lia.
               }
               assert (1 * (z ÷ z0) <= z0 * (z ÷ z0))%Z. {
                 apply Z.mul_le_mono_nonneg_r.
                 - apply Zquot.Z_quot_pos; lia.
                 - lia.
               }
               lia.
            -- subst.
               rewrite Zquot.Zquot_0_l.
               lia.
            -- assert (z ÷ z0 = -(-z ÷ z0))%Z. rewrite Zquot.Zquot_opp_l; lia.
               assert (0 <= -z ÷ z0)%Z. apply Zquot.Z_quot_pos; lia.
               lia.
          * destruct (Z.lt_total 0 z) as [?|[?|?]].
            -- assert (z ÷ z0 = -(z ÷ -z0))%Z. rewrite Zquot.Zquot_opp_r; lia.
               assert (0 <= z ÷ -z0)%Z. apply Zquot.Z_quot_pos; lia.
               lia.
            -- subst.
               rewrite Zquot.Zquot_0_l.
               lia.
            -- destruct H3.
               rewrite int_lower_sintT in H1.
               assert (-z0 * (-z ÷ -z0) <= -z)%Z. {
                 apply Zquot.Z_mult_quot_le; lia.
               }
               assert (1 * (-z ÷ -z0) <= -z0 * (-z ÷ -z0))%Z. {
                 apply Z.mul_le_mono_nonneg_r.
                 - apply Zquot.Z_quot_pos; lia.
                 - lia.
               }
               assert (z ÷ z0 = -z ÷ -z0)%Z. {
                 rewrite Zquot.Zquot_opp_l.
                 rewrite Zquot.Zquot_opp_r.
                 lia.
               }
               lia.
    }
    destruct H.
    subst.
    exists [].
    eexists; eexists.
    simpl; split; [reflexivity|].
    split. {
      constructor. constructor.
      -- assumption.
      -- apply H.
    }
    split. {
      rewrite (right_id_L _ (∪)).
      unfold Int.divs.
      rewrite Int.signed_repr. 2:{ apply int_typed_limits; assumption. }
      rewrite Int.signed_repr. 2:{ apply int_typed_limits; assumption. }
      constructor.
      assumption.
    }
    reflexivity.
  + injection H2; clear H2; intros; subst.
    destruct (IHexpr_equiv1 C0 K_ RV a ẽ ṁ t a' ṁ' ρ m H4) as [E [e5 [e6 [? [? ?]]]]]; try trivial.
    exists (E ++ [CBinOpL (ArithOp DivOp) e2])%E; eexists; eexists.
    rewrite subst_snoc.
    rewrite subst_snoc.
    simpl.
    rewrite H1.
    split; try trivial.
    split. { apply H2. }
    split. { constructor; tauto. }
    destruct H5; congruence.
  + injection H2; clear H2; intros; subst.
    destruct (IHexpr_equiv2 C0 K_ RV a ẽ ṁ t a' ṁ' ρ m H4) as [E [e5 [e6 [? [? [? Hṁ']]]]]]; try trivial.
    exists (E ++ [CBinOpR (ArithOp DivOp) e1])%E; eexists; eexists.
    rewrite subst_snoc.
    rewrite subst_snoc.
    simpl.
    rewrite H1.
    split; try trivial.
    split. { apply H2. }
    split. { constructor; assumption. }
    assumption.
- inversion H0; clear H0; subst; try discriminate.
  subst.
  inversion H2; clear H2; subst; inversion H0; clear H0; subst. 2:{
    apply False_ind.
    revert H4 i H.
    induction 1; intros.
    - discriminate.
    - destruct i.
      + simpl in H0.
        injection H0; clear H0; intros; subst.
        congruence.
      + simpl in H0.
        eapply IHenv_equiv; eassumption.
  }
  exists [].
  exists (var i)%E.
  exists (%(Ptr (addr_top (Npos b) sintT)))%E.
  split. { reflexivity. }
  split. {
    constructor.
    revert H4 i H.
    induction 1; intros.
    - discriminate.
    - destruct i.
      + simpl in H0.
        injection H0; clear H0; intros; subst.
        assert (b0 = b). congruence.
        subst.
        reflexivity.
      + simpl in *.
        apply IHenv_equiv; assumption.
  }
  split. {
    constructor.
  }
  reflexivity.
- inversion H; clear H; subst; try discriminate.
  subst.
  inversion H1; clear H1; subst; inversion H; clear H; subst.
- inversion H0; clear H0; subst; try discriminate.
  + subst.
    inversion H2; clear H2; subst; inversion H0; clear H0; subst.
    inversion H; clear H; subst.
    inversion H9; clear H9; subst; try discriminate.
    simpl in H.
    injection H; clear H; intros; subst.
    pose proof (blocks_equiv _ _ H3 b).
    inversion H; clear H; subst; try congruence.
    assert (v = compcert_val_of oz). congruence. subst.
    exists []; eexists; eexists.
    split. { reflexivity. }
    split. {
      assert (m = mem_force Γ (addr_top (N.pos b) sintT) m). {
        unfold mem_force.
        simpl.
        unfold cmap_alter_ref.
        destruct m.
        simpl.
        rewrite alter_id.
        - reflexivity.
        - intros.
          unfold cmap_elem_map.
          destruct x; reflexivity.
      }
      rewrite H at 2.
      constructor.
      eassumption.
    }
    split. {
      destruct oz; constructor.
      assumption.
    }
    reflexivity.
  + injection H1; clear H1; intros; subst.
    destruct (IHexpr_equiv _ _ _ _ _ _ _ _ _ _ _ H5 eq_refl H2 H3 H4) as [E [e1 [e2 [? [? [? ?]]]]]].
    subst.
    exists (E ++ [CLoad]); eexists; eexists.
    rewrite ! subst_snoc.
    split. { reflexivity. }
    split. { eassumption. }
    split. {
      simpl.
      constructor; assumption.
    }
    reflexivity.
- inversion H; clear H; subst; try discriminate.
  subst.
  inversion H1; clear H1; subst; inversion H; clear H; subst.
Qed.

Lemma expr_equiv_no_call e ė θ:
  expr_equiv e ė θ →
  ∀ a m fd vargs ty K C,
  callred (globalenv p) a m fd vargs ty →
  context RV K C →
  ė ≠ C a.
Proof.
induction 1; intros.
- inversion H1; subst; try discriminate.
  intro; subst.
  inversion H0.
- inversion H2; subst; try discriminate.
  + intro; subst.
    inversion H1.
  + intro.
    injection H4; clear H4; intros; subst.
    apply IHexpr_equiv1 with (1:=H1) (2:=H3) (3:=eq_refl).
  + intro.
    injection H4; clear H4; intros; subst.
    apply IHexpr_equiv2 with (1:=H1) (2:=H3) (3:=eq_refl).
- inversion H1; subst; try discriminate.
  intro; subst.
  inversion H0.
- inversion H0; subst; try discriminate.
  intro; subst.
  inversion H.
- inversion H1; subst; try discriminate.
  + intro; subst.
    inversion H0.
  + intro.
    injection H3; clear H3; intros; subst.
    apply IHexpr_equiv with (1:=H0) (2:=H2) (3:=eq_refl).
- inversion H0; subst; try discriminate.
  intro; subst.
  inversion H.
Qed.

Definition kind_of_type(θ: type_): kind :=
  match θ with
    Int => RV
  | Loc => LV
  end.

Lemma expr_equiv_imm_safe e ė θ:
  expr_equiv e ė θ →
  ∀ m ṁ ẽ ρ,
  mem_equiv m ṁ →
  env_equiv ẽ ê ρ →
  (∀ (E: ectx K) e1, e = subst E e1 → is_redex e1 → Γ \ ρ ⊢ₕ safe e1, m) →
  imm_safe (globalenv p) ẽ (kind_of_type θ) ė ṁ.
Proof.
induction 1; intros.
- apply imm_safe_val.
- assert (imm_safe (globalenv p) ẽ RV ė1 ṁ). {
    eapply IHexpr_equiv1; try eassumption.
    intros.
    subst.
    apply (H3 (E++[CBinOpL (ArithOp DivOp) e2])); try assumption.
    simpl.
    rewrite subst_snoc.
    reflexivity.
  }
  inversion H4; clear H4; subst.
  + assert (imm_safe (globalenv p) ẽ RV ė2 ṁ). {
      eapply IHexpr_equiv2; try eassumption.
      intros; subst.
      apply (H3 (E++[CBinOpR (ArithOp DivOp) e1])); try assumption.
      rewrite subst_snoc.
      reflexivity.
    }
    inversion H4; clear H4; subst.
    * inversion H; clear H; subst. 2:{
        inversion H0; clear H0; subst.
        -- lapply (H3 [] _ eq_refl). 2:{
             constructor.
             constructor.
             constructor.
           }
           intros.
           inversion H; clear H; subst.
           inversion H0; clear H0; subst.
           inversion H12; clear H12; subst.
        -- lapply (H3 [] _ eq_refl). 2:{
             constructor.
             constructor.
             constructor.
           }
           intros.
           inversion H; clear H; subst.
           inversion H0; clear H0; subst.
           inversion H11; clear H11; subst.
      }
      inversion H0; clear H0; subst. 2:{
        lapply (H3 [] _ eq_refl). 2:{
           constructor.
           constructor.
           constructor.
         }
         intros.
         inversion H; clear H; subst.
         inversion H0; clear H0; subst.
         inversion H12; clear H12; subst.
      }
      eapply imm_safe_rred with (C:=λ x, x). 2:{
        apply ctx_top.
      }
      constructor.
      simpl.
      assert (Γ \ ρ ⊢ₕ safe (# intV{sintT} z / # intV{sintT} z0)%E, m). {
        apply H3 with (E:=[]).
        - reflexivity.
        - constructor; constructor.
      }
      inversion H; clear H; subst.
      inversion H0; clear H0; subst.
      inversion H13; clear H13; subst.
      assert (z0 ≠ 0)%Z. { apply H. }
      assert (int_typed (z ÷ z0) (sintT%IT: int_type K)). { apply H0. }
      clear H H0.
      unfold sem_div.
      unfold sem_binarith.
      simpl.
      rewrite sem_cast_int.
      rewrite sem_cast_int.
      rewrite Int.eq_signed.
      rewrite Int.signed_repr. 2:{ apply int_typed_limits; assumption. }
      rewrite Int.signed_zero.
      destruct (Coqlib.zeq z0 0); try lia.
      simpl.
      rewrite Int.eq_signed.
      rewrite Int.signed_repr. 2:{ apply int_typed_limits; assumption. }
      rewrite Int.signed_repr. 2:{
        split. { reflexivity. }
        pose proof Int.min_signed_neg.
        pose proof Int.max_signed_pos.
        lia.
      }
      rewrite Int_min_signed.
      rewrite Int.eq_signed.
      rewrite Int.signed_repr. 2:{ apply int_typed_limits; assumption. }
      rewrite Int.signed_mone.
      assert (
        (if Coqlib.zeq z (-2147483648) then true else false) &&
        (if Coqlib.zeq z0 (-1) then true else false)
        = false
      ). {
        destruct (Coqlib.zeq z (-2147483648)). {
          destruct (Coqlib.zeq z0 (-1)). {
            subst.
            destruct H7.
            rewrite int_upper_sintT in H0.
            discriminate.
          }
          reflexivity.
        }
        reflexivity.
      }
      rewrite H.
      reflexivity.
    * eapply imm_safe_lred with (C:=λ x, Ebinop Odiv (Eval v ty) (C x) tint). 2:{
        apply ctx_binop_right; assumption.
      }
      eassumption.
    * eapply imm_safe_rred with (C:=λ x, Ebinop Odiv (Eval v ty) (C x) tint). 2:{
        apply ctx_binop_right; assumption.
      }
      eassumption.
    * eelim (expr_equiv_no_call _ _ _ H0); try eassumption.
      reflexivity.
  + eapply imm_safe_lred with (C:=λ x, Ebinop Odiv (C x) ė2 tint). 2:{
      apply ctx_binop_left; assumption.
    }
    eassumption.
  + eapply imm_safe_rred with (C:=λ x, Ebinop Odiv (C x) ė2 tint). 2:{
      apply ctx_binop_left; assumption.
    }
    eassumption.
  + eelim (expr_equiv_no_call _ _ _ H); try eassumption.
    reflexivity.
- destruct (env_equiv_lookup _ _ _ H1 _ _ H).
  eapply imm_safe_lred with (C:=λ x, x). 2:{ apply ctx_top. }
  constructor.
  eassumption.
- apply imm_safe_loc.
- assert (imm_safe (globalenv p) ẽ LV ė ṁ). {
    eapply IHexpr_equiv; try eassumption.
    intros; subst.
    apply H2 with (E0:=E++[CLoad]); try assumption.
    rewrite subst_snoc.
    reflexivity.
  }
  inversion H3; clear H3; subst.
  + inversion H; clear H; subst.
    lapply (H2 [] _ eq_refl). 2:{ constructor. constructor. }
    intros.
    inversion H; clear H; subst.
    inversion H3; clear H3; subst.
    destruct (blocks_equiv _ _ H0 b). {
      assert (forall {X} (x1 x2 x3 x4: X), x1 = x2 -> x3 = x4 -> x1 = x3 -> x2 = x4). {
        intros; congruence.
      }
      lapply (H7 _ _ _ _ _ H5 H8); try reflexivity.
      intros; congruence.
    }
    eapply imm_safe_rred with (C:=λ x, x). 2:{ apply ctx_top. }
    constructor.
    eapply deref_loc_value; try reflexivity.
    apply H.
  + eapply imm_safe_lred with (C:=λ x, Evalof (C x) tint). 2:{ constructor. assumption. }
    eassumption.
  + eapply imm_safe_rred with (C:=λ x, Evalof (C x) tint). 2:{ constructor. assumption. }
    eassumption.
  + eelim (expr_equiv_no_call _ _ _ H); eauto.
- apply imm_safe_val.
Qed.

Lemma expr_equiv_imm_safe e ė:
  expr_equiv e ė →
  ∀ K_ C a ρ m ẽ ṁ,
  context K_ RV C →
  ė = C a →
  (∀ (E: ectx K) e1, e = subst E e1 → is_redex e1 → Γ \ ρ ⊢ₕ safe e1, m) →
  imm_safe (globalenv p) ẽ K_ a ṁ.
Proof.
induction 1; intros.
- inversion H0; clear H0; subst; try discriminate.
  subst.
  constructor.
- inversion H1; clear H1; subst; try discriminate.
  + subst.
    edestruct (expr_equiv_imm_safe_rred (e1 / e2) (Ebinop Odiv ė1 ė2 tint))%E. {
      constructor; assumption.
    } {
      eassumption.
    }
    * destruct H1 as [? [? ?]]; discriminate.
    * destruct (H1 ṁ) as [C [a [t [a' [HC [Hė Hrred]]]]]].
      rewrite Hė.
      eapply imm_safe_rred with (C:=C) (e0:=a); eassumption.
  + injection H2; clear H2; intros; subst.
    eapply IHexpr_equiv1; try eassumption.
    * reflexivity.
    * intros.
      eapply H3 with (E:=E++[CBinOpL (ArithOp DivOp) e2]); try assumption.
      rewrite subst_snoc.
      simpl.
      congruence.
  + injection H2; clear H2; intros; subst.
    eapply IHexpr_equiv2; try eassumption.
    * reflexivity.
    * intros.
      eapply H3 with (E:=E++[CBinOpR (ArithOp DivOp) e1]); try assumption.
      rewrite subst_snoc.
      simpl.
      congruence.
Qed.

Lemma eval_soundness Q n e ė k ḳ m ṁ f:
  expr_equiv e ė →
  ch2o_safe_state Γ δ Q (State k (Expr e) m) →
  (∀ z n',
   n' ≤ n →
   int_typed z (sintT: int_type K) →
   ch2o_safe_state Γ δ Q (State k (Expr (# intV{sintT} z)) m) →
   compcertc_safe_state_n Q p n' (ExprState f (Eval (Vint (Int.repr z)) (Tint I32 Signed noattr)) ḳ empty_env ṁ)) →
  compcertc_safe_state_n Q p n (ExprState f ė ḳ empty_env ṁ).
Proof.
revert e ė.
apply well_founded_induction with (1:=lt_wf) (a:=n).
clear n.
intros n IH.
intros.
intros t s HstarN.
inversion HstarN; subst.
- (* refl *)
  destruct (compcertc_expr_never_stuck f ė ḳ empty_env ṁ).
  + destruct H2 as [v [ty H2]].
    subst.
    inversion H; clear H; subst.
    unfold compcertc_safe_state_n in H1.
    eapply H1 with (n':=0) (trace:=[]); try eauto.
  + tauto.
- case_eq (match ė with Eval _ _ => true | _ => false end); intros. {
    inversion H; clear H; subst; try discriminate.
    unfold compcertc_safe_state_n in H1.
    eapply H1 with (n':=S n0) (4:=HstarN); try eauto.
  }
  destruct H2. 2:{
    inversion H2; subst; discriminate.
  }
  inversion H2; clear H2; subst.
  + (* step_lred *)
    eapply expr_equiv_no_LV_context in H; [elim H; reflexivity | assumption].
  + (* step_rred *)
    edestruct (rred_safe _ _ H) as [E [e1 [e2 [He1 [He1e2 [Hee' Hṁ']]]]]]; try (eassumption || reflexivity).
    unfold compcertc_safe_state_n in IH.
    subst.
    eapply IH with (2:=Hee') (5:=H3).
    * lia.
    * intro S'.
      intro HS'.
      apply H0.
      eapply rtc_l; try eassumption.
      assert (∀ e, cast{sintT%T} (subst E e) = subst (E ++ [CCast (sintT%T)]) e)%E. {
        intros; rewrite subst_snoc.
        reflexivity.
      }
      apply cstep_expr_head.
      apply He1e2.
    * intros z n' Hn'.
      apply (H1 z n'); lia.
  + (* step_call *)
    apply expr_equiv_no_call with (2:=H12) (3:=H13) in H.
    elim H; reflexivity.
  + elim H13.
    eapply expr_equiv_imm_safe with (1:=H) (2:=H12). { reflexivity. }
    intros.
    destruct (classic (Γ \ locals k ⊢ₕ safe e1, m)); try eassumption.
    destruct (H0 (State k (Undef (UndefExpr E e1)) m)). {
      eapply rtc_l; [|apply rtc_refl].
      subst.
      apply cstep_expr_undef; assumption.
    }
    * inversion H7.
    * destruct H7 as [S'' H7].
      inversion H7.
Qed.

Lemma eval_soundness' Q n e ė k ḳ m ṁ f:
  expr_equiv e ė →
  ch2o_safe_state Γ δ Q (State k (Expr (cast{sintT%T} e)) m) →
  (∀ z n',
   n' ≤ n →
   int_typed z (sintT: int_type K) →
   ch2o_safe_state Γ δ Q (State k (Expr (# intV{sintT} z)) m) →
   compcertc_safe_state_n Q p n' (ExprState f (Eval (Vint (Int.repr z)) (Tint I32 Signed noattr)) ḳ empty_env ṁ)) →
  compcertc_safe_state_n Q p n (ExprState f ė ḳ empty_env ṁ).
Proof.
revert e ė.
apply well_founded_induction with (1:=lt_wf) (a:=n).
clear n.
intros n IH.
intros.
intros t s HstarN.
inversion HstarN; subst.
- (* refl *)
  destruct (compcertc_expr_never_stuck f ė ḳ empty_env ṁ).
  + destruct H2 as [v [ty H2]].
    subst.
    inversion H; clear H; subst.
    unfold compcertc_safe_state_n in H1.
    eapply H1 with (n':=0) (trace:=[]); try eauto.
    intro; intros; eapply H0.
    eapply rtc_l; try eassumption.
    apply cstep_expr_head with (E:=[]).
    constructor.
    apply H4.
  + tauto.
- case_eq (match ė with Eval _ _ => true | _ => false end); intros. {
    inversion H; clear H; subst; try discriminate.
    unfold compcertc_safe_state_n in H1.
    eapply H1 with (n':=S n0) (4:=HstarN); try eauto.
    intro; intros; eapply H0.
    eapply rtc_l; try eassumption.
    apply cstep_expr_head with (E:=[]).
    constructor.
    apply H5.
  }
  destruct H2. 2:{
    inversion H2; subst; discriminate.
  }
  inversion H2; clear H2; subst.
  + (* step_lred *)
    eapply expr_equiv_no_LV_context in H; [elim H; reflexivity | assumption].
  + (* step_rred *)
    edestruct (rred_safe _ _ H) as [E [e1 [e2 [He1 [He1e2 [Hee' Hṁ']]]]]]; try (eassumption || reflexivity).
    unfold compcertc_safe_state_n in IH.
    subst.
    eapply IH with (2:=Hee') (5:=H3).
    * lia.
    * intro S'.
      intro HS'.
      apply H0.
      eapply rtc_l; try eassumption.
      assert (∀ e, cast{sintT%T} (subst E e) = subst (E ++ [CCast (sintT%T)]) e)%E. {
        intros; rewrite subst_snoc.
        reflexivity.
      }
      rewrite 2 H2.
      apply cstep_expr_head.
      apply He1e2.
    * intros z n' Hn'.
      apply (H1 z n'); lia.
  + (* step_call *)
    apply expr_equiv_no_call with (2:=H12) (3:=H13) in H.
    elim H; reflexivity.
  + elim H13.
    eapply expr_equiv_imm_safe with (1:=H) (2:=H12). { reflexivity. }
    intros.
    destruct (classic (Γ \ locals k ⊢ₕ safe e1, m)); try eassumption.
    destruct (H0 (State k (Undef (UndefExpr (E ++ [CCast sintT]) e1)) m)). {
      eapply rtc_l; [|apply rtc_refl].
      subst.
      assert (cast{sintT%T} (subst E e1) = subst (E ++ [CCast sintT]) e1)%E. rewrite subst_snoc; reflexivity.
      rewrite H2.
      apply cstep_expr_undef; assumption.
    }
    * inversion H7.
    * destruct H7 as [S'' H7].
      inversion H7.
Qed.

Lemma stmt_soundness Q f s ṡ:
  stmt_equiv s ṡ →
  ∀ n k ḳ m ṁ,
  ch2o_safe_state Γ δ Q (State k (Stmt ↘ s) m) →
  (∀ n',
   n' ≤ n →
   ch2o_safe_state Γ δ Q (State k (Stmt ↗ s) m) →
   compcertc_safe_state_n Q p n' (Csem.State f Sskip ḳ empty_env ṁ)) →
  (∀ n' z ḳ',
   n' ≤ n →
   int_typed z (sintT: int_type K) →
   call_cont ḳ' = call_cont ḳ →
   ch2o_safe_state Γ δ Q (State k (Stmt (⇈ (intV{sintT} z)) s) m) →
   compcertc_safe_state_n Q p n' (ExprState f (Eval (Vint (Int.repr z)) tint) (Kreturn ḳ') empty_env ṁ)) →
  compcertc_safe_state_n Q p n (Csem.State f ṡ ḳ empty_env ṁ).
Proof.
(* TODO: When adding support for loops, we'll need to perform well-founded induction on n here as well. *)
induction 1.
- (* return *)
  intros.
  intro; intros.
  inversion H3; clear H3; subst. {
    right.
    eexists; eexists.
    right.
    constructor.
  }
  inversion H4; clear H4; subst; inversion H3; clear H3; subst; try intuition discriminate.
  eapply eval_soundness'; try eassumption. {
    intro; intros.
    eapply H0.
    eapply rtc_l; [|eassumption].
    apply cstep_expr with (E:=CReturnE).
  }
  intros.
  eapply H2; try eassumption.
  + lia.
  + reflexivity.
  + intro; intros.
    eapply H6.
    eapply rtc_l; [|eassumption].
    rewrite <- mem_unlock_empty at 2.
    constructor.
- (* skip *)
  intros.
  eapply H0.
  + reflexivity.
  + intro; intros.
    eapply H.
    eapply rtc_l; [|eassumption].
    constructor.
- (* sequence *)
  intros.
  intro; intros.
  inversion H4; clear H4; subst. {
    right.
    eexists; eexists.
    right.
    constructor.
  }
  inversion H5; clear H5; subst; inversion H4; clear H4; subst; try intuition discriminate.
  eapply IHstmt_equiv1; try eassumption. {
    intro; intros.
    eapply H1.
    eapply rtc_l; [|eassumption].
    constructor.
  } 2:{
    intros.
    simpl in H7.
    eapply H3; try eassumption.
    - lia.
    - intro; intros.
      eapply H8.
      eapply rtc_l; [|eassumption].
      constructor.
  }
  intros.
  intro; intros.
  inversion H7; clear H7; subst. {
    right.
    eexists; eexists.
    right.
    constructor.
  }
  inversion H8; clear H8; subst; inversion H7; clear H7; subst. 2:{
    inversion H15.
  }
  eapply IHstmt_equiv2; try eassumption. {
    intro; intros.
    eapply H5.
    eapply rtc_l; [|eassumption].
    constructor.
  } 2:{
    intros.
    intro; intros.
    eapply H3; try eassumption.
    + lia.
    + intro; intros.
      eapply H11.
      eapply rtc_l; [|eassumption].
      constructor.
  }
  intros.
  eapply H2; try eassumption.
  + lia.
  + intro; intros.
    eapply H8.
    eapply rtc_l; [|eassumption].
    constructor.
- (* if *)
  intros.
  intro; intros.
  inversion H5; clear H5; subst. {
    right.
    eexists; eexists.
    right.
    constructor.
  }
  inversion H6; clear H6; subst; inversion H5; clear H5; subst; try intuition discriminate.
  eapply eval_soundness; try eassumption. {
    intro; intros.
    eapply H2.
    eapply rtc_l; [|eassumption].
    apply cstep_expr with (E:=CIfE s1 s2).
  }
  intros.
  intro; intros.
  inversion H9; clear H9; subst. {
    right.
    eexists; eexists.
    right.
    constructor.
    unfold bool_val.
    simpl.
    reflexivity.
  }
  inversion H10; clear H10; subst; inversion H9; clear H9; subst. {
    inversion H19; clear H19; subst; try discriminate.
  } {
    inversion H19; clear H19; subst; try discriminate.
    subst.
    inversion H18; clear H18; subst.
  } {
    inversion H19; clear H19; subst; try discriminate.
    subst.
    inversion H18; clear H18; subst.
  } {
    inversion H18; clear H18; subst; try discriminate.
    subst.
    elim H19; constructor.
  }
  unfold bool_val in H21.
  simpl in H21.
  injection H21; clear H21; intros; subst.
  rewrite Int.eq_signed in H11.
  rewrite Int.signed_repr in H11. 2:{
    apply int_typed_limits; assumption.
  }
  rewrite Int.signed_zero in H11.
  destruct (Coqlib.zeq z 0); simpl in H11.
  + (* z = 0 *)
    subst.
    eapply IHstmt_equiv2; try eassumption. {
      intro; intros.
      eapply H8.
      eapply rtc_l; [|eassumption].
      constructor.
      - simpl. constructor.
      - constructor.
    } 2:{
      intros.
      eapply H4; try eassumption.
      - lia.
      - intro; intros.
        eapply H13.
        eapply rtc_l; [|eassumption].
        rewrite mem_unlock_empty.
        constructor.
    }
    intros.
    rewrite mem_unlock_empty in H10.
    intro; intros.
    eapply H3; try eassumption.
    * lia.
    * intro; intros.
      eapply H10.
      eapply rtc_l; [|eassumption].
      constructor.
  + (* z ≠ 0 *)
    eapply IHstmt_equiv1; try eassumption. {
      intro; intros.
      eapply H8.
      eapply rtc_l; [|eassumption].
      constructor.
      - constructor.
      - intro.
        elim n1.
        inversion H10; clear H10; subst.
        reflexivity.
    } 2:{
      intros.
      eapply H4; try eassumption.
      - lia.
      - intro; intros.
        eapply H13.
        eapply rtc_l; [|eassumption].
        rewrite mem_unlock_empty.
        constructor.
    }
    intros.
    rewrite mem_unlock_empty in H10.
    eapply H3; try eassumption.
    * lia.
    * intro; intros.
      eapply H10.
      eapply rtc_l; [|eassumption].
      constructor.
Qed.

Theorem soundness Q:
  program_equiv →
  ch2o_safe_program Γ δ Q →
  compcertc_safe_program Q p.
Proof.
intros Hequiv Hch2o.
destruct Hequiv.
case_eq (Genv.init_mem p); intros; try tauto. clear H0; rename H4 into H0.
econstructor. { econstructor; try eassumption. reflexivity. }
intro n; intro; intros.
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
(* Ssequence *)
inversion H6 ; clear H6; subst. {
  right.
  eexists.
  eexists.
  right.
  constructor.
}
inversion H1; clear H1; subst; inversion H4; clear H4; subst.
rename H2 into H6.
(* Executing the body *)
eapply stmt_soundness; try eassumption. {
  intro; intros.
  destruct (Hch2o S'); try tauto.
  apply rtc_transitive with (2:=H1).
  (* Showing a CH2O execution *)
  (* Calling main *)
  eapply rtc_l. {
    econstructor.
    - apply H.
    - constructor.
    - reflexivity.
  }
  simpl.
  apply rtc_refl.
} {
  intros.
  destruct (H2 (State [] (Return "main" voidV) ∅)). {
    eapply rtc_l; [|apply rtc_refl].
    constructor.
  }
  - inversion H4.
  - destruct H4 as [S'' H4].
    inversion H4.
}
intros.
intro; intros.
inversion H7; clear H7; subst. {
  right.
  eexists; eexists.
  right.
  constructor.
  - simpl.
    apply sem_cast_int.
  - reflexivity.
}
inversion H8; clear H8; subst; inversion H7; clear H7; subst. {
  inversion H17; clear H17; subst; try discriminate.
} {
  inversion H17; clear H17; subst; try discriminate.
  subst.
  inversion H16.
} {
  inversion H17; clear H17; subst; try discriminate.
  subst.
  inversion H16.
} {
  inversion H16; clear H16; subst; try discriminate.
  subst.
  elim H17.
  constructor.
}
rewrite H4 in H9.
simpl in H9.
inversion H9; clear H9; subst. 2:{
  inversion H7; clear H7; subst; inversion H9; clear H9; subst.
}
left.
simpl in H17.
rewrite sem_cast_int in H17.
injection H17; clear H17; intros; subst.
constructor.
rewrite Int.signed_repr. 2:{
  apply int_typed_limits; assumption.
}
(* Proving Q z *)
destruct (H5 (state.State [] (Return "main" (intV{sintT} z)) ∅)). 2:{
  inversion H7; assumption.
} 2:{
  destruct H7.
  inversion H7.
}
(* Finishing executing ret *)
eapply rtc_l. {
  constructor.
}
simpl.
apply rtc_refl.
Qed.

End Program.
