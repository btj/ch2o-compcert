From ch2o_compcert Require Export ch2o_safety compcertc_safety.
From ch2o Require Export stringmap types expressions statements architectures architecture_spec state.
(* We prove soundness for LP64 architectures. *)
From ch2o_compcert Require Export ch2o_lp64.
From compcert Require Export Cop Csyntax Ctypes Globalenvs.

From Coq Require Import Classical.

Section Program.

Local Open Scope string_scope.

Context (Γ: types.env K) (δ: funenv K) (p: Csyntax.program) (valid_Γ: ✓ Γ).

Notation tint := (Tint I32 Signed noattr).

Inductive type_ := Int | Loc.

Section Locals.

Context (ê: list AST.ident).

Inductive expr_equiv: expressions.expr K → Csyntax.expr → type_ → Prop :=
| expr_equiv_val_int Ω z:
  int_typed z (sintT: int_type K) → (* TODO: Require the CH2O program to be well-typed instead? *)
  expr_equiv (#{Ω} intV{sintT} z) (Eval (Vint (Int.repr z)) tint) Int
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
| expr_equiv_assign e1 ė1 e2 ė2:
  expr_equiv e1 ė1 Loc →
  expr_equiv e2 ė2 Int →
  expr_equiv (e1 ::= e2) (Eassign ė1 ė2 tint) Int
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
| stmt_equiv_do e ė:
  expr_equiv e ė Int →
  stmt_equiv (! (cast{voidT%T} e)) (Sdo ė)
.

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
  
Lemma mem_lookup_dom m i v:
  m !!{Γ} addr_top i sintT = Some v → i ∈ dom indexset m.
Proof.
  unfold lookupE.
  unfold mem_lookup.
  unfold lookupE.
  unfold cmap_lookup.
  rewrite option_guard_True. 2:{ constructor. simpl. lia. }
  unfold lookupE.
  unfold cmap_lookup_ref.
  simpl.
  case_eq (cmap_car m !! i); simpl; intros; try congruence.
  apply elem_of_dom_2 in H.
  destruct m.
  assumption.
Qed.

Lemma mem_writable_dom i m:
  mem_writable Γ (addr_top i sintT) m → i ∈ dom indexset m.
Proof.
  destruct m as [m].
  unfold mem_writable.
  intros.
  destruct H as [w [? ?]].
  unfold lookupE in H.
  unfold cmap_lookup in H.
  rewrite option_guard_True in H. 2:{ constructor. simpl. lia. }
  simpl in H.
  case_eq (m !! i); intros; rewrite H1 in H; try discriminate.
  apply elem_of_dom_2 in H1.
  assumption.
Qed.

Lemma mem_lookup_index_alive m i v:
  m !!{Γ} addr_top i sintT = Some v → index_alive '{m} i.
Proof.
  destruct m as [m]; simpl.
  unfold mem_lookup; simpl.
  unfold cmap_lookup.
  unfold index_alive.
  rewrite option_guard_True. 2:{ constructor. simpl. lia. }
  simpl.
  case_eq (m !! i); simpl; intros; try congruence.
  destruct c as [|w μ]; simpl in H0; try congruence.
  exists (type_of w).
  rewrite lookup_fmap.
  rewrite H.
  reflexivity.
Qed.

Inductive block_equiv(m: memory_map.mem K)(ṁ: Memory.Mem.mem)(b: Values.block): Prop :=
| block_equiv_not_alloced:
  (*
  Memory.Mem.loadv AST.Mint32 ṁ (Vptr b Ptrofs.zero) = None →
  (∀ v, Memory.Mem.storev AST.Mint32 ṁ (Vptr b Ptrofs.zero) v = None) →
  Memory.Mem.free ṁ b 0%Z 4%Z = None →
  m !!{Γ} addr_top (Npos b) sintT = None →
  ~ mem_writable Γ (addr_top (Npos b) sintT) m →
  *)
  ¬ index_alive '{m} (Npos b) →
  block_equiv m ṁ b
| block_equiv_alloced oz:
  Memory.Mem.loadv AST.Mint32 ṁ (Vptr b Ptrofs.zero) = Some (compcert_val_of oz) →
  Memory.Mem.valid_access ṁ AST.Mint32 b 0 Memtype.Writable →
  Memory.Mem.range_perm ṁ b 0%Z 4%Z Memtype.Cur Memtype.Freeable →
  index_alive '{m} (Npos b) →
  (Γ, '{m}) ⊢ addr_top (N.pos b) sintT : TType sintT%T →
  m !!{Γ} addr_top (Npos b) sintT = Some (ch2o_val_of oz) →
  mem_writable Γ (addr_top (Npos b) sintT) m →
  match oz with None => True | Some z => int_typed z (sintT: int_type K) end →
  block_equiv m ṁ b
.

Record mem_equiv(m: memory_map.mem K)(ṁ: Memory.Mem.mem) := {
  blocks_equiv: ∀ b, block_equiv m ṁ b;
  domains_equiv: ∀ b, (ṁ.(Memory.Mem.nextblock) ≤ b)%positive → (Npos b : index) ∉ dom indexset m;
  mem_valid: ✓{Γ} m
}.

Lemma mem_equiv_insert m ṁ b z ṁ':
  mem_equiv m ṁ →
  (Γ, '{m}) ⊢ addr_top (N.pos b) sintT : TType sintT%T →
  mem_writable Γ (addr_top (N.pos b) sintT) m →
  Memory.Mem.storev AST.Mint32 ṁ (Vptr b Ptrofs.zero)
    (Vint (Int.repr z)) = Some ṁ' →
  int_typed z (sintT: int_type K) →
  mem_equiv
    (<[addr_top (N.pos b) sintT:=intV{sintT} z]{Γ}> m)
    ṁ'.
Proof.
  intros ? Hwelltyped; intros.
  assert (Hvalue_welltyped: (Γ, '{m}) ⊢ intV{sintT} z : sintT%T). {
    constructor.
    constructor.
    assumption.
  }
  split.
  - intros.
    destruct H.
    destruct (classic (b0 = b)).
    + subst.
      destruct (blocks_equiv0 b). {
        elim H.
        eapply mem_writable_alive in H0; try eassumption.
      }
      apply block_equiv_alloced with (oz:=Some z).
      * simpl.
        simpl in H1.
        apply Memory.Mem.load_store_same with (1:=H1).
      * apply Memory.Mem.store_valid_access_1 with (1:=H1).
        apply Memory.Mem.store_valid_access_3 with (1:=H1).
      * intro; intros.
        apply Memory.Mem.perm_store_1 with (1:=H1).
        apply H4; assumption.
      * erewrite mem_insert_memenv_of; try eassumption.
      * erewrite mem_insert_memenv_of; try eassumption.
      * assert (freeze true (ch2o_val_of (Some z)) = ch2o_val_of (Some z)). reflexivity.
        rewrite <- H10.
        eapply mem_lookup_insert; try eassumption.
        constructor.
      * eapply mem_insert_writable; try eassumption.
        tauto.
      * assumption.
    + destruct (blocks_equiv0 b0).
      * apply block_equiv_not_alloced.
        erewrite mem_insert_memenv_of; eassumption.
      * apply block_equiv_alloced with (oz:=oz).
        -- simpl.
           rewrite Memory.Mem.load_store_other with (1:=H1).
           ++ assumption.
           ++ left; assumption.
        -- apply Memory.Mem.store_valid_access_1 with (1:=H1) (2:=H4).
        -- intro; intros.
           apply Memory.Mem.perm_store_1 with (1:=H1).
           apply H5; assumption.
        -- erewrite mem_insert_memenv_of; eassumption.
        -- erewrite mem_insert_memenv_of; try eassumption.
        -- eapply mem_lookup_insert_disjoint; try eassumption.
           constructor.
           simpl.
           congruence.
        -- eapply mem_insert_writable; try eassumption.
           right.
           constructor.
           simpl; congruence.
        -- assumption.
  - destruct H.
    intros.
    rewrite mem_dom_insert.
    rewrite Memory.Mem.nextblock_store with (1:=H1) in H.
    auto.
  - destruct H.
    eapply mem_insert_valid'; try eassumption.
Qed.

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

Lemma indexmap_merge_spec A B C (f: option A -> option B -> option C) (t1: indexmap A) (t2: indexmap B) i:
  f None None = None →
  merge f t1 t2 !! i = f (t1 !! i) (t2 !! i).
Proof.
  intros.
  destruct t1.
  destruct t2.
  destruct i.
  - simpl.
    reflexivity.
  - simpl.
    destruct Nmap_pos.
    destruct Nmap_pos0.
    simpl.
    unfold pmap.Pmerge.
    simpl.
    unfold lookup.
    unfold pmap.Plookup.
    simpl.
    apply pmap.Pmerge_spec.
    assumption.
Qed.

Lemma mem_unlock_all_lookup m b v:
  m !!{Γ} addr_top (N.pos b) sintT = Some v →
  mem_unlock_all m !!{Γ} addr_top (N.pos b) sintT = Some v.
Proof.
  destruct m as [m].
  simpl.
  unfold mem_lookup.
  simpl.
  unfold cmap_lookup.
  rewrite option_guard_True. 2:{ constructor. simpl. lia. }
  simpl.
  intro.
  unfold lookup in H.
  case_eq (indexmap_lookup (N.pos b) m); intros; rewrite H0 in H. 2:{
    discriminate.
  }
  destruct c; try discriminate.
  simpl in H.
  destruct (classic (ctree_Forall (λ γb : pbit K, Some Readable ⊆ pbit_kind γb) c)). 2:{
    rewrite option_guard_False in H; try assumption; discriminate.
  }
  rewrite option_guard_True in H; try assumption.
  injection H; clear H; intros; subst.
  rewrite indexmap_merge_spec; try reflexivity.
  rewrite lookup_omap.
  unfold lookup.
  rewrite H0.
  simpl.
  destruct (classic (natmap.of_bools (pbit_locked <$> ctree_flatten c) ≠ ∅)).
  - rewrite option_guard_True; try assumption.
    simpl.
    rewrite option_guard_True. 2:{
      rewrite ctree_flatten_merge.
      apply Forall_zip_with_fst with (1:=H1).
      apply Forall_forall.
      intros.
      destruct x; simpl; try assumption.
      destruct x0; simpl.
      simpl in H3.
      destruct tagged_perm; try assumption.
      destruct l; try assumption.
      unfold perm_kind in H3.
      elim H3.
    }
    f_equal.
    clear H0 H1 H.
    rewrite natmap.to_of_bools.
    rewrite resize_all_alt. 2:{
      unfold fmap.
      rewrite fmap_length.
      reflexivity.
    }
    apply ctree_ind_alt with (w:=c); intros.
    + simpl.
      f_equal.
      f_equal.
      induction xs.
      * reflexivity.
      * simpl.
        unfold fmap in IHxs.
        rewrite IHxs.
        f_equal; try reflexivity.
        destruct a.
        simpl.
        destruct tagged_perm; try reflexivity.
        destruct l; reflexivity.
    + simpl.
      f_equal.
      revert H.
      induction ws; intros; try reflexivity.
      simpl.
      inversion H; subst.
      f_equal.
      * rewrite <- fmap_take.
        rewrite take_app.
        assumption.
      * rewrite <- fmap_drop.
        rewrite drop_app.
        auto.
    + simpl.
      f_equal.
      revert H; induction wxss; intros; simpl. reflexivity.
      destruct a.
      simpl.
      inversion H; clear H; subst.
      f_equal.
      * rewrite <- fmap_take.
        rewrite <- app_assoc.
        rewrite take_app.
        assumption.
      * rewrite <- fmap_drop.
        rewrite <- fmap_drop.
        rewrite <- app_assoc.
        rewrite drop_app.
        rewrite drop_app.
        auto.
    + simpl.
      f_equal.
      rewrite <- fmap_take.
      rewrite take_app.
      assumption.
    + simpl.
      f_equal.
      induction xs.
      * reflexivity.
      * simpl.
        f_equal.
        -- destruct a.
           destruct tagged_perm; try reflexivity.
           destruct l; reflexivity.
        -- assumption.
  - rewrite option_guard_False; try assumption.
    simpl.
    rewrite option_guard_True; try assumption.
    reflexivity.
Qed.

Lemma mem_writable_unlock_all m b:
  mem_writable Γ (addr_top (N.pos b) sintT) m →
  mem_writable Γ (addr_top (N.pos b) sintT) (mem_unlock_all m).
Proof.
  unfold mem_writable.
  intros.
  destruct H as [w [Hw Hw']].
  unfold mem_unlock_all.
  unfold mem_unlock.
  destruct (mem_locks m) as [Ω].
  destruct m as [m].
  simpl.
  unfold cmap_lookup.
  rewrite option_guard_True. 2:{ constructor. simpl. lia. }
  simpl.
  rewrite indexmap_merge_spec. 2:{ reflexivity. }
  unfold lookup.
  simpl in Hw.
  unfold cmap_lookup in Hw.
  rewrite option_guard_True in Hw. 2:{ constructor. simpl. lia. }
  simpl in Hw.
  unfold lookup in Hw.
  case_eq (indexmap_lookup (N.pos b) m); intros; rewrite H in Hw. 2:{ discriminate. }
  destruct c as [|w1 μ]; try discriminate.
  simpl in Hw.
  injection Hw; clear Hw; intros; subst.
  case_eq (indexmap_lookup (N.pos b) Ω); intros.
  - simpl.
    eexists; split. reflexivity.
    rewrite ctree_flatten_merge.
    apply Forall_zip_with_fst with (1:=Hw').
    apply Forall_forall; intros.
    destruct x; simpl; try assumption.
    destruct x0; try assumption.
    destruct tagged_perm as [[]|[]]; try assumption.
    elim H2.
  - simpl.
    eexists; split. reflexivity.
    assumption.
Qed.

Lemma mem_unlock_all_spec' (m: mem K):
  mem_unlock_all m =
    let (m) := m in
    CMap $ cmap_elem_map (ctree_map pbit_unlock) <$> m.
Proof.
  destruct m as [m].
  unfold mem_unlock_all.
  simpl.
  f_equal.
  apply map_eq; intro i.
  rewrite indexmap_merge_spec; try reflexivity.
  rewrite lookup_fmap.
  rewrite lookup_omap.
  destruct (m !! i); try reflexivity.
  destruct c as [|ω μ]; try reflexivity.
  simpl.
  destruct (classic (natmap.of_bools (pbit_locked <$> ctree_flatten ω) = ∅)). {
    rewrite option_guard_False. 2:{
      tauto.
    }
    f_equal.
    f_equal.
    Search ctree_map.
    rewrite ctree_map_id with (P:=λ b, pbit_locked b = false).
    - reflexivity.
    - intros.
      destruct x.
      destruct tagged_perm; try reflexivity.
      destruct l.
      + discriminate.
      + reflexivity.
    - apply Forall_lookup_2; intros.
      case_eq (pbit_locked x); intros; try trivial.
      assert ((pbit_locked <$> ctree_flatten ω) !! i0 = Some true). {
        rewrite list_lookup_fmap.
        rewrite H0.
        simpl.
        congruence.
      }
      apply natmap.elem_of_of_bools in H2.
      rewrite H in H2.
      apply not_elem_of_empty in H2.
      elim H2.
  }
  rewrite option_guard_True; try assumption.
  f_equal.
  f_equal.
  rewrite natmap.to_of_bools.
  rewrite resize_all_alt. 2:{
    rewrite fmap_length.
    reflexivity.
  }
  apply ctree_merge_map. {
    rewrite fmap_length.
    reflexivity.
  }
  clear H.
  induction (ctree_flatten ω); try reflexivity.
  simpl.
  f_equal.
  - destruct a.
    destruct tagged_perm; try reflexivity.
    destruct l0; reflexivity.
  - apply IHl.
Qed.

Lemma mem_unlock_all_mem_lock b m:
  mem_unlock_all (mem_lock Γ (addr_top (N.pos b) sintT) m) = mem_unlock_all m.
Proof.
  rewrite mem_unlock_all_spec'.
  rewrite mem_unlock_all_spec'.
  destruct m as [m].
  simpl.
  f_equal.
  apply map_eq; intro i.
  rewrite lookup_fmap.
  rewrite lookup_fmap.
  destruct (classic (i = N.pos b)). 2:{
    rewrite lookup_alter_ne; congruence.
  }
  subst.
  rewrite lookup_alter.
  destruct (m !! (N.pos b: index)); try reflexivity.
  simpl.
  f_equal.
  destruct c as [|ω μ]; try reflexivity.
  simpl.
  f_equal.
  rewrite <- ctree_map_compose.
  assert (pbit_unlock (K:=K) ∘ pbit_lock = pbit_unlock). {
    apply functional_extensionality; intros.
    destruct x.
    destruct tagged_perm; try reflexivity.
    destruct l; reflexivity.
  }
  congruence.
Qed.

Lemma fmap_zip_with {A B C D} (f: C → D) (g: A → B → C) xs ys:
  f <$> zip_with g xs ys = zip_with (λ x y, f (g x y)) xs ys.
Proof.
  revert ys.
  induction xs; intros; simpl.
  - reflexivity.
  - destruct ys.
    + reflexivity.
    + simpl.
      f_equal.
      apply IHxs.
Qed.

Lemma ctree_map_ctree_merge {A B C D} (f: C → D) (g: A → B → C) (w: ctree K A) ys:
  ctree_map f (ctree_merge g w ys) = ctree_merge (λ x y, f (g x y)) w ys.
Proof.
  revert ys.
  apply ctree_ind_alt with (w:=w); intros; simpl.
  - f_equal.
    apply fmap_zip_with.
  - f_equal.
    revert ys.
    induction ws; intros; try reflexivity.
    simpl.
    inversion H; clear H; subst.
    f_equal.
    + apply H2.
    + apply IHws.
      apply H3.
  - f_equal.
    revert ys.
    induction wxss; intros; try reflexivity.
    destruct a.
    simpl.
    inversion H; clear H; subst.
    f_equal.
    + f_equal.
      * apply H2.
      * apply fmap_zip_with.
    + apply IHwxss.
      apply H3.
  - f_equal.
    + apply H.
    + apply fmap_zip_with.
  - f_equal.
    apply fmap_zip_with.
Qed.

Lemma mem_unlock_all_mem_unlock Ω (m: mem K):
  mem_unlock_all (mem_unlock Ω m) = mem_unlock_all m.
Proof.
  rewrite !mem_unlock_all_spec'.
  destruct m as [m].
  destruct Ω as [Ω HΩ].
  simpl.
  f_equal.
  apply map_eq; intro i.
  rewrite !lookup_fmap.
  rewrite indexmap_merge_spec; [|reflexivity].
  destruct (Ω !! i); try reflexivity.
  destruct (m !! i); try reflexivity.
  destruct c as [|w μ]; try reflexivity.
  simpl.
  f_equal.
  f_equal.
  rewrite ctree_map_ctree_merge.
  apply ctree_merge_map. {
    rewrite natmap.to_bools_length.
    reflexivity.
  }
  pose proof (natmap.to_bools_length m0 (Datatypes.length (ctree_flatten w))).
  revert H.
  generalize (natmap.to_bools (Datatypes.length (ctree_flatten w)) m0).
  induction (ctree_flatten w); intros; try reflexivity.
  simpl.
  destruct l0; try discriminate.
  f_equal.
  - destruct a as [[[]|[]]]; destruct b; try reflexivity.
  - apply IHl.
    simpl in H.
    lia.
Qed.

Lemma mem_unlock_all_mem_insert b v (m: mem K):
  mem_unlock_all (<[addr_top (N.pos b) sintT: addr K:=v]{Γ}> m) =
  <[addr_top (N.pos b) sintT:=v]{Γ}> (mem_unlock_all m).
Proof.
  rewrite !mem_unlock_all_spec'.
  destruct m as [m].
  simpl.
  f_equal.
  apply map_eq; intro i.
  rewrite !lookup_fmap.
  destruct (classic (i = N.pos b)). 2:{
    rewrite !lookup_alter_ne; try congruence.
    rewrite lookup_fmap.
    reflexivity.
  }
  subst.
  rewrite !lookup_alter.
  rewrite lookup_fmap.
  destruct (m !! (N.pos b: index)); try reflexivity.
  destruct c as [|ω μ]; try reflexivity.
  simpl.
  f_equal.
  f_equal.
  rewrite ctree_map_of_val with (g:=perm_unlock). 2:{ intros; reflexivity. }
  f_equal.
  rewrite ctree_flatten_map.
  rewrite <- !list_fmap_compose.
  reflexivity.
Qed.

Lemma mem_unlock_all_mem_alloc o μ γ v (m: mem K):
  perm_unlock γ = γ →
  mem_unlock_all (mem_alloc Γ o μ γ v m) =
  mem_alloc Γ o μ γ v (mem_unlock_all m).
Proof.
  intros ?.
  rewrite !mem_unlock_all_spec'.
  destruct m as [m].
  simpl.
  f_equal.
  rewrite fmap_insert.
  f_equal.
  simpl.
  f_equal.
  rewrite ctree_map_of_val with (g:=perm_unlock). 2:{ intros; reflexivity. }
  f_equal.
  rewrite fmap_replicate.
  f_equal.
  assumption.
Qed.



Lemma dom_mem_unlock_all (m: mem K): dom indexset (mem_unlock_all m) = dom indexset m.
Proof.
  rewrite mem_unlock_all_spec'.
  destruct m as [m].
  simpl.
  apply dom_fmap_L.
Qed.

Lemma memenv_of_mem_unlock_all (m: mem K): '{mem_unlock_all m} = '{m}.
Proof.
  rewrite mem_unlock_all_spec'.
  destruct m as [m].
  simpl.
  apply map_eq; intro i.
  rewrite !lookup_fmap.
  destruct (m !! i); try reflexivity.
  destruct c as [|w μ]; simpl; try reflexivity.
  rewrite ctree_map_type_of.
  reflexivity.
Qed.

Lemma lrred_safe e ė θ:
  expr_equiv e ė θ →
  ∀ C K_ K_' a ẽ ṁ t a' ṁ' ρ m,
  context K_ K_' C →
  ė = C a →
  lrred ẽ K_ a ṁ t a' ṁ' →
  mem_equiv (mem_unlock_all m) ṁ →
  env_equiv ẽ ê ρ →
  ∀(Hsafe: ∀ (E: ectx K) e1, e = subst E e1 → is_redex e1 → Γ \ ρ ⊢ₕ safe e1, m),
  ∃ (E: ectx K) e1 e2 m',
  e = subst E e1 ∧
  Γ \ ρ ⊢ₕ e1, m ⇒ e2, m' ∧
  expr_equiv (subst E e2) (C a') θ ∧
  mem_equiv (mem_unlock_all m') ṁ' ∧
  '{m'} = '{m}.
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
    eexists; eexists; eexists.
    simpl; split; [reflexivity|].
    split. {
      constructor. constructor.
      -- assumption.
      -- apply H.
    }
    split. {
      unfold Int.divs.
      rewrite Int.signed_repr. 2:{ apply int_typed_limits; assumption. }
      rewrite Int.signed_repr. 2:{ apply int_typed_limits; assumption. }
      constructor.
      assumption.
    }
    split. assumption. reflexivity.
  + injection H2; clear H2; intros; subst.
    destruct (IHexpr_equiv1 C0 K_ RV a ẽ ṁ t a' ṁ' ρ m H4) as [E [e5 [e6 [m' [? [? ?]]]]]]; try trivial. {
      intros; subst.
      apply Hsafe with (E0:=E++[CBinOpL (ArithOp DivOp) e2]) (2:=H2).
      rewrite subst_snoc; reflexivity.
    }
    exists (E ++ [CBinOpL (ArithOp DivOp) e2])%E; eexists; eexists; eexists.
    rewrite subst_snoc.
    rewrite subst_snoc.
    simpl.
    rewrite H1.
    split; try trivial.
    split. { apply H2. }
    split. { constructor; tauto. }
    destruct H5; congruence.
  + injection H2; clear H2; intros; subst.
    destruct (IHexpr_equiv2 C0 K_ RV a ẽ ṁ t a' ṁ' ρ m H4) as [E [e5 [e6 [m' [? [? [? Hṁ']]]]]]]; try trivial. {
      intros; subst.
      apply Hsafe with (E0:=E++[CBinOpR (ArithOp DivOp) e1]) (2:=H2).
      rewrite subst_snoc; reflexivity.
    }
    exists (E ++ [CBinOpR (ArithOp DivOp) e1])%E; eexists; eexists; eexists.
    rewrite subst_snoc.
    rewrite subst_snoc.
    simpl.
    rewrite H1.
    split; try trivial.
    split. { apply H2. }
    split. { constructor; tauto. }
    destruct H5; congruence.
- (* var i *)
  inversion H0; clear H0; subst; try discriminate.
  subst.
  inversion H2; clear H2; subst; inversion H0; clear H0; subst. 2:{
    apply False_ind.
    clear Hsafe.
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
  exists m.
  split. { reflexivity. }
  split. {
    constructor.
    clear Hsafe.
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
  split. assumption. reflexivity.
- (* loc *)
  inversion H; clear H; subst; try discriminate.
  subst.
  inversion H1; clear H1; subst; inversion H; clear H; subst.
- (* load *)
  inversion H0; clear H0; subst; try discriminate.
  + subst.
    inversion H2; clear H2; subst; inversion H0; clear H0; subst.
    inversion H; clear H; subst.
    inversion H9; clear H9; subst; try discriminate.
    simpl in H.
    injection H; clear H; intros; subst.
    pose proof (blocks_equiv _ _ H3 b).
    assert (Hsafe': Γ \ ρ ⊢ₕ safe (load (% Ptr (addr_top (N.pos b) sintT))), m). {
      apply Hsafe with (E:=[]); try reflexivity.
      repeat constructor.
    }
    inversion Hsafe'; clear Hsafe'; subst.
    inversion H2; clear H2; subst; try congruence.
    pose proof H10.
    apply mem_lookup_index_alive in H2.
    rewrite <- memenv_of_mem_unlock_all in H2.
    inversion H; clear H; subst; try tauto.
    assert (v = compcert_val_of oz). congruence. subst.
    exists []; eexists; eexists; exists m.
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
      apply mem_unlock_all_lookup in H10.
      rewrite H10 in H11.
      injection H11; clear H11; intros; subst.
      destruct oz; constructor.
      assumption.
    }
    split. assumption. reflexivity.
  + injection H1; clear H1; intros; subst.
    destruct (IHexpr_equiv _ _ _ _ _ _ _ _ _ _ _ H5 eq_refl H2 H3 H4) as [E [e1 [e2 [m' [? [? [? ?]]]]]]]. {
      intros; subst.
      apply Hsafe with (E0:=E++[CLoad]) (2:=H1).
      rewrite subst_snoc; reflexivity.
    }
    subst.
    exists (E ++ [CLoad]); eexists; eexists; eexists.
    rewrite ! subst_snoc; simpl.
    split. { reflexivity. }
    split. { eassumption. }
    split. {
      simpl.
      constructor; assumption.
    }
    assumption.
- (* indetV *)
  inversion H; clear H; subst; try discriminate.
  subst.
  inversion H1; clear H1; subst; inversion H; clear H; subst.
- (* assign *)
  inversion H1; clear H1; subst; try discriminate.
  + subst.
    inversion H3; clear H3; subst; inversion H1; clear H1; subst.
    inversion H; clear H; subst.
    inversion H0; clear H0; subst.
    * rewrite sem_cast_int in H11.
      injection H11; clear H11; subst.
      inversion H12; clear H12; subst; try discriminate.
      intros; subst.
      simpl in H.
      injection H; clear H; intros; subst.
      lapply (Hsafe [] _ eq_refl). 2:{ repeat constructor. }
      intros.
      inversion H; clear H; subst.
      inversion H3; clear H3; subst.
      exists []; eexists; eexists; eexists.
      split. { reflexivity. }
      split. {
        constructor; eassumption.
      }
      inversion H14; clear H14.
      simpl in H3.
      erewrite int_cast_self in H3; try assumption.
      subst.
      split. {
        simpl.
        constructor.
        assumption.
      }
      rewrite mem_unlock_all_mem_lock.
      rewrite mem_unlock_all_mem_insert.
      inversion H4; subst.
      pose proof H13.
      apply mem_writable_unlock_all in H3.
      eapply mem_writable_alive with (Δ:='{mem_unlock_all m}) in H3; try eassumption.
      destruct (blocks_equiv0 b); try tauto.
      split. {
        eapply mem_equiv_insert; try eassumption.
      }
      rewrite <- memenv_of_mem_unlock_all.
      rewrite mem_unlock_all_mem_lock.
      rewrite mem_unlock_all_mem_insert.
      rewrite <- memenv_of_mem_unlock_all with (m:=m).
      eapply mem_insert_memenv_of; try eassumption.
      constructor.
      constructor.
      assumption.
    * lapply (Hsafe [] _ eq_refl). 2:{ repeat constructor. }
      intros.
      inversion H; clear H; subst.
      inversion H0; clear H0; subst.
      inversion H13; clear H13; subst.
      inversion H; clear H; subst.
      discriminate.
  + injection H2; clear H2; intros; subst.
    destruct (IHexpr_equiv1 _ _ _ _ _ _ _ _ _ _ _ H6 eq_refl H3 H4 H5) as [E [e1' [e2' [m' [? [? [? ?]]]]]]]. {
      intros; subst.
      apply Hsafe with (E0:=E++[CAssignL Assign e2]) (2:=H2).
      rewrite subst_snoc; reflexivity.
    }
    subst.
    exists (E ++ [CAssignL Assign e2]); eexists; eexists; eexists.
    rewrite ! subst_snoc; simpl.
    split. { reflexivity. }
    split. { eassumption. }
    split. {
      simpl.
      constructor; assumption.
    }
    assumption.
  + injection H2; clear H2; intros; subst.
    destruct (IHexpr_equiv2 _ _ _ _ _ _ _ _ _ _ _ H6 eq_refl H3 H4 H5) as [E [e1' [e2' [m' [? [? [? ?]]]]]]]. {
      intros; subst.
      apply Hsafe with (E0:=E++[CAssignR Assign e1]) (2:=H2).
      rewrite subst_snoc; reflexivity.
    }
    subst.
    exists (E ++ [CAssignR Assign e1]); eexists; eexists; eexists.
    rewrite ! subst_snoc; simpl.
    split. { reflexivity. }
    split. { eassumption. }
    split. {
      simpl.
      constructor; assumption.
    }
    assumption.
  Unshelve.
  exact (IntEnvSpec_instance_0 A).
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
- inversion H2; subst; try discriminate.
  + intro.
    subst.
    inversion H1.
  + intro.
    injection H4; clear H4; intros; subst.
    apply IHexpr_equiv1 with (1:=H1) (2:=H3).
    reflexivity.
  + intro.
    injection H4; clear H4; intros; subst.
    apply IHexpr_equiv2 with (1:=H1) (2:=H3).
    reflexivity.
Qed.

Definition kind_of_type(θ: type_): kind :=
  match θ with
    Int => RV
  | Loc => LV
  end.

Lemma expr_equiv_imm_safe e ė θ:
  expr_equiv e ė θ →
  ∀ m ṁ ẽ ρ,
  mem_equiv (mem_unlock_all m) ṁ →
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
      assert (Γ \ ρ ⊢ₕ safe (#{Ω} intV{sintT} z / #{Ω0} intV{sintT} z0)%E, m). {
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
    pose proof H8.
    apply mem_lookup_index_alive in H.
    rewrite <- memenv_of_mem_unlock_all in H.
    destruct (blocks_equiv _ _ H0 b); try tauto.
    eapply imm_safe_rred with (C:=λ x, x). 2:{ apply ctx_top. }
    constructor.
    eapply deref_loc_value; try reflexivity.
    apply H3.
  + eapply imm_safe_lred with (C:=λ x, Evalof (C x) tint). 2:{ constructor. assumption. }
    eassumption.
  + eapply imm_safe_rred with (C:=λ x, Evalof (C x) tint). 2:{ constructor. assumption. }
    eassumption.
  + eelim (expr_equiv_no_call _ _ _ H); eauto.
- apply imm_safe_val.
- assert (imm_safe (globalenv p) ẽ LV ė1 ṁ). {
    eapply IHexpr_equiv1; try eassumption.
    intros; subst.
    apply H3 with (E0:=E++[CAssignL Assign e2]); try assumption.
    rewrite subst_snoc.
    reflexivity.
  }
  inversion H4; clear H4; subst.
  + assert (imm_safe (globalenv p) ẽ RV ė2 ṁ). {
      eapply IHexpr_equiv2; try eassumption.
      intros; subst.
      apply H3 with (E0:=E++[CAssignR Assign e1]); try assumption.
      rewrite subst_snoc.
      reflexivity.
    }
    inversion H4; clear H4; subst.
    * inversion H; clear H; subst.
      inversion H0; clear H0; subst.
      -- lapply (H3 [] _ eq_refl). 2:{ constructor. constructor. constructor. }
         intros.
         inversion H; clear H; subst.
         inversion H0; clear H0; subst.
         pose proof H12.
         destruct H1.
         apply mem_writable_unlock_all in H.
         eapply mem_writable_alive in H; try eassumption.
         destruct (blocks_equiv0 b); try tauto.
         edestruct Memory.Mem.valid_access_store with (1:=H1).
         eapply imm_safe_rred with (C:=λ x, x). 2:{ apply ctx_top. }
         econstructor; try reflexivity.
         econstructor; try reflexivity.
         apply e.
      -- lapply (H3 [] _ eq_refl). 2:{ constructor. constructor. constructor. }
         intros.
         inversion H; clear H; subst.
         inversion H0; clear H0; subst.
         inversion H12; clear H12; subst.
         inversion H; clear H; subst.
         discriminate.
    * eapply imm_safe_lred with (C:=λ x, Eassign (Eloc b ofs ty) (C x) tint). 2:{ constructor. assumption. }
      eassumption.
    * eapply imm_safe_rred with (C:=λ x, Eassign (Eloc b ofs ty) (C x) tint). 2:{ constructor. assumption. }
      eassumption.
    * eelim (expr_equiv_no_call _ _ _ H0); eauto.
  + eapply imm_safe_lred with (C:=λ x, Eassign (C x) ė2 tint). 2:{ constructor; assumption. }
    eassumption.
  + eapply imm_safe_rred with (C:=λ x, Eassign (C x) ė2 tint). 2:{ constructor; assumption. }
    eassumption.
  + eelim (expr_equiv_no_call _ _ _ H); eauto.
Qed.

Lemma expr_equiv_subexpr_imm_safe:
  ∀ K1 K2 C,
  context K1 K2 C →
  ∀ e ė θ,
  expr_equiv e ė θ →
  K2 = kind_of_type θ →
  ∀ m ṁ ẽ ρ a,
  mem_equiv (mem_unlock_all m) ṁ →
  env_equiv ẽ ê ρ →
  ė = C a →
  (∀ (E: ectx K) e1, e = subst E e1 → is_redex e1 → Γ \ ρ ⊢ₕ safe e1, m) →
  imm_safe (globalenv p) ẽ K1 a ṁ.
Proof.
  induction 1; intros; subst; try (eapply expr_equiv_imm_safe; eassumption);
  inversion H0; clear H0; subst.
  - eapply IHcontext; eauto.
    intros; subst.
    eapply H5 with (E0:=E++[CLoad]) (2:=H4).
    rewrite subst_snoc; reflexivity.
  - eapply IHcontext with (1:=H11); eauto.
    intros; subst.
    eapply H5 with (E0:=E++[CBinOpL (ArithOp DivOp) e0]) (2:=H4).
    rewrite subst_snoc; reflexivity.
  - eapply IHcontext with (1:=H12); eauto.
    intros; subst.
    eapply H5 with (E0:=E++[CBinOpR (ArithOp DivOp) e0]) (2:=H4).
    rewrite subst_snoc; reflexivity.
  - eapply IHcontext with (1:=H10); eauto.
    intros; subst.
    eapply H5 with (E0:=E++[CAssignL Assign e0]); eauto.
    rewrite subst_snoc; reflexivity.
  - eapply IHcontext with (1:=H11); eauto.
    intros; subst.
    eapply H5 with (E0:=E++[CAssignR Assign e0]); eauto.
    rewrite subst_snoc; reflexivity.
Qed.

Lemma ch2o_safe_state_subexpr_safe Q k e m:
  ch2o_safe_state Γ δ Q (State k (Expr e) m) →
  ∀ (E : ectx K) (e1 : expressions.expr K),
  e = subst E e1 → is_redex e1 → Γ \ locals k ⊢ₕ safe e1, m.
Proof.
  intros.
  destruct (classic (Γ \ locals k ⊢ₕ safe e1, m)); try assumption.
  edestruct H.
  - eapply rtc_l.
    + rewrite H0.
      eapply cstep_expr_undef; eassumption.
    + apply rtc_refl.
  - inversion H3.
  - destruct H3.
    inversion H3.
Qed.

Lemma eval_soundness Q n e ė k ḳ m ṁ ẽ f:
  expr_equiv e ė Int →
  mem_equiv (mem_unlock_all m) ṁ →
  env_equiv ẽ ê (locals k) →
  ∀(Hlocals_alive: Forall (λ iτ, index_alive '{m} (iτ.1)) (locals k)),
  ch2o_safe_state Γ δ Q (State k (Expr e) m) →
  (∀ n',
   n' ≤ n →
   ∀ Ω ν v m' ṁ',
   ∀(Hlocals_alive: Forall (λ iτ, index_alive '{m'} (iτ.1)) (locals k)),
   ch2o_safe_state Γ δ Q (State k (Expr (%#{ Ω } ν)) m') →
   expr_equiv (%#{ Ω } ν) v Int →
   mem_equiv (mem_unlock_all m') ṁ' →
   compcertc_safe_state_n Q p n' (ExprState f v ḳ ẽ ṁ')) →
  compcertc_safe_state_n Q p n (ExprState f ė ḳ ẽ ṁ).
Proof.
revert e ė m ṁ.
apply well_founded_induction with (1:=lt_wf) (a:=n).
clear n.
intros n IH.
intros e ė m ṁ ? Hmem_equiv Henv_equiv; intros.
intros t s HstarN.
inversion HstarN; subst.
- (* refl *)
  destruct (compcertc_expr_never_stuck f ė ḳ ẽ ṁ).
  + destruct H2 as [v [ty H2]].
    subst.
    inversion H; clear H; subst.
    * unfold compcertc_safe_state_n in H1.
      eapply H1 with (n':=0) (trace:=[]); try eauto.
      constructor.
      assumption.
    * unfold compcertc_safe_state_n in H1.
      eapply H1 with (n':=0) (trace:=[]); try eauto.
      constructor.
  + tauto.
- case_eq (match ė with Eval _ _ => true | _ => false end); intros. {
    inversion H; clear H; subst; try discriminate.
    - unfold compcertc_safe_state_n in H1.
      eapply H1 with (n':=S n0) (6:=HstarN); try eauto.
      constructor.
      assumption.
    - unfold compcertc_safe_state_n in H1.
      eapply H1 with (n':=S n0) (6:=HstarN); try eauto.
      constructor.
  }
  destruct H2. 2:{
    inversion H2; subst; discriminate.
  }
  inversion H2; clear H2; subst.
  + (* step_Lred *)
    rename m' into ṁ'.
    edestruct (lrred_safe _ _ _ H) as [E [e1 [e2 [m' [He1 [He1e2 [Hee' [Hṁ' Hlocals_alive']]]]]]]]; try (eassumption || reflexivity). {
      apply lrred_lred.
      eassumption.
    } { apply ch2o_safe_state_subexpr_safe with (1:=H0). }
    unfold compcertc_safe_state_n in IH.
    subst.
    eapply IH with (2:=Hee') (8:=H3); try eassumption.
    * lia.
    * rewrite Hlocals_alive'; assumption.
    * intro S'.
      intro HS'.
      apply H0.
      eapply rtc_l; try eassumption.
      apply cstep_expr_head.
      apply He1e2.
    * intros n' Hn'.
      apply (H1 n'); lia.
  + (* step_rred *)
    rename m' into ṁ'.
    edestruct (lrred_safe _ _ _ H) as [E [e1 [e2 [m' [He1 [He1e2 [Hee' [Hṁ' Hlocals_alive']]]]]]]]; try (eassumption || reflexivity). {
      apply lrred_rred; eassumption.
    } { apply ch2o_safe_state_subexpr_safe with (1:=H0). }
    unfold compcertc_safe_state_n in IH.
    subst.
    eapply IH with (2:=Hee') (8:=H3); try eassumption.
    * lia.
    * rewrite Hlocals_alive'; assumption.
    * intro S'.
      intro HS'.
      apply H0.
      eapply rtc_l; try eassumption.
      apply cstep_expr_head.
      apply He1e2.
    * intros n' Hn'.
      apply (H1 n'); lia.
  + (* step_call *)
    apply expr_equiv_no_call with (2:=H12) (3:=H13) in H.
    elim H; reflexivity.
  + elim H13; clear H13.
    eapply expr_equiv_subexpr_imm_safe with (1:=H12) (2:=H); try (eassumption || reflexivity).
    apply ch2o_safe_state_subexpr_safe with (1:=H0).
Qed.

Lemma eval_soundness_cast_int Q n e ė k ḳ m ṁ ẽ f:
  expr_equiv e ė Int →
  mem_equiv (mem_unlock_all m) ṁ →
  env_equiv ẽ ê (locals k) →
  ∀(Hlocals_alive: Forall (λ iτ, index_alive '{m} (iτ.1)) (locals k)),
  ch2o_safe_state Γ δ Q (State k (Expr (cast{sintT%T} e)) m) →
  (∀ n',
   n' ≤ n →
   ∀ Ω z m' ṁ',
   int_typed z (sintT: int_type K) →
   ∀(Hlocals_alive: Forall (λ iτ, index_alive '{m'} (iτ.1)) (locals k)),
   ch2o_safe_state Γ δ Q (State k (Expr (#{ Ω } (intV{sintT} z))) m') →
   mem_equiv (mem_unlock_all m') ṁ' →
   compcertc_safe_state_n Q p n' (ExprState f (Eval (Vint (Int.repr z)) tint) ḳ ẽ ṁ')) →
  compcertc_safe_state_n Q p n (ExprState f ė ḳ ẽ ṁ).
Proof.
revert e ė m ṁ.
apply well_founded_induction with (1:=lt_wf) (a:=n).
clear n.
intros n IH.
intros e ė m ṁ ? Hmem_equiv Henv_equiv; intros.
case_eq (match ė with Eval _ _ => true | _ => false end); intros HEval. {
  inversion H; clear H; subst; try discriminate.
  * eapply H1 with (n':=n); try eauto.
    intro; intros.
    apply H0.
    eapply rtc_l; try eassumption.
    apply cstep_expr_head with (E:=[]).
    constructor.
    assumption.
  * eapply ch2o_safe_state_subexpr_safe with (E:=[]) in H0. 2:{
      reflexivity.
    } 2:{ constructor. constructor. }
    inversion H0; clear H0; subst.
    inversion H; clear H; subst.
    inversion H7.
    discriminate.
}
intros t s HstarN.
inversion HstarN; subst.
- (* refl *)
  destruct (compcertc_expr_never_stuck f ė ḳ ẽ ṁ).
  + destruct H2 as [v [ty H3]].
    subst.
    discriminate.
  + tauto.
- destruct H2. 2:{
    inversion H2; subst; discriminate.
  }
  inversion H2; clear H2; subst.
  + (* step_Lred *)
    rename m' into ṁ'.
    edestruct (lrred_safe _ _ _ H) as [E [e1 [e2 [m' [He1 [He1e2 [Hee' [Hṁ' Hlocals_alive']]]]]]]]; try (eassumption || reflexivity). {
      apply lrred_lred.
      eassumption.
    } {
      intros.
      eapply ch2o_safe_state_subexpr_safe with (1:=H0) (3:=H4) (E:=E ++ [CCast (sintT%T)]).
      rewrite H2.
      rewrite subst_snoc; reflexivity.
    }
    unfold compcertc_safe_state_n in IH.
    subst.
    eapply IH with (2:=Hee') (8:=H3); try eassumption.
    * lia.
    * rewrite Hlocals_alive'; assumption.
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
    * intros n' Hn'.
      apply (H1 n'); lia.
  + (* step_rred *)
    rename m' into ṁ'.
    edestruct (lrred_safe _ _ _ H) as [E [e1 [e2 [m' [He1 [He1e2 [Hee' [Hṁ' Hlocals_alive']]]]]]]]; try (eassumption || reflexivity). {
      apply lrred_rred; eassumption.
    } { 
      intros; subst.
      apply ch2o_safe_state_subexpr_safe with (1:=H0) (E:=E++[CCast (sintT%T)]) (3:=H4).
      rewrite subst_snoc; reflexivity.
    }
    unfold compcertc_safe_state_n in IH.
    subst.
    eapply IH with (2:=Hee') (8:=H3); try eassumption.
    * lia.
    * rewrite Hlocals_alive'; assumption.
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
    * intros n' Hn'.
      apply (H1 n'); lia.
  + (* step_call *)
    apply expr_equiv_no_call with (2:=H11) (3:=H12) in H.
    elim H; reflexivity.
  + elim H12; clear H12.
    eapply expr_equiv_subexpr_imm_safe with (1:=H11) (2:=H); try (eassumption || reflexivity).
    intros; subst.
    apply ch2o_safe_state_subexpr_safe with (1:=H0) (3:=H4) (E:=E++[CCast (sintT%T)]).
    rewrite subst_snoc; reflexivity.
Qed.

Lemma eval_soundness_cast_void Q n e ė k ḳ m ṁ ẽ f:
  expr_equiv e ė Int →
  mem_equiv (mem_unlock_all m) ṁ →
  env_equiv ẽ ê (locals k) →
  ∀(Hlocals_alive: Forall (λ iτ, index_alive '{m} (iτ.1)) (locals k)),
  ch2o_safe_state Γ δ Q (State k (Expr (cast{voidT%T} e)) m) →
  (∀ n',
   n' ≤ n →
   ∀ Ω v ṿ ty m' ṁ',
   ∀(Hlocals_alive: Forall (λ iτ, index_alive '{m'} (iτ.1)) (locals k)),
   ch2o_safe_state Γ δ Q (State k (Expr (#{ Ω } v)) m') →
   mem_equiv (mem_unlock_all m') ṁ' →
   compcertc_safe_state_n Q p n' (ExprState f (Eval ṿ ty) ḳ ẽ ṁ')) →
  compcertc_safe_state_n Q p n (ExprState f ė ḳ ẽ ṁ).
Proof.
revert e ė m ṁ.
apply well_founded_induction with (1:=lt_wf) (a:=n).
clear n.
intros n IH.
intros e ė m ṁ ? Hmem_equiv Henv_equiv; intros.
case_eq (match ė with Eval _ _ => true | _ => false end); intros HEval. {
  inversion H; clear H; subst; try discriminate.
  * eapply H1 with (n':=n); try eauto.
    intro; intros.
    apply H0.
    eapply rtc_l; try eassumption.
    apply cstep_expr_head with (E:=[]).
    constructor.
    constructor.
  * eapply ch2o_safe_state_subexpr_safe with (E:=[]) in H0. 2:{
      reflexivity.
    } 2:{ constructor. constructor. }
    inversion H0; clear H0; subst.
    inversion H; clear H; subst.
    inversion H7.
}
intros t s HstarN.
inversion HstarN; subst.
- (* refl *)
  destruct (compcertc_expr_never_stuck f ė ḳ ẽ ṁ).
  + destruct H2 as [v [ty H3]].
    subst.
    discriminate.
  + tauto.
- destruct H2. 2:{
    inversion H2; subst; discriminate.
  }
  inversion H2; clear H2; subst.
  + (* step_Lred *)
    rename m' into ṁ'.
    edestruct (lrred_safe _ _ _ H) as [E [e1 [e2 [m' [He1 [He1e2 [Hee' [Hṁ' Hlocals_alive']]]]]]]]; try (eassumption || reflexivity). {
      apply lrred_lred.
      eassumption.
    } {
      intros.
      eapply ch2o_safe_state_subexpr_safe with (1:=H0) (3:=H4) (E:=E ++ [CCast (voidT%T)]).
      rewrite H2.
      rewrite subst_snoc; reflexivity.
    }
    unfold compcertc_safe_state_n in IH.
    subst.
    eapply IH with (2:=Hee') (8:=H3); try eassumption.
    * lia.
    * rewrite Hlocals_alive'; assumption.
    * intro S'.
      intro HS'.
      apply H0.
      eapply rtc_l; try eassumption.
      assert (∀ e, cast{voidT%T} (subst E e) = subst (E ++ [CCast (voidT%T)]) e)%E. {
        intros; rewrite subst_snoc.
        reflexivity.
      }
      rewrite 2 H2.
      apply cstep_expr_head.
      apply He1e2.
    * intros n' Hn'.
      apply (H1 n'); lia.
  + (* step_rred *)
    rename m' into ṁ'.
    edestruct (lrred_safe _ _ _ H) as [E [e1 [e2 [m' [He1 [He1e2 [Hee' [Hṁ' Hlocals_alive']]]]]]]]; try (eassumption || reflexivity). {
      apply lrred_rred; eassumption.
    } { 
      intros; subst.
      apply ch2o_safe_state_subexpr_safe with (1:=H0) (E:=E++[CCast (voidT%T)]) (3:=H4).
      rewrite subst_snoc; reflexivity.
    }
    unfold compcertc_safe_state_n in IH.
    subst.
    eapply IH with (2:=Hee') (8:=H3); try eassumption.
    * lia.
    * rewrite Hlocals_alive'; assumption.
    * intro S'.
      intro HS'.
      apply H0.
      eapply rtc_l; try eassumption.
      assert (∀ e, cast{voidT%T} (subst E e) = subst (E ++ [CCast (voidT%T)]) e)%E. {
        intros; rewrite subst_snoc.
        reflexivity.
      }
      rewrite 2 H2.
      apply cstep_expr_head.
      apply He1e2.
    * intros n' Hn'.
      apply (H1 n'); lia.
  + (* step_call *)
    apply expr_equiv_no_call with (2:=H11) (3:=H12) in H.
    elim H; reflexivity.
  + elim H12; clear H12.
    eapply expr_equiv_subexpr_imm_safe with (1:=H11) (2:=H); try (eassumption || reflexivity).
    intros; subst.
    apply ch2o_safe_state_subexpr_safe with (1:=H0) (3:=H4) (E:=E++[CCast (voidT%T)]).
    rewrite subst_snoc; reflexivity.
Qed.

Lemma stmt_soundness Q f s ṡ:
  stmt_equiv s ṡ →
  ∀ n k ḳ m ṁ ẽ,
  mem_equiv (mem_unlock_all m) ṁ →
  env_equiv ẽ ê (locals k) →
  ∀(Hlocals_alive: Forall (λ iτ, index_alive '{m} (iτ.1)) (locals k)),
  ch2o_safe_state Γ δ Q (State k (Stmt ↘ s) m) →
  (∀ n',
   n' ≤ n →
   ∀ m' ṁ',
   ∀(Hlocals_alive: Forall (λ iτ, index_alive '{m'} (iτ.1)) (locals k)),
   ch2o_safe_state Γ δ Q (State k (Stmt ↗ s) m') →
   mem_equiv (mem_unlock_all m') ṁ' →
   compcertc_safe_state_n Q p n' (Csem.State f Sskip ḳ ẽ ṁ')) →
  (∀ n',
   n' ≤ n →
   ∀ z ḳ' m' ṁ',
   int_typed z (sintT: int_type K) →
   call_cont ḳ' = call_cont ḳ →
   mem_equiv (mem_unlock_all m') ṁ' →
   ∀(Hlocals_alive: Forall (λ iτ, index_alive '{m'} (iτ.1)) (locals k)),
   ch2o_safe_state Γ δ Q (State k (Stmt (⇈ (intV{sintT} z)) s) m') →
   compcertc_safe_state_n Q p n' (ExprState f (Eval (Vint (Int.repr z)) tint) (Kreturn ḳ') ẽ ṁ')) →
  compcertc_safe_state_n Q p n (Csem.State f ṡ ḳ ẽ ṁ).
Proof.
(* TODO: When adding support for loops, we'll need to perform well-founded induction on n here as well. *)
induction 1; intros n k ḳ m ṁ ẽ Hmem_equiv Henv_equiv; intros.
- (* return *)
  intro; intros.
  inversion H3; clear H3; subst. {
    right.
    eexists; eexists.
    right.
    constructor.
  }
  inversion H4; clear H4; subst; inversion H3; clear H3; subst; try intuition discriminate.
  eapply eval_soundness_cast_int with (k:=CExpr (cast{sintT%T} e) CReturnE :: k); try eassumption. {
    intro; intros.
    eapply H0.
    eapply rtc_l; [|eassumption].
    apply cstep_expr with (E:=CReturnE).
  }
  intros.
  eapply H2 with (m':=mem_unlock Ω m'); try eassumption.
  + lia.
  + reflexivity.
  + rewrite mem_unlock_all_mem_unlock.
    eassumption.
  + rewrite mem_unlock_memenv_of.
    assumption.
  + intro; intros.
    eapply H6.
    eapply rtc_l; [|eassumption].
    constructor.
- (* skip *)
  intros.
  eapply H0; try eassumption.
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
  eapply IHstmt_equiv1 with (n:=n0) (ḳ:=Kseq ṡ2 ḳ). 4:{
    intro; intros.
    eapply H1.
    eapply rtc_l; [|eassumption].
    constructor.
  } { eassumption. } { eassumption. } { eassumption. } 2:{
    intros.
    eapply H3; try eassumption. { lia. }
    intro; intros.
    eapply H9.
    eapply rtc_l; [|eassumption].
    constructor.
  } 2:{
    eassumption.
  }
  intros.
  intro; intros.
  inversion H8; clear H8; subst. {
    right.
    eexists; eexists.
    right.
    constructor.
  }
  inversion H9; clear H9; subst; inversion H8; clear H8; subst. 2:{
    inversion H16.
  }
  eapply IHstmt_equiv2. 4:{
    intro; intros.
    eapply H5.
    eapply rtc_l; [|eassumption].
    constructor.
  } { eassumption. } { eassumption. } { eassumption. } 3:{ eassumption. } 2:{
    intros.
    intro; intros.
    eapply H3; try eassumption.
    + lia.
    + intro; intros.
      eapply H13.
      eapply rtc_l; [|eassumption].
      constructor.
  }
  intros.
  eapply H2; try eassumption.
  + lia.
  + intro; intros.
    eapply H9.
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
  eapply eval_soundness with (k:=CExpr e (CIfE s1 s2) :: k); try eassumption. {
    intro; intros.
    eapply H2.
    eapply rtc_l; [|eassumption].
    apply cstep_expr with (E:=CIfE s1 s2).
  }
  intros.
  intro; intros.
  inversion H10; clear H10; subst. {
    right.
    inversion H8; clear H8; subst.
    - eexists; eexists.
      right.
      eapply step_ifthenelse_2.
      unfold bool_val.
      simpl.
      reflexivity.
    - edestruct H6.
      + eapply rtc_l.
        * apply cstep_expr_if_indet.
          intro.
          inversion H8.
        * apply rtc_refl.
      + inversion H8.
      + destruct H8.
        inversion H8.
  }
  inversion H11; clear H11; subst; inversion H10; clear H10; subst. {
    inversion H8; subst; inversion H20; clear H20; subst; try discriminate.
  } {
    inversion H8; subst; inversion H20; clear H20; subst; try discriminate;
    subst;
    inversion H19; clear H19; subst.
  } {
    inversion H8; subst; inversion H20; clear H20; subst; try discriminate;
    subst;
    inversion H19; clear H19; subst.
  } {
    inversion H8; subst; inversion H19; clear H19; subst; try discriminate;
    subst;
    elim H20; constructor.
  }
  inversion H8; subst; try discriminate.
  unfold bool_val in H21.
  simpl in H21.
  injection H21; clear H21; intros; subst.
  rewrite Int.eq_signed in H12.
  rewrite Int.signed_repr in H12. 2:{
    apply int_typed_limits; assumption.
  }
  rewrite Int.signed_zero in H12.
  destruct (Coqlib.zeq z 0); simpl in H12.
  + (* z = 0 *)
    subst.
    eapply IHstmt_equiv2. 7:{ eassumption. } 4:{
      intro; intros.
      eapply H6.
      eapply rtc_l; [|eassumption].
      apply cstep_expr_if_false.
      - simpl. constructor.
      - constructor.
    } {
      rewrite mem_unlock_all_mem_unlock; eassumption.
    } {
      eassumption.
    } {
      rewrite mem_unlock_memenv_of.
      assumption.
    } 2:{
      intros.
      eapply H4; try eassumption.
      - lia.
      - intro; intros.
        eapply H16.
        eapply rtc_l; [|eassumption].
        constructor.
    }
    intros.
    eapply H3; try eassumption.
    * lia.
    * intro; intros.
      eapply H13.
      eapply rtc_l; [|eassumption].
      constructor.
  + (* z ≠ 0 *)
    eapply IHstmt_equiv1. 7:{ eassumption. } 4:{
      intro; intros.
      eapply H6.
      eapply rtc_l; [|eassumption].
      constructor.
      - constructor.
      - intro.
        elim n1.
        inversion H13; clear H13; subst.
        reflexivity.
    } {
      rewrite mem_unlock_all_mem_unlock.
      eassumption.
    } {
      eassumption.
    } {
      rewrite mem_unlock_memenv_of; assumption.
    } 2:{
      intros.
      eapply H4; try eassumption.
      - lia.
      - intro; intros.
        eapply H16.
        eapply rtc_l; [|eassumption].
        constructor.
    }
    intros.
    eapply H3; try eassumption.
    * lia.
    * intro; intros.
      eapply H13.
      eapply rtc_l; [|eassumption].
      constructor.
- intro; intros.
  inversion H3; clear H3; subst. {
    right.
    eexists; eexists; right.
    constructor.
  }
  inversion H4; clear H4; subst; inversion H3; clear H3; subst; try destruct H12; try discriminate.
  eapply eval_soundness_cast_void with (k:=CExpr (cast{voidT%T} e) CDoE :: k). eassumption. eassumption. 5:{ eassumption. } 3:{
    intro; intros.
    eapply H0.
    eapply rtc_l.
    - eapply cstep_expr with (E:=CDoE).
    - eassumption.
  } { eassumption. } { eassumption. }
  intros.
  intro; intros.
  inversion H7; clear H7; subst. {
    right.
    eexists; eexists; right.
    constructor.
  }
  inversion H8; clear H8; subst; inversion H7; clear H7; subst; try discriminate. {
    inversion H17; clear H17; subst; try discriminate.
  } {
    inversion H17; clear H17; subst; try discriminate; subst.
    inversion H16; clear H16; subst.
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
  eapply H1. 5:{
    eassumption.
  } { lia. } 2:{
    intro; intros.
    eapply H4; try eassumption.
    eapply rtc_l.
    * constructor.
    * eassumption.
  } {
    rewrite mem_unlock_memenv_of; assumption.
  }
  rewrite mem_unlock_all_mem_unlock.
  eassumption.
Qed.

End Locals.

Lemma mem_lookup_mem_alloc_ne m b v b1:
  b1 ≠ b →
  m !!{Γ} addr_top (N.pos b) sintT = Some v →
  mem_alloc Γ (N.pos b1) false perm_full (val_new Γ sintT) m
    !!{Γ} addr_top (N.pos b) sintT = Some v.
Proof.
  intros ?.
  destruct m as [m].
  simpl.
  unfold mem_lookup.
  simpl.
  unfold cmap_lookup.
  rewrite option_guard_True. 2:{ constructor. simpl. lia. }
  simpl.
  rewrite lookup_insert_ne. 2:{ congruence. }
  tauto.
Qed.

Lemma list_norepet_rev {A} (xs: list A):
  Coqlib.list_norepet xs → Coqlib.list_norepet (rev xs).
Proof.
  induction xs; simpl; intros.
  - constructor.
  - inversion H; clear H; subst.
    apply Coqlib.list_norepet_append_commut.
    constructor.
    + intro.
      elim H2.
      apply In_rev.
      assumption.
    + auto.
Qed.

Lemma free_list_app_elim ṁ0 xs ys ṁ2:
  Memory.Mem.free_list ṁ0 (xs ++ ys) = Some ṁ2 →
  ∃ ṁ1,
  Memory.Mem.free_list ṁ0 xs = Some ṁ1 /\
  Memory.Mem.free_list ṁ1 ys = Some ṁ2.
Proof.
  revert ṁ0.
  induction xs; intros.
  - exists ṁ0.
    split. {
      reflexivity.
    }
    assumption.
  - inversion H; clear H; subst.
    destruct a.
    destruct p0.
    case_eq (Memory.Mem.free ṁ0 b z0 z); intros; rewrite H in H1; try discriminate.
    rename m into ṁ0'.
    destruct (IHxs _ H1) as [ṁ1 [? ?]].
    exists ṁ1.
    split. {
      simpl.
      rewrite H.
      assumption.
    }
    congruence.
Qed.

Lemma free_list_app_intro ṁ0 xs ṁ1 ys ṁ2:
  Memory.Mem.free_list ṁ0 xs = Some ṁ1 →
  Memory.Mem.free_list ṁ1 ys = Some ṁ2 →
  Memory.Mem.free_list ṁ0 (xs ++ ys) = Some ṁ2.
Proof.
  revert ṁ0.
  induction xs; intros.
  - simpl in H.
    inversion H; clear H; subst.
    assumption.
  - inversion H; clear H; subst.
    destruct a.
    destruct p0.
    case_eq (Memory.Mem.free ṁ0 b z0 z); intros; rewrite H in H2; try discriminate.
    rename m into ṁ0'.
    simpl.
    rewrite H.
    apply IHxs; assumption.
Qed.

Lemma alloc_variables_soundness Q f ê ê' s ṡ:
  Coqlib.list_norepet (ê ++ ê') →
  stmt_equiv (rev (ê ++ ê')) s ṡ →
  ∀ n k ḳ m ṁ0 ṁ ẽ0 ẽ,
  mem_equiv (mem_unlock_all m) ṁ0 →
  env_equiv ẽ0 (rev ê) (locals k) →
  alloc_variables (globalenv p) ẽ0 ṁ0 (map (λ x, (x, tint)) ê') ẽ ṁ →
  ∀(Hlocals_alive: Forall (λ iτ, index_alive '{m} (iτ.1)) (locals k)),
  ch2o_safe_state Γ δ Q (State k (Stmt ↘ (Nat.iter (length ê') (λ s, local{sintT} s) s)) m) →
  (∀ m',
   ch2o_safe_state Γ δ Q (State k (Stmt ↗ (Nat.iter (length ê') (λ s, local{sintT} s) s)) m') →
   False) →
  (∀ n',
   n' ≤ n →
   ∀ z ḳ' m' ṁ'0 ṁ',
   int_typed z (sintT: int_type K) →
   call_cont ḳ' = call_cont ḳ →
   (∀ x, In x ê → Maps.PTree.get x ẽ = Maps.PTree.get x ẽ0) →
   Memory.Mem.free_list ṁ'0 (map (λ x, match Maps.PTree.get x ẽ with None => (1%positive, 0%Z, 0%Z) | Some (b, τ) => (b, 0%Z, sizeof (globalenv p) τ) end) (rev ê')) = Some ṁ' →
   mem_equiv (mem_unlock_all m') ṁ' →
   ∀(Hlocals_alive: Forall (λ iτ, index_alive '{m'} (iτ.1)) (locals k)),
   ch2o_safe_state Γ δ Q (State k (Stmt (⇈ (intV{sintT} z)) (Nat.iter (length ê') (λ s, local{sintT} s) s)) m') →
   compcertc_safe_state_n Q p n' (ExprState f (Eval (Vint (Int.repr z)) tint) (Kreturn ḳ') ẽ ṁ'0)) →
  compcertc_safe_state_n Q p n
    (Csem.State f (Ssequence ṡ (Sreturn (Some (Eval (Vint (Int.repr 0)) tint)))) ḳ ẽ ṁ).
Proof.
  revert ê' ê.
  induction ê'; intros.
  - intro; intros.
    inversion H7; clear H7; subst. {
      right.
      eexists; eexists.
      right.
      constructor.
    }
    inversion H8; clear H8; subst; inversion H7; clear H7; subst; try (destruct H16); try discriminate.
    inversion H3; clear H3; subst.
    eapply stmt_soundness. 8:{ eassumption. } eassumption. eassumption. {
      rewrite app_nil_r. eassumption.
    } eassumption. eassumption. 2:{
      intros.
      eapply H6. lia. assumption. assumption. reflexivity. reflexivity. eassumption.
      assumption. assumption.
    }
    intros.
    (* Ssequence *)
    apply H5 in H7.
    tauto.
  - rename a into x.
    simpl in H3.
    inversion H3; clear H3; subst.
    rename m1 into ṁ0'.
    destruct H1.
    assert (Hdom: (N.pos b1: index) ∉ dom indexset m). {
      rewrite <- dom_mem_unlock_all.
      apply domains_equiv0.
      rewrite Memory.Mem.alloc_result with (1:=H14).
      reflexivity.
    }
    eapply IHê' with (ê:=(ê ++ [x])%list). {
     rewrite <- app_assoc. assumption.
    } {
      rewrite <- app_assoc. assumption.
    } 3:{
      eassumption.
    } 4:{
      intro; intros.
      eapply H4.
      eapply rtc_l; [|eassumption].
      apply cstep_in_block with (o:=Npos b1).
      - constructor.
      - assumption.
    } {
      split.
      - intros.
        destruct (classic (b = b1)).
        + subst.
          apply block_equiv_alloced with (oz:=None).
          * apply Memory.Mem.load_alloc_same' with (1:=H14).
            -- reflexivity.
            -- reflexivity.
            -- simpl.
               apply Z.divide_0_r.
          * intros.
            eapply Memory.Mem.valid_access_implies.
            apply Memory.Mem.valid_access_alloc_same with (1:=H14).
            -- reflexivity.
            -- reflexivity.
            -- simpl; apply Z.divide_0_r.
            -- constructor.
          * intro; intros.
            apply Memory.Mem.perm_alloc_2 with (1:=H14).
            assumption.
          * rewrite memenv_of_mem_unlock_all.
            apply mem_alloc_new_index_alive'.
            -- assumption.
            -- constructor.
               constructor.
          * rewrite memenv_of_mem_unlock_all.
            constructor.
            -- eapply mem_alloc_new_index_typed'.
               ++ assumption.
               ++ constructor; constructor.
            -- constructor; constructor.
            -- constructor.
            -- reflexivity.
            -- simpl.
               lia.
            -- apply Nat.divide_0_r.
            -- constructor.
          * erewrite mem_unlock_all_lookup. reflexivity.
            erewrite mem_lookup_alloc; try eassumption.
            -- reflexivity.
            -- apply val_new_typed.
               ++ assumption.
               ++ constructor; constructor.
            -- constructor.
          * apply mem_writable_unlock_all.
            eapply mem_alloc_writable_top.
            -- assumption.
            -- apply val_new_typed.
               ++ assumption.
               ++ constructor; constructor.
            -- constructor.
          * constructor.
        + destruct (blocks_equiv0 b).
          * apply block_equiv_not_alloced.
            rewrite memenv_of_mem_unlock_all.
            intro.
            elim H3.
            erewrite mem_alloc_memenv_of in H7.
            -- eapply mem_alloc_index_alive_inv. 2:{ rewrite memenv_of_mem_unlock_all. eassumption. }
               congruence.
            -- assumption.
            -- apply val_new_typed.
               ++ assumption.
               ++ constructor; constructor.
          * apply block_equiv_alloced with (oz:=oz).
            -- apply Memory.Mem.load_alloc_other with (1:=H14) (2:=H3).
            -- apply Memory.Mem.valid_access_alloc_other with (1:=H14).
               assumption.
            -- intro; intros.
               apply Memory.Mem.perm_alloc_1 with (1:=H14).
               apply H8; assumption.
            -- rewrite memenv_of_mem_unlock_all.
               erewrite mem_alloc_memenv_of.
               ++ rewrite memenv_of_mem_unlock_all in H9.
                  apply mem_alloc_index_alive_ne; try assumption.
                  congruence.
               ++ assumption.
               ++ apply val_new_typed.
                  ** assumption.
                  ** constructor; constructor.
            -- rewrite memenv_of_mem_unlock_all.
               apply addr_top_typed.
               ++ assumption.
               ++ eapply memenv_forward_typed.
                  ** apply mem_alloc_new_forward'.
                     --- assumption.
                     --- assumption.
                     --- constructor; constructor.
                  ** inversion H10; clear H10; subst.
                     rewrite memenv_of_mem_unlock_all in H22.
                     assumption.
               ++ constructor; constructor.
           -- rewrite mem_unlock_all_mem_alloc. 2:{ reflexivity. }
              apply mem_lookup_mem_alloc_ne. { congruence. }
              assumption.
           -- rewrite mem_unlock_all_mem_alloc. 2:{ reflexivity. }
              apply mem_alloc_writable.
              ++ exact sintT%T.
              ++ rewrite dom_mem_unlock_all.
                 assumption.
              ++ assumption.
           -- assumption.
      - intros.
        rewrite dom_mem_unlock_all.
        rewrite mem_dom_alloc.
        rewrite Memory.Mem.alloc_result with (1:=H14).
        rewrite Memory.Mem.nextblock_alloc with (1:=H14) in H1.
        rewrite elem_of_union.
        intro.
        destruct H3.
        + rewrite elem_of_singleton in H3.
          injection H3; clear H3; intros; subst.
          lia.
        + rewrite <- dom_mem_unlock_all in H3.
          apply domains_equiv0 in H3. assumption.
          lia.
      - rewrite mem_unlock_all_mem_alloc. 2:{ reflexivity. }
        apply mem_alloc_new_valid'; try eassumption.
        + rewrite dom_mem_unlock_all. assumption.
        + apply perm_full_valid.
        + apply perm_full_mapped.
        + constructor; constructor.
    } {
      simpl.
      rewrite rev_app_distr.
      simpl.
      constructor.
      - apply Maps.PTree.gss.
      - assert (ê ++ x :: ê' = (ê ++ [x]) ++ ê')%list. {
          rewrite <- app_assoc.
          reflexivity.
        }
        rewrite H1 in H.
        apply Coqlib.list_norepet_append_left in H.
        apply list_norepet_rev in H.
        revert H.
        revert H2.
        rewrite rev_app_distr.
        simpl.
        generalize (locals k).
        induction (rev ê); intros.
        + inversion H2; clear H2; subst.
          constructor.
        + inversion H2; clear H2; subst.
          inversion H; clear H; subst.
          inversion H9; clear H9; subst.
          constructor.
          * rewrite Maps.PTree.gso. assumption.
            intro; subst.
            elim H7.
            left.
            reflexivity.
          * apply IHl. assumption.
            constructor.
            -- intro.
               elim H7.
               right.
               assumption.
            -- assumption.
    } {
      constructor.
      - eapply mem_alloc_index_alive'. assumption.
        apply val_new_typed. assumption. { constructor; constructor. }
      - apply Forall_impl with (1:=Hlocals_alive); intros.
        erewrite mem_alloc_memenv_of with (τ:=sintT%T).
        + destruct (classic (x0.1 = N.pos b1)).
          * rewrite H3.
            eapply mem_alloc_index_alive.
          * eapply mem_alloc_index_alive_ne. congruence. assumption.
        + assumption.
        + apply val_new_typed.
          * assumption.
          * constructor; constructor.
    } 2:{
      intros.
      destruct H10.
      inversion Hlocals_alive0; clear Hlocals_alive0; subst.
      destruct (blocks_equiv1 b1). {
        rewrite memenv_of_mem_unlock_all in H10.
        elim (H10 H13).
      }
      destruct (Memory.Mem.range_perm_free ṁ' b1 0 4 H17) as [ṁ'1 Hṁ'1].
      eapply H6. lia. assumption. assumption. {
        intros.
        rewrite H8. 2:{ apply in_or_app. left. assumption. }
        assert (ê ++ x :: ê' = (ê ++ [x]) ++ ê')%list. {
          rewrite <- app_assoc.
          reflexivity.
        }
        rewrite H24 in H.
        apply Coqlib.list_norepet_append_left in H.
        apply list_norepet_rev in H.
        rewrite rev_app_distr in H.
        inversion H; clear H; subst.
        rewrite <- In_rev in H27.
        apply Maps.PTree.gso.
        intro; subst; tauto.
      } {
        simpl.
        rewrite map_app.
        eapply free_list_app_intro.
        - apply H9.
        - simpl.
          rewrite H8. 2:{ apply in_or_app; right. left. reflexivity. }
          rewrite Maps.PTree.gss.
          assert (sizeof (prog_comp_env p) tint = 4%Z). reflexivity.
          rewrite H23.
          rewrite Hṁ'1.
          reflexivity.
      } 3:{
        intro; intros.
        eapply H11; try eassumption.
        eapply rtc_l; [|eassumption].
        constructor.
        constructor.
      } {
        split.
        - intros.
          destruct (classic (b = b1)).
          + subst.
            apply block_equiv_not_alloced.
            rewrite memenv_of_mem_unlock_all.
            rewrite mem_free_memenv_of.
            apply mem_free_index_alive.
          + destruct (blocks_equiv1 b).
            * apply block_equiv_not_alloced.
              rewrite memenv_of_mem_unlock_all.
              rewrite memenv_of_mem_unlock_all in H24.
              rewrite mem_free_memenv_of.
              intro.
              elim H24.
              apply mem_free_index_alive_inv with (1:=H25).
            * apply block_equiv_alloced with (oz:=oz0).
              -- unfold Memory.Mem.loadv.
                 rewrite Memory.Mem.load_free with (1:=Hṁ'1).
                 ++ apply H24.
                 ++ tauto.
              -- apply Memory.Mem.valid_access_free_1 with (1:=Hṁ'1) (2:=H25). tauto.
              -- intro; intros.
                 apply Memory.Mem.perm_free_1 with (1:=Hṁ'1). tauto.
                 apply H26; assumption.
              -- rewrite memenv_of_mem_unlock_all.
                 rewrite memenv_of_mem_unlock_all in H27.
                 rewrite mem_free_memenv_of.
                 apply mem_free_index_alive_ne. congruence.
                 assumption.
              -- apply addr_top_typed.
                 ++ assumption.
                 ++ rewrite memenv_of_mem_unlock_all.
                    eapply memenv_forward_typed.
                    ** rewrite mem_free_memenv_of.
                       apply mem_free_forward.
                    ** inversion H28; subst.
                       rewrite memenv_of_mem_unlock_all in H38.
                       assumption.
                 ++ constructor; constructor.
              -- 
              

            
    
Inductive program_equiv: Prop :=
| program_equiv_intro ê s ṡ b:
  stringmap_lookup "main" δ = Some (Nat.iter (length ê) (λ s, local{sintT} s) s) →
  Genv.init_mem p <> None →
  let ge := globalenv p in
  Genv.find_symbol ge p.(prog_main) = Some b →
  let f := {|
    fn_return:=type_int32s;
    fn_callconv:=AST.cc_default;
    fn_params:=nil;
    fn_vars:=rev (map (λ x, (x, tint)) ê);
    fn_body:=
      Ssequence
        ṡ 
        (Sreturn (Some (Eval (Vint (Int.repr 0)) (Tint I32 Signed noattr))))
  |} in
  Coqlib.list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) →
  Genv.find_funct_ptr ge b = Some (Internal f) →
  stmt_equiv ê s ṡ →
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

Lemma alloc_variables_not_stuck ṁ ẽ xs:
  ∃ ẽ' ṁ', alloc_variables (globalenv p) ẽ ṁ xs ẽ' ṁ'.
Proof.
  revert ẽ ṁ.
  induction xs; intros.
  - eexists; eexists; constructor.
  - destruct a as [x τ].
    case_eq (Memory.Mem.alloc ṁ 0 (sizeof (globalenv p) τ)); intros ṁ' b ?.
    destruct (IHxs (Maps.PTree.set x (b, τ) ẽ) ṁ') as [ẽ'' [ṁ'' ?]].
    eexists; eexists; econstructor; eassumption.
Qed.

Lemma alloc_variables_app:
  ∀ xs ẽ ṁ ys ẽ' ṁ',
  alloc_variables (globalenv p) ẽ ṁ (xs ++ ys)%list ẽ' ṁ' →
  ∃ ẽ'' ṁ'', alloc_variables (globalenv p) ẽ ṁ xs ẽ'' ṁ'' /\ alloc_variables (globalenv p) ẽ'' ṁ'' ys ẽ' ṁ'.
Proof.
  induction xs; intros.
  - eexists; eexists.
    split. constructor. assumption.
  - destruct a as [x τ].
    inversion H; clear H; subst.
    rename m1 into ṁ'''.
    rename b1 into b.
    destruct (IHxs _ _ _ _ _ H8) as [ẽ'' [ṁ'' [? ?]]].
    eexists; eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

(*
Lemma alloc_variables_soundness :
  alloc_variables (globalenv p) ṁ ẽ (foldr (λ x xs, ((x, tint)::xs)) [] ê) ṁ' ẽ' →
  mem_equiv ṁ' env_equiv
*)

Theorem soundness Q:
  program_equiv →
  ch2o_safe_program Γ δ Q →
  compcertc_safe_program Q p.
Proof.
intros Hequiv Hch2o.
destruct Hequiv.
case_eq (Genv.init_mem p). 2:{ intros; tauto. }
intros ṁ ?. clear H0; rename H4 into H0.
econstructor. { econstructor; try eassumption. reflexivity. }
intro n; intro; intros.
(* Callstate *)
inversion H4; clear H4; subst. {
  right.
  edestruct alloc_variables_not_stuck as [? [? ?]].
  eexists.
  eexists.
  right.
  eapply step_internal_function. {
    assumption.
  } {
    eassumption.
  } {
    constructor.
  }
}
inversion H6; clear H6; subst; inversion H4; clear H4; subst.
inversion H15; clear H15; subst.
rename m2 into ṁ1.
rename e into ẽ.
simpl in H7.
(* Allocating the locals *)
revert H7.
simpl in H13.
simpl in H14.
revert H14.
revert H13.
revert ẽ ṁ1.
inversion Hch2o.

(* Ssequence *)
inversion H7; clear H7; subst. {
  right.
  eexists.
  eexists.
  right.
  constructor.
}
inversion H4; clear H4; subst; inversion H7; clear H7; subst.
(* Executing the body *)
eapply stmt_soundness; try eassumption. {
  
} {
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
