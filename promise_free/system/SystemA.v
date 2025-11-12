Require Import CRIS.
Require Export PFMemHeader SystemHeader SystemI.
Require Import HistoryRA AtomicRA LatticeRA.
From iris.algebra Require Export csum gmap_view.
From iris.bi Require Export fractional.

Class sysG `{!crisG Γ Σ α β τ _S _I} := {
  sys_inG :: inG (gmap_viewUR Ident.t (agreeR TViewO)) Γ
}.

Section SystemRA.
  Context `{!crisG Γ Σ α β τ _S _I, !histG, !atomicG, !sysG}.

  Definition tview_sys_auth (ths : gmap Ident.t TView.t) : iProp Σ :=
    (own base_γ (gmap_view_auth (DfracOwn 1) (to_agree <$> ths)) ∗
    [∗ map] tid ↦ 𝓥 ∈ ths, tview tid 𝓥).

  Definition tview_sys_gen (q : Qp) (tid : Ident.t) (𝓥 : TView.t) : iProp Σ :=
    own base_γ (gmap_view_frag tid (DfracOwn q) (to_agree 𝓥)).

  Definition tview_sys (tid : Ident.t) (𝓥 : TView.t) : iProp Σ :=
    tview_sys_gen 1 tid 𝓥.

  Lemma tview_sys_lookup (ths : gmap Ident.t TView.t) (tid : Ident.t) (𝓥 : TView.t) (q : Qp) :
    tview_sys_auth ths -∗
    tview_sys_gen q tid 𝓥 -∗
    ⌜ ths !! tid = Some 𝓥 ⌝.
  Proof.
    rewrite /tview_sys_auth /tview_sys /tview_sys_gen; iIntros "[TA TVS] TV".
    iCombine "TA TV" gives %[𝓥' [? [_ [Hlookup [_ Hincl]]]]]%gmap_view_both_dfrac_valid_discrete.
    rewrite lookup_fmap fmap_Some in Hlookup; destruct Hlookup as [𝓥'' [Hlookup ->]].
    eapply Some_pair_included_r in Hincl.
    rewrite Some_included_total to_agree_included_L in Hincl; subst; done.
  Qed.

  Instance tview_sys_gen_fractional tid 𝓥 : Fractional (λ q, tview_sys_gen q tid 𝓥).
  Proof. ii; by rewrite /tview_sys_gen -own_op -gmap_view_frag_add agree_idemp. Qed.

  #[global] Instance tview_sys_gen_as_fractional tid 𝓥 q :
    AsFractional (tview_sys_gen q tid 𝓥) (λ q, tview_sys_gen q tid 𝓥) q.
  Proof. split; ss; typeclasses eauto. Qed.
End SystemRA.

Module SystemA. Section SystemA.
  Context `{!crisG Γ Σ α β τ _S _I, !histG, !atomicG, !sysG}.
  Context (sp_user : spl_type).

  (* Specifications *)
  Definition fspec_spawnable (fn : string) (pre : TView.t → SAny.t → SAny.t → iProp Σ) : Prop :=
    ∃ fsp, alist_find (Some fn) sp_user = Some (Some fsp) ∧
      fspec_imply
        fsp
        (fspec_winv ⊤
          (fspec_virtual (λ '(tid, V),
            ((λ (varg : SAny.t) (arg : Any.t),
              tview_sys tid V ∗ ∃ sarg, ⌜arg = sarg↑⌝ ∗ pre V varg sarg),
            (λ (vret : SAny.t) _, tview_sys tid V)))))%I.

  Definition _spawn_spec : fspec := 
    fspec_virtual (λ (_ : ()),
      (λ varg arg,
        ∃ (tid : Ident.t) V pre fvarg farg fn,
          ⌜varg = (tid, fn, fvarg) ∧ arg = (tid, fn, farg)↑ ∧ fspec_spawnable fn pre⌝ ∗
          tview_sys_gen (1/2) tid V ∗
          pre V fvarg farg,
      λ (_ : SAny.t) _, False%I))%I.

  Definition spawn_spec (E : coPset) : fspec :=
    fspec_winv E
      (fspec_virtual (λ '(tid, pre, 𝓥),
        ((λ varg arg,
          ∃ fvarg farg fn, ⌜varg = (fn, fvarg) ∧ arg = (fn, farg)↑ ∧ fspec_spawnable fn pre⌝ ∗
            tview_sys tid 𝓥 ∗ pre 𝓥 fvarg farg),
        (λ vret ret, tview_sys tid 𝓥 ∗ ⌜vret = tt ∧ ret = tt↑⌝))))%I.

  Definition yield_spec (E : coPset) : fspec :=
    fspec_winv E
      (fspec_simple (λ '(tid, 𝓥),
        ((λ varg, ⌜varg = tt↑⌝ ∗ tview_sys tid 𝓥),
        (λ vret, ⌜vret = tt↑⌝ ∗ tview_sys tid 𝓥))))%I.

  Definition get_tid_spec : fspec :=
    fspec_simple (λ '(tid, 𝓥),
      ((λ varg, ⌜varg = tt↑⌝ ∗ tview_sys tid 𝓥),
       (λ vret, ⌜vret = tid↑⌝ ∗ tview_sys tid 𝓥)))%I.

  Definition alloc_spec : fspec :=
    fspec_simple (X := Ident.t * nat * TView.t)
      (λ '(tid, sz, 𝓥),
        ((λ varg, ⌜varg = sz↑⌝ ∗ tview_sys tid 𝓥),
        (λ vret, ∃ loc 𝓥', ⌜vret = (Val.Vptr loc)↑ ∧ TView.le 𝓥 𝓥'⌝ ∗
          tview_sys tid 𝓥' ∗
          †loc…sz ∗
          @{TView.cur 𝓥'} loc ↦∗ repeat Val.Vundef sz)))%I.

  (* non-atomic read *)
  Definition read_spec_0 : fspec :=
    fspec_simple (X:=Ident.t * Loc.t * Ordering.t * Val.t * Qp * TView.t)
      (λ '(tid, loc, ord, v, q, 𝓥),
        ((λ varg, ⌜varg = (loc, ord)↑⌝ ∗
          @{TView.cur 𝓥} loc ↦{q} v ∗ tview_sys tid 𝓥),
         (λ vret, ∃ v' 𝓥', ⌜vret = v'↑ ∧ Val.le v' v⌝ ∗
          @{TView.cur 𝓥'} loc ↦{q} v ∗ tview_sys tid 𝓥')))%I.

  (* atomic read *)
  (* TODO : give variants of this specification (SW, SYNC, CAS, ...) *)
  Definition read_spec_1 : fspec :=
    fspec_simple
      (X:=Ident.t * Loc.t * Ordering.t * Cell.t * Cell.t * Time.t * positive * Qp * AtomicMode * TView.t * View.t)
      (λ '(tid, loc, ord, ζ, ζ', t, γ, q, mode, 𝓥, Vb),
        ((λ varg,
          ⌜varg = (loc, ord)↑ ∧ Ordering.le Ordering.relaxed ord⌝ ∗
          @{TView.cur 𝓥} loc sn⊒{γ} ζ' ∗ (* ζ' abstract history seen by current thread *)
          @{Vb} AtomicPtsToX loc γ t ζ mode ∗ (* ζ global abstract history *)
          tview_sys tid 𝓥), (* 𝓥 current thread view *)
        (λ vret, ∃ ζ'' f' na v' v'' V' 𝓥',
          ⌜vret = v'↑ ∧
          Val.le v' v'' ∧
          Cell.le ζ' ζ'' ∧
          Cell.le ζ'' ζ ∧
          Cell.get (Cell.max_ts ζ'') ζ'' = Some (f', Message.message v'' V' na) ∧
          (TView.cur 𝓥) ⊑ (TView.cur 𝓥') ∧
          V' ⊑ (if Ordering.le Ordering.acqrel ord then TView.cur 𝓥' else TView.acq 𝓥')⌝ ∗
          @{TView.cur 𝓥'} loc sn⊒{γ} ζ'' ∗
          @{Vb} AtomicPtsToX loc γ t ζ mode ∗
          tview_sys tid 𝓥')))%I.

  Definition read_spec : fspec := app_fspec [read_spec_0; read_spec_1].

  (* non-atomic write *)
  Definition write_spec_0 : fspec :=
    fspec_simple (X:=Ident.t * Loc.t * Val.t * Ordering.t * TView.t)
      (λ '(tid, loc, val, ord, 𝓥),
        ((λ varg, ⌜varg = (loc, val, ord)↑⌝ ∗
          @{TView.cur 𝓥} loc ↦ ? ∗ tview_sys tid 𝓥),
        (λ vret, ∃ 𝓥', ⌜vret = Val.zero↑ ∧ TView.le 𝓥 𝓥'⌝ ∗
          @{TView.cur 𝓥'} loc ↦ val ∗ tview_sys tid 𝓥')))%I.

  #[local] Definition own_writer γ (m : AtomicMode) (q : frac) ζ tx : iProp Σ :=
    match m with
    | SingleWriter => at_writer γ ζ ∗ at_exclusive_write γ tx 1%Qp
    | CASOnly => at_exclusive_write γ tx q
    | ConcurrentWriter => True
    end.

  (* atomic write *)
  Definition write_spec_1 : fspec :=
    fspec_simple
      (X:=Ident.t * Loc.t * Val.t * Ordering.t * TView.t * gname * Cell.t * View.t * Time.t * Cell.t * AtomicMode * Qp * Time.t)
      (λ '(tid, loc, val, ord, 𝓥, γ, ζ', Vb, tx, ζ, mode, q, tx'),
        ((λ varg,
          ⌜varg = (loc, val, ord)↑ ∧ Ordering.le Ordering.relaxed ord⌝ ∗
          @{TView.cur 𝓥} loc sn⊒{γ} ζ' ∗
          @{Vb} AtomicPtsToX loc γ tx ζ mode ∗
          tview_sys tid 𝓥 ∗
          own_writer γ mode q ζ' tx'),
        (λ vret, ∃ f t (LT : Time.lt f t) V' ζ'' ζn,
          let 𝓥' := TView.write_tview 𝓥 loc t ord in
          ⌜vret = Val.zero↑
          ∧ Time.lt (Cell.max_ts ζ') t
          ∧ if Ordering.le Ordering.acqrel ord
            then V' = TView.cur 𝓥'
            else (TView.rel 𝓥 loc) ⊑ V' ∧ V' ⊑ TView.cur 𝓥'
          ∧ Cell.add ζ' f t (Message.message val V' false) ζ''
          ∧ Cell.add ζ f t (Message.message val V' false) ζn⌝ ∗
          @{TView.cur 𝓥'} loc sn⊒{γ} ζ'' ∗
          own_writer γ mode q ζ'' (if mode is SingleWriter then t else tx') ∗
          @{TView.cur 𝓥'} loc sy⊒{γ} Cell.singleton (Message.message val V' false) LT ∗
          @{Vb ⊔ TView.cur 𝓥'} AtomicPtsToX loc γ (if mode is SingleWriter then t else tx') ζn mode ∗
          tview_sys tid 𝓥')))%I.

  Definition write_spec : fspec := app_fspec [write_spec_0; write_spec_1].

  Definition sp (E : coPset) : spl_type :=
    Seal.sealing CRIS
      [(Some SystemHdr._spawn,  Some _spawn_spec);
       (Some SystemHdr.spawn,   Some (spawn_spec E));
       (Some SystemHdr.yield,   Some (yield_spec E));
       (Some SystemHdr.get_tid, Some get_tid_spec);
       (Some SystemHdr.alloc,   Some alloc_spec);
       (Some SystemHdr.write,   Some write_spec);
       (Some SystemHdr.read,    Some read_spec)].

  (* Module definitions *)
  Definition scopes := ["System"].
  Definition v_internal := "System" ↯ "internal".

  (* Parameterized functions *)
  Definition check_internal : itree crisE unit :=
    _internal <- cgetU v_internal;;
    assume (_internal = true);;;
    cput v_internal false.

  Definition trigger_Yield (nxt_tid : Ident.t) : itree crisE unit :=
    cput v_internal true;;;
    SystemI.trigger_Yield nxt_tid;;;
    check_internal.

  Definition new_tid (tids : tidmap) (tid : Ident.t) : itree crisE Ident.t :=
    '(exist _ tid_new _) : _ <- trigger (Choose ({tid_new : Ident.t | tids !! tid_new = None}));;
    Ret tid_new.

  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some SystemHdr._spawn,  (true, wmask_all, scopes, (Some _spawn_spec,    (cfunN (SystemI._spawn check_internal)))));
     (Some SystemHdr.spawn,   (true, wmask_all, scopes, (Some (spawn_spec ⊤), (cfunN (SystemI.spawn new_tid)))));
     (Some SystemHdr.yield,   (true, wmask_all, scopes, (Some (yield_spec ⊤), (cfunN (SystemI.yield trigger_Yield)))));
     (Some SystemHdr.get_tid, (true, wmask_all, scopes, (Some get_tid_spec,   (cfunN SystemI.get_tid))));
     (Some SystemHdr.alloc,   (true, wmask_all, scopes, (Some alloc_spec,     fbody_trivial)));
     (Some SystemHdr.write,   (true, wmask_all, scopes, (Some write_spec,     fbody_trivial)));
     (Some SystemHdr.read,    (true, wmask_all, scopes, (Some read_spec,      fbody_trivial)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := (v_internal, false↑) :: SystemI.Mod.(SMod.initial_st);
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond size : iProp Σ :=
    tview_sys_auth {[1%positive := TView.init size]}.

  Definition t sp : Mod.t := Seal.sealing CRIS (SMod.to_mod sp Mod).
End SystemA. End SystemA.