Require Import CRIS.
Require Import PFMemHeader HistoryRA AtomicRA.
Require Import Time Cell View TView base.

(* Specification of promise-free memory module *)
Module PFMemA. Section PFMemA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !histG, !atomicG}.
  Definition scopes := ["PFMem"].

  Definition alloc_spec : fspec :=
    fspec_simple (X:=Ident.t * nat * TView.t)
      (λ '(tid, n, 𝓥),
        ((λ varg, ⌜varg = (tid, Z.of_nat n)↑⌝
          ∗ tview tid 𝓥),
        (λ vret, ∃ loc 𝓥', ⌜vret = (Val.Vptr loc)↑ ∧ TView.le 𝓥 𝓥'⌝
          ∗ tview tid 𝓥'
          ∗ †loc…n
          ∗ @{TView.cur 𝓥'} loc ↦∗ repeat Val.Vundef n)))%I.

  Definition free_spec : fspec :=
    fspec_simple (X:=Ident.t * Loc.t * nat * TView.t)
      (λ '(tid, loc, n, 𝓥),
        ((λ varg, ⌜varg = (tid, loc)↑⌝
          ∗ tview tid 𝓥
          ∗ own_loc_vec loc 1 n (TView.cur 𝓥)
          ∗ †loc…n),
        (λ vret, ⌜vret = (Val.zero)↑⌝)))%I.

  (* non-atomic read *)
  Definition read_spec_0 : fspec :=
    fspec_simple (X:=Ident.t * Loc.t * Ordering.t * Val.t * Qp * TView.t)
      (λ '(tid, loc, ord, v, q, 𝓥),
        ((λ varg, ⌜varg = (tid, loc, ord)↑⌝
          ∗ @{TView.cur 𝓥} loc ↦{q} v ∗ tview tid 𝓥),
        (λ vret, ∃ v' 𝓥', ⌜vret = v'↑ ∧ Val.le v' v⌝
          ∗ @{TView.cur 𝓥'} loc ↦{q} v ∗ tview tid 𝓥')))%I.

  (* atomic read *)
  (* TODO : give variants of this specification (SW, SYNC, CAS, ...) *)
  Definition read_spec_1 : fspec :=
    fspec_simple
      (X:=Ident.t * Loc.t * Ordering.t * Cell.t * Cell.t * Time.t * positive * Qp * AtomicMode * TView.t * View.t)
      (λ '(tid, loc, ord, ζ, ζ', t, γ, q, mode, 𝓥, Vb),
        ((λ varg,
          ⌜varg = (tid, loc, ord)↑ ∧ Ordering.le Ordering.relaxed ord⌝
          ∗ @{TView.cur 𝓥} loc sn⊒{γ} ζ' (* ζ' abstract history seen by current thread *)
          ∗ @{Vb} AtomicPtsToX loc γ t ζ mode (* ζ global abstract history *)
          ∗ tview tid 𝓥), (* 𝓥 current thread view *)
        (λ vret, ∃ ζ'' f' na v' v'' V' 𝓥',
          ⌜vret = v'↑
          ∧ Val.le v' v''
          ∧ Cell.le ζ' ζ'' ∧ Cell.le ζ'' ζ
          ∧ Cell.get (Cell.max_ts ζ'') ζ'' = Some (f', Message.message v'' V' na)
          (* ∧ TView.readable (TView.cur 𝓥) loc (Cell.max_ts ζ'') ord *)
          ∧ (TView.cur 𝓥) ⊑ (TView.cur 𝓥')
          ∧ V' ⊑ (if Ordering.le Ordering.acqrel ord then TView.cur 𝓥' else TView.acq 𝓥')⌝
          ∗ @{TView.cur 𝓥'} loc sn⊒{γ} ζ''
          ∗ @{Vb} AtomicPtsToX loc γ t ζ mode
          ∗ tview tid 𝓥')))%I.

  Definition read_spec : fspec := app_fspec [read_spec_0; read_spec_1].

  (* non-atomic write *)
  Definition write_spec_0 : fspec :=
    fspec_simple (X:=Ident.t * Loc.t * Val.t * Ordering.t * TView.t)
      (λ '(tid, loc, val, ord, 𝓥),
        ((λ varg, ⌜varg = (tid, loc, val, ord)↑⌝
          ∗ @{TView.cur 𝓥} loc ↦ ? ∗ tview tid 𝓥),
        (λ vret, ∃ 𝓥',
          ⌜vret = Val.zero↑ ∧ TView.le 𝓥 𝓥'⌝ ∗
          @{TView.cur 𝓥'} loc ↦ val ∗ tview tid 𝓥')))%I.

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
          ⌜varg = (tid, loc, val, ord)↑ ∧ Ordering.le Ordering.relaxed ord⌝
          ∗ @{TView.cur 𝓥} loc sn⊒{γ} ζ' (* ζ' abstract history seen by current thread *)
          ∗ @{Vb} AtomicPtsToX loc γ tx ζ mode (* ζ global abstract history *)
          ∗ tview tid 𝓥 (* 𝓥 current thread view *)
          ∗ own_writer γ mode q ζ' tx'),
        (λ vret, ∃ f t (LT : Time.lt f t) V' ζ'' ζn,
          let 𝓥' := TView.write_tview 𝓥 loc t ord in
          ⌜vret = Val.zero↑
          ∧ Time.lt (Cell.max_ts ζ') t
          ∧ if Ordering.le Ordering.acqrel ord (* TODO : maybe this can be just V' = TView.write_released *)
            then V' = TView.cur 𝓥'
            else (TView.rel 𝓥 loc) ⊑ V' ∧ V' ⊑ TView.cur 𝓥'
          ∧ Cell.add ζ' f t (Message.message val V' false) ζ''
          ∧ Cell.add ζ f t (Message.message val V' false) ζn⌝
          ∗ @{TView.cur 𝓥'} loc sn⊒{γ} ζ''
          ∗ own_writer γ mode q ζ'' (if mode is SingleWriter then t else tx')
          ∗ @{TView.cur 𝓥'} loc sy⊒{γ} Cell.singleton (Message.message val V' false) LT
          (* ∗ @{V'} loc sn⊒{γ} Cell.singleton (Message.message val V' false) LT *)
          (* TODO : the condition above is improvable since release view may not have observed
            allocation
          *)
          ∗ @{Vb ⊔ TView.cur 𝓥'} AtomicPtsToX loc γ (if mode is SingleWriter then t else tx') ζn mode
          ∗ tview tid 𝓥')))%I.

  Definition write_spec : fspec := app_fspec [write_spec_0; write_spec_1].

  (* TODO : Move to appropriate space *)
  Definition comparable (v1 v2 : Val.t) : Prop :=
    match v1, v2 with
    | Val.Vnum _, Val.Vnum _
    | Val.Vptr _, Val.Vptr _ => True
    | _, _ => False
    end.

  Definition cas_spec : fspec :=
    fspec_simple
      (X:=Ident.t * Loc.t * Val.t * Val.t * Ordering.t * Ordering.t * TView.t * gname * Cell.t * View.t * Time.t * Cell.t * AtomicMode * iProp Σ)
      (λ '(tid, loc, old, new, ordr, ordw, 𝓥, γ, ζ', Vb, tx, ζ, mode, Pr),
        let Wv ζ : iProp Σ := (if mode is SingleWriter then at_writer γ ζ else True)%I in
        ((λ varg,
          ⌜ varg = (tid, loc, old, new, ordr, ordw)↑
            ∧ Ordering.le Ordering.relaxed ordr
            ∧ Ordering.le Ordering.relaxed ordw
            ∧ (∀ t f v V b,
              Time.le (Cell.max_ts ζ') t
              → Cell.get t ζ = Some (f, Message.message v V b)
              → comparable old v
                ∧ if v is Val.Vptr loc
                  then
                    if Ordering.le Ordering.acqrel ordr
                    then (View.alloc_view V) (Loc.get_tbid loc)
                    else (View.alloc_view (TView.cur 𝓥)) (Loc.get_tbid loc)
                  else True) ⌝
          ∗ tview tid 𝓥
          ∗ @{TView.cur 𝓥} loc sn⊒{γ} ζ'
          ∗ @{Vb} AtomicPtsToX loc γ tx ζ mode
          ∗ Wv ζ
          ∗ Pr
          ∗ □ if old is (Val.Vptr lr) then
                (Pr ==∗ ((∃ qr Cr Vr γ Cr', @{Vr} lr p↦{qr} Cr ∗ @{TView.cur 𝓥} lr sn⊒{γ} Cr') ∧
                  (∀ t f (l' : Loc.t) V' b,
                    ⌜Time.le (Cell.max_ts ζ') t
                      ∧ Cell.get t ζ = Some (f, Message.message (Val.Vptr l') V' b)
                      ∧ l' <> lr⌝
                    -∗ ∃ q' C' V'', @{V''} l' p↦{q'} C')))
              else emp
          ),
        (λ vret, ∃ ret ζ'' ζn t' f' (LT : Time.lt f' t') v' Vr b 𝓥',
          ⌜vret = ret↑
            ∧ Cell.le ζ' ζ'' ∧ Cell.le ζ'' ζn
            ∧ Cell.get t' ζ'' = Some (f', Message.message v' Vr b)
            ∧ Time.le (Cell.max_ts ζ') t'
            ∧ TView.le 𝓥 𝓥'⌝
          ∗ tview tid 𝓥'
          (* ∗ @{TView.cur 𝓥'} loc sn⊒{γ} (Cell.singleton (Message.message v' Vr b) LT) *)
          ∗ @{TView.cur 𝓥'} loc sn⊒{γ} ζ''
          ∗ Pr
          ∗ ((⌜ret = Val.zero ∧ old <> v'
              ∧ (Vr ⊑ if Ordering.le Ordering.acqrel ordr then TView.cur 𝓥' else TView.acq 𝓥')
              ∧ ζ = ζn⌝
              ∗ @{Vb} AtomicPtsToX loc γ tx ζ mode)
            ∨ (∃ Vw,
                ⌜ret = Val.one ∧ old = v'
                ∧ ∃ t'', Cell.add ζ t' t'' (Message.message new Vw false) ζn
                ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
                ∧ ¬ (TView.cur 𝓥') ⊑ Vr
                ∧ 𝓥' ≠ 𝓥
                ∧ if Ordering.le Ordering.acqrel ordw
                  then if Ordering.le Ordering.acqrel ordr
                      then Vw = TView.cur 𝓥'
                      else TView.cur 𝓥' ⊑ Vw (* This seems to be because of liftings in gpfsl *)
                  else (TView.rel 𝓥' loc) ⊑ Vw
                ∧ Vw ⊑ if Ordering.le Ordering.acqrel ordr then TView.cur 𝓥' else TView.acq 𝓥'⌝
                ∗ Wv ζn
                ∗ @{Vb ⊔ TView.cur 𝓥'} AtomicPtsToX loc γ tx ζn mode))
          )))%I.

  Definition spawn_spec : fspec :=
    fspec_simple
      (λ '(tid, 𝓥),
        ((λ varg, ⌜varg = tid↑⌝ ∗ tview tid 𝓥),
         (λ vret, ∃ tid_new, ⌜vret = tid_new↑⌝ ∗ tview tid 𝓥 ∗ tview tid_new 𝓥)))%I.
  (* TODO : cmp, faa, fence *)

  (* For now, we don't consider the case where "ordw = seqcst" *)
  Definition fence_spec : fspec :=
    fspec_simple
      (λ '(tid, ordr, ordw, 𝓥),
        ((λ varg, 
          ⌜varg = (tid, ordr, ordw)↑  ∧ Ordering.le ordw Ordering.acqrel⌝ ∗
          tview tid 𝓥),
         (λ vret, ∃ 𝓥',
          ⌜vret = Val.zero↑ ∧
           (TView.cur 𝓥' = if Ordering.le Ordering.acqrel ordr then TView.acq 𝓥 else TView.cur 𝓥) ∧
           (TView.rel 𝓥' = λ loc, if Ordering.le Ordering.acqrel ordw then TView.cur 𝓥' else TView.rel 𝓥 loc) ∧
           (TView.acq 𝓥' = TView.acq 𝓥)⌝ ∗
          tview tid 𝓥')))%I.

  Definition sp : spl_type :=  
    Seal.sealing CRIS
      [(Some PFMemHdr.alloc, Some alloc_spec);
       (Some PFMemHdr.free,  Some free_spec);
       (Some PFMemHdr.read,  Some read_spec);
       (Some PFMemHdr.write, Some write_spec);
       (Some PFMemHdr.cas,   Some cas_spec);
       (Some PFMemHdr.fence, Some fence_spec);
       (Some PFMemHdr.spawn, Some spawn_spec)].

  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some PFMemHdr.alloc, (true, wmask_all, scopes, (Some alloc_spec, fbody_trivial)));
     (Some PFMemHdr.free,  (true, wmask_all, scopes, (Some free_spec,  fbody_trivial)));
     (Some PFMemHdr.read,  (true, wmask_all, scopes, (Some read_spec,  fbody_trivial)));
     (Some PFMemHdr.write, (true, wmask_all, scopes, (Some write_spec, fbody_trivial)));
     (Some PFMemHdr.cas,   (true, wmask_all, scopes, (Some cas_spec,   fbody_trivial)));
     (Some PFMemHdr.fence, (true, wmask_all, scopes, (Some fence_spec, fbody_trivial)));
     (Some PFMemHdr.spawn, (true, wmask_all, scopes, (Some spawn_spec, fbody_trivial)))].

  (* Module definition *)
  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t sp : Mod.t := Seal.sealing CRIS (SMod.to_mod sp smod).
End PFMemA. End PFMemA.