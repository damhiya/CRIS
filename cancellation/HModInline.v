Require Import Coqlib.
Require Import sflib.
Require Import ITreelib.
Require Import AList.
Require Import Behavior.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Export STB.
Require Import Events HMod.

Set Implicit Arguments.



(* Inlining every function call in HMod. *)
Section INTERP.
  Context `{Σ: GRA.t}.

  Definition handle_callE (prog: callE ~> itree hmodE): itree hmodE Any.t -> itree hmodE (_ + Any.t)
  :=
    fun itr =>
      match observe (itr: itree hmodE Any.t) with
      | RetF rv => Ret (inr rv)
      | TauF itr' => tau;; Ret (inl itr')
      | VisF (inr1 (inr1 (inr1 (inr1 e)))) k =>
          v <- trigger e;; Ret (inl (k v))
      | VisF (inr1 (inr1 (inr1 (inl1 e)))) k => 
          v <- trigger e;; Ret (inl (k v))
      | VisF (inr1 (inr1 (inl1 c))) k =>
          Ret (inl (x <- prog _ c;; tau;; (k x)))
      | VisF (inr1 (inl1 e)) k =>
          v <- trigger e;; Ret (inl (k v))
      | VisF (inl1 e) k =>
          v <- trigger e;; Ret (inl (k v))
      end.

  Definition inline_hp (prog: callE ~> itree hmodE) (itr: itree hmodE Any.t)
    : itree hmodE Any.t
    :=
    ITree.iter (handle_callE prog) itr.

  Definition inline_hp_fun (prog: callE ~> itree hmodE) (body: Any.t -> itree hmodE Any.t)
    : Any.t -> itree hmodE Any.t
    :=
    fun args =>
      inline_hp prog (body args).

  Definition prog (ms: HModSem.t) : callE ~> itree hmodE :=
    fun _ '(Call fn args) =>
      lbody <- (alist_find fn ms.(HModSem.fnsems))!;;
      HModSem.sandbox_body lbody args.
      
  Definition inline_hp_fbody (ms: HModSem.t)
    : (list string * (Any.t -> itree hmodE Any.t)) -> (list string * (Any.t -> itree hmodE Any.t))
    :=
    fun '(k, b) => (k, inline_hp_fun (prog ms) b).

  Definition wrap_sandbox scopeS: list string * (Any.t -> itree hmodE Any.t) -> list string * (Any.t -> itree hmodE Any.t)
    := 
    fun kb => (scopeS, HModSem.sandbox_body kb).

  Definition wrap_elimI ms: list string * (Any.t -> itree hmodE Any.t) -> list string * (Any.t -> itree hmodE Any.t)
    :=
    fun kb => inline_hp_fbody ms (wrap_sandbox ms.(HModSem.scopes) kb). 

End INTERP.

Module HModSemAux.
  Section AUX.
    Context `{Σ: GRA.t}.
    Import HModSem.

    Program Definition inline (ms: HModSem.t): HModSem.t := {|
      HModSem.scopes := ms.(scopes);
      HModSem.fnsems := List.map (map_snd (wrap_elimI ms)) (ms.(fnsems));
      (* HModSem.fnsems := List.map (map_snd (λ ksb, (ksb.1, inline_hp_fun (prog ms) ksb.2))) (ms.(fnsems)); *)
      HModSem.initial_st := ms.(initial_st);
    |}.
    Next Obligation.
      i. depdes ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in*.
      rewrite! alist_find_map in H. unfold o_map in H.
      des_ifs; ss. 
      (* inv Heq0.
      specialize (well_scoped_fns0 fn a).
      des_ifs; ss. inv Heq. eauto. *)
    Qed.
    Next Obligation. ii. destruct ms. ss. eauto. Qed.
    Next Obligation. ii. destruct ms. ss. eauto. Qed.

    (* Definition to_elim ms := to_hmod ((interp_sb_hp_elim) ∘ fsb_body) ms. *)

  End AUX.
End HModSemAux.

Module HModAux.
  Section AUX.
    Context `{Σ: GRA.t}.
    Import HMod.

    Definition inline (md: t) := {|
      HMod.modsem := fun sk => HModSemAux.inline (md.(modsem) sk);
      HMod.sk := md.(sk);
    |}.

  End AUX.
End HModAux.

Module HIRed.
  Section RED.
    Context `{Σ: GRA.t}.

    Variable ms: HModSem.t.

    Lemma iter_handle_bind i k:
      ITree.iter (handle_callE (prog ms)) (i >>= k)
      =
      x <- (ITree.iter (handle_callE (prog ms)) i);; ITree.iter (handle_callE (prog ms)) (k x).
    Proof. 
      eapply bisim_is_eq.
      eapply (@gpaco2_init _ _ _ _ (eqitC eq false false)); eauto with paco.
      revert i k. gcofix CIH. i.
      ides i.
      - grind. rewrite/__ [_ _ (Ret _)]unfold_iter_eq. grind.
        gfinal. right. eapply paco2_mon_bot; eauto.
        apply Reflexive_eqit. auto.
      - grind. rewrite! unfold_iter_eq. grind.
        gstep. econs. gstep. econs. gbase. eapply CIH.
      - rewrite! unfold_iter_eq.
        destruct e.
        {
          grind. rewrite! bind_trigger. gstep. econs. i.
          r. grind. gstep. econs. gbase. eauto.
        }
        destruct p.
        {
          grind. rewrite! bind_trigger. gstep. econs. i.
          r. grind. gstep. econs. gbase. eauto.  
        }
        destruct s.
        {
          grind. gstep. econs. 
          guclo eqit_clo_trans; eauto.
          econs; cycle 1.
          { refl. }
          { gbase. eapply CIH. }
          { instantiate (1:= eq). i. subst. refl. }
          { i. subst. refl. }
          grind. 
          replace (` x : X <- prog ms c;; (tau;; ITree.subst k (k0 x)))
          with (` r0 : X <- prog ms c;; ` x : Any.t <- (tau;; k0 r0);; k x) by grind.
          refl.
        } 
        destruct s.
        {
          grind. rewrite! bind_trigger. gstep. econs. i.
          r. grind. gstep. econs. gbase. eauto.
        }
        grind. rewrite! bind_trigger. gstep. econs. i.
        r. grind. gstep. econs. gbase. eauto.
      Unshelve. eauto with paco.
    Qed.
        
    Lemma ret 
      prog (x: Any.t)
    :
      inline_hp prog (Ret x) = Ret x.
    Proof.
      rewrite/inline_hp unfold_iter_eq. grind.
    Qed.

    Lemma tau
      prog t
    :
      inline_hp prog (tau;; t) = tau;; tau;; inline_hp prog t.
    Proof.
      rewrite/inline_hp unfold_iter_eq. grind.
    Qed.

    Lemma bind
      itr ktr
    :
      inline_hp (prog ms) (itr >>= ktr)
      =
      x <- inline_hp (prog ms) itr;; inline_hp (prog ms) (ktr x).
    Proof.
      rewrite/inline_hp iter_handle_bind. refl.
    Qed.

    Lemma bind_sch
      X prog (e: schE X) ktr
    :
      inline_hp prog (x <- trigger e;; ktr x) 
      =
      x <- trigger e;; tau;; inline_hp prog (ktr x).
    Proof.
      rewrite/inline_hp unfold_iter_eq. grind.
    Qed.

    Lemma bind_core
      X prog (e: coreE X) ktr
    :
      inline_hp prog (x <- trigger e;; ktr x) 
      =
      x <- trigger e;; tau;; inline_hp prog (ktr x).
    Proof.
      rewrite/inline_hp unfold_iter_eq. grind.
    Qed.

    Lemma bind_pg
      X prog (e: pgE X) ktr
    :
      inline_hp prog (x <- trigger e;; ktr x) 
      =
      x <- trigger e;; tau;; inline_hp prog (ktr x).
    Proof.
      rewrite/inline_hp unfold_iter_eq. grind.
    Qed.

    Lemma bind_ag
      X prog (e: agE X) ktr
    :
      inline_hp prog (x <- trigger e;; ktr x) 
      =
      x <- trigger e;; tau;; inline_hp prog (ktr x).
    Proof.
      rewrite/inline_hp unfold_iter_eq. grind.
    Qed.

    Lemma call
      prog ktr (fn: string) arg 
    :
      inline_hp prog (trigger (Call fn arg) >>= ktr)
      =
      tau;; inline_hp prog (x <- prog Any.t (resum IFun Any.t (Call fn arg));; tau;; ITree.subst ktr (Ret x)).
    Proof.
      rewrite/inline_hp unfold_iter_eq. ired. refl.
    Qed.

  End RED.
End HIRed.