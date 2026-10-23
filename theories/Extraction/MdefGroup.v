(** * Deciding a Mutual Definition's Group

    The group of a mutual definition, its uniform parameters and each
    function's member ([mdef_group]), computed ([mdef_group_dec]): the run
    of a mutual definition reads them, and so does the access fill of its
    functions' results and clauses, which are filled in the eliminator's
    contexts at the group.  The computed group is the relation's
    ([mdef_group_dec_complete]). *)

From Stdlib Require Import List String PeanoNat Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Core.Semantic Require Import NbE.
From Mctt.Extraction Require Import Lookup NbE TypeCheckBase TypeCheck GlobalCheck IndDecl.
Import Syntax_Notations.

Local Open Scope string_scope.

(** An option, with its value or its absence. *)
Definition opt_case {A} (o : option A) : {a | o = Some a} + {o = None} :=
  match o as o0 return {a | o0 = Some a} + {o0 = None} with
  | Some a => inleft (exist _ a eq_refl)
  | None => inright eq_refl
  end.

(** Why a function of a mutual definition is rejected, for the checker's
    message. *)
Inductive mdef_why : Set :=
(** The type of the scrutinee is not a type *)
| mw_scrut_untyped : mdef_why
(** The type of a member at the uniform parameters is not a type *)
| mw_member_untyped : nat -> mdef_why
(** The scrutinee's type is that of no member of the group: its normal
    form *)
| mw_no_member : nf -> mdef_why
(** The member has another number of non-uniform parameters: theirs, then
    the function's *)
| mw_nparams : nat -> nat -> mdef_why.

Section MdefDecide.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.

  (** Types, each a type and then normalized, pointwise. *)
  Fixpoint tys_nbe_dec {X : Type} (T : X -> exp) (Γ : ctx) (xs : list X) {struct xs} :
      ({Ws | Forall2 (fun x W => (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ T x : Typeω@i) /\ nbe_ty Θ Ξ Γ (T x) W) xs Ws}
       + {j : nat | forall Ws, ~ Forall2 (fun x W => (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ T x : Typeω@i) /\ nbe_ty Θ Ξ Γ (T x) W) xs Ws})%type.
  Proof.
    destruct xs as [| x xs'].
    - left; exists nil; constructor.
    - destruct (typ_least_dec Θ Ξ HΞ Γ (T x)) as [[i [HT _]] | HnT];
        [| right; exists 0; intros Ws H; inversion H as [| ? ? ? ? [[i HT] _] _]; exact (HnT _ HT) ].
      destruct (@nbe_ty_impl Θ Ξ (fctx_none Θ Ξ) Γ (T x) (typ_nbe_ty_order Θ Ξ _ _ _ HT)) as [W HW].
      destruct (tys_nbe_dec X T Γ xs') as [[Ws HWs] | [j Hn]].
      + left; exists (W :: Ws); constructor; [ split; [ exists i; exact HT | exact HW ] | exact HWs ].
      + right; exists (S j); intros Ws H; inversion H; subst; eapply Hn; eassumption.
  Defined.

  (** The member of a function, or why it has none. *)
  Definition mdef_member_dec (pq : qname) (D : ind_decl) (Us : list exp) (Δ : ctx) (f : raw_fun) :
      ({m | mdef_member Θ Ξ pq D Us Δ f m} + {e : mdef_why | forall m, ~ mdef_member Θ Ξ pq D Us Δ f m})%type.
  Proof.
    set (Γ := (rf_nparams f ++ Δ ++ gs_tele Ξ)%list).
    set (n := List.length (rf_nparams f)).
    set (T := fun jM : (nat * imember)%type =>
                im_ty_at pq (fst jM) (snd jM) (List.map (fun U => U[wk_shiftn n]ʷ) Us) (vars_from 0 n)).
    destruct (typ_least_dec Θ Ξ HΞ Γ (rf_scrut f)) as [[i [HZ _]] | HnZ];
      [| right; exists mw_scrut_untyped; intros m H; inversion H as [? ? ? ? ? [i' HZ'] _ _ _ _ _]; exact (HnZ _ HZ') ].
    destruct (@nbe_ty_impl Θ Ξ (fctx_none Θ Ξ) Γ (rf_scrut f) (typ_nbe_ty_order Θ Ξ _ _ _ HZ)) as [W HW].
    destruct (tys_nbe_dec T Γ (List.combine (List.seq 0 (List.length (ind_members D))) (ind_members D))) as [[Ws HWs] | [j Hn]];
      [| right; exists (mw_member_untyped j); intros m H; inversion H; subst; eapply Hn; eassumption ].
    destruct (nf_index W Ws) as [m |] eqn:Hm.
    2:{ right; exists (mw_no_member W); intros m H; inversion H as [? W' Ws' ? Mm _ HW' HWs' Hm' _ _]; subst.
        pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-.
        assert (Ws' = Ws) as ->.
        { eapply Forall2_functional; [| exact HWs' | exact HWs ].
          intros x W1 W2 [_ H1] [_ H2]; exact (functional_nbe_ty _ _ _ _ H1 H2). }
        congruence. }
    destruct (ind_member D m) as [Mm |] eqn:HMm.
    2:{ right; exists (mw_no_member W); intros m' H; inversion H as [? W' Ws' ? Mm _ HW' HWs' Hm' HMm' _]; subst.
        pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-.
        assert (Ws' = Ws) as ->.
        { eapply Forall2_functional; [| exact HWs' | exact HWs ].
          intros x W1 W2 [_ H1] [_ H2]; exact (functional_nbe_ty _ _ _ _ H1 H2). }
        congruence. }
    destruct (PeanoNat.Nat.eq_dec (im_nn Mm) n) as [Hnn | Hnn].
    - left; exists m; econstructor; [ exists i; exact HZ | exact HW | exact HWs | exact Hm | exact HMm | exact Hnn ].
    - right; exists (mw_nparams (im_nn Mm) n); intros m' H; inversion H as [? W' Ws' ? Mm' _ HW' HWs' Hm' HMm' Hnn']; subst.
      pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-.
      assert (Ws' = Ws) as ->.
      { eapply Forall2_functional; [| exact HWs' | exact HWs ].
        intros x W1 W2 [_ H1] [_ H2]; exact (functional_nbe_ty _ _ _ _ H1 H2). }
      assert (m' = m) as -> by congruence; assert (Mm' = Mm) as -> by congruence; contradiction.
  Defined.

  (** The members of the functions, function by function; a rejection
      names the function. *)
  Fixpoint mdef_members_dec (pq : qname) (D : ind_decl) (Us : list exp) (Δ : ctx) (fs : list raw_fun) {struct fs} :
      ({ms | Forall2 (mdef_member Θ Ξ pq D Us Δ) fs ms}
       + {e : (string * mdef_why) | forall ms, ~ Forall2 (mdef_member Θ Ξ pq D Us Δ) fs ms})%type.
  Proof.
    destruct fs as [| f fs'].
    - left; exists nil; constructor.
    - destruct (mdef_member_dec pq D Us Δ f) as [[m Hm] | [e He]];
        [| right; exists (rf_name f, e); intros ms H; inversion H; subst; eapply He; eassumption ].
      destruct (mdef_members_dec pq D Us Δ fs') as [[ms Hms] | [e He]].
      + left; exists (m :: ms); constructor; assumption.
      + right; exists e; intros ms' H; inversion H; subst; eapply He; eassumption.
  Defined.
End MdefDecide.

(** Distinct members, decided by a computation: [ListDec.NoDup_dec] is
    opaque, so extraction would bypass it. *)
Definition members_distinct_dec : forall l : list nat, { NoDup l } + { ~ NoDup l }.
Proof.
  induction l as [| x l IH].
  - left; constructor.
  - destruct (in_dec PeanoNat.Nat.eq_dec x l) as [Hin | Hn].
    + right; intros Hnd; inversion Hnd; contradiction.
    + destruct IH as [H | H]; [ left; constructor; assumption | right; intros Hnd; inversion Hnd; contradiction ].
Defined.

(** The members of the functions alike along an equivalence. *)
Lemma equiv_mdef_member : forall Θ Θ' Ξ pq D Us Δ f m, gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ ->
    mdef_member Θ Ξ pq D Us Δ f m -> mdef_member Θ' Ξ pq D Us Δ f m.
Proof.
  intros * He HΞ [f0 W Ws m0 Mm [i HZ] HW HWs Hm HMm Hnn].
  econstructor; [ exists i; exact (equiv_exp _ _ _ _ _ _ He HΞ HZ) | exact (equiv_nbe_ty _ _ _ He _ _ _ HW)
                | | exact Hm | exact HMm | exact Hnn ].
  eapply Forall2_impl; [| exact HWs ]; intros jM Wj [[j HT] HWj].
  split; [ exists j; exact (equiv_exp _ _ _ _ _ _ He HΞ HT) | exact (equiv_nbe_ty _ _ _ He _ _ _ HWj) ].
Qed.

(** The group alike along an equivalence. *)
Lemma equiv_mdef_group : forall Θ Θ' Ξ Δ f0 fs pq m0 Ps D Us ms, gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ ->
    mdef_group Θ Ξ Δ f0 fs pq m0 Ps D Us ms -> mdef_group Θ' Ξ Δ f0 fs pq m0 Ps D Us ms.
Proof.
  intros * He HΞ [[i HZ] HW Hl Hm0 HUs Hms Hlen Hnd].
  constructor; [ exists i; exact (equiv_exp _ _ _ _ _ _ He HΞ HZ) | exact (equiv_nbe_ty _ _ _ He _ _ _ HW)
               | rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); exact Hl | exact Hm0 | exact HUs
               | | exact Hlen | exact Hnd ].
  eapply Forall2_impl; [ intros f m; apply (equiv_mdef_member _ _ _ _ _ _ _ _ _ He HΞ) | exact Hms ].
Qed.

(** Why a mutual definition's functions have no group, for the checker's
    message. *)
Inductive mdef_group_why : Set :=
(** A function, named, has no member: why *)
| mgw_function : string -> mdef_why -> mdef_group_why
(** The first function's scrutinee's type, named by the function, is no
    inductive type *)
| mgw_not_inductive : string -> mdef_group_why
(** The group its scrutinee's type names is not filed *)
| mgw_no_group : qname -> mdef_group_why
(** The first function's scrutinee's type is a view, not a declared type *)
| mgw_view : string -> mdef_group_why
(** The uniform parameters of the first function's scrutinee's type
    depend on its non-uniform parameters *)
| mgw_uparams : string -> mdef_group_why
(** Not one function per member: the members, then the functions *)
| mgw_count : nat -> nat -> mdef_group_why
(** Two functions are for the same member *)
| mgw_shared : mdef_group_why.

(** The group of a mutual definition's functions [f0 :: fs] over [Δ],
    checked premise by premise as [mdef_group] reads it. *)
Definition mdef_group_dec (Θ : gdeps) (Ξ : gstack) (HΞ : ⊢ᵍ Θ ⍮ Ξ) (Δ : ctx) (f0 : raw_fun) (fs : list raw_fun) :
    ({r : qname * nat * nfs * ind_decl * list exp * list nat |
       let '(pq, m0, Ps, D, Us, ms) := r in mdef_group Θ Ξ Δ f0 fs pq m0 Ps D Us ms} + mdef_group_why)%type :=
  match typ_least_dec Θ Ξ HΞ (rf_nparams f0 ++ Δ ++ gs_tele Ξ) (rf_scrut f0) with
  | inright _ => inr (mgw_function (rf_name f0) mw_scrut_untyped)
  | inleft (exist _ i (conj HZ _)) =>
      match @nbe_ty_impl Θ Ξ (fctx_none _ _) (rf_nparams f0 ++ Δ ++ gs_tele Ξ) (rf_scrut f0) (typ_nbe_ty_order _ _ _ _ _ HZ) with
      | exist _ (nf_indty pq m0 Ps) HW =>
          match opt_case (ind_lookup Θ Ξ pq) with
          | inright _ => inr (mgw_no_group pq)
          | inleft (exist _ D Hl) =>
              match Compare_dec.lt_dec m0 (ind_ndecl D) with
              | right _ => inr (mgw_view (rf_name f0))
              | left Hm0 =>
                  match inspect (img_pats (List.repeat true (List.length (rf_nparams f0)))
                                   (List.firstn (ind_nu D) (nfs_to_exps Ps))) with
                  | exist _ None _ => inr (mgw_uparams (rf_name f0))
                  | exist _ (Some Us) HUs =>
                      match mdef_members_dec Θ Ξ HΞ pq D Us Δ (f0 :: fs) with
                      | inr (exist _ (f, e) _) => inr (mgw_function f e)
                      | inl (exist _ ms Hms) =>
                          match PeanoNat.Nat.eq_dec (List.length ms) (List.length (ind_members D)) with
                          | right _ => inr (mgw_count (List.length (ind_members D)) (List.length ms))
                          | left Hlen =>
                              match members_distinct_dec ms with
                              | right _ => inr mgw_shared
                              | left Hnd =>
                                  inl (exist _ (pq, m0, Ps, D, Us, ms)
                                         (mk_mdef_group _ _ _ _ _ _ _ _ _ _ _ (ex_intro _ i HZ) HW Hl Hm0 HUs Hms Hlen Hnd))
                              end
                          end
                      end
                  end
              end
          end
      | exist _ _ _ => inr (mgw_not_inductive (rf_name f0))
      end
  end.

(** The group the relation has, [mdef_group_dec] finds. *)
Lemma mdef_group_dec_complete : forall Θ Ξ HΞ Δ f0 fs pq m0 Ps D Us ms,
    mdef_group Θ Ξ Δ f0 fs pq m0 Ps D Us ms ->
    exists Hp, mdef_group_dec Θ Ξ HΞ Δ f0 fs = inl (exist _ (pq, m0, Ps, D, Us, ms) Hp).
Proof.
  intros * Hgp; pose proof Hgp as [[i HZ] HW Hl Hm0 HUs Hms Hlen Hnd]; unfold mdef_group_dec.
  destruct (typ_least_dec Θ Ξ HΞ _ _) as [[j [HZ' _]] | HnZ]; [| exfalso; exact (HnZ _ HZ) ].
  destruct (@nbe_ty_impl Θ Ξ (fctx_none _ _) _ _ _) as [W HW'].
  pose proof (functional_nbe_ty _ _ _ _ HW' HW) as ->.
  destruct (opt_case (ind_lookup Θ Ξ pq)) as [[D' Hl'] | Hl']; [| congruence ].
  assert (D' = D) as -> by congruence.
  destruct (Compare_dec.lt_dec m0 (ind_ndecl D)) as [Hm0' | Hm0']; [| contradiction ].
  destruct (inspect _) as [[Us' |] HUs']; [| congruence ].
  assert (Us' = Us) as -> by congruence.
  destruct (mdef_members_dec Θ Ξ HΞ pq D Us Δ (f0 :: fs)) as [[ms' Hms'] | [[f e] Hn]]; [| exfalso; exact (Hn _ Hms) ].
  assert (ms' = ms) as ->
    by (eapply Forall2_functional; [| exact Hms' | exact Hms ]; intros; eapply mdef_member_functional; eassumption).
  destruct (PeanoNat.Nat.eq_dec _ _) as [Hlen' | Hlen']; [| contradiction ].
  destruct (members_distinct_dec ms) as [Hnd' | Hnd']; [| contradiction ].
  eexists; reflexivity.
Qed.
