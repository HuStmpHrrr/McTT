(** * Checking Privacy

    [decl_impl] computes where a member reached from a unit is declared, by
    recursion on the order [mt_order] of member types, which follows aliases
    exactly as [mdecl] does.  [refs_check] decides [acc_ok], and names the
    first private member that is out of reach. *)

From Stdlib Require Import List String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Import Definitions Privacy.
From Mctt.Extraction Require Import MemberType.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** A private member out of reach: declared in the module of a unit, or
    an entry of a local body, at the chain of submodules [ch] from the local
    module. *)
Inductive priv_err : Set :=
| pe_global : qname -> string -> priv_err
| pe_local : list string -> string -> priv_err.

Section PrivacyImpl.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local]
  Ltac decl_obl :=
    intros; cbv beta in *;
    repeat match goal with
      | H : mt_order _ _ _ _ _ |- _ => progressive_invert H
      | H : umt_order _ _ _ _ _ |- _ => progressive_invert H
      end;
    repeat match goal with H : ?a = ?a -> _ |- _ => specialize (H eq_refl) end;
    try solve [ eauto ];
    first
      [ solve [ match goal with Hd : exists T E, _ = _ /\ _ |- _ =>
                  destruct Hd as (? & ? & -> & ?); eapply mdl_alias; [ | eassumption | eassumption ]; discriminate end ]
      | solve [ eapply mdl_entry; [ eassumption | reflexivity ] ]
      | solve [ eapply mdl_alias; [ | eassumption | eassumption ]; discriminate ]
      | solve [ do 2 eexists; split; [ reflexivity | eassumption ] ]
      | solve [ econstructor; eassumption ]
      | solve [ eapply mdl_alias; eassumption ]
      | solve [ intros; match goal with HN : forall _ _, ~ mdecl _ _ ?E ?c _ _, Hd : mdecl _ _ ?E ?c _ _ |- _ =>
                  exact (HN _ _ Hd) end ]
      | solve [ intros * Heq; try discriminate; injection Heq; intros; subst; intros ? ? ?;
                match goal with HN : forall _ _, ~ mdecl _ _ ?E ?c _ _, Hd : mdecl _ _ ?E ?c _ _ |- _ =>
                  exact (HN _ _ Hd) end ]
      | solve [ intros * Hd; inversion Hd; subst; try congruence;
                try match goal with HN : forall _ _, ~ mdecl _ _ _ _ _ _ |- _ => eapply HN; eassumption end;
                try match goal with
                    | H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = _ |- _ =>
                        rewrite H1 in H2; try discriminate; injection H2; intros; subst end;
                try match goal with HN : forall _ _, ~ mdecl _ _ _ _ _ _ |- _ => eapply HN; eassumption end;
                try match goal with HN : forall _ _, _ = _ -> forall _ _, ~ mdecl _ _ _ _ _ _ |- _ =>
                      eapply HN; [ reflexivity | eassumption ] end;
                congruence ] ].

  #[local] Ltac decl_obl_try := try decl_obl.

  #[tactic="decl_obl_try",derive(equations=no,eliminator=no)]
  Equations decl_impl Γ H ch (Ho : mt_order Θ Ξ Γ H ch) :
      { d : qname * bool | mdecl Θ Ξ H ch (fst d) (snd d) } + { forall qd pv, ~ mdecl Θ Ξ H ch qd pv }
      by struct Ho :=
  | Γ, me_unit fp, ch, Ho with inspect (gc_entry Θ Ξ (q_abs fp ch)) := {
    | exist _ (Some E) Er => inleft (exist _ (q_abs fp (removelast ch), ge_private E) _)
    | exist _ None Er with inspect (gc_module Θ Ξ (q_abs fp ch)) := {
      | exist _ (Some (mr_alias U (y :: r))) Em with decl_unit_impl nil U (y :: r) _ := {
        | inleft (exist _ d Hd) => inleft (exist _ d _)
        | inright HN => inright _ }
      | exist _ _ Em => inright _ } }
  | Γ, me_var x, ch, Ho => inright _
  | Γ, me_lit U, ch, Ho => inright _
  | Γ, me_mem M y, ch, Ho with decl_impl Γ M (y :: ch) _ := {
    | inleft (exist _ d Hd) => inleft (exist _ d _)
    | inright HN => inright _ }
  | Γ, me_app M N, ch, Ho with decl_impl Γ M ch _ := {
    | inleft (exist _ d Hd) => inleft (exist _ d _)
    | inright HN => inright _ }

  with decl_unit_impl Γ U ch (Ho : umt_order Θ Ξ Γ U ch) :
      { d : qname * bool | exists T E, U = gu_mk T (md_alias E) /\ mdecl Θ Ξ E ch (fst d) (snd d) } +
      { forall T E, U = gu_mk T (md_alias E) -> forall qd pv, ~ mdecl Θ Ξ E ch qd pv }
      by struct Ho :=
  | Γ, gu_mk Δ (md_alias E), ch, Ho with decl_impl (Δ ++ Γ) E ch _ := {
    | inleft (exist _ d Hd) => inleft (exist _ d _)
    | inright HN => inright _ }
  | Γ, gu_mk Δ (md_body Φ), ch, Ho => inright _.
  Next Obligation. decl_obl. Qed.

  (** Whether a module is an open frame or an ancestor of one. *)
  Definition open_anc_b (qd : qname) : bool :=
    existsb (fun e => andb (path_beq (q_unit (fst e)) (q_unit qd))
                      (match strip_prefix (q_chain qd) (q_chain (fst e)) with Some _ => true | None => false end)) Ξ.

  Lemma open_anc_b_spec : forall qd, open_anc_b qd = true <-> open_anc Ξ qd.
  Proof.
    intros qd; unfold open_anc_b, open_anc; rewrite existsb_exists; split.
    - intros ([mp U] & Hin & Hb); apply andb_prop in Hb as [H1 H2]; cbn in *.
      apply path_beq_true in H1.
      destruct (strip_prefix (q_chain qd) (q_chain mp)) as [suf |] eqn:E; [| discriminate ].
      exists mp, U, suf; repeat split; [ exact Hin | exact H1 | exact (strip_prefix_spec _ _ _ E) ].
    - intros (mp & U & suf & Hin & H1 & H2); exists (mp, U); split; [ exact Hin |]; cbn.
      rewrite H1, path_beq_refl, H2, strip_prefix_app; reflexivity.
  Qed.

  Hypothesis Hg : ⊢g Θ ⍮ Ξ.

  (** A reference to a member reached from a unit is checked where the
      member is declared; a failure names that module and the member. *)
  Definition glob_check (H : modexp) (x : string) :
      { qx : qname * string | ~ glob_ok Θ Ξ H x } + { glob_ok Θ Ξ H x }.
  Proof.
    unfold glob_ok.
    destruct (modexp_spine H) as [[[fp | k | H0 y | H0 N | U] args] pre]; try (right; exact I).
    destruct (decl_impl nil (me_unit fp) (pre ++ x :: nil) (mt_order_unit _ _ _ _ _ Hg)) as [[[qd [|]] Hd] | HN];
      cbn [fst snd] in *.
    - destruct (open_anc_b qd) eqn:Eo.
      + right; intros qd' Hd'; destruct (mdecl_functional _ _ _ _ _ _ Hd _ _ Hd') as [<- _].
        apply open_anc_b_spec; exact Eo.
      + left; exists (qd, x); intros Hok; specialize (Hok _ Hd).
        apply open_anc_b_spec in Hok; congruence.
    - right; intros qd' Hd'; destruct (mdecl_functional _ _ _ _ _ _ Hd _ _ Hd') as [_ [=]].
    - right; intros qd' Hd'; exfalso; exact (HN _ _ Hd').
  Defined.

  Definition ref_check (r : (ptab * string)%type) :
      { e : priv_err | ~ ref_ok Θ Ξ r } + { ref_ok Θ Ξ r }.
  Proof.
    destruct r as [[| H | ch es] x]; unfold ref_ok; cbn [fst snd].
    - right; exact I.
    - destruct (glob_check H x) as [[qx Hq] | Hok]; [ left; exists (pe_global (fst qx) (snd qx)); exact Hq | right; exact Hok ].
    - destruct (option_map fst (tab_find x es)) as [[|] |] eqn:E.
      + left; exists (pe_local ch x); intros Hn; apply Hn; reflexivity.
      + right; discriminate.
      + right; discriminate.
  Defined.

  Definition refs_check : forall (l : list (ptab * string)%type),
      { e : priv_err | ~ acc_ok Θ Ξ l } + { acc_ok Θ Ξ l }.
  Proof.
    induction l as [| r l IH]; [ right; constructor |].
    destruct (ref_check r) as [[e Hr] | Hr]; [ left; exists e; intros Hall; inversion Hall; contradiction |].
    destruct IH as [[e Hl] | Hl]; [ left; exists e; intros Hall; inversion Hall; contradiction | right; constructor; assumption ].
  Defined.
End PrivacyImpl.
