(** * Computing What an Open Generates

    The checker computes the entries an open of a well-formed module
    expression generates ([import_gen]) from what its members denote
    ([mdenote_impl]): it computes exactly the generation relation of the core
    ([open_gens], [import_gen_spec]), or says why there is none ([xerr]).  A
    local open ([g = false]) of an inductive type is rejected ([xe_ind]). *)

From Stdlib Require Import List String Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Members.
From Mctt.Core.Syntactic Require Import Command.
From Mctt.Core.Syntactic.System Require Import GlobalModules.
From Mctt.Extraction Require Import MemberType.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** ** Results *)

(** Why an open fails. *)
Inductive xerr : Set :=
(** The open's target is not a module *)
| xe_target : modexp -> xerr
(** Not a member of the target *)
| xe_member : modexp -> string -> xerr
(** A member both used and exported *)
| xe_both : string -> xerr
(** A name the open declares twice *)
| xe_fresh : string -> xerr
(** An inductive type, or an inductive alias, opened in a local module *)
| xe_ind : string -> xerr.

Inductive xres (A : Type) : Type :=
| xok : A -> xres A
| xfail : xerr -> xres A.

Arguments xok {A}.
Arguments xfail {A}.

Definition xbind {A B} (m : xres A) (f : A -> xres B) : xres B :=
  match m with
  | xok a => f a
  | xfail e => xfail e
  end.

#[local] Notation "'let+' x ':=' m 'in' f" := (xbind m (fun x => f))
  (at level 200, x name, m at level 100, f at level 200, right associativity).

Fixpoint xmap {A B} (f : A -> xres B) (l : list A) : xres (list B) :=
  match l with
  | nil => xok nil
  | a :: l' => let+ b := f a in let+ bs := xmap f l' in xok (b :: bs)
  end.

(** ** Generation *)

Section Gen.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** What a module expression denotes, when it has an order. *)
  Definition denote_of (Γ : ctx) (H : modexp) (Ho : dn_order Θ Ξ Γ H) : option mdesc :=
    match mdenote_impl Θ Ξ Hg Γ H Ho with
    | inleft (exist _ R _) => Some R
    | inright _ => None
    end.

  Lemma denote_of_spec : forall Γ H Ho R, denote_of Γ H Ho = Some R <-> mdenote Θ Ξ Γ H R.
  Proof.
    intros *; unfold denote_of.
    destruct (mdenote_impl _ _ _ _ _ _) as [[R' HR'] | HN]; split; intros HR.
    - injection HR as <-; exact HR'.
    - f_equal; exact (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR' _ HR).
    - discriminate.
    - exfalso; exact (HN _ HR).
  Qed.

  Section Target.
    Variables (Γ : ctx) (H : modexp) (H' : modexp).
    Hypothesis HH : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H'.

    (** The item [it] of an open of [H], by what the member it names
        denotes: a term gives a definition, a module an alias, an inductive
        type at the global level ([g = true]) an inductive alias; or the
        alias of [H] itself. *)
    Definition item_gen (g : bool) (it : iitem) : xres igen :=
      match it with
      | (None, d, pv) => xok (ig_alias d pv H)
      | (Some n, d, pv) =>
          match denote_of Γ (me_mem H n) (dn_order_mem_of_wf _ _ Hg _ _ _ n HH) with
          | Some (ds_term A _) => xok (ig_def d pv A (a_mem H n))
          | Some (ds_open _ _ _) | Some (ds_closed _ _ _ _ _) => xok (ig_alias d pv (me_mem H n))
          | Some (ds_ind Θ' p Ns) => if g then xok (ig_ind_alias d pv Θ' p Ns) else xfail (xe_ind n)
          | None => xfail (xe_member H n)
          end
      end.

    (** [import_gen g its]: [H] is a module, each item names a member of
        it, no member is both used and exported, and the names declared are
        distinct; then each item's declaration, all in [Γ]. *)
    Definition import_gen (g : bool) (its : list iitem) : xres (list igen) :=
      match option_map (ds_mod Θ Ξ) (denote_of Γ H (dn_order_of_wf _ _ Hg _ _ _ HH)) with
      | Some (Some _) =>
          let+ gs := xmap (item_gen g) its in
          match both_dup its with
          | Some n => xfail (xe_both n)
          | None =>
              match name_dup (map iitem_name its) with
              | Some d => xfail (xe_fresh d)
              | None => xok gs
              end
          end
      | _ => xfail (xe_target H)
      end.

    (** ** Generation Computes the Relation *)

    Lemma xmap_item_gen_sound : forall g its gs,
        xmap (item_gen g) its = xok gs -> items_gen Θ Ξ g Γ H its gs.
    Proof.
      intros g; induction its as [| [[[n |] d] pv] its IH]; intros gs Hx; cbn in Hx.
      - injection Hx as <-; constructor.
      - destruct (denote_of Γ (me_mem H n) _) as [[A om | Δ Φ | Θ' ? T Φ Ns | Θ' p Ns] |] eqn:E; cbn in Hx;
          [| | | | discriminate ]; apply denote_of_spec in E.
        + destruct (xmap (item_gen g) its) as [gs' |] eqn:Er; cbn in Hx; [| discriminate ].
          injection Hx as <-; eapply ign_def; [ exact E | apply IH; reflexivity ].
        + destruct (xmap (item_gen g) its) as [gs' |] eqn:Er; cbn in Hx; [| discriminate ].
          injection Hx as <-; eapply ign_mod; [ exact E | exact I | apply IH; reflexivity ].
        + destruct (xmap (item_gen g) its) as [gs' |] eqn:Er; cbn in Hx; [| discriminate ].
          injection Hx as <-; eapply ign_mod; [ exact E | exact I | apply IH; reflexivity ].
        + destruct g; cbn in Hx; [| discriminate ].
          destruct (xmap (item_gen true) its) as [gs' |] eqn:Er; cbn in Hx; [| discriminate ].
          injection Hx as <-; eapply ign_ind; [ exact E | apply IH; reflexivity ].
      - destruct (xmap (item_gen g) its) as [gs' |] eqn:Er; cbn in Hx; [| discriminate ].
        injection Hx as <-; constructor; apply IH; reflexivity.
    Qed.

    Lemma xmap_item_gen_complete : forall g its gs,
        items_gen Θ Ξ g Γ H its gs -> xmap (item_gen g) its = xok gs.
    Proof.
      intros g; induction its as [| [[[n |] d] pv] its IH]; intros gs Hi; inversion Hi; subst; cbn.
      - reflexivity.
      - rewrite (proj2 (denote_of_spec _ _ _ _) ltac:(eassumption)), (IH _ ltac:(eassumption)); reflexivity.
      - match goal with Hm : mdenote _ _ _ _ ?R, Hk : ds_is_mod ?R |- _ =>
          rewrite (proj2 (denote_of_spec _ _ _ _) Hm), (IH _ ltac:(eassumption));
          destruct R; cbn in Hk; try contradiction; reflexivity end.
      - rewrite (proj2 (denote_of_spec _ _ _ _) ltac:(eassumption)), (IH _ ltac:(eassumption)); reflexivity.
      - rewrite (IH _ ltac:(eassumption)); reflexivity.
    Qed.

    Lemma xmap_item_gen_spec : forall g its gs,
        xmap (item_gen g) its = xok gs <-> items_gen Θ Ξ g Γ H its gs.
    Proof. split; [ apply xmap_item_gen_sound | apply xmap_item_gen_complete ]. Qed.

    (** [import_gen] computes [open_gens]. *)
    Theorem import_gen_spec : forall g its gs,
        import_gen g its = xok gs <-> open_gens Θ Ξ g Γ H its gs.
    Proof.
      intros; unfold import_gen, open_gens, items_ok.
      destruct (denote_of Γ H _) as [R |] eqn:E; cbn [option_map].
      - apply denote_of_spec in E.
        destruct (ds_mod Θ Ξ R) as [Rm |] eqn:Em.
        + destruct (xmap (item_gen g) its) as [gs' | e] eqn:Er; cbn.
          * destruct (both_dup its) eqn:Eb; [ split; [ discriminate | intros (_ & _ & Hb & _); discriminate ] |].
            destruct (name_dup (map iitem_name its)) eqn:En; [ split; [ discriminate | intros (_ & _ & _ & Hn); discriminate ] |].
            split; [ intros [= <-]; repeat split; eauto; apply xmap_item_gen_spec; exact Er |].
            intros (_ & Hi & _); apply xmap_item_gen_spec in Hi; congruence.
          * split; [ discriminate |]; intros (_ & Hi & _); apply xmap_item_gen_spec in Hi; congruence.
        + split; [ discriminate |]; intros ((R' & Rm' & HR & HRm) & _).
          rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR _ E) in HRm; congruence.
      - split; [ discriminate |]; intros ((R' & Rm' & HR & _) & _).
        rewrite (proj2 (denote_of_spec _ _ _ _) HR) in E; discriminate.
    Qed.
  End Target.
End Gen.

(** ** The First Open That Generates Nothing

    Where a command is rejected, the error names the first open in it that
    generates nothing, if there is one ([cmd_open_error]): its terms are
    read in order, each local body entry by entry, every open replaced by
    what it generates so that the ones after it are read in the context it
    makes.  This only chooses the message; the judgment and the checker
    read the opens themselves ([body_xp]).

    [S] is the slot skeleton of the context: [Some U] for a module slot
    holding the unit [U], [None] for anything else.  Member types read a
    context only through its module slots. *)

Abbreviation skel := (list (option gunit)).

Definition skel_ctx (S : skel) : ctx :=
  map (fun o => match o with Some U => ce_mod U | None => ce_ass a_True end) S.

Definition centry_skel (e : centry) : option gunit :=
  match e with
  | ce_mod U => Some U
  | _ => None
  end.

Definition entry_skel (E : gentry) : option gunit :=
  match E with
  | ge_mod _ U => Some U
  | _ => None
  end.

Definition bnd_skel (b : bnd) : option gunit :=
  match b with
  | b_mod U => Some U
  | _ => None
  end.

(** The skeleton of the indices a body binds, newest first. *)
Fixpoint body_skel (Φ : gmod) : skel :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ _ E => entry_skel E :: body_skel Φ
  | gm_open Φ _ its => repeat None (List.length its) ++ body_skel Φ
  end.

(** The skeleton of a frame: its parameters are assumptions. *)
Definition frame_skel (Ξ : gstack) : skel := map (fun _ => None) (gs_tele Ξ).

Section OpenError.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.
  (** The checker of module expressions: what an open generates is computed
      only for a target it accepts. *)
  Variable mchk : forall Γ H, option (Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H).

  Fixpoint oe_exp (S : skel) (M : exp) {struct M} : xres exp :=
    match M with
    | a_typ _ | a_level _ | a_llit _ | a_True | a_true | a_False | a_var _ => xok M
    | a_univ M => let+ M' := oe_exp S M in xok (a_univ M')
    | a_succl M => let+ M' := oe_exp S M in xok (a_succl M')
    | a_maxl M N =>
        let+ M' := oe_exp S M in
        let+ N' := oe_exp S N in
        xok (a_maxl M' N')
    | a_exfalso A M =>
        let+ A' := oe_exp (None :: S) A in
        let+ M' := oe_exp S M in
        xok (a_exfalso A' M')
    (** The literals are generated before expansion ([Builtin]). *)
    | a_ind _ | a_con _ _ | a_nlit _ | a_ntok => xok M
    | a_elim nm A Bs M =>
        let+ A' := oe_exp (List.repeat None nm ++ S) A in
        let+ Bs' := (fix oe_brs (Bs : list (String.string * nat * exp)) : xres (list (String.string * nat * exp)) :=
                       match Bs with
                       | nil => xok nil
                       | b :: Bs0 =>
                           let+ B' := oe_exp (List.repeat None (snd (fst b)) ++ S) (snd b) in
                           let+ Bs0' := oe_brs Bs0 in
                           xok ((fst b, B') :: Bs0')
                       end) Bs in
        let+ M' := oe_exp S M in
        xok (a_elim nm A' Bs' M')
    | a_pi A B =>
        let+ A' := oe_exp S A in
        let+ B' := oe_exp (None :: S) B in
        xok (a_pi A' B')
    | a_fn A M =>
        let+ A' := oe_exp S A in
        let+ M' := oe_exp (None :: S) M in
        xok (a_fn A' M')
    | a_app M N =>
        let+ M' := oe_exp S M in
        let+ N' := oe_exp S N in
        xok (a_app M' N')
    | a_let b B =>
        let+ b' := oe_bnd S b in
        let+ B' := oe_exp (bnd_skel b' :: S) B in
        xok (a_let b' B')
    | a_mem H x => let+ H' := oe_modexp S H in xok (a_mem H' x)
    end
  with oe_modexp (S : skel) (H : modexp) {struct H} : xres modexp :=
    match H with
    | me_unit _ | me_var _ => xok H
    | me_mem H y => let+ H' := oe_modexp S H in xok (me_mem H' y)
    | me_app H N =>
        let+ H' := oe_modexp S H in
        let+ N' := oe_exp S N in
        xok (me_app H' N')
    | me_lit U => let+ U' := oe_unit S U in xok (me_lit U')
    end
  with oe_bnd (S : skel) (b : bnd) {struct b} : xres bnd :=
    match b with
    | b_def oA M =>
        let+ oA' := match oA with
                    | Some A => let+ A' := oe_exp S A in xok (Some A')
                    | None => xok None
                    end in
        let+ M' := oe_exp S M in
        xok (b_def oA' M')
    | b_mod U => let+ U' := oe_unit S U in xok (b_mod U')
    end
  with oe_unit (S : skel) (U : gunit) {struct U} : xres gunit :=
    match U with
    | gu_mk Δ D =>
        let+ Δ' := (fix oe_tele (Δ : list centry) : xres ctx :=
                      match Δ with
                      | nil => xok nil
                      | e :: Δ0 =>
                          let+ Δ0' := oe_tele Δ0 in
                          let+ e' := oe_centry (map centry_skel Δ0' ++ S) e in
                          xok (e' :: Δ0')
                      end) Δ in
        let+ D' := oe_def (map centry_skel Δ' ++ S) D in
        xok (gu_mk Δ' D')
    end
  with oe_def (S : skel) (D : moddef) {struct D} : xres moddef :=
    match D with
    | md_body sm Φ => let+ Φ' := oe_body S Φ in xok (md_body sm Φ')
    | md_alias E => let+ E' := oe_modexp S E in xok (md_alias E')
    end
  with oe_body (S : skel) (Φ : gmod) {struct Φ} : xres gmod :=
    match Φ with
    | gm_nil => xok gm_nil
    | gm_ext Φ x E =>
        let+ Φ' := oe_body S Φ in
        let+ E' := oe_entry (body_skel Φ' ++ S) E in
        xok (gm_ext Φ' x E')
    | gm_open Φ H its =>
        let+ Φ' := oe_body S Φ in
        let+ H' := oe_modexp (body_skel Φ' ++ S) H in
        match mchk (skel_ctx (body_skel Φ' ++ S)) H' with
        | Some HH =>
            let+ gs := import_gen Θ Ξ Hg (skel_ctx (body_skel Φ' ++ S)) H' H' HH false its in
            xok (gens_append Φ' 0 gs)
        | None => xfail (xe_target H')
        end
    end
  with oe_entry (S : skel) (E : gentry) {struct E} : xres gentry :=
    match E with
    | ge_def b pv A B =>
        let+ A' := oe_exp S A in
        let+ B' := match B with
                   | Some M => let+ M' := oe_exp S M in xok (Some M')
                   | None => xok None
                   end in
        xok (ge_def b pv A' B')
    | ge_mod pv U => let+ U' := oe_unit S U in xok (ge_mod pv U')
    | ge_ind _ _ _ _ | ge_ind_alias _ _ _ _ => xok E
    end
  with oe_centry (S : skel) (e : centry) {struct e} : xres centry :=
    match e with
    | ce_ass A => let+ A' := oe_exp S A in xok (ce_ass A')
    | ce_def A M =>
        let+ A' := oe_exp S A in
        let+ M' := oe_exp S M in
        xok (ce_def A' M')
    | ce_mod U => let+ U' := oe_unit S U in xok (ce_mod U')
    end.

  (** A telescope, each entry in the skeleton of the entries outside it. *)
  Fixpoint oe_tele (S : skel) (Δ : ctx) : xres ctx :=
    match Δ with
    | nil => xok nil
    | e :: Δ0 =>
        let+ Δ0' := oe_tele S Δ0 in
        let+ e' := oe_centry (map centry_skel Δ0' ++ S) e in
        xok (e' :: Δ0')
    end.

  (** The arguments of a constructor as written: each binds a variable for
      the ones after it. *)
  Fixpoint oe_rargs (S : skel) (args : list (string * exp)) : xres (list (string * exp)) :=
    match args with
    | nil => xok nil
    | (y, T) :: args' =>
        let+ T' := oe_exp S T in
        let+ args'' := oe_rargs (None :: S) args' in
        xok ((y, T') :: args'')
    end.

  (** A declaration as written: its parameters as a telescope, its sort over
      the uniform ones, its constructors' arguments over the declared type
      and all the parameters. *)
  Definition oe_decl (S : skel) (R : raw_decl) : xres raw_decl :=
    let+ Δ' := oe_tele S (rd_params R) in
    let S' := map centry_skel Δ' ++ S in
    let+ A' := oe_exp (skipn (List.length (rd_params R) - rd_nu R) S') (rd_sort R) in
    let+ cs' := xmap (fun cg => let+ args := oe_rargs (None :: S') (snd cg) in xok (fst cg, args)) (rd_cons R) in
    xok (mk_raw (rd_nu R) Δ' A' cs').

  (** A command's own terms: the nested commands of a module are expanded
      when they run. *)
  Definition oe_cmd (S : skel) (c : ccmd) : xres ccmd :=
    match c with
    | cc_def x b pv A (Some M) =>
        let+ A' := oe_exp S A in
        let+ M' := oe_exp S M in
        xok (cc_def x b pv A' (Some M'))
    | cc_def x b pv A None =>
        let+ A' := oe_exp S A in
        xok (cc_def x b pv A' None)
    | cc_mod x pv Δ cs =>
        let+ Δ' := oe_tele S Δ in
        xok (cc_mod x pv Δ' cs)
    | cc_alias x pv Δ E =>
        let+ Δ' := oe_tele S Δ in
        let+ E' := oe_modexp (map centry_skel Δ' ++ S) E in
        xok (cc_alias x pv Δ' E')
    | cc_load fp => xok (cc_load fp)
    | cc_open E its =>
        let+ E' := oe_modexp S E in
        xok (cc_open E' its)
    | cc_eval M oA =>
        let+ M' := oe_exp S M in
        let+ oA' := match oA with
                    | Some A => let+ A' := oe_exp S A in xok (Some A')
                    | None => xok None
                    end in
        xok (cc_eval M' oA')
    | cc_ind x pv D =>
        let+ D' := oe_decl S D in
        xok (cc_ind x pv D')
    | cc_builtin k H =>
        let+ H' := oe_modexp S H in
        xok (cc_builtin k H')
    | cc_ind_alias x pv Δ H =>
        let+ Δ' := oe_tele S Δ in
        let+ H' := oe_modexp (map centry_skel Δ' ++ S) H in
        xok (cc_ind_alias x pv Δ' H')
    end.
  (** The first open of a command's own terms that generates nothing, if
      any, read as the checker reads the command. *)
  Definition cmd_open_error (S : skel) (c : ccmd) : option xerr :=
    match oe_cmd S c with
    | xfail e => Some e
    | xok _ => None
    end.

  Definition tele_open_error (S : skel) (Δ : ctx) : option xerr :=
    match oe_tele S Δ with
    | xfail e => Some e
    | xok _ => None
    end.
End OpenError.
