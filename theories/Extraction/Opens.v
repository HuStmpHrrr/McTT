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
From Mctt.Core.Syntactic.System.Global Require Import Modules.
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
| xe_ind : string -> xerr
(** A record type, which an open does not use *)
| xe_record : string -> xerr.

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

    (** Whether a description is a module only, an open or a closed one. *)
    Definition ds_is_modb (R : mdesc) : bool :=
      match R with
      | ds_open _ _ _ | ds_closed _ _ _ _ _ => true
      | _ => false
      end.

    Lemma ds_is_modb_spec : forall R, ds_is_modb R = true <-> ds_is_mod R.
    Proof. intros []; cbn; split; first [ tauto | discriminate | intros [] ]. Qed.

    (** The definition with a module part an item names, at the global
        level: a member with a term part and a module part ([ign_dm]). *)
    Definition dm_gen (d : string) (pv : bool) (n : string) (R : mdesc) : xres igen :=
      match ds_ty Θ Ξ R, ds_mod Θ Ξ R with
      | Some _, Some _ => xok (ig_def_mod d pv (a_mem H n) (me_mem H n))
      | _, _ => xfail (xe_member H n)
      end.

    (** The item [it] of an open of [H], by what the member it names
        denotes: a term gives a definition, a module an alias, a member with
        a term part and a module part at the global level ([g = true]) a
        definition with a module part; an item naming no member, the alias
        of [H] itself. *)
    Definition item_gen (g : bool) (it : iitem) : xres igen :=
      match it with
      | (None, d, pv) => xok (ig_alias d pv H)
      | (Some n, d, pv) =>
          match denote_of Γ (me_mem H n) (dn_order_mem_of_wf _ _ Hg _ _ _ n HH) with
          | Some (ds_term A _) => xok (ig_def d pv A (a_mem H n))
          | Some R =>
              if ds_is_modb R then xok (ig_alias d pv (me_mem H n))
              else if g then dm_gen d pv n R
              else match R with ds_record _ _ _ => xfail (xe_record n) | _ => xfail (xe_ind n) end
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
      - destruct (denote_of Γ (me_mem H n) _) as [R |] eqn:E; cbn in Hx; [| discriminate ]; apply denote_of_spec in E.
        destruct R as [A om | Δ Φ Φx | Θ' ? T Φ Ns | Θ' p k Ns | Θ' p Ns | Θd A M Rm]; cbn -[dm_gen] in Hx.
        1-3: destruct (xmap (item_gen g) its) as [gs' |] eqn:Er; cbn in Hx; [| discriminate ]; injection Hx as <-;
          first [ eapply ign_def; [ exact E | apply IH; reflexivity ]
                | eapply ign_mod; [ exact E | exact I | apply IH; reflexivity ] ].
        all: destruct g; cbn -[dm_gen] in Hx; [| discriminate ].
        all: unfold dm_gen in Hx; destruct (ds_ty Θ Ξ _) as [A0 |] eqn:Et; [| discriminate ];
          destruct (ds_mod Θ Ξ _) as [Rm0 |] eqn:Em; [| discriminate ]; cbn in Hx.
        all: destruct (xmap (item_gen true) its) as [gs' |] eqn:Er; cbn in Hx; [| discriminate ]; injection Hx as <-.
        all: eapply ign_dm; [ exact E | exact Et | exact Em | apply IH; reflexivity ].
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
      - match goal with Hm : mdenote _ _ _ _ ?R, Ht : ds_ty _ _ ?R = Some _, Hd : ds_mod _ _ ?R = Some _ |- _ =>
          rewrite (proj2 (denote_of_spec _ _ _ _) Hm); destruct R; try (cbn in Ht; discriminate); try (cbn in Hd; discriminate);
          cbn [ds_is_modb]; unfold dm_gen; rewrite Ht, Hd, (IH _ ltac:(eassumption)); reflexivity end.
      - rewrite (IH _ ltac:(eassumption)); reflexivity.
    Qed.

    Lemma xmap_item_gen_spec : forall g its gs,
        xmap (item_gen g) its = xok gs <-> items_gen Θ Ξ g Γ H its gs.
    Proof. split; [ apply xmap_item_gen_sound | apply xmap_item_gen_complete ]. Qed.

    (** [import_gen] computes [open_gens]. *)
    Theorem import_gen_spec : forall g its gs,
        import_gen g its = xok gs <-> open_gens Θ Ξ g Γ H its gs.
    Proof.
      intros; unfold import_gen.
      destruct (denote_of Γ H _) as [R |] eqn:E; cbn [option_map].
      - apply denote_of_spec in E.
        destruct (ds_mod Θ Ξ R) as [Rm |] eqn:Em.
        + destruct (xmap (item_gen g) its) as [gs' | e] eqn:Er; cbn.
          * destruct (both_dup its) eqn:Eb; [ split; [ discriminate | intros [_ _ _ _ _ [Hb _]]; congruence ] |].
            destruct (name_dup (map iitem_name its)) eqn:En; [ split; [ discriminate | intros [_ _ _ _ _ [_ Hn]]; congruence ] |].
            split; [ intros [= <-]; eapply mk_open_gens; [ exact E | exact Em | apply xmap_item_gen_spec; exact Er | split; assumption ] |].
            intros [_ _ _ _ Hi _]; apply xmap_item_gen_spec in Hi; congruence.
          * split; [ discriminate |]; intros [_ _ _ _ Hi _]; apply xmap_item_gen_spec in Hi; congruence.
        + split; [ discriminate |]; intros [R' Rm' HR HRm _ _].
          rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR _ E) in HRm; congruence.
      - split; [ discriminate |]; intros [R' Rm' HR _ _ _].
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
    | a_ind _ _ | a_con _ _ _ | a_nlit _ | a_ntok => xok M
    (** An eliminator: its uniform parameters, each block's annotation,
        motive and branches under their binders, its scrutinee *)
    | a_elim oq Us m Bks M =>
        let+ Us' := (fix oe_us (Us : list exp) : xres (list exp) :=
                       match Us with
                       | nil => xok nil
                       | U :: Us0 => let+ U' := oe_exp S U in let+ Us0' := oe_us Us0 in xok (U' :: Us0')
                       end) Us in
        let+ Bks' := (fix oe_blocks (Bks : list eblock) : xres (list eblock) :=
                        match Bks with
                        | nil => xok nil
                        | eb_mk nm oZ A Bs :: Bks0 =>
                            let+ oZ' := match oZ with
                                        | Some Z => let+ Z' := oe_exp (List.repeat None (nm - 1) ++ S) Z in xok (Some Z')
                                        | None => xok None
                                        end in
                            let+ A' := oe_exp (List.repeat None nm ++ S) A in
                            let+ Bs' := (fix oe_brs (Bs : list (String.string * nat * exp)) : xres (list (String.string * nat * exp)) :=
                                           match Bs with
                                           | nil => xok nil
                                           | b :: Bs0 =>
                                               let+ B' := oe_exp (List.repeat None (snd (fst b)) ++ S) (snd b) in
                                               let+ Bs0' := oe_brs Bs0 in
                                               xok ((fst b, B') :: Bs0')
                                           end) Bs in
                            let+ Bks0' := oe_blocks Bks0 in
                            xok (eb_mk nm oZ' A' Bs' :: Bks0')
                        end) Bks in
        let+ M' := oe_exp S M in
        xok (a_elim oq Us' m Bks' M')
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
    (** A record type former is closed; a tuple, its type and its fields;
        a projection, its argument *)
    | a_record _ => xok M
    | a_tuple T fs =>
        let+ T' := oe_exp S T in
        let+ fs' := (fix oe_flds (fs : list (String.string * exp)) : xres (list (String.string * exp)) :=
                       match fs with
                       | nil => xok nil
                       | (f, N) :: fs0 => let+ N' := oe_exp S N in let+ fs0' := oe_flds fs0 in xok ((f, N') :: fs0')
                       end) fs in
        xok (a_tuple T' fs')
    | a_proj f N => let+ N' := oe_exp S N in xok (a_proj f N')
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
    | ge_ind _ _ _ _ _ | ge_def_mod _ _ _ _ | ge_record _ _ _ _ => xok E
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

  (** A member of a group as written, its uniform parameters [Su] and the
      number [n] of the group's declared types: its non-uniform parameters
      as a telescope over the uniform ones, its sort over the uniform ones,
      its constructors' arguments over the member's parameters and the
      declared types ([raw_member]). *)
  Definition oe_member (Su : skel) (S : skel) (Δu : ctx) (n : nat) (M : raw_member) : xres raw_member :=
    let+ Δn := oe_tele Su (rm_nparams M) in
    let+ A' := oe_exp Su (rm_sort M) in
    let Sm := map centry_skel Δn ++ map centry_skel Δu ++ List.repeat None n ++ S in
    let+ cs' := xmap (fun cg => let+ args := oe_rargs Sm (snd cg) in xok (fst cg, args)) (rm_cons M) in
    xok (mk_rmem (rm_name M) Δn A' cs').

  (** A group as written: its uniform parameters as a telescope, then each
      member. *)
  Definition oe_decl (S : skel) (R : raw_decl) : xres raw_decl :=
    let+ Δ' := oe_tele S (rd_uparams R) in
    let+ ms' := xmap (oe_member (map centry_skel Δ' ++ S) S Δ' (List.length (rd_members R))) (rd_members R) in
    xok (mk_raw Δ' ms' (rd_rec R)).

  (** A function of a [mutual def] as written, over the block's parameters'
      skeleton [Sd]: its non-uniform parameters as a telescope, its
      scrutinee's type over them, its result type over them and the
      scrutinee, and its clauses under their binders. *)
  Definition oe_fun (Sd : skel) (f : raw_fun) : xres raw_fun :=
    let+ ys := oe_tele Sd (rf_nparams f) in
    let Sy := map centry_skel ys ++ Sd in
    let+ Z := oe_exp Sy (rf_scrut f) in
    let+ A := oe_exp (None :: Sy) (rf_res f) in
    let+ cls := xmap (fun cl => let+ B := oe_exp (List.repeat None (snd (fst cl)) ++ Sd) (snd cl) in xok (fst cl, B))
                  (rf_clauses f) in
    xok (mk_rfun (rf_name f) ys Z A cls).

  (** A command's own terms: the nested commands of a module are expanded
      when they run. *)
  Fixpoint oe_cmd (S : skel) (c : ccmd) : xres ccmd :=
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
    | cc_ind pv D =>
        let+ D' := oe_decl S D in
        xok (cc_ind pv D')
    | cc_mdef b pv Δ fs =>
        let+ Δ' := oe_tele S Δ in
        let+ fs' := xmap (oe_fun (map centry_skel Δ' ++ S)) fs in
        xok (cc_mdef b pv Δ' fs')
    | cc_builtin k H =>
        let+ H' := oe_modexp S H in
        xok (cc_builtin k H')
    | cc_ind_alias x pv Δ H =>
        let+ Δ' := oe_tele S Δ in
        let+ H' := oe_modexp (map centry_skel Δ' ++ S) H in
        xok (cc_ind_alias x pv Δ' H')
    | cc_record_alias x pv Δ H =>
        let+ Δ' := oe_tele S Δ in
        let+ H' := oe_modexp (map centry_skel Δ' ++ S) H in
        xok (cc_record_alias x pv Δ' H')
    | cc_record x pv Δ Srt fs cs =>
        let+ Δ' := oe_tele S Δ in
        let+ Srt' := oe_exp (map centry_skel Δ' ++ S) Srt in
        let+ fs' := oe_rargs (map centry_skel Δ' ++ S) fs in
        xok (cc_record x pv Δ' Srt' fs' cs)
    | cc_gen c0 =>
        let+ c0' := oe_cmd S c0 in
        xok (cc_gen c0')
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
