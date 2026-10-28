(** * Computing What an Open Generates

    The checker computes the entries an open of a well-formed module
    expression generates ([import_gen]) from what its members denote
    ([mdenote_impl]): it computes exactly the generation relation of the core
    ([open_gens], [import_gen_spec]), or says why there is none ([open_failure_reason]). *)

From Stdlib Require Import List String Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Members.
From Mctt.Core.Syntactic Require Import Command.
From Mctt.Core.Syntactic.System.Global Require Import Modules.
From Mctt.Extraction Require Import Lookup FastDesc MemberType.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** ** Results *)

(** Why an open fails. *)
Inductive open_failure_reason : Set :=
(** The open's target is not a module *)
| open_failure_reason_target : modexp -> open_failure_reason
(** Not a member of the target *)
| open_failure_reason_member : modexp -> string -> open_failure_reason
(** A member both used and exported *)
| open_failure_reason_both : string -> open_failure_reason
(** A name the open declares twice *)
| open_failure_reason_fresh : string -> open_failure_reason.

Inductive open_result (A : Type) : Type :=
| open_success : A -> open_result A
| open_failure : open_failure_reason -> open_result A.

Arguments open_success {A}.
Arguments open_failure {A}.

Definition open_bind {A B} (m : open_result A) (f : A -> open_result B) : open_result B :=
  match m with
  | open_success a => f a
  | open_failure e => open_failure e
  end.

#[local] Notation "'let+' x ':=' m 'in' f" := (open_bind m (fun x => f))
  (at level 200, x name, m at level 100, f at level 200, right associativity).

Fixpoint open_map {A B} (f : A -> open_result B) (l : list A) : open_result (list B) :=
  match l with
  | nil => open_success nil
  | a :: l' => let+ b := f a in let+ bs := open_map f l' in open_success (b :: bs)
  end.

(** ** Generation *)

Section Gen.
  (** The fast context the denotations are computed in; the judgments are
      at the Core context it stands for. *)
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** What a module expression denotes, when it has an order: a fast
      description, standing for the Core one *)
  Definition mdenote_with_order (Γ : ctx) (H : modexp) (Ho : mdenote_order Θ Ξ Γ H) : option fmdesc :=
    match mdenote_impl F Hg Γ H Ho with
    | inleft (exist _ R _) => Some R
    | inright _ => None
    end.

  Lemma mdenote_with_order_spec : forall Γ H Ho R, option_map dec_desc (mdenote_with_order Γ H Ho) = Some R <-> mdenote Θ Ξ Γ H R.
  Proof.
    intros *; unfold mdenote_with_order.
    destruct (mdenote_impl _ _ _ _ _) as [[R' HR'] | HN]; cbn [option_map]; split; intros HR.
    - injection HR as <-; exact HR'.
    - f_equal; exact (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR' _ HR).
    - discriminate.
    - exfalso; exact (HN _ HR).
  Qed.

  (** A fast description found stands for what the expression denotes. *)
  Lemma mdenote_with_order_sound : forall Γ H Ho R, mdenote_with_order Γ H Ho = Some R -> mdenote Θ Ξ Γ H (dec_desc R).
  Proof. intros * E; apply (proj1 (mdenote_with_order_spec Γ H Ho _)); rewrite E; reflexivity. Qed.

  (** What an expression denotes is found, as a fast description standing
      for it. *)
  Lemma mdenote_with_order_complete : forall Γ H Ho R, mdenote Θ Ξ Γ H R ->
      exists R', mdenote_with_order Γ H Ho = Some R' /\ dec_desc R' = R.
  Proof.
    intros * Hm; apply (proj2 (mdenote_with_order_spec Γ H Ho R)) in Hm.
    destruct (mdenote_with_order Γ H Ho) as [R' |]; cbn in Hm; [| discriminate ]; injection Hm as <-; eauto.
  Qed.

  Section Target.
    Variables (Γ : ctx) (H : modexp) (H' : modexp).
    Hypothesis HH : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H'.

    (** Whether a description is a module only, an open or a closed one. *)
    Definition mdesc_is_modb (R : mdesc) : bool :=
      match R with
      | mdesc_open _ _ _ | mdesc_closed _ _ _ _ _ => true
      | _ => false
      end.

    Lemma mdesc_is_modb_spec : forall R, mdesc_is_modb R = true <-> mdesc_is_mod R.
    Proof. intros []; cbn; split; first [ tauto | discriminate | intros [] ]. Qed.

    (** The definition with a module part an item names: a member with a
        term part and a module part ([items_gen_dm]), of the term part's type. *)
    Definition dm_gen (d : string) (pv : bool) (n : string) (R : fmdesc) : open_result generated_item :=
      match fmdesc_type R, fmdesc_mod R with
      | Some A, Some _ => open_success (generated_item_def_mod d pv A (a_mem H n) (me_mem H n))
      | _, _ => open_failure (open_failure_reason_member H n)
      end.

    (** The item [it] of an open of [H], by what the member it names
        denotes: a term gives a definition, a module an alias, a member with
        a term part and a module part a definition with a module part; an
        item naming no member, the alias of [H] itself. *)
    Definition item_gen (it : iitem) : open_result generated_item :=
      match it with
      | (None, d, pv) => open_success (generated_item_alias d pv H)
      | (Some n, d, pv) =>
          match mdenote_with_order Γ (me_mem H n) (mdenote_order_mem_of_wf _ _ Hg _ _ _ n HH) with
          | Some (fmdesc_term A _) => open_success (generated_item_def d pv A (a_mem H n))
          | Some R =>
              if fmdesc_is_modb R then open_success (generated_item_alias d pv (me_mem H n))
              else dm_gen d pv n R
          | None => open_failure (open_failure_reason_member H n)
          end
      end.

    (** [import_gen its]: [H] is a module, each item names a member of it,
        no member is both used and exported, and the names declared are
        distinct; then each item's declaration, all in [Γ]. *)
    Definition import_gen (its : list iitem) : open_result (list generated_item) :=
      match option_map fmdesc_mod (mdenote_with_order Γ H (mdenote_order_of_wf _ _ Hg _ _ _ HH)) with
      | Some (Some _) =>
          let+ gs := open_map item_gen its in
          match both_dup its with
          | Some n => open_failure (open_failure_reason_both n)
          | None =>
              match name_dup (map iitem_name its) with
              | Some d => open_failure (open_failure_reason_fresh d)
              | None => open_success gs
              end
          end
      | _ => open_failure (open_failure_reason_target H)
      end.

    (** ** Generation Computes the Relation *)

    Lemma open_map_item_gen_sound : forall its gs,
        open_map item_gen its = open_success gs -> items_gen Θ Ξ Γ H its gs.
    Proof.
      induction its as [| [[[n |] d] pv] its IH]; intros gs Hx; cbn in Hx.
      - injection Hx as <-; constructor.
      - destruct (mdenote_with_order Γ (me_mem H n) _) as [R |] eqn:E; cbn in Hx; [| discriminate ]; apply mdenote_with_order_sound in E.
        destruct R as [A om | Δ Φ Φx | Θ' ? T t Ht Ns | Θd A M Rm]; cbn -[dm_gen] in Hx.
        1-3: destruct (open_map item_gen its) as [gs' |] eqn:Er; cbn in Hx; [| discriminate ]; injection Hx as <-;
          cbn [dec_desc] in E;
          first [ eapply items_gen_def; [ exact E | apply IH; reflexivity ]
                | eapply items_gen_mod; [ exact E | exact I | apply IH; reflexivity ] ].
        unfold dm_gen in Hx; destruct (fmdesc_type _) as [A0 |] eqn:Et; [| discriminate ];
          destruct (fmdesc_mod _) as [Rm0 |] eqn:Em; [| discriminate ]; cbn in Hx.
        destruct (open_map item_gen its) as [gs' |] eqn:Er; cbn in Hx; [| discriminate ]; injection Hx as <-.
        eapply items_gen_dm; [ exact E | rewrite fmdesc_type_dec; exact Et | rewrite fmdesc_mod_dec, Em; reflexivity | apply IH; reflexivity ].
      - destruct (open_map item_gen its) as [gs' |] eqn:Er; cbn in Hx; [| discriminate ].
        injection Hx as <-; constructor; apply IH; reflexivity.
    Qed.

    Lemma open_map_item_gen_complete : forall its gs,
        items_gen Θ Ξ Γ H its gs -> open_map item_gen its = open_success gs.
    Proof.
      induction its as [| [[[n |] d] pv] its IH]; intros gs Hi; inversion Hi; subst; cbn.
      - reflexivity.
      - match goal with Hm : mdenote _ _ _ _ _ |- _ =>
          destruct (mdenote_with_order_complete _ _ (mdenote_order_mem_of_wf _ _ Hg _ _ _ n HH) _ Hm) as (R' & -> & ER) end.
        destruct R'; cbn in ER; try discriminate; injection ER as <- <-; rewrite (IH _ ltac:(eassumption)); reflexivity.
      - match goal with Hm : mdenote _ _ _ _ ?R, Hk : mdesc_is_mod ?R |- _ =>
          destruct (mdenote_with_order_complete _ _ (mdenote_order_mem_of_wf _ _ Hg _ _ _ n HH) _ Hm) as (R' & -> & <-);
          rewrite (IH _ ltac:(eassumption));
          destruct R'; cbn in Hk; try contradiction; reflexivity end.
      - match goal with Hm : mdenote _ _ _ _ ?R, Ht : mdesc_type ?R = Some _, Hd : mdesc_mod ?R = Some _ |- _ =>
          destruct (mdenote_with_order_complete _ _ (mdenote_order_mem_of_wf _ _ Hg _ _ _ n HH) _ Hm) as (R' & -> & <-);
          rewrite fmdesc_type_dec in Ht; rewrite fmdesc_mod_dec in Hd;
          destruct R'; try (cbn in Ht; discriminate); try (cbn in Hd; discriminate);
          cbn [fmdesc_is_modb]; unfold dm_gen; rewrite Ht;
          destruct (fmdesc_mod _); [| discriminate ]; rewrite (IH _ ltac:(eassumption)); reflexivity end.
      - rewrite (IH _ ltac:(eassumption)); reflexivity.
    Qed.

    Lemma open_map_item_gen_spec : forall its gs,
        open_map item_gen its = open_success gs <-> items_gen Θ Ξ Γ H its gs.
    Proof. split; [ apply open_map_item_gen_sound | apply open_map_item_gen_complete ]. Qed.

    (** [import_gen] computes [open_gens]. *)
    Theorem import_gen_spec : forall its gs,
        import_gen its = open_success gs <-> open_gens Θ Ξ Γ H its gs.
    Proof.
      intros; unfold import_gen.
      destruct (mdenote_with_order Γ H _) as [R |] eqn:E; cbn [option_map].
      - apply mdenote_with_order_sound in E.
        destruct (fmdesc_mod R) as [Rm |] eqn:Em.
        + destruct (open_map item_gen its) as [gs' | e] eqn:Er; cbn.
          * destruct (both_dup its) eqn:Eb; [ split; [ discriminate | intros [_ _ _ _ _ [Hb _]]; congruence ] |].
            destruct (name_dup (map iitem_name its)) eqn:En; [ split; [ discriminate | intros [_ _ _ _ _ [_ Hn]]; congruence ] |].
            split; [ intros [= <-]; eapply mk_open_gens;
                     [ exact E | rewrite fmdesc_mod_dec, Em; reflexivity | apply open_map_item_gen_spec; exact Er | split; assumption ] |].
            intros [_ _ _ _ Hi _]; apply open_map_item_gen_spec in Hi; congruence.
          * split; [ discriminate |]; intros [_ _ _ _ Hi _]; apply open_map_item_gen_spec in Hi; congruence.
        + split; [ discriminate |]; intros [R' Rm' HR HRm _ _].
          rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR _ E), fmdesc_mod_dec, Em in HRm; discriminate.
      - split; [ discriminate |]; intros [R' Rm' HR _ _ _].
        destruct (mdenote_with_order_complete _ _ (mdenote_order_of_wf _ _ Hg _ _ _ HH) _ HR) as (R'' & E' & _); congruence.
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
  | ce_mod U | ce_dm _ _ U => Some U
  | _ => None
  end.

Definition entry_skel (E : gentry) : option gunit :=
  match E with
  | ge_mod _ U | ge_def_mod _ _ _ U => Some U
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
  (** The fast context the opens are generated in *)
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.
  (** The checker of module expressions: what an open generates is computed
      only for a target it accepts. *)
  Variable mchk : forall Γ H, option (Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H).

  Fixpoint oe_exp (S : skel) (M : exp) {struct M} : open_result exp :=
    match M with
    | a_typ _ | a_level _ | a_llit _ | a_True | a_true | a_False | a_var _ => open_success M
    | a_univ M => let+ M' := oe_exp S M in open_success (a_univ M')
    | a_succl M => let+ M' := oe_exp S M in open_success (a_succl M')
    | a_maxl M N =>
        let+ M' := oe_exp S M in
        let+ N' := oe_exp S N in
        open_success (a_maxl M' N')
    | a_exfalso A M =>
        let+ A' := oe_exp (None :: S) A in
        let+ M' := oe_exp S M in
        open_success (a_exfalso A' M')
    (** The literals are generated before expansion ([Builtin]). *)
    | a_ind _ _ | a_con _ _ _ | a_nlit _ | a_ntok => open_success M
    (** An eliminator: its uniform parameters, each block's annotation,
        motive and branches under their binders, its scrutinee *)
    | a_elim oq Us m Bks M =>
        let+ Us' := (fix oe_us (Us : list exp) : open_result (list exp) :=
                       match Us with
                       | nil => open_success nil
                       | U :: Us0 => let+ U' := oe_exp S U in let+ Us0' := oe_us Us0 in open_success (U' :: Us0')
                       end) Us in
        let+ Bks' := (fix oe_blocks (Bks : list eblock) : open_result (list eblock) :=
                        match Bks with
                        | nil => open_success nil
                        | eb_mk nm oZ A Bs :: Bks0 =>
                            let+ oZ' := match oZ with
                                        | Some Z => let+ Z' := oe_exp (List.repeat None (nm - 1) ++ S) Z in open_success (Some Z')
                                        | None => open_success None
                                        end in
                            let+ A' := oe_exp (List.repeat None nm ++ S) A in
                            let+ Bs' := (fix oe_brs (Bs : list (String.string * nat * exp)) : open_result (list (String.string * nat * exp)) :=
                                           match Bs with
                                           | nil => open_success nil
                                           | b :: Bs0 =>
                                               let+ B' := oe_exp (List.repeat None (snd (fst b)) ++ S) (snd b) in
                                               let+ Bs0' := oe_brs Bs0 in
                                               open_success ((fst b, B') :: Bs0')
                                           end) Bs in
                            let+ Bks0' := oe_blocks Bks0 in
                            open_success (eb_mk nm oZ' A' Bs' :: Bks0')
                        end) Bks in
        let+ M' := oe_exp S M in
        open_success (a_elim oq Us' m Bks' M')
    | a_pi A B =>
        let+ A' := oe_exp S A in
        let+ B' := oe_exp (None :: S) B in
        open_success (a_pi A' B')
    | a_fn A M =>
        let+ A' := oe_exp S A in
        let+ M' := oe_exp (None :: S) M in
        open_success (a_fn A' M')
    | a_app M N =>
        let+ M' := oe_exp S M in
        let+ N' := oe_exp S N in
        open_success (a_app M' N')
    | a_let b B =>
        let+ b' := oe_bnd S b in
        let+ B' := oe_exp (bnd_skel b' :: S) B in
        open_success (a_let b' B')
    | a_mem H x => let+ H' := oe_modexp S H in open_success (a_mem H' x)
    (** A record type former is closed; a tuple, its type and its fields;
        a projection, its argument *)
    | a_record _ => open_success M
    | a_tuple T fs =>
        let+ T' := oe_exp S T in
        let+ fs' := (fix oe_flds (fs : list (String.string * exp)) : open_result (list (String.string * exp)) :=
                       match fs with
                       | nil => open_success nil
                       | (f, N) :: fs0 => let+ N' := oe_exp S N in let+ fs0' := oe_flds fs0 in open_success ((f, N') :: fs0')
                       end) fs in
        open_success (a_tuple T' fs')
    | a_proj f N => let+ N' := oe_exp S N in open_success (a_proj f N')
    end
  with oe_modexp (S : skel) (H : modexp) {struct H} : open_result modexp :=
    match H with
    | me_unit _ | me_var _ => open_success H
    | me_mem H y => let+ H' := oe_modexp S H in open_success (me_mem H' y)
    | me_app H N =>
        let+ H' := oe_modexp S H in
        let+ N' := oe_exp S N in
        open_success (me_app H' N')
    | me_lit U => let+ U' := oe_unit S U in open_success (me_lit U')
    end
  with oe_bnd (S : skel) (b : bnd) {struct b} : open_result bnd :=
    match b with
    | b_def oA M =>
        let+ oA' := match oA with
                    | Some A => let+ A' := oe_exp S A in open_success (Some A')
                    | None => open_success None
                    end in
        let+ M' := oe_exp S M in
        open_success (b_def oA' M')
    | b_mod U => let+ U' := oe_unit S U in open_success (b_mod U')
    end
  with oe_unit (S : skel) (U : gunit) {struct U} : open_result gunit :=
    match U with
    | gu_mk Δ D =>
        let+ Δ' := (fix oe_tele (Δ : list centry) : open_result ctx :=
                      match Δ with
                      | nil => open_success nil
                      | e :: Δ0 =>
                          let+ Δ0' := oe_tele Δ0 in
                          let+ e' := oe_centry (map centry_skel Δ0' ++ S) e in
                          open_success (e' :: Δ0')
                      end) Δ in
        let+ D' := oe_def (map centry_skel Δ' ++ S) D in
        open_success (gu_mk Δ' D')
    end
  with oe_def (S : skel) (D : moddef) {struct D} : open_result moddef :=
    match D with
    | md_body sm Φ => let+ Φ' := oe_body S Φ in open_success (md_body sm Φ')
    | md_alias E => let+ E' := oe_modexp S E in open_success (md_alias E')
    end
  with oe_body (S : skel) (Φ : gmod) {struct Φ} : open_result gmod :=
    match Φ with
    | gm_nil => open_success gm_nil
    | gm_ext Φ x E =>
        let+ Φ' := oe_body S Φ in
        let+ E' := oe_entry (body_skel Φ' ++ S) E in
        open_success (gm_ext Φ' x E')
    | gm_open Φ H its =>
        let+ Φ' := oe_body S Φ in
        let+ H' := oe_modexp (body_skel Φ' ++ S) H in
        match mchk (skel_ctx (body_skel Φ' ++ S)) H' with
        | Some HH =>
            let+ gs := import_gen F Hg (skel_ctx (body_skel Φ' ++ S)) H' H' HH its in
            open_success (gens_append Φ' 0 gs)
        | None => open_failure (open_failure_reason_target H')
        end
    end
  with oe_entry (S : skel) (E : gentry) {struct E} : open_result gentry :=
    match E with
    | ge_def b pv A B =>
        let+ A' := oe_exp S A in
        let+ B' := match B with
                   | Some M => let+ M' := oe_exp S M in open_success (Some M')
                   | None => open_success None
                   end in
        open_success (ge_def b pv A' B')
    | ge_mod pv U => let+ U' := oe_unit S U in open_success (ge_mod pv U')
    | ge_def_mod pv A M U =>
        let+ A' := oe_exp S A in
        let+ M' := oe_exp S M in
        let+ U' := oe_unit S U in
        open_success (ge_def_mod pv A' M' U')
    | ge_ind _ _ _ _ _ | ge_record _ _ _ _ => open_success E
    end
  with oe_centry (S : skel) (e : centry) {struct e} : open_result centry :=
    match e with
    | ce_ass A => let+ A' := oe_exp S A in open_success (ce_ass A')
    | ce_def A M =>
        let+ A' := oe_exp S A in
        let+ M' := oe_exp S M in
        open_success (ce_def A' M')
    | ce_mod U => let+ U' := oe_unit S U in open_success (ce_mod U')
    | ce_dm A M U =>
        let+ A' := oe_exp S A in
        let+ M' := oe_exp S M in
        let+ U' := oe_unit S U in
        open_success (ce_dm A' M' U')
    end.

  (** A telescope, each entry in the skeleton of the entries outside it. *)
  Fixpoint oe_tele (S : skel) (Δ : ctx) : open_result ctx :=
    match Δ with
    | nil => open_success nil
    | e :: Δ0 =>
        let+ Δ0' := oe_tele S Δ0 in
        let+ e' := oe_centry (map centry_skel Δ0' ++ S) e in
        open_success (e' :: Δ0')
    end.

  (** The arguments of a constructor as written: each binds a variable for
      the ones after it. *)
  Fixpoint oe_rargs (S : skel) (args : list (string * exp)) : open_result (list (string * exp)) :=
    match args with
    | nil => open_success nil
    | (y, T) :: args' =>
        let+ T' := oe_exp S T in
        let+ args'' := oe_rargs (None :: S) args' in
        open_success ((y, T') :: args'')
    end.

  (** A member of a group as written, its uniform parameters [Su] and the
      number [n] of the group's declared types: its non-uniform parameters
      as a telescope over the uniform ones, its sort over the uniform ones,
      its constructors' arguments over the member's parameters and the
      declared types ([raw_member]). *)
  Definition oe_member (Su : skel) (S : skel) (Δu : ctx) (n : nat) (M : raw_member) : open_result raw_member :=
    let+ Δn := oe_tele Su (raw_member_nparams M) in
    let+ A' := oe_exp Su (raw_member_sort M) in
    let Sm := map centry_skel Δn ++ map centry_skel Δu ++ List.repeat None n ++ S in
    let+ cs' := open_map (fun cg => let+ args := oe_rargs Sm (snd cg) in open_success (fst cg, args)) (raw_member_cons M) in
    open_success (mk_rmem (raw_member_name M) Δn A' cs').

  (** A group as written: its uniform parameters as a telescope, then each
      member. *)
  Definition oe_decl (S : skel) (R : raw_decl) : open_result raw_decl :=
    let+ Δ' := oe_tele S (raw_decl_uparams R) in
    let+ ms' := open_map (oe_member (map centry_skel Δ' ++ S) S Δ' (List.length (raw_decl_members R))) (raw_decl_members R) in
    open_success (mk_raw Δ' ms' (raw_decl_rec_field R)).

  (** A function of a [mutual def] as written, over the block's parameters'
      skeleton [Sd]: its non-uniform parameters as a telescope, its
      scrutinee's type over them, its result type over them and the
      scrutinee, and its clauses under their binders. *)
  Definition oe_fun (Sd : skel) (f : raw_fun) : open_result raw_fun :=
    let+ ys := oe_tele Sd (raw_fun_nparams f) in
    let Sy := map centry_skel ys ++ Sd in
    let+ Z := oe_exp Sy (raw_fun_scrut f) in
    let+ A := oe_exp (None :: Sy) (raw_fun_res f) in
    let+ cls := open_map (fun cl => let+ B := oe_exp (List.repeat None (snd (fst cl)) ++ Sd) (snd cl) in open_success (fst cl, B))
                  (raw_fun_clauses f) in
    open_success (mk_rfun (raw_fun_name f) ys Z A cls).

  (** A command's own terms: the nested commands of a module are expanded
      when they run. *)
  Fixpoint oe_cmd (S : skel) (c : core_cmd) : open_result core_cmd :=
    match c with
    | core_cmd_def x b pv A (Some M) =>
        let+ A' := oe_exp S A in
        let+ M' := oe_exp S M in
        open_success (core_cmd_def x b pv A' (Some M'))
    | core_cmd_def x b pv A None =>
        let+ A' := oe_exp S A in
        open_success (core_cmd_def x b pv A' None)
    | core_cmd_mod x pv Δ cs =>
        let+ Δ' := oe_tele S Δ in
        open_success (core_cmd_mod x pv Δ' cs)
    | core_cmd_alias x pv Δ E =>
        let+ Δ' := oe_tele S Δ in
        let+ E' := oe_modexp (map centry_skel Δ' ++ S) E in
        open_success (core_cmd_alias x pv Δ' E')
    | core_cmd_load fp => open_success (core_cmd_load fp)
    | core_cmd_open E its =>
        let+ E' := oe_modexp S E in
        open_success (core_cmd_open E' its)
    | core_cmd_eval M oA =>
        let+ M' := oe_exp S M in
        let+ oA' := match oA with
                    | Some A => let+ A' := oe_exp S A in open_success (Some A')
                    | None => open_success None
                    end in
        open_success (core_cmd_eval M' oA')
    | core_cmd_inductive pv D =>
        let+ D' := oe_decl S D in
        open_success (core_cmd_inductive pv D')
    | core_cmd_mdef b pv Δ fs =>
        let+ Δ' := oe_tele S Δ in
        let+ fs' := open_map (oe_fun (map centry_skel Δ' ++ S)) fs in
        open_success (core_cmd_mdef b pv Δ' fs')
    | core_cmd_builtin k H =>
        let+ H' := oe_modexp S H in
        open_success (core_cmd_builtin k H')
    | core_cmd_inductive_alias x pv Δ H =>
        let+ Δ' := oe_tele S Δ in
        let+ H' := oe_modexp (map centry_skel Δ' ++ S) H in
        open_success (core_cmd_inductive_alias x pv Δ' H')
    | core_cmd_record_alias x pv Δ H =>
        let+ Δ' := oe_tele S Δ in
        let+ H' := oe_modexp (map centry_skel Δ' ++ S) H in
        open_success (core_cmd_record_alias x pv Δ' H')
    | core_cmd_record x pv Δ Srt fs cs =>
        let+ Δ' := oe_tele S Δ in
        let+ Srt' := oe_exp (map centry_skel Δ' ++ S) Srt in
        let+ fs' := oe_rargs (map centry_skel Δ' ++ S) fs in
        open_success (core_cmd_record x pv Δ' Srt' fs' cs)
    | core_cmd_gen c0 =>
        let+ c0' := oe_cmd S c0 in
        open_success (core_cmd_gen c0')
    end.
  (** The first open of a command's own terms that generates nothing, if
      any, read as the checker reads the command. *)
  Definition cmd_open_error (S : skel) (c : core_cmd) : option open_failure_reason :=
    match oe_cmd S c with
    | open_failure e => Some e
    | open_success _ => None
    end.

  Definition tele_open_error (S : skel) (Δ : ctx) : option open_failure_reason :=
    match oe_tele S Δ with
    | open_failure e => Some e
    | open_success _ => None
    end.
End OpenError.
