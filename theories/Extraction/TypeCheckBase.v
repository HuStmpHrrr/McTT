From Stdlib Require Import List ListDec Morphisms_Relations String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base.
From Mctt.Core Require Import Consequences.Consistency Semantic.Realizability.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Core.Semantic Require Import MemberWf.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import FastDomain NbE PseudoMonadic Subtyping FastDesc MemberType.
From Mctt.Extraction Require Import Evaluation.
Import Domain_Notations Wk_Notations Fixed_Notations.

(** * What the Checker's Parts Share

    The checker ([Extraction.TypeCheck]) and its parts for inductive and
    record types ([Extraction.IndCheck], [Extraction.RecordCheck]) recurse
    along the same orders, decide the same side conditions, carry the same
    initial environment, and prove their obligations with the same
    tactics, which are therefore defined here. *)

Section Fixed_GCtx.
Context {GC : GCtx}.

Section type_check.
  (** ** Deciding the Side Conditions of Terms *)

  (** Whether a normal form is a universe, and at which index: the side
      condition of every rule that asks for a type of a universe.  A plain
      [match], so that the extracted code is one case analysis and the two
      universe cases are visibly the only ones. *)
  Definition univ_nf_idx_dec (A : nf) : { u : universe_nf | is_univ_nf A u } + { forall u, ~ is_univ_nf A u }.
  Proof.
    refine (match A with
            | nf_typ i => inleft (exist _ (universe_large i) _)
            | nf_univ c xs => inleft (exist _ (universe_small (c, xs)) _)
            | _ => inright _
            end);
      first [ constructor | intros ? H; inversion H ].
  Defined.

  (** Whether a normal form is the type of a type, of which kind and in
      which universe: a universe, [Prop] or [LevelSort] ([is_sort_nf]). *)
  Definition sort_nf_dec (A : nf) : { κ & { u : universe_nf | is_sort_nf A κ u } } + { forall κ u, ~ is_sort_nf A κ u }.
  Proof.
    destruct (univ_nf_idx_dec A) as [[u Hu] | Hnu]; [ left; exists ak_relevant, u; constructor; exact Hu |].
    destruct A; try (right; intros ? ? H; inversion H; subst; eapply Hnu; eassumption).
    - left; exists ak_level, (universe_small (ordinal_of_nat 0, nil)); constructor.
    - left; exists ak_propositional, (universe_small (ordinal_of_nat 0, nil)); constructor.
  Defined.

  (** Whether a normal form is [Prop]. *)
  #[derive(equations=no,eliminator=no)]
  Equations prop_nf_dec (A : nf) : { A = Propⁿ } + { A <> Propⁿ } :=
  | Propⁿ => left eq_refl
  | _ => right _
  .

  (** Whether a normal form is [LevelSort]. *)
  #[derive(equations=no,eliminator=no)]
  Equations level_sort_nf_dec (A : nf) : { A = LevelSortⁿ } + { A <> LevelSortⁿ } :=
  | LevelSortⁿ => left eq_refl
  | _ => right _
  .

  (** Whether a normal form is a [Π], and its kinds and parts. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_pi_nf (A : nf) :
      { κd & { κc & { B & { C | A = nf_pi κd κc B C } } } } + { forall κd κc B C, A <> nf_pi κd κc B C } :=
  | nf_pi κd κc B C => pureo (existT _ κd (existT _ κc (existT _ B (exist _ C _))))
  | _ => inright _
  .

  (** Whether a normal form is a conjunction, and its parts. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_and_nf (A : nf) : { P & { Q | A = Σₚⁿ P Q } } + { forall P Q, A <> Σₚⁿ P Q } :=
  | Σₚⁿ P Q => pureo (existT _ P (exist _ Q _))
  | _ => inright _
  .

  (** Whether a normal form is a type of levels, and of which sort. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_level_sort_nf (A : nf) : { k | A = Levelⁿ@k } + { forall k, A <> Levelⁿ@k } :=
  | Levelⁿ@k => pureo (exist _ k _)
  | _        => inright _
  .

  (** Whether two kinds are ones a [Π] may join ([pi_kinds]). *)
  Definition pi_kinds_dec (κd κc : abs_kind) : { pi_kinds κd κc } + { ~ pi_kinds κd κc }.
  Proof.
    destruct κc; [ left; constructor | left; constructor |].
    destruct κd; [ right; intros H; inversion H | right; intros H; inversion H | left; constructor ].
  Defined.

  (** Whether a normal form, read as a term, is [LevelSort]: the
      condition on the body's type of a λ and of a local binding. *)
  Definition nf_level_sort_dec (B : nf) : { nf_to_exp B = LevelSort } + { nf_to_exp B <> LevelSort }.
  Proof. exact (exp_eq_dec (nf_to_exp B) LevelSort). Defined.

  (** Extraction should set the 9th bit of [Extraction Flag] (for example,
      [Set Extraction Flag 1007.]); otherwise the decisions that return
      parts introduce redundant pair construction and pattern matching. *)
  Extraction Inline univ_nf_idx_dec sort_nf_dec prop_nf_dec level_sort_nf_dec get_pi_nf get_and_nf
    get_level_sort_nf pi_kinds_dec nf_level_sort_dec.

  (** ** Deciding the Side Conditions of Units *)

  (** Whether every entry of a telescope is an assumption. *)
  Definition all_assumptions_dec : forall Δ, { all_assumptions Δ } + { ~ all_assumptions Δ }.
  Proof.
    induction Δ as [| [κ A | A M | U | A M U] Δ IH].
    - left; constructor.
    - destruct IH as [H | H]; [ left; constructor; eauto | right; intros Hf; inversion Hf; contradiction ].
    - right; intros Hf; inversion Hf as [| ? ? (? & ? & ?) _]; discriminate.
    - right; intros Hf; inversion Hf as [| ? ? (? & ? & ?) _]; discriminate.
    - right; intros Hf; inversion Hf as [| ? ? (? & ? & ?) _]; discriminate.
  Defined.

  (** [ListDec.NoDup_dec] is opaque, so extraction would bypass it. *)
  Definition names_nodup_dec : forall l : list string, { NoDup l } + { ~ NoDup l }.
  Proof.
    induction l as [| x l IH].
    - left; constructor.
    - destruct (in_dec string_dec x l) as [Hin | Hn].
      + right; intros Hnd; inversion Hnd; contradiction.
      + destruct IH as [H | H]; [ left; constructor; assumption | right; intros Hnd; inversion Hnd; contradiction ].
  Defined.

  Definition entry_shape_dec : forall E E', { entry_shape E E' } + { ~ entry_shape E E' }.
  Proof.
    intros [b pv κ A [M |] | pm U | pvi pk ki Di Φi | pd ? ? ? | ? ? ? ?]
      [b' pv' κ' A' [M' |] | pm' U' | pvi' pk' ki' Di' Φi' | pd' ? ? ? | ? ? ? ?]; cbn;
      try (right; intros []; fail); try (left; exact I).
    - destruct b, b', (Bool.bool_dec pv pv'), (abs_kind_eq_dec κ κ'); try (right; intuition congruence; fail); left; auto.
    - exact (Bool.bool_dec pm pm').
    - exact (Bool.bool_dec pd pd').
  Defined.

  Definition import_item_eq_dec : forall it it' : import_item, { it = it' } + { it <> it' }.
  Proof. repeat decide equality; apply string_dec. Defined.

  Fixpoint body_shape_dec (Φ Φ' : gmod) {struct Φ} : { body_shape Φ Φ' } + { ~ body_shape Φ Φ' }.
  Proof.
    destruct Φ as [| Φ x E | Φ H its Φg], Φ' as [| Φ' x' E' | Φ' H' its' Φg']; cbn;
      try (left; exact I); try (right; intros []; fail).
    - destruct (body_shape_dec Φ Φ') as [H1 | H1]; [| right; intuition ].
      destruct (string_dec x x') as [H2 | H2]; [| right; intuition ].
      destruct (entry_shape_dec E E') as [H3 | H3]; [ left; auto | right; intuition ].
    - destruct (body_shape_dec Φ Φ') as [H1 | H1]; [| right; intuition ].
      destruct (list_eq_dec import_item_eq_dec its its') as [H2 | H2]; [| right; intuition ].
      destruct (body_shape_dec Φg Φg') as [H3 | H3]; [ left; auto | right; intuition ].
  Defined.

  (** The outermost parameter of an arity, if any. *)
  Equations tele_view_dec (T : ctx) : { B : typ & { T1 : ctx | tele_view T = Some (B, T1) } } + { tele_view T = None } :=
  tele_view_dec T with inspect (tele_view T) := {
    | exist _ (Some (B, T1)) E => inleft (existT _ B (exist _ T1 E))
    | exist _ None E => inright E }.

  (** What a description gives the rules: a member's type ([mdesc_type]), a
      module's telescope ([mdesc_mod_tele]) and module part ([mdesc_mod]), read off
      the fast description of [MemberType.mdenote_impl]. *)
  Equations mdesc_type_dec (R : fmdesc) : { A | mdesc_type (decode_desc R) = Some A } + { mdesc_type (decode_desc R) = None } :=
  mdesc_type_dec R with fmdesc_type_s R := {
    | exist _ (Some A) E => inleft (exist _ A E)
    | exist _ None E => inright E }.

  Equations mdesc_mod_tele_dec (R : fmdesc) : { T | mdesc_mod_tele (decode_desc R) = Some T } + { mdesc_mod_tele (decode_desc R) = None } :=
  mdesc_mod_tele_dec R with inspect (fmdesc_mod_tele R) := {
    | exist _ (Some T) E => inleft (exist _ T (eq_trans (fmdesc_mod_tele_dec R) E))
    | exist _ None E => inright (eq_trans (fmdesc_mod_tele_dec R) E) }.

  Equations mdesc_mod_dec (R : fmdesc) : { Rm : fmdesc | mdesc_mod (decode_desc R) = Some (decode_desc Rm) } + { mdesc_mod (decode_desc R) = None } :=
  mdesc_mod_dec R with fmdesc_mod_s R := {
    | exist _ (Some Rm) E => inleft (exist _ Rm E)
    | exist _ None E => inright E }.

  Extraction Inline mdesc_type_dec mdesc_mod_tele_dec mdesc_mod_dec tele_view_dec.

  (** ** Facts the Obligations Use *)

  (** A type has the order of its normalization. *)
  Lemma nbe_order_of_type : forall G X, G ⊢ᵗ X -> nbe_ty_order gc_deps gc_stack G X.
  Proof. intros * HX; destruct (nbe_ty_exists_wf_type HX) as [W HW]; eauto using nbe_ty_order_sound. Qed.

  (** The same for a type of a large universe. *)
  Lemma nbe_order_of_typ : forall G X i, G ⊢ X : Typeω@i -> nbe_ty_order gc_deps gc_stack G X.
  Proof. intros * HX; apply nbe_order_of_type; eapply wf_type_of_sort; [ apply type_sort_universe | exact HX ]. Qed.

  (** The context of a type is well-formed. *)
  Lemma wf_type_ctx : forall G X, G ⊢ᵗ X -> ⊢ G.
  Proof. intros * [? S HS HX | HG]; [ gen_presups; assumption | exact HG ]. Qed.

  (** The type a term infers is a type. *)
  Lemma wf_type_of_infer : forall G M A, ⊢ G -> G ⊢a M ⟹ A -> G ⊢ᵗ A.
  Proof. intros * HG HM; exact (presup_exp_typ (alg_type_infer_sound HM HG)). Qed.

  (** The normal form of a type is a type. *)
  Lemma wf_type_nbe : forall G X W, G ⊢ᵗ X -> nbe_ty_f G X W -> G ⊢ᵗ W.
  Proof.
    intros * [? S HS HX | HG] HW.
    - pose proof (soundness_ty_at_sort HS HX HW) as HXW.
      eapply wf_type_of_sort; [ exact HS | gen_presups; eassumption ].
    - pose proof (nbe_ty_level_sort_self HG).
      functional_nbe_rewrite_clear; exact (wf_type_level_sort HG).
  Qed.

  (** A type whose inferred sort is one of a kind ([is_sort_nf]) is a
      type. *)
  Lemma type_of_sort_infer : forall G A UA κ u, ⊢ G -> G ⊢a A ⟹ UA -> is_sort_nf UA κ u -> G ⊢ᵗ A.
  Proof.
    intros * HG HA Hs.
    exact (wf_type_of_sort _ (type_sort_kind_universe κ (universe_nf_large_index u))
             (sort_typed_of_is_sort_nf (alg_type_infer_sound HA HG) Hs)).
  Qed.

  (** The type a member of a checked module expression is read at is a
      type ([member_wf]). *)
  Lemma member_typ_of_alg : forall G M x R A, ⊢ G -> G ⊢aᵐ M ->
      mdenote gc_deps gc_stack G (me_mem M x) R -> mdesc_type R = Some A -> G ⊢ᵗ A.
  Proof.
    intros * HG HM Hm Ht.
    destruct (proj1 (member_wf _ _ _ _ _ (alg_modexp_sound HM HG) Hm Ht)) as (S & HS & HA).
    exact (wf_type_of_sort _ HS HA).
  Qed.

  (** ** The Initial Environment the Checker Carries

      Every normalization the checker does is at the initial environment of
      its context, as a fast environment that erases to it ([fast_env]).
      The checker computes it once, where it enters a context, and extends
      it entry by entry under binders, rather than once per normalization
      ([nbe_ty_env_impl]). *)
  Definition checker_env G := fast_env gc_deps gc_stack G.

  (** A well-formed context has an initial environment. *)
  Lemma initial_env_of_wf : forall G, ⊢ G -> exists ρ, initial_env_f G ρ.
  Proof.
    intros G HG.
    destruct (nbe_ty_exists_sort (type_sort_universe 1) (wf_typ _ _ _ 0 HG)) as [W [ρ a Hρ _ _]].
    exists ρ; exact Hρ.
  Qed.

  Lemma checker_env_order_of_wf : forall G, ⊢ G -> initial_env_order gc_deps gc_stack G.
  Proof. intros G HG; destruct (initial_env_of_wf G HG) as [ρ Hρ]; eauto using initial_env_order_sound. Qed.

  (** The initial environment of a context one entry longer: by its rule,
      at the initial environment of the context. *)
  Lemma initial_env_of_wf_cons : forall G e ρ, ⊢ e :: G -> initial_env_f G ρ ->
      exists ρ', initial_env_f (e :: G) ρ'.
  Proof. intros * HG _; exact (initial_env_of_wf _ HG). Qed.

  (** The type of an assumption evaluates at the initial environment. *)
  Lemma checker_env_order_ass : forall G κ A ρ, ⊢ G ▹{κ} A -> initial_env_f G ρ -> eval_exp_order gc_deps gc_stack A ρ.
  Proof.
    intros * HG Hρ; destruct (initial_env_of_wf _ HG) as [ρ' Hρ'].
    inversion Hρ'; subst; functional_initial_env_rewrite_clear; eauto using eval_exp_order_sound.
  Qed.

  (** So does the type of a definition, and its body at a type of an
      evaluated kind. *)
  Lemma checker_env_order_def_typ : forall G A M ρ, ⊢ G ▸ A ≔ M -> initial_env_f G ρ -> eval_exp_order gc_deps gc_stack A ρ.
  Proof.
    intros * HG Hρ; destruct (initial_env_of_wf _ HG) as [ρ' Hρ'].
    inversion Hρ'; subst; functional_initial_env_rewrite_clear; eauto using eval_exp_order_sound.
  Qed.

  Lemma checker_env_order_def : forall G A M ρ a, ⊢ G ▸ A ≔ M -> initial_env_f G ρ ->
      ⟦ A ⟧ ρ ↘ a -> evaluated_kind (domain_kind a) -> eval_exp_order gc_deps gc_stack M ρ.
  Proof.
    intros * HG Hρ Ha Hk; destruct (initial_env_of_wf _ HG) as [ρ' Hρ'].
    inversion Hρ'; subst; functional_initial_env_rewrite_clear; functional_eval_rewrite_clear;
      eauto using eval_exp_order_sound.
    exfalso; eapply evaluated_kind_not_propositional; eassumption.
  Qed.

  (** The unit of a module slot evaluates. *)
  Lemma checker_env_order_mod : forall G U ρ, ⊢ G ▹ₘ U -> initial_env_f G ρ ->
      eval_modexp_order gc_deps gc_stack (me_lit U) ρ.
  Proof.
    intros * HG Hρ; destruct (initial_env_of_wf _ HG) as [ρ' Hρ'].
    inversion Hρ'; subst; functional_initial_env_rewrite_clear; eauto using eval_modexp_order_sound.
  Qed.

  (** The type, the term and the unit of a definition with a module part
      evaluate. *)
  Lemma checker_env_order_dm : forall G A M U ρ, ⊢ G ▸ₘ A ≔ M ‖ U -> initial_env_f G ρ ->
      eval_exp_order gc_deps gc_stack A ρ /\ eval_exp_order gc_deps gc_stack M ρ /\
      eval_modexp_order gc_deps gc_stack (me_lit U) ρ.
  Proof.
    intros * HG Hρ; destruct (initial_env_of_wf _ HG) as [ρ' Hρ'].
    inversion Hρ'; subst; functional_initial_env_rewrite_clear;
      eauto 6 using eval_exp_order_sound, eval_modexp_order_sound.
  Qed.

  (** A type evaluates at the initial environment. *)
  Lemma checker_env_order_type : forall G T ρ, G ⊢ᵗ T -> initial_env_f G ρ -> eval_exp_order gc_deps gc_stack T ρ.
  Proof.
    intros * HT Hρ; destruct (nbe_ty_exists_wf_type HT) as [W [ρ' a Hρ' Ha _]].
    functional_initial_env_rewrite_clear; eauto using eval_exp_order_sound.
  Qed.

  (** ** The Orders of the Checker

      The checker recurses along the syntax; every term, unit and module
      expression has its order ([type_infer_order_all] and the like). *)
  Inductive type_check_order : exp -> Prop :=
  | type_check_order_ti : forall {A}, type_infer_order A -> type_check_order A
  with type_infer_order : exp -> Prop :=
  | type_infer_order_typ : forall {i}, type_infer_order Typeω@i
  | type_infer_order_suniv : forall {M}, type_infer_order M -> type_infer_order Type⟨M⟩
  | type_infer_order_level : forall {n}, type_infer_order Level@n
  (** [LevelSort] is of no type: nothing to check *)
  | type_infer_order_level_sort : type_infer_order LevelSort
  | type_infer_order_llit : forall {o}, type_infer_order (𝕃ᵒ o)
  | type_infer_order_succl : forall {M}, type_infer_order M -> type_infer_order (succl M)
  | type_infer_order_maxl : forall {M N}, type_infer_order M -> type_infer_order N -> type_infer_order (maxl M N)
  (** [Prop], the closed propositions and the introduction of [⊤] recurse
      on nothing *)
  | type_infer_order_prop : type_infer_order Propₘ
  | type_infer_order_True : type_infer_order ⊤
  | type_infer_order_tt : type_infer_order a_tt
  | type_infer_order_False : type_infer_order ⊥
  (** Ex falso infers its target and checks its proof *)
  | type_infer_order_absurd : forall {C M}, type_infer_order C -> type_check_order M -> type_infer_order (efq M return C)
  (** A conjunction infers its parts *)
  | type_infer_order_and : forall {P Q}, type_infer_order P -> type_infer_order Q -> type_infer_order (Σₚ P Q)
  (** A proof of a conjunction infers its annotations and checks its
      components *)
  | type_infer_order_conj : forall {P Q M N}, type_infer_order P -> type_infer_order Q ->
      type_check_order M -> type_check_order N -> type_infer_order (a_conj P Q M N)
  (** The components of a proof of a conjunction infer it *)
  | type_infer_order_left : forall {M}, type_infer_order M -> type_infer_order (a_left M)
  | type_infer_order_right : forall {M}, type_infer_order M -> type_infer_order (a_right M)
  | type_infer_order_indty : forall {p k}, type_infer_order (a_ind p k)
  | type_infer_order_con : forall {p k c}, type_infer_order (a_con p k c)
  (** An eliminator: its scrutinee infers, its uniform parameters, the
      scrutinee types, the motives and the branches of its blocks are
      checked. *)
  | type_infer_order_elim : forall {r oq Us m Bks M}, type_infer_order M ->
      (forall U, List.In U Us -> type_check_order U) ->
      (forall b, List.In b Bks -> type_check_order (eb_scrutinee_type b)) ->
      (forall b, List.In b Bks -> type_check_order (eb_motive b)) ->
      (forall b br, List.In b Bks -> List.In br (eb_brs b) -> type_check_order (snd br)) ->
      type_infer_order (a_elim r oq Us m Bks M)
  (** A [Π] infers its domain and its codomain *)
  | type_infer_order_pi : forall {κd κc A B}, type_infer_order A -> type_infer_order B -> type_infer_order (a_pi κd κc A B)
  | type_infer_order_fn : forall {A M}, type_infer_order A -> type_infer_order M -> type_infer_order λ A M
  | type_infer_order_app : forall {M N}, type_infer_order M -> type_check_order N -> type_infer_order (M $ N)
  | type_infer_order_let : forall {A M B}, type_infer_order A -> type_check_order M -> type_infer_order B ->
      type_infer_order (a_let (b_def A M) B)
  | type_infer_order_let_mod : forall {U B}, unit_order U -> type_infer_order B -> type_infer_order (ℓₘ U in B)
  | type_infer_order_mem : forall {H x}, modexp_order H -> type_infer_order (a_mem H x)
  | type_infer_order_vlookup : forall {x}, type_infer_order #x
  (** A record's type former recurses on nothing *)
  | type_infer_order_record : forall {p}, type_infer_order (a_record p)
  (** A tuple infers its annotation and checks its fields *)
  | type_infer_order_tuple : forall {T fs}, type_infer_order T -> (forall fm, List.In fm fs -> type_check_order (snd fm)) ->
      type_infer_order (a_tuple T fs)
  (** A projection infers its element *)
  | type_infer_order_proj : forall {f M}, type_infer_order M -> type_infer_order (a_proj f M)
  with ext_order : ctx -> Prop :=
  | ext_order_nil : ext_order nil
  | ext_order_ass : forall {κ A Ψ}, ext_order Ψ -> type_infer_order A -> ext_order (Ψ ▹{κ} A)
  | ext_order_def : forall {A M Ψ}, ext_order Ψ -> type_infer_order A -> type_check_order M -> ext_order (Ψ ▸ A ≔ M)
  | ext_order_mod : forall {U Ψ}, ext_order Ψ -> unit_order U -> ext_order (Ψ ▹ₘ U)
  (** A definition with a module part: as a definition and as a slot *)
  | ext_order_dm : forall {A M U Ψ}, ext_order Ψ -> type_infer_order A -> type_check_order M -> unit_order U ->
      ext_order (Ψ ▸ₘ A ≔ M ‖ U)
  with unit_order : gunit -> Prop :=
  | unit_order_body : forall {Δ sm Φ}, ext_order Δ -> body_order Φ -> unit_order (gu_mk Δ (md_body sm Φ))
  | unit_order_alias : forall {Δ E}, ext_order Δ -> modexp_order E -> unit_order (gu_mk Δ (md_alias E))
  (** A body, entry by entry; an entry no body may hold has nothing to
      check. *)
  with body_order : gmod -> Prop :=
  | body_order_nil : body_order gm_nil
  | body_order_def : forall {Φ x b pv κ A M}, body_order Φ -> type_infer_order A -> type_check_order M ->
      body_order (gm_ext Φ x (ge_def b pv κ A (Some M)))
  | body_order_mod : forall {Φ x pm U}, body_order Φ -> unit_order U -> body_order (gm_ext Φ x (ge_mod pm U))
  | body_order_axiom : forall {Φ x b pv κ A}, body_order Φ -> body_order (gm_ext Φ x (ge_def b pv κ A None))
  | body_order_ind_case : forall {Φ x pv p k D Φi}, body_order Φ -> body_order (gm_ext Φ x (ge_ind pv p k D Φi))
  (** A definition with a module part: its term part as a definition, its
      unit as a submodule *)
  | body_order_def_mod : forall {Φ x pv A M U}, body_order Φ -> type_infer_order A -> type_check_order M -> unit_order U ->
      body_order (gm_ext Φ x (ge_def_mod pv A M U))
  (** A record declaration: as written in no local body, only the entries
      before it *)
  | body_order_record : forall {Φ x pv pr R Φr}, body_order Φ -> body_order (gm_ext Φ x (ge_record pv pr R Φr))
  | body_order_open : forall {Φ H its Φg}, body_order Φ -> modexp_order H -> body_order (gm_open Φ H its Φg)
  with modexp_order : modexp -> Prop :=
  | modexp_order_unit : forall {fp}, modexp_order (me_unit fp)
  | modexp_order_var : forall {x}, modexp_order (me_var x)
  | modexp_order_lit : forall {U}, unit_order U -> modexp_order (me_lit U)
  | modexp_order_mem : forall {H y}, modexp_order H -> modexp_order (me_mem H y)
  | modexp_order_app : forall {H N}, modexp_order H -> type_check_order N -> modexp_order (me_app H N)
  .

  #[local]
  Hint Constructors type_check_order type_infer_order ext_order unit_order body_order modexp_order : mctt.

  (** The order of a context entry *)
  Definition centry_order (e : centry) : Prop :=
    match e with
    | ce_ass _ A => type_infer_order A
    | ce_def A M => type_infer_order A /\ type_check_order M
    | ce_mod U => unit_order U
    | ce_dm A M U => type_infer_order A /\ type_check_order M /\ unit_order U
    end.

  Lemma ext_order_app : forall X Δ, List.Forall centry_order X -> ext_order Δ -> ext_order (X ++ Δ).
  Proof.
    induction X as [| [κ A | A M | U | A M U] X IH]; intros * HX HΔ; cbn; [ exact HΔ | | | |];
      inversion HX as [| ? ? He HX']; subst; cbn in He; destruct_conjs; constructor; auto.
  Qed.

  Lemma ext_order_of_forall : forall X, List.Forall centry_order X -> ext_order X.
  Proof. intros X HX; rewrite <- (app_nil_r X); apply ext_order_app; [ exact HX | constructor ]. Qed.

  (** Every piece of syntax has its order. *)
  Lemma syn_orders_all :
    (forall M, type_infer_order M) /\
    (forall H, modexp_order H) /\
    (forall b, match b with
           | b_def A M => type_infer_order A /\ type_infer_order M
           | b_mod U => unit_order U
           end) /\
    (forall U, unit_order U) /\
    (forall D, match D with
           | md_body sm Φ => body_order Φ
           | md_alias E => modexp_order E
           end) /\
    (forall Φ, body_order Φ) /\
    (forall E, match E with
           | ge_def _ _ _ A B => type_infer_order A /\ (forall M, B = Some M -> type_infer_order M)
           | ge_mod _ U => unit_order U
           | ge_def_mod _ A M U => type_infer_order A /\ type_infer_order M /\ unit_order U
           | ge_ind _ _ _ _ _ | ge_record _ _ _ _ => True
           end) /\
    (forall e, centry_order e).
  Proof.
    apply (syn_mut_ind type_infer_order modexp_order
      (fun b => match b with
             | b_def A M => type_infer_order A /\ type_infer_order M
             | b_mod U => unit_order U
             end)
      unit_order
      (fun D => match D with
             | md_body sm Φ => body_order Φ
             | md_alias E => modexp_order E
             end)
      body_order
      (fun E => match E with
             | ge_def _ _ _ A B => type_infer_order A /\ (forall M, B = Some M -> type_infer_order M)
             | ge_mod _ U => unit_order U
             | ge_def_mod _ A M U => type_infer_order A /\ type_infer_order M /\ unit_order U
             | ge_ind _ _ _ _ _ | ge_record _ _ _ _ => True
             end)
      centry_order); intros; cbn in *; destruct_conjs; eauto 6 with mctt.
    (* a tuple: its fields are checked *)
    all: try match goal with HF : List.Forall _ ?fs |- type_infer_order (a_tuple _ ?fs) =>
           rewrite List.Forall_forall in HF; constructor; [ assumption | intros fm Hfm; apply type_check_order_ti; auto ] end.
    - (* an eliminator: its uniform parameters, scrutinee types, motives and branches are checked *)
      match goal with
      | HU : List.Forall _ ?Us, HB : List.Forall _ ?Bks |- type_infer_order (a_elim _ _ ?Us _ ?Bks _) =>
          rewrite List.Forall_forall in HU, HB
      end.
      constructor; [ assumption | intros U HU'; apply type_check_order_ti; auto
                   | intros b Hb; apply type_check_order_ti;
                     match goal with HB : forall x, List.In x _ -> _ /\ _ |- _ => exact (proj1 (HB b Hb)) end
                   | intros b Hb; apply type_check_order_ti;
                     match goal with HB : forall x, List.In x _ -> _ /\ _ |- _ => exact (proj1 (proj2 (HB b Hb))) end
                   | intros b br Hb Hbr; apply type_check_order_ti;
                     match goal with HB : forall x, List.In x _ -> _ /\ _ |- _ =>
                       exact (proj1 (List.Forall_forall _ _) (proj2 (proj2 (HB b Hb))) br Hbr) end ].
    - (* a local binding *)
      destruct b as [A M | U]; destruct_conjs;
        [ apply type_infer_order_let; [ assumption | constructor; assumption | assumption ]
        | apply type_infer_order_let_mod; assumption ].
    - destruct D; destruct_conjs; constructor; auto using ext_order_of_forall.
    - destruct E as [b pv κ A [M |] | pm U | pvi pk ki Di Φi | ? ? ? ? | ? ? ? ?]; destruct_conjs;
        first [ apply body_order_def; eauto with mctt | apply body_order_mod; assumption
              | apply body_order_axiom; assumption | apply body_order_ind_case; assumption | apply body_order_def_mod; eauto with mctt
              | apply body_order_record; assumption ].
  Qed.

  Lemma type_infer_order_all : forall M, type_infer_order M.
  Proof. exact (proj1 syn_orders_all). Qed.

  Lemma type_check_order_all : forall M, type_check_order M.
  Proof. intros; constructor; apply type_infer_order_all. Qed.

  Lemma modexp_order_all : forall H, modexp_order H.
  Proof. exact (proj1 (proj2 syn_orders_all)). Qed.

  Lemma unit_order_all : forall U, unit_order U.
  Proof. exact (proj1 (proj2 (proj2 (proj2 syn_orders_all)))). Qed.

  Lemma body_order_all : forall Φ, body_order Φ.
  Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 syn_orders_all)))))). Qed.

  Lemma ext_order_all : forall Ψ, ext_order Ψ.
  Proof.
    intros; apply ext_order_of_forall, Forall_forall; intros.
    destruct syn_orders_all as (_ & _ & _ & _ & _ & _ & _ & Hc); apply Hc.
  Qed.

  (** [LevelSort] is of no type ([level_sort_untyped]). *)
  Lemma alg_level_sort_no_infer : forall G A, ⊢ G -> ~ G ⊢a LevelSort ⟹ A.
  Proof. intros * HG H; exact (level_sort_untyped (alg_type_infer_sound H HG)). Qed.

  (** A closed body is a filed module's or an open frame's: no unit the
      checker is given is one. *)
  Lemma alg_unit_closed_no : forall G Δ Φ, ~ G ⊢aᵘ gu_body Δ Φ.
  Proof. intros * H; inversion H. Qed.

End type_check.
End Fixed_GCtx.

(** ** The Computations, Through a Fast Context

    The checker's helpers that run: they take the fast context [F], and
    the judgments are those of the global context it stands for
    ([fc_gctx F]). *)
Section Fast.
Variable F : FCtx.
#[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.

Section lookup.
  #[local]
  Ltac impl_obligation_tac1 :=
    match goal with
    | |- ~ _ => intro
    | H: ⊢ _ :: _ |- _ => inversion_clear H
    | H: ⋅ ∋ #_ : _ |- _ => inversion_clear H
    | H: _ :: _ ∋ #(S _) : _ |- _ => inversion_clear H
    | H: ce_mod _ :: _ ∋ #0 : _ |- _ => inversion H
    end.

  #[local]
  Ltac impl_obligation_tac :=
    intros;
    repeat impl_obligation_tac1;
    intuition (mauto 4).

  (** The type of a variable *)
  #[tactic="impl_obligation_tac",derive(equations=no,eliminator=no)]
  Equations lookup G (HG : ⊢ G) x : { A | G ∋ #x : A } + { forall A, ~ G ∋ #x : A } :=
  | cons e G, HG, x with x => {
    | 0 with e => {
      | ce_ass κ A => pureo (exist _ A[↑]ʷ _)
      | ce_def A M => pureo (exist _ A[↑]ʷ _)
      | ce_mod _ => inright _
      | ce_dm A M U => pureo (exist _ A[↑]ʷ _) }
    | S x' =>
        let*o (exist _ B _) := lookup G _ x' while _ in
        pureo (exist _ B[↑]ʷ _)
    }
  | ⋅, HG, x => inright _.
End lookup.

(** *** Deciding What Module Expressions Denote

    What a module expression denotes is computed by [mdenote_impl], at
    the order a well-formed module expression, or a selection from one,
    has ([mdenote_order_of_wf], [mdenote_order_mem_of_wf]); a path has one
    outright. *)

Definition mdenote_dec (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) Γ H (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :
    { R : fmdesc | mdenote gc_deps gc_stack Γ H (decode_desc R) } + { forall R, ~ mdenote gc_deps gc_stack Γ H R } :=
  mdenote_impl F Hg Γ H (mdenote_order_of_wf _ _ Hg _ _ _ HH).

Definition mem_denote_dec (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) Γ H y (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :
    { R : fmdesc | mdenote gc_deps gc_stack Γ (me_mem H y) (decode_desc R) } + { forall R, ~ mdenote gc_deps gc_stack Γ (me_mem H y) R } :=
  mdenote_impl F Hg Γ (me_mem H y) (mdenote_order_mem_of_wf _ _ Hg _ _ _ y HH).

Definition path_denote_dec (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) Γ fp :
    { R : fmdesc | mdenote gc_deps gc_stack Γ (me_unit fp) (decode_desc R) } + { forall R, ~ mdenote gc_deps gc_stack Γ (me_unit fp) R } :=
  mdenote_impl F Hg Γ (me_unit fp) (mdenote_order_path _ _ Γ fp).

(** What a local open of a module generates. *)
Definition items_gen_dec (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) Γ H its (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) :
    { gs | items_gen gc_deps gc_stack Γ H its gs } + { forall gs, ~ items_gen gc_deps gc_stack Γ H its gs } :=
  items_gen_impl F Hg Γ H its (items_gen_order_of_wf _ _ Hg _ _ _ its HH).

Extraction Inline mdenote_dec mem_denote_dec path_denote_dec items_gen_dec.

(** *** The Initial Environment, Computed *)

(** The initial environment of a context, from scratch. *)
Definition checker_env_of G (HG : ⊢ G) : checker_env G :=
  initial_env_impl F G (checker_env_order_of_wf G HG).

(** The initial environment of an extended context, from that of the
    context: one entry more, by its rule of [initial_env]. *)
Definition checker_env_ass G (P : checker_env G) κ A (HGA : ⊢ G ▹{κ} A) : checker_env (G ▹{κ} A) :=
  let (p, Hp) := P in
  let (a, Ha) := fast_eval_exp_impl F A p (proj2 Hp) (checker_env_order_ass G κ A _ HGA (proj1 Hp)) in
  exist _ (fextend_env p (fd_neut a (fd_var (List.length G))) (fentry_type_value a)) (fast_env_ass _ _ _ _ _ _ _ Hp Ha).

(** The same for a definition entry, by the kind of its type: its body's
    value, or the body kept at a proposition. *)
Definition checker_env_def G (P : checker_env G) A M (HGA : ⊢ G ▸ A ≔ M) : checker_env (G ▸ A ≔ M) :=
  let (p, Hp) := P in
  let (a, Ha) := fast_eval_exp_impl F A p (proj2 Hp) (checker_env_order_def_typ G A M _ HGA (proj1 Hp)) in
  match abs_kind_eq_dec (fdomain_kind a) ak_propositional with
  | left Hk => exist _ (fextend_env p (fd_proof M p) (fentry_type_value a)) (fast_env_def_proof _ _ _ _ _ _ _ Hp Ha Hk)
  | right Hk =>
      let Hk' := evaluated_kind_of_not_propositional _ Hk in
      let (m, Hm) := fast_eval_exp_impl F M p (proj2 Hp)
                       (checker_env_order_def G A M _ _ HGA (proj1 Hp) (proj1 Ha)
                          (eq_rect_r evaluated_kind Hk' (fdomain_kind_erase a))) in
      exist _ (fextend_env p m (fentry_type_value a)) (fast_env_def _ _ _ _ _ _ _ _ Hp Ha Hk' Hm)
  end.

(** The same for a module slot: the closure of its unit. *)
Definition checker_env_mod G (P : checker_env G) U (HGU : ⊢ G ▹ₘ U) : checker_env (G ▹ₘ U) :=
  let (p, Hp) := P in
  let (h, Hh) := fast_eval_modexp_impl F (me_lit U) p (proj2 Hp) (checker_env_order_mod G U _ HGU (proj1 Hp)) in
  exist _ (fextend_env_mod p h U) (fast_env_mod _ _ _ _ _ _ Hp Hh).

(** The same for a definition with a module part: the value of its term
    part's body, at its type, and the closure of its unit, side by side. *)
Definition checker_env_dm G (P : checker_env G) A M U (HG : ⊢ G ▸ₘ A ≔ M ‖ U) : checker_env (G ▸ₘ A ≔ M ‖ U) :=
  let (p, Hp) := P in
  let Ho := checker_env_order_dm G A M U _ HG (proj1 Hp) in
  let (a, Ha) := fast_eval_exp_impl F A p (proj2 Hp) (proj1 Ho) in
  let (m, Hm) := fast_eval_exp_impl F M p (proj2 Hp) (proj1 (proj2 Ho)) in
  let (h, Hh) := fast_eval_modexp_impl F (me_lit U) p (proj2 Hp) (proj2 (proj2 Ho)) in
  exist _ (fextend_env_dm p m (fentry_type_value a) h U) (fast_env_dm _ _ _ _ _ _ _ _ _ _ Hp Ha Hm Hh).

(** The kind of a type, read off its fast value at the environment the
    checker carries ([nbe_ty_kind]). *)
Definition checker_kind G (P : checker_env G) T (HT : G ⊢ᵗ T) : { κ | nbe_ty_kind G T κ } :=
  let (p, Hp) := P in
  let (a, Ha) := fast_eval_exp_impl F T p (proj2 Hp) (checker_env_order_type G T _ HT (proj1 Hp)) in
  exist _ (fdomain_kind a) (ex_intro _ _ (ex_intro _ _ (conj (proj1 Hp) (conj (proj1 Ha) (fdomain_kind_erase a))))).

(** The initial environment of an extension [Ψ ++ G], from that of [G]:
    one entry more per entry of [Ψ], rather than all of [G]'s again. *)
Fixpoint checker_env_ext G (P : checker_env G) (Ψ : ctx) {struct Ψ} : ⊢ Ψ ++ G -> checker_env (Ψ ++ G) :=
  match Ψ as Ψ0 return ⊢ Ψ0 ++ G -> checker_env (Ψ0 ++ G) with
  | nil => fun _ => P
  | ce_ass κ A :: Ψ' => fun H => checker_env_ass (Ψ' ++ G) (checker_env_ext G P Ψ' (ctx_decomp_tail H)) κ A H
  | ce_def A M :: Ψ' => fun H => checker_env_def (Ψ' ++ G) (checker_env_ext G P Ψ' (ctx_decomp_tail H)) A M H
  | ce_mod U :: Ψ' => fun H => checker_env_mod (Ψ' ++ G) (checker_env_ext G P Ψ' (ctx_decomp_tail H)) U H
  | ce_dm A M U :: Ψ' => fun H => checker_env_dm (Ψ' ++ G) (checker_env_ext G P Ψ' (ctx_decomp_tail H)) A M U H
  end.
End Fast.
