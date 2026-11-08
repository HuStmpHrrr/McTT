(** * The Fast Evaluation Simulates the Reference One

    [Extraction.FastEval] skips the recursive result of a recursive
    argument of a constructor when the eliminator's branch does not read
    it.  Its values then differ from the reference ones only in entries of
    environments that nothing reads:

    - [domain_simulation a a'], between a reference value [a] and a fast one [a'], is
      equality of the two up to the entries of closures' environments at
      which the closure's body is fresh ([exp_fresh]);
    - [env_agree P ρ ρ'] is agreement of two environments at the entries
      [P] selects; a term is evaluated in environments that agree where the
      term may read, [fun x => ~ exp_fresh x M].

    Evaluation, from environments that agree where the term may read, gives
    values related by [domain_simulation] ([fast_eval_sim]), and readback of related values
    gives the same normal form ([fast_read_sim]).  So both evaluations normalize
    alike, which is what [Extraction.NbE] needs. *)
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Records Fresh NfRename.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import Domain Evaluation Readback Avoid.
From Mctt.Core.Semantic.Kinds Require Import Kinds.
From Mctt.Extraction Require Import FastEval FastRead FastDomain.
Import Domain_Notations.
#[local] Open Scope list_scope.

#[local] Open Scope bool_scope.

(** The fast relations here run with the skip on. *)
#[local] Existing Instance skip_on_mode.

(** ** The Relation *)

(** The components of a shape, each under the domains before it, are fresh
    at [k]. *)
Fixpoint ptyp_fresh (k : nat) (t : ptyp) : Prop :=
  match t with
  | pt_pi B t => exp_fresh k B /\ ptyp_fresh (S k) t
  | pt_self _ Ps => Forall (exp_fresh k) Ps
  end.

(** The relation is over a global context: the family of the types of a
    function shape's recursive result reads the motives of the members its
    leaf paths end in, which the group's declaration fixes
    ([ends_agree]). *)
Section Sim.
  Variables (Θ : gdeps) (Ξ : gstack).

(** [domain_simulation a a']: the reference value [a] and the fast value [a'] are equal
    up to the entries of closures' environments that the closures' bodies
    do not read; mutually, for neutrals, normal values, module values, level
    atoms, lists of values and environment entries. *)
Inductive domain_simulation : domain -> domain -> Prop :=
(** A [Π] at kinds, the same on both sides: related domains, environments
    agreeing where the codomain reads *)
| domain_simulation_pi : forall κd κc a a' (ρ ρ' : env) B,
    domain_simulation a a' ->
    (forall x, ~ exp_fresh (S x) B -> dentry_simulation (env_entry ρ x) (env_entry ρ' x)) ->
    domain_simulation (d_pi κd κc a ρ B) (d_pi κd κc a' ρ' B)
(** A large universe *)
| domain_simulation_univ : forall i, domain_simulation 𝕌ω@i 𝕌ω@i
(** A small universe at related levels *)
| domain_simulation_suniv : forall l l', domain_simulation l l' -> domain_simulation 𝕌@l 𝕌@l'
(** A type of levels *)
| domain_simulation_level : forall n, domain_simulation (Levelᵈ@n) (Levelᵈ@n)
(** The sort of the types of levels *)
| domain_simulation_level_sort : domain_simulation LevelSortᵈ LevelSortᵈ
(** A level of related atoms *)
| domain_simulation_lvl : forall c xs xs', level_atoms_simulation xs xs' -> domain_simulation (lvᵈ c xs) (lvᵈ c xs')
(** The universe of propositions *)
| domain_simulation_prop : domain_simulation Propᵈ Propᵈ
(** The true proposition *)
| domain_simulation_True : domain_simulation ⊤ᵈ ⊤ᵈ
(** Two kept proofs.  A proof is never evaluated nor taken apart, and
    with the skip on it reads back as its term ([fast_read_proof_kept_skipping]),
    which the outputs compare up to proofs only: any two are related. *)
| domain_simulation_proof : forall M ρ M' ρ', domain_simulation ⋆ᵈ⟨M, ρ⟩ ⋆ᵈ⟨M', ρ'⟩
(** The false proposition *)
| domain_simulation_False : domain_simulation ⊥ᵈ ⊥ᵈ
(** A dependent conjunction: related first components, environments
    agreeing where the second reads *)
| domain_simulation_and : forall p p' (ρ ρ' : env) Q,
    domain_simulation p p' ->
    (forall x, ~ exp_fresh (S x) Q -> dentry_simulation (env_entry ρ x) (env_entry ρ' x)) ->
    domain_simulation (Σₚᵈ p ρ Q) (Σₚᵈ p' ρ' Q)
(** A λ: related domains, environments agreeing where the body reads *)
| domain_simulation_fn : forall a a' (ρ ρ' : env) M,
    domain_simulation a a' ->
    (forall x, ~ exp_fresh (S x) M -> dentry_simulation (env_entry ρ x) (env_entry ρ' x)) ->
    domain_simulation (λᵈ a ρ M) (λᵈ a' ρ' M)
(** A neutral at related types *)
| domain_simulation_neut : forall a a' m m', domain_simulation a a' -> domain_ne_simulation m m' -> domain_simulation (⇑ a m) (⇑ a' m')
(** A member of related module values *)
| domain_simulation_member : forall h h' ch, dmod_simulation h h' -> domain_simulation (d_member h ch) (d_member h' ch)
(** A type former at related arguments *)
| domain_simulation_indty : forall p k args args', domain_list_simulation args args' -> domain_simulation (d_ind p k args) (d_ind p k args')
(** A constructor at related arguments *)
| domain_simulation_con : forall p k c args args', domain_list_simulation args args' -> domain_simulation (d_con p k c args) (d_con p k c args')
(** A recursive result of a function shape: the environments agree where
    the blocks' motives and branches may read, as [domain_ne_simulation_elim] *)
| domain_simulation_ihfn : forall (ρ ρ' : env) Bks p ups ups' t i f f',
    (forall b, In b Bks ->
       (forall x, ~ exp_fresh (eb_binder_count b + x) (eb_motive b) -> dentry_simulation (env_entry ρ x) (env_entry ρ' x)) /\
       (forall c n B, In (c, n, B) (eb_brs b) -> forall x, ~ exp_fresh (n + x) B -> dentry_simulation (env_entry ρ x) (env_entry ρ' x))) ->
    domain_list_simulation ups ups' ->
    domain_simulation f f' -> domain_simulation (d_ihfn ρ Bks p ups t i f) (d_ihfn ρ' Bks p ups' t i f')
(** The family of the type of an argument of a function shape: where the
    rest of the shape may read under the domain the family binds *)
| domain_simulation_shfam : forall p ups ups' (ρ ρ' : env) B t,
    domain_list_simulation ups ups' ->
    (forall x, ~ ptyp_fresh x (pt_pi B t) -> dentry_simulation (env_entry ρ x) (env_entry ρ' x)) ->
    domain_simulation (d_shfam p ups ρ B t) (d_shfam p ups' ρ' B t)
(** The family of the type of a recursive result: where the motives of the
    members the shape's leaf paths end in may read ([ends_agree]), at
    related uniform parameters, and where the rest of the shape may read *)
| domain_simulation_ihfam : forall (ρm ρm' : env) As p ups ups' (ρ ρ' : env) B t i f f',
    ends_agree p As ρm ρm' t ->
    domain_list_simulation ups ups' ->
    (forall x, ~ ptyp_fresh x (pt_pi B t) -> dentry_simulation (env_entry ρ x) (env_entry ρ' x)) ->
    domain_simulation f f' -> domain_simulation (d_ihfam ρm As p ups ρ B t i f) (d_ihfam ρm' As p ups' ρ' B t i f')
(** A record's type former at related arguments *)
| domain_simulation_record : forall p args args', domain_list_simulation args args' -> domain_simulation (d_record p args) (d_record p args')
(** A tuple of related fields *)
| domain_simulation_tuple : forall vs vs', domain_fields_simulation vs vs' -> domain_simulation (d_tuple vs) (d_tuple vs')
with domain_ne_simulation : domain_ne -> domain_ne -> Prop :=
(** A variable *)
| domain_ne_simulation_var : forall x, domain_ne_simulation (#ᵈ x) (#ᵈ x)
(** An application *)
| domain_ne_simulation_app : forall m m' n n', domain_ne_simulation m m' -> domain_nf_simulation n n' -> domain_ne_simulation (m $ᵈ n) (m' $ᵈ n')
(** A stuck [efq], at related types, of related proofs *)
| domain_ne_simulation_absurd : forall c c' d d',
    domain_simulation c c' -> domain_simulation d d' ->
    domain_ne_simulation (d_absurd c d) (d_absurd c' d')
(** A global *)
| domain_ne_simulation_glob : forall p, domain_ne_simulation (d_glob p) (d_glob p)
(** A stuck eliminator: the environments agree where the blocks' motives
    and branches may read, under their binders. *)
| domain_ne_simulation_elim : forall (ρ ρ' : env) Bks p ups ups' j args args' m m',
    (forall b, In b Bks ->
       (forall x, ~ exp_fresh (eb_binder_count b + x) (eb_motive b) -> dentry_simulation (env_entry ρ x) (env_entry ρ' x)) /\
       (forall c n B, In (c, n, B) (eb_brs b) -> forall x, ~ exp_fresh (n + x) B -> dentry_simulation (env_entry ρ x) (env_entry ρ' x))) ->
    domain_list_simulation ups ups' -> domain_list_simulation args args' -> domain_ne_simulation m m' ->
    domain_ne_simulation (d_elim ρ Bks p ups j args m) (d_elim ρ' Bks p ups' j args' m')
(** The field of a neutral *)
| domain_ne_simulation_proj : forall f m m', domain_ne_simulation m m' -> domain_ne_simulation (d_proj f m) (d_proj f m')
with domain_nf_simulation : domain_nf -> domain_nf -> Prop :=
(** A value at a type, both related *)
| domain_nf_simulation_dom : forall a a' m m', domain_simulation a a' -> domain_simulation m m' -> domain_nf_simulation (⇓ a m) (⇓ a' m')
with dmod_simulation : dmod -> dmod -> Prop :=
(** A global module at related arguments *)
| dmod_simulation_global : forall p args args', domain_list_simulation args args' -> dmod_simulation (dm_global p args) (dm_global p args')
(** A closure: the environments agree where the unit may read. *)
| dmod_simulation_local : forall Δ D (ρ ρ' : env),
    (forall x, ~ gunit_fresh x (gu_mk Δ D) -> dentry_simulation (env_entry ρ x) (env_entry ρ' x)) ->
    dmod_simulation (dm_local Δ D ρ) (dm_local Δ D ρ')
(** A member closure of related module values *)
| dmod_simulation_member : forall h h' ch, dmod_simulation h h' -> dmod_simulation (dm_member h ch) (dm_member h' ch)
with level_atoms_simulation : list (nat * nat * domain_ne) -> list (nat * nat * domain_ne) -> Prop :=
(** No atom *)
| level_atoms_simulation_nil : level_atoms_simulation nil nil
(** Related first atoms, then the rest *)
| level_atoms_simulation_cons : forall k n m m' xs xs', domain_ne_simulation m m' -> level_atoms_simulation xs xs' -> level_atoms_simulation ((k, n, m) :: xs) ((k, n, m') :: xs')
with domain_list_simulation : list domain -> list domain -> Prop :=
(** No value *)
| domain_list_simulation_nil : domain_list_simulation nil nil
(** Related first values, then the rest *)
| domain_list_simulation_cons : forall a a' args args', domain_simulation a a' -> domain_list_simulation args args' -> domain_list_simulation (a :: args) (a' :: args')
(** Named fields, the same names at related values *)
with domain_fields_simulation : list (string * domain) -> list (string * domain) -> Prop :=
(** No field *)
| domain_fields_simulation_nil : domain_fields_simulation nil nil
(** A field of the same name at related values, then the rest *)
| domain_fields_simulation_cons : forall f a a' vs vs', domain_simulation a a' -> domain_fields_simulation vs vs' -> domain_fields_simulation ((f, a) :: vs) ((f, a') :: vs')
with dentry_simulation : dentry -> dentry -> Prop :=
(** Related terms, at any types: an entry's type is read only by the
    definitions around a kept proof ([read_entry]), which the skip on does
    not read ([fast_read_proof_kept_skipping]) *)
| dentry_simulation_term : forall d d' t t', domain_simulation d d' -> dentry_simulation (de_term d t) (de_term d' t')
(** Related modules at one unit *)
| dentry_simulation_mod : forall h h' U, dmod_simulation h h' -> dentry_simulation (de_mod h U) (de_mod h' U)
(** Related terms with related module parts, at one unit *)
| dentry_simulation_dm : forall d d' t t' h h' U, domain_simulation d d' -> dmod_simulation h h' ->
    dentry_simulation (de_dm d t h U) (de_dm d' t' h' U)
(** [ends_agree p As ρm ρm' t]: the motives [As] in [ρm] and [ρm'] agree
    where the motive of each member a leaf path of the shape [t] ends in
    may read, under that path's end's parameters and the argument; at a
    record view, along its recursive fields, as [Core.Semantic.Avoid]'s
    [ends_fresh] *)
with ends_agree : qname -> list exp -> env -> env -> ptyp -> Prop :=
(** The end, at a member with a block: its motive *)
| ends_agree_self : forall p As ρm ρm' D j Mj Ps,
    ind_lookup Θ Ξ p = Some D -> ind_member D j = Some Mj -> im_is_rview Mj = false ->
    (forall x, ~ exp_fresh (S (List.length Ps) + x) (List.nth j As a_prop) -> dentry_simulation (env_entry ρm x) (env_entry ρm' x)) ->
    ends_agree p As ρm ρm' (pt_self j Ps)
(** The end, at a record view: along each of its recursive fields *)
| ends_agree_rview : forall p As ρm ρm' D j Mj qr Is fl Ps,
    ind_lookup Θ Ξ p = Some D -> ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
    (forall c gs gs1 t gs2, im_cons Mj = (c, gs) :: nil -> gs = gs1 ++ ca_rec t :: gs2 -> ends_agree p As ρm ρm' t) ->
    ends_agree p As ρm ρm' (pt_self j Ps)
(** A domain: the rest *)
| ends_agree_pi : forall p As ρm ρm' B t,
    ends_agree p As ρm ρm' t -> ends_agree p As ρm ρm' (pt_pi B t).

#[local]
Hint Constructors domain_simulation domain_ne_simulation domain_nf_simulation dmod_simulation level_atoms_simulation domain_list_simulation domain_fields_simulation dentry_simulation ends_agree : mctt.

(** Agreement of two environments at the entries [P] selects. *)
Definition env_agree (P : nat -> Prop) (ρ ρ' : env) : Prop :=
  forall x, P x -> dentry_simulation (env_entry ρ x) (env_entry ρ' x).

(** Agreement of two environments where the blocks of an eliminator may
    read: each motive under its binders, and each branch under its own.
    (The annotations are never evaluated.)  It is the premise of [domain_ne_simulation_elim]
    and [domain_simulation_ihfn]. *)
Definition blocks_agree (Bks : list eblock) (ρ ρ' : env) : Prop :=
  forall b, In b Bks ->
    env_agree (fun x => ~ exp_fresh (eb_binder_count b + x) (eb_motive b)) ρ ρ' /\
    (forall c n B, In (c, n, B) (eb_brs b) -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ').

(** ** Environments *)

Lemma env_agree_mono : forall P Q ρ ρ', env_agree P ρ ρ' -> (forall x, Q x -> P x) -> env_agree Q ρ ρ'.
Proof. intros * H HQ x Hx; apply H, HQ, Hx. Qed.

Lemma env_agree_nil : forall P, env_agree P nil nil.
Proof. intros P x _; induction x; cbn; [ repeat constructor | exact IHx ]. Qed.

Lemma env_agree_cons : forall P Q e e' ρ ρ',
    env_agree P ρ ρ' -> dentry_simulation e e' -> (forall y, Q (S y) -> P y) -> env_agree Q (e :: ρ) (e' :: ρ').
Proof. intros * H He HQ [| y] Hy; cbn; [ exact He | apply H, HQ, Hy ]. Qed.

Lemma domain_list_simulation_length : forall args args', domain_list_simulation args args' -> List.length args = List.length args'.
Proof. induction 1; cbn; congruence. Qed.

(** Values extended by, at any types, related one for one *)
Definition typed_simulation (vts vts' : list (domain * entry_type)) : Prop :=
  domain_list_simulation (List.map fst vts) (List.map fst vts').

Lemma env_agree_args : forall vts vts' P Q ρ ρ',
    env_agree P ρ ρ' -> typed_simulation vts vts' ->
    (forall y, Q (List.length vts + y) -> P y) ->
    env_agree Q (env_extend_typed ρ vts) (env_extend_typed ρ' vts').
Proof.
  unfold typed_simulation, env_extend_typed.
  induction vts as [| [a t] vts IH]; intros [| [a' t'] vts'] * Hρ Ha HQ; inversion Ha; subst; cbn.
  - eapply env_agree_mono; [ exact Hρ | intros y Hy; apply HQ, Hy ].
  - eapply IH; [ eapply env_agree_cons with (Q := fun y => match y with 0 => True | S y => P y end);
                 [ exact Hρ | constructor; assumption | intros; assumption ]
               | eassumption |].
    intros [| y] Hy; [ exact I |]; apply HQ.
    replace (List.length vts + S y) with (S (List.length vts) + y) in Hy by lia; exact Hy.
Qed.

Lemma env_agree_var : forall P ρ ρ' x, env_agree P ρ ρ' -> P x -> domain_simulation (ρ x) (ρ' x).
Proof. intros * H Hx; unfold env_var; destruct (H x Hx); [ assumption | constructor | assumption ]. Qed.

Lemma env_agree_mod : forall P ρ ρ' x, env_agree P ρ ρ' -> P x -> dmod_simulation (env_mod ρ x) (env_mod ρ' x).
Proof. intros * H Hx; unfold env_mod; destruct (H x Hx); [ repeat constructor | assumption | assumption ]. Qed.

(** ** Relevance

    Related values have the same head, so evaluation reads the same sorts
    off them: of a type ([domain_relevance]), and of the next argument of
    a function ([arg_relevance]). *)

(** A global module lacks no parameter at related arguments alike. *)
Lemma module_saturated_sim : forall p args args', module_saturated Θ Ξ p args -> domain_list_simulation args args' ->
    module_saturated Θ Ξ p args'.
Proof. intros * H Ha T Φ Hl; rewrite <- (domain_list_simulation_length _ _ Ha); exact (H _ _ Hl). Qed.

(** Related types are of the same kind. *)
Lemma domain_kind_sim : forall a a', domain_simulation a a' -> domain_kind a = domain_kind a'.
Proof.
  intros * H; destruct H; try reflexivity.
  match goal with H : domain_simulation _ _ |- _ => destruct H; reflexivity end.
Qed.

(** Related module values take parameters of the same kind. *)
Lemma dmod_param_kind_sim : forall h h', dmod_simulation h h' -> dmod_param_kind Θ Ξ h = dmod_param_kind Θ Ξ h'.
Proof.
  induction 1; cbn [dmod_param_kind]; try reflexivity; [| assumption ].
  rewrite (domain_list_simulation_length _ _ ltac:(eassumption)); reflexivity.
Qed.

(** Related functions take arguments of the same kind. *)
Lemma arg_kind_sim : forall f f', domain_simulation f f' -> arg_kind Θ Ξ f = arg_kind Θ Ξ f'.
Proof.
  intros * H; destruct H; cbn [arg_kind]; try reflexivity.
  all: try (apply domain_kind_sim; assumption).
  all: try (match goal with H : domain_simulation _ _ |- _ => destruct H; try reflexivity end;
            apply domain_kind_sim; assumption).
  all: try (apply dmod_param_kind_sim; assumption).
  all: rewrite (domain_list_simulation_length _ _ ltac:(eassumption)); reflexivity.
Qed.

(** ** Levels *)

Lemma domain_level_sort_sim : forall a a', domain_simulation a a' -> domain_level_sort a = domain_level_sort a'.
Proof. intros * H; destruct H; reflexivity. Qed.

Lemma domain_level_const_sim : forall d d', domain_simulation d d' -> domain_level_const d = domain_level_const d'.
Proof. intros * H; destruct H; reflexivity. Qed.

Lemma domain_level_atoms_sim : forall d d', domain_simulation d d' -> level_atoms_simulation (domain_level_atoms d) (domain_level_atoms d').
Proof.
  intros * H; destruct H; cbn; try constructor; try assumption.
  erewrite domain_level_sort_sim by eassumption; repeat constructor; assumption.
Qed.

Lemma level_atoms_simulation_suc : forall xs xs', level_atoms_simulation xs xs' ->
    level_atoms_simulation (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs)
            (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs').
Proof. induction 1; cbn; constructor; assumption. Qed.

Lemma level_atoms_simulation_app : forall xs xs' ys ys', level_atoms_simulation xs xs' -> level_atoms_simulation ys ys' -> level_atoms_simulation (xs ++ ys) (xs' ++ ys').
Proof. induction 1; intros; cbn; [ assumption | constructor; auto ]. Qed.

Lemma domain_simulation_lvl_suc : forall d d', domain_simulation d d' -> domain_simulation (domain_level_suc d) (domain_level_suc d').
Proof.
  intros * H; unfold domain_level_suc; rewrite (domain_level_const_sim _ _ H).
  constructor; apply level_atoms_simulation_suc, domain_level_atoms_sim, H.
Qed.

Lemma domain_simulation_lvl_max : forall d d' e e', domain_simulation d d' -> domain_simulation e e' -> domain_simulation (domain_level_max d e) (domain_level_max d' e').
Proof.
  intros * Hd He; unfold domain_level_max; rewrite (domain_level_const_sim _ _ Hd), (domain_level_const_sim _ _ He).
  constructor; apply level_atoms_simulation_app; apply domain_level_atoms_sim; assumption.
Qed.

Lemma domain_list_simulation_snoc : forall args args' n n', domain_list_simulation args args' -> domain_simulation n n' ->
    domain_list_simulation (args ++ n :: nil) (args' ++ n' :: nil).
Proof. induction 1; intros; cbn; repeat constructor; auto. Qed.

Lemma domain_list_simulation_app : forall args args' bs bs', domain_list_simulation args args' -> domain_list_simulation bs bs' ->
    domain_list_simulation (args ++ bs) (args' ++ bs').
Proof. induction 1; intros; cbn; [ assumption | constructor; auto ]. Qed.

Lemma domain_list_simulation_firstn : forall n args args', domain_list_simulation args args' -> domain_list_simulation (firstn n args) (firstn n args').
Proof. intros n args args' H; revert n; induction H; intros [| n]; cbn; constructor; auto. Qed.

Lemma domain_list_simulation_skipn : forall n args args', domain_list_simulation args args' -> domain_list_simulation (skipn n args) (skipn n args').
Proof. intros n args args' H; revert n; induction H; intros [| n]; cbn; try constructor; auto. Qed.

(** The fields of a tuple, named alike at related values. *)
Lemma domain_fields_simulation_combine : forall fs vs vs', domain_list_simulation vs vs' -> domain_fields_simulation (List.combine fs vs) (List.combine fs vs').
Proof. induction fs as [| f fs IH]; intros vs vs' H; destruct H; cbn; constructor; auto. Qed.

(** A field of related tuples: related values. *)
Lemma field_lookup_sim : forall vs vs' f r, domain_fields_simulation vs vs' -> field_lookup vs f = Some r ->
    exists r', field_lookup vs' f = Some r' /\ domain_simulation r r'.
Proof.
  induction 1 as [| g a a' vs vs' Ha Hvs IH]; cbn; intros Hl; [ discriminate |].
  destruct (String.eqb f g); [ injection Hl as <-; eauto | auto ].
Qed.

(** An entry of related lists: related values. *)
Lemma domain_list_simulation_nth_error : forall args args' k r, domain_list_simulation args args' -> List.nth_error args k = Some r ->
    exists r', List.nth_error args' k = Some r' /\ domain_simulation r r'.
Proof.
  intros * H; revert k; induction H as [| a a' args args' Ha Hargs IH]; intros [| k]; cbn; intros Hk;
    try discriminate; [ injection Hk as <-; eauto | auto ].
Qed.

(** Agreement everywhere: the environments of the telescopes of a
    declaration, whose types are read at every entry. *)
Lemma env_agree_all_args : forall vts vts' ρ ρ',
    env_agree (fun _ => True) ρ ρ' -> typed_simulation vts vts' ->
    env_agree (fun _ => True) (env_extend_typed ρ vts) (env_extend_typed ρ' vts').
Proof. intros * Hρ Ha; eapply env_agree_args; [ exact Hρ | exact Ha | intros; exact I ]. Qed.

Lemma env_agree_all_cons : forall ρ ρ' d d' t t',
    env_agree (fun _ => True) ρ ρ' -> domain_simulation d d' -> env_agree (fun _ => True) (ρ ↦ d ⦂ t) (ρ' ↦ d' ⦂ t').
Proof. intros * Hρ Hd; eapply env_agree_cons; [ exact Hρ | constructor; exact Hd | intros; exact I ]. Qed.

(** An environment of closed terms' values only: it agrees wherever. *)
Lemma env_agree_nil_args : forall P vts vts', typed_simulation vts vts' ->
    env_agree P (env_extend_typed nil vts) (env_extend_typed nil vts').
Proof.
  intros * Ha; eapply env_agree_mono; [ apply env_agree_all_args; [ apply env_agree_nil | exact Ha ] | intros; exact I ].
Qed.

(** The environment of a telescope's values over nothing, at related
    values: it agrees wherever. *)
Lemma env_agree_tele_nil : forall P T vs vs', domain_list_simulation vs vs' ->
    env_agree P (env_tele nil T vs) (env_tele nil T vs').
Proof. intros * H; unfold env_tele; apply env_agree_nil_args; unfold typed_simulation; rewrite !tele_entries_values; exact H. Qed.

(** The environment of a telescope's values over environments related
    everywhere, at related values: it agrees everywhere. *)
Lemma env_agree_tele : forall ρ ρ' T vs vs', env_agree (fun _ => True) ρ ρ' -> domain_list_simulation vs vs' ->
    env_agree (fun _ => True) (env_tele ρ T vs) (env_tele ρ' T vs').
Proof.
  intros * Hρ H; unfold env_tele; eapply env_agree_args; [ exact Hρ | | intros; exact I ].
  unfold typed_simulation; rewrite !tele_entries_values; exact H.
Qed.

Lemma env_agree_decl_env : forall P D ups ups', domain_list_simulation ups ups' ->
    env_agree P (decl_env D ups) (decl_env D ups').
Proof. intros; apply env_agree_tele_nil; assumption. Qed.

(** The term an entry defines is fresh where the entry is. *)
Lemma gentry_fresh_tm : forall k E A M, entry_tm E = Some (A, M) -> gentry_fresh k E -> exp_fresh k M.
Proof.
  intros * He Hf; destruct E as [b pv r A0 [M0 |] | | | |]; cbn in He; try discriminate;
    injection He as <- <-; cbn in Hf; tauto.
Qed.

(** The unit an entry holds is fresh where the entry is. *)
Lemma gentry_fresh_unit : forall k E U, entry_unit E = Some U -> gentry_fresh k E -> gunit_fresh k U.
Proof. intros * He Hf; destruct E; cbn in He; try discriminate; injection He as <-; cbn in Hf; tauto. Qed.

(** The environment of a closure under its [n] binders: the [n] entries are
    related, and the rest agree where the body may read. *)
Lemma env_agree_binders : forall n B vts vts' ρ ρ',
    env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ' -> typed_simulation vts vts' -> List.length vts = n ->
    env_agree (fun x => ~ exp_fresh x B) (env_extend_typed ρ vts) (env_extend_typed ρ' vts').
Proof. intros * Hρ Ha Hl; eapply env_agree_args; [ exact Hρ | exact Ha |]; intros y Hy; rewrite Hl in Hy; exact Hy. Qed.

(** Two lists of values related at the entries [P] selects, once they
    extend an environment: the entry of [a] in
    [env_extend_typed ρ ((a, t) :: l)] is [List.length l]. *)
Inductive domain_list_simulation_at (P : nat -> Prop) : list domain -> list domain -> Prop :=
(** No value *)
| domain_list_simulation_at_nil : domain_list_simulation_at P nil nil
(** The first values related if [P] selects their entry, then the rest *)
| domain_list_simulation_at_cons : forall a a' l l', (P (List.length l) -> domain_simulation a a') -> domain_list_simulation_at P l l' ->
    domain_list_simulation_at P (a :: l) (a' :: l').

#[local]
Hint Constructors domain_list_simulation_at : mctt.

Lemma domain_list_simulation_at_app : forall P l1 l1' l2 l2', domain_list_simulation l1 l1' -> domain_list_simulation_at P l2 l2' ->
    domain_list_simulation_at P (l1 ++ l2) (l1' ++ l2').
Proof. induction 1; intros; cbn; [ assumption | constructor; auto ]. Qed.

Lemma domain_list_simulation_at_length : forall P l l', domain_list_simulation_at P l l' -> List.length l = List.length l'.
Proof. induction 1; cbn; congruence. Qed.

Lemma env_agree_args_at : forall P Q vts vts' ρ ρ',
    env_agree P ρ ρ' -> domain_list_simulation_at Q (List.map fst vts) (List.map fst vts') ->
    (forall y, Q (List.length vts + y) -> P y) ->
    env_agree Q (env_extend_typed ρ vts) (env_extend_typed ρ' vts').
Proof.
  unfold env_extend_typed; intros P Q vts; revert P.
  induction vts as [| [a t] vts IH]; intros P [| [a' t'] vts'] * Hρ Ha HQ; inversion Ha; subst; cbn.
  - eapply env_agree_mono; [ exact Hρ | intros y Hy; apply HQ, Hy ].
  - rewrite List.length_map in *.
    eapply IH with (P := fun y => match y with 0 => Q (List.length vts) | S y => P y end); [ | eassumption |].
    + intros [| y] Hy; cbn.
      * constructor; auto.
      * apply Hρ; exact Hy.
    + intros [| y] Hy; [ rewrite Nat.add_0_r in Hy; exact Hy |]; apply HQ; cbn.
      replace (S (List.length vts + y)) with (List.length vts + S y) by lia; exact Hy.
Qed.

(** The environment of a branch under its [n] binders, whose last entries,
    the recursive results, are related only where the branch reads. *)
Lemma env_agree_binders_at : forall n B vts vts' ρ ρ',
    env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ' ->
    domain_list_simulation_at (fun x => ~ exp_fresh x B) (List.map fst vts) (List.map fst vts') -> List.length vts = n ->
    env_agree (fun x => ~ exp_fresh x B) (env_extend_typed ρ vts) (env_extend_typed ρ' vts').
Proof. intros * Hρ Ha Hl; eapply env_agree_args_at; [ exact Hρ | exact Ha |]; intros y Hy; rewrite Hl in Hy; exact Hy. Qed.

(** The values of a branch's entries: the non-uniform parameters, the
    arguments and the recursive results, at whatever types. *)
Lemma branch_entries_map_fst : forall D Mj p ups As ρm gs ns vs ihs,
    List.map fst (branch_entries D Mj p ups As ρm gs ns vs ihs) = ns ++ vs ++ ihs.
Proof.
  intros; unfold branch_entries; rewrite !List.map_app, tele_entries_values, cargs_entries_values,
    pair_values_with_types_values; reflexivity.
Qed.

(** The number of a branch's entries. *)
Lemma branch_entries_length : forall D Mj p ups As ρm gs ns vs ihs,
    List.length (branch_entries D Mj p ups As ρm gs ns vs ihs) = List.length ns + List.length vs + List.length ihs.
Proof.
  intros; rewrite <- (List.length_map fst), branch_entries_map_fst, !List.length_app; lia.
Qed.

(** The values of a motive's entries: the non-uniform parameters and the
    scrutinee, at whatever types. *)
Lemma motive_entries_map_fst : forall D Mk ups ns a m, List.map fst (motive_entries D Mk ups ns a m) = ns ++ m :: nil.
Proof. intros; unfold motive_entries; rewrite List.map_app, tele_entries_values; reflexivity. Qed.

(** The number of a telescope's entries: one per value. *)
Lemma tele_entries_values_length : forall ρ T vs, List.length (tele_entries ρ T vs) = List.length vs.
Proof. intros; rewrite <- (List.length_map fst), tele_entries_values; reflexivity. Qed.

(** The number of a motive's entries. *)
Lemma motive_entries_length : forall D Mk ups ns a m, List.length (motive_entries D Mk ups ns a m) = S (List.length ns).
Proof. intros; rewrite <- (List.length_map fst), motive_entries_map_fst, List.length_app; cbn; lia. Qed.

(** The type of an argument of a function shape, and of its recursive
    result: a [Π] over a family in an environment that holds only it. *)
Lemma domain_simulation_fam_pi : forall b b' d d', domain_simulation b b' -> domain_simulation d d' ->
    domain_simulation (Πᵈ{ak_relevant} b (nil ↦ d ⦂ entry_type_none) fam_cod) (Πᵈ{ak_relevant} b' (nil ↦ d' ⦂ entry_type_none) fam_cod).
Proof.
  intros * Hb Hd; constructor; [ exact Hb |].
  intros [| x] _; cbn; [ constructor; exact Hd | apply env_agree_nil with (P := fun _ => True); exact I ].
Qed.

(** The parts of an eliminator may read only what the eliminator may: its
    blocks, under their binders. *)
Lemma agree_elim_blocks : forall r oq Us j Bks M ρ ρ',
    env_agree (fun x => ~ exp_fresh x (a_elim r oq Us j Bks M)) ρ ρ' -> blocks_agree Bks ρ ρ'.
Proof.
  intros * H b Hb; split.
  - intros x Hx; apply H; intros Hf; apply Hx.
    pose proof (optional_exp_fresh_elim_blocks (Some x) r oq Us j Bks M Hf b Hb) as [Hm _]; exact Hm.
  - intros c n B Hin x Hx; apply H; intros Hf; apply Hx.
    pose proof (optional_exp_fresh_elim_blocks (Some x) r oq Us j Bks M Hf b Hb) as [_ Hbr]; exact (Hbr _ _ _ Hin).
Qed.

(** The motives at the ends of the leaf paths of a shape, read where the
    blocks may: each end at as many parameters as its member's motive
    binds ([rview_leaf_arity], [blocks_binder_count_at]), down the record views'
    fields by their order, as [Core.Semantic.Avoid]'s
    [ends_fresh_of_blocks]. *)
Lemma ends_agree_of_blocks : forall p D Bks ρ ρ', ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D ->
    blocks_binder_count_at D None Bks -> blocks_agree Bks ρ ρ' ->
    forall t, (exists Mj, ind_member D (ptyp_mem t) = Some Mj /\ List.length (ptyp_ps t) = im_nn Mj) ->
      ends_agree p (blocks_motives Bks) ρ ρ' t.
Proof.
  intros p D Bks ρ ρ' HD Har Hnm HB.
  enough (H : forall n t, (forall Mj, ind_member D (ptyp_mem t) = Some Mj -> im_is_rview Mj = true -> ptyp_mem t < n) ->
                (exists Mj, ind_member D (ptyp_mem t) = Some Mj /\ List.length (ptyp_ps t) = im_nn Mj) ->
                ends_agree p (blocks_motives Bks) ρ ρ' t)
    by (intros t Hpl; apply (H (S (ptyp_mem t)) t); [ intros; lia | exact Hpl ]).
  induction n as [n IHn] using Wf_nat.lt_wf_ind.
  induction t as [j Ps | B t IHt]; intros Hrk (Mj & HMj & Hl); cbn [ptyp_mem ptyp_ps] in *.
  - destruct (im_is_rview Mj) eqn:Hrv.
    + (** A record view: its fields, at members before it. *)
      unfold im_is_rview in Hrv; destruct (im_head Mj) as [| | qr Is fl] eqn:Hh; try discriminate Hrv.
      eapply ends_agree_rview; [ exact HD | exact HMj | exact Hh |].
      intros c gs gs1 t gs2 Hcs E.
      pose proof (rview_leaf_params_length _ Har _ _ _ _ HMj ltac:(unfold im_is_rview; rewrite Hh; reflexivity)
                    ltac:(rewrite Hcs; left; reflexivity) gs1 t gs2 E) as Hpt.
      apply (IHn j (Hrk Mj HMj ltac:(unfold im_is_rview; rewrite Hh; reflexivity)) t); [| exact Hpt ].
      intros Mt HMt HrT; exact (rview_leaf_order _ Har _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs E HMt HrT).
    + (** A member with a block: its motive. *)
      eapply ends_agree_self; [ exact HD | exact HMj | exact Hrv |].
      pose proof (nth_motives_sel None Bks j) as Hm; cbn [motives_sel elim_src] in Hm.
      destruct Hm as [-> | (b & Hb & ->)]; [ intros x Hx; exfalso; apply Hx; exact I |].
      rewrite Hl, <- (Hnm _ _ _ HMj Hb); exact (proj1 (HB _ (List.nth_error_In _ _ Hb))).
  - apply ends_agree_pi, IHt; [ exact Hrk | exists Mj; split; assumption ].
Qed.

(** And so at every recursive argument of a constructor of [D]. *)
Lemma cargs_ends_agree : forall p D Bks ρ ρ' gs, ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D ->
    blocks_binder_count_at D None Bks -> blocks_agree Bks ρ ρ' -> cargs_params_length D gs ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_agree p (blocks_motives Bks) ρ ρ' t.
Proof. intros * HD Har Hnm HB Hpl gs1 t gs2 E; exact (ends_agree_of_blocks _ _ _ _ _ HD Har Hnm HB t (Hpl gs1 t gs2 E)). Qed.

#[local]
Hint Resolve domain_simulation_lvl_suc domain_simulation_lvl_max domain_list_simulation_snoc env_agree_nil
  domain_list_simulation_app domain_list_simulation_firstn domain_list_simulation_skipn env_agree_all_args env_agree_all_cons : mctt.

(** ** Environments of Bodies and Spines *)

(** The environment of a body agrees on the entries the body adds, and,
    above them, where the environment it extends did. *)
Definition above (n : nat) (P : nat -> Prop) (z : nat) : Prop := z < n \/ exists y, z = n + y /\ P y.

Lemma above_zero : forall P z, above 0 P z -> P z.
Proof. intros * [Hz | (y & -> & Hy)]; [ lia | exact Hy ]. Qed.

Lemma above_of : forall n (P Q : nat -> Prop), (forall y, Q (n + y) -> P y) -> forall z, Q z -> above n P z.
Proof.
  intros * H z Hz; destruct (Nat.lt_ge_cases z n) as [Hlt | Hge]; [ left; exact Hlt | right ].
  exists (z - n); split; [ lia | apply H; replace (n + (z - n)) with z by lia; exact Hz ].
Qed.

(** A member's prefix reads only where the module with the member does. *)
Lemma gmod_fresh_ext_prefix : forall Φ y E z, ~ gmod_fresh z Φ -> ~ gmod_fresh z (gm_ext Φ y E).
Proof. intros * Hz Hf; apply Hz; cbn in Hf; exact (proj1 Hf). Qed.

(** A body's environment agrees, where the body may read, also where the
    prefix up to one of its members may read. *)
Lemma env_agree_body_prefix : forall sm Φ x Φx ρ ρ',
    gm_prefix_upto (gm_expand Φ) x = Some Φx ->
    env_agree (fun z => ~ gunit_fresh z (gu_mk nil (md_body sm Φ))) ρ ρ' ->
    env_agree (fun z => ~ gmod_fresh z Φx) ρ ρ'.
Proof.
  intros * Hp Hρ z Hz; apply Hρ; intros Hf; apply Hz; cbn in Hf; destruct Hf as [_ Hf].
  exact (prefix_upto_fresh _ _ _ _ Hp (gmod_fresh_expand _ _ Hf)).
Qed.

(** The environment of a prefix ending in a member agrees where the
    member's term may read. *)
Lemma env_agree_above_entry_tm : forall Φ y E A M (P : nat -> Prop) ρ ρ',
    entry_tm E = Some (A, M) ->
    (forall z, ~ gmod_fresh z (gm_ext Φ y E) -> P z) ->
    env_agree (above (gm_binders Φ) P) ρ ρ' ->
    env_agree (fun z => ~ exp_fresh z M) ρ ρ'.
Proof.
  intros * He HP Hab z Hz; apply Hab; apply above_of with (Q := fun z => ~ exp_fresh z M); [| exact Hz ].
  intros w Hw; apply HP; intros Hf; apply Hw; cbn in Hf; destruct Hf as [_ Hf];
    exact (gentry_fresh_tm _ _ _ _ He Hf).
Qed.

(** The environment of a prefix ending in a member agrees where the
    member's unit may read. *)
Lemma env_agree_above_entry_unit : forall Φ y E U (P : nat -> Prop) ρ ρ',
    entry_unit E = Some U ->
    (forall z, ~ gmod_fresh z (gm_ext Φ y E) -> P z) ->
    env_agree (above (gm_binders Φ) P) ρ ρ' ->
    env_agree (fun z => ~ gunit_fresh z U) ρ ρ'.
Proof.
  intros * He HP Hab z Hz; apply Hab; apply above_of with (Q := fun z => ~ gunit_fresh z U); [| exact Hz ].
  intros w Hw; apply HP; intros Hf; apply Hw; cbn in Hf; destruct Hf as [_ Hf];
    exact (gentry_fresh_unit _ _ _ He Hf).
Qed.

(** A function shape's domain reads only where the shape does. *)
Lemma env_agree_pi_domain : forall B t ρ ρ',
    env_agree (fun x => ~ ptyp_fresh x (pt_pi B t)) ρ ρ' -> env_agree (fun x => ~ exp_fresh x B) ρ ρ'.
Proof. intros * H; eapply env_agree_mono; [ exact H | intros x Hx Hf; apply Hx; cbn in Hf; exact (proj1 Hf) ]. Qed.

(** The body environment of the empty module is the one it extends. *)
Lemma env_agree_above_zero : forall (P : nat -> Prop) ρ ρ', env_agree P ρ ρ' -> env_agree (above 0 P) ρ ρ'.
Proof. intros * H z Hz; apply H; exact (above_zero _ _ Hz). Qed.

Lemma env_agree_above_cons : forall n P e e' ρ ρ',
    env_agree (above n P) ρ ρ' -> dentry_simulation e e' -> env_agree (above (S n) P) (e :: ρ) (e' :: ρ').
Proof.
  intros * H He [| z] Hz; cbn; [ exact He |].
  apply H; destruct Hz as [Hz | (y & Hy & HP)]; [ left; lia | right; exists y; split; [ lia | exact HP ] ].
Qed.

Lemma nil_agree : forall x, dentry_simulation (env_entry nil x) (env_entry nil x).
Proof. intros; apply env_agree_nil with (P := fun _ => True); exact I. Qed.

Lemma agree_spine : forall H R args pre y (ρ ρ' : env),
    modexp_spine H = (R, args, pre) ->
    env_agree (fun x => ~ exp_fresh x (a_mem H y)) ρ ρ' ->
    env_agree (fun x => ~ modexp_fresh x R) ρ ρ' /\ env_agree (fun x => ~ Forall (exp_fresh x) args) ρ ρ'.
Proof.
  intros * Hs Hρ; split; eapply env_agree_mono; try exact Hρ; intros x Hx Hf; apply Hx;
    cbn in Hf; destruct (modexp_spine_fresh _ _ _ _ _ Hs Hf); assumption.
Qed.

#[local]
Hint Resolve nil_agree : mctt.

(** ** Evaluation *)

(** The parts of a term may read only what the term may. *)
Ltac nf_sub := let x := fresh "x" in let Hx := fresh "Hx" in let Hf := fresh "Hf" in
  intros x Hx Hf; apply Hx; cbn in Hf |- *; rewrite ?Forall_cons_iff in Hf;
  rewrite ?all_list_Forall in Hf; tauto.

(** Inversion of the relation on a value whose head is known. *)
Ltac sim_inv :=
  match goal with
  | H : domain_simulation (_ _) _ |- _ => inversion H; subst; clear H
  | H : domain_simulation (_ _ _) _ |- _ => inversion H; subst; clear H
  | H : domain_simulation (_ _ _ _) _ |- _ => inversion H; subst; clear H
  | H : domain_simulation (_ _ _ _ _) _ |- _ => inversion H; subst; clear H
  | H : domain_simulation (_ _ _ _ _ _) _ |- _ => inversion H; subst; clear H
  | H : domain_simulation ⊤ᵈ _ |- _ => inversion H; subst; clear H
  | H : domain_simulation ⊥ᵈ _ |- _ => inversion H; subst; clear H
  | H : domain_simulation Propᵈ _ |- _ => inversion H; subst; clear H
  | H : dmod_simulation (_ _ _) _ |- _ => inversion H; subst; clear H
  | H : dmod_simulation (_ _ _ _) _ |- _ => inversion H; subst; clear H
  | H : domain_list_simulation (_ :: _) _ |- _ => inversion H; subst; clear H
  | H : domain_list_simulation nil _ |- _ => inversion H; subst; clear H
  | Hs : modexp_spine ?H = (?R, ?args, ?pre), Hρ : env_agree (fun x => ~ exp_fresh x (a_mem ?H _)) ?ρ ?ρ' |- _ =>
      destruct (agree_spine _ _ _ _ _ _ _ Hs Hρ); clear Hρ
  | H : forall x, ~ @?F x -> dentry_simulation (env_entry ?ρ x) (env_entry ?ρ' x) |- _ =>
      change (env_agree (fun x => ~ F x) ρ ρ') in H; cbv beta in H
  | H : forall b, In b ?Bks -> (forall x, _ -> dentry_simulation (env_entry ?ρ x) (env_entry ?ρ' x)) /\ _ |- _ =>
      change (blocks_agree Bks ρ ρ') in H
  end.

(** A related entry: a related value, or the closure of a unit over
    environments that agree where the unit may read. *)
Ltac related_entry_tac :=
  first [ constructor; eassumption
        | constructor; solve [ eauto with mctt ]
        | apply dentry_simulation_mod; apply dmod_simulation_local;
          eapply env_agree_mono; [ eassumption | nf_sub ] ].

(** An environment that agrees where a term may read, for one of its parts:
    the same environment, or one extended by related entries, or one of
    values of closed terms. *)
Ltac agree_tac :=
  first [ eassumption
        | match goal with Hρ : env_agree _ ?ρ _ |- env_agree _ ?ρ _ =>
            eapply env_agree_mono; [ exact Hρ | nf_sub ] end
        | match goal with |- env_agree _ (env_extend_typed nil ?args) _ =>
            apply env_agree_nil_args; solve [ unfold typed_simulation; eauto with mctt ] end
        | match goal with
          | |- env_agree _ (_ :: ?ρ) _ => idtac
          | |- env_agree _ (extend_env ?ρ _ _) _ => unfold extend_env
          | |- env_agree _ (extend_env_mod ?ρ _ _) _ => unfold extend_env_mod
          | |- env_agree _ (extend_env_dm ?ρ _ _ _ _) _ => unfold extend_env_dm
          end;
          match goal with |- env_agree _ (_ :: ?ρ) _ =>
            match goal with Hρ : env_agree _ ?ρ _ |- _ =>
              eapply env_agree_cons; [ exact Hρ | related_entry_tac | nf_sub ] end end
        | match goal with |- env_agree _ nil _ => apply env_agree_nil end
        | match goal with |- env_agree _ (env_extend_typed ?ρ ?args) _ =>
            match goal with Hρ : env_agree _ ?ρ _, Ha : typed_simulation args _ |- _ =>
              eapply env_agree_args; [ exact Hρ | exact Ha |];
              let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
              intros y Hy Hf; apply Hy; cbn in Hf;
              repeat match goal with He : List.length args = List.length _ |- _ => rewrite He end;
              tauto end end ].

(** A premise on the length of the fast arguments, from the reference ones. *)
Ltac len_tac :=
  match goal with Hl : domain_list_simulation ?a ?a' |- context [List.length ?a'] =>
    rewrite <- (domain_list_simulation_length _ _ Hl); eassumption end.

(** Forward reasoning: each induction hypothesis, at the fast arguments that
    are related to its reference ones. *)
Ltac sim_fwd :=
  match goal with
  | IH : forall ρ0, env_agree ?P ?ρ ρ0 -> exists _, _ /\ _ |- _ =>
      let H' := fresh "Ha" in
      eassert (H' : env_agree P ρ _) by agree_tac;
      destruct (IH _ H') as (? & ? & ?); clear IH H'
  | IH : forall m0 n0, domain_simulation ?m m0 -> domain_simulation ?n n0 -> exists _, _ /\ _, Hm : domain_simulation ?m ?m', Hn : domain_simulation ?n ?n' |- _ =>
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  | IH : forall m0 n0, domain_simulation ?m m0 -> domain_list_simulation ?n n0 -> exists _, _ /\ _, Hm : domain_simulation ?m ?m', Hn : domain_list_simulation ?n ?n' |- _ =>
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  (** An application to the proof, related to itself *)
  | IH : forall m0 n0, domain_simulation ?m m0 -> domain_simulation ⋆ᵈ⟨?N, ?ρ⟩ n0 -> exists _, _ /\ _,
      Hm : domain_simulation ?m ?m', Hρ : env_agree _ ?ρ ?ρ' |- _ =>
      destruct (IH _ ⋆ᵈ⟨N, ρ'⟩ Hm (domain_simulation_proof _ _ _ _)) as (? & ? & ?); clear IH
  | IH : forall m0 n0, dmod_simulation ?m m0 -> domain_simulation ?n n0 -> exists _, _ /\ _, Hm : dmod_simulation ?m ?m', Hn : domain_simulation ?n ?n' |- _ =>
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  | IH : forall m0, dmod_simulation ?m m0 -> exists _, _ /\ _, Hm : dmod_simulation ?m ?m' |- _ =>
      destruct (IH _ Hm) as (? & ? & ?); clear IH
  | IH : forall m0 n0, dmod_simulation ?m m0 -> domain_list_simulation ?n n0 -> exists _, _ /\ _, Hm : dmod_simulation ?m ?m', Hn : domain_list_simulation ?n ?n' |- _ =>
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  | IH : forall m0 n0, domain_simulation ?m m0 -> domain_list_simulation ?n n0 -> exists _, _ /\ _, Hn : domain_list_simulation ?n ?n' |- _ =>
      let Hm := fresh "Hm" in
      eassert (Hm : domain_simulation m _) by (eauto with mctt);
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  | IH : forall m0, dmod_simulation ?m m0 -> exists _, _ /\ _ |- _ =>
      let Hm := fresh "Hm" in
      eassert (Hm : dmod_simulation m _) by (eauto with mctt);
      destruct (IH _ Hm) as (? & ? & ?); clear IH
  (** The member a view stands for, at related uniform parameters *)
  | IH : forall u0, domain_list_simulation ?u u0 -> exists _, _ /\ _, Hu : domain_list_simulation ?u ?u' |- _ =>
      destruct (IH _ Hu) as (? & ? & ?); clear IH
  (** A function applied along terms: at the related function, in an
      environment that agrees where the terms read *)
  | IH : forall f0 ρ0, domain_simulation ?f f0 -> env_agree ?P ?ρ ρ0 -> exists _, _ /\ _, Hf : domain_simulation ?f ?f' |- _ =>
      let H' := fresh "Ha" in
      eassert (H' : env_agree P ρ _) by agree_tac;
      destruct (IH _ _ Hf H') as (? & ? & ?); clear IH H'
  end.

(** The kinds evaluation reads off a value, carried to the related fast
    value ([arg_kind_sim], [domain_kind_sim]). *)
Ltac rel_transfer :=
  repeat match goal with
  | H : arg_kind ?T ?X ?m = ?r, Hs : domain_simulation ?m ?m' |- _ =>
      lazymatch goal with
      | _ : arg_kind T X m' = r |- _ => fail
      | _ => pose proof (eq_trans (eq_sym (arg_kind_sim _ _ Hs)) H)
      end
  | H : evaluated_kind (arg_kind ?T ?X ?m), Hs : domain_simulation ?m ?m' |- _ =>
      lazymatch goal with
      | _ : evaluated_kind (arg_kind T X m') |- _ => fail
      | _ => pose proof (eq_ind _ evaluated_kind H _ (arg_kind_sim _ _ Hs))
      end
  | H : domain_kind ?a = ?r, Hs : domain_simulation ?a ?a' |- _ =>
      lazymatch goal with
      | _ : domain_kind a' = r |- _ => fail
      | _ => pose proof (eq_trans (eq_sym (domain_kind_sim _ _ Hs)) H)
      end
  | H : evaluated_kind (domain_kind ?a), Hs : domain_simulation ?a ?a' |- _ =>
      lazymatch goal with
      | _ : evaluated_kind (domain_kind a') |- _ => fail
      | _ => pose proof (eq_ind _ evaluated_kind H _ (domain_kind_sim _ _ Hs))
      end
  end.

(** The goal: the fast rule, and the relation between the results, whose
    closures agree where the reference ones may read. *)
Ltac sim_finish :=
  eexists; split;
  [ first [ solve [ econstructor; solve [ eassumption | len_tac | eapply module_saturated_sim; eassumption
                                        | rewrite <- (domain_list_simulation_length _ _ ltac:(eassumption)); eassumption ] ]
          | solve [ eauto 3 with mctt ] ]
  | repeat first [ eassumption
                 | eapply env_agree_var; [ eassumption | cbn; intros Hne; apply Hne; reflexivity ]
                 | eapply env_agree_mod; [ eassumption | cbn; intros Hne; apply Hne; reflexivity ]
                 | solve [ eauto with mctt ]
                 | constructor
                 | match goal with |- forall x, ~ _ -> dentry_simulation _ _ =>
                     let x := fresh "x" in let Hx := fresh "Hx" in
                     intros x Hx; match goal with Hρ : env_agree _ _ _ |- _ =>
                       apply Hρ; let Hf := fresh "Hf" in intros Hf; apply Hx; cbn in Hf; tauto end end ] ].

(** ** Recursive Results

    The entries of a list of recursive results that are read: those the
    branch [B] reads, at [Some B]; all of them, at [None]. *)
Definition ihs_read (oB : option exp) : nat -> Prop :=
  match oB with Some B => fun x => ~ exp_fresh x B | None => fun _ => True end.

(** The group's table of leaf paths is coherent where results may be
    skipped: the skipped results of an argument are as many as its leaf
    paths. *)
Definition ihs_coherent (p : qname) (oB : option exp) : Prop :=
  match oB with Some _ => forall D, ind_lookup Θ Ξ p = Some D -> leaves_coherent D | None => True end.

(** Lists related at every entry are related. *)
Lemma domain_list_simulation_at_true : forall l l', domain_list_simulation_at (fun _ => True) l l' -> domain_list_simulation l l'.
Proof. induction 1; constructor; auto. Qed.

(** A block of entries none of which is read, before related ones. *)
Lemma domain_list_simulation_at_skip : forall P l1 l1' l2 l2', List.length l1 = List.length l1' ->
    (forall i, i < List.length l1 -> ~ P (List.length l2 + i)) -> domain_list_simulation_at P l2 l2' ->
    domain_list_simulation_at P (l1 ++ l2) (l1' ++ l2').
Proof.
  induction l1 as [| a l1 IH]; intros [| a' l1'] * Hl HP H2; cbn in Hl; try discriminate; cbn; [ exact H2 |].
  injection Hl as Hl; constructor; [| apply IH; [ exact Hl | intros; apply HP; cbn; lia | exact H2 ] ].
  intros Hp; exfalso; apply (HP (List.length l1)); [ cbn; lia |].
  rewrite List.length_app in Hp; replace (List.length l2 + List.length l1) with (List.length l1 + List.length l2) by lia; exact Hp.
Qed.

(** A list of terms evaluates to as many values. *)
Lemma eval_exps_length : forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> List.length ms = List.length Ms.
Proof. induction 1; cbn; congruence. Qed.

(** The recursive results of an argument are of a filed group. *)
Lemma eval_ih_lookup : forall ρ p ups Bks t v rs, ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
    exists D, ind_lookup Θ Ξ p = Some D.
Proof. inversion 1; subst; eauto. Qed.

(** The recursive results of a function shape, one closure per leaf path,
    over related parts. *)
Lemma domain_list_simulation_map_ihfn : forall ρ ρ' Bks p ups ups' t f f' n,
    blocks_agree Bks ρ ρ' -> domain_list_simulation ups ups' -> domain_simulation f f' ->
    domain_list_simulation (List.map (fun i => d_ihfn ρ Bks p ups t i f) (List.seq 0 n))
              (List.map (fun i => d_ihfn ρ' Bks p ups' t i f') (List.seq 0 n)).
Proof.
  intros * HB Hu Hf; generalize 0; induction n as [| n IH]; intros k; cbn; constructor; [| apply IH ].
  constructor; [ exact HB | exact Hu | exact Hf ].
Qed.

(** The types of the recursive results of a function shape, one family per
    leaf path, over related parts. *)
Lemma domain_list_simulation_map_ihfam : forall b b' ρm ρm' As p ups ups' ρ ρ' B t f f' n,
    domain_simulation b b' -> ends_agree p As ρm ρm' t -> domain_list_simulation ups ups' ->
    env_agree (fun x => ~ ptyp_fresh x (pt_pi B t)) ρ ρ' -> domain_simulation f f' ->
    domain_list_simulation
      (List.map (fun i => Πᵈ{ak_relevant} b (nil ↦ d_ihfam ρm As p ups ρ B t i f ⦂ entry_type_none) fam_cod) (List.seq 0 n))
      (List.map (fun i => Πᵈ{ak_relevant} b' (nil ↦ d_ihfam ρm' As p ups' ρ' B t i f' ⦂ entry_type_none) fam_cod) (List.seq 0 n)).
Proof.
  intros * Hb HA Hu Hρ Hf; generalize 0; induction n as [| n IH]; intros k; cbn; constructor; [| apply IH ].
  apply domain_simulation_fam_pi; [ exact Hb | constructor; [ exact HA | exact Hu | exact Hρ | exact Hf ] ].
Qed.

#[local]
Hint Resolve domain_fields_simulation_combine : mctt.

Section Eval.

  Theorem fast_eval_sim :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> forall ρ', env_agree (fun x => ~ exp_fresh x M) ρ ρ' ->
       exists m', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ m' /\ domain_simulation m m') /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> forall m' n', domain_simulation m m' -> domain_simulation n n' ->
       exists r', $ᶠ| m' & n' | Θ ⍮ Ξ ↘ r' /\ domain_simulation r r') /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> forall ρ', env_agree (fun x => ~ Forall (exp_fresh x) Ms) ρ ρ' ->
       exists ms', ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ms' /\ domain_list_simulation ms ms') /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r -> forall m' args', domain_simulation m m' -> domain_list_simulation args args' ->
       exists r', $*ᶠ| m' & args' | Θ ⍮ Ξ ↘ r' /\ domain_simulation r r') /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall ρ', env_agree (fun x => ~ modexp_fresh x H) ρ ρ' ->
       exists h', ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ' ↘ h' /\ dmod_simulation h h') /\
    (forall Δ D ρ h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall ρ', env_agree (fun x => ~ gunit_fresh x (gu_mk Δ D)) ρ ρ' ->
       exists h', ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ' ↘ h' /\ dmod_simulation h h') /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> forall h' n', dmod_simulation h h' -> domain_simulation n n' ->
       exists r', $ᵐᶠ| h' & n' | Θ ⍮ Ξ ↘ r' /\ dmod_simulation r r') /\
    (forall h ns r, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r -> forall h' ns', dmod_simulation h h' -> domain_list_simulation ns ns' ->
       exists r', $ᵐ*ᶠ| h' & ns' | Θ ⍮ Ξ ↘ r' /\ dmod_simulation r r') /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> forall h', dmod_simulation h h' -> exists r', h' ·ₜᶠ x Θ ⍮ Ξ ↘ r' /\ domain_simulation r r') /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> forall h', dmod_simulation h h' -> exists r', h' ·ₘᶠ y Θ ⍮ Ξ ↘ r' /\ dmod_simulation r r') /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> forall h', dmod_simulation h h' -> exists r', h' ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r' /\ domain_simulation r r') /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> forall h', dmod_simulation h h' -> exists r', h' ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r' /\ dmod_simulation r r') /\
    (forall ρ Φ ρ1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 -> forall ρ' (P : nat -> Prop),
       (forall x, ~ gmod_fresh x Φ -> P x) -> env_agree P ρ ρ' ->
       exists ρ1', ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ρ1' /\ env_agree (above (gm_binders Φ) P) ρ1 ρ1') /\
    (forall ρ p ups Bks j m r, ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> forall ρ' ups' m',
       blocks_agree Bks ρ ρ' -> domain_list_simulation ups ups' -> domain_simulation m m' ->
       exists r', ⟦elimᶠ m' at j of p ups' Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ domain_simulation r r') /\
    (forall ρ p ups Bks gs vs ihs, ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs -> forall ρ' ups' vs' oB,
       blocks_agree Bks ρ ρ' -> domain_list_simulation ups ups' -> domain_list_simulation vs vs' -> ihs_coherent p oB ->
       exists ihs', ⟦ihsᶠ vs' of gs under p ups' Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ihs' /\
       domain_list_simulation_at (ihs_read oB) ihs ihs') /\
    (forall ρ p ups Bks t m r, ⟦ih m of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> forall ρ' ups' m',
       blocks_agree Bks ρ ρ' -> domain_list_simulation ups ups' -> domain_simulation m m' ->
       exists r', ⟦ihᶠ m' of t under p ups' Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ domain_list_simulation r r') /\
    (forall p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r -> forall ups', domain_list_simulation ups ups' ->
       exists pre', ⟦mrefᶠ j of p ups' ⟧ᶠ Θ ⍮ Ξ ↘ (fst r, pre') /\ domain_list_simulation (snd r) pre') /\
    (forall p ups ρ t a, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> forall ups' ρ',
       domain_list_simulation ups ups' -> env_agree (fun x => ~ ptyp_fresh x t) ρ ρ' ->
       exists a', ⟦shtyᶠ t of p ups' ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ a' /\ domain_simulation a a') /\
    (forall p ups ρm As ρ t m a, ⟦ihty m of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> forall ups' ρm' ρ' m',
       domain_list_simulation ups ups' -> ends_agree p As ρm ρm' t -> env_agree (fun x => ~ ptyp_fresh x t) ρ ρ' -> domain_simulation m m' ->
       exists a', ⟦ihtyᶠ m' of t at p ups' under ρm' As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ a' /\ domain_list_simulation a a') /\
    (forall f m r, eval_proj Θ Ξ f m r -> forall m', domain_simulation m m' ->
       exists r', fast_eval_proj Θ Ξ f m' r' /\ domain_simulation r r') /\
    (forall m ρ fl rs, eval_neutral_fields Θ Ξ m ρ fl rs -> forall m' ρ',
       domain_ne_simulation m m' -> env_agree (fun _ => True) ρ ρ' ->
       exists rs', fast_eval_neutral_fields Θ Ξ m' ρ' fl rs' /\ domain_list_simulation rs rs') /\
    (forall fl v ws, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws -> forall v', domain_simulation v v' ->
       exists ws', ⟦projsᶠ fl of v' ⟧ᶠ Θ ⍮ Ξ ↘ ws' /\ domain_list_simulation ws ws') /\
    (forall p ups ρm As ρ gs vs rs, ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs -> forall ups' ρm' ρ' vs',
       domain_list_simulation ups ups' -> (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_agree p As ρm ρm' t) ->
       env_agree (fun _ => True) ρ ρ' -> domain_list_simulation vs vs' ->
       exists rs', ⟦ihtysᶠ vs' of gs at p ups' under ρm' As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ rs' /\ domain_list_simulation rs rs') /\
    (forall rs Ms ρ ms, eval_field_vals Θ Ξ rs Ms ρ ms -> forall ρ', env_agree (fun x => ~ Forall (exp_fresh x) Ms) ρ ρ' ->
       exists ms', fast_eval_field_vals Θ Ξ rs Ms ρ' ms' /\ domain_list_simulation ms ms') /\
    (forall f Ms ρ r, eval_app_args Θ Ξ f Ms ρ r -> forall f' ρ', domain_simulation f f' ->
       env_agree (fun x => ~ Forall (exp_fresh x) Ms) ρ ρ' ->
       exists r', fast_eval_app_args Θ Ξ f' Ms ρ' r' /\ domain_simulation r r').
  Proof.
    apply (eval_mut_ind Θ Ξ
      (fun M ρ m _ => forall ρ', env_agree (fun x => ~ exp_fresh x M) ρ ρ' ->
         exists m', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ m' /\ domain_simulation m m')
      (fun m n r _ => forall m' n', domain_simulation m m' -> domain_simulation n n' -> exists r', $ᶠ| m' & n' | Θ ⍮ Ξ ↘ r' /\ domain_simulation r r')
      (fun Ms ρ ms _ => forall ρ', env_agree (fun x => ~ Forall (exp_fresh x) Ms) ρ ρ' ->
         exists ms', ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ms' /\ domain_list_simulation ms ms')
      (fun m args r _ => forall m' args', domain_simulation m m' -> domain_list_simulation args args' ->
         exists r', $*ᶠ| m' & args' | Θ ⍮ Ξ ↘ r' /\ domain_simulation r r')
      (fun H ρ h _ => forall ρ', env_agree (fun x => ~ modexp_fresh x H) ρ ρ' ->
         exists h', ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ' ↘ h' /\ dmod_simulation h h')
      (fun Δ D ρ h _ => forall ρ', env_agree (fun x => ~ gunit_fresh x (gu_mk Δ D)) ρ ρ' ->
         exists h', ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ' ↘ h' /\ dmod_simulation h h')
      (fun h n r _ => forall h' n', dmod_simulation h h' -> domain_simulation n n' -> exists r', $ᵐᶠ| h' & n' | Θ ⍮ Ξ ↘ r' /\ dmod_simulation r r')
      (fun h ns r _ => forall h' ns', dmod_simulation h h' -> domain_list_simulation ns ns' -> exists r', $ᵐ*ᶠ| h' & ns' | Θ ⍮ Ξ ↘ r' /\ dmod_simulation r r')
      (fun h x r _ => forall h', dmod_simulation h h' -> exists r', h' ·ₜᶠ x Θ ⍮ Ξ ↘ r' /\ domain_simulation r r')
      (fun h y r _ => forall h', dmod_simulation h h' -> exists r', h' ·ₘᶠ y Θ ⍮ Ξ ↘ r' /\ dmod_simulation r r')
      (fun h ch r _ => forall h', dmod_simulation h h' -> exists r', h' ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r' /\ domain_simulation r r')
      (fun h ch r _ => forall h', dmod_simulation h h' -> exists r', h' ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r' /\ dmod_simulation r r')
      (fun ρ Φ ρ1 _ => forall ρ' (P : nat -> Prop),
         (forall x, ~ gmod_fresh x Φ -> P x) -> env_agree P ρ ρ' ->
         exists ρ1', ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ρ1' /\ env_agree (above (gm_binders Φ) P) ρ1 ρ1')
      (fun ρ p ups Bks j m r _ => forall ρ' ups' m',
         blocks_agree Bks ρ ρ' -> domain_list_simulation ups ups' -> domain_simulation m m' ->
         exists r', ⟦elimᶠ m' at j of p ups' Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ domain_simulation r r')
      (fun ρ p ups Bks gs vs ihs _ => forall ρ' ups' vs' oB,
         blocks_agree Bks ρ ρ' -> domain_list_simulation ups ups' -> domain_list_simulation vs vs' -> ihs_coherent p oB ->
         exists ihs', ⟦ihsᶠ vs' of gs under p ups' Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ihs' /\
         domain_list_simulation_at (ihs_read oB) ihs ihs')
      (fun ρ p ups Bks t m r _ => forall ρ' ups' m',
         blocks_agree Bks ρ ρ' -> domain_list_simulation ups ups' -> domain_simulation m m' ->
         exists r', ⟦ihᶠ m' of t under p ups' Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ domain_list_simulation r r')
      (fun p ups j r _ => forall ups', domain_list_simulation ups ups' ->
         exists pre', ⟦mrefᶠ j of p ups' ⟧ᶠ Θ ⍮ Ξ ↘ (fst r, pre') /\ domain_list_simulation (snd r) pre')
      (fun p ups ρ t a _ => forall ups' ρ',
         domain_list_simulation ups ups' -> env_agree (fun x => ~ ptyp_fresh x t) ρ ρ' ->
         exists a', ⟦shtyᶠ t of p ups' ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ a' /\ domain_simulation a a')
      (fun p ups ρm As ρ t m a _ => forall ups' ρm' ρ' m',
         domain_list_simulation ups ups' -> ends_agree p As ρm ρm' t -> env_agree (fun x => ~ ptyp_fresh x t) ρ ρ' -> domain_simulation m m' ->
         exists a', ⟦ihtyᶠ m' of t at p ups' under ρm' As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ a' /\ domain_list_simulation a a')
      (fun f m r _ => forall m', domain_simulation m m' -> exists r', fast_eval_proj Θ Ξ f m' r' /\ domain_simulation r r')
      (fun m ρ fl rs _ => forall m' ρ',
         domain_ne_simulation m m' -> env_agree (fun _ => True) ρ ρ' ->
         exists rs', fast_eval_neutral_fields Θ Ξ m' ρ' fl rs' /\ domain_list_simulation rs rs')
      (fun fl v ws _ => forall v', domain_simulation v v' -> exists ws', ⟦projsᶠ fl of v' ⟧ᶠ Θ ⍮ Ξ ↘ ws' /\ domain_list_simulation ws ws')
      (fun p ups ρm As ρ gs vs rs _ => forall ups' ρm' ρ' vs',
         domain_list_simulation ups ups' -> (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_agree p As ρm ρm' t) ->
         env_agree (fun _ => True) ρ ρ' -> domain_list_simulation vs vs' ->
         exists rs', ⟦ihtysᶠ vs' of gs at p ups' under ρm' As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ rs' /\ domain_list_simulation rs rs')
      (fun rs Ms ρ ms _ => forall ρ', env_agree (fun x => ~ Forall (exp_fresh x) Ms) ρ ρ' ->
         exists ms', fast_eval_field_vals Θ Ξ rs Ms ρ' ms' /\ domain_list_simulation ms ms')
      (fun f Ms ρ r _ => forall f' ρ', domain_simulation f f' -> env_agree (fun x => ~ Forall (exp_fresh x) Ms) ρ ρ' ->
         exists r', fast_eval_app_args Θ Ξ f' Ms ρ' r' /\ domain_simulation r r'));
      intros; cbn [fst snd ptyp_ps ptyp_mem] in *.
    all: try solve [ repeat sim_inv; repeat sim_fwd; rel_transfer; sim_finish ].
    (** A local definition: its type, its body, then the rest under the
        definition, by the kind of its type *)
    all: try solve [ match goal with
      | IHA : forall ρ0, env_agree (fun x => ~ exp_fresh x ?A) ?ρ ρ0 -> exists _, _ /\ _,
        IHM : forall ρ0, env_agree (fun x => ~ exp_fresh x ?M) ?ρ ρ0 -> exists _, _ /\ _,
        IHB : forall ρ0, env_agree (fun x => ~ exp_fresh x ?B) (?ρ ↦ ?m ⦂ _) ρ0 -> exists _, _ /\ _,
        Hρ : env_agree (fun x => ~ exp_fresh x (ℓ ?A ≔ ?M in ?B)) ?ρ ?ρ' |- _ =>
          let a' := fresh "a'" in let m' := fresh "m'" in let r' := fresh "r'" in
          destruct (IHA ρ') as (a' & ? & ?); [ eapply env_agree_mono; [ exact Hρ | nf_sub ] |];
          destruct (IHM ρ') as (m' & ? & ?); [ eapply env_agree_mono; [ exact Hρ | nf_sub ] |];
          destruct (IHB (ρ' ↦ m' ⦂ entry_type_value a')) as (r' & ? & ?);
            [ eapply env_agree_cons; [ exact Hρ | constructor; eassumption | nf_sub ] |];
          rel_transfer; exists r'; split; [ eapply fast_eval_exp_let; eassumption | assumption ]
      | IHA : forall ρ0, env_agree (fun x => ~ exp_fresh x ?A) ?ρ ρ0 -> exists _, _ /\ _,
        IHB : forall ρ0, env_agree (fun x => ~ exp_fresh x ?B) (?ρ ↦ ⋆ᵈ⟨?M, ?ρ⟩ ⦂ _) ρ0 -> exists _, _ /\ _,
        Hρ : env_agree (fun x => ~ exp_fresh x (ℓ ?A ≔ ?M in ?B)) ?ρ ?ρ' |- _ =>
          let a' := fresh "a'" in let r' := fresh "r'" in
          destruct (IHA ρ') as (a' & ? & ?); [ eapply env_agree_mono; [ exact Hρ | nf_sub ] |];
          destruct (IHB (ρ' ↦ ⋆ᵈ⟨M, ρ'⟩ ⦂ entry_type_value a')) as (r' & ? & ?);
            [ eapply env_agree_cons; [ exact Hρ | constructor; constructor | nf_sub ] |];
          rel_transfer; exists r'; split; [ eapply fast_eval_exp_let_proof; eassumption | assumption ]
      (** with a module part: also the unit's literal *)
      | IHA : forall ρ0, env_agree (fun x => ~ exp_fresh x ?A) ?ρ ρ0 -> exists _, _ /\ _,
        IHM : forall ρ0, env_agree (fun x => ~ exp_fresh x ?M) ?ρ ρ0 -> exists _, _ /\ _,
        IHU : forall ρ0, env_agree (fun x => ~ modexp_fresh x (me_lit ?U)) ?ρ ρ0 -> exists _, _ /\ _,
        IHB : forall ρ0, env_agree (fun x => ~ exp_fresh x ?B) (?ρ ↦ᵈ ?m ⦂ _ ‖ ?h ⦂ ?U) ρ0 -> exists _, _ /\ _,
        Hρ : env_agree (fun x => ~ exp_fresh x (ℓᵈ ?A ≔ ?M ‖ ?U in ?B)) ?ρ ?ρ' |- _ =>
          let a' := fresh "a'" in let m' := fresh "m'" in let h' := fresh "h'" in let r' := fresh "r'" in
          destruct (IHA ρ') as (a' & ? & ?); [ eapply env_agree_mono; [ exact Hρ | nf_sub ] |];
          destruct (IHM ρ') as (m' & ? & ?); [ eapply env_agree_mono; [ exact Hρ | nf_sub ] |];
          destruct (IHU ρ') as (h' & ? & ?); [ eapply env_agree_mono; [ exact Hρ | nf_sub ] |];
          destruct (IHB (ρ' ↦ᵈ m' ⦂ entry_type_value a' ‖ h' ⦂ U)) as (r' & ? & ?);
            [ eapply env_agree_cons; [ exact Hρ | constructor; eassumption | nf_sub ] |];
          exists r'; split; [ eapply fast_eval_exp_let_dm; eassumption | assumption ]
      end ].
    (** An eliminator: its uniform parameters, its scrutinee, then the
        elimination, whose blocks read only what the eliminator may *)
    all: try solve [ match goal with
      | IHU : forall ρ0, env_agree (fun x => ~ Forall (exp_fresh x) ?Us) ?ρ ρ0 -> exists _, _ /\ _,
        IHM : forall ρ0, env_agree (fun x => ~ exp_fresh x ?M) ?ρ ρ0 -> exists _, _ /\ _,
        IHE : forall ρ0 ups0 m0, blocks_agree ?Bks ?ρ ρ0 -> _ -> _ -> exists _, _ /\ _,
        Hρ : env_agree (fun x => ~ exp_fresh x (a_elim ?κ ?p ?Us ?j ?Bks ?M)) ?ρ ?ρ' |- _ =>
          let ups' := fresh "ups'" in let m' := fresh "m'" in let r' := fresh "r'" in
          destruct (IHU ρ') as (ups' & ? & ?); [ eapply env_agree_mono; [ exact Hρ | nf_sub ] |];
          destruct (IHM ρ') as (m' & ? & ?); [ eapply env_agree_mono; [ exact Hρ | nf_sub ] |];
          destruct (IHE ρ' ups' m') as (r' & ? & ?); [ eapply agree_elim_blocks; exact Hρ | assumption | assumption |];
          exists r'; split; [ econstructor; eassumption | assumption ]
      end ].
    (** A tuple: its type, a record's type former, then its fields *)
    all: try solve [ match goal with
      | IHT : forall ρ0, env_agree (fun x => ~ exp_fresh x ?T) ?ρ ρ0 -> exists _, _ /\ domain_simulation (d_record ?p ?ns) _,
        IHF : forall ρ0, env_agree (fun x => ~ Forall (exp_fresh x) (List.map snd ?fs)) ?ρ ρ0 -> exists _, _ /\ _,
        Hρ : env_agree (fun x => ~ exp_fresh x (a_tuple ?T ?fs)) ?ρ ?ρ' |- _ =>
          let t' := fresh "t'" in let Ht := fresh "Ht" in let vs' := fresh "vs'" in
          destruct (IHT ρ') as (t' & ? & Ht); [ eapply env_agree_mono; [ exact Hρ | nf_sub ] |];
          inversion Ht; subst;
          destruct (IHF ρ') as (vs' & ? & ?);
            [ eapply env_agree_mono; [ exact Hρ |];
              let x := fresh "x" in let Hx := fresh "Hx" in let Hf := fresh "Hf" in
              intros x Hx Hf; apply Hx; cbn [exp_fresh] in Hf; destruct Hf as [_ Hf];
              apply (proj2 (List.Forall_map _ _ _)), (proj1 (all_list_Forall _ _)), Hf
            |];
          eexists; split; [ econstructor; eassumption | constructor; apply domain_fields_simulation_combine; assumption ]
      (** A field of a value *)
      | IHM : forall ρ0, env_agree (fun x => ~ exp_fresh x ?M) ?ρ ρ0 -> exists _, _ /\ _,
        IHp : forall m0, domain_simulation ?m m0 -> exists _, fast_eval_proj _ _ ?f m0 _ /\ _,
        Hρ : env_agree (fun x => ~ exp_fresh x (a_proj ?f ?M)) ?ρ ?ρ' |- _ =>
          let m' := fresh "m'" in let r' := fresh "r'" in
          destruct (IHM ρ') as (m' & ? & ?); [ exact Hρ |];
          destruct (IHp m') as (r' & ? & ?); [ assumption |];
          exists r'; split; [ econstructor; eassumption | assumption ]
      end ].
    (** A constructor of a view at its last uniform parameter: the
        container's, at the view's arguments over related parameters *)
    all: try solve [ match goal with
      | IH : forall ρ0, env_agree (fun x => ~ Forall (exp_fresh x) ?Is) (decl_env ?D (?vs ++ ?n :: nil)) ρ0 -> exists _, _ /\ _,
        Hm : domain_simulation (d_con ?p ?j ?c ?vs) ?m', Hn : domain_simulation ?n ?n' |- _ =>
          inversion Hm; subst;
          match goal with Hvs : domain_list_simulation vs ?vs' |- _ =>
            let cups' := fresh "cups'" in
            destruct (IH (decl_env D (vs' ++ n' :: nil))) as (cups' & ? & ?);
              [ apply env_agree_decl_env; apply domain_list_simulation_snoc; assumption |];
            eexists; split;
              [ econstructor; try eassumption; rewrite <- (domain_list_simulation_length _ _ Hvs); assumption
              | constructor; assumption ] end
      (** A recursive result of a function shape, applied: the function
          applied, then the recursive results at it *)
      | IHa : forall m0 n0, domain_simulation ?f m0 -> domain_simulation ?n n0 -> exists _, _ /\ _,
        IHi : forall ρ0 ups0 m0, blocks_agree ?Bks ?ρ ρ0 -> _ -> _ -> exists _, _ /\ domain_list_simulation ?rs _,
        Hk : List.nth_error ?rs ?i = Some _,
        Hm : domain_simulation (d_ihfn ?ρ ?Bks ?p ?ups ?t ?i ?f) _, Hn : domain_simulation ?n ?n' |- _ =>
          inversion Hm; subst;
          match goal with |- exists _, $ᶠ| d_ihfn ?ρ' _ _ ?ups' _ _ ?f' & _ | _ ⍮ _ ↘ _ /\ _ =>
            let fn' := fresh "fn'" in let rs' := fresh "rs'" in let Hrs := fresh "Hrs" in let r' := fresh "r'" in
            let HB := fresh "HB" in let Hu := fresh "Hu" in let Hf := fresh "Hf" in
            assert (HB : blocks_agree Bks ρ ρ') by assumption;
            assert (Hu : domain_list_simulation ups ups') by assumption;
            assert (Hf : domain_simulation f f') by assumption;
            destruct (IHa f' n' Hf Hn) as (fn' & ? & ?);
            destruct (IHi ρ' ups' fn' HB Hu) as (rs' & ? & Hrs); [ assumption |];
            destruct (domain_list_simulation_nth_error _ _ _ _ Hrs Hk) as (r' & ? & ?);
            exists r'; split; [ econstructor; eassumption | assumption ] end
      end ].
    (** The family of the type of an argument of a function shape,
        applied: the shape's type in its environment extended by the
        argument *)
    all: try solve [ match goal with
      | IH : forall ups0 ρ0, domain_list_simulation ?ups ups0 ->
               env_agree (fun x => ~ ptyp_fresh x ?t) (?ρ ↦ ?n ⦂ entry_type_closure ?B ?ρ) ρ0 -> exists _, _ /\ _,
        Hm : domain_simulation (d_shfam ?p ?ups ?ρ ?B ?t) _, Hn : domain_simulation ?n ?n' |- _ =>
          inversion Hm; subst;
          match goal with |- exists _, $ᶠ| d_shfam _ ?ups' ?ρ' _ _ & _ | _ ⍮ _ ↘ _ /\ _ =>
            let a' := fresh "a'" in
            destruct (IH ups' (ρ' ↦ n' ⦂ entry_type_closure B ρ')) as (a' & ? & ?);
              [ assumption
              | intros [| y] Hy; cbn; [ constructor; exact Hn |];
                match goal with Hρ : forall x, ~ ptyp_fresh x (pt_pi B t) -> _ |- _ =>
                  apply Hρ; intros Hf; apply Hy; cbn in Hf; tauto end
              |];
            exists a'; split; [ econstructor; eassumption | assumption ] end
      (** The family of the type of a recursive result, applied: the
          function applied, then the type of the result at it *)
      | IHa : forall m0 n0, domain_simulation ?f m0 -> domain_simulation ?n n0 -> exists _, _ /\ _,
        IH : forall ups0 ρm0 ρ0 m0, domain_list_simulation ?ups ups0 -> ends_agree ?p ?As ?ρm ρm0 ?t ->
               env_agree (fun x => ~ ptyp_fresh x ?t) (?ρ ↦ ?n ⦂ entry_type_closure ?B ?ρ) ρ0 -> _ -> exists _, _ /\ domain_list_simulation ?as' _,
        Hk : List.nth_error ?as' ?i = Some _,
        Hm : domain_simulation (d_ihfam ?ρm ?As ?p ?ups ?ρ ?B ?t ?i ?f) _, Hn : domain_simulation ?n ?n' |- _ =>
          inversion Hm; subst;
          match goal with |- exists _, $ᶠ| d_ihfam ?ρm' _ _ ?ups' ?ρ' _ _ _ ?f' & _ | _ ⍮ _ ↘ _ /\ _ =>
            let fn' := fresh "fn'" in let as2 := fresh "as2" in let Has := fresh "Has" in let a' := fresh "a'" in
            let Hf := fresh "Hf" in
            assert (Hf : domain_simulation f f') by assumption;
            destruct (IHa f' n' Hf Hn) as (fn' & ? & ?);
            destruct (IH ups' ρm' (ρ' ↦ n' ⦂ entry_type_closure B ρ') fn') as (as2 & ? & Has);
              [ assumption | assumption
              | intros [| y] Hy; cbn; [ constructor; exact Hn |];
                match goal with Hρ : forall x, ~ ptyp_fresh x (pt_pi B t) -> _ |- _ =>
                  apply Hρ; intros Hfr; apply Hy; cbn in Hfr; tauto end
              | assumption |];
            destruct (domain_list_simulation_nth_error _ _ _ _ Has Hk) as (a' & ? & ?);
            exists a'; split; [ econstructor; eassumption | assumption ] end
      end ].
    (** The closure of a body, expanded: environments that agree where the
        unit may read, and so where its expansion may *)
    all: try solve [ match goal with
      | H : env_agree (fun x => ~ gunit_fresh x (gu_mk ?Δ (md_body ?sm ?Φ))) ?ρ ?ρ'
        |- exists _, ⟦ ?Δ ⊢ md_body ?sm ?Φ ⟧ᶜᶠ _ ⍮ _ ⍮ ?ρ' ↘ _ /\ _ =>
          eexists; split; [ econstructor | constructor ];
          eapply env_agree_mono; [ exact H |];
          let x := fresh "x" in let Hx := fresh "Hx" in let Hf := fresh "Hf" in
          intros x Hx Hf; apply Hx;
          exact (optional_gunit_fresh_expand (Some x) (gu_mk Δ (md_body sm Φ)) Hf)
      (** A closure lacking a parameter, applied: the unit in the
          environment extended by the argument *)
      | IH : forall ρ0, env_agree (fun x => ~ gunit_fresh x (gu_mk ?Δ ?D)) (?ρ ↦ ?n ⦂ entry_type_closure ?A ?ρ) ρ0 -> exists _, _ /\ _,
        Hh : dmod_simulation (dm_local ?Δ1 ?D ?ρ) _, Hn : domain_simulation ?n ?n' |- _ =>
          inversion Hh; subst;
          match goal with Hρ : forall x, ~ gunit_fresh x (gu_mk Δ1 D) -> dentry_simulation (env_entry ρ x) (env_entry ?ρ' x) |- _ =>
            let r' := fresh "r'" in
            destruct (IH (ρ' ↦ n' ⦂ entry_type_closure A ρ')) as (r' & ? & ?);
              [ intros [| y] Hy; cbn; [ constructor; exact Hn |];
                apply Hρ; intros Hf; apply Hy;
                exact (optional_gunit_fresh_snoc (Some y) _ _ _ Hf)
              |];
            exists r'; split; [ econstructor; eassumption | assumption ] end
      end ].
    (** A member of a body's closure: the body's environment up to the
        member, which agrees where the member's prefix may read, then the
        member's term in it *)
    all: try solve [ match goal with
      | Hp : gm_prefix_upto (gm_expand ?Φ) ?x = Some (gm_ext ?Φ' ?x ?E), He : entry_tm ?E = Some (?A, ?M),
        IHb : forall ρ0 (P : nat -> Prop), (forall z, ~ gmod_fresh z ?Φ' -> P z) -> env_agree P ?ρ ρ0 -> _,
        IHm : forall ρ0, env_agree (fun z => ~ exp_fresh z ?M) ?ρ1 ρ0 -> exists _, _ /\ _,
        Hh : dmod_simulation (dm_local nil (md_body ?sm ?Φ) ?ρ) _ |- _ =>
          inversion Hh; subst;
          match goal with |- exists _, dm_local _ _ ?ρ' ·ₜᶠ _ _ ⍮ _ ↘ _ /\ _ =>
            let ρ1' := fresh "ρ1'" in let Hab := fresh "Hab" in let r' := fresh "r'" in let Hρ := fresh "Hρ" in
            assert (Hρ : env_agree (fun z => ~ gunit_fresh z (gu_mk nil (md_body sm Φ))) ρ ρ') by assumption;
            destruct (IHb ρ' _ (gmod_fresh_ext_prefix Φ' x E) (env_agree_body_prefix _ _ _ _ _ _ Hp Hρ))
              as (ρ1' & ? & Hab);
            destruct (IHm ρ1' (env_agree_above_entry_tm _ _ _ _ _ _ _ _ He (fun _ h => h) Hab)) as (r' & ? & ?);
            exists r'; split; [ econstructor; eassumption | assumption ] end
      (** a submodule: its unit's closure in the environment up to it *)
      | Hp : gm_prefix_upto (gm_expand ?Φ) ?x = Some (gm_ext ?Φ' ?x ?E), He : entry_unit ?E = Some (gu_mk ?Δy ?Dy),
        IHb : forall ρ0 (P : nat -> Prop), (forall z, ~ gmod_fresh z ?Φ' -> P z) -> env_agree P ?ρ ρ0 -> _,
        IHm : forall ρ0, env_agree (fun z => ~ gunit_fresh z (gu_mk ?Δy ?Dy)) ?ρ1 ρ0 -> exists _, _ /\ _,
        Hh : dmod_simulation (dm_local nil (md_body ?sm ?Φ) ?ρ) _ |- _ =>
          inversion Hh; subst;
          match goal with |- exists _, dm_local _ _ ?ρ' ·ₘᶠ _ _ ⍮ _ ↘ _ /\ _ =>
            let ρ1' := fresh "ρ1'" in let Hab := fresh "Hab" in let r' := fresh "r'" in let Hρ := fresh "Hρ" in
            assert (Hρ : env_agree (fun z => ~ gunit_fresh z (gu_mk nil (md_body sm Φ))) ρ ρ') by assumption;
            destruct (IHb ρ' _ (gmod_fresh_ext_prefix Φ' x E) (env_agree_body_prefix _ _ _ _ _ _ Hp Hρ))
              as (ρ1' & ? & Hab);
            destruct (IHm ρ1' (env_agree_above_entry_unit _ _ _ _ _ _ _ He (fun _ h => h) Hab)) as (r' & ? & ?);
            exists r'; split; [ econstructor; eassumption | assumption ] end
      end ].
    (** The environment a body's members see: the empty body adds
        nothing; each member adds a related entry over the environment of
        its prefix, which agrees above as the extended one did *)
    all: try solve [ match goal with
      | |- exists _, ⟦ gm_nil ⟧ᵇᶠ _ ⍮ _ ⍮ ?ρ' ↘ _ /\ _ =>
          exists ρ'; split; [ constructor | apply env_agree_above_zero; assumption ]
      end ].
    all: try solve [ match goal with
      | IHb : forall ρ0 (P0 : nat -> Prop), (forall z, ~ gmod_fresh z ?Φ -> P0 z) -> env_agree P0 ?ρ ρ0 -> _,
        HP : forall z, ~ gmod_fresh z (gm_ext ?Φ ?y ?E) -> ?P z,
        Hρ : env_agree ?P ?ρ ?ρ' |- _ =>
          let ρ1' := fresh "ρ1'" in let Hab := fresh "Hab" in
          destruct (IHb ρ' P (fun z h => HP z (gmod_fresh_ext_prefix _ y E z h)) Hρ) as (ρ1' & ? & Hab);
          first
            [ (** a definition with a module part: both parts *)
              match goal with
              | IHm : forall ρ0, env_agree (fun z => ~ exp_fresh z ?M) _ ρ0 -> exists _, _ /\ _,
                IHu : forall ρ0, env_agree (fun z => ~ gunit_fresh z ?U) _ ρ0 -> exists _, _ /\ _ |- _ =>
                  let m' := fresh "m'" in let h' := fresh "h'" in
                  destruct (IHm ρ1' (env_agree_above_entry_tm Φ y E _ M P _ _ eq_refl HP Hab)) as (m' & ? & ?);
                  destruct (IHu ρ1' (env_agree_above_entry_unit Φ y E U P _ _ eq_refl HP Hab)) as (h' & ? & ?);
                  eexists; split; [ eapply fast_eval_body_env_dm; eassumption |];
                  apply env_agree_above_cons; [ exact Hab | constructor; assumption ]
              end
            | (** a definition: its value *)
              match goal with
              | IHm : forall ρ0, env_agree (fun z => ~ exp_fresh z ?M) _ ρ0 -> exists _, _ /\ _ |- _ =>
                  let m' := fresh "m'" in
                  destruct (IHm ρ1' (env_agree_above_entry_tm Φ y E _ M P _ _ eq_refl HP Hab)) as (m' & ? & ?);
                  eexists; split; [ eapply fast_eval_body_env_def; eassumption |];
                  apply env_agree_above_cons; [ exact Hab | constructor; assumption ]
              end
            | (** a submodule: its unit's closure *)
              match goal with
              | IHu : forall ρ0, env_agree (fun z => ~ gunit_fresh z ?U) _ ρ0 -> exists _, _ /\ _ |- _ =>
                  let h' := fresh "h'" in
                  destruct (IHu ρ1' (env_agree_above_entry_unit Φ y E U P _ _ eq_refl HP Hab)) as (h' & ? & ?);
                  eexists; split; [ eapply fast_eval_body_env_mod; eassumption |];
                  apply env_agree_above_cons; [ exact Hab | constructor; assumption ]
              end
            | (** a proposition: kept on both sides *)
              eexists; split; [ eapply fast_eval_body_env_def_proof; eassumption |];
              apply env_agree_above_cons; [ exact Hab | constructor; constructor ] ]
      end ].
    (** The eliminator on a constructor: the recursive results the branch
        reads, then the branch, in the environment of the non-uniform
        parameters, the arguments and the results, related where the
        branch reads *)
    all: try solve [ match goal with
      | Hm : domain_simulation (d_con _ _ _ _) ?m' |- exists _, ⟦elimᶠ ?m' at _ of _ _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
          inversion Hm; subst; clear Hm;
          match goal with
          | IHi : forall ρ0 ups0 vs0 oB0, blocks_agree ?Bks ?ρ ρ0 -> domain_list_simulation ?ups ups0 ->
                  domain_list_simulation (skipn _ ?vs) vs0 -> ihs_coherent ?p oB0 -> exists _, _ /\ _,
            IHB : forall ρ0, env_agree (fun x => ~ exp_fresh x ?B) (env_extend_typed ?ρ _) ρ0 -> exists _, _ /\ _,
            HBk : blocks_agree ?Bks ?ρ ?ρ', Hu : domain_list_simulation ?ups ?ups',
            Hvs : domain_list_simulation ?vs ?vs', Hb : nth_error ?Bks _ = Some ?bk,
            Hbr : brs_lookup (eb_brs ?bk) ?c = Some (?n, ?B),
            Hl : List.length ?vs = (im_np ?Dq ?Mk + List.length ?gs)%nat,
            Hlk : ind_lookup _ _ ?p = Some ?D, Hmj : ind_member ?D _ = Some ?Mj, Hco : leaves_coherent ?D,
            Hih : ⟦ihs _ of ?gs under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?ihs |- _ =>
              let ihs' := fresh "ihs'" in let Hihs' := fresh "Hihs'" in let Hsi := fresh "Hsi" in
              let r' := fresh "r'" in let Hcoh := fresh "Hcoh" in
              assert (Hcoh : ihs_coherent p (Some B))
                by (let D0 := fresh "D0" in let HD0 := fresh "HD0" in
                    intros D0 HD0; rewrite Hlk in HD0; injection HD0 as <-; exact Hco);
              destruct (IHi ρ' ups' (skipn (im_np Dq Mk) vs') (Some B) HBk Hu (domain_list_simulation_skipn _ _ _ Hvs) Hcoh)
                as (ihs' & Hihs' & Hsi); cbn [ihs_read] in Hsi;
              destruct (IHB (env_extend_typed ρ' (branch_entries D Mj p ups' (blocks_motives Bks) ρ' gs
                              (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs')) (skipn (im_np Dq Mk) vs') ihs')))
                as (r' & ? & ?);
                [ eapply env_agree_binders_at;
                    [ exact (proj2 (HBk _ (nth_error_In _ _ Hb)) _ _ _ (brs_lookup_in _ _ _ _ Hbr))
                    | rewrite !branch_entries_map_fst; apply domain_list_simulation_at_app;
                        [ apply domain_list_simulation_skipn, domain_list_simulation_firstn, Hvs
                        | apply domain_list_simulation_at_app; [ apply domain_list_simulation_skipn, Hvs | exact Hsi ] ]
                    | rewrite branch_entries_length, !List.length_skipn, List.length_firstn,
                        (proj2 (eval_ihs_length _ _ _ _ _ _ _ _ Hlk Hco Hih)), Hl;
                      unfold im_np; lia ]
                |];
              exists r'; split;
                [ eapply fast_eval_elim_con; try eassumption; try reflexivity;
                  rewrite <- (domain_list_simulation_length _ _ Hvs); exact Hl
                | assumption ]
          end
      end ].
    (** The eliminator on a neutral: the motive's instance, and a stuck
        eliminator over environments that agree where the blocks read *)
    all: try solve [ match goal with
      | Hm : domain_simulation (⇑ (d_ind _ _ _) _) ?m' |- exists _, ⟦elimᶠ ?m' at _ of _ _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
          inversion Hm; subst; clear Hm;
          match goal with Ha : domain_simulation (d_ind _ _ _) _ |- _ => inversion Ha; subst; clear Ha end;
          match goal with
          | IHr : forall ups0, domain_list_simulation ?ups ups0 -> exists _, ⟦mrefᶠ _ of _ ups0 ⟧ᶠ _ ⍮ _ ↘ _ /\ _,
            IHa : forall ρ0, env_agree (fun x => ~ exp_fresh x (eb_motive ?bk)) (env_extend_typed ?ρ _) ρ0 -> exists _, _ /\ _,
            HBk : blocks_agree ?Bks ?ρ ?ρ', Hb : nth_error ?Bks _ = Some ?bk, Hc : eb_binder_count ?bk = S (im_nn ?Mk),
            Has : domain_list_simulation ?as' ?as'', Hn : domain_ne_simulation ?m ?m'', Hu : domain_list_simulation ?ups ?ups',
            Hl : List.length ?as' = im_np ?Dq ?Mk, Hlk : ind_lookup _ _ ?p = Some ?D, Hmj : ind_member ?D _ = Some ?Mj
            |- exists _, ⟦elimᶠ ⇑ (d_ind ?pc ?k ?as'') ?m'' at _ of _ _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
              let pre' := fresh "pre'" in let a' := fresh "a'" in
              destruct (IHr ups' Hu) as (pre' & ? & ?);
              destruct (IHa (env_extend_typed ρ' (motive_entries D Mj ups' (skipn (ind_nu Dq) as'')
                              (d_ind pc k (pre' ++ skipn (ind_nu Dq) as'')) (⇑ (d_ind pc k as'') m''))))
                as (a' & ? & ?);
                [ eapply env_agree_binders;
                    [ exact (proj1 (HBk _ (nth_error_In _ _ Hb)))
                    | unfold typed_simulation; rewrite !motive_entries_map_fst;
                      apply domain_list_simulation_app;
                        [ apply domain_list_simulation_skipn, Has | repeat constructor; assumption ]
                    | rewrite motive_entries_length, List.length_skipn, Hl, Hc; unfold im_np; lia ]
                |];
              eexists; split;
                [ eapply fast_eval_elim_neut; try eassumption;
                  rewrite <- (domain_list_simulation_length _ _ Has); exact Hl
                | constructor; [ assumption | apply domain_ne_simulation_elim; [ exact HBk | exact Hu | exact Has | exact Hn ] ] ]
          end
      end ].
    (** The recursive results: those of an argument are computed when the
        branch reads one of them, and skipped when it reads none, as the
        fast rule decides; skipped ones are as many as the argument's leaf
        paths, the group's table being coherent. *)
    all: try solve [ eexists; split; [ constructor | constructor ] ].
    all: try solve [ match goal with
      | Hvs0 : domain_list_simulation (_ :: _) ?vs0' |- exists _, ⟦ihsᶠ ?vs0' of _ :: _ under _ _ _ for _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
          inversion Hvs0; subst; clear Hvs0;
          match goal with
          | IH : forall ρ0 ups0 vs0 oB0, blocks_agree ?Bks ?ρ ρ0 -> domain_list_simulation ?ups ups0 ->
                 domain_list_simulation ?vs vs0 -> ihs_coherent ?p oB0 -> exists _, _ /\ _,
            HB : blocks_agree ?Bks ?ρ ?ρ', Hu : domain_list_simulation ?ups ?ups', Hvs : domain_list_simulation ?vs ?vs',
            Hc : ihs_coherent ?p ?oB
            |- exists _, ⟦ihsᶠ _ of ca_arg _ _ :: _ under _ _ _ for _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
              let ihs' := fresh "ihs'" in
              destruct (IH ρ' ups' vs' oB HB Hu Hvs Hc) as (ihs' & ? & ?);
              exists ihs'; split; [ constructor; eassumption | assumption ]
          | IHi : forall ρ0 ups0 m0, blocks_agree ?Bks ?ρ ρ0 -> domain_list_simulation ?ups ups0 -> domain_simulation ?v m0 ->
                  exists _, ⟦ihᶠ _ of _ under _ _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _,
            IHs : forall ρ0 ups0 vs0 oB0, blocks_agree ?Bks ?ρ ρ0 -> domain_list_simulation ?ups ups0 ->
                  domain_list_simulation ?vs vs0 -> ihs_coherent ?p oB0 -> exists _, _ /\ _,
            Hi : ⟦ih ?v of ?t under ?p ?ups ?Bks ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?ihs1,
            Hs : ⟦ihs ?vs of ?gs under ?p ?ups ?Bks ⟧ _ ⍮ _ ⍮ ?ρ ↘ ?ihs,
            HB : blocks_agree ?Bks ?ρ ?ρ', Hu : domain_list_simulation ?ups ?ups', Hv : domain_simulation ?v ?v',
            Hvs : domain_list_simulation ?vs ?vs', Hc : ihs_coherent ?p ?oB
            |- exists _, ⟦ihsᶠ _ of ca_rec ?t :: ?gs under _ _ _ for _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
              let D := fresh "D" in let HD := fresh "HD" in let ihs' := fresh "ihs'" in let Hsi := fresh "Hsi" in
              let Hsk := fresh "Hsk" in
              destruct (eval_ih_lookup _ _ _ _ _ _ _ Hi) as (D & HD);
              destruct (IHs ρ' ups' vs' oB HB Hu Hvs Hc) as (ihs' & ? & Hsi);
              destruct (ihs_skip_at skip_on oB (cargs_nrec D gs) (List.length (shape_leaves (rview_leaves D) 0 t))) eqn:Hsk;
              [ let B := fresh "B" in let HBf := fresh "HBf" in let Hco := fresh "Hco" in let Hli := fresh "Hli" in
                destruct (ihs_skip_at_sound _ _ _ _ Hsk) as (_ & B & -> & HBf);
                pose proof (Hc D HD) as Hco;
                pose proof (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Hi _ HD Hco) as Hli;
                exists (List.repeat 𝕌ω@0 (List.length (shape_leaves (rview_leaves D) 0 t)) ++ ihs'); split;
                [ eapply fast_eval_ihs_skip; eassumption
                | apply domain_list_simulation_at_skip;
                  [ rewrite List.repeat_length; exact Hli
                  | let i0 := fresh "i0" in let Hi0 := fresh "Hi0" in let Hn := fresh "Hn" in
                    intros i0 Hi0; cbn [ihs_read]; rewrite (proj2 (eval_ihs_length _ _ _ _ _ _ _ _ HD Hco Hs));
                    intros Hn; apply Hn, HBf; rewrite Hli in Hi0; exact Hi0
                  | exact Hsi ] ]
              | let ih' := fresh "ih'" in
                destruct (IHi ρ' ups' v' HB Hu Hv) as (ih' & ? & ?);
                exists (ih' ++ ihs'); split;
                  [ eapply fast_eval_ihs_rec; eassumption | apply domain_list_simulation_at_app; assumption ] ]
          end
      end ].
    (** The recursive results of an argument: at a member with a block,
        the eliminator; at a record view, those of its fields at the
        projections; at a function shape, one closure per leaf path *)
    all: try solve [ match goal with
      | IH : forall ρ0 ups0 m0, blocks_agree ?Bks ?ρ ρ0 -> domain_list_simulation ?ups ups0 -> domain_simulation ?v m0 ->
             exists _, ⟦elimᶠ _ at _ of _ _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _,
        HB : blocks_agree ?Bks ?ρ ?ρ', Hu : domain_list_simulation ?ups ?ups', Hv : domain_simulation ?v ?v'
        |- exists _, ⟦ihᶠ _ of pt_self _ _ under _ _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ domain_list_simulation (_ :: nil) _ =>
          let r' := fresh "r'" in
          destruct (IH ρ' ups' v' HB Hu Hv) as (r' & ? & ?); exists (r' :: nil); split;
            [ econstructor; eassumption | repeat constructor; assumption ]
      | IHp : forall v0, domain_simulation ?v v0 -> exists _, ⟦projsᶠ _ of v0 ⟧ᶠ _ ⍮ _ ↘ _ /\ _,
        IHs : forall ρ0 ups0 vs0 oB0, blocks_agree ?Bks ?ρ ρ0 -> domain_list_simulation ?ups ups0 ->
              domain_list_simulation ?ws vs0 -> ihs_coherent _ oB0 -> exists _, _ /\ _,
        HB : blocks_agree ?Bks ?ρ ?ρ', Hu : domain_list_simulation ?ups ?ups', Hv : domain_simulation ?v ?v'
        |- exists _, ⟦ihᶠ _ of _ under _ _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
          let ws' := fresh "ws'" in let Hws := fresh "Hws" in let rs' := fresh "rs'" in let Hrs := fresh "Hrs" in
          destruct (IHp v' Hv) as (ws' & ? & Hws); destruct (IHs ρ' ups' ws' None HB Hu Hws I) as (rs' & ? & Hrs);
          exists rs'; split; [ econstructor; eassumption | apply domain_list_simulation_at_true; exact Hrs ]
      | HB : blocks_agree ?Bks ?ρ ?ρ', Hu : domain_list_simulation ?ups ?ups', Hv : domain_simulation ?v ?v',
        e : ind_lookup _ _ ?p = Some ?D
        |- exists _, ⟦ihᶠ _ of pt_pi _ _ under ?p _ ?Bks ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
          eexists; split; [ econstructor; exact e | apply domain_list_simulation_map_ihfn; assumption ]
      end ].
    (** A view's container member, and a record view's type: the view's
        arguments over related uniform parameters *)
    all: try solve [ match goal with
      | IH : forall ρ0, env_agree (fun x => ~ Forall (exp_fresh x) ?Is) (decl_env ?D ?ups) ρ0 -> exists _, _ /\ _,
        Hu : domain_list_simulation ?ups ?ups', Hh : im_head _ = mh_view _ _ _ _
        |- exists _, ⟦mrefᶠ _ of _ ?ups' ⟧ᶠ _ ⍮ _ ↘ _ /\ _ =>
          let ms' := fresh "ms'" in
          destruct (IH (decl_env D ups') (env_agree_decl_env _ _ _ _ Hu)) as (ms' & ? & ?);
          exists ms'; split; [ eapply fast_eval_mref_view; eassumption | assumption ]
      | IH : forall ρ0, env_agree (fun x => ~ Forall (exp_fresh x) ?Is) (decl_env ?D ?ups) ρ0 -> exists _, _ /\ _,
        Hu : domain_list_simulation ?ups ?ups', Hh : im_head _ = mh_record _ _ _
        |- exists _, ⟦shtyᶠ pt_self _ _ of _ ?ups' ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
          let ms' := fresh "ms'" in
          destruct (IH (decl_env D ups') (env_agree_decl_env _ _ _ _ Hu)) as (ms' & ? & ?);
          eexists; split; [ eapply fast_eval_shape_type_rview; eassumption | constructor; assumption ]
      end ].
    (** A function shape's type: a [Π] over its domain, of the shape
        family over the environment the shape reads *)
    all: try solve [ match goal with
      | IH : forall ρ0, env_agree (fun x => ~ exp_fresh x ?B) ?ρ ρ0 -> exists _, _ /\ _,
        Hu : domain_list_simulation ?ups ?ups', Hρ : env_agree (fun x => ~ ptyp_fresh x (pt_pi ?B ?t)) ?ρ ?ρ'
        |- exists _, ⟦shtyᶠ pt_pi _ _ of _ ?ups' ⟧ᶠ _ ⍮ _ ⍮ ?ρ' ↘ _ /\ _ =>
          let b' := fresh "b'" in
          destruct (IH ρ' (env_agree_pi_domain _ _ _ _ Hρ)) as (b' & ? & ?);
          eexists; split;
            [ eapply fast_eval_shape_type_pi; eassumption
            | apply domain_simulation_fam_pi; [ assumption | constructor; [ exact Hu | exact Hρ ] ] ]
      end ].
    (** The types of the recursive results of an argument: at a member
        with a block, its motive at the shape's parameters and the
        argument; at a record view, those of its fields; at a function
        shape, one family per leaf path *)
    all: try solve [ match goal with
      | Hea : ends_agree ?p ?As ?ρm ?ρm' (pt_self ?j ?Ps), Hl : ind_lookup _ _ ?p = Some ?D,
        Hm : ind_member ?D ?j = Some ?Mj, Hr : im_is_rview ?Mj = false,
        e2 : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ ?ρ ↘ ?bs,
        IHP : forall ρ0, env_agree (fun x => ~ Forall (exp_fresh x) ?Ps) ?ρ ρ0 -> exists _, _ /\ _,
        IH : forall ρ0, env_agree _ (env_extend_typed ?ρm _) ρ0 -> exists _, _ /\ _,
        Hu : domain_list_simulation ?ups ?ups', Hρ : env_agree (fun x => ~ ptyp_fresh x (pt_self ?j ?Ps)) ?ρ ?ρ',
        Hv : domain_simulation ?v ?v'
        |- exists _, ⟦ihtyᶠ ?v' of pt_self _ _ at _ ?ups' under ?ρm' _ ⟧ᶠ _ ⍮ _ ⍮ ?ρ' ↘ _ /\ _ =>
          let bs' := fresh "bs'" in let Hbs := fresh "Hbs" in let a' := fresh "a'" in
          let D0 := fresh "D0" in let HD0 := fresh "HD0" in let HM0 := fresh "HM0" in let HA0 := fresh "HA0" in
          inversion Hea as [? ? ? ? D0 ? ? ? HD0 HM0 ? HA0 | ? ? ? ? D0 ? ? ? ? ? ? HD0 HM0 ? ? |]; subst;
          rewrite Hl in HD0; injection HD0 as <-; rewrite Hm in HM0; injection HM0 as <-;
          [| exfalso; unfold im_is_rview in Hr; match goal with Hh : im_head _ = mh_record _ _ _ |- _ => rewrite Hh in Hr end;
             discriminate Hr ];
          destruct (IHP ρ' Hρ) as (bs' & ? & Hbs);
          destruct (IH (env_extend_typed ρm' (tele_entries (decl_env D ups') (List.rev (im_nparams Mj)) bs' ++
                                                (v', entry_type_shape p ups' ρ' (pt_self j Ps)) :: nil)))
            as (a' & ? & ?);
            [ eapply env_agree_binders;
                [ exact HA0
                | unfold typed_simulation; rewrite !List.map_app, !tele_entries_values;
                  apply domain_list_simulation_app; [ exact Hbs | repeat constructor; assumption ]
                | rewrite List.length_app, tele_entries_values_length, (eval_exps_length _ _ _ e2); cbn; lia ]
            |];
          exists (a' :: nil); split; [ eapply fast_eval_ihty_self; eassumption | repeat constructor; assumption ]
      | Hea : ends_agree ?p ?As ?ρm ?ρm' (pt_self ?j ?Ps), Hl : ind_lookup _ _ ?p = Some ?D,
        Hm : ind_member ?D ?j = Some ?Mj, Hh : im_head ?Mj = mh_record _ _ _, Hc : im_cons ?Mj = (_, ?gs) :: nil,
        IHp : forall v0, domain_simulation ?v v0 -> exists _, ⟦projsᶠ _ of v0 ⟧ᶠ _ ⍮ _ ↘ _ /\ _,
        IH : forall ups0 ρm0 ρ0 vs0, domain_list_simulation ?ups ups0 -> _ -> env_agree _ (decl_env ?D ?ups) ρ0 -> _ ->
             exists _, _ /\ _,
        Hu : domain_list_simulation ?ups ?ups', Hv : domain_simulation ?v ?v'
        |- exists _, ⟦ihtyᶠ ?v' of pt_self _ _ at _ ?ups' under ?ρm' _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
          let ws' := fresh "ws'" in let Hws := fresh "Hws" in let rs' := fresh "rs'" in
          let D0 := fresh "D0" in let HD0 := fresh "HD0" in let HM0 := fresh "HM0" in let HR0 := fresh "HR0" in
          let HF := fresh "HF" in
          inversion Hea as [? ? ? ? D0 ? ? ? HD0 HM0 HR0 ? | ? ? ? ? D0 ? ? ? ? ? ? HD0 HM0 ? HF |]; subst;
          rewrite Hl in HD0; injection HD0 as <-; rewrite Hm in HM0; injection HM0 as <-;
          [ exfalso; unfold im_is_rview in HR0; rewrite Hh in HR0; discriminate HR0 |];
          destruct (IHp v' Hv) as (ws' & ? & Hws);
          destruct (IH ups' ρm' (decl_env D ups') ws' Hu) as (rs' & ? & ?);
            [ let gs1 := fresh "gs1" in let t := fresh "t" in let gs2 := fresh "gs2" in let E := fresh "E" in
              intros gs1 t gs2 E; eapply HF; [ exact Hc | exact E ]
            | apply env_agree_decl_env; exact Hu | exact Hws |];
          exists rs'; split;
            [ eapply fast_eval_ihty_rview; [ exact Hl | exact Hm | exact Hh | exact Hc | eassumption | eassumption ]
            | assumption ]
      | Hea : ends_agree _ _ _ _ (pt_pi _ _), IH : forall ρ0, env_agree (fun x => ~ exp_fresh x ?B) ?ρ ρ0 -> exists _, _ /\ _,
        Hu : domain_list_simulation ?ups ?ups', Hρ : env_agree (fun x => ~ ptyp_fresh x (pt_pi ?B _)) ?ρ ?ρ',
        Hv : domain_simulation _ ?v', e : ind_lookup _ _ _ = Some _
        |- exists _, ⟦ihtyᶠ ?v' of pt_pi _ _ at _ _ under _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
          let Ht := fresh "Ht" in let b' := fresh "b'" in
          inversion Hea as [| | ? ? ? ? ? ? Ht]; subst;
          destruct (IH ρ' (env_agree_pi_domain _ _ _ _ Hρ)) as (b' & ? & ?);
          eexists; split;
            [ eapply fast_eval_ihty_pi; eassumption
            | apply domain_list_simulation_map_ihfam; [ assumption | exact Ht | exact Hu | exact Hρ | exact Hv ] ]
      end ].
    (** The types of the recursive results of fields, along them *)
    all: try solve [ match goal with
      | |- exists _, ⟦ihtysᶠ _ of nil at _ _ under _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
          match goal with Hvs : domain_list_simulation nil _ |- _ => inversion Hvs; subst end;
          exists nil; split; constructor
      | Hvs0 : domain_list_simulation (_ :: _) ?vs0' |- exists _, ⟦ihtysᶠ ?vs0' of _ :: _ at _ _ under _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
          inversion Hvs0; subst; clear Hvs0;
          match goal with
          | IH : forall ups0 ρm0 ρ0 vs0, domain_list_simulation ?ups ups0 -> _ ->
                 env_agree _ (?ρ ↦ ?v ⦂ _) ρ0 -> domain_list_simulation ?vs vs0 -> exists _, _ /\ _,
            Hu : domain_list_simulation ?ups ?ups', HA : forall gs1 t gs2, _ -> ends_agree _ _ _ ?ρm' _,
            Hρ : env_agree (fun _ => True) ?ρ ?ρ', Hv : domain_simulation ?v ?v', Hvs : domain_list_simulation ?vs ?vs'
            |- exists _, ⟦ihtysᶠ _ of ca_arg ?ra ?T :: _ at _ _ under _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
              let rs' := fresh "rs'" in
              destruct (IH ups' ρm' (ρ' ↦ v' ⦂ entry_type_closure T ρ') vs' Hu) as (rs' & ? & ?);
                [ let gs1 := fresh "gs1" in let t := fresh "t" in let gs2 := fresh "gs2" in let E := fresh "E" in
                  intros gs1 t gs2 E; apply (HA (ca_arg ra T :: gs1) t gs2); rewrite E; reflexivity
                | apply env_agree_all_cons; assumption | exact Hvs |];
              exists rs'; split; [ constructor; eassumption | assumption ]
          | IHt : forall ups0 ρm0 ρ0 m0, domain_list_simulation ?ups ups0 -> ends_agree _ _ _ ρm0 ?t ->
                  env_agree _ ?ρ ρ0 -> domain_simulation ?v m0 -> exists _, _ /\ _,
            IH : forall ups0 ρm0 ρ0 vs0, domain_list_simulation ?ups ups0 -> _ -> env_agree _ ?ρ ρ0 ->
                 domain_list_simulation ?vs vs0 -> exists _, _ /\ _,
            Hu : domain_list_simulation ?ups ?ups', HA : forall gs1 t0 gs2, ca_rec ?t :: _ = _ -> ends_agree _ _ _ ?ρm' _,
            Hρ : env_agree (fun _ => True) ?ρ ?ρ', Hv : domain_simulation ?v ?v', Hvs : domain_list_simulation ?vs ?vs'
            |- exists _, ⟦ihtysᶠ _ of ca_rec _ :: _ at _ _ under _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
              let rs1' := fresh "rs1'" in let rs' := fresh "rs'" in
              destruct (IHt ups' ρm' ρ' v' Hu (HA nil t _ eq_refl)) as (rs1' & ? & ?);
                [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] | exact Hv |];
              destruct (IH ups' ρm' ρ' vs' Hu) as (rs' & ? & ?);
                [ let gs1 := fresh "gs1" in let t0 := fresh "t0" in let gs2 := fresh "gs2" in let E := fresh "E" in
                  intros gs1 t0 gs2 E; apply (HA (ca_rec t :: gs1) t0 gs2); rewrite E; reflexivity
                | exact Hρ | exact Hvs |];
              exists (rs1' ++ rs'); split; [ econstructor; eassumption | apply domain_list_simulation_app; assumption ]
          end
      end ].
    (** Records: a field of a tuple, the projections of a neutral at its
        record's fields, and projections along a path *)
    all: try solve [ match goal with
      | Hl : field_lookup ?vs ?f = Some _, Hs : domain_simulation (d_tuple ?vs) _ |- _ =>
          inversion Hs; subst;
          match goal with Hfs : domain_fields_simulation vs _ |- _ =>
            let r' := fresh "r'" in
            destruct (field_lookup_sim _ _ _ _ Hfs Hl) as (r' & ? & ?);
            exists r'; split; [ constructor; assumption | assumption ] end
      | IH : forall m0 ρ0, domain_ne_simulation ?m m0 -> env_agree _ (env_tele nil _ ?ns) ρ0 -> exists _, _ /\ _,
        Hk : List.nth_error ?rs ?k = Some _, Hs : domain_simulation (⇑ (d_record _ ?ns) ?m) _ |- _ =>
          inversion Hs; subst;
          match goal with Ha : domain_simulation (d_record _ _) _ |- _ => inversion Ha; subst end;
          match goal with Hns : domain_list_simulation ns ?ns', Hm : domain_ne_simulation m ?m' |- _ =>
            let rs' := fresh "rs'" in let r' := fresh "r'" in let Hrs := fresh "Hrs" in
            destruct (IH m' _ Hm (env_agree_tele_nil _ _ _ _ Hns)) as (rs' & ? & Hrs);
            destruct (domain_list_simulation_nth_error _ _ _ _ Hrs Hk) as (r' & ? & ?);
            exists r'; split; [ econstructor; eassumption | assumption ] end
      | |- exists _, fast_eval_neutral_fields _ _ _ _ nil _ /\ _ => eexists; split; constructor
      | IHT : forall ρ0, env_agree (fun x => ~ exp_fresh x ?T) ?ρ ρ0 -> exists _, _ /\ _,
        IH : forall m0 ρ0, domain_ne_simulation ?m m0 -> env_agree _ (?ρ ↦ _ ⦂ _) ρ0 -> exists _, _ /\ _,
        Hm : domain_ne_simulation ?m ?m', Hρ : env_agree (fun _ => True) ?ρ ?ρ'
        |- exists _, fast_eval_neutral_fields _ _ _ _ ((?g, _) :: _) _ /\ _ =>
          let a' := fresh "a'" in let rs' := fresh "rs'" in
          destruct (IHT ρ' (env_agree_mono _ _ _ _ Hρ (fun _ _ => I))) as (a' & ? & ?);
          destruct (IH m' (ρ' ↦ ⇑ a' (d_proj g m') ⦂ entry_type_closure T ρ') Hm) as (rs' & ? & ?);
            [ apply env_agree_all_cons; [ exact Hρ | constructor; [ assumption | constructor; exact Hm ] ] |];
          eexists; split; [ econstructor; eassumption | constructor; [ constructor; [ assumption | constructor; exact Hm ] | assumption ] ]
      | |- exists _, ⟦projsᶠ nil of _ ⟧ᶠ _ ⍮ _ ↘ _ /\ _ => exists nil; split; constructor
      | IHf : forall m0, domain_simulation ?v m0 -> exists _, fast_eval_proj _ _ _ m0 _ /\ _,
        IHr : forall v0, domain_simulation ?v v0 -> exists _, ⟦projsᶠ _ of v0 ⟧ᶠ _ ⍮ _ ↘ _ /\ _, Hv : domain_simulation ?v ?v'
        |- exists _, ⟦projsᶠ _ :: _ of _ ⟧ᶠ _ ⍮ _ ↘ _ /\ _ =>
          let w' := fresh "w'" in let ws' := fresh "ws'" in
          destruct (IHf v' Hv) as (w' & ? & ?); destruct (IHr v' Hv) as (ws' & ? & ?);
          exists (w' :: ws'); split; [ econstructor; eassumption | constructor; assumption ]
      end ].
  Qed.
End Eval.

Section Read.

  Lemma fast_eval_exp_sim : forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> forall ρ', env_agree (fun x => ~ exp_fresh x M) ρ ρ' ->
      exists m', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ m' /\ domain_simulation m m'.
  Proof. exact (proj1 fast_eval_sim). Qed.

  Lemma fast_eval_app_sim : forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> forall m' n', domain_simulation m m' -> domain_simulation n n' ->
      exists r', $ᶠ| m' & n' | Θ ⍮ Ξ ↘ r' /\ domain_simulation r r'.
  Proof. exact (proj1 (proj2 fast_eval_sim)). Qed.

  Lemma fast_eval_exps_sim : forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> forall ρ', env_agree (fun x => ~ Forall (exp_fresh x) Ms) ρ ρ' ->
      exists ms', ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ms' /\ domain_list_simulation ms ms'.
  Proof. exact (proj1 (proj2 (proj2 fast_eval_sim))). Qed.

  Lemma fast_eval_modexp_sim : forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall ρ', env_agree (fun x => ~ modexp_fresh x H) ρ ρ' ->
      exists h', ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ' ↘ h' /\ dmod_simulation h h'.
  Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 fast_eval_sim))))). Qed.

  (** A closure, at one or two related arguments. *)
  Lemma fast_eval_clo_sim : forall B (ρ ρ' : env) c c' t t' b,
      env_agree (fun x => ~ exp_fresh (S x) B) ρ ρ' -> domain_simulation c c' -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ⦂ t ↘ b ->
      exists b', ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ (ρ' ↦ c' ⦂ t') ↘ b' /\ domain_simulation b b'.
  Proof.
    intros * Hρ Hc Hb; eapply fast_eval_exp_sim; [ exact Hb |].
    intros [| x] Hx; cbn; [ constructor; exact Hc | apply Hρ, Hx ].
  Qed.

  (** A closure that does not read its argument, at any argument. *)
  Lemma fast_eval_clo_unread : forall B (ρ ρ' : env) c c' t t' b,
      env_agree (fun x => ~ exp_fresh (S x) B) ρ ρ' -> exp_fresh 0 B -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ⦂ t ↘ b ->
      exists b', ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ (ρ' ↦ c' ⦂ t') ↘ b' /\ domain_simulation b b'.
  Proof.
    intros * Hρ H0 Hb; eapply fast_eval_exp_sim; [ exact Hb |].
    intros [| x] Hx; cbn; [ contradiction | apply Hρ, Hx ].
  Qed.

  Lemma fast_eval_clo2_sim : forall B (ρ ρ' : env) c1 c1' c2 c2' t1 t1' t2 t2' b,
      env_agree (fun x => ~ exp_fresh (S (S x)) B) ρ ρ' -> domain_simulation c1 c1' -> domain_simulation c2 c2' ->
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c1 ⦂ t1 ↦ c2 ⦂ t2 ↘ b ->
      exists b', ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ (ρ' ↦ c1' ⦂ t1' ↦ c2' ⦂ t2') ↘ b' /\ domain_simulation b b'.
  Proof.
    intros * Hρ Hc1 Hc2 Hb; eapply fast_eval_exp_sim; [ exact Hb |].
    intros [| [| x]] Hx; cbn; [ constructor; exact Hc2 | constructor; exact Hc1 | apply Hρ, Hx ].
  Qed.

  (** The fresh variables of the telescopes of a declaration, from
      environments related everywhere. *)
  Lemma fast_fresh_tele_sim : forall ρ T s ns, Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ns ->
      forall ρ', env_agree (fun _ => True) ρ ρ' ->
      exists ns', Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ ns' /\ domain_list_simulation ns ns'.
  Proof.
    induction 1; intros ρ' Hρ; [ exists nil; split; constructor |].
    destruct (fast_eval_exp_sim _ _ _ H ρ') as (a' & Ha' & Hsa); [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |].
    assert (Hv : domain_simulation (⇑! a s) (⇑! a' s)) by (repeat constructor; assumption).
    destruct (IHfresh_tele (ρ' ↦ ⇑! a' s ⦂ entry_type_closure A ρ')) as (ns' & ? & ?);
      [ apply env_agree_all_cons; [ exact Hρ | exact Hv ] |].
    exists (⇑! a' s :: ns'); split; [ constructor; assumption | constructor; assumption ].
  Qed.

  Lemma fast_eval_ih_sim : forall ρ p ups Bks t m r, ⟦ih m of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> forall ρ' ups' m',
      blocks_agree Bks ρ ρ' -> domain_list_simulation ups ups' -> domain_simulation m m' ->
      exists r', ⟦ihᶠ m' of t under p ups' Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ domain_list_simulation r r'.
  Proof.
    intros * H; destruct fast_eval_sim as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _).
    exact (Hi _ _ _ _ _ _ _ H).
  Qed.

  Lemma fast_eval_mref_sim : forall p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r -> forall ups', domain_list_simulation ups ups' ->
      exists pre', ⟦mrefᶠ j of p ups' ⟧ᶠ Θ ⍮ Ξ ↘ (fst r, pre') /\ domain_list_simulation (snd r) pre'.
  Proof.
    intros * H; destruct fast_eval_sim as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & _).
    exact (Hm _ _ _ _ H).
  Qed.

  Lemma fast_eval_shape_type_sim : forall p ups ρ t a, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> forall ups' ρ',
      domain_list_simulation ups ups' -> env_agree (fun x => ~ ptyp_fresh x t) ρ ρ' ->
      exists a', ⟦shtyᶠ t of p ups' ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ a' /\ domain_simulation a a'.
  Proof.
    intros * H; destruct fast_eval_sim as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _).
    exact (Hs _ _ _ _ _ H).
  Qed.

  Lemma fast_eval_ihty_sim : forall p ups ρm As ρ t m a, ⟦ihty m of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
      forall ups' ρm' ρ' m', domain_list_simulation ups ups' -> ends_agree p As ρm ρm' t ->
      env_agree (fun x => ~ ptyp_fresh x t) ρ ρ' -> domain_simulation m m' ->
      exists a', ⟦ihtyᶠ m' of t at p ups' under ρm' As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ a' /\ domain_list_simulation a a'.
  Proof.
    intros * H; destruct fast_eval_sim as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hy & _).
    exact (Hy _ _ _ _ _ _ _ _ H).
  Qed.

  (** The fields along a record view's path of related values: related
      values. *)
  Lemma fast_eval_projs_sim : forall fl v ws, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws -> forall v', domain_simulation v v' ->
      exists ws', ⟦projsᶠ fl of v' ⟧ᶠ Θ ⍮ Ξ ↘ ws' /\ domain_list_simulation ws ws'.
  Proof.
    intros * H; destruct fast_eval_sim as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
    exact (Hp _ _ _ H).
  Qed.

  (** A field of related values: related values. *)
  Lemma fast_eval_proj_sim : forall f m r, eval_proj Θ Ξ f m r -> forall m', domain_simulation m m' ->
      exists r', fast_eval_proj Θ Ξ f m' r' /\ domain_simulation r r'.
  Proof.
    intros * H; destruct fast_eval_sim as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
    exact (Hp _ _ _ H).
  Qed.

  Lemma fast_fresh_cargs_sim : forall p ups ρ gs s vs, Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs ->
      forall ups' ρ', domain_list_simulation ups ups' -> env_agree (fun _ => True) ρ ρ' ->
      exists vs', Fcargsᶠ gs of p ups' in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ vs' /\ domain_list_simulation vs vs'.
  Proof.
    induction 1; intros ups' ρ' Hu Hρ.
    - exists nil; repeat constructor.
    - destruct (fast_eval_exp_sim _ _ _ H ρ') as (a' & Ha' & Hsa); [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |].
      assert (Hv : domain_simulation (⇑! a s) (⇑! a' s)) by (repeat constructor; assumption).
      destruct (IHfresh_cargs ups' (ρ' ↦ ⇑! a' s ⦂ entry_type_closure A ρ')) as (vs' & ? & ?);
        [ exact Hu | apply env_agree_all_cons; [ exact Hρ | exact Hv ] |].
      exists (⇑! a' s :: vs'); split; [ constructor; assumption | constructor; assumption ].
    - destruct (fast_eval_shape_type_sim _ _ _ _ _ H ups' ρ' Hu) as (a' & Ha' & Hsa);
        [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |].
      destruct (IHfresh_cargs ups' ρ' Hu Hρ) as (vs' & ? & ?).
      exists (⇑! a' s :: vs'); split; [ constructor; assumption | repeat constructor; assumption ].
  Qed.

  (** ** The Leaf Paths of a Recursive Argument

      The fresh variables at the paths of the container's, and the results
      along each path, by the paths' flags. *)
  Lemma fresh_leaf_vars_lengths : forall bs as' s vs, fresh_leaf_vars bs as' s vs -> List.length as' = List.length bs.
  Proof. induction 1; cbn; congruence. Qed.

  Lemma fresh_leaf_vars_exists : forall bs as' s, List.length as' = List.length bs -> exists vs, fresh_leaf_vars bs as' s vs.
  Proof.
    induction bs as [| b bs IH]; intros [| a as'] s Hl; cbn in Hl; try discriminate; [ eexists; constructor |].
    injection Hl as Hl; destruct b.
    - destruct (IH as' (S s) Hl) as (vs & Hvs); eexists; constructor; exact Hvs.
    - destruct (IH as' s Hl) as (vs & Hvs); eexists; constructor; exact Hvs.
  Qed.

  Lemma fresh_leaf_vars_sim : forall bs as1 s vs1, fresh_leaf_vars bs as1 s vs1 ->
      forall as2 vs2, fresh_leaf_vars bs as2 s vs2 -> domain_list_simulation as1 as2 -> domain_list_simulation vs1 vs2.
  Proof.
    induction 1; intros * H2 Ha; inversion H2; subst; inversion Ha; subst; [ constructor | | ].
    - constructor; [ repeat constructor; assumption | eauto ].
    - eauto.
  Qed.

  (** Results along the paths take, of [l1 ++ l2], the variables [l1] at the
      paths of the container's, as many as those. *)
  Lemma wrap_leaf_vals_app : forall bs rs l ihs' out, wrap_leaf_vals bs rs l ihs' out ->
      forall l1 l2, l = l1 ++ l2 -> List.length l1 = List.length (List.filter (fun b => b) bs) ->
      ihs' = l2 /\ wrap_leaf_vals bs rs l1 nil out.
  Proof.
    induction 1; intros l1 l2 E Hl; cbn in Hl.
    - destruct l1; [ cbn in E; subst; split; [ reflexivity | constructor ] | discriminate ].
    - destruct l1 as [| x l1]; [ discriminate | cbn in E; injection E as -> E; injection Hl as Hl ].
      destruct (IHwrap_leaf_vals _ _ E Hl) as [-> Hw]; split; [ reflexivity | constructor; exact Hw ].
    - destruct (IHwrap_leaf_vals _ _ E Hl) as [-> Hw]; split; [ reflexivity | constructor; exact Hw ].
  Qed.

  Lemma wrap_leaf_vals_extend : forall bs rs l1 out, wrap_leaf_vals bs rs l1 nil out ->
      forall l2, wrap_leaf_vals bs rs (l1 ++ l2) l2 out.
  Proof.
    intros * H; remember nil as e eqn:Ee; revert Ee; induction H; intros -> l2; cbn; constructor; auto.
  Qed.

  Lemma wrap_leaf_vals_exists : forall bs rs l1, List.length rs = List.length bs ->
      List.length l1 = List.length (List.filter (fun b => b) bs) -> exists out, wrap_leaf_vals bs rs l1 nil out.
  Proof.
    induction bs as [| b bs IH]; intros [| r rs] l1 Hl Hl1; cbn in Hl, Hl1; try discriminate.
    - destruct l1; [ eexists; constructor | discriminate ].
    - injection Hl as Hl; destruct b.
      + destruct l1 as [| x l1]; [ discriminate | injection Hl1 as Hl1 ].
        destruct (IH rs l1 Hl Hl1) as (out & Ho); eexists; constructor; exact Ho.
      + destruct (IH rs l1 Hl Hl1) as (out & Ho); eexists; constructor; exact Ho.
  Qed.

  Lemma wrap_leaf_vals_sim : forall bs rs1 l1 e1 out1, wrap_leaf_vals bs rs1 l1 e1 out1 ->
      forall rs2 l2 e2 out2, wrap_leaf_vals bs rs2 l2 e2 out2 -> domain_list_simulation rs1 rs2 ->
      domain_list_simulation (List.firstn (List.length (List.filter (fun b => b) bs)) l1)
                (List.firstn (List.length (List.filter (fun b => b) bs)) l2) ->
      domain_list_simulation out1 out2.
  Proof.
    induction 1; intros * H2 Hr Hl; inversion H2; subst; inversion Hr; subst; cbn in Hl; [ constructor | | ].
    - inversion Hl; subst; constructor; [ assumption | eauto ].
    - constructor; [ assumption | eauto ].
  Qed.

  (** The recursive results a branch [B] is read under, fresh and wrapped:
      related where [B] reads them.  The results of an argument the branch
      reads none of are variables of type [𝕌ω@0] in the fast readback,
      along the paths of the container's. *)
  Lemma fast_fresh_wrap_sim : forall ρ As p ups Dc ρa gs' gs vs s ihs,
      Fihs vs at gs' gs of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs ->
      forall Bks wihs, ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
      forall D B ρ' ρa' ups' vs', ind_lookup Θ Ξ p = Some D -> leaves_coherent D ->
      (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_agree p As ρ ρ' t) ->
      env_agree (fun _ => True) ρa ρa' -> blocks_agree Bks ρ ρ' -> domain_list_simulation ups ups' -> domain_list_simulation vs vs' ->
      exists ihs' wihs', Fihsᶠ vs' at gs' gs of Dc under ρ' As at p ups' for B in Θ ⍮ Ξ ⍮ ρa' ⍮ s ↘ ihs' /\
        ⟦wihsᶠ vs' of gs' gs of Dc with ihs' under p ups' Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ wihs' /\
        domain_list_simulation_at (fun x => ~ exp_fresh x B) wihs wihs'.
  Proof.
    induction 1; intros Bks wihs Hw D0 B ρ' ρa' ups' vs' HD Hco HA Hρa HB Hu Hv; inversion Hw; subst; clear Hw.
    - inversion Hv; subst; exists nil, nil; repeat constructor.
    - inversion Hv; subst.
      match goal with Hv1 : domain_simulation v ?v1, Hv2 : domain_list_simulation vs ?vs1, Hw1 : wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        destruct (IHfresh_ihs _ _ Hw1 D0 B ρ' (ρa' ↦ v1 ⦂ entry_type_closure T ρa') ups' vs1 HD Hco
                    ltac:(intros gs1 t gs2 E; apply (HA (ca_arg ra T :: gs1) t gs2); rewrite E; reflexivity)
                    ltac:(apply env_agree_all_cons; assumption) HB Hu Hv2)
          as (ihs' & wihs' & ? & ? & ?) end.
      exists ihs', wihs'; repeat split; [ constructor; assumption | constructor; assumption | assumption ].
    - (** Recursive in both: the variables at the paths of the container's,
          then the rest *)
      inversion Hv; subst.
      repeat match goal with H1 : ind_lookup _ _ ?p = Some _, H2 : ind_lookup _ _ ?p = Some _ |- _ =>
               rewrite H1 in H2; injection H2 as <- end.
      rename H into HD', H0 into Hty, H1 into Hfl, H12 into Hih, H13 into Hwl, H14 into Hw1, H5 into Hv1, H7 into Hv2.
      pose proof (fresh_leaf_vars_length _ _ _ _ Hfl) as Hl1.
      destruct (wrap_leaf_vals_app _ _ _ _ _ Hwl _ _ eq_refl Hl1) as [<- Hwl1].
      destruct (IHfresh_ihs _ _ Hw1 D B ρ' ρa' ups' args' HD' Hco
                  ltac:(intros gs1 t0 gs2 E; apply (HA (ca_rec t :: gs1) t0 gs2); rewrite E; reflexivity)
                  Hρa HB Hu Hv2) as (ihs'0 & wihs' & ? & ? & Hsi).
      destruct (fast_eval_ih_sim _ _ _ _ _ _ _ Hih ρ' ups' a' HB Hu Hv1) as (rs' & ? & Hrs).
      pose proof (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Hih _ HD' Hco) as Hlr.
      assert (Hlb : List.length (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t))
                    = List.length (shape_leaves (rview_leaves D) 0 t)) by apply List.length_map.
      destruct (ihs_skip_at skip_on (Some B) (cargs_nrec D gs) (List.length (shape_leaves (rview_leaves D) 0 t))) eqn:Hsk.
      + (** Skipped: variables at [𝕌ω@0], none read *)
        destruct (fresh_leaf_vars_exists (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t))
                    (List.repeat 𝕌ω@0 (List.length (shape_leaves (rview_leaves D) 0 t))) s
                    ltac:(rewrite List.repeat_length, Hlb; reflexivity)) as (ihs1' & Hfl').
        destruct (wrap_leaf_vals_exists _ rs' ihs1' ltac:(rewrite <- (domain_list_simulation_length _ _ Hrs), Hlr, Hlb; reflexivity)
                    (fresh_leaf_vars_length _ _ _ _ Hfl')) as (out' & Hout).
        exists (ihs1' ++ ihs'0), (out' ++ wihs'); repeat split.
        * eapply fast_fresh_ihs_skip; [ exact HD' | exact Hsk | exact Hfl' | rewrite (fresh_leaf_vars_length _ _ _ _ Hfl'), <- Hl1; assumption ].
        * eapply fast_wrap_ihs_eval_rec; [ exact HD' | eassumption | apply wrap_leaf_vals_extend; exact Hout | assumption ].
        * destruct (ihs_skip_at_sound _ _ _ _ Hsk) as (_ & B0 & EB & HBf); injection EB as <-.
          apply domain_list_simulation_at_skip.
          -- rewrite (wrap_leaf_vals_length _ _ _ _ _ Hwl1), (wrap_leaf_vals_length _ _ _ _ _ Hout); reflexivity.
          -- intros i0 Hi0 Hn; apply Hn.
             rewrite (proj1 (wrap_ihs_eval_length _ _ _ _ _ _ _ _ _ _ _ _ _ HD' Hco Hw1)); apply HBf.
             rewrite (wrap_leaf_vals_length _ _ _ _ _ Hwl1), Hlb in Hi0; exact Hi0.
          -- exact Hsi.
      + (** Computed: variables at the related types *)
        destruct (fast_eval_ihty_sim _ _ _ _ _ _ _ _ Hty ups' ρ' ρa' a' Hu (HA nil t gs eq_refl)
                    ltac:(eapply env_agree_mono; [ exact Hρa | intros; exact I ]) Hv1) as (a2 & ? & Ha2).
        destruct (fresh_leaf_vars_exists (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) a2 s
                    ltac:(rewrite <- (domain_list_simulation_length _ _ Ha2); exact (fresh_leaf_vars_lengths _ _ _ _ Hfl))) as (ihs1' & Hfl').
        destruct (wrap_leaf_vals_exists _ rs' ihs1' ltac:(rewrite <- (domain_list_simulation_length _ _ Hrs), Hlr, Hlb; reflexivity)
                    (fresh_leaf_vars_length _ _ _ _ Hfl')) as (out' & Hout).
        exists (ihs1' ++ ihs'0), (out' ++ wihs'); repeat split.
        * eapply fast_fresh_ihs_rec; [ exact HD' | exact Hsk | eassumption | exact Hfl' | rewrite (fresh_leaf_vars_length _ _ _ _ Hfl'), <- Hl1; assumption ].
        * eapply fast_wrap_ihs_eval_rec; [ exact HD' | eassumption | apply wrap_leaf_vals_extend; exact Hout | assumption ].
        * apply domain_list_simulation_at_app; [| exact Hsi ].
          eapply wrap_leaf_vals_sim; [ exact Hwl1 | exact Hout | exact Hrs |].
          rewrite !List.firstn_all2 by (first [ rewrite Hl1 | rewrite (fresh_leaf_vars_length _ _ _ _ Hfl') ]; lia).
          exact (fresh_leaf_vars_sim _ _ _ _ Hfl _ _ Hfl' Ha2).
    - (** Nested through: the eliminator's results along each path *)
      inversion Hv; subst.
      match goal with Hv1 : domain_simulation v ?v1, Hv2 : domain_list_simulation vs ?vs1, Hw1 : wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ _ _,
                      Hi : eval_ih _ _ _ _ _ _ _ _ _ |- _ =>
        let rs' := fresh "rs'" in
        destruct (fast_eval_ih_sim _ _ _ _ _ _ _ Hi ρ' ups' v1 HB Hu Hv1) as (rs' & ? & ?);
        destruct (IHfresh_ihs _ _ Hw1 D0 B ρ' ρa' ups' vs1 HD Hco
                    ltac:(intros gs1 t0 gs2 E; apply (HA (ca_rec t :: gs1) t0 gs2); rewrite E; reflexivity)
                    Hρa HB Hu Hv2) as (ihs' & wihs' & ? & ? & ?);
        exists ihs', (rs' ++ wihs'); repeat split;
          [ constructor; assumption | econstructor; eassumption | apply domain_list_simulation_at_app; assumption ]
      end.
  Qed.

  (** ** Readback

      The formers readback builds respect equality up to proofs. *)
  Lemma nf_proof_upto_proofs : forall P P' M M', nf_eq_upto_proofs P P' -> nf_eq_upto_proofs (nf_proof P M) (nf_proof P' M').
  Proof. intros * H; exact H. Qed.

  Lemma nf_neut_upto_proofs : forall κ κ' M M', κ = κ' -> ne_eq_upto_proofs M M' -> nf_eq_upto_proofs (nf_neut κ M) (nf_neut κ' M').
  Proof. intros * <- H; unfold nf_eq_upto_proofs, ne_eq_upto_proofs in *; cbn; rewrite dec_eqb_refl, H; reflexivity. Qed.

  Lemma ne_absurd_upto_proofs : forall C C' M M', nf_eq_upto_proofs C C' -> ne_eq_upto_proofs (ne_absurd C M) (ne_absurd C' M').
  Proof. intros * H; exact H. Qed.

  Lemma nf_lvl_atom_upto_proofs : forall k n n' M M', n = n' -> ne_eq_upto_proofs M M' ->
      nf_eq_upto_proofs (lvⁿ ordinal_zero (mk_level_atom k n M :: nil)) (lvⁿ ordinal_zero (mk_level_atom k n' M' :: nil)).
  Proof.
    intros * <- H; apply (nf_lvl_of_upto_proofs (ordinal_zero, _) (ordinal_zero, _)).
    split; [ reflexivity | apply level_atoms_eq_upto_proofs_cons; [ exact H | reflexivity ] ].
  Qed.

  Lemma nf_lvl_canon_upto_proofs : forall c ys ys', level_atoms_eq_upto_proofs ys ys' ->
      nf_eq_upto_proofs (nf_lvl_of (lvl_canon (c, ys))) (nf_lvl_of (lvl_canon (c, ys'))).
  Proof. intros * H; apply nf_lvl_of_upto_proofs, lvl_canon_upto_proofs, H. Qed.

  (** A normal form equal up to proofs to a level's is one. *)
  Lemma nf_lvl_of_upto_proofs_inv_l : forall l W, nf_eq_upto_proofs (nf_lvl_of l) W ->
      exists l', W = nf_lvl_of l' /\ lvl_eq_upto_proofs l l'.
  Proof.
    intros [c xs] [] H; unfold nf_eq_upto_proofs in H; cbn in H; try discriminate.
    match goal with |- exists l', nf_lvl ?c' ?xs' = _ /\ _ => exists (c', xs') end.
    split; [ reflexivity | apply nf_lvl_of_upto_proofs_iff; exact H ].
  Qed.

  Lemma nf_univ_of_upto_proofs : forall l l', lvl_eq_upto_proofs l l' -> nf_eq_upto_proofs (nf_univ_of l) (nf_univ_of l').
  Proof. intros * H; apply nf_univ_of_upto_proofs_iff, H. Qed.

  Lemma nfs_eq_upto_proofs_cons_intro : forall W W' Ws Ws', nf_eq_upto_proofs W W' -> nfs_eq_upto_proofs Ws Ws' ->
      nfs_eq_upto_proofs (W :: Ws) (W' :: Ws').
  Proof. intros * H H'; apply nfs_eq_upto_proofs_cons; split; assumption. Qed.

  Lemma env_agree_all_nil : env_agree (fun _ => True) nil nil.
  Proof. apply env_agree_nil. Qed.

  (** The type of a fast environment's entry for that of a reference one,
      over related values and environments. *)
  Ltac fast_entry_type t :=
    lazymatch t with
    | entry_type_value ?a => match goal with H : domain_simulation a ?a' |- _ => constr:(entry_type_value a') end
    | entry_type_closure ?A ?ρ => match goal with H : env_agree (fun _ => True) ρ ?ρ' |- _ => constr:(entry_type_closure A ρ') end
    | _ => t
    end.

  (** The fast evaluations the readback of related values makes: closures
      at related arguments, applications, terms in environments related
      everywhere, and the parts of inductive types. *)
  Ltac read_eval_fwd :=
    repeat match goal with
    | He : ⟦ ?B ⟧ Θ ⍮ Ξ ⍮ ?ρ ↦ ?c ⦂ ?t ↘ ?b,
      Hρ : forall x, ~ exp_fresh (S x) ?B -> dentry_simulation (env_entry ?ρ x) (env_entry ?ρ' x) |- _ =>
        let t' := fast_entry_type t in
        destruct (fast_eval_clo_sim B ρ ρ' c _ t t' b Hρ ltac:(eauto with mctt) He) as (? & ? & ?); clear He
    | He : $| ?m & ?n | Θ ⍮ Ξ ↘ ?r, Hm : domain_simulation ?m ?m' |- _ =>
        destruct (fast_eval_app_sim _ _ _ He m' _ Hm ltac:(eauto with mctt)) as (? & ? & ?); clear He
    | He : ⟦ ?A ⟧ Θ ⍮ Ξ ⍮ ?ρ ↘ ?a, Hρ : env_agree (fun _ => True) ?ρ ?ρ' |- _ =>
        destruct (fast_eval_exp_sim _ _ _ He ρ' (env_agree_mono _ _ _ _ Hρ (fun _ _ => I))) as (? & ? & ?); clear He
    | He : ⟦ ?Ps ⟧* Θ ⍮ Ξ ⍮ ?ρ ↘ ?bs, Hρ : env_agree (fun _ => True) ?ρ ?ρ' |- _ =>
        pose proof (eval_exps_length _ _ _ He);
        destruct (fast_eval_exps_sim _ _ _ He ρ' (env_agree_mono _ _ _ _ Hρ (fun _ _ => I))) as (? & ? & ?); clear He
    | He : ⟦projs ?fl of ?v ⟧ Θ ⍮ Ξ ↘ ?ws, Hv : domain_simulation ?v ?v' |- _ =>
        destruct (fast_eval_projs_sim _ _ _ He _ Hv) as (? & ? & ?); clear He
    | He : eval_proj Θ Ξ ?f ?v ?r, Hv : domain_simulation ?v ?v' |- _ =>
        destruct (fast_eval_proj_sim _ _ _ He _ Hv) as (? & ? & ?); clear He
    | He : ⟦mref ?j of ?p ?ups ⟧ Θ ⍮ Ξ ↘ ?r, Hu : domain_list_simulation ?ups ?ups' |- _ =>
        destruct (fast_eval_mref_sim _ _ _ _ He ups' Hu) as (? & ? & ?); cbn [fst snd] in *; clear He
    | He : Ftele ?T in Θ ⍮ Ξ ⍮ ?ρ ⍮ ?s ↘ ?ns, Hρ : env_agree (fun _ => True) ?ρ ?ρ' |- _ =>
        pose proof (fresh_tele_length _ _ _ _ He);
        destruct (fast_fresh_tele_sim _ _ _ _ He ρ' Hρ) as (? & ? & ?); clear He
    | He : Fcargs ?gs of ?p ?ups in Θ ⍮ Ξ ⍮ ?ρ ⍮ ?s ↘ ?vs, Hu : domain_list_simulation ?ups ?ups',
      Hρ : env_agree (fun _ => True) ?ρ ?ρ' |- _ =>
        destruct (fast_fresh_cargs_sim _ _ _ _ _ _ He ups' ρ' Hu Hρ) as (? & ? & ?); clear He
    end.

  (** The agreement of the environments readback reads at: the empty one,
      a telescope's over nothing, a declaration's, and one extended by a
      value at a closure's type. *)
  Ltac read_env_seed :=
    repeat match goal with
    | IH : context [env_tele nil ?T ?vs], H : domain_list_simulation ?vs ?vs' |- _ =>
        lazymatch goal with
        | _ : env_agree (fun _ => True) (env_tele nil T vs) _ |- _ => fail
        | _ => pose proof (env_agree_tele_nil (fun _ => True) T vs vs' H)
        end
    | IH : context [decl_env ?D ?vs], H : domain_list_simulation ?vs ?vs' |- _ =>
        lazymatch goal with
        | _ : env_agree (fun _ => True) (decl_env D vs) _ |- _ => fail
        | _ => pose proof (env_agree_decl_env (fun _ => True) D vs vs' H)
        end
    | IH : context [?ρ ↦ ?v ⦂ entry_type_closure ?A ?ρ], Hρ : env_agree (fun _ => True) ?ρ ?ρ', Hv : domain_simulation ?v ?v' |- _ =>
        lazymatch goal with
        | _ : env_agree (fun _ => True) (ρ ↦ v ⦂ entry_type_closure A ρ) _ |- _ => fail
        | _ => pose proof (env_agree_all_cons ρ ρ' v v' (entry_type_closure A ρ) (entry_type_closure A ρ') Hρ Hv)
        end
    | IH : context [env_tele ?ρ ?T ?vs], Hρ : env_agree (fun _ => True) ?ρ ?ρ', H : domain_list_simulation ?vs ?vs' |- _ =>
        lazymatch goal with
        | _ : env_agree (fun _ => True) (env_tele ρ T vs) _ |- _ => fail
        | _ => pose proof (env_agree_tele ρ ρ' T vs vs' Hρ H)
        end
    | IH : context [firstn ?n ?l], H : domain_list_simulation ?l ?l' |- _ =>
        lazymatch goal with
        | _ : domain_list_simulation (firstn n l) _ |- _ => fail
        | _ => pose proof (domain_list_simulation_firstn n l l' H)
        end
    | IH : context [skipn ?n ?l], H : domain_list_simulation ?l ?l' |- _ =>
        lazymatch goal with
        | _ : domain_list_simulation (skipn n l) _ |- _ => fail
        | _ => pose proof (domain_list_simulation_skipn n l l' H)
        end
    | IH : context [d_ind ?p ?j (?l1 ++ ?l2)], H1 : domain_list_simulation ?l1 ?l1', H2 : domain_list_simulation ?l2 ?l2' |- _ =>
        lazymatch goal with
        | _ : domain_simulation (d_ind p j (l1 ++ l2)) _ |- _ => fail
        | _ => pose proof (domain_simulation_indty p j _ _ (domain_list_simulation_app _ _ _ _ H1 H2))
        end
    | IH : context [⇑! ?b ?s], H : domain_simulation ?b ?b' |- _ =>
        lazymatch goal with
        | _ : domain_simulation (⇑! b s) _ |- _ => fail
        | _ => pose proof (domain_simulation_neut _ _ _ _ H (domain_ne_simulation_var s))
        end
    | Ha : domain_simulation ?a ?a', Hb : domain_ne_simulation ?b ?b' |- context [⇑ ?a' ?b'] =>
        lazymatch goal with
        | _ : domain_simulation (⇑ a b) (⇑ a' b') |- _ => fail
        | _ => pose proof (domain_simulation_neut _ _ _ _ Ha Hb)
        end
    end;
    try pose proof env_agree_all_nil.

  (** The induction hypotheses at the related values and environments. *)
  Ltac read_ih_fwd :=
    repeat match goal with
    | IH : forall n', domain_nf_simulation (⇓ ?a ?m) n' -> exists _, _ /\ _,
      Ha : domain_simulation ?a ?a', Hm : domain_simulation ?m ?m' |- _ =>
        destruct (IH (⇓ a' m') (domain_nf_simulation_dom _ _ _ _ Ha Hm)) as (? & ? & ?); clear IH
    | IH : forall n', domain_nf_simulation (⇓ ?a ?m) n' -> exists _, _ /\ _, Hm : domain_simulation ?m ?m' |- _ =>
        let Ha := fresh "Ha" in assert (Ha : domain_simulation a a) by constructor;
        destruct (IH (⇓ a m') (domain_nf_simulation_dom _ _ _ _ Ha Hm)) as (? & ? & ?); clear IH Ha
    | IH : forall ρ0 ups0 D0, blocks_agree ?Bks ?ρ ρ0 -> domain_list_simulation ?ups ups0 -> ind_lookup _ _ ?p = Some D0 -> _ ->
           _ -> exists _, _ /\ _,
      HB : blocks_agree ?Bks ?ρ ?ρ', Hu : domain_list_simulation ?ups ?ups', Hl : ind_lookup _ _ ?p = Some ?D,
      Hb : blocks_binder_count_at ?D None ?Bks, Hr : rview_leaf_arity ?D |- _ =>
        destruct (IH ρ' ups' D HB Hu Hl Hb Hr) as (? & ? & ?); clear IH
    | IH : forall a', domain_simulation ?a a' -> exists _, _ /\ _, Ha : domain_simulation ?a ?a' |- _ =>
        destruct (IH a' Ha) as (? & ? & ?); clear IH
    | IH : forall a', domain_simulation ?a a' -> exists _, Rprfᶠ _ in _ ⍮ _ ⍮ _ ↘ _, Ha : domain_simulation ?a ?a' |- _ =>
        destruct (IH a' Ha) as (? & ?); clear IH
    | IH : forall m', domain_ne_simulation ?m m' -> exists _, _ /\ _, Hm : domain_ne_simulation ?m ?m' |- _ =>
        destruct (IH m' Hm) as (? & ? & ?); clear IH
    | IH : forall xs', level_atoms_simulation ?xs xs' -> exists _, _ /\ _, Hx : level_atoms_simulation ?xs ?xs' |- _ =>
        destruct (IH xs' Hx) as (? & ? & ?); clear IH
    | IH : forall ρ0 vs0, env_agree _ ?ρ ρ0 -> domain_list_simulation ?vs vs0 -> exists _, _ /\ _,
      Hρ : env_agree (fun _ => True) ?ρ ?ρ', Hv : domain_list_simulation ?vs ?vs' |- _ =>
        destruct (IH ρ' vs' Hρ Hv) as (? & ? & ?); clear IH
    | IH : forall ρ0 v0, env_agree _ ?ρ ρ0 -> domain_simulation ?v v0 -> exists _, _ /\ _,
      Hρ : env_agree (fun _ => True) ?ρ ?ρ', Hv : domain_simulation ?v ?v' |- _ =>
        destruct (IH ρ' v' Hρ Hv) as (? & ? & ?); clear IH
    | IH : forall ups0 ρ0 vs0, domain_list_simulation ?ups ups0 -> env_agree _ ?ρ ρ0 -> domain_list_simulation ?vs vs0 -> exists _, _ /\ _,
      Hu : domain_list_simulation ?ups ?ups', Hρ : env_agree (fun _ => True) ?ρ ?ρ', Hv : domain_list_simulation ?vs ?vs' |- _ =>
        destruct (IH ups' ρ' vs' Hu Hρ Hv) as (? & ? & ?); clear IH
    | IH : forall ups0 ρ0 v0, domain_list_simulation ?ups ups0 -> env_agree _ ?ρ ρ0 -> domain_simulation ?v v0 -> exists _, _ /\ _,
      Hu : domain_list_simulation ?ups ?ups', Hρ : env_agree (fun _ => True) ?ρ ?ρ', Hv : domain_simulation ?v ?v' |- _ =>
        destruct (IH ups' ρ' v' Hu Hρ Hv) as (? & ? & ?); clear IH
    end.

  (** The lists simulated have the lengths the reference ones have. *)
  Ltac read_lengths :=
    repeat match goal with
    | Hs : domain_list_simulation ?l ?l', He : List.length ?l = ?X |- _ =>
        lazymatch goal with
        | _ : List.length l' = X |- _ => fail
        | _ => pose proof (eq_trans (eq_sym (domain_list_simulation_length _ _ Hs)) He)
        end
    end.

  Create HintDb upto.
  #[local]
  Hint Resolve nf_proof_upto_proofs nf_neut_upto_proofs ne_absurd_upto_proofs nf_lvl_atom_upto_proofs
    nf_lvl_canon_upto_proofs nf_univ_of_upto_proofs nf_con_upto_proofs nf_indty_upto_proofs nf_record_upto_proofs
    nf_fn_upto_proofs nf_pi_upto_proofs nf_and_upto_proofs nf_tuple_upto_proofs ne_app_upto_proofs ne_proj_upto_proofs
    ne_elim_upto_proofs nfs_eq_upto_proofs_app nfs_eq_upto_proofs_cons_intro branches_eq_upto_proofs_nil
    branches_eq_upto_proofs_cons blocks_eq_upto_proofs_nil blocks_eq_upto_proofs_cons level_atoms_eq_upto_proofs_cons
    domain_kind_sim domain_level_sort_sim : upto.

  (** S3: readback of related values, with the skip on, gives a normal form
      equal up to proofs: the kept proofs read as their terms
      ([fast_read_proof_kept_skipping]), with nothing around them, and
      nothing reads the definitions a kept proof is read under. *)
  Theorem fast_read_simulation :
    (forall s n W, Rnf n in Θ ⍮ Ξ ⍮ s ↘ W -> forall n', domain_nf_simulation n n' ->
       exists W', Rnfᶠ n' in Θ ⍮ Ξ ⍮ s ↘ W' /\ nf_eq_upto_proofs W W') /\
    (forall s m W, Rne m in Θ ⍮ Ξ ⍮ s ↘ W -> forall m', domain_ne_simulation m m' ->
       exists W', Rneᶠ m' in Θ ⍮ Ξ ⍮ s ↘ W' /\ ne_eq_upto_proofs W W') /\
    (forall s a W, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ W -> forall a', domain_simulation a a' ->
       exists W', Rtypᶠ a' in Θ ⍮ Ξ ⍮ s ↘ W' /\ nf_eq_upto_proofs W W') /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys -> forall xs', level_atoms_simulation xs xs' ->
       exists ys', Rlaᶠ xs' in Θ ⍮ Ξ ⍮ s ↘ ys' /\ level_atoms_eq_upto_proofs ys ys') /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> forall ρ' vs',
       env_agree (fun _ => True) ρ ρ' -> domain_list_simulation vs vs' ->
       exists Ms', Rpsᶠ vs' at T in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Ms' /\ nfs_eq_upto_proofs Ms Ms') /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> forall ups' ρ' vs',
       domain_list_simulation ups ups' -> env_agree (fun _ => True) ρ ρ' -> domain_list_simulation vs vs' ->
       exists Ms', Rcargsᶠ vs' at gs of p ups' in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Ms' /\ nfs_eq_upto_proofs Ms Ms') /\
    (forall s p ups ρ t v V, Rsh v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V -> forall ups' ρ' v',
       domain_list_simulation ups ups' -> env_agree (fun _ => True) ρ ρ' -> domain_simulation v v' ->
       exists V', Rshᶠ v' at t of p ups' in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ V' /\ nf_eq_upto_proofs V V') /\
    (forall s ρ p ups Bks Dc sel i Ms NBks, Rblks i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks -> forall ρ' ups' D,
       blocks_agree Bks ρ ρ' -> domain_list_simulation ups ups' -> ind_lookup Θ Ξ p = Some D -> blocks_binder_count_at D None Bks ->
       rview_leaf_arity D ->
       exists NBks', Rblksᶠ i Ms of Dc from p ups' Bks sel in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ NBks' /\ blocks_eq_upto_proofs NBks NBks') /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       forall ρ' ups' pre' D,
       blocks_agree Bks ρ ρ' -> domain_list_simulation ups ups' -> domain_list_simulation (snd r) pre' ->
       ind_lookup Θ Ξ p = Some D -> blocks_binder_count_at D None Bks -> rview_leaf_arity D -> im_nn Mv = im_nn Mi ->
       env_agree (fun x => ~ exp_fresh (S (im_nn Mi) + x) A) ρ ρ' ->
       (forall c n B, In (c, n, B) Bs -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ') ->
       exists Bs'', Rbrsᶠ Bs at cs of Mi (fst r, pre') of Dc from p ups' Bks Mv A in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Bs'' /\
         branches_eq_upto_proofs Bs' Bs'') /\
    (forall s ρ fl v Fs, Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs -> forall ρ' v',
       env_agree (fun _ => True) ρ ρ' -> domain_simulation v v' ->
       exists Fs', Rfldsᶠ v' at fl in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Fs' /\ nfs_eq_upto_proofs Fs Fs') /\
    (forall s m M, Rprf m in Θ ⍮ Ξ ⍮ s ↘ M -> forall m', domain_simulation m m' ->
       exists M', Rprfᶠ m' in Θ ⍮ Ξ ⍮ s ↘ M') /\
    (forall s ρ k bs, Rlets ρ at k in Θ ⍮ Ξ ⍮ s ↘ bs -> True) /\
    (forall s e b, Rent e in Θ ⍮ Ξ ⍮ s ↘ b -> True).
  Proof.
    apply (read_mut_ind Θ Ξ
      (fun s n W _ => forall n', domain_nf_simulation n n' -> exists W', Rnfᶠ n' in Θ ⍮ Ξ ⍮ s ↘ W' /\ nf_eq_upto_proofs W W')
      (fun s m W _ => forall m', domain_ne_simulation m m' -> exists W', Rneᶠ m' in Θ ⍮ Ξ ⍮ s ↘ W' /\ ne_eq_upto_proofs W W')
      (fun s a W _ => forall a', domain_simulation a a' -> exists W', Rtypᶠ a' in Θ ⍮ Ξ ⍮ s ↘ W' /\ nf_eq_upto_proofs W W')
      (fun s xs ys _ => forall xs', level_atoms_simulation xs xs' ->
         exists ys', Rlaᶠ xs' in Θ ⍮ Ξ ⍮ s ↘ ys' /\ level_atoms_eq_upto_proofs ys ys')
      (fun s ρ T vs Ms _ => forall ρ' vs', env_agree (fun _ => True) ρ ρ' -> domain_list_simulation vs vs' ->
         exists Ms', Rpsᶠ vs' at T in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Ms' /\ nfs_eq_upto_proofs Ms Ms')
      (fun s p ups ρ gs vs Ms _ => forall ups' ρ' vs',
         domain_list_simulation ups ups' -> env_agree (fun _ => True) ρ ρ' -> domain_list_simulation vs vs' ->
         exists Ms', Rcargsᶠ vs' at gs of p ups' in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Ms' /\ nfs_eq_upto_proofs Ms Ms')
      (fun s p ups ρ t v V _ => forall ups' ρ' v',
         domain_list_simulation ups ups' -> env_agree (fun _ => True) ρ ρ' -> domain_simulation v v' ->
         exists V', Rshᶠ v' at t of p ups' in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ V' /\ nf_eq_upto_proofs V V')
      (fun s ρ p ups Bks Dc sel i Ms NBks _ => forall ρ' ups' D,
         blocks_agree Bks ρ ρ' -> domain_list_simulation ups ups' -> ind_lookup Θ Ξ p = Some D ->
         blocks_binder_count_at D None Bks -> rview_leaf_arity D ->
         exists NBks', Rblksᶠ i Ms of Dc from p ups' Bks sel in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ NBks' /\ blocks_eq_upto_proofs NBks NBks')
      (fun s ρ p ups Bks Dc Mv A Mi r cs Bs Bs' _ => forall ρ' ups' pre' D,
         blocks_agree Bks ρ ρ' -> domain_list_simulation ups ups' -> domain_list_simulation (snd r) pre' ->
         ind_lookup Θ Ξ p = Some D -> blocks_binder_count_at D None Bks -> rview_leaf_arity D -> im_nn Mv = im_nn Mi ->
         env_agree (fun x => ~ exp_fresh (S (im_nn Mi) + x) A) ρ ρ' ->
         (forall c n B, In (c, n, B) Bs -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ') ->
         exists Bs'', Rbrsᶠ Bs at cs of Mi (fst r, pre') of Dc from p ups' Bks Mv A in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Bs'' /\
           branches_eq_upto_proofs Bs' Bs'')
      (fun s ρ fl v Fs _ => forall ρ' v', env_agree (fun _ => True) ρ ρ' -> domain_simulation v v' ->
         exists Fs', Rfldsᶠ v' at fl in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Fs' /\ nfs_eq_upto_proofs Fs Fs')
      (fun s m M _ => forall m', domain_simulation m m' -> exists M', Rprfᶠ m' in Θ ⍮ Ξ ⍮ s ↘ M')
      (fun _ _ _ _ _ => True)
      (fun _ _ _ _ => True));
      intros; cbn [fst snd] in *; try exact I;
      repeat match goal with
        | H : domain_nf_simulation _ _ |- _ => inversion H; subst; clear H
        | H : domain_ne_simulation (_ _) _ |- _ => inversion H; subst; clear H
        | H : domain_ne_simulation (_ _ _) _ |- _ => inversion H; subst; clear H
        | H : domain_ne_simulation (_ _ _ _ _ _ _ _) _ |- _ => inversion H; subst; clear H
        | H : level_atoms_simulation (_ :: _) _ |- _ => inversion H; subst; clear H
        | H : level_atoms_simulation nil _ |- _ => inversion H; subst; clear H
        | H : domain_simulation (_ _) _ |- _ => inversion H; subst; clear H
        | H : domain_simulation (_ _ _) _ |- _ => inversion H; subst; clear H
        | H : domain_simulation (_ _ _ _) _ |- _ => inversion H; subst; clear H
        | H : domain_simulation (_ _ _ _ _) _ |- _ => inversion H; subst; clear H
        | H : domain_simulation ⊤ᵈ _ |- _ => inversion H; subst; clear H
        | H : domain_simulation ⊥ᵈ _ |- _ => inversion H; subst; clear H
        | H : domain_simulation Propᵈ _ |- _ => inversion H; subst; clear H
        | H : domain_simulation LevelSortᵈ _ |- _ => inversion H; subst; clear H
        | H : domain_list_simulation (_ :: _) _ |- _ => inversion H; subst; clear H
        | H : domain_list_simulation nil _ |- _ => inversion H; subst; clear H
        | H : forall b, In b ?Bks -> (forall x, _ -> dentry_simulation (env_entry ?ρ x) (env_entry ?ρ' x)) /\ _ |- _ =>
            change (blocks_agree Bks ρ ρ') in H
        end.
    all: do 2 (read_eval_fwd; read_env_seed); read_ih_fwd; read_lengths; rel_transfer.
    all: try solve [ eexists; split; [ eauto with mctt | eauto with upto mctt ] ].
    (** A proof: a neutral as its neutral, a kept proof as its term *)
    all: try solve [ eexists; eauto with mctt | eexists; apply fast_read_proof_kept_skipping; reflexivity ].
    all: try solve [ exists nil; split; [ constructor | reflexivity ] ].
    (** A small universe: its level reads back as a level's normal form *)
    all: try solve [ match goal with
      | HW : Rnfᶠ ⇓ _ _ in _ ⍮ _ ⍮ _ ↘ ?W, Hup : nf_eq_upto_proofs (nf_lvl_of ?L) ?W |- _ =>
          let L' := fresh "L'" in let HL := fresh "HL" in
          destruct (nf_lvl_of_upto_proofs_inv_l _ _ Hup) as (L' & -> & HL);
          exists (nf_univ_of L'); split; [ constructor; exact HW | apply nf_univ_of_upto_proofs, HL ]
      end ].
    (** A block: its motive under the fresh non-uniform parameters of its
        member and the scrutinee, its branches and the blocks after it;
        the block's member has as many non-uniform parameters as the
        member read, both being the motive's binders. *)
    all: try solve [ match goal with
      | e : ind_lookup Θ Ξ ?p = Some ?D, HD0 : ind_lookup Θ Ξ ?p = Some ?D0,
        HMv : ind_member ?D ?ix = Some ?Mv, Hnth : List.nth_error ?Bks ?ix = Some ?bk,
        Hbn : eb_binder_count ?bk = S (im_nn ?Mi), Hbc : blocks_binder_count_at ?D0 None ?Bks, Har : rview_leaf_arity ?D0,
        e4 : ⟦ eb_motive ?bk ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ?ρ (motive_entries ?D ?Mv ?ups ?ns _ _) ↘ ?a,
        Hln : List.length ?ns = List.length (List.rev (im_nparams ?Mv)),
        Hns : domain_list_simulation ?ns ?ns', Hind : domain_simulation (⇑! (d_ind ?hd ?k (?pre ++ ?ns)) ?n) ?v',
        Hpre : domain_list_simulation ?pre ?pre',
        IHA : forall a0, domain_simulation ?a a0 -> exists _, _ /\ _,
        IHS : forall ρ0 ups0 pre0 D1, blocks_agree ?Bks ?ρ ρ0 -> _,
        HB : blocks_agree ?Bks ?ρ ?ρ', Hu : domain_list_simulation ?ups ?ups' |- _ =>
          rewrite e in HD0; injection HD0 as <-;
          let Hnn := fresh "Hnn" in let HBm := fresh "HBm" in let a' := fresh "a'" in let Hsa := fresh "Hsa" in
          assert (Hnn : im_nn Mv = im_nn Mi)
            by (let Hx := fresh "Hx" in pose proof (Hbc _ _ _ HMv Hnth) as Hx; cbn [elim_src] in Hx; congruence);
          assert (HBm : env_agree (fun x => ~ exp_fresh (S (im_nn Mi) + x) (eb_motive bk)) ρ ρ')
            by (rewrite <- Hbn; exact (proj1 (HB _ (nth_error_In _ _ Hnth))));
          match type of Hind with domain_simulation _ ?v' =>
          destruct (fast_eval_exp_sim _ _ _ e4 (env_extend_typed ρ' (motive_entries D Mv ups' ns' (d_ind hd k (pre' ++ ns')) v')))
            as (a' & ? & Hsa);
            [ eapply env_agree_binders;
                [ exact HBm
                | unfold typed_simulation; rewrite !motive_entries_map_fst; apply domain_list_simulation_app;
                    [ exact Hns | constructor; [ exact Hind | constructor ] ]
                | rewrite motive_entries_length, Hln, List.length_rev; change (List.length (im_nparams Mv)) with (im_nn Mv);
                  rewrite Hnn; reflexivity ]
            |] end;
          let A2 := fresh "A2" in let Bs2 := fresh "Bs2" in
          destruct (IHA a' Hsa) as (A2 & ? & ?);
          destruct (IHS ρ' ups' pre' D HB Hu Hpre e Hbc Har Hnn HBm (proj2 (HB _ (nth_error_In _ _ Hnth)))) as (Bs2 & ? & ?);
          eexists; split; [ eapply fast_read_blocks_cons; eassumption | apply blocks_eq_upto_proofs_cons; assumption ]
      end ].
    (** A branch: under the fresh non-uniform parameters, arguments and
        recursive results, the last read only where the branch reads them;
        the motive at the constructor. *)
    all: try solve [ match goal with
      | f0 : Fcargs ?gs of ?p ?ups in Θ ⍮ Ξ ⍮ ?ρa ⍮ _ ↘ ?vs,
        f1 : Fihs ?vs at ?gs' ?gs of ?Dc under ?ρ _ at ?p ?ups in Θ ⍮ Ξ ⍮ ?ρa ⍮ _ ↘ _,
        w : ⟦wihs ?vs of ?gs' ?gs of ?Dc with _ under ?p ?ups ?Bks ⟧ Θ ⍮ Ξ ⍮ ?ρ ↘ ?wihs,
        e0 : ind_lookup Θ Ξ ?p = Some ?D, HD0 : ind_lookup Θ Ξ ?p = Some ?D0,
        Hbc : blocks_binder_count_at ?D0 None ?Bks, Har : rview_leaf_arity ?D0, c0 : cargs_params_length ?D ?gs,
        HB : blocks_agree ?Bks ?ρ ?ρ', Hu : domain_list_simulation ?ups ?ups', Hρa : env_agree (fun _ => True) ?ρa ?ρa',
        e4 : ⟦ ?B ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ?ρ (branch_entries ?D ?Mv ?p ?ups _ ?ρ ?gs ?ns ?vs ?wihs) ↘ ?b,
        e5 : ⟦ ?A ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ?ρ (motive_entries ?D ?Mv ?ups ?ns _ (d_con ?hd ?k ?c (?pre ++ _))) ↘ ?t,
        e1 : ?n0 = (im_nn ?Mi + List.length ?gs' + cargs_nrec ?D ?gs)%nat,
        Hln : List.length ?ns = List.length (List.rev (im_nparams ?Mv)), Hns : domain_list_simulation ?ns ?ns',
        Hpre : domain_list_simulation ?pre ?pre', Hnn : im_nn ?Mv = im_nn ?Mi,
        HA : env_agree (fun x => ~ exp_fresh (S (im_nn ?Mi) + x) ?A) ?ρ ?ρ',
        HBs : forall c1 n1 B1, In (c1, n1, B1) ((?c, ?n0, ?B) :: _) -> _,
        IHV : forall n', domain_nf_simulation (⇓ ?t ?b) n' -> exists _, _ /\ _,
        IHT : forall ρ0 ups0 pre0 D1, blocks_agree ?Bks ?ρ ρ0 -> _ |- _ =>
          rewrite e0 in HD0; injection HD0 as <-;
          let vs' := fresh "vs'" in let Hsv := fresh "Hsv" in let Hco := fresh "Hco" in
          let Hl2 := fresh "Hl" in let Hl3 := fresh "Hl" in
          let ihs' := fresh "ihs'" in let wihs' := fresh "wihs'" in let Hsi := fresh "Hsi" in
          let b' := fresh "b'" in let Hsb := fresh "Hsb" in let t' := fresh "t'" in let Hst := fresh "Hst" in
          let B2 := fresh "B2" in let Bs2 := fresh "Bs2" in
          destruct (fast_fresh_cargs_sim _ _ _ _ _ _ f0 ups' ρa' Hu Hρa) as (vs' & ? & Hsv);
          pose proof (leaves_coherent_of_order _ (rview_leaf_order _ Har)) as Hco;
          pose proof (wrap_ihs_eval_length _ _ _ _ _ _ _ _ _ _ _ _ _ e0 Hco w) as [Hl2 Hl3];
          destruct (fast_fresh_wrap_sim _ _ _ _ _ _ _ _ _ _ _ f1 _ _ w _ B ρ' ρa' ups' vs' e0 Hco
                      (cargs_ends_agree _ _ _ _ _ _ e0 Har Hbc HB c0) Hρa HB Hu Hsv) as (ihs' & wihs' & ? & ? & Hsi);
          destruct (fast_eval_exp_sim _ _ _ e4 (env_extend_typed ρ' (branch_entries D Mv p ups' (blocks_motives Bks) ρ' gs ns' vs' wihs')))
            as (b' & ? & Hsb);
            [ eapply env_agree_binders_at;
                [ exact (HBs _ _ _ (or_introl eq_refl))
                | rewrite !branch_entries_map_fst; apply domain_list_simulation_at_app;
                    [ exact Hns | apply domain_list_simulation_at_app; [ exact Hsv | exact Hsi ] ]
                | rewrite branch_entries_length, Hl2, Hl3, Hln, List.length_rev, e1;
                  change (List.length (im_nparams Mv)) with (im_nn Mv); rewrite Hnn; lia ]
            |];
          destruct (fast_eval_exp_sim _ _ _ e5 (env_extend_typed ρ' (motive_entries D Mv ups' ns' (d_ind hd k (pre' ++ ns'))
                                                        (d_con hd k c (pre' ++ ns' ++ vs'))))) as (t' & ? & Hst);
            [ eapply env_agree_binders;
                [ exact HA
                | unfold typed_simulation; rewrite !motive_entries_map_fst; apply domain_list_simulation_app;
                    [ exact Hns
                    | constructor; [ apply domain_simulation_con, domain_list_simulation_app;
                                       [ exact Hpre | apply domain_list_simulation_app; assumption ] | constructor ] ]
                | rewrite motive_entries_length, Hln, List.length_rev; change (List.length (im_nparams Mv)) with (im_nn Mv);
                  rewrite Hnn; reflexivity ]
            |];
          destruct (IHV (⇓ t' b') (domain_nf_simulation_dom _ _ _ _ Hst Hsb)) as (B2 & ? & ?);
          destruct (IHT ρ' ups' pre' D HB Hu Hpre e0 Hbc Har Hnn HA
                      (fun c1 n1 B1 Hin => HBs c1 n1 B1 (or_intror Hin))) as (Bs2 & ? & ?);
          eexists; split; [ eapply fast_read_brs_cons; eassumption | apply branches_eq_upto_proofs_cons; assumption ]
      end ].
  Qed.


  Corollary fast_read_typ_simulation : forall s a a' W, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ W -> domain_simulation a a' ->
      exists W', Rtypᶠ a' in Θ ⍮ Ξ ⍮ s ↘ W' /\ nf_eq_upto_proofs W W'.
  Proof. intros; eapply (proj1 (proj2 (proj2 fast_read_simulation))); eassumption. Qed.

  Corollary fast_read_nf_simulation : forall s n n' W, Rnf n in Θ ⍮ Ξ ⍮ s ↘ W -> domain_nf_simulation n n' ->
      exists W', Rnfᶠ n' in Θ ⍮ Ξ ⍮ s ↘ W' /\ nf_eq_upto_proofs W W'.
  Proof. intros; eapply (proj1 fast_read_simulation); eassumption. Qed.
End Read.
End Sim.

#[export]
Hint Constructors domain_simulation domain_ne_simulation domain_nf_simulation dmod_simulation level_atoms_simulation domain_list_simulation domain_fields_simulation dentry_simulation ends_agree domain_list_simulation_at : mctt.
#[export]
Hint Resolve domain_simulation_lvl_suc domain_simulation_lvl_max domain_list_simulation_snoc env_agree_nil
  domain_list_simulation_app domain_list_simulation_firstn domain_list_simulation_skipn env_agree_all_args env_agree_all_cons nil_agree : mctt.

(** ** Fast Values

    A fast value ([Extraction.FastDomain]) is related to a reference one
    through its erasure, and the declarations it carries are right. *)
Section FastSim.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** The reference value [a] and the fast value [a'] *)
  Definition fast_value_simulation (a : domain) (a' : fdomain) : Prop :=
    domain_simulation Θ Ξ a (fdomain_erase a') /\ fdomain_ok Θ Ξ a'.

  (** A reference environment and a fast one, agreeing at the entries [P]
      selects *)
  Definition fast_env_agree (P : nat -> Prop) (ρ : env) (ρ' : fenv) : Prop :=
    env_agree Θ Ξ P ρ (fenv_erase ρ') /\ fenv_ok Θ Ξ ρ'.

  Lemma fast_env_agree_all : forall P ρ ρ', fast_env_agree (fun _ => True) ρ ρ' -> env_agree Θ Ξ P ρ (fenv_erase ρ').
  Proof. intros * [H _]; eapply env_agree_mono; [ exact H | intros; exact I ]. Qed.

  Lemma fast_env_agree_ok : forall P ρ ρ', fast_env_agree P ρ ρ' -> fenv_ok Θ Ξ ρ'.
  Proof. intros * [_ H]; exact H. Qed.

  Lemma fast_env_agree_nil : forall P, fast_env_agree P nil nil.
  Proof. intros; split; [ apply env_agree_nil | constructor ]. Qed.

  (** One entry more, of each kind *)
  Lemma fast_env_agree_term : forall ρ ρ' d d' t t', fast_env_agree (fun _ => True) ρ ρ' ->
      domain_simulation Θ Ξ d (fdomain_erase d') -> fdomain_ok Θ Ξ d' -> fentry_type_ok Θ Ξ t' ->
      fast_env_agree (fun _ => True) (ρ ↦ d ⦂ t) (fextend_env ρ' d' t').
  Proof.
    intros * [Hag Hok] Hs Hd Ht; split; [ rewrite fextend_env_erase | apply fextend_env_ok; assumption ].
    eapply env_agree_cons; [ exact Hag | constructor; assumption | intros; exact I ].
  Qed.

  Lemma fast_env_agree_mod : forall ρ ρ' h h' U, fast_env_agree (fun _ => True) ρ ρ' ->
      dmod_simulation Θ Ξ h (fdmod_erase h') -> fdmod_ok Θ Ξ h' ->
      fast_env_agree (fun _ => True) (ρ ↦ᵐ h ⦂ U) (fextend_env_mod ρ' h' U).
  Proof.
    intros * [Hag Hok] Hs Hh; split; [ rewrite fextend_env_mod_erase | apply fextend_env_mod_ok; assumption ].
    eapply env_agree_cons; [ exact Hag | constructor; assumption | intros; exact I ].
  Qed.

  Lemma fast_env_agree_dm : forall ρ ρ' d d' t t' h h' U, fast_env_agree (fun _ => True) ρ ρ' ->
      domain_simulation Θ Ξ d (fdomain_erase d') -> fdomain_ok Θ Ξ d' -> fentry_type_ok Θ Ξ t' ->
      dmod_simulation Θ Ξ h (fdmod_erase h') -> fdmod_ok Θ Ξ h' ->
      fast_env_agree (fun _ => True) (ρ ↦ᵈ d ⦂ t ‖ h ⦂ U) (fextend_env_dm ρ' d' t' h' U).
  Proof.
    intros * [Hag Hok] Hs Hd Ht Hsh Hh; split; [ rewrite fextend_env_dm_erase | apply fextend_env_dm_ok; assumption ].
    eapply env_agree_cons; [ exact Hag | constructor; assumption | intros; exact I ].
  Qed.
End FastSim.
