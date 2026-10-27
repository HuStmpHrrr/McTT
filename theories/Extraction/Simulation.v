(** * The Fast Evaluation Simulates the Reference One

    [Extraction.FastEval] skips the recursive result of a recursive
    argument of a constructor when the eliminator's branch does not read
    it.  Its values then differ from the reference ones only in entries of
    environments that nothing reads:

    - [dsim a a'], between a reference value [a] and a fast one [a'], is
      equality of the two up to the entries of closures' environments at
      which the closure's body is fresh ([exp_fresh]);
    - [env_agree P ρ ρ'] is agreement of two environments at the entries
      [P] selects; a term is evaluated in environments that agree where the
      term may read, [fun x => ~ exp_fresh x M].

    Evaluation, from environments that agree where the term may read, gives
    values related by [dsim] ([feval_sim]), and readback of related values
    gives the same normal form ([fread_sim]).  So both evaluations normalize
    alike, which is what [Extraction.NbE] needs. *)
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Records Fresh.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import Domain Evaluation Readback Avoid.
From Mctt.Core.Semantic.Kinds Require Import Kinds.
From Mctt.Extraction Require Import FastEval.
Import Domain_Notations.
#[local] Open Scope list_scope.

(** ** The Relation *)

(** The components of a shape, each under the domains before it, are fresh
    at [k]. *)
Fixpoint pt_fresh (k : nat) (t : ptyp) : Prop :=
  match t with
  | pt_pi B t => exp_fresh k B /\ pt_fresh (S k) t
  | pt_self _ Ps => Forall (exp_fresh k) Ps
  end.

(** The relation is over a global context: the family of the types of a
    function shape's recursive result reads the motives of the members its
    leaf paths end in, which the group's declaration fixes
    ([ends_agree]). *)
Section Sim.
  Variables (Θ : gdeps) (Ξ : gstack).

(** [dsim a a']: the reference value [a] and the fast value [a'] are equal
    up to the entries of closures' environments that the closures' bodies
    do not read; mutually, for neutrals, normal values, module values, level
    atoms, lists of values and environment entries. *)
Inductive dsim : domain -> domain -> Prop :=
(** A [Π]: related domains, environments agreeing where the codomain reads *)
| ds_pi : forall a a' (ρ ρ' : env) B,
    dsim a a' ->
    (forall x, ~ exp_fresh (S x) B -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim (Πᵈ a ρ B) (Πᵈ a' ρ' B)
(** A large universe *)
| ds_univ : forall i, dsim 𝕌ω@i 𝕌ω@i
(** A small universe at related levels *)
| ds_suniv : forall l l', dsim l l' -> dsim 𝕌@l 𝕌@l'
(** A type of levels *)
| ds_level : forall n, dsim (Levelᵈ@n) (Levelᵈ@n)
(** A level of related atoms *)
| ds_lvl : forall c xs xs', dsim_la xs xs' -> dsim (lvᵈ c xs) (lvᵈ c xs')
(** The unit type *)
| ds_True : dsim ⊤ᵈ ⊤ᵈ
(** The unit's element *)
| ds_true : dsim ⋆ᵈ ⋆ᵈ
(** The empty type *)
| ds_False : dsim ⊥ᵈ ⊥ᵈ
(** A λ: environments agreeing where the body reads *)
| ds_fn : forall (ρ ρ' : env) M,
    (forall x, ~ exp_fresh (S x) M -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim (λᵈ ρ M) (λᵈ ρ' M)
(** A neutral at related types *)
| ds_neut : forall a a' m m', dsim a a' -> dsim_ne m m' -> dsim (⇑ a m) (⇑ a' m')
(** A member of related module values *)
| ds_member : forall h h' ch, dmsim h h' -> dsim (d_member h ch) (d_member h' ch)
(** A type former at related arguments *)
| ds_indty : forall p k args args', dsim_list args args' -> dsim (d_ind p k args) (d_ind p k args')
(** A constructor at related arguments *)
| ds_con : forall p k c args args', dsim_list args args' -> dsim (d_con p k c args) (d_con p k c args')
(** A recursive result of a function shape: the environments agree where
    the blocks' motives and branches may read, as [dsim_ne_elim] *)
| ds_ihfn : forall (ρ ρ' : env) Bks p ups ups' t i f f',
    (forall b, In b Bks ->
       (forall x, ~ exp_fresh (eb_nm b + x) (eb_motive b) -> desim (env_entry ρ x) (env_entry ρ' x)) /\
       (forall c n B, In (c, n, B) (eb_brs b) -> forall x, ~ exp_fresh (n + x) B -> desim (env_entry ρ x) (env_entry ρ' x))) ->
    dsim_list ups ups' ->
    dsim f f' -> dsim (d_ihfn ρ Bks p ups t i f) (d_ihfn ρ' Bks p ups' t i f')
(** The family of the type of an argument of a function shape: where the
    rest of the shape may read under the domain the family binds *)
| ds_shfam : forall p ups ups' (ρ ρ' : env) t,
    dsim_list ups ups' ->
    (forall x, ~ pt_fresh (S x) t -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim (d_shfam p ups ρ t) (d_shfam p ups' ρ' t)
(** The family of the type of a recursive result: where the motives of the
    members the shape's leaf paths end in may read ([ends_agree]), at
    related uniform parameters, and where the rest of the shape may read *)
| ds_ihfam : forall (ρm ρm' : env) As p ups ups' (ρ ρ' : env) t i f f',
    ends_agree p As ρm ρm' t ->
    dsim_list ups ups' ->
    (forall x, ~ pt_fresh (S x) t -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim f f' -> dsim (d_ihfam ρm As p ups ρ t i f) (d_ihfam ρm' As p ups' ρ' t i f')
(** A record's type former at related arguments *)
| ds_record : forall p args args', dsim_list args args' -> dsim (d_record p args) (d_record p args')
(** A tuple of related fields *)
| ds_tuple : forall vs vs', dsim_fields vs vs' -> dsim (d_tuple vs) (d_tuple vs')
with dsim_ne : domain_ne -> domain_ne -> Prop :=
(** A variable *)
| dsim_ne_var : forall x, dsim_ne (#ᵈ x) (#ᵈ x)
(** An application *)
| dsim_ne_app : forall m m' n n', dsim_ne m m' -> dsim_nf n n' -> dsim_ne (m $ᵈ n) (m' $ᵈ n')
(** A stuck [efq]: environments agreeing where its motive reads *)
| dsim_ne_exfalso : forall (ρ ρ' : env) A m m',
    (forall x, ~ exp_fresh (S x) A -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim_ne m m' ->
    dsim_ne (efqᵈ m under ρ return A) (efqᵈ m' under ρ' return A)
(** A global *)
| dsim_ne_glob : forall p, dsim_ne (d_glob p) (d_glob p)
(** A stuck eliminator: the environments agree where the blocks' motives
    and branches may read, under their binders. *)
| dsim_ne_elim : forall (ρ ρ' : env) Bks p ups ups' j args args' m m',
    (forall b, In b Bks ->
       (forall x, ~ exp_fresh (eb_nm b + x) (eb_motive b) -> desim (env_entry ρ x) (env_entry ρ' x)) /\
       (forall c n B, In (c, n, B) (eb_brs b) -> forall x, ~ exp_fresh (n + x) B -> desim (env_entry ρ x) (env_entry ρ' x))) ->
    dsim_list ups ups' -> dsim_list args args' -> dsim_ne m m' ->
    dsim_ne (d_elim ρ Bks p ups j args m) (d_elim ρ' Bks p ups' j args' m')
(** The field of a neutral *)
| dsim_ne_proj : forall f m m', dsim_ne m m' -> dsim_ne (d_proj f m) (d_proj f m')
with dsim_nf : domain_nf -> domain_nf -> Prop :=
(** A value at a type, both related *)
| dsim_nf_dom : forall a a' m m', dsim a a' -> dsim m m' -> dsim_nf (⇓ a m) (⇓ a' m')
with dmsim : dmod -> dmod -> Prop :=
(** A global module at related arguments *)
| dmsim_global : forall p args args', dsim_list args args' -> dmsim (dm_global p args) (dm_global p args')
(** A closure: the environments agree where the unit may read. *)
| dmsim_local : forall Δ D (ρ ρ' : env),
    (forall x, ~ gunit_fresh x (gu_mk Δ D) -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dmsim (dm_local Δ D ρ) (dm_local Δ D ρ')
(** A member closure of related module values *)
| dmsim_member : forall h h' ch, dmsim h h' -> dmsim (dm_member h ch) (dm_member h' ch)
with dsim_la : list (nat * nat * domain_ne) -> list (nat * nat * domain_ne) -> Prop :=
(** No atom *)
| dsim_la_nil : dsim_la nil nil
(** Related first atoms, then the rest *)
| dsim_la_cons : forall k n m m' xs xs', dsim_ne m m' -> dsim_la xs xs' -> dsim_la ((k, n, m) :: xs) ((k, n, m') :: xs')
with dsim_list : list domain -> list domain -> Prop :=
(** No value *)
| dsim_list_nil : dsim_list nil nil
(** Related first values, then the rest *)
| dsim_list_cons : forall a a' args args', dsim a a' -> dsim_list args args' -> dsim_list (a :: args) (a' :: args')
(** Named fields, the same names at related values *)
with dsim_fields : list (string * domain) -> list (string * domain) -> Prop :=
(** No field *)
| dsim_fields_nil : dsim_fields nil nil
(** A field of the same name at related values, then the rest *)
| dsim_fields_cons : forall f a a' vs vs', dsim a a' -> dsim_fields vs vs' -> dsim_fields ((f, a) :: vs) ((f, a') :: vs')
with desim : dentry -> dentry -> Prop :=
(** Related terms *)
| desim_term : forall d d', dsim d d' -> desim (de_term d) (de_term d')
(** Related modules *)
| desim_mod : forall h h', dmsim h h' -> desim (de_mod h) (de_mod h')
(** Related terms with related module parts *)
| desim_dm : forall d d' h h', dsim d d' -> dmsim h h' -> desim (de_dm d h) (de_dm d' h')
(** [ends_agree p As ρm ρm' t]: the motives [As] in [ρm] and [ρm'] agree
    where the motive of each member a leaf path of the shape [t] ends in
    may read, under that path's end's parameters and the argument; at a
    record view, along its recursive fields, as [Core.Semantic.Avoid]'s
    [ends_fresh] *)
with ends_agree : qname -> list exp -> env -> env -> ptyp -> Prop :=
(** The end, at a member with a block: its motive *)
| ends_agree_self : forall p As ρm ρm' D j Mj Ps,
    ind_lookup Θ Ξ p = Some D -> ind_member D j = Some Mj -> im_is_rview Mj = false ->
    (forall x, ~ exp_fresh (S (List.length Ps) + x) (List.nth j As a_True) -> desim (env_entry ρm x) (env_entry ρm' x)) ->
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
Hint Constructors dsim dsim_ne dsim_nf dmsim dsim_la dsim_list dsim_fields desim ends_agree : mctt.

(** Agreement of two environments at the entries [P] selects. *)
Definition env_agree (P : nat -> Prop) (ρ ρ' : env) : Prop :=
  forall x, P x -> desim (env_entry ρ x) (env_entry ρ' x).

(** Agreement of two environments where the blocks of an eliminator may
    read: each motive under its binders, and each branch under its own.
    (The annotations are never evaluated.)  It is the premise of [dsim_ne_elim]
    and [ds_ihfn]. *)
Definition blocks_agree (Bks : list eblock) (ρ ρ' : env) : Prop :=
  forall b, In b Bks ->
    env_agree (fun x => ~ exp_fresh (eb_nm b + x) (eb_motive b)) ρ ρ' /\
    (forall c n B, In (c, n, B) (eb_brs b) -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ').

(** ** Environments *)

Lemma env_agree_mono : forall P Q ρ ρ', env_agree P ρ ρ' -> (forall x, Q x -> P x) -> env_agree Q ρ ρ'.
Proof. intros * H HQ x Hx; apply H, HQ, Hx. Qed.

Lemma env_agree_nil : forall P, env_agree P nil nil.
Proof. intros P x _; induction x; cbn; [ repeat constructor | exact IHx ]. Qed.

Lemma env_agree_cons : forall P Q e e' ρ ρ',
    env_agree P ρ ρ' -> desim e e' -> (forall y, Q (S y) -> P y) -> env_agree Q (e :: ρ) (e' :: ρ').
Proof. intros * H He HQ [| y] Hy; cbn; [ exact He | apply H, HQ, Hy ]. Qed.

Lemma dsim_list_length : forall args args', dsim_list args args' -> List.length args = List.length args'.
Proof. induction 1; cbn; congruence. Qed.

Lemma env_agree_args : forall args args' P Q ρ ρ',
    env_agree P ρ ρ' -> dsim_list args args' ->
    (forall y, Q (List.length args + y) -> P y) ->
    env_agree Q (env_args ρ args) (env_args ρ' args').
Proof.
  induction args as [| a args IH]; intros * Hρ Ha HQ; inversion Ha; subst; cbn.
  - eapply env_agree_mono; [ exact Hρ | intros y Hy; apply HQ, Hy ].
  - eapply IH; [ eapply env_agree_cons with (Q := fun y => match y with 0 => True | S y => P y end);
                 [ exact Hρ | constructor; assumption | intros; assumption ]
               | eassumption |].
    intros [| y] Hy; [ exact I |]; apply HQ.
    replace (List.length args + S y) with (S (List.length args) + y) in Hy by lia; exact Hy.
Qed.

Lemma env_agree_var : forall P ρ ρ' x, env_agree P ρ ρ' -> P x -> dsim (ρ x) (ρ' x).
Proof. intros * H Hx; unfold env_var; destruct (H x Hx); [ assumption | constructor | assumption ]. Qed.

Lemma env_agree_mod : forall P ρ ρ' x, env_agree P ρ ρ' -> P x -> dmsim (env_mod ρ x) (env_mod ρ' x).
Proof. intros * H Hx; unfold env_mod; destruct (H x Hx); [ repeat constructor | assumption | assumption ]. Qed.

(** ** Levels *)

Lemma dsort_sim : forall a a', dsim a a' -> dsort a = dsort a'.
Proof. intros * H; destruct H; reflexivity. Qed.

Lemma dlvl_cst_sim : forall d d', dsim d d' -> dlvl_cst d = dlvl_cst d'.
Proof. intros * H; destruct H; reflexivity. Qed.

Lemma dlvl_atoms_sim : forall d d', dsim d d' -> dsim_la (dlvl_atoms d) (dlvl_atoms d').
Proof.
  intros * H; destruct H; cbn; try constructor; try assumption.
  erewrite dsort_sim by eassumption; repeat constructor; assumption.
Qed.

Lemma dsim_la_suc : forall xs xs', dsim_la xs xs' ->
    dsim_la (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs)
            (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs').
Proof. induction 1; cbn; constructor; assumption. Qed.

Lemma dsim_la_app : forall xs xs' ys ys', dsim_la xs xs' -> dsim_la ys ys' -> dsim_la (xs ++ ys) (xs' ++ ys').
Proof. induction 1; intros; cbn; [ assumption | constructor; auto ]. Qed.

Lemma dsim_lvl_suc : forall d d', dsim d d' -> dsim (dlvl_suc d) (dlvl_suc d').
Proof.
  intros * H; unfold dlvl_suc; rewrite (dlvl_cst_sim _ _ H).
  constructor; apply dsim_la_suc, dlvl_atoms_sim, H.
Qed.

Lemma dsim_lvl_max : forall d d' e e', dsim d d' -> dsim e e' -> dsim (dlvl_max d e) (dlvl_max d' e').
Proof.
  intros * Hd He; unfold dlvl_max; rewrite (dlvl_cst_sim _ _ Hd), (dlvl_cst_sim _ _ He).
  constructor; apply dsim_la_app; apply dlvl_atoms_sim; assumption.
Qed.

Lemma dsim_list_snoc : forall args args' n n', dsim_list args args' -> dsim n n' ->
    dsim_list (args ++ n :: nil) (args' ++ n' :: nil).
Proof. induction 1; intros; cbn; repeat constructor; auto. Qed.

Lemma dsim_list_app : forall args args' bs bs', dsim_list args args' -> dsim_list bs bs' ->
    dsim_list (args ++ bs) (args' ++ bs').
Proof. induction 1; intros; cbn; [ assumption | constructor; auto ]. Qed.

Lemma dsim_list_firstn : forall n args args', dsim_list args args' -> dsim_list (firstn n args) (firstn n args').
Proof. intros n args args' H; revert n; induction H; intros [| n]; cbn; constructor; auto. Qed.

Lemma dsim_list_skipn : forall n args args', dsim_list args args' -> dsim_list (skipn n args) (skipn n args').
Proof. intros n args args' H; revert n; induction H; intros [| n]; cbn; try constructor; auto. Qed.

(** The fields of a tuple, named alike at related values. *)
Lemma dsim_fields_combine : forall fs vs vs', dsim_list vs vs' -> dsim_fields (List.combine fs vs) (List.combine fs vs').
Proof. induction fs as [| f fs IH]; intros vs vs' H; destruct H; cbn; constructor; auto. Qed.

(** A field of related tuples: related values. *)
Lemma field_lookup_sim : forall vs vs' f r, dsim_fields vs vs' -> field_lookup vs f = Some r ->
    exists r', field_lookup vs' f = Some r' /\ dsim r r'.
Proof.
  induction 1 as [| g a a' vs vs' Ha Hvs IH]; cbn; intros Hl; [ discriminate |].
  destruct (String.eqb f g); [ injection Hl as <-; eauto | auto ].
Qed.

(** An entry of related lists: related values. *)
Lemma dsim_list_nth_error : forall args args' k r, dsim_list args args' -> List.nth_error args k = Some r ->
    exists r', List.nth_error args' k = Some r' /\ dsim r r'.
Proof.
  intros * H; revert k; induction H as [| a a' args args' Ha Hargs IH]; intros [| k]; cbn; intros Hk;
    try discriminate; [ injection Hk as <-; eauto | auto ].
Qed.

(** Agreement everywhere: the environments of the telescopes of a
    declaration, whose types are read at every entry. *)
Lemma env_agree_all_args : forall args args' ρ ρ',
    env_agree (fun _ => True) ρ ρ' -> dsim_list args args' ->
    env_agree (fun _ => True) (env_args ρ args) (env_args ρ' args').
Proof. intros * Hρ Ha; eapply env_agree_args; [ exact Hρ | exact Ha | intros; exact I ]. Qed.

Lemma env_agree_all_cons : forall ρ ρ' d d',
    env_agree (fun _ => True) ρ ρ' -> dsim d d' -> env_agree (fun _ => True) (ρ ↦ d) (ρ' ↦ d').
Proof. intros * Hρ Hd; eapply env_agree_cons; [ exact Hρ | constructor; exact Hd | intros; exact I ]. Qed.

(** An environment of closed terms' values only: it agrees wherever. *)
Lemma env_agree_nil_args : forall P args args', dsim_list args args' ->
    env_agree P (env_args nil args) (env_args nil args').
Proof.
  intros * Ha; eapply env_agree_mono; [ apply env_agree_all_args; [ apply env_agree_nil | exact Ha ] | intros; exact I ].
Qed.

(** The environment of a closure under its [n] binders: the [n] entries are
    related, and the rest agree where the body may read. *)
Lemma env_agree_binders : forall n B args args' ρ ρ',
    env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ' -> dsim_list args args' -> List.length args = n ->
    env_agree (fun x => ~ exp_fresh x B) (env_args ρ args) (env_args ρ' args').
Proof. intros * Hρ Ha Hl; eapply env_agree_args; [ exact Hρ | exact Ha |]; intros y Hy; rewrite Hl in Hy; exact Hy. Qed.

(** Two lists of values related at the entries [P] selects, once they
    extend an environment: the entry of [a] in [env_args ρ (a :: l)] is
    [List.length l]. *)
Inductive dsim_list_at (P : nat -> Prop) : list domain -> list domain -> Prop :=
(** No value *)
| dsim_list_at_nil : dsim_list_at P nil nil
(** The first values related if [P] selects their entry, then the rest *)
| dsim_list_at_cons : forall a a' l l', (P (List.length l) -> dsim a a') -> dsim_list_at P l l' ->
    dsim_list_at P (a :: l) (a' :: l').

#[local]
Hint Constructors dsim_list_at : mctt.

Lemma dsim_list_at_app : forall P l1 l1' l2 l2', dsim_list l1 l1' -> dsim_list_at P l2 l2' ->
    dsim_list_at P (l1 ++ l2) (l1' ++ l2').
Proof. induction 1; intros; cbn; [ assumption | constructor; auto ]. Qed.

Lemma dsim_list_at_length : forall P l l', dsim_list_at P l l' -> List.length l = List.length l'.
Proof. induction 1; cbn; congruence. Qed.

Lemma env_agree_args_at : forall P Q args args' ρ ρ',
    env_agree P ρ ρ' -> dsim_list_at Q args args' ->
    (forall y, Q (List.length args + y) -> P y) ->
    env_agree Q (env_args ρ args) (env_args ρ' args').
Proof.
  intros * Hρ Ha; revert P ρ ρ' Hρ; induction Ha as [| a a' l l' Hh Ht IH]; intros P ρ ρ' Hρ HQ; cbn.
  - eapply env_agree_mono; [ exact Hρ | intros y Hy; apply HQ, Hy ].
  - eapply IH with (P := fun y => Q (List.length l + y)); [| intros; assumption ].
    intros [| y] Hy; cbn.
    + constructor; apply Hh; rewrite Nat.add_0_r in Hy; exact Hy.
    + apply Hρ, HQ; cbn; replace (S (List.length l + y)) with (List.length l + S y) by lia; exact Hy.
Qed.

(** The environment of a branch under its [n] binders, whose last entries,
    the recursive results, are related only where the branch reads. *)
Lemma env_agree_binders_at : forall n B args args' ρ ρ',
    env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ' ->
    dsim_list_at (fun x => ~ exp_fresh x B) args args' -> List.length args = n ->
    env_agree (fun x => ~ exp_fresh x B) (env_args ρ args) (env_args ρ' args').
Proof. intros * Hρ Ha Hl; eapply env_agree_args_at; [ exact Hρ | exact Ha |]; intros y Hy; rewrite Hl in Hy; exact Hy. Qed.

(** The type of an argument of a function shape, and of its recursive
    result: a [Π] over a family in an environment that holds only it. *)
Lemma dsim_fam_pi : forall b b' d d', dsim b b' -> dsim d d' ->
    dsim (Πᵈ b (nil ↦ d) fam_cod) (Πᵈ b' (nil ↦ d') fam_cod).
Proof.
  intros * Hb Hd; constructor; [ exact Hb |].
  intros [| x] _; cbn; [ constructor; exact Hd | apply env_agree_nil with (P := fun _ => True); exact I ].
Qed.

(** The parts of an eliminator may read only what the eliminator may: its
    blocks, under their binders. *)
Lemma agree_elim_blocks : forall oq Us j Bks M ρ ρ',
    env_agree (fun x => ~ exp_fresh x (a_elim oq Us j Bks M)) ρ ρ' -> blocks_agree Bks ρ ρ'.
Proof.
  intros * H b Hb; split.
  - intros x Hx; apply H; intros Hf; apply Hx.
    pose proof (ofresh_elim_blocks (Some x) oq Us j Bks M Hf b Hb) as [Hm _]; exact Hm.
  - intros c n B Hin x Hx; apply H; intros Hf; apply Hx.
    pose proof (ofresh_elim_blocks (Some x) oq Us j Bks M Hf b Hb) as [_ Hbr]; exact (Hbr _ _ _ Hin).
Qed.

(** The group an eliminator eliminates by is read off related values
    alike. *)
Lemma elim_grp_of_sim : forall oq m m', dsim m m' -> elim_grp_of oq m' = elim_grp_of oq m.
Proof.
  intros * H; destruct oq; [ reflexivity |].
  destruct H; cbn; try reflexivity.
  match goal with H : dsim _ _ |- _ => destruct H; reflexivity end.
Qed.

(** The motives at the ends of the leaf paths of a shape, read where the
    blocks may: each end at as many parameters as its member's motive
    binds ([rview_leaf_arity], [blocks_nm_at]), down the record views'
    fields by their order, as [Core.Semantic.Avoid]'s
    [ends_fresh_of_blocks]. *)
Lemma ends_agree_of_blocks : forall p D Bks ρ ρ', ind_lookup Θ Ξ p = Some D -> rview_leaf_arity D ->
    blocks_nm_at D None Bks -> blocks_agree Bks ρ ρ' ->
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
      pose proof (rview_leaf_plen _ Har _ _ _ _ HMj ltac:(unfold im_is_rview; rewrite Hh; reflexivity)
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
    blocks_nm_at D None Bks -> blocks_agree Bks ρ ρ' -> cargs_plen D gs ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_agree p (blocks_motives Bks) ρ ρ' t.
Proof. intros * HD Har Hnm HB Hpl gs1 t gs2 E; exact (ends_agree_of_blocks _ _ _ _ _ HD Har Hnm HB t (Hpl gs1 t gs2 E)). Qed.

#[local]
Hint Resolve dsim_lvl_suc dsim_lvl_max dsim_list_snoc env_agree_nil
  dsim_list_app dsim_list_firstn dsim_list_skipn env_agree_all_args env_agree_all_cons : mctt.

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

Lemma env_agree_above_cons : forall n P e e' ρ ρ',
    env_agree (above n P) ρ ρ' -> desim e e' -> env_agree (above (S n) P) (e :: ρ) (e' :: ρ').
Proof.
  intros * H He [| z] Hz; cbn; [ exact He |].
  apply H; destruct Hz as [Hz | (y & Hy & HP)]; [ left; lia | right; exists y; split; [ lia | exact HP ] ].
Qed.

Lemma nil_agree : forall x, desim (env_entry nil x) (env_entry nil x).
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
  | H : dsim (_ _) _ |- _ => inversion H; subst; clear H
  | H : dsim (_ _ _) _ |- _ => inversion H; subst; clear H
  | H : dsim (_ _ _ _) _ |- _ => inversion H; subst; clear H
  | H : dsim (_ _ _ _ _) _ |- _ => inversion H; subst; clear H
  | H : dsim (_ _ _ _ _ _) _ |- _ => inversion H; subst; clear H
  | H : dsim ⊤ᵈ _ |- _ => inversion H; subst; clear H
  | H : dsim ⋆ᵈ _ |- _ => inversion H; subst; clear H
  | H : dsim ⊥ᵈ _ |- _ => inversion H; subst; clear H
  | H : dmsim (_ _ _) _ |- _ => inversion H; subst; clear H
  | H : dmsim (_ _ _ _) _ |- _ => inversion H; subst; clear H
  | H : dsim_list (_ :: _) _ |- _ => inversion H; subst; clear H
  | H : dsim_list nil _ |- _ => inversion H; subst; clear H
  | Hs : modexp_spine ?H = (?R, ?args, ?pre), Hρ : env_agree (fun x => ~ exp_fresh x (a_mem ?H _)) ?ρ ?ρ' |- _ =>
      destruct (agree_spine _ _ _ _ _ _ _ Hs Hρ); clear Hρ
  | H : forall x, ~ @?F x -> desim (env_entry ?ρ x) (env_entry ?ρ' x) |- _ =>
      change (env_agree (fun x => ~ F x) ρ ρ') in H; cbv beta in H
  | H : forall b, In b ?Bks -> (forall x, _ -> desim (env_entry ?ρ x) (env_entry ?ρ' x)) /\ _ |- _ =>
      change (blocks_agree Bks ρ ρ') in H
  end.

(** A related entry: a related value, or the closure of a unit over
    environments that agree where the unit may read. *)
Ltac ent_tac :=
  first [ constructor; eassumption
        | constructor; solve [ eauto with mctt ]
        | apply desim_mod; apply dmsim_local;
          eapply env_agree_mono; [ eassumption | nf_sub ] ].

(** An environment that agrees where a term may read, for one of its parts:
    the same environment, or one extended by related entries, or one of
    values of closed terms. *)
Ltac agree_tac :=
  first [ eassumption
        | match goal with Hρ : env_agree _ ?ρ _ |- env_agree _ ?ρ _ =>
            eapply env_agree_mono; [ exact Hρ | nf_sub ] end
        | match goal with |- env_agree _ (env_args nil ?args) _ =>
            apply env_agree_nil_args; solve [ eauto with mctt ] end
        | match goal with
          | |- env_agree _ (_ :: ?ρ) _ => idtac
          | |- env_agree _ (extend_env ?ρ _) _ => unfold extend_env
          | |- env_agree _ (extend_env_mod ?ρ _) _ => unfold extend_env_mod
          end;
          match goal with |- env_agree _ (_ :: ?ρ) _ =>
            match goal with Hρ : env_agree _ ?ρ _ |- _ =>
              eapply env_agree_cons; [ exact Hρ | ent_tac | nf_sub ] end end
        | match goal with |- env_agree _ nil _ => apply env_agree_nil end
        | match goal with |- env_agree _ (env_args ?ρ ?args) _ =>
            match goal with Hρ : env_agree _ ?ρ _, Ha : dsim_list args _ |- _ =>
              eapply env_agree_args; [ exact Hρ | exact Ha |];
              let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
              intros y Hy Hf; apply Hy; cbn in Hf;
              repeat match goal with He : List.length args = List.length _ |- _ => rewrite He end;
              tauto end end ].

(** A premise on the length of the fast arguments, from the reference ones. *)
Ltac len_tac :=
  match goal with Hl : dsim_list ?a ?a' |- context [List.length ?a'] =>
    rewrite <- (dsim_list_length _ _ Hl); eassumption end.

(** Forward reasoning: each induction hypothesis, at the fast arguments that
    are related to its reference ones. *)
Ltac sim_fwd :=
  match goal with
  | IH : forall ρ0, env_agree ?P ?ρ ρ0 -> exists _, _ /\ _ |- _ =>
      let H' := fresh "Ha" in
      eassert (H' : env_agree P ρ _) by agree_tac;
      destruct (IH _ H') as (? & ? & ?); clear IH H'
  | IH : forall m0 n0, dsim ?m m0 -> dsim ?n n0 -> exists _, _ /\ _, Hm : dsim ?m ?m', Hn : dsim ?n ?n' |- _ =>
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  | IH : forall m0 n0, dsim ?m m0 -> dsim_list ?n n0 -> exists _, _ /\ _, Hm : dsim ?m ?m', Hn : dsim_list ?n ?n' |- _ =>
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  | IH : forall m0 n0, dmsim ?m m0 -> dsim ?n n0 -> exists _, _ /\ _, Hm : dmsim ?m ?m', Hn : dsim ?n ?n' |- _ =>
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  | IH : forall m0, dmsim ?m m0 -> exists _, _ /\ _, Hm : dmsim ?m ?m' |- _ =>
      destruct (IH _ Hm) as (? & ? & ?); clear IH
  | IH : forall m0 n0, dmsim ?m m0 -> dsim_list ?n n0 -> exists _, _ /\ _, Hm : dmsim ?m ?m', Hn : dsim_list ?n ?n' |- _ =>
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  | IH : forall m0 n0, dsim ?m m0 -> dsim_list ?n n0 -> exists _, _ /\ _, Hn : dsim_list ?n ?n' |- _ =>
      let Hm := fresh "Hm" in
      eassert (Hm : dsim m _) by (eauto with mctt);
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  | IH : forall m0, dmsim ?m m0 -> exists _, _ /\ _ |- _ =>
      let Hm := fresh "Hm" in
      eassert (Hm : dmsim m _) by (eauto with mctt);
      destruct (IH _ Hm) as (? & ? & ?); clear IH
  (** The member a view stands for, at related uniform parameters *)
  | IH : forall u0, dsim_list ?u u0 -> exists _, _ /\ _, Hu : dsim_list ?u ?u' |- _ =>
      destruct (IH _ Hu) as (? & ? & ?); clear IH
  end.

(** The goal: the fast rule, and the relation between the results, whose
    closures agree where the reference ones may read. *)
Ltac sim_fin :=
  eexists; split;
  [ econstructor; solve [ eassumption | len_tac
                        | rewrite <- (dsim_list_length _ _ ltac:(eassumption)); eassumption ]
  | repeat first [ eassumption
                 | eapply env_agree_var; [ eassumption | cbn; intros Hne; apply Hne; reflexivity ]
                 | eapply env_agree_mod; [ eassumption | cbn; intros Hne; apply Hne; reflexivity ]
                 | solve [ eauto with mctt ]
                 | constructor
                 | match goal with |- forall x, ~ _ -> desim _ _ =>
                     let x := fresh "x" in let Hx := fresh "Hx" in
                     intros x Hx; match goal with Hρ : env_agree _ _ _ |- _ =>
                       apply Hρ; let Hf := fresh "Hf" in intros Hf; apply Hx; cbn in Hf; tauto end end ] ].

(** ** Kinds

    The kinds of members read an environment only through the module
    entries the syntax reads, so environments that agree where the syntax
    may read give the same kinds, and the same generated entries. *)

Lemma env_agree_kpad : forall n (P Q : nat -> Prop) ρ ρ', env_agree P ρ ρ' -> (forall y, Q (n + y) -> P y) ->
    env_agree Q (kpad n ρ) (kpad n ρ').
Proof.
  unfold kpad; induction n as [| n IH]; intros * Hρ HQ; cbn [List.repeat app].
  - eapply env_agree_mono; [ exact Hρ | exact HQ ].
  - eapply env_agree_cons with (P := fun y => Q (S y)); [| repeat constructor | intros; assumption ].
    eapply IH; [ exact Hρ | intros y Hy; apply HQ; exact Hy ].
Qed.

(** A weakening past [k] entries reads none of them. *)
Lemma modexp_unfresh_shiftn : forall E k z, ~ modexp_fresh z (modexp_wk E (wk_shiftn k)) ->
    exists w, z = k + w /\ ~ modexp_fresh w E.
Proof.
  intros * Hz.
  destruct (Nat.lt_ge_cases z k) as [Hlt | Hge].
  - exfalso; apply Hz; apply (proj1 (proj2 syn_wk_fresh)).
    intros x; cbn [wk_shiftn]; lia.
  - exists (z - k); split; [ lia |]; intros Hf; apply Hz.
    replace z with (k + (z - k)) by lia; apply modexp_fresh_shiftn; exact Hf.
Qed.

Lemma above_above_inv : forall n m P z, above (n + m) P z -> above n (above m P) z.
Proof.
  intros * [Hz | (w & -> & Hw)].
  - destruct (Nat.lt_ge_cases z n) as [Hlt | Hge]; [ left; exact Hlt |].
    right; exists (z - n); split; [ lia | left; lia ].
  - right; exists (m + w); split; [ lia | right; exists w; split; [ reflexivity | exact Hw ] ].
Qed.

Section KindSim.

  Lemma kgens_env_sim : forall ρ0 H its gs, kgens Θ Ξ ρ0 H its gs ->
      forall (Q : nat -> Prop), (forall x, ~ modexp_fresh x H -> Q x) ->
      forall gs1, (forall g, In g gs1 -> In g gs) ->
      forall k ρ ρ', env_agree (above k Q) ρ ρ' ->
      env_agree (above (List.length gs1 + k) Q) (kgens_env ρ k gs1) (kgens_env ρ' k gs1).
  Proof.
    intros * Hg Q HQ gs1; induction gs1 as [| g gs1 IH]; intros Hin k ρ ρ' Hρ; cbn [kgens_env List.length]; [ exact Hρ |].
    rewrite Nat.add_succ_comm; apply IH; [ intros; apply Hin; right; assumption |].
    apply env_agree_above_cons; [ exact Hρ |].
    destruct (kgens_shape _ _ _ _ _ _ Hg g (Hin g (or_introl eq_refl)))
      as [(d & pv & A0 & M & ->) | [(d & pv & E & ->) | (d & pv & A0 & M & E & ->)]];
      cbn [kentry]; [ repeat constructor | |].
    - constructor; apply dmsim_local.
      intros z Hz; apply Hρ; cbn in Hz.
      assert (Hz' : ~ modexp_fresh z (modexp_wk E (wk_shiftn k))) by (intros Hf; apply Hz; split; [ exact I | exact Hf ]).
      destruct (modexp_unfresh_shiftn _ _ _ Hz') as (w & -> & Hw).
      right; exists w; split; [ reflexivity | apply HQ ].
      destruct (kgens_alias_target _ _ _ _ _ _ Hg _ _ _ (Hin _ (or_introl eq_refl))) as [-> | (n & ->)]; [ exact Hw |].
      intros Hf; apply Hw; exact Hf.
    - (* a definition with a module part: a placeholder and the alias of
         the selection *)
      constructor; [ constructor | apply dmsim_local ].
      intros z Hz; apply Hρ; cbn in Hz.
      assert (Hz' : ~ modexp_fresh z (modexp_wk E (wk_shiftn k))) by (intros Hf; apply Hz; split; [ exact I | exact Hf ]).
      destruct (modexp_unfresh_shiftn _ _ _ Hz') as (w & -> & Hw).
      right; exists w; split; [ reflexivity | apply HQ ].
      destruct (kgens_dm_target _ _ _ _ _ _ Hg _ _ _ _ _ (Hin _ (or_introl eq_refl))) as (n & ->).
      intros Hf; apply Hw; exact Hf.
  Qed.

  Lemma kind_sim :
    (forall h ch k, dkind Θ Ξ h ch k -> forall h', dmsim h h' -> dkind Θ Ξ h' ch k) /\
    (forall ρ U ch k, ukind Θ Ξ ρ U ch k -> forall ρ', env_agree (fun x => ~ gunit_fresh x U) ρ ρ' -> ukind Θ Ξ ρ' U ch k) /\
    (forall ρ H ch k, skind Θ Ξ ρ H ch k -> forall ρ', env_agree (fun x => ~ modexp_fresh x H) ρ ρ' -> skind Θ Ξ ρ' H ch k) /\
    (forall ρ Φ ρ1, kenv Θ Ξ ρ Φ ρ1 -> forall ρ' (P : nat -> Prop), (forall x, ~ gmod_fresh x Φ -> P x) -> env_agree P ρ ρ' ->
       exists ρ1', kenv Θ Ξ ρ' Φ ρ1' /\ env_agree (above (gm_binders Φ) P) ρ1 ρ1') /\
    (forall ρ Φ Φx, kbody Θ Ξ ρ Φ Φx -> forall ρ' (P : nat -> Prop), (forall x, ~ gmod_fresh x Φ -> P x) -> env_agree P ρ ρ' ->
       kbody Θ Ξ ρ' Φ Φx) /\
    (forall ρ H its gs, kgens Θ Ξ ρ H its gs -> forall ρ', env_agree (fun x => ~ modexp_fresh x H) ρ ρ' -> kgens Θ Ξ ρ' H its gs).
  Proof.
    apply kind_mut_ind.
    (* values *)
    1-2: intros * Hr h' Hs; inversion Hs; subst; econstructor; eassumption.
    - intros * Hd Hl h' Hs; inversion Hs; subst; econstructor; eassumption.
    - intros * Hr Hc Hu _ h' Hs; inversion Hs; subst; econstructor; eassumption.
    - intros * Hr Hd Hu _ h' Hs; inversion Hs; subst; econstructor; eassumption.
    - intros * Hna Hc _ IH h' Hs; inversion Hs; subst; apply dkind_global_step; [ exact Hna | exact Hc | apply IH; constructor; assumption ].
    - intros * Hu IH h' Hs; inversion Hs; subst; constructor; auto.
    - intros * Hd IH Hc h' Hs; inversion Hs; subst; constructor; auto.
    - intros * Hd IH h' Hs; inversion Hs; subst; apply dkind_member_dm; auto.
    (* units *)
    - intros; constructor.
    - intros; econstructor; eassumption.
    - (* a module of a body, read in the environment of the body before it *)
      intros * Hp Hk IHk Hu IHu ρ' Hρ.
      destruct (IHk (kpad (List.length Δ) ρ') (fun x => ~ gmod_fresh x Φ)) as (ρ1' & Hk1 & Hρ1).
      { intros x Hx Hf; apply Hx; pose proof (prefix_upto_fresh _ _ _ _ Hp Hf) as Hf'; cbn in Hf'; tauto. }
      { eapply env_agree_kpad; [ exact Hρ |]; intros y0 Hy Hf; apply Hy; cbn in Hf |- *; destruct Hf as [_ Hf]; exact Hf. }
      eapply ukind_mod; [ eassumption | exact Hk1 |].
      apply IHu; eapply env_agree_mono; [ exact Hρ1 | apply above_of ].
      intros y0 Hy Hf; apply Hy; pose proof (prefix_upto_fresh _ _ _ _ Hp Hf) as Hf'; cbn in Hf'; tauto.
    - (* a definition with a module part of a body, itself: by its module
         part, read in the environment of the body before it *)
      intros * Hp Hk IHk Hu IHu ρ' Hρ.
      destruct (IHk (kpad (List.length Δ) ρ') (fun x => ~ gmod_fresh x Φ)) as (ρ1' & Hk1 & Hρ1).
      { intros x Hx Hf; apply Hx; pose proof (prefix_upto_fresh _ _ _ _ Hp Hf) as Hf'; cbn in Hf'; tauto. }
      { eapply env_agree_kpad; [ exact Hρ |]; intros y0 Hy Hf; apply Hy; cbn in Hf |- *; destruct Hf as [_ Hf]; exact Hf. }
      eapply ukind_dm_here; [ eassumption | exact Hk1 |].
      apply IHu; eapply env_agree_mono; [ exact Hρ1 | apply above_of ].
      intros y0 Hy Hf; apply Hy; pose proof (prefix_upto_fresh _ _ _ _ Hp Hf) as Hf'; cbn in Hf'; tauto.
    - (* a chain through a definition with a module part of a body *)
      intros * Hp Hc Hk IHk Hu IHu ρ' Hρ.
      destruct (IHk (kpad (List.length Δ) ρ') (fun x => ~ gmod_fresh x Φ)) as (ρ1' & Hk1 & Hρ1).
      { intros x Hx Hf; apply Hx; pose proof (prefix_upto_fresh _ _ _ _ Hp Hf) as Hf'; cbn in Hf'; tauto. }
      { eapply env_agree_kpad; [ exact Hρ |]; intros y0 Hy Hf; apply Hy; cbn in Hf |- *; destruct Hf as [_ Hf]; exact Hf. }
      eapply ukind_dm_step; [ eassumption | exact Hc | exact Hk1 |].
      apply IHu; eapply env_agree_mono; [ exact Hρ1 | apply above_of ].
      intros y0 Hy Hf; apply Hy; pose proof (prefix_upto_fresh _ _ _ _ Hp Hf) as Hf'; cbn in Hf'; tauto.
    - (* a name an open declares, read in the open's target *)
      intros * Hi Hk IHk Hs IHs ρ' Hρ.
      destruct (IHk (kpad (List.length Δ) ρ') (fun x => ~ gmod_fresh x Φ)) as (ρ0' & Hk0 & Hρ0).
      { intros x0 Hx Hf; apply Hx; pose proof (item_upto_fresh _ _ _ _ _ _ _ Hi Hf) as Hf'; cbn in Hf'; tauto. }
      { eapply env_agree_kpad; [ exact Hρ |]; intros y0 Hy Hf; apply Hy; cbn in Hf |- *; destruct Hf as [_ Hf]; exact Hf. }
      assert (Hq : env_agree (fun x => ~ modexp_fresh x H) ρ0 ρ0').
      { eapply env_agree_mono; [ exact Hρ0 | apply above_of ].
        intros y0 Hy Hf; apply Hy; pose proof (item_upto_fresh _ _ _ _ _ _ _ Hi Hf) as Hf'; cbn in Hf'; tauto. }
      eapply ukind_item_def; [ eassumption | exact Hk0 | auto ].
    - intros * Hi Hk IHk Hs IHs Hs2 IHs2 ρ' Hρ.
      destruct (IHk (kpad (List.length Δ) ρ') (fun x => ~ gmod_fresh x Φ)) as (ρ0' & Hk0 & Hρ0).
      { intros x0 Hx Hf; apply Hx; pose proof (item_upto_fresh _ _ _ _ _ _ _ Hi Hf) as Hf'; cbn in Hf'; tauto. }
      { eapply env_agree_kpad; [ exact Hρ |]; intros y0 Hy Hf; apply Hy; cbn in Hf |- *; destruct Hf as [_ Hf]; exact Hf. }
      assert (Hq : env_agree (fun x => ~ modexp_fresh x H) ρ0 ρ0').
      { eapply env_agree_mono; [ exact Hρ0 | apply above_of ].
        intros y0 Hy Hf; apply Hy; pose proof (item_upto_fresh _ _ _ _ _ _ _ Hi Hf) as Hf'; cbn in Hf'; tauto. }
      eapply ukind_item_mod; [ eassumption | exact Hk0 | auto | auto ].
    - intros * Hi Hk IHk Hs IHs Hs2 IHs2 ρ' Hρ.
      destruct (IHk (kpad (List.length Δ) ρ') (fun x => ~ gmod_fresh x Φ)) as (ρ0' & Hk0 & Hρ0).
      { intros x0 Hx Hf; apply Hx; pose proof (item_upto_fresh _ _ _ _ _ _ _ Hi Hf) as Hf'; cbn in Hf'; tauto. }
      { eapply env_agree_kpad; [ exact Hρ |]; intros y0 Hy Hf; apply Hy; cbn in Hf |- *; destruct Hf as [_ Hf]; exact Hf. }
      assert (Hq : env_agree (fun x => ~ modexp_fresh x H) ρ0 ρ0').
      { eapply env_agree_mono; [ exact Hρ0 | apply above_of ].
        intros y0 Hy Hf; apply Hy; pose proof (item_upto_fresh _ _ _ _ _ _ _ Hi Hf) as Hf'; cbn in Hf'; tauto. }
      eapply ukind_item_dm; [ eassumption | exact Hk0 | auto | auto ].
    - intros * Hi Hk IHk Hs IHs ρ' Hρ.
      destruct (IHk (kpad (List.length Δ) ρ') (fun x => ~ gmod_fresh x Φ)) as (ρ0' & Hk0 & Hρ0).
      { intros x0 Hx Hf; apply Hx; pose proof (item_upto_fresh _ _ _ _ _ _ _ Hi Hf) as Hf'; cbn in Hf'; tauto. }
      { eapply env_agree_kpad; [ exact Hρ |]; intros y0 Hy Hf; apply Hy; cbn in Hf |- *; destruct Hf as [_ Hf]; exact Hf. }
      assert (Hq : env_agree (fun x => ~ modexp_fresh x H) ρ0 ρ0').
      { eapply env_agree_mono; [ exact Hρ0 | apply above_of ].
        intros y0 Hy Hf; apply Hy; pose proof (item_upto_fresh _ _ _ _ _ _ _ Hi Hf) as Hf'; cbn in Hf'; tauto. }
      eapply ukind_item_self; [ eassumption | exact Hk0 | auto ].
    - intros * Hs IH ρ' Hρ; constructor; apply IH.
      eapply env_agree_kpad; [ exact Hρ |]; intros y0 Hy Hf; apply Hy; cbn in Hf |- *; destruct Hf as [_ Hf]; exact Hf.
    (* module expressions *)
    - intros * Hd _ ρ' _; constructor; exact Hd.
    - intros * Hd IH ρ' Hρ; constructor; apply IH; eapply env_agree_mod; [ exact Hρ | cbn; intros Hne; apply Hne; reflexivity ].
    - intros * Hu IH ρ' Hρ; constructor; apply IH; eapply env_agree_mono; [ exact Hρ | intros x Hx Hf; apply Hx; exact Hf ].
    - intros * Hs IH Hc ρ' Hρ; constructor; [ apply IH; eapply env_agree_mono; [ exact Hρ | intros x Hx Hf; apply Hx; exact Hf ] | exact Hc ].
    - intros * Hs IH ρ' Hρ; apply skind_mem_dm; apply IH; eapply env_agree_mono; [ exact Hρ | intros x Hx Hf; apply Hx; exact Hf ].
    - intros * Hs IH ρ' Hρ; constructor; apply IH; eapply env_agree_mono; [ exact Hρ | intros x Hx Hf; apply Hx; cbn in Hf; tauto ].
    (* bodies *)
    - intros * HP Hρ; exists ρ'; split; [ constructor |].
      eapply env_agree_mono; [ exact Hρ | intros ? ?; apply above_zero; assumption ].
    - intros * Hk IH ρ' P HP Hρ.
      destruct (IH ρ' P) as (ρ1' & Hk1 & Hρ1); [ intros x Hx; apply HP; cbn; tauto | exact Hρ |].
      exists (kbentry ρ1' E :: ρ1'); split; [ constructor; exact Hk1 |].
      cbn [gm_binders]; apply env_agree_above_cons; [ exact Hρ1 |].
      destruct E as [? ? ? ? | pm U | ? ? ? ? ? | pv A M U | ? ? ?]; cbn [kbentry]; try (repeat constructor; fail).
      + destruct U as [Δu Du]; cbn [dm_clo]; constructor; constructor.
        eapply env_agree_mono; [ exact Hρ1 | apply above_of ].
        intros y0 Hy; apply HP; intros Hf; apply Hy; cbn [gmod_fresh gentry_fresh] in Hf; destruct Hf as [_ Hf]; exact Hf.
      + (* a definition with a module part: a placeholder and its unit's
           closure *)
        destruct U as [Δu Du]; cbn [dm_clo]; constructor; [ constructor | constructor ].
        eapply env_agree_mono; [ exact Hρ1 | apply above_of ].
        intros y0 Hy; apply HP; intros Hf; apply Hy; cbn [gmod_fresh gentry_fresh] in Hf; tauto.
    - intros * Hk IH Hg IHg ρ' P HP Hρ.
      destruct (IH ρ' P) as (ρ1' & Hk1 & Hρ1); [ intros x Hx; apply HP; cbn; tauto | exact Hρ |].
      assert (HH : forall x, ~ modexp_fresh x H -> above (gm_binders Φ) P x).
      { apply above_of; intros y0 Hy; apply HP; intros Hf; apply Hy; cbn in Hf; tauto. }
      assert (HHa : env_agree (fun x => ~ modexp_fresh x H) ρ1 ρ1')
        by (eapply env_agree_mono; [ exact Hρ1 | exact HH ]).
      exists (kgens_env ρ1' 0 gs); split; [ econstructor; [ exact Hk1 | auto ] |].
      cbn [gm_binders]; rewrite <- (kgens_length _ _ _ _ _ _ Hg).
      eapply env_agree_mono; [| intros z Hz; apply above_above_inv; exact Hz ].
      pose proof (kgens_env_sim _ _ _ _ Hg _ HH gs (fun g Hin => Hin) 0 ρ1 ρ1'
                    (env_agree_mono _ _ _ _ Hρ1 (fun z Hz => above_zero _ _ Hz))) as Hs.
      rewrite Nat.add_0_r in Hs; exact Hs.
    (* bodies read through their opens *)
    - intros; constructor.
    - intros * Hb IH ρ' P HP Hρ; apply kbody_ext; eapply IH; [| exact Hρ ]; intros z Hz; apply HP; intros Hf; apply Hz; cbn in Hf; tauto.
    - intros * Hb IH Hk IHk Hg IHg ρ' P HP Hρ.
      assert (HPΦ : forall z, ~ gmod_fresh z Φ -> P z) by (intros z Hz; apply HP; intros Hf; apply Hz; cbn in Hf; tauto).
      assert (Hbn : gm_binders Φx = gm_binders Φ)
        by (clear - Hb; induction Hb; cbn; auto; rewrite gens_append_binders; erewrite kgens_length by eassumption; lia).
      destruct (IHk ρ' P) as (ρ1' & Hk1 & Hρ1); [| exact Hρ |].
      { intros z Hz; apply HPΦ; intros Hf; apply Hz; exact (proj1 (kbody_fresh _ _ _ _ _ Hb _ Hf)). }
      eapply kbody_open; [ exact (IH _ _ HPΦ Hρ) | exact Hk1 |].
      apply IHg; eapply env_agree_mono; [ exact Hρ1 | apply above_of ].
      intros y0 Hy; apply HP; intros Hf; apply Hy; cbn in Hf; rewrite Hbn; tauto.
    (* generated entries *)
    - intros; constructor.
    - intros * Hg IH ρ' Hρ; constructor; auto.
    - intros * Hs IHs Hg IH ρ' Hρ; constructor; auto.
    - intros * Hs IHs Hg IH ρ' Hρ; constructor; auto.
    - intros * Hs IHs Hg IH ρ' Hρ; constructor; auto.
  Qed.
End KindSim.

(** ** Recursive Results

    The entries of a list of recursive results that are read: those the
    branch [B] reads, at [Some B]; all of them, at [None]. *)
Definition ihs_read (oB : option exp) : nat -> Prop :=
  match oB with Some B => fun x => ~ exp_fresh x B | None => fun _ => True end.

(** The group's table of leaf paths is coherent where results may be
    skipped: the skipped results of an argument are as many as its leaf
    paths. *)
Definition ihs_coh (p : qname) (oB : option exp) : Prop :=
  match oB with Some _ => forall D, ind_lookup Θ Ξ p = Some D -> leaves_coherent D | None => True end.

(** Lists related at every entry are related. *)
Lemma dsim_list_at_true : forall l l', dsim_list_at (fun _ => True) l l' -> dsim_list l l'.
Proof. induction 1; constructor; auto. Qed.

(** A block of entries none of which is read, before related ones. *)
Lemma dsim_list_at_skip : forall P l1 l1' l2 l2', List.length l1 = List.length l1' ->
    (forall i, i < List.length l1 -> ~ P (List.length l2 + i)) -> dsim_list_at P l2 l2' ->
    dsim_list_at P (l1 ++ l2) (l1' ++ l2').
Proof.
  induction l1 as [| a l1 IH]; intros [| a' l1'] * Hl HP H2; cbn in Hl; try discriminate; cbn; [ exact H2 |].
  injection Hl as Hl; constructor; [| apply IH; [ exact Hl | intros; apply HP; cbn; lia | exact H2 ] ].
  intros Hp; exfalso; apply (HP (List.length l1)); [ cbn; lia |].
  rewrite List.length_app in Hp; replace (List.length l2 + List.length l1) with (List.length l1 + List.length l2) by lia; exact Hp.
Qed.

(** The recursive results of an argument are of a filed group. *)
Lemma eval_ih_lookup : forall ρ p ups Bks t v rs, ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
    exists D, ind_lookup Θ Ξ p = Some D.
Proof. inversion 1; subst; eauto. Qed.

(** The recursive results of a function shape, one closure per leaf path,
    over related parts. *)
Lemma dsim_list_map_ihfn : forall ρ ρ' Bks p ups ups' t f f' n,
    blocks_agree Bks ρ ρ' -> dsim_list ups ups' -> dsim f f' ->
    dsim_list (List.map (fun i => d_ihfn ρ Bks p ups t i f) (List.seq 0 n))
              (List.map (fun i => d_ihfn ρ' Bks p ups' t i f') (List.seq 0 n)).
Proof.
  intros * HB Hu Hf; generalize 0; induction n as [| n IH]; intros k; cbn; constructor; [| apply IH ].
  constructor; [ exact HB | exact Hu | exact Hf ].
Qed.

(** The types of the recursive results of a function shape, one family per
    leaf path, over related parts. *)
Lemma dsim_list_map_ihfam : forall b b' ρm ρm' As p ups ups' ρ ρ' t f f' n,
    dsim b b' -> ends_agree p As ρm ρm' t -> dsim_list ups ups' ->
    env_agree (fun x => ~ pt_fresh (S x) t) ρ ρ' -> dsim f f' ->
    dsim_list (List.map (fun i => Πᵈ b (nil ↦ d_ihfam ρm As p ups ρ t i f) fam_cod) (List.seq 0 n))
              (List.map (fun i => Πᵈ b' (nil ↦ d_ihfam ρm' As p ups' ρ' t i f') fam_cod) (List.seq 0 n)).
Proof.
  intros * Hb HA Hu Hρ Hf; generalize 0; induction n as [| n IH]; intros k; cbn; constructor; [| apply IH ].
  apply dsim_fam_pi; [ exact Hb | constructor; [ exact HA | exact Hu | exact Hρ | exact Hf ] ].
Qed.

#[local]
Hint Resolve dsim_fields_combine : mctt.

Section Eval.

  Theorem feval_sim :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> forall ρ', env_agree (fun x => ~ exp_fresh x M) ρ ρ' ->
       exists m', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ m' /\ dsim m m') /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> forall m' n', dsim m m' -> dsim n n' ->
       exists r', $ᶠ| m' & n' | Θ ⍮ Ξ ↘ r' /\ dsim r r') /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> forall ρ', env_agree (fun x => ~ Forall (exp_fresh x) Ms) ρ ρ' ->
       exists ms', ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ms' /\ dsim_list ms ms') /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r -> forall m' args', dsim m m' -> dsim_list args args' ->
       exists r', $*ᶠ| m' & args' | Θ ⍮ Ξ ↘ r' /\ dsim r r') /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall ρ', env_agree (fun x => ~ modexp_fresh x H) ρ ρ' ->
       exists h', ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ' ↘ h' /\ dmsim h h') /\
    (forall Δ D ρ h, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall ρ', env_agree (fun x => ~ gunit_fresh x (gu_mk Δ D)) ρ ρ' ->
       exists h', ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ' ↘ h' /\ dmsim h h') /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> forall h' n', dmsim h h' -> dsim n n' ->
       exists r', $ᵐᶠ| h' & n' | Θ ⍮ Ξ ↘ r' /\ dmsim r r') /\
    (forall h ns r, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r -> forall h' ns', dmsim h h' -> dsim_list ns ns' ->
       exists r', $ᵐ*ᶠ| h' & ns' | Θ ⍮ Ξ ↘ r' /\ dmsim r r') /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> forall h', dmsim h h' -> exists r', h' ·ₜᶠ x Θ ⍮ Ξ ↘ r' /\ dsim r r') /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> forall h', dmsim h h' -> exists r', h' ·ₘᶠ y Θ ⍮ Ξ ↘ r' /\ dmsim r r') /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> forall h', dmsim h h' -> exists r', h' ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r' /\ dsim r r') /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> forall h', dmsim h h' -> exists r', h' ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r' /\ dmsim r r') /\
    (forall ρ Φ ρ1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 -> forall ρ' (P : nat -> Prop),
       (forall x, ~ gmod_fresh x Φ -> P x) -> env_agree P ρ ρ' ->
       exists ρ1', ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ρ1' /\ env_agree (above (gm_binders Φ) P) ρ1 ρ1') /\
    (forall ρ p ups Bks j m r, ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> forall ρ' ups' m',
       blocks_agree Bks ρ ρ' -> dsim_list ups ups' -> dsim m m' ->
       exists r', ⟦elimᶠ m' at j of p ups' Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ dsim r r') /\
    (forall ρ p ups Bks gs vs ihs, ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs -> forall ρ' ups' vs' oB,
       blocks_agree Bks ρ ρ' -> dsim_list ups ups' -> dsim_list vs vs' -> ihs_coh p oB ->
       exists ihs', ⟦ihsᶠ vs' of gs under p ups' Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ihs' /\
       dsim_list_at (ihs_read oB) ihs ihs') /\
    (forall ρ p ups Bks t m r, ⟦ih m of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> forall ρ' ups' m',
       blocks_agree Bks ρ ρ' -> dsim_list ups ups' -> dsim m m' ->
       exists r', ⟦ihᶠ m' of t under p ups' Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ dsim_list r r') /\
    (forall p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r -> forall ups', dsim_list ups ups' ->
       exists pre', ⟦mrefᶠ j of p ups' ⟧ᶠ Θ ⍮ Ξ ↘ (fst r, pre') /\ dsim_list (snd r) pre') /\
    (forall p ups ρ t a, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> forall ups' ρ',
       dsim_list ups ups' -> env_agree (fun x => ~ pt_fresh x t) ρ ρ' ->
       exists a', ⟦shtyᶠ t of p ups' ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ a' /\ dsim a a') /\
    (forall p ups ρm As ρ t m a, ⟦ihty m of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> forall ups' ρm' ρ' m',
       dsim_list ups ups' -> ends_agree p As ρm ρm' t -> env_agree (fun x => ~ pt_fresh x t) ρ ρ' -> dsim m m' ->
       exists a', ⟦ihtyᶠ m' of t at p ups' under ρm' As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ a' /\ dsim_list a a') /\
    (forall f m r, eval_proj Θ Ξ f m r -> forall m', dsim m m' ->
       exists r', feval_proj Θ Ξ f m' r' /\ dsim r r') /\
    (forall ns m fl pre rs, eval_nflds Θ Ξ ns m fl pre rs -> forall ns' m' pre',
       dsim_list ns ns' -> dsim_ne m m' -> dsim_list pre pre' ->
       exists rs', feval_nflds Θ Ξ ns' m' fl pre' rs' /\ dsim_list rs rs') /\
    (forall fl v ws, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws -> forall v', dsim v v' ->
       exists ws', ⟦projsᶠ fl of v' ⟧ᶠ Θ ⍮ Ξ ↘ ws' /\ dsim_list ws ws') /\
    (forall p ups ρm As ρ gs vs rs, ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs -> forall ups' ρm' ρ' vs',
       dsim_list ups ups' -> (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_agree p As ρm ρm' t) ->
       env_agree (fun _ => True) ρ ρ' -> dsim_list vs vs' ->
       exists rs', ⟦ihtysᶠ vs' of gs at p ups' under ρm' As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ rs' /\ dsim_list rs rs').
  Proof.
    apply (eval_mut_ind Θ Ξ
      (fun M ρ m _ => forall ρ', env_agree (fun x => ~ exp_fresh x M) ρ ρ' ->
         exists m', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ m' /\ dsim m m')
      (fun m n r _ => forall m' n', dsim m m' -> dsim n n' -> exists r', $ᶠ| m' & n' | Θ ⍮ Ξ ↘ r' /\ dsim r r')
      (fun Ms ρ ms _ => forall ρ', env_agree (fun x => ~ Forall (exp_fresh x) Ms) ρ ρ' ->
         exists ms', ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ms' /\ dsim_list ms ms')
      (fun m args r _ => forall m' args', dsim m m' -> dsim_list args args' ->
         exists r', $*ᶠ| m' & args' | Θ ⍮ Ξ ↘ r' /\ dsim r r')
      (fun H ρ h _ => forall ρ', env_agree (fun x => ~ modexp_fresh x H) ρ ρ' ->
         exists h', ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ' ↘ h' /\ dmsim h h')
      (fun Δ D ρ h _ => forall ρ', env_agree (fun x => ~ gunit_fresh x (gu_mk Δ D)) ρ ρ' ->
         exists h', ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ' ↘ h' /\ dmsim h h')
      (fun h n r _ => forall h' n', dmsim h h' -> dsim n n' -> exists r', $ᵐᶠ| h' & n' | Θ ⍮ Ξ ↘ r' /\ dmsim r r')
      (fun h ns r _ => forall h' ns', dmsim h h' -> dsim_list ns ns' -> exists r', $ᵐ*ᶠ| h' & ns' | Θ ⍮ Ξ ↘ r' /\ dmsim r r')
      (fun h x r _ => forall h', dmsim h h' -> exists r', h' ·ₜᶠ x Θ ⍮ Ξ ↘ r' /\ dsim r r')
      (fun h y r _ => forall h', dmsim h h' -> exists r', h' ·ₘᶠ y Θ ⍮ Ξ ↘ r' /\ dmsim r r')
      (fun h ch r _ => forall h', dmsim h h' -> exists r', h' ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r' /\ dsim r r')
      (fun h ch r _ => forall h', dmsim h h' -> exists r', h' ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r' /\ dmsim r r')
      (fun ρ Φ ρ1 _ => forall ρ' (P : nat -> Prop),
         (forall x, ~ gmod_fresh x Φ -> P x) -> env_agree P ρ ρ' ->
         exists ρ1', ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ρ1' /\ env_agree (above (gm_binders Φ) P) ρ1 ρ1')
      (fun ρ p ups Bks j m r _ => forall ρ' ups' m',
         blocks_agree Bks ρ ρ' -> dsim_list ups ups' -> dsim m m' ->
         exists r', ⟦elimᶠ m' at j of p ups' Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ dsim r r')
      (fun ρ p ups Bks gs vs ihs _ => forall ρ' ups' vs' oB,
         blocks_agree Bks ρ ρ' -> dsim_list ups ups' -> dsim_list vs vs' -> ihs_coh p oB ->
         exists ihs', ⟦ihsᶠ vs' of gs under p ups' Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ihs' /\
         dsim_list_at (ihs_read oB) ihs ihs')
      (fun ρ p ups Bks t m r _ => forall ρ' ups' m',
         blocks_agree Bks ρ ρ' -> dsim_list ups ups' -> dsim m m' ->
         exists r', ⟦ihᶠ m' of t under p ups' Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ dsim_list r r')
      (fun p ups j r _ => forall ups', dsim_list ups ups' ->
         exists pre', ⟦mrefᶠ j of p ups' ⟧ᶠ Θ ⍮ Ξ ↘ (fst r, pre') /\ dsim_list (snd r) pre')
      (fun p ups ρ t a _ => forall ups' ρ',
         dsim_list ups ups' -> env_agree (fun x => ~ pt_fresh x t) ρ ρ' ->
         exists a', ⟦shtyᶠ t of p ups' ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ a' /\ dsim a a')
      (fun p ups ρm As ρ t m a _ => forall ups' ρm' ρ' m',
         dsim_list ups ups' -> ends_agree p As ρm ρm' t -> env_agree (fun x => ~ pt_fresh x t) ρ ρ' -> dsim m m' ->
         exists a', ⟦ihtyᶠ m' of t at p ups' under ρm' As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ a' /\ dsim_list a a')
      (fun f m r _ => forall m', dsim m m' -> exists r', feval_proj Θ Ξ f m' r' /\ dsim r r')
      (fun ns m fl pre rs _ => forall ns' m' pre',
         dsim_list ns ns' -> dsim_ne m m' -> dsim_list pre pre' ->
         exists rs', feval_nflds Θ Ξ ns' m' fl pre' rs' /\ dsim_list rs rs')
      (fun fl v ws _ => forall v', dsim v v' -> exists ws', ⟦projsᶠ fl of v' ⟧ᶠ Θ ⍮ Ξ ↘ ws' /\ dsim_list ws ws')
      (fun p ups ρm As ρ gs vs rs _ => forall ups' ρm' ρ' vs',
         dsim_list ups ups' -> (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_agree p As ρm ρm' t) ->
         env_agree (fun _ => True) ρ ρ' -> dsim_list vs vs' ->
         exists rs', ⟦ihtysᶠ vs' of gs at p ups' under ρm' As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ rs' /\ dsim_list rs rs'));
      intros; cbn [fst snd ptyp_ps ptyp_mem] in *.
    (** Records: a tuple's fields, a field of a value, and the projections
        of a neutral, each from related parts. *)
    all: try solve [ match goal with
      | IH : forall ρ0, env_agree (fun x => ~ Forall (exp_fresh x) (List.map snd ?fs)) ?ρ ρ0 -> exists _, _ /\ _,
        Hρ : env_agree (fun x => ~ exp_fresh x (a_tuple ?T ?fs)) ?ρ ?ρ' |- _ =>
          let vs' := fresh "vs'" in
          destruct (IH ρ') as (vs' & ? & ?);
            [ eapply env_agree_mono; [ exact Hρ |];
              let x := fresh "x" in let Hx := fresh "Hx" in let Hf := fresh "Hf" in
              intros x Hx Hf; apply Hx; cbn [exp_fresh] in Hf; destruct Hf as [_ Hf];
              apply (proj2 (List.Forall_map _ _ _)), (proj1 (all_list_Forall _ _)), Hf
            |];
          eexists; split; [ constructor; eassumption | constructor; apply dsim_fields_combine; assumption ]
      | IHM : forall ρ0, env_agree (fun x => ~ exp_fresh x ?M) ?ρ ρ0 -> exists _, _ /\ _,
        IHp : forall m0, dsim ?m m0 -> exists _, feval_proj _ _ ?f m0 _ /\ _,
        Hρ : env_agree (fun x => ~ exp_fresh x (a_proj ?f ?M)) ?ρ ?ρ' |- _ =>
          let m' := fresh "m'" in let r' := fresh "r'" in
          destruct (IHM ρ') as (m' & ? & ?); [ exact Hρ |];
          destruct (IHp m') as (r' & ? & ?); [ assumption |];
          exists r'; split; [ econstructor; eassumption | assumption ]
      | Hl : field_lookup ?vs ?f = Some _, Hs : dsim (d_tuple ?vs) _ |- _ =>
          inversion Hs; subst;
          match goal with Hfs : dsim_fields vs _ |- _ =>
            let r' := fresh "r'" in
            destruct (field_lookup_sim _ _ _ _ Hfs Hl) as (r' & ? & ?);
            exists r'; split; [ constructor; assumption | assumption ] end
      | IH : forall ns0 m0 pre0, dsim_list ?ns ns0 -> dsim_ne ?m m0 -> dsim_list nil pre0 -> exists _, _ /\ _,
        Hk : List.nth_error ?rs ?k = Some _, Hs : dsim (⇑ (d_record _ ?ns) ?m) _ |- _ =>
          inversion Hs; subst;
          match goal with Ha : dsim (d_record _ _) _ |- _ => inversion Ha; subst end;
          match goal with Hns : dsim_list ns ?ns', Hm : dsim_ne m ?m' |- _ =>
            let rs' := fresh "rs'" in let r' := fresh "r'" in
            destruct (IH ns' m' nil Hns Hm ltac:(constructor)) as (rs' & ? & Hrs);
            destruct (dsim_list_nth_error _ _ _ _ Hrs Hk) as (r' & ? & ?);
            exists r'; split; [ econstructor; eassumption | assumption ] end
      | |- exists _, feval_nflds _ _ _ _ nil _ _ /\ _ => eexists; split; constructor
      end ].
    all: repeat first [ sim_inv | sim_fwd ].
    (** The next field of a neutral: its type, at the related parameters
        ([sim_fwd]), then the rest after its projection. *)
    all: try solve [ match goal with
      | IH : forall ns0 m0 pre0, dsim_list ?ns ns0 -> dsim_ne ?m m0 ->
               dsim_list (?pre ++ ⇑ ?a (d_proj ?g ?m) :: nil) pre0 -> exists _, _ /\ _,
        Hns : dsim_list ?ns ?ns', Hm : dsim_ne ?m ?m', Hpre : dsim_list ?pre ?pre',
        HT : ⟦ _ ⟧ᶠ _ ⍮ _ ⍮ env_args nil (?ns' ++ ?pre') ↘ ?a', Ha : dsim ?a ?a' |- _ =>
          let rs' := fresh "rs'" in
          destruct (IH ns' m' (pre' ++ ⇑ a' (d_proj g m') :: nil) Hns Hm) as (rs' & ? & ?);
            [ apply dsim_list_snoc; [ exact Hpre | constructor; [ exact Ha | constructor; exact Hm ] ] |];
          eexists; split; [ econstructor; eassumption | constructor; [ constructor; [ exact Ha | constructor; exact Hm ] | assumption ] ]
      end ].
    all: repeat first [ sim_inv | sim_fwd ].
    all: try solve [ sim_fin ].
    (** The eliminator: its blocks agree where it does; the group it
        eliminates by is read off related values alike. *)
    all: try solve [ match goal with
      | IH : forall ρ0 ups0 m0, blocks_agree ?Bks ?ρ ρ0 -> dsim_list ?ups ups0 -> dsim ?m m0 -> exists _, _ /\ _,
        Hm : dsim ?m ?m', Hu : dsim_list ?ups ?ups', He : elim_grp_of _ ?m = Some _,
        Hρ : env_agree (fun x => ~ exp_fresh x (a_elim _ _ _ ?Bks _)) ?ρ ?ρ' |- _ =>
          let r' := fresh "r'" in
          destruct (IH ρ' ups' m' (agree_elim_blocks _ _ _ _ _ _ _ Hρ) Hu Hm) as (r' & ? & ?);
          exists r'; split;
            [ eapply feval_exp_elim; [ eassumption | eassumption | rewrite (elim_grp_of_sim _ _ _ Hm); exact He | eassumption ]
            | assumption ]
      end ].
    (** On a constructor: the recursive results, then the branch, in the
        environment of the parameters, the arguments and the results. *)
    all: try solve [ match goal with
      | IHi : forall ρ0 ups0 vs0 oB0, blocks_agree ?Bks ?ρ ρ0 -> dsim_list ?ups ups0 -> dsim_list (skipn _ ?vs) vs0 ->
              ihs_coh ?p oB0 -> exists _, _ /\ _,
        IHB : forall ρ0, env_agree (fun x => ~ exp_fresh x ?B) (env_args ?ρ _) ρ0 -> exists _, _ /\ _,
        HBk : blocks_agree ?Bks ?ρ ?ρ', Hu : dsim_list ?ups ?ups',
        Hvs : dsim_list ?vs ?vs', Hb : nth_error ?Bks _ = Some ?bk, e : brs_lookup (eb_brs ?bk) ?c = Some (_, ?B),
        Hl : List.length ?vs = (im_np ?Dq ?Mk + List.length ?gs)%nat,
        Hlk : ind_lookup _ _ ?p = Some ?D, Hco : leaves_coherent ?D,
        Hih : ⟦ihs _ of ?gs under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?ihs |- _ =>
          let ihs' := fresh "ihs'" in let Hihs' := fresh "Hihs'" in let Hsi := fresh "Hsi" in
          let r' := fresh "r'" in let Hcoh := fresh "Hcoh" in
          assert (Hcoh : ihs_coh p (Some B))
            by (let D0 := fresh "D0" in let HD0 := fresh "HD0" in
                intros D0 HD0; rewrite Hlk in HD0; injection HD0 as <-; exact Hco);
          destruct (IHi ρ' ups' (skipn (im_np Dq Mk) vs') (Some B) HBk Hu (dsim_list_skipn _ _ _ Hvs) Hcoh)
            as (ihs' & Hihs' & Hsi); cbn [ihs_read] in Hsi;
          destruct (IHB (env_args ρ' (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs') ++ skipn (im_np Dq Mk) vs' ++ ihs')))
            as (r' & ? & ?);
            [ eapply env_agree_binders_at;
                [ exact (proj2 (HBk _ (nth_error_In _ _ Hb)) _ _ _ (brs_lookup_in _ _ _ _ e))
                | apply dsim_list_at_app; [ apply dsim_list_skipn, dsim_list_firstn, Hvs
                                          | apply dsim_list_at_app; [ apply dsim_list_skipn, Hvs | exact Hsi ] ]
                | rewrite (ind_branch_args_length _ _ _ _ _ Hl), (proj2 (eval_ihs_length _ _ _ _ _ _ _ _ Hlk Hco Hih));
                  first [ reflexivity | lia ] ]
            |];
          exists r'; split;
            [ eapply feval_elim_con; try eassumption; try reflexivity; rewrite <- (dsim_list_length _ _ Hvs); exact Hl
            | assumption ]
      end ].
    (** On a neutral: the motive's instance, and a neutral eliminator over
        environments that agree where the blocks read. *)
    all: try solve [ match goal with
      | IH : forall ρ0, env_agree (fun x => ~ exp_fresh x (eb_motive ?bk)) (env_args ?ρ _) ρ0 -> exists _, _ /\ _,
        HBk : blocks_agree ?Bks ?ρ ?ρ', Hb : nth_error ?Bks _ = Some ?bk, Hn : eb_nm ?bk = S (im_nn ?Mk),
        Has : dsim_list ?as' ?as'', Hm : dsim_ne ?m ?m', Hu : dsim_list ?ups ?ups',
        Hl : List.length ?as' = im_np ?Dq ?Mk
        |- exists _, ⟦elimᶠ ⇑ (d_ind ?pc ?k ?as'') ?m' at _ of _ _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
          let a' := fresh "a'" in
          destruct (IH (env_args ρ' (skipn (ind_nu Dq) as'' ++ ⇑ (d_ind pc k as'') m' :: nil))) as (a' & ? & ?);
            [ eapply env_agree_binders;
                [ exact (proj1 (HBk _ (nth_error_In _ _ Hb)))
                | apply dsim_list_app; [ apply dsim_list_skipn, Has | repeat constructor; assumption ]
                | rewrite (ind_motive_args_length _ _ _ _ Hl), Hn; reflexivity ]
            |];
          eexists; split;
            [ eapply feval_elim_neut; try eassumption; rewrite <- (dsim_list_length _ _ Has); exact Hl
            | constructor; [ assumption | apply dsim_ne_elim; [ exact HBk | exact Hu | exact Has | exact Hm ] ] ]
      end ].
    (** The recursive results: those of an argument are computed when the
        branch reads one of them, and skipped when it reads none, as the
        fast rule decides; skipped ones are as many as the argument's leaf
        paths, the group's table being coherent. *)
    all: try solve [ eexists; split; [ constructor | constructor ] ].
    all: try solve [ match goal with
      | IH : forall ρ0 ups0 vs0 oB0, blocks_agree ?Bks ?ρ ρ0 -> dsim_list ?ups ups0 -> dsim_list ?vs vs0 -> ihs_coh ?p oB0 -> exists _, _ /\ _,
        HB : blocks_agree ?Bks ?ρ ?ρ', Hu : dsim_list ?ups ?ups', Hvs : dsim_list ?vs ?vs', Hc : ihs_coh ?p ?oB
        |- exists _, feval_ihs _ _ _ _ _ _ ?oB (ca_arg _ :: _) _ _ /\ _ =>
          let ihs' := fresh "ihs'" in
          destruct (IH ρ' ups' vs' oB HB Hu Hvs Hc) as (ihs' & ? & ?);
          exists ihs'; split; [ constructor; eassumption | assumption ]
      | IHi : forall ρ0 ups0 m0, blocks_agree ?Bks ?ρ ρ0 -> dsim_list ?ups ups0 -> dsim ?v m0 -> exists _, feval_ih _ _ _ _ _ _ _ _ _ /\ _,
        IHs : forall ρ0 ups0 vs0 oB0, blocks_agree ?Bks ?ρ ρ0 -> dsim_list ?ups ups0 -> dsim_list ?vs vs0 -> ihs_coh ?p oB0 -> exists _, _ /\ _,
        Hi : eval_ih _ _ ?ρ ?p ?ups ?Bks ?t ?v ?ihs1, Hs : eval_ihs _ _ ?ρ ?p ?ups ?Bks ?gs ?vs ?ihs,
        HB : blocks_agree ?Bks ?ρ ?ρ', Hu : dsim_list ?ups ?ups', Hv : dsim ?v ?v', Hvs : dsim_list ?vs ?vs', Hc : ihs_coh ?p ?oB
        |- exists _, feval_ihs _ _ _ _ _ _ ?oB (ca_rec ?t :: ?gs) _ _ /\ _ =>
          let D := fresh "D" in let HD := fresh "HD" in let ihs' := fresh "ihs'" in let Hsi := fresh "Hsi" in
          let Hsk := fresh "Hsk" in
          destruct (eval_ih_lookup _ _ _ _ _ _ _ Hi) as (D & HD);
          destruct (IHs ρ' ups' vs' oB HB Hu Hvs Hc) as (ihs' & ? & Hsi);
          destruct (ihs_skipb oB (cargs_nrec D gs) (List.length (shape_leaves (rv_leaves D) 0 t))) eqn:Hsk;
          [ let B := fresh "B" in let HBf := fresh "HBf" in let Hco := fresh "Hco" in let Hli := fresh "Hli" in
            destruct (ihs_skipb_sound _ _ _ Hsk) as (B & -> & HBf);
            pose proof (Hc D HD) as Hco;
            pose proof (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Hi _ HD Hco) as Hli;
            exists (List.repeat 𝕌ω@0 (List.length (shape_leaves (rv_leaves D) 0 t)) ++ ihs'); split;
            [ eapply feval_ihs_skip; eassumption
            | apply dsim_list_at_skip;
              [ rewrite List.repeat_length; exact Hli
              | let i0 := fresh "i0" in let Hi0 := fresh "Hi0" in let Hn := fresh "Hn" in
                intros i0 Hi0; cbn [ihs_read]; rewrite (proj2 (eval_ihs_length _ _ _ _ _ _ _ _ HD Hco Hs));
                intros Hn; apply Hn, HBf; rewrite Hli in Hi0; exact Hi0
              | exact Hsi ] ]
          | let ih' := fresh "ih'" in
            destruct (IHi ρ' ups' v' HB Hu Hv) as (ih' & ? & ?);
            exists (ih' ++ ihs'); split; [ eapply feval_ihs_rec; eassumption | apply dsim_list_at_app; assumption ] ]
      end ].
    (** Function shapes.  A recursive result of a function shape and the
        families of their types, applied; the recursive results at a leaf,
        at a member with a block or at a record view; the types, a [Π] over
        each family; the projections along a record view's path, and the
        types of its fields' recursive results. *)
    all: try solve [ match goal with
      | IH : forall ρ0 ups0 m0, blocks_agree ?Bks ?ρ ρ0 -> dsim_list ?ups ups0 -> dsim ?fn m0 -> exists _, feval_ih _ _ _ _ _ _ _ _ _ /\ _,
        HB : blocks_agree ?Bks ?ρ ?ρ', Hu : dsim_list ?ups ?ups', Hf : dsim ?fn ?x, Ha : $ᶠ| _ & _ | _ ⍮ _ ↘ ?x,
        Hi : nth_error ?rs ?i = Some _ |- exists _, $ᶠ| d_ihfn _ _ _ _ _ _ _ & _ | _ ⍮ _ ↘ _ /\ _ =>
          let rs' := fresh "rs'" in let Hrs := fresh "Hrs" in let r' := fresh "r'" in
          destruct (IH _ _ _ HB Hu Hf) as (rs' & ? & Hrs);
          destruct (dsim_list_nth_error _ _ _ _ Hrs Hi) as (r' & ? & ?);
          exists r'; split; [ econstructor; eassumption | assumption ]
      | IH : forall ups0 ρm0 ρ0 m0, dsim_list ?ups ups0 -> ends_agree _ _ ?ρm ρm0 _ -> env_agree _ (?ρ ↦ ?n) ρ0 -> dsim ?fn m0 ->
             exists _, _ /\ _,
        Hu : dsim_list ?ups ?ups', HA : ends_agree _ _ ?ρm ?ρm' _, Hρ : env_agree (fun x => ~ pt_fresh (S x) ?t) ?ρ ?ρ',
        Hn : dsim ?n ?n', Hf : dsim ?fn ?x, Ha : $ᶠ| _ & _ | _ ⍮ _ ↘ ?x, Hi : nth_error ?ys ?i = Some _
        |- exists _, $ᶠ| d_ihfam _ _ _ _ _ _ _ _ & _ | _ ⍮ _ ↘ _ /\ _ =>
          let ys' := fresh "ys'" in let Hys := fresh "Hys" in let a' := fresh "a'" in
          destruct (IH ups' ρm' (ρ' ↦ n') x Hu HA) as (ys' & ? & Hys);
            [ unfold extend_env; eapply env_agree_cons; [ exact Hρ | constructor; exact Hn | intros y Hy; exact Hy ] | exact Hf |];
          destruct (dsim_list_nth_error _ _ _ _ Hys Hi) as (a' & ? & ?);
          exists a'; split; [ econstructor; eassumption | assumption ]
      | IH : forall ρ0 ups0 m0, blocks_agree ?Bks ?ρ ρ0 -> dsim_list ?ups ups0 -> dsim ?v m0 -> exists _, feval_elim _ _ _ _ _ _ _ _ _ /\ _,
        HB : blocks_agree ?Bks ?ρ ?ρ', Hu : dsim_list ?ups ?ups', Hv : dsim ?v ?v'
        |- exists _, feval_ih _ _ _ _ _ _ (pt_self _ _) _ _ /\ dsim_list (_ :: nil) _ =>
          let r' := fresh "r'" in
          destruct (IH ρ' ups' v' HB Hu Hv) as (r' & ? & ?); exists (r' :: nil); split;
            [ econstructor; eassumption | repeat constructor; assumption ]
      | IHp : forall v0, dsim ?v v0 -> exists _, feval_projs _ _ _ _ _ /\ _,
        IHs : forall ρ0 ups0 vs0 oB0, blocks_agree ?Bks ?ρ ρ0 -> dsim_list ?ups ups0 -> dsim_list ?ws vs0 -> ihs_coh _ oB0 ->
              exists _, _ /\ _,
        HB : blocks_agree ?Bks ?ρ ?ρ', Hu : dsim_list ?ups ?ups', Hv : dsim ?v ?v'
        |- exists _, feval_ih _ _ _ _ _ _ _ _ _ /\ _ =>
          let ws' := fresh "ws'" in let Hws := fresh "Hws" in let rs' := fresh "rs'" in let Hrs := fresh "Hrs" in
          destruct (IHp v' Hv) as (ws' & ? & Hws); destruct (IHs ρ' ups' ws' None HB Hu Hws I) as (rs' & ? & Hrs);
          exists rs'; split; [ econstructor; eassumption | apply dsim_list_at_true; exact Hrs ]
      | HB : blocks_agree ?Bks ?ρ ?ρ', Hu : dsim_list ?ups ?ups', Hv : dsim ?v ?v', e : ind_lookup _ _ ?p = Some ?D
        |- exists _, feval_ih _ _ _ ?p _ ?Bks (pt_pi _ _) _ _ /\ _ =>
          eexists; split; [ econstructor; exact e | apply dsim_list_map_ihfn; assumption ]
      | IHf : forall m0, dsim ?v m0 -> exists _, feval_proj _ _ _ _ _ /\ _,
        IHr : forall v0, dsim ?v v0 -> exists _, feval_projs _ _ _ _ _ /\ _, Hv : dsim ?v ?v'
        |- exists _, feval_projs _ _ _ _ _ /\ _ =>
          let w' := fresh "w'" in let ws' := fresh "ws'" in
          destruct (IHf v' Hv) as (w' & ? & ?); destruct (IHr v' Hv) as (ws' & ? & ?);
          exists (w' :: ws'); split; [ econstructor; eassumption | constructor; assumption ]
      | |- exists _, feval_projs _ _ nil _ _ /\ _ => exists nil; split; constructor
      | |- exists _, feval_ihtys _ _ _ _ _ _ _ nil nil _ /\ _ => exists nil; split; constructor
      | IH : forall ups0 ρm0 ρ0 vs0, dsim_list ?ups ups0 -> _ -> env_agree _ (?ρ ↦ ?v) ρ0 -> dsim_list ?vs vs0 -> exists _, _ /\ _,
        Hu : dsim_list ?ups ?ups', HA : forall gs1 t gs2, _ -> ends_agree _ _ _ ?ρm' _,
        Hρ : env_agree (fun _ => True) ?ρ ?ρ', Hv : dsim ?v ?v', Hvs : dsim_list ?vs ?vs'
        |- exists _, feval_ihtys _ _ _ _ _ _ _ (ca_arg ?T :: _) _ _ /\ _ =>
          let rs' := fresh "rs'" in
          destruct (IH ups' ρm' (ρ' ↦ v') vs' Hu) as (rs' & ? & ?);
            [ let gs1 := fresh "gs1" in let t := fresh "t" in let gs2 := fresh "gs2" in let E := fresh "E" in
              intros gs1 t gs2 E; apply (HA (ca_arg T :: gs1) t gs2); rewrite E; reflexivity
            | apply env_agree_all_cons; assumption | exact Hvs |];
          exists rs'; split; [ constructor; eassumption | assumption ]
      | IHt : forall ups0 ρm0 ρ0 m0, dsim_list ?ups ups0 -> ends_agree _ _ _ ρm0 ?t -> env_agree _ ?ρ ρ0 -> dsim ?v m0 -> exists _, _ /\ _,
        IH : forall ups0 ρm0 ρ0 vs0, dsim_list ?ups ups0 -> _ -> env_agree _ ?ρ ρ0 -> dsim_list ?vs vs0 -> exists _, _ /\ _,
        Hu : dsim_list ?ups ?ups', HA : forall gs1 t0 gs2, ca_rec ?t :: _ = _ -> ends_agree _ _ _ ?ρm' _,
        Hρ : env_agree (fun _ => True) ?ρ ?ρ', Hv : dsim ?v ?v', Hvs : dsim_list ?vs ?vs'
        |- exists _, feval_ihtys _ _ _ _ _ _ _ (ca_rec _ :: _) _ _ /\ _ =>
          let rs1' := fresh "rs1'" in let rs' := fresh "rs'" in
          destruct (IHt ups' ρm' ρ' v' Hu (HA nil t _ eq_refl)) as (rs1' & ? & ?);
            [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] | exact Hv |];
          destruct (IH ups' ρm' ρ' vs' Hu) as (rs' & ? & ?);
            [ let gs1 := fresh "gs1" in let t0 := fresh "t0" in let gs2 := fresh "gs2" in let E := fresh "E" in
              intros gs1 t0 gs2 E; apply (HA (ca_rec t :: gs1) t0 gs2); rewrite E; reflexivity
            | exact Hρ | exact Hvs |];
          exists (rs1' ++ rs'); split; [ econstructor; eassumption | apply dsim_list_app; assumption ]
      | Hea : ends_agree ?p ?As ?ρm ?ρm' (pt_self ?j ?Ps), Hl : ind_lookup _ _ ?p = Some ?D, Hm : ind_member ?D ?j = Some ?Mj,
        Hr : im_is_rview ?Mj = false, e2 : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?bs,
        IH : forall ρ0, env_agree _ (env_args ?ρm (?bs ++ ?v :: nil)) ρ0 -> exists _, _ /\ _,
        Hbs : dsim_list ?bs ?bs', Hv : dsim ?v ?v', HbsF : ⟦ ?Ps ⟧*ᶠ _ ⍮ _ ⍮ _ ↘ ?bs'
        |- exists _, feval_ihty _ _ _ _ _ _ _ (pt_self _ _) _ _ /\ _ =>
          let Hlb := fresh "Hlb" in let a' := fresh "a'" in
          assert (Hlb : List.length bs = List.length Ps) by (clear - e2; induction e2; cbn; congruence);
          inversion Hea as [? ? ? ? D0 j0 Mj0 Ps0 HD0 HM0 HR0 HA0 | ? ? ? ? D0 j0 Mj0 qr0 Is0 fl0 Ps0 HD0 HM0 Hh0 _ |]; subst;
          rewrite Hl in HD0; injection HD0 as <-; rewrite Hm in HM0; injection HM0 as <-;
          [| exfalso; unfold im_is_rview in Hr; rewrite Hh0 in Hr; discriminate Hr ];
          destruct (IH (env_args ρm' (bs' ++ v' :: nil))) as (a' & ? & ?);
            [ eapply env_agree_binders; [ exact HA0 | apply dsim_list_app; [ exact Hbs | repeat constructor; assumption ] |];
              rewrite List.length_app, Hlb; cbn; lia |];
          exists (a' :: nil); split; [ econstructor; eassumption | repeat constructor; assumption ]
      | Hea : ends_agree ?p ?As ?ρm ?ρm' (pt_self ?j ?Ps), Hl : ind_lookup _ _ ?p = Some ?D, Hm : ind_member ?D ?j = Some ?Mj,
        Hh : im_head ?Mj = mh_record _ _ _, Hc : im_cons ?Mj = (_, ?gs) :: nil, Hpj : eval_projs _ _ _ _ _,
        IHp : forall v0, dsim ?v v0 -> exists _, feval_projs _ _ _ _ _ /\ _,
        IH : forall ups0 ρm0 ρ0 vs0, dsim_list ?ups ups0 -> _ -> env_agree _ (env_args nil ?ups) ρ0 -> _ -> exists _, _ /\ _,
        Hu : dsim_list ?ups ?ups', Hv : dsim ?v ?v'
        |- exists _, feval_ihty _ _ _ _ _ _ _ (pt_self _ _) _ _ /\ _ =>
          let ws' := fresh "ws'" in let Hws := fresh "Hws" in let rs' := fresh "rs'" in
          inversion Hea as [? ? ? ? D0 j0 Mj0 Ps0 HD0 HM0 HR0 HA0 | ? ? ? ? D0 j0 Mj0 qr0 Is0 fl0 Ps0 HD0 HM0 Hh0 HF |]; subst;
          rewrite Hl in HD0; injection HD0 as <-; rewrite Hm in HM0; injection HM0 as <-;
          [ exfalso; unfold im_is_rview in HR0; rewrite Hh in HR0; discriminate HR0 |];
          clear Hh0;
          destruct (IHp v' Hv) as (ws' & ? & Hws);
          destruct (IH ups' ρm' (env_args nil ups') ws' Hu) as (rs' & ? & ?);
            [ let gs1 := fresh "gs1" in let t := fresh "t" in let gs2 := fresh "gs2" in let E := fresh "E" in
              intros gs1 t gs2 E; eapply HF; [ exact Hc | exact E ]
            | apply env_agree_all_args; [ apply env_agree_nil | exact Hu ] | exact Hws |];
          exists rs'; split; [ eapply feval_ihty_rview; eassumption | assumption ]
      | Hea : ends_agree _ _ _ _ (pt_pi _ _), Hu : dsim_list ?ups ?ups', Hρ : env_agree (fun x => ~ pt_fresh x (pt_pi _ _)) _ _,
        Hv : dsim _ ?v', He : ⟦ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ ?b', Hb : dsim _ ?b', e : ind_lookup _ _ _ = Some _
        |- exists _, feval_ihty _ _ _ _ _ _ _ (pt_pi _ _) ?v' _ /\ _ =>
          let Ht := fresh "Ht" in
          inversion Hea as [| | ? ? ? ? ? ? Ht]; subst;
          eexists; split; [ econstructor; [ exact e | exact He ] | apply dsim_list_map_ihfam; [ exact Hb | exact Ht | exact Hu | | exact Hv ] ];
          let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
          intros y Hy; apply Hρ; cbn; intros [_ Hf]; exact (Hy Hf)
      | IH : forall ups0 ρ0, dsim_list ?ups ups0 -> env_agree _ (?ρ ↦ ?n) ρ0 -> exists _, _ /\ _,
        Hu : dsim_list ?ups ?ups', Hρ : env_agree (fun x => ~ pt_fresh (S x) ?t) ?ρ ?ρ', Hn : dsim ?n ?n'
        |- exists _, $ᶠ| d_shfam _ _ _ _ & _ | _ ⍮ _ ↘ _ /\ _ =>
          let a' := fresh "a'" in
          destruct (IH ups' (ρ' ↦ n') Hu) as (a' & ? & ?);
            [ unfold extend_env; eapply env_agree_cons; [ exact Hρ | constructor; exact Hn | intros y Hy; exact Hy ] |];
          exists a'; split; [ econstructor; eassumption | assumption ]
      | Hu : dsim_list ?ups ?ups', Hρ : env_agree (fun x => ~ pt_fresh x (pt_pi _ _)) _ _,
        He : ⟦ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ ?b', Hb : dsim _ ?b' |- exists _, feval_shty _ _ _ _ _ _ _ /\ _ =>
          eexists; split; [ constructor; exact He | apply dsim_fam_pi; [ exact Hb | constructor; [ exact Hu |] ] ];
          let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
          intros y Hy; apply Hρ; cbn; intros [_ Hf]; exact (Hy Hf)
      end ].
    (** A closure given its outermost missing parameter: the environment it
        is extended by agrees where the unit lacking one parameter fewer may
        read. *)
    all: try solve [ match goal with
      | IH : forall ρ0, env_agree (fun x => ~ gunit_fresh x (gu_mk ?Δ ?D)) (?ρ ↦ ?n) ρ0 -> exists _, _ /\ _,
        Hn : dsim ?n ?n', Hρ : env_agree (fun x => ~ gunit_fresh x (gu_mk (?Δ ++ _) ?D)) ?ρ ?ρ' |- _ =>
          let h' := fresh "h'" in let Hh' := fresh "Hh'" in let Hs := fresh "Hs" in
          destruct (IH (ρ' ↦ n')) as (h' & Hh' & Hs);
            [ let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
              intros [| y] Hy; cbn;
                [ constructor; exact Hn | apply Hρ; intros Hf; apply Hy; exact (oufresh_snoc (Some y) _ _ _ Hf) ]
            |];
          exists h'; split; [ econstructor; exact Hh' | exact Hs ]
      end ].
    (** A member or a submodule of a saturated body, in the body read
        through its opens, which the kinds read alike in both environments:
        the environment of the body before it agrees where the body may read,
        and so where the member may. *)
    all: try solve [ match goal with
      | Hk : kbody _ _ ?ρ ?Φ ?Φx, Hp : gm_prefix_upto ?Φx _ = Some (gm_ext ?Φ' _ ?E),
        IHb : forall ρ0 (P : nat -> Prop), (forall x, ~ gmod_fresh x ?Φ' -> P x) -> env_agree P ?ρ ρ0 -> _,
        IH : forall ρ0, env_agree _ ?ρ1 ρ0 -> exists _, _ /\ _,
        Hρ : env_agree (fun x => ~ gunit_fresh x (gu_mk nil (md_body ?sm ?Φ))) ?ρ ?ρ' |- _ =>
          let HΦ := fresh "HΦ" in let Hk' := fresh "Hk'" in let HE := fresh "HE" in
          let ρ1' := fresh "ρ1'" in let Hb' := fresh "Hb'" in let Hab := fresh "Hab" in
          let r' := fresh "r'" in let Hr' := fresh "Hr'" in let Hs := fresh "Hs" in
          assert (HΦ : env_agree (fun x => ~ gmod_fresh x Φ) ρ ρ')
            by (eapply env_agree_mono; [ exact Hρ |];
                let z := fresh "z" in let Hz := fresh "Hz" in let Hf := fresh "Hf" in
                intros z Hz Hf; apply Hz; cbn in Hf; destruct Hf as [_ Hf]; exact Hf);
          pose proof (proj1 (proj2 (proj2 (proj2 (proj2 kind_sim)))) _ _ _ Hk ρ' _ (fun z Hz => Hz) HΦ) as Hk';
          assert (HE : forall z, gmod_fresh z Φ -> gmod_fresh z (gm_ext Φ' _ E))
            by (let z := fresh "z" in let Hf := fresh "Hf" in
                intros z Hf; exact (prefix_upto_fresh _ _ _ _ Hp (proj1 (kbody_fresh _ _ _ _ _ Hk _ Hf))));
          destruct (IHb ρ' (fun z => ~ gmod_fresh z Φ)) as (ρ1' & Hb' & Hab);
            [ let z := fresh "z" in let Hz := fresh "Hz" in let Hf := fresh "Hf" in
              intros z Hz Hf; apply Hz; exact (proj1 (HE _ Hf))
            | exact HΦ |];
          destruct (IH ρ1') as (r' & Hr' & Hs);
            [ eapply env_agree_mono; [ exact Hab | apply above_of ];
              let z := fresh "z" in let Hz := fresh "Hz" in let Hf := fresh "Hf" in
              intros z Hz Hf; apply Hz; pose proof (proj2 (HE _ Hf)) as HEz; first [ exact (entry_tm_fresh _ _ _ _ ltac:(eassumption) HEz)
                                                            | exact (entry_unit_fresh _ _ _ ltac:(eassumption) HEz) ]
            |];
          exists r'; split; [ first [ eapply feval_sel_body | eapply feval_selm_body ]; eassumption | exact Hs ]
      end ].
    (** The environment of a body, entry by entry. *)
    all: try match goal with
      | |- exists ρ1', ⟦ gm_nil ⟧ᵇᶠ _ ⍮ _ ⍮ _ ↘ ρ1' /\ _ =>
          eexists; split; [ constructor |];
          eapply env_agree_mono; [ eassumption | intros ? ?; apply above_zero; assumption ]
      | IH : forall ρ0 (P0 : nat -> Prop), (forall x, ~ gmod_fresh x ?Φ -> P0 x) -> env_agree P0 ?ρ ρ0 -> _,
        HQ : forall x, ~ gmod_fresh x (gm_ext ?Φ _ ?E) -> ?P x, Hρ : env_agree ?P ?ρ ?ρ' |- _ =>
          let HP := fresh "HP" in
          assert (HP : forall x, ~ gmod_fresh x Φ -> P x)
            by (let x := fresh "x" in let Hx := fresh "Hx" in let Hf := fresh "Hf" in
                intros x Hx; apply HQ; intros Hf; apply Hx; cbn in Hf; tauto);
          destruct (IH _ _ HP Hρ) as (ρ1' & ? & ?); clear IH
      end.
    all: try match goal with
      | HQ : forall x, ~ gmod_fresh x (gm_ext ?Φ _ (ge_def _ _ _ (Some ?M))) -> ?P x,
        IH : forall ρ0, env_agree (fun x => ~ exp_fresh x ?M) ?ρ1 ρ0 -> _,
        Hab : env_agree (above (gm_binders ?Φ) ?P) ?ρ1 ?ρ1' |- _ =>
          let Hq := fresh "Hq" in
          assert (Hq : env_agree (fun x => ~ exp_fresh x M) ρ1 ρ1')
            by (eapply env_agree_mono; [ exact Hab | apply above_of ];
                let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
                intros y Hy; apply HQ; intros Hf; apply Hy; cbn in Hf; tauto);
          destruct (IH _ Hq) as (? & ? & ?);
          eexists; split; [ econstructor; eassumption |];
          cbn [gm_binders]; apply env_agree_above_cons; [ exact Hab | constructor; eassumption ]
      | HQ : forall x, ~ gmod_fresh x (gm_ext ?Φ _ (ge_mod _ (gu_mk ?Δy ?Dy))) -> ?P x,
        IH : forall ρ0, env_agree (fun x => ~ gunit_fresh x (gu_mk ?Δy ?Dy)) ?ρ1 ρ0 -> _,
        Hab : env_agree (above (gm_binders ?Φ) ?P) ?ρ1 ?ρ1' |- _ =>
          let Hq := fresh "Hq" in
          assert (Hq : env_agree (fun x => ~ gunit_fresh x (gu_mk Δy Dy)) ρ1 ρ1')
            by (eapply env_agree_mono; [ exact Hab | apply above_of ];
                let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
                intros y Hy; apply HQ; intros Hf; apply Hy; cbn [gmod_fresh gentry_fresh] in Hf; tauto);
          destruct (IH _ Hq) as (? & ? & ?);
          eexists; split; [ econstructor; eassumption |];
          cbn [gm_binders]; apply env_agree_above_cons; [ exact Hab | constructor; eassumption ]
      (** A definition with a module part: its term and its unit, both in
          the environment of the body before it. *)
      | HQ : forall x, ~ gmod_fresh x (gm_ext ?Φ _ (ge_def_mod _ _ ?M (gu_mk ?Δy ?Dy))) -> ?P x,
        IHM : forall ρ0, env_agree (fun x => ~ exp_fresh x ?M) ?ρ1 ρ0 -> _,
        IHU : forall ρ0, env_agree (fun x => ~ gunit_fresh x (gu_mk ?Δy ?Dy)) ?ρ1 ρ0 -> _,
        Hab : env_agree (above (gm_binders ?Φ) ?P) ?ρ1 ?ρ1' |- _ =>
          let Hm := fresh "Hm" in let Hu := fresh "Hu" in
          assert (Hm : env_agree (fun x => ~ exp_fresh x M) ρ1 ρ1')
            by (eapply env_agree_mono; [ exact Hab | apply above_of ];
                let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
                intros y Hy; apply HQ; intros Hf; apply Hy; cbn [gmod_fresh gentry_fresh] in Hf; tauto);
          assert (Hu : env_agree (fun x => ~ gunit_fresh x (gu_mk Δy Dy)) ρ1 ρ1')
            by (eapply env_agree_mono; [ exact Hab | apply above_of ];
                let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
                intros y Hy; apply HQ; intros Hf; apply Hy; cbn [gmod_fresh gentry_fresh] in Hf; tauto);
          destruct (IHM _ Hm) as (? & ? & ?); destruct (IHU _ Hu) as (? & ? & ?);
          eexists; split; [ econstructor; eassumption |];
          cbn [gm_binders]; apply env_agree_above_cons; [ exact Hab | constructor; eassumption ]
      end.
  Qed.
End Eval.

Section Read.

  Lemma feval_exp_sim : forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> forall ρ', env_agree (fun x => ~ exp_fresh x M) ρ ρ' ->
      exists m', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ m' /\ dsim m m'.
  Proof. exact (proj1 feval_sim). Qed.

  Lemma feval_app_sim : forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> forall m' n', dsim m m' -> dsim n n' ->
      exists r', $ᶠ| m' & n' | Θ ⍮ Ξ ↘ r' /\ dsim r r'.
  Proof. exact (proj1 (proj2 feval_sim)). Qed.

  Lemma feval_exps_sim : forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> forall ρ', env_agree (fun x => ~ Forall (exp_fresh x) Ms) ρ ρ' ->
      exists ms', ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ms' /\ dsim_list ms ms'.
  Proof. exact (proj1 (proj2 (proj2 feval_sim))). Qed.

  Lemma feval_modexp_sim : forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall ρ', env_agree (fun x => ~ modexp_fresh x H) ρ ρ' ->
      exists h', ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ' ↘ h' /\ dmsim h h'.
  Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 feval_sim))))). Qed.

  (** A closure, at one or two related arguments. *)
  Lemma feval_clo_sim : forall B (ρ ρ' : env) c c' b,
      env_agree (fun x => ~ exp_fresh (S x) B) ρ ρ' -> dsim c c' -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ↘ b ->
      exists b', ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ (ρ' ↦ c') ↘ b' /\ dsim b b'.
  Proof.
    intros * Hρ Hc Hb; eapply feval_exp_sim; [ exact Hb |].
    intros [| x] Hx; cbn; [ constructor; exact Hc | apply Hρ, Hx ].
  Qed.

  (** A closure that does not read its argument, at any argument. *)
  Lemma feval_clo_unread : forall B (ρ ρ' : env) c c' b,
      env_agree (fun x => ~ exp_fresh (S x) B) ρ ρ' -> exp_fresh 0 B -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ↘ b ->
      exists b', ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ (ρ' ↦ c') ↘ b' /\ dsim b b'.
  Proof.
    intros * Hρ H0 Hb; eapply feval_exp_sim; [ exact Hb |].
    intros [| x] Hx; cbn; [ contradiction | apply Hρ, Hx ].
  Qed.

  Lemma feval_clo2_sim : forall B (ρ ρ' : env) c1 c1' c2 c2' b,
      env_agree (fun x => ~ exp_fresh (S (S x)) B) ρ ρ' -> dsim c1 c1' -> dsim c2 c2' ->
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c1 ↦ c2 ↘ b ->
      exists b', ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ (ρ' ↦ c1' ↦ c2') ↘ b' /\ dsim b b'.
  Proof.
    intros * Hρ Hc1 Hc2 Hb; eapply feval_exp_sim; [ exact Hb |].
    intros [| [| x]] Hx; cbn; [ constructor; exact Hc2 | constructor; exact Hc1 | apply Hρ, Hx ].
  Qed.

  (** The fresh variables of the telescopes of a declaration, from
      environments related everywhere. *)
  Lemma ffresh_tele_sim : forall ρ T s ns, Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ns ->
      forall ρ', env_agree (fun _ => True) ρ ρ' ->
      exists ns', Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ ns' /\ dsim_list ns ns'.
  Proof.
    induction 1; intros ρ' Hρ; [ exists nil; split; constructor |].
    destruct (feval_exp_sim _ _ _ H ρ') as (a' & Ha' & Hsa); [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |].
    destruct (IHfresh_tele (ρ' ↦ ⇑! a' s)) as (ns' & ? & ?);
      [ apply env_agree_all_cons; [ exact Hρ | repeat constructor; assumption ] |].
    exists (⇑! a' s :: ns'); split; constructor; try eassumption; repeat constructor; assumption.
  Qed.

  Lemma feval_ih_sim : forall ρ p ups Bks t m r, ⟦ih m of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> forall ρ' ups' m',
      blocks_agree Bks ρ ρ' -> dsim_list ups ups' -> dsim m m' ->
      exists r', ⟦ihᶠ m' of t under p ups' Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ dsim_list r r'.
  Proof.
    intros * H; destruct feval_sim as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _).
    exact (Hi _ _ _ _ _ _ _ H).
  Qed.

  Lemma feval_mref_sim : forall p ups j r, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r -> forall ups', dsim_list ups ups' ->
      exists pre', ⟦mrefᶠ j of p ups' ⟧ᶠ Θ ⍮ Ξ ↘ (fst r, pre') /\ dsim_list (snd r) pre'.
  Proof.
    intros * H; destruct feval_sim as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & _).
    exact (Hm _ _ _ _ H).
  Qed.

  Lemma feval_shty_sim : forall p ups ρ t a, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> forall ups' ρ',
      dsim_list ups ups' -> env_agree (fun x => ~ pt_fresh x t) ρ ρ' ->
      exists a', ⟦shtyᶠ t of p ups' ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ a' /\ dsim a a'.
  Proof.
    intros * H; destruct feval_sim as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _).
    exact (Hs _ _ _ _ _ H).
  Qed.

  Lemma feval_ihty_sim : forall p ups ρm As ρ t m a, ⟦ihty m of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
      forall ups' ρm' ρ' m', dsim_list ups ups' -> ends_agree p As ρm ρm' t ->
      env_agree (fun x => ~ pt_fresh x t) ρ ρ' -> dsim m m' ->
      exists a', ⟦ihtyᶠ m' of t at p ups' under ρm' As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ a' /\ dsim_list a a'.
  Proof.
    intros * H; destruct feval_sim as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hy & _).
    exact (Hy _ _ _ _ _ _ _ _ H).
  Qed.

  (** The fields along a record view's path of related values: related
      values. *)
  Lemma feval_projs_sim : forall fl v ws, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws -> forall v', dsim v v' ->
      exists ws', ⟦projsᶠ fl of v' ⟧ᶠ Θ ⍮ Ξ ↘ ws' /\ dsim_list ws ws'.
  Proof.
    intros * H; destruct feval_sim as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
    exact (Hp _ _ _ H).
  Qed.

  (** A field of related values: related values. *)
  Lemma feval_proj_sim : forall f m r, eval_proj Θ Ξ f m r -> forall m', dsim m m' ->
      exists r', feval_proj Θ Ξ f m' r' /\ dsim r r'.
  Proof.
    intros * H; destruct feval_sim as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
    exact (Hp _ _ _ H).
  Qed.

  Lemma ffresh_cargs_sim : forall p ups ρ gs s vs, Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs ->
      forall ups' ρ', dsim_list ups ups' -> env_agree (fun _ => True) ρ ρ' ->
      exists vs', Fcargsᶠ gs of p ups' in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ vs' /\ dsim_list vs vs'.
  Proof.
    induction 1; intros ups' ρ' Hu Hρ.
    - exists nil; repeat constructor.
    - destruct (feval_exp_sim _ _ _ H ρ') as (a' & Ha' & Hsa); [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |].
      destruct (IHfresh_cargs ups' (ρ' ↦ ⇑! a' s)) as (vs' & ? & ?);
        [ exact Hu | apply env_agree_all_cons; [ exact Hρ | repeat constructor; assumption ] |].
      exists (⇑! a' s :: vs'); split; [ constructor; assumption | repeat constructor; assumption ].
    - destruct (feval_shty_sim _ _ _ _ _ H ups' ρ' Hu) as (a' & Ha' & Hsa);
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
      forall as2 vs2, fresh_leaf_vars bs as2 s vs2 -> dsim_list as1 as2 -> dsim_list vs1 vs2.
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
      forall rs2 l2 e2 out2, wrap_leaf_vals bs rs2 l2 e2 out2 -> dsim_list rs1 rs2 ->
      dsim_list (List.firstn (List.length (List.filter (fun b => b) bs)) l1)
                (List.firstn (List.length (List.filter (fun b => b) bs)) l2) ->
      dsim_list out1 out2.
  Proof.
    induction 1; intros * H2 Hr Hl; inversion H2; subst; inversion Hr; subst; cbn in Hl; [ constructor | | ].
    - inversion Hl; subst; constructor; [ assumption | eauto ].
    - constructor; [ assumption | eauto ].
  Qed.

  (** The recursive results a branch [B] is read under, fresh and wrapped:
      related where [B] reads them.  The results of an argument the branch
      reads none of are variables of type [𝕌ω@0] in the fast readback,
      along the paths of the container's. *)
  Lemma ffresh_wrap_sim : forall ρ As p ups Dc ρa gs' gs vs s ihs,
      Fihs vs at gs' gs of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs ->
      forall Bks wihs, ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
      forall D B ρ' ρa' ups' vs', ind_lookup Θ Ξ p = Some D -> leaves_coherent D ->
      (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ends_agree p As ρ ρ' t) ->
      env_agree (fun _ => True) ρa ρa' -> blocks_agree Bks ρ ρ' -> dsim_list ups ups' -> dsim_list vs vs' ->
      exists ihs' wihs', Fihsᶠ vs' at gs' gs of Dc under ρ' As at p ups' for B in Θ ⍮ Ξ ⍮ ρa' ⍮ s ↘ ihs' /\
        ⟦wihsᶠ vs' of gs' gs of Dc with ihs' under p ups' Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ wihs' /\
        dsim_list_at (fun x => ~ exp_fresh x B) wihs wihs'.
  Proof.
    induction 1; intros Bks wihs Hw D0 B ρ' ρa' ups' vs' HD Hco HA Hρa HB Hu Hv; inversion Hw; subst; clear Hw.
    - inversion Hv; subst; exists nil, nil; repeat constructor.
    - inversion Hv; subst.
      match goal with Hv1 : dsim v ?v1, Hv2 : dsim_list vs ?vs1, Hw1 : wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        destruct (IHfresh_ihs _ _ Hw1 D0 B ρ' (ρa' ↦ v1) ups' vs1 HD Hco
                    ltac:(intros gs1 t gs2 E; apply (HA (ca_arg T :: gs1) t gs2); rewrite E; reflexivity)
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
      destruct (feval_ih_sim _ _ _ _ _ _ _ Hih ρ' ups' a' HB Hu Hv1) as (rs' & ? & Hrs).
      pose proof (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Hih _ HD' Hco) as Hlr.
      assert (Hlb : List.length (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t))
                    = List.length (shape_leaves (rv_leaves D) 0 t)) by apply List.length_map.
      destruct (ihs_skipb (Some B) (cargs_nrec D gs) (List.length (shape_leaves (rv_leaves D) 0 t))) eqn:Hsk.
      + (** Skipped: variables at [𝕌ω@0], none read *)
        destruct (fresh_leaf_vars_exists (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t))
                    (List.repeat 𝕌ω@0 (List.length (shape_leaves (rv_leaves D) 0 t))) s
                    ltac:(rewrite List.repeat_length, Hlb; reflexivity)) as (ihs1' & Hfl').
        destruct (wrap_leaf_vals_exists _ rs' ihs1' ltac:(rewrite <- (dsim_list_length _ _ Hrs), Hlr, Hlb; reflexivity)
                    (fresh_leaf_vars_length _ _ _ _ Hfl')) as (out' & Hout).
        exists (ihs1' ++ ihs'0), (out' ++ wihs'); repeat split.
        * eapply ffresh_ihs_skip; [ exact HD' | exact Hsk | exact Hfl' | rewrite (fresh_leaf_vars_length _ _ _ _ Hfl'), <- Hl1; assumption ].
        * eapply fwrap_ihs_eval_rec; [ exact HD' | eassumption | apply wrap_leaf_vals_extend; exact Hout | assumption ].
        * destruct (ihs_skipb_sound _ _ _ Hsk) as (B0 & EB & HBf); injection EB as <-.
          apply dsim_list_at_skip.
          -- rewrite (wrap_leaf_vals_length _ _ _ _ _ Hwl1), (wrap_leaf_vals_length _ _ _ _ _ Hout); reflexivity.
          -- intros i0 Hi0 Hn; apply Hn.
             rewrite (proj1 (wrap_ihs_eval_length _ _ _ _ _ _ _ _ _ _ _ _ _ HD' Hco Hw1)); apply HBf.
             rewrite (wrap_leaf_vals_length _ _ _ _ _ Hwl1), Hlb in Hi0; exact Hi0.
          -- exact Hsi.
      + (** Computed: variables at the related types *)
        destruct (feval_ihty_sim _ _ _ _ _ _ _ _ Hty ups' ρ' ρa' a' Hu (HA nil t gs eq_refl)
                    ltac:(eapply env_agree_mono; [ exact Hρa | intros; exact I ]) Hv1) as (a2 & ? & Ha2).
        destruct (fresh_leaf_vars_exists (List.map (leaf_in Dc t') (shape_leaves (rv_leaves D) 0 t)) a2 s
                    ltac:(rewrite <- (dsim_list_length _ _ Ha2); exact (fresh_leaf_vars_lengths _ _ _ _ Hfl))) as (ihs1' & Hfl').
        destruct (wrap_leaf_vals_exists _ rs' ihs1' ltac:(rewrite <- (dsim_list_length _ _ Hrs), Hlr, Hlb; reflexivity)
                    (fresh_leaf_vars_length _ _ _ _ Hfl')) as (out' & Hout).
        exists (ihs1' ++ ihs'0), (out' ++ wihs'); repeat split.
        * eapply ffresh_ihs_rec; [ exact HD' | exact Hsk | eassumption | exact Hfl' | rewrite (fresh_leaf_vars_length _ _ _ _ Hfl'), <- Hl1; assumption ].
        * eapply fwrap_ihs_eval_rec; [ exact HD' | eassumption | apply wrap_leaf_vals_extend; exact Hout | assumption ].
        * apply dsim_list_at_app; [| exact Hsi ].
          eapply wrap_leaf_vals_sim; [ exact Hwl1 | exact Hout | exact Hrs |].
          rewrite !List.firstn_all2 by (first [ rewrite Hl1 | rewrite (fresh_leaf_vars_length _ _ _ _ Hfl') ]; lia).
          exact (fresh_leaf_vars_sim _ _ _ _ Hfl _ _ Hfl' Ha2).
    - (** Nested through: the eliminator's results along each path *)
      inversion Hv; subst.
      match goal with Hv1 : dsim v ?v1, Hv2 : dsim_list vs ?vs1, Hw1 : wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ _ _,
                      Hi : eval_ih _ _ _ _ _ _ _ _ _ |- _ =>
        let rs' := fresh "rs'" in
        destruct (feval_ih_sim _ _ _ _ _ _ _ Hi ρ' ups' v1 HB Hu Hv1) as (rs' & ? & ?);
        destruct (IHfresh_ihs _ _ Hw1 D0 B ρ' ρa' ups' vs1 HD Hco
                    ltac:(intros gs1 t0 gs2 E; apply (HA (ca_rec t :: gs1) t0 gs2); rewrite E; reflexivity)
                    Hρa HB Hu Hv2) as (ihs' & wihs' & ? & ? & ?);
        exists ihs', (rs' ++ wihs'); repeat split;
          [ constructor; assumption | econstructor; eassumption | apply dsim_list_at_app; assumption ]
      end.
  Qed.

  (** Readback of related values gives the same normal form. *)
  Theorem fread_sim :
    (forall s n W, Rnf n in Θ ⍮ Ξ ⍮ s ↘ W -> forall n', dsim_nf n n' -> Rnfᶠ n' in Θ ⍮ Ξ ⍮ s ↘ W) /\
    (forall s m W, Rne m in Θ ⍮ Ξ ⍮ s ↘ W -> forall m', dsim_ne m m' -> Rneᶠ m' in Θ ⍮ Ξ ⍮ s ↘ W) /\
    (forall s a W, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ W -> forall a', dsim a a' -> Rtypᶠ a' in Θ ⍮ Ξ ⍮ s ↘ W) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys -> forall xs', dsim_la xs xs' -> Rlaᶠ xs' in Θ ⍮ Ξ ⍮ s ↘ ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> forall ρ' vs',
       env_agree (fun _ => True) ρ ρ' -> dsim_list vs vs' -> Rpsᶠ vs' at T in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Ms) /\
    (forall s p ups ρ gs vs Ms, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> forall ups' ρ' vs',
       dsim_list ups ups' -> env_agree (fun _ => True) ρ ρ' -> dsim_list vs vs' -> Rcargsᶠ vs' at gs of p ups' in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Ms) /\
    (forall s p ups ρ t v V, Rsh v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V -> forall ups' ρ' v',
       dsim_list ups ups' -> env_agree (fun _ => True) ρ ρ' -> dsim v v' -> Rshᶠ v' at t of p ups' in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ V) /\
    (forall s ρ p ups Bks Dc sel i Ms NBks, Rblks i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks -> forall ρ' ups' D,
       blocks_agree Bks ρ ρ' -> dsim_list ups ups' -> ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks ->
       rview_leaf_arity D ->
       Rblksᶠ i Ms of Dc from p ups' Bks sel in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ NBks) /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs', Rbrs Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
       forall ρ' ups' pre' D,
       blocks_agree Bks ρ ρ' -> dsim_list ups ups' -> dsim_list (snd r) pre' ->
       ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks -> rview_leaf_arity D -> im_nn Mv = im_nn Mi ->
       env_agree (fun x => ~ exp_fresh (S (im_nn Mi) + x) A) ρ ρ' ->
       (forall c n B, In (c, n, B) Bs -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ') ->
       Rbrsᶠ Bs at cs of Mi (fst r, pre') of Dc from p ups' Bks Mv A in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Bs') /\
    (forall s ρ fl v Fs, Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs -> forall ρ' v',
       env_agree (fun _ => True) ρ ρ' -> dsim v v' -> Rfldsᶠ v' at fl in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Fs).
  Proof.
    apply (read_mut_ind Θ Ξ
      (fun s n W _ => forall n', dsim_nf n n' -> Rnfᶠ n' in Θ ⍮ Ξ ⍮ s ↘ W)
      (fun s m W _ => forall m', dsim_ne m m' -> Rneᶠ m' in Θ ⍮ Ξ ⍮ s ↘ W)
      (fun s a W _ => forall a', dsim a a' -> Rtypᶠ a' in Θ ⍮ Ξ ⍮ s ↘ W)
      (fun s xs ys _ => forall xs', dsim_la xs xs' -> Rlaᶠ xs' in Θ ⍮ Ξ ⍮ s ↘ ys)
      (fun s ρ T vs Ms _ => forall ρ' vs',
         env_agree (fun _ => True) ρ ρ' -> dsim_list vs vs' -> Rpsᶠ vs' at T in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Ms)
      (fun s p ups ρ gs vs Ms _ => forall ups' ρ' vs',
         dsim_list ups ups' -> env_agree (fun _ => True) ρ ρ' -> dsim_list vs vs' -> Rcargsᶠ vs' at gs of p ups' in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Ms)
      (fun s p ups ρ t v V _ => forall ups' ρ' v',
         dsim_list ups ups' -> env_agree (fun _ => True) ρ ρ' -> dsim v v' -> Rshᶠ v' at t of p ups' in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ V)
      (fun s ρ p ups Bks Dc sel i Ms NBks _ => forall ρ' ups' D,
         blocks_agree Bks ρ ρ' -> dsim_list ups ups' -> ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks ->
         rview_leaf_arity D ->
         Rblksᶠ i Ms of Dc from p ups' Bks sel in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ NBks)
      (fun s ρ p ups Bks Dc Mv A Mi r cs Bs Bs' _ => forall ρ' ups' pre' D,
         blocks_agree Bks ρ ρ' -> dsim_list ups ups' -> dsim_list (snd r) pre' ->
         ind_lookup Θ Ξ p = Some D -> blocks_nm_at D None Bks -> rview_leaf_arity D -> im_nn Mv = im_nn Mi ->
         env_agree (fun x => ~ exp_fresh (S (im_nn Mi) + x) A) ρ ρ' ->
         (forall c n B, In (c, n, B) Bs -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ') ->
         Rbrsᶠ Bs at cs of Mi (fst r, pre') of Dc from p ups' Bks Mv A in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Bs')
      (fun s ρ fl v Fs _ => forall ρ' v',
         env_agree (fun _ => True) ρ ρ' -> dsim v v' -> Rfldsᶠ v' at fl in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Fs));
      intros; cbn [fst snd] in *;
      repeat match goal with
        | H : dsim_nf _ _ |- _ => inversion H; subst; clear H
        | H : dsim_ne (_ _) _ |- _ => inversion H; subst; clear H
        | H : dsim_ne (_ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim_ne (_ _ _ _ _ _ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim_la (_ :: _) _ |- _ => inversion H; subst; clear H
        | H : dsim_la nil _ |- _ => inversion H; subst; clear H
        | H : dsim (_ _) _ |- _ => inversion H; subst; clear H
        | H : dsim (_ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim (_ _ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim (_ _ _ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim ⊤ᵈ _ |- _ => inversion H; subst; clear H
        | H : dsim ⊥ᵈ _ |- _ => inversion H; subst; clear H
        | H : dsim_list (_ :: _) _ |- _ => inversion H; subst; clear H
        | H : dsim_list nil _ |- _ => inversion H; subst; clear H
        | H : forall b, In b ?Bks -> (forall x, _ -> desim (env_entry ?ρ x) (env_entry ?ρ' x)) /\ _ |- _ =>
            change (blocks_agree Bks ρ ρ') in H
        end.
    (** Records.  A value of a record type, its parameters at their
        telescope and its fields' projections at their types; a record
        type; and the fields, each a projection of related values at a type
        evaluated in environments related everywhere. *)
    all: try solve [ match goal with
      | IH1 : forall ρ0 vs0, env_agree _ nil ρ0 -> dsim_list ?ns vs0 -> Rpsᶠ vs0 at _ in _ ⍮ _ ⍮ ρ0 ⍮ _ ↘ ?Ps,
        IH2 : forall ρ0 v0, env_agree _ (env_args nil ?ns) ρ0 -> dsim ?v v0 -> Rfldsᶠ v0 at _ in _ ⍮ _ ⍮ ρ0 ⍮ _ ↘ ?Fs,
        Ha : dsim_list ?ns ?ns', Hv : dsim ?v ?v'
        |- Rnfᶠ ⇓ (d_record _ ?ns') ?v' in _ ⍮ _ ⍮ _ ↘ nf_tuple _ ?Ps _ ?Fs =>
          econstructor; try eassumption;
            [ rewrite <- (dsim_list_length _ _ Ha); assumption
            | apply IH1; [ apply env_agree_nil | exact Ha ]
            | apply IH2; [ apply env_agree_all_args; [ apply env_agree_nil | exact Ha ] | exact Hv ] ]
      | IH : forall ρ0 vs0, env_agree _ nil ρ0 -> dsim_list ?ns vs0 -> Rpsᶠ vs0 at _ in _ ⍮ _ ⍮ ρ0 ⍮ _ ↘ ?Ps,
        Ha : dsim_list ?ns ?ns' |- Rtypᶠ d_record _ ?ns' in _ ⍮ _ ⍮ _ ↘ nf_record _ ?Ps =>
          econstructor; try eassumption;
            [ rewrite <- (dsim_list_length _ _ Ha); assumption | apply IH; [ apply env_agree_nil | exact Ha ] ]
      | Hp : eval_proj _ _ ?f ?v ?r, e : ⟦ ?T ⟧ Θ ⍮ Ξ ⍮ ?ρ ↘ ?t, Hρ : env_agree (fun _ => True) ?ρ ?ρ',
        IHV : forall n0, dsim_nf (⇓ ?t ?r) n0 -> _, IHR : forall ρ0 v0, env_agree _ (?ρ ↦ ?r) ρ0 -> dsim ?v v0 -> _,
        Hv : dsim ?v ?v' |- _ =>
          let r' := fresh "r'" in let t' := fresh "t'" in
          destruct (feval_proj_sim _ _ _ Hp v' Hv) as (r' & ? & ?);
          destruct (feval_exp_sim _ _ _ e ρ') as (t' & ? & ?);
            [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |];
          econstructor; [ eassumption | eassumption | apply IHV; constructor; assumption
                        | apply IHR; [ apply env_agree_all_cons; assumption | exact Hv ] ]
      end ].
    (** Inductive types.  A constructor, a type, and the parameters and
        arguments of each, at their types: the types are evaluated in
        environments related everywhere. *)
    all: try solve [ match goal with
      | IH1 : forall ρ0 vs0, env_agree _ nil ρ0 -> dsim_list ?as' vs0 -> Rpsᶠ vs0 at _ in _ ⍮ _ ⍮ ρ0 ⍮ _ ↘ ?Ps,
        IH2 : forall ups0 ρ0 vs0, dsim_list _ ups0 -> env_agree _ (env_args nil ?as') ρ0 -> dsim_list _ vs0 ->
              fread_cargs _ _ _ _ ups0 ρ0 _ vs0 ?Args,
        Ha : dsim_list ?as' ?as'', Hv : dsim_list ?vs ?vs'
        |- Rnfᶠ ⇓ (d_ind _ _ ?as'') (d_con _ _ _ ?vs') in _ ⍮ _ ⍮ _ ↘ nf_con _ _ _ (?Ps ++ ?Args) =>
          econstructor; try eassumption;
            [ rewrite <- (dsim_list_length _ _ Ha); assumption
            | rewrite <- (dsim_list_length _ _ Hv); assumption
            | apply IH1; [ apply env_agree_nil | exact Ha ]
            | apply IH2; [ apply dsim_list_firstn, Ha | apply env_agree_all_args; [ apply env_agree_nil | exact Ha ]
                         | apply dsim_list_skipn, Hv ] ]
      end ].
    (** A constructor at a view, read as the view's: its arguments are the
        last ones. *)
    all: try solve [ match goal with
      | IH1 : forall ρ0 vs0, env_agree _ nil ρ0 -> dsim_list ?as' vs0 -> Rpsᶠ vs0 at _ in _ ⍮ _ ⍮ ρ0 ⍮ _ ↘ ?Ps,
        IH2 : forall ups0 ρ0 vs0, dsim_list _ ups0 -> env_agree _ (env_args nil ?as') ρ0 -> dsim_list (skipn ?n ?vs) vs0 ->
              fread_cargs _ _ _ _ ups0 ρ0 _ vs0 ?Args,
        Ha : dsim_list ?as' ?as'', Hv : dsim_list ?vs ?vs'
        |- Rnfᶠ ⇓ (d_ind _ _ ?as'') (d_con _ _ _ ?vs') in _ ⍮ _ ⍮ _ ↘ nf_con _ _ _ (?Ps ++ ?Args) =>
          eapply fread_nf_con_view with (n := n); try eassumption;
            [ rewrite <- (dsim_list_length _ _ Ha); assumption
            | rewrite <- (dsim_list_length _ _ Hv); assumption
            | apply IH1; [ apply env_agree_nil | exact Ha ]
            | apply IH2; [ apply dsim_list_firstn, Ha | apply env_agree_all_args; [ apply env_agree_nil | exact Ha ]
                         | apply dsim_list_skipn, Hv ] ]
      end ].
    (** A value at a record view, read as the view's constructor: its
        arguments the value's projections, related. *)
    all: try solve [ match goal with
      | e : ⟦projs ?fl of ?v ⟧ Θ ⍮ Ξ ↘ ?ws,
        IH1 : forall ρ0 vs0, env_agree _ nil ρ0 -> dsim_list ?as' vs0 -> Rpsᶠ vs0 at _ in _ ⍮ _ ⍮ ρ0 ⍮ _ ↘ ?Ps,
        IH2 : forall ups0 ρ0 vs0, dsim_list ?as' ups0 -> env_agree _ (env_args nil ?as') ρ0 -> dsim_list ?ws vs0 ->
              fread_cargs _ _ _ _ ups0 ρ0 _ vs0 ?Args,
        Ha : dsim_list ?as' ?as'', Hv : dsim ?v ?v'
        |- Rnfᶠ ⇓ (d_ind _ _ ?as'') ?v' in _ ⍮ _ ⍮ _ ↘ nf_con _ _ _ (?Ps ++ ?Args) =>
          let ws' := fresh "ws'" in let Hws := fresh "Hws" in
          destruct (feval_projs_sim _ _ _ e _ Hv) as (ws' & ? & Hws);
          eapply fread_nf_rview; try eassumption;
            [ rewrite <- (dsim_list_length _ _ Ha); assumption
            | apply IH1; [ apply env_agree_nil | exact Ha ]
            | apply IH2; [ exact Ha | apply env_agree_all_args; [ apply env_agree_nil | exact Ha ] | exact Hws ] ]
      end ].
    all: try solve [ match goal with
      | IH : forall ρ0 vs0, env_agree _ nil ρ0 -> dsim_list ?as' vs0 -> Rpsᶠ vs0 at _ in _ ⍮ _ ⍮ ρ0 ⍮ _ ↘ ?Ps,
        Hps : Rps ?as' at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Ps,
        Ha : dsim_list ?as' ?as'' |- Rtypᶠ d_ind _ _ ?as'' in _ ⍮ _ ⍮ _ ↘ nf_indty _ _ ?Ps =>
          destruct as'' as [| a0 as0];
          [ (** without arguments, by the rule that reads no declaration *)
            inversion Ha; subst; inversion Hps; subst; apply fread_typ_indty_nil
          | eapply fread_typ_indty; [ eassumption | eassumption | |];
            [ rewrite <- (dsim_list_length _ _ Ha); assumption | apply IH; [ apply env_agree_nil | exact Ha ] ] ]
      end ].
    all: try solve [ match goal with
      | e : ⟦ ?A ⟧ Θ ⍮ Ξ ⍮ ?ρ ↘ ?a, Hρ : env_agree (fun _ => True) ?ρ ?ρ',
        IHV : forall n0, dsim_nf (⇓ ?a ?v) n0 -> _, Hv : dsim ?v ?v' |- _ =>
          let a' := fresh "a'" in
          destruct (feval_exp_sim _ _ _ e ρ') as (a' & ? & ?);
            [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |];
          econstructor; [ eassumption | apply IHV; constructor; assumption |];
          match goal with IH : forall ρ0, _ |- _ => eapply IH; eauto with mctt end
      end ].
    (** A recursive argument, along its shape. *)
    all: try solve [ match goal with
      | IHS : forall ups0 ρ0 v0, dsim_list ?ups ups0 -> env_agree _ ?ρ ρ0 -> dsim ?v v0 -> fread_shape _ _ _ _ ups0 ρ0 _ v0 _,
        IHR : forall ups0 ρ0 vs0, dsim_list ?ups ups0 -> env_agree _ ?ρ ρ0 -> dsim_list ?vs vs0 -> fread_cargs _ _ _ _ ups0 ρ0 _ vs0 _,
        Hu : dsim_list ?ups ?ups', Hρ : env_agree _ ?ρ ?ρ', Hv : dsim ?v ?v', Hvs : dsim_list ?vs ?vs' |- _ =>
          constructor; [ apply IHS; assumption | apply IHR; assumption ]
      end ].
    (** The end of a shape: the member at the uniform parameters and the
        shape's own; a function shape, under a fresh variable of its domain. *)
    all: try solve [ match goal with
      | e : ⟦ ?Ps ⟧* Θ ⍮ Ξ ⍮ ?ρ ↘ ?bs, Hρ : env_agree (fun _ => True) ?ρ ?ρ', Hu : dsim_list ?ups ?ups', Hv : dsim ?v ?v',
        IH : forall n0, dsim_nf (⇓ (d_ind ?p ?j (?ups ++ ?bs)) ?v) n0 -> _ |- _ =>
          let bs' := fresh "bs'" in let Hbs := fresh "Hbs" in
          destruct (feval_exps_sim _ _ _ e ρ') as (bs' & ? & Hbs);
            [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |];
          econstructor; [ eassumption | apply IH; constructor; [ constructor; apply dsim_list_app; assumption | exact Hv ] ]
      | e : ⟦ ?B ⟧ Θ ⍮ Ξ ⍮ ?ρ ↘ ?b, ea : $| ?v & ⇑! ?b ?s | Θ ⍮ Ξ ↘ ?r,
        Hρ : env_agree (fun _ => True) ?ρ ?ρ', Hu : dsim_list ?ups ?ups', Hv : dsim ?v ?v',
        IHA : forall a0, dsim ?b a0 -> Rtypᶠ a0 in _ ⍮ _ ⍮ _ ↘ _,
        IHV : forall ups0 ρ0 v0, dsim_list ?ups ups0 -> env_agree _ (?ρ ↦ _) ρ0 -> dsim ?r v0 -> _ |- _ =>
          let b' := fresh "b'" in let Hb := fresh "Hb" in let r' := fresh "r'" in let Hr := fresh "Hr" in
          destruct (feval_exp_sim _ _ _ e ρ') as (b' & ? & Hb);
            [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |];
          destruct (feval_app_sim _ _ _ ea v' (⇑! b' s) Hv ltac:(repeat constructor; exact Hb)) as (r' & ? & Hr);
          econstructor; [ eassumption | apply IHA; exact Hb | eassumption
                        | apply IHV; [ exact Hu | apply env_agree_all_cons; [ exact Hρ | repeat constructor; exact Hb ] | exact Hr ] ]
      end ].
    (** A stuck eliminator: the container's uniform parameters read at
        their telescope; the blocks at the eliminator's uniform
        parameters. *)
    all: try solve [ match goal with
      | em : eval_mref _ _ ?p ?ups ?j (_, _, ?pre),
        IHU : forall ρ0 vs0, env_agree _ nil ρ0 -> dsim_list ?pre vs0 -> _,
        IHB : forall ρ0 ups0 D0, blocks_agree ?Bks ?ρ ρ0 -> _,
        IHM : forall m0, dsim_ne ?m m0 -> _,
        HBk : blocks_agree ?Bks ?ρ ?ρ', Hu : dsim_list ?ups ?ups', Ha : dsim_list ?as' ?as'', Hm : dsim_ne ?m ?m'
        |- Rneᶠ d_elim _ _ _ _ _ _ _ in _ ⍮ _ ⍮ _ ↘ _ =>
          let pre' := fresh "pre'" in let Hem := fresh "Hem" in let Hpre := fresh "Hpre" in
          destruct (feval_mref_sim _ _ _ _ em ups' Hu) as (pre' & Hem & Hpre); cbn [fst snd] in Hem, Hpre;
          eapply fread_ne_elim; try eassumption;
            try solve [ rewrite <- (dsim_list_length _ _ Ha); assumption
                      | apply IHU; [ apply env_agree_nil | exact Hpre ]
                      | eapply IHB; eassumption
                      | apply IHM; exact Hm ]
      end ].
    (** A block: its motive under the fresh non-uniform parameters of its
        member and the scrutinee; its branches; and the blocks after it.
        The block's member has as many non-uniform parameters as the member
        read, both being the motive's binders. *)
    all: try solve [ constructor ].
    all: try solve [ match goal with
      | f : fresh_tele _ _ (env_args nil ?ups) (List.rev (im_nparams ?Mv)) ?s ?ns,
        Hnth : List.nth_error ?Bks ?ix = Some ?bk, Hnmb : eb_nm ?bk = S (im_nn ?Mi), HMv : ind_member ?D0 ?ix = Some ?Mv,
        em : eval_mref _ _ ?p ?ups _ (?pk, ?k, ?pre),
        e2 : ⟦ eb_motive ?bk ⟧ Θ ⍮ Ξ ⍮ env_args ?ρ (?ns ++ _) ↘ ?a,
        IHA : forall a0, dsim ?a a0 -> Rtypᶠ a0 in _ ⍮ _ ⍮ _ ↘ _,
        IHS : forall ρ0 ups0 pre0 D1, blocks_agree ?Bks ?ρ ρ0 -> _,
        IHR : forall ρ0 ups0 D1, blocks_agree ?Bks ?ρ ρ0 -> _,
        HD0 : ind_lookup Θ Ξ ?p = Some ?D0, Hl : ind_lookup Θ Ξ ?p = Some ?D, Hnm : blocks_nm_at ?D None ?Bks,
        HBk : blocks_agree ?Bks ?ρ ?ρ', Hu : dsim_list ?ups ?ups' |- _ =>
          let pre' := fresh "pre'" in let Hem := fresh "Hem" in let Hpre := fresh "Hpre" in
          let ns' := fresh "ns'" in let Hsn := fresh "Hsn" in let a' := fresh "a'" in let Hsa := fresh "Hsa" in
          let Hnn := fresh "Hnn" in let Hln := fresh "Hln" in
          rewrite HD0 in Hl; injection Hl as <-;
          assert (Hnn : im_nn Mv = im_nn Mi) by (pose proof (Hnm _ _ _ HMv Hnth) as Hx; cbn [elim_src] in Hx; congruence);
          pose proof (fresh_tele_length _ _ _ _ f) as Hln; rewrite length_rev in Hln;
          change (List.length (im_nparams Mv)) with (im_nn Mv) in Hln;
          destruct (feval_mref_sim _ _ _ _ em ups' Hu) as (pre' & Hem & Hpre); cbn [fst snd] in Hem, Hpre;
          destruct (ffresh_tele_sim _ _ _ _ f (env_args nil ups')) as (ns' & ? & Hsn);
            [ apply env_agree_all_args; [ apply env_agree_nil | exact Hu ] |];
          destruct (feval_exp_sim _ _ _ e2 (env_args ρ' (ns' ++ ⇑! (d_ind pk k (pre' ++ ns')) (s + im_nn Mi) :: nil)))
            as (a' & ? & Hsa);
            [ eapply env_agree_binders;
                [ exact (proj1 (HBk _ (List.nth_error_In _ _ Hnth)))
                | apply dsim_list_app; [ exact Hsn | repeat constructor; apply dsim_list_app; assumption ]
                | rewrite length_app, Hln, Hnn, Hnmb; cbn; lia ]
            |];
          eapply fread_blocks_cons; try eassumption;
            [ apply IHA; exact Hsa
            | eapply IHS; try eassumption;
                [ rewrite <- Hnmb; exact (proj1 (HBk _ (List.nth_error_In _ _ Hnth)))
                | exact (proj2 (HBk _ (List.nth_error_In _ _ Hnth))) ]
            | eapply IHR; eassumption ]
      end ].
    (** A branch: under the fresh non-uniform parameters, arguments and
        recursive results; the motive at the constructor. *)
    all: try solve [ match goal with
      | f : fresh_tele _ _ (env_args nil ?ups) (List.rev (im_nparams ?Mv)) ?s ?ns,
        f0 : fresh_cargs _ _ ?p ?ups (env_args nil (?ups ++ ?ns)) ?gs _ ?vs,
        f2 : fresh_ihs _ _ ?ρ _ _ _ _ _ ?gs' ?gs ?vs _ ?ihs,
        fw : wrap_ihs_eval _ _ ?ρ _ _ _ _ ?gs' ?gs ?vs ?ihs ?wihs,
        e0 : ⟦ ?B ⟧ Θ ⍮ Ξ ⍮ env_args ?ρ (?ns ++ ?vs ++ ?wihs) ↘ ?b,
        e1 : ⟦ ?A ⟧ Θ ⍮ Ξ ⍮ env_args ?ρ (?ns ++ d_con ?pk ?k ?c (?pre ++ _) :: nil) ↘ ?t,
        Hn0 : ?n0 = _, Hpl : cargs_plen ?D0 ?gs, HD0 : ind_lookup Θ Ξ ?p = Some ?D0,
        Hl : ind_lookup Θ Ξ ?p = Some ?D, Hnm : blocks_nm_at ?D None ?Bks, Har : rview_leaf_arity ?D,
        Hnn : im_nn ?Mv = im_nn ?Mi,
        IHV : forall n0, dsim_nf (⇓ ?t ?b) n0 -> _,
        IHT : forall ρ0 ups0 pre0 D1, blocks_agree ?Bks ?ρ ρ0 -> _,
        HBk : blocks_agree ?Bks ?ρ ?ρ', Hu : dsim_list ?ups ?ups', Hpre : dsim_list ?pre ?pre',
        HA : env_agree (fun x => ~ exp_fresh (S (im_nn ?Mi) + x) ?A) ?ρ ?ρ',
        HBs : forall c n B, In (c, n, B) (_ :: _) -> env_agree _ ?ρ ?ρ' |- _ =>
          let ns' := fresh "ns'" in let vs' := fresh "vs'" in let ihs' := fresh "ihs'" in let wihs' := fresh "wihs'" in
          let Hsn := fresh "Hsn" in let Hsv := fresh "Hsv" in let Hsi := fresh "Hsi" in
          let b' := fresh "b'" in let t' := fresh "t'" in
          let Hl1 := fresh "Hl" in let Hl2 := fresh "Hl" in let Hl3 := fresh "Hl" in
          let Hco := fresh "Hco" in
          rewrite HD0 in Hl; injection Hl as <-;
          pose proof (leaves_coherent_of_order _ (rview_leaf_order _ Har)) as Hco;
          pose proof (fresh_tele_length _ _ _ _ f) as Hl1; rewrite length_rev in Hl1;
          change (List.length (im_nparams Mv)) with (im_nn Mv) in Hl1;
          pose proof (wrap_ihs_eval_length _ _ _ _ _ _ _ _ _ _ _ _ _ HD0 Hco fw) as [Hl2 Hl3];
          destruct (ffresh_tele_sim _ _ _ _ f (env_args nil ups')) as (ns' & ? & Hsn);
            [ apply env_agree_all_args; [ apply env_agree_nil | exact Hu ] |];
          destruct (ffresh_cargs_sim _ _ _ _ _ _ f0 ups' (env_args nil (ups' ++ ns'))) as (vs' & ? & Hsv);
            [ exact Hu | apply env_agree_all_args; [ apply env_agree_nil | apply dsim_list_app; assumption ] |];
          destruct (ffresh_wrap_sim _ _ _ _ _ _ _ _ _ _ _ f2 _ _ fw _ B ρ' (env_args nil (ups' ++ ns')) ups' vs' HD0 Hco
                      (cargs_ends_agree _ _ _ _ _ _ HD0 Har Hnm HBk Hpl)
                      ltac:(apply env_agree_all_args; [ apply env_agree_nil | apply dsim_list_app; assumption ])
                      HBk Hu Hsv) as (ihs' & wihs' & ? & ? & Hsi);
          destruct (feval_exp_sim _ _ _ e0 (env_args ρ' (ns' ++ vs' ++ wihs'))) as (b' & ? & ?);
            [ eapply env_agree_binders_at;
                [ exact (HBs _ _ _ (or_introl eq_refl))
                | apply dsim_list_at_app; [ exact Hsn | apply dsim_list_at_app; assumption ]
                | rewrite !length_app, Hl1, Hl2, Hl3, Hn0, Hnn; lia ]
            |];
          destruct (feval_exp_sim _ _ _ e1 (env_args ρ' (ns' ++ d_con pk k c (pre' ++ ns' ++ vs') :: nil))) as (t' & ? & ?);
            [ eapply env_agree_binders;
                [ exact HA
                | apply dsim_list_app; [ exact Hsn | repeat constructor; apply dsim_list_app; [ exact Hpre | apply dsim_list_app; assumption ] ]
                | rewrite length_app, Hl1, Hnn; cbn; lia ]
            |];
          eapply fread_brs_cons; try eassumption;
            [ apply IHV; constructor; assumption
            | eapply IHT; try eassumption; intros c1 n1 B1 Hin; exact (HBs c1 n1 B1 (or_intror Hin)) ]
      end ].
    (** The closures are evaluated at related arguments, then read back. *)
    all: repeat match goal with
      | He : ⟦ ?B ⟧ Θ ⍮ Ξ ⍮ ?ρ ↦ ?c1 ↦ ?c2 ↘ ?b,
        Hρ : forall x, ~ exp_fresh (S (S x)) ?B -> desim (env_entry ?ρ x) (env_entry ?ρ' x) |- _ =>
          destruct (feval_clo2_sim B ρ ρ' c1 _ c2 _ b Hρ ltac:(eauto with mctt) ltac:(eauto with mctt) He)
            as (? & ? & ?); clear He
      | He : ⟦ ?B ⟧ Θ ⍮ Ξ ⍮ ?ρ ↦ ?c ↘ ?b,
        Hρ : forall x, ~ exp_fresh (S x) ?B -> desim (env_entry ?ρ x) (env_entry ?ρ' x) |- _ =>
          destruct (feval_clo_sim B ρ ρ' c _ b Hρ ltac:(eauto with mctt) He) as (? & ? & ?); clear He
      | He : $| ?m & ?n | Θ ⍮ Ξ ↘ ?r, Hm : dsim ?m ?m' |- _ =>
          destruct (feval_app_sim _ _ _ He m' _ Hm ltac:(eauto with mctt)) as (? & ? & ?); clear He
      end.
    (** A neutral level's sort is read off its type, which is related. *)
    all: try (erewrite dsort_sim by eassumption).
    all: solve [ econstructor; eauto 6 with mctt ].
  Qed.

  Corollary fread_typ_sim : forall s a a' W, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ W -> dsim a a' -> Rtypᶠ a' in Θ ⍮ Ξ ⍮ s ↘ W.
  Proof. intros; eapply (proj1 (proj2 (proj2 fread_sim))); eassumption. Qed.

  Corollary fread_nf_sim : forall s n n' W, Rnf n in Θ ⍮ Ξ ⍮ s ↘ W -> dsim_nf n n' -> Rnfᶠ n' in Θ ⍮ Ξ ⍮ s ↘ W.
  Proof. intros; eapply (proj1 fread_sim); eassumption. Qed.
End Read.
End Sim.

#[export]
Hint Constructors dsim dsim_ne dsim_nf dmsim dsim_la dsim_list dsim_fields desim ends_agree dsim_list_at : mctt.
#[export]
Hint Resolve dsim_lvl_suc dsim_lvl_max dsim_list_snoc env_agree_nil
  dsim_list_app dsim_list_firstn dsim_list_skipn env_agree_all_args env_agree_all_cons nil_agree : mctt.
