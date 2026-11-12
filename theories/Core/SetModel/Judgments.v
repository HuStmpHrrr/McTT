(** * The Set Judgments

    The judgments of the set model, at a universe tower [T] and a
    valuation [γ] of the global context.  Environments of a context are
    related ([set_env_rel]) when their entries are equal and of the
    entries' types, definitions and units; a term denotes a function of
    the environment ([set_denotes]) when that function is its value at
    every environment of the context and every value of it at a related
    environment equals the function's.  Existence and uniqueness are thus
    proved together, by the fundamental theorem, for well-formed terms
    only.

    The judgments then follow the syntactic ones: equal terms of a type
    denote one function into the type's carriers ([set_exp_eq]), a subtype
    has the smaller carriers ([set_subtyp]), equal extensions relate the
    same environments ([set_ext_eq]), equal module expressions and units
    denote one module whose members are of their types ([set_modexp_eq],
    [set_unit_eq]). *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation Require Export Functional.
From Mctt.Core.Syntactic Require Import Syntax Members.
Import ListNotations.

(** The environment without its variable [#0]. *)
Definition set_env_tail (ρ : set_env) : set_env := fun x => ρ (S x).

Section Judgments.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** ** Related Environments *)

(** [set_assumption_with Γ ρ κ A e e' x x' a]: the entries [e] and [e'] of
    an assumption of [A] of the kind [κ] are equal values [x] and [x'] of
    [A]'s value [a]. *)
Record set_assumption_with (Γ : ctx) (ρ : set_env) (κ : abs_kind) (A : exp) (e e' : set_entry) (x x' a : aczel_set) : Prop :=
  { (** The left entry is the term [x] *)
    set_assumption_left : e = set_entry_term κ x
    (** The right entry is the term [x'] *)
  ; set_assumption_right : e' = set_entry_term κ x'
    (** [A] denotes [a] *)
  ; set_assumption_type : set_interp T γ Γ ρ A a
    (** [x] is of [a] *)
  ; set_assumption_mem : set_mem x (code_carrier a)
    (** The two are equal *)
  ; set_assumption_eq : set_eq x x' }.

(** [set_definition_with Γ ρ M e e' v v' w]: the entries [e] and [e'] of a
    definition of [M] are values [v] and [v'] equal to [M]'s value [w]. *)
Record set_definition_with (Γ : ctx) (ρ : set_env) (M : exp) (e e' : set_entry) (v v' w : aczel_set) : Prop :=
  { (** The left entry is the relevant term [v] *)
    set_definition_left : e = set_entry_term ak_relevant v
    (** The right entry is the relevant term [v'] *)
  ; set_definition_right : e' = set_entry_term ak_relevant v'
    (** [M] denotes [w] *)
  ; set_definition_value : set_interp T γ Γ ρ M w
    (** [v] is [w] *)
  ; set_definition_left_eq : set_eq v w
    (** [v'] is [w] *)
  ; set_definition_right_eq : set_eq v' w }.

(** [set_module_slot_with Γ ρ U e e' m m' n]: the entries [e] and [e'] of
    a module slot of the unit [U] are modules [m] and [m'] equal to [U]'s
    module [n]. *)
Record set_module_slot_with (Γ : ctx) (ρ : set_env) (U : gunit) (e e' : set_entry) (m m' n : set_module) : Prop :=
  { (** The left entry is the module [m] *)
    set_module_slot_left : e = set_entry_module m
    (** The right entry is the module [m'] *)
  ; set_module_slot_right : e' = set_entry_module m'
    (** [U] denotes [n] *)
  ; set_module_slot_unit : set_interp_gunit T γ Γ ρ U n
    (** [m] is [n] *)
  ; set_module_slot_left_eq : set_module_eq m n
    (** [m'] is [n] *)
  ; set_module_slot_right_eq : set_module_eq m' n }.

(** [set_definition_module_with Γ ρ M U e e' v v' w m m' n]: the entries
    [e] and [e'] of a definition of [M] with the module part [U] are terms
    [v], [v'] equal to [M]'s value [w], with modules [m], [m'] equal to
    [U]'s module [n]. *)
Record set_definition_module_with (Γ : ctx) (ρ : set_env) (M : exp) (U : gunit) (e e' : set_entry)
    (v v' w : aczel_set) (m m' n : set_module) : Prop :=
  { (** The left entry is the term [v] with the module [m] *)
    set_definition_module_left : e = set_entry_both v m
    (** The right entry is the term [v'] with the module [m'] *)
  ; set_definition_module_right : e' = set_entry_both v' m'
    (** [M] denotes [w] *)
  ; set_definition_module_value : set_interp T γ Γ ρ M w
    (** [U] denotes [n] *)
  ; set_definition_module_unit : set_interp_gunit T γ Γ ρ U n
    (** [v] is [w] *)
  ; set_definition_module_left_eq : set_eq v w
    (** [v'] is [w] *)
  ; set_definition_module_right_eq : set_eq v' w
    (** [m] is [n] *)
  ; set_definition_module_left_module_eq : set_module_eq m n
    (** [m'] is [n] *)
  ; set_definition_module_right_module_eq : set_module_eq m' n }.

(** [set_entry_rel Γ ρ ce e e']: [e] and [e'] are related entries of the
    context entry [ce] of [Γ], at [ρ]. *)
Definition set_entry_rel (Γ : ctx) (ρ : set_env) (ce : centry) (e e' : set_entry) : Prop :=
  match ce with
  | ce_ass κ A => exists x x' a, set_assumption_with Γ ρ κ A e e' x x' a
  | ce_def _ M => exists v v' w, set_definition_with Γ ρ M e e' v v' w
  | ce_mod U => exists m m' n, set_module_slot_with Γ ρ U e e' m m' n
  | ce_dm _ M U => exists v v' w m m' n, set_definition_module_with Γ ρ M U e e' v v' w m m' n
  end.

(** [set_env_rel Γ ρ ρ']: [ρ] and [ρ'] are related environments of [Γ];
    below the context their entries are equal, as a term read past its
    context would read them. *)
Fixpoint set_env_rel (Γ : ctx) (ρ ρ' : set_env) : Prop :=
  match Γ with
  | nil => set_env_eq ρ ρ'
  | ce :: Γ' => set_env_rel Γ' (set_env_tail ρ) (set_env_tail ρ') /\ set_entry_rel Γ' (set_env_tail ρ) ce (ρ 0) (ρ' 0)
  end.

(** [ρ] is an environment of [Γ]. *)
Definition set_env_in (Γ : ctx) (ρ : set_env) : Prop := set_env_rel Γ ρ ρ.

(** ** Denotations *)

(** [set_denotes Γ M F]: [M] denotes [F] in [Γ]. *)
Record set_denotes (Γ : ctx) (M : exp) (F : set_env -> aczel_set) : Prop :=
  { (** [F ρ] is [M]'s value at every environment *)
    set_denotes_exists : forall ρ, set_env_in Γ ρ -> set_interp T γ Γ ρ M (F ρ)
    (** Every value of [M] at a related environment is [F]'s *)
  ; set_denotes_unique : forall ρ ρ' v, set_env_rel Γ ρ ρ' -> set_interp T γ Γ ρ' M v -> set_eq v (F ρ) }.

(** [set_modexp_denotes Γ H F]: the module expression [H] denotes [F] in
    [Γ]. *)
Record set_modexp_denotes (Γ : ctx) (H : modexp) (F : set_env -> set_module) : Prop :=
  { (** [F ρ] is [H]'s module at every environment *)
    set_modexp_denotes_exists : forall ρ, set_env_in Γ ρ -> set_interp_modexp T γ Γ ρ H (F ρ)
    (** Every module of [H] at a related environment is [F]'s *)
  ; set_modexp_denotes_unique : forall ρ ρ' m, set_env_rel Γ ρ ρ' -> set_interp_modexp T γ Γ ρ' H m -> set_module_eq m (F ρ) }.

(** The submodule at the chain [ys] of a module. *)
Definition select_modules (m : set_module) (ys : list string) : set_module := fold_left (select_module γ) ys m.

(** [set_members_valid Γ H F]: every term member of a submodule of [H],
    of [F]'s modules, is of its type, and is its δ-reduct when it has
    one. *)
Definition set_members_valid (Γ : ctx) (H : modexp) (F : set_env -> set_module) : Prop :=
  forall ys x R A FA, mdenote gc_deps gc_stack Γ (me_mem (me_mems H ys) x) R -> mdesc_type R = Some A ->
    set_denotes Γ A FA -> forall ρ, set_env_in Γ ρ ->
    set_mem (select_term γ (select_modules (F ρ) ys) x) (code_carrier (FA ρ)) /\
    (forall N FN, mdesc_reduct R = Some N -> set_denotes Γ N FN -> set_eq (select_term γ (select_modules (F ρ) ys) x) (FN ρ)).

(** ** The Judgments *)

(** [set_exp_eq_with Γ A M M' FA FM FM']: [A] denotes [FA], [M] and [M']
    the equal [FM] and [FM'], of [FA]'s carriers.  The two are equal, not
    the same function: a denotation is a term's exact value, and equal terms
    such as [(λ A M) N] and [M[N]] have equal values, not the same. *)
Record set_exp_eq_with (Γ : ctx) (A M M' : exp) (FA FM FM' : set_env -> aczel_set) : Prop :=
  { (** The type's denotation *)
    set_exp_eq_type : set_denotes Γ A FA
    (** The left term's *)
  ; set_exp_eq_left : set_denotes Γ M FM
    (** The right term's *)
  ; set_exp_eq_right : set_denotes Γ M' FM'
    (** The two are equal *)
  ; set_exp_eq_eq : forall ρ, set_env_in Γ ρ -> set_eq (FM ρ) (FM' ρ)
    (** Of the type *)
  ; set_exp_eq_mem : forall ρ, set_env_in Γ ρ -> set_mem (FM ρ) (code_carrier (FA ρ)) }.

(** [M] and [M'] are equal terms of the type [A] in [Γ]. *)
Definition set_exp_eq (Γ : ctx) (A M M' : exp) : Prop := exists FA FM FM', set_exp_eq_with Γ A M M' FA FM FM'.

(** [set_subtyp_with Γ A A' FA FA']: [A] and [A'] denote [FA] and [FA'],
    the first's carriers in the second's. *)
Record set_subtyp_with (Γ : ctx) (A A' : exp) (FA FA' : set_env -> aczel_set) : Prop :=
  { (** The subtype's denotation *)
    set_subtyp_left : set_denotes Γ A FA
    (** The supertype's *)
  ; set_subtyp_right : set_denotes Γ A' FA'
    (** The subtype's carriers are in the supertype's *)
  ; set_subtyp_sub : forall ρ, set_env_in Γ ρ -> set_sub (code_carrier (FA ρ)) (code_carrier (FA' ρ)) }.

(** [A] is a subtype of [A'] in [Γ]. *)
Definition set_subtyp (Γ : ctx) (A A' : exp) : Prop := exists FA FA', set_subtyp_with Γ A A' FA FA'.

(** [set_modexp_eq_with Γ H H' F F']: [H] and [H'] denote the equal [F] and
    [F'], whose members are valid. *)
Record set_modexp_eq_with (Γ : ctx) (H H' : modexp) (F F' : set_env -> set_module) : Prop :=
  { (** The left expression's denotation *)
    set_modexp_eq_left : set_modexp_denotes Γ H F
    (** The right expression's *)
  ; set_modexp_eq_right : set_modexp_denotes Γ H' F'
    (** The two are equal *)
  ; set_modexp_eq_eq : forall ρ, set_env_in Γ ρ -> set_module_eq (F ρ) (F' ρ)
    (** Its members are of their types *)
  ; set_modexp_eq_members : set_members_valid Γ H F }.

(** [H] and [H'] are equal module expressions in [Γ]. *)
Definition set_modexp_eq (Γ : ctx) (H H' : modexp) : Prop := exists F F', set_modexp_eq_with Γ H H' F F'.

(** [U] and [U'] are equal units in [Γ]: as literal module expressions. *)
Definition set_unit_eq (Γ : ctx) (U U' : gunit) : Prop := set_modexp_eq Γ (me_lit U) (me_lit U').

(** [set_entry_valid Γ ce]: the context entry [ce] is valid in [Γ]: its
    type, definition or unit denotes. *)
Definition set_entry_valid (Γ : ctx) (ce : centry) : Prop :=
  match ce with
  | ce_ass _ A => exists FA, set_denotes Γ A FA
  | ce_def A M => set_exp_eq Γ A M M
  | ce_mod U => set_unit_eq Γ U U
  | ce_dm A M U => set_exp_eq Γ A M M /\ set_unit_eq Γ U U
  end.

(** [set_ctx Γ]: every entry of [Γ] is valid in the context before it. *)
Fixpoint set_ctx (Γ : ctx) : Prop :=
  match Γ with
  | nil => True
  | ce :: Γ' => set_ctx Γ' /\ set_entry_valid Γ' ce
  end.

(** [set_ext_eq_with Γ Ψ Ψ']: the extensions [Ψ] and [Ψ'] of [Γ] are
    valid and relate the same environments. *)
Record set_ext_eq_with (Γ Ψ Ψ' : ctx) : Prop :=
  { (** The left extension is valid *)
    set_ext_eq_left : set_ctx (Ψ ++ Γ)
    (** The right extension is valid *)
  ; set_ext_eq_right : set_ctx (Ψ' ++ Γ)
    (** They relate the same environments *)
  ; set_ext_eq_rel : forall ρ ρ', set_env_rel (Ψ ++ Γ) ρ ρ' <-> set_env_rel (Ψ' ++ Γ) ρ ρ' }.

(** ** Denotations Respect Related Environments *)

Lemma set_denotes_rel : forall Γ M F ρ ρ', set_denotes Γ M F -> set_env_rel Γ ρ ρ' -> set_env_in Γ ρ' ->
    set_eq (F ρ') (F ρ).
Proof. intros * [Hex Hun] Hr Hin. exact (Hun _ _ _ Hr (Hex _ Hin)). Qed.

Lemma set_modexp_denotes_rel : forall Γ H F ρ ρ', set_modexp_denotes Γ H F -> set_env_rel Γ ρ ρ' -> set_env_in Γ ρ' ->
    set_module_eq (F ρ') (F ρ).
Proof. intros * [Hex Hun] Hr Hin. exact (Hun _ _ _ Hr (Hex _ Hin)). Qed.

Lemma set_interp_me_lit_iff : forall Γ ρ U m, set_interp_modexp T γ Γ ρ (me_lit U) m <-> set_interp_gunit T γ Γ ρ U m.
Proof. intros. split; intros H; [inversion H; subst; assumption | constructor; exact H]. Qed.

(** Related environments extended by equal values of an assumption's
    type are related. *)
Lemma set_env_rel_extend_ass : forall Γ ρ ρ' κ A a x x', set_env_rel Γ ρ ρ' -> set_interp T γ Γ ρ A a ->
    set_mem x (code_carrier a) -> set_eq x x' ->
    set_env_rel (ce_ass κ A :: Γ) (set_env_extend ρ (set_entry_term κ x)) (set_env_extend ρ' (set_entry_term κ x')).
Proof. intros * Hr Ha Hx E. split; [exact Hr |]. exists x, x', a. constructor; auto. Qed.

Lemma set_env_in_extend_ass : forall Γ ρ κ A a x, set_env_in Γ ρ -> set_interp T γ Γ ρ A a ->
    set_mem x (code_carrier a) -> set_env_in (ce_ass κ A :: Γ) (set_env_extend ρ (set_entry_term κ x)).
Proof. intros * Hr Ha Hx. apply set_env_rel_extend_ass with (a := a); [exact Hr | exact Ha | exact Hx | apply set_eq_refl]. Qed.

(** Related environments of a valid context form a partial equivalence. *)
Lemma set_env_rel_per : forall Γ, set_ctx Γ ->
    (forall ρ ρ', set_env_rel Γ ρ ρ' -> set_env_rel Γ ρ' ρ) /\
    (forall ρ1 ρ2 ρ3, set_env_rel Γ ρ1 ρ2 -> set_env_rel Γ ρ2 ρ3 -> set_env_rel Γ ρ1 ρ3).
Proof.
  induction Γ as [| ce Γ IH]; intros HΓ.
  { split; cbn [set_env_rel].
    - intros ρ ρ' H x. apply set_entry_eq_sym. apply H.
    - intros ρ1 ρ2 ρ3 H1 H2 x. eapply set_entry_eq_trans; [apply H1 | apply H2]. }
  destruct HΓ as [HΓ Hce]. destruct (IH HΓ) as [Hsym Htrans].
  assert (Hin : forall ρ ρ', set_env_rel Γ ρ ρ' -> set_env_in Γ ρ /\ set_env_in Γ ρ')
    by (intros ρ ρ' H; split; [eapply Htrans; [exact H | apply Hsym; exact H] | eapply Htrans; [apply Hsym; exact H | exact H]]).
  split.
  - intros ρ ρ' [Ht He]. split; [apply Hsym; exact Ht |].
    destruct (Hin _ _ Ht) as [Hl Hr].
    destruct ce as [κ A | A M | U | A M U]; cbn [set_entry_rel set_entry_valid] in He, Hce |- *.
    + destruct He as (x & x' & a & [E1 E2 Ha Hx Exx']). destruct Hce as [FA HFA].
      pose proof (set_denotes_exists _ _ _ HFA _ Hr) as Ha'.
      pose proof (set_denotes_unique _ _ _ HFA _ _ _ Hl Ha) as Ea.
      pose proof (set_denotes_rel _ _ _ _ _ HFA Ht Hr) as Ea'.
      exists x', x, (FA (set_env_tail ρ')). constructor; try assumption; [| apply set_eq_sym; exact Exx'].
      eapply set_mem_eq_l; [exact Exx' |]. eapply set_mem_eq_r; [| exact Hx]. apply code_carrier_resp.
      eapply set_eq_trans; [exact Ea | apply set_eq_sym; exact Ea'].
    + destruct He as (v & v' & w & [E1 E2 Hw Ev Ev']). destruct Hce as (FA & FM & FM' & [_ HFM _ _ _]).
      pose proof (set_denotes_unique _ _ _ HFM _ _ _ Hl Hw) as Ew.
      pose proof (set_denotes_rel _ _ _ _ _ HFM Ht Hr) as Ew'.
      exists v', v, (FM (set_env_tail ρ')). constructor; try assumption; [exact (set_denotes_exists _ _ _ HFM _ Hr) | |].
      * eapply set_eq_trans; [exact Ev' |]. eapply set_eq_trans; [exact Ew | apply set_eq_sym; exact Ew'].
      * eapply set_eq_trans; [exact Ev |]. eapply set_eq_trans; [exact Ew | apply set_eq_sym; exact Ew'].
    + destruct He as (m & m' & n & [E1 E2 Hn Em Em']). destruct Hce as (FU & FU' & [HFU _ _ _]).
      pose proof (set_modexp_denotes_unique _ _ _ HFU _ _ _ Hl (proj2 (set_interp_me_lit_iff _ _ _ _) Hn)) as En.
      pose proof (set_modexp_denotes_rel _ _ _ _ _ HFU Ht Hr) as En'.
      exists m', m, (FU (set_env_tail ρ')). constructor; try assumption;
        [exact (proj1 (set_interp_me_lit_iff _ _ _ _) (set_modexp_denotes_exists _ _ _ HFU _ Hr)) | |].
      * eapply set_module_eq_trans; [exact Em' |]. eapply set_module_eq_trans; [exact En | apply set_module_eq_sym; exact En'].
      * eapply set_module_eq_trans; [exact Em |]. eapply set_module_eq_trans; [exact En | apply set_module_eq_sym; exact En'].
    + destruct He as (v & v' & w & m & m' & n & [E1 E2 Hw Hn Ev Ev' Em Em']).
      destruct Hce as [(FA & FM & FM' & [_ HFM _ _ _]) (FU & FU' & [HFU _ _ _])].
      pose proof (set_denotes_unique _ _ _ HFM _ _ _ Hl Hw) as Ew.
      pose proof (set_denotes_rel _ _ _ _ _ HFM Ht Hr) as Ew'.
      pose proof (set_modexp_denotes_unique _ _ _ HFU _ _ _ Hl (proj2 (set_interp_me_lit_iff _ _ _ _) Hn)) as En.
      pose proof (set_modexp_denotes_rel _ _ _ _ _ HFU Ht Hr) as En'.
      exists v', v, (FM (set_env_tail ρ')), m', m, (FU (set_env_tail ρ')). constructor; try assumption;
        [exact (set_denotes_exists _ _ _ HFM _ Hr)
        | exact (proj1 (set_interp_me_lit_iff _ _ _ _) (set_modexp_denotes_exists _ _ _ HFU _ Hr)) | | | |].
      * eapply set_eq_trans; [exact Ev' |]. eapply set_eq_trans; [exact Ew | apply set_eq_sym; exact Ew'].
      * eapply set_eq_trans; [exact Ev |]. eapply set_eq_trans; [exact Ew | apply set_eq_sym; exact Ew'].
      * eapply set_module_eq_trans; [exact Em' |]. eapply set_module_eq_trans; [exact En | apply set_module_eq_sym; exact En'].
      * eapply set_module_eq_trans; [exact Em |]. eapply set_module_eq_trans; [exact En | apply set_module_eq_sym; exact En'].
  - intros ρ1 ρ2 ρ3 [Ht12 He12] [Ht23 He23]. split; [eapply Htrans; eassumption |].
    destruct ce as [κ A | A M | U | A M U]; cbn [set_entry_rel set_entry_valid] in He12, He23, Hce |- *.
    + destruct He12 as (x1 & x2 & a & [E1 E2 Ha Hx Ex]). destruct He23 as (y2 & y3 & b & [F2 F3 Hb Hy Ey]).
      rewrite E2 in F2. injection F2 as <-. exists x1, y3, a. constructor; try assumption. eapply set_eq_trans; eassumption.
    + destruct He12 as (v1 & v2 & w & [E1 E2 Hw Ev1 Ev2]). destruct He23 as (u2 & u3 & w' & [F2 F3 Hw' Eu2 Eu3]).
      rewrite E2 in F2. injection F2 as <-. destruct Hce as (FA & FM & FM' & [_ HFM _ _ _]).
      destruct (Hin _ _ Ht12) as [Hl1 Hr2].
      pose proof (set_denotes_unique _ _ _ HFM _ _ _ Hl1 Hw) as Ew.
      pose proof (set_denotes_unique _ _ _ HFM _ _ _ Hr2 Hw') as Ew'.
      pose proof (set_denotes_rel _ _ _ _ _ HFM Ht12 Hr2) as E12.
      exists v1, u3, w. constructor; try assumption.
      eapply set_eq_trans; [exact Eu3 |]. eapply set_eq_trans; [exact Ew' |].
      eapply set_eq_trans; [exact E12 | apply set_eq_sym; exact Ew].
    + destruct He12 as (m1 & m2 & n & [E1 E2 Hn Em1 Em2]). destruct He23 as (k2 & k3 & n' & [F2 F3 Hn' Ek2 Ek3]).
      rewrite E2 in F2. injection F2 as <-. destruct Hce as (FU & FU' & [HFU _ _ _]).
      destruct (Hin _ _ Ht12) as [Hl1 Hr2].
      pose proof (set_modexp_denotes_unique _ _ _ HFU _ _ _ Hl1 (proj2 (set_interp_me_lit_iff _ _ _ _) Hn)) as En.
      pose proof (set_modexp_denotes_unique _ _ _ HFU _ _ _ Hr2 (proj2 (set_interp_me_lit_iff _ _ _ _) Hn')) as En'.
      pose proof (set_modexp_denotes_rel _ _ _ _ _ HFU Ht12 Hr2) as E12.
      exists m1, k3, n. constructor; try assumption.
      eapply set_module_eq_trans; [exact Ek3 |]. eapply set_module_eq_trans; [exact En' |].
      eapply set_module_eq_trans; [exact E12 | apply set_module_eq_sym; exact En].
    + destruct He12 as (v1 & v2 & w & m1 & m2 & n & [E1 E2 Hw Hn Ev1 Ev2 Em1 Em2]).
      destruct He23 as (u2 & u3 & w' & k2 & k3 & n' & [F2 F3 Hw' Hn' Eu2 Eu3 Ek2 Ek3]).
      rewrite E2 in F2. injection F2 as <- <-. destruct Hce as [(FA & FM & FM' & [_ HFM _ _ _]) (FU & FU' & [HFU _ _ _])].
      destruct (Hin _ _ Ht12) as [Hl1 Hr2].
      pose proof (set_denotes_unique _ _ _ HFM _ _ _ Hl1 Hw) as Ew.
      pose proof (set_denotes_unique _ _ _ HFM _ _ _ Hr2 Hw') as Ew'.
      pose proof (set_denotes_rel _ _ _ _ _ HFM Ht12 Hr2) as E12.
      pose proof (set_modexp_denotes_unique _ _ _ HFU _ _ _ Hl1 (proj2 (set_interp_me_lit_iff _ _ _ _) Hn)) as En.
      pose proof (set_modexp_denotes_unique _ _ _ HFU _ _ _ Hr2 (proj2 (set_interp_me_lit_iff _ _ _ _) Hn')) as En'.
      pose proof (set_modexp_denotes_rel _ _ _ _ _ HFU Ht12 Hr2) as F12.
      exists v1, u3, w, m1, k3, n. constructor; try assumption.
      * eapply set_eq_trans; [exact Eu3 |]. eapply set_eq_trans; [exact Ew' |].
        eapply set_eq_trans; [exact E12 | apply set_eq_sym; exact Ew].
      * eapply set_module_eq_trans; [exact Ek3 |]. eapply set_module_eq_trans; [exact En' |].
        eapply set_module_eq_trans; [exact F12 | apply set_module_eq_sym; exact En].
Qed.

(** Related environments have equal entries. *)
Lemma set_env_rel_eq : forall Γ ρ ρ', set_env_rel Γ ρ ρ' -> set_env_eq ρ ρ'.
Proof.
  induction Γ as [| ce Γ IH]; intros ρ ρ' H; [exact H |]. destruct H as [Ht He].
  pose proof (IH _ _ Ht) as Et. intros [| x]; [| exact (Et x)].
  destruct ce as [κ A | A M | U | A M U]; cbn [set_entry_rel] in He.
  - destruct He as (x & x' & a & [-> -> _ _ E]). constructor. exact E.
  - destruct He as (v & v' & w & [-> -> _ E1 E2]). constructor. eapply set_eq_trans; [exact E1 | apply set_eq_sym; exact E2].
  - destruct He as (m & m' & n & [-> -> _ E1 E2]). constructor. eapply set_module_eq_trans; [exact E1 | apply set_module_eq_sym; exact E2].
  - destruct He as (v & v' & w & m & m' & n & [-> -> _ _ E1 E2 E3 E4]). constructor;
      [eapply set_eq_trans; [exact E1 | apply set_eq_sym; exact E2] | eapply set_module_eq_trans; [exact E3 | apply set_module_eq_sym; exact E4]].
Qed.

Section Functional.
  Hypothesis Hfn : fn_kinds_unique.
  Hypothesis Hmods : forall q, set_module_eq (global_module γ q) (global_module γ q).

(** A term that has a value at every environment of a valid context
    denotes it: functionality gives the uniqueness. *)
Corollary set_denotes_of_exists : forall Γ M F, set_ctx Γ ->
    (forall ρ, set_env_in Γ ρ -> set_interp T γ Γ ρ M (F ρ)) -> set_denotes Γ M F.
Proof.
  intros * HΓ Hex. constructor; [exact Hex |]. intros ρ ρ' v Hr Hv.
  destruct (set_env_rel_per _ HΓ) as [Hsym Htrans].
  assert (Hρ : set_env_in Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
  apply set_eq_sym. exact (set_interp_functional T γ Hfn Hmods _ _ _ _ (Hex _ Hρ) _ _ (set_env_rel_eq _ _ _ Hr) Hv).
Qed.

Corollary set_modexp_denotes_of_exists : forall Γ H F, set_ctx Γ ->
    (forall ρ, set_env_in Γ ρ -> set_interp_modexp T γ Γ ρ H (F ρ)) -> set_modexp_denotes Γ H F.
Proof.
  intros * HΓ Hex. constructor; [exact Hex |]. intros ρ ρ' m Hr Hm.
  destruct (set_env_rel_per _ HΓ) as [Hsym Htrans].
  assert (Hρ : set_env_in Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
  apply set_module_eq_sym. exact (set_interp_modexp_functional T γ Hfn Hmods _ _ _ _ (Hex _ Hρ) _ _ (set_env_rel_eq _ _ _ Hr) Hm).
Qed.

End Functional.

End Judgments.
