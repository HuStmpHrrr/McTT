From Stdlib Require List.

#[global] Declare Scope mctt_scope.
#[global] Delimit Scope mctt_scope with mctt.
#[global] Bind Scope mctt_scope with Sortclass.

(** The [mctt] hint database is created here, in the module every other
    module loads first, so that no [Hint ... : mctt] creates it implicitly. *)
Create HintDb mctt discriminated.

(** [Syntax.cmd], [Command.ccmd] and [Domain.domain] nest through [list]; with
    this scheme registered, their generated induction principles carry the
    induction hypothesis for the list elements (as [list_all]). *)
Scheme All for list.

(** The surface syntax ([Syntax.Cst]), the terms ([Syntax.exp]) and the
    values ([Domain.domain]) also nest through pairs and options: the
    branches of an eliminator, the fields of a record value, the binders of
    a block.  With these two schemes registered, the generated principles
    carry the induction hypotheses for the components of a pair
    ([prod_all]) and for the content of an option ([option_all]) as well;
    a component of another type gets the trivial hypothesis [unit]. *)
Scheme All for prod.
Scheme All for option.

(** The hypotheses of these schemes, read as [Forall] and as a [match],
    the forms proofs by induction on the elements state them in.  The
    lemmas are universe polymorphic, as the schemes are: a hypothesis about
    a list of [Set]s is one at the universe of [Set]. *)

(** Every element's hypothesis implies the claim of it. *)
#[universes(polymorphic)]
Lemma list_all_Forall_impl : forall A (Q : A -> Type) (R : A -> Prop) (l : list A),
    (forall x, Q x -> R x) -> list_all A Q l -> List.Forall R l.
Proof.
  intros A Q R l HQR H; induction H as [| x Hx l _ IH];
    [ apply List.Forall_nil | apply List.Forall_cons; [ exact (HQR x Hx) | exact IH ] ].
Qed.

(** The hypotheses of a list's elements. *)
#[universes(polymorphic)]
Lemma list_all_Forall : forall A (P : A -> Prop) (l : list A), list_all A P l -> List.Forall P l.
Proof. intros A P l; apply list_all_Forall_impl; intros x Hx; exact Hx. Qed.

(** The hypotheses of the second components of a list of pairs. *)
#[universes(polymorphic)]
Lemma list_all_snd : forall A B (P : B -> Prop) (l : list (prod A B)),
    list_all (prod A B) (prod_all A (fun _ => unit) B P) l -> List.Forall (fun p => P (snd p)) l.
Proof. intros A B P l; apply list_all_Forall_impl; intros x Hx; destruct Hx as [a _ b Hb]; exact Hb. Qed.

(** The hypothesis of an option's content, if any. *)
#[universes(polymorphic)]
Lemma option_all_match : forall A (P : A -> Prop) (o : option A),
    option_all A P o -> match o with Some a => P a | None => True end.
Proof. intros A P o H; destruct H; [ assumption | exact I ]. Qed.
