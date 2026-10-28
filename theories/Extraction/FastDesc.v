From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Extraction Require Import Lookup.
Import ListNotations Syntax_Notations.

(** * Fast Member Descriptions

    The twin of Core's member descriptions ([mdesc]) whose closed modules
    hold their bodies as tries: what a module expression denotes, as the
    extracted checker computes it ([MemberType.mdenote_fimpl]), reading a
    filed or open-frame body by one lookup per name.  A local body ([mdesc_open])
    stays Core's.  Each operation of Core on descriptions has a twin here,
    equal to it through the decoding [dec_desc] ([fmdesc_at_dec] and the
    like).

    A closed body is the translation of a canonical Core body
    ([canon_trie]), and an entry read off it of a canonical entry
    ([canon_fentry]): both are [Prop] arguments, erased by extraction, which
    make decoding exact on them. *)

(** ** Canonical Tries and Entries *)

(** A trie that translates a canonical body *)
Definition canon_trie (t : ftrie) : Prop := exists Φ, t = tr_mod Φ /\ canon_mod Φ.

(** An entry that translates a canonical entry *)
Definition canon_fentry (e : fentry) : Prop := exists E, e = tr_entry E /\ canon_entry E.

(** An entry found in a canonical trie is canonical. *)
Lemma canon_trie_find : forall t y e, canon_trie t -> ft_find t y = Some e -> canon_fentry e.
Proof.
  intros t y e (Φ & -> & Hc) Hf; rewrite tr_mod_find in Hf.
  destruct (gm_newest Φ y) as [E |] eqn:En; [| discriminate ]; injection Hf as <-.
  exists E; split; [ reflexivity | exact (canon_newest _ _ _ Hc En) ].
Qed.

(** A stored closed entry read in a closed body of telescope [T], [ge_read]'s
    twin: a closed submodule is read with its full telescope. *)
Definition fe_read (T : ctx) (e : fentry) : fentry :=
  match e with
  | fe_mod pv (fu_mk Δ (fmd_body t)) => fe_mod pv (fu_mk (Δ ++ T) (fmd_body t))
  | _ => e
  end.

(** Reading keeps an entry canonical. *)
Lemma canon_fe_read : forall T e, canon_fentry e -> canon_fentry (fe_read T e).
Proof.
  intros T e (E & -> & Hc).
  destruct E as [| pv [Δ [[|] Φ | H]] | | |]; cbn in Hc; try contradiction;
    first [ exists (ge_read T (ge_mod pv (gu_mk Δ (md_body sm_closed Φ)))); split; [ reflexivity | exact Hc ]
          | eexists; split; [ reflexivity | exact Hc ] ].
Qed.

(** Reading commutes with decoding on a canonical entry. *)
Lemma fe_read_dec : forall T e, canon_fentry e -> dec_entry (fe_read T e) = ge_read T (dec_entry e).
Proof.
  intros T e (E & -> & Hc); rewrite dec_tr_entry by exact Hc.
  destruct E as [| pv [Δ [[|] Φ | H]] | | |]; cbn in Hc |- *; try contradiction; try reflexivity;
    rewrite ?dec_tr_mod, ?dec_tr_unit by exact Hc; reflexivity.
Qed.

(** ** Descriptions *)

Inductive fmdesc : Type :=
(** [mdesc_term A om] *)
| fmdesc_term : typ -> option exp -> fmdesc
(** [mdesc_open Δ Φ Φx]: a local body, Core's *)
| fmdesc_open : ctx -> gmod -> gmod -> fmdesc
(** [mdesc_closed Θ' p T Φ Ns], with the stored body [Φ] kept as the
    canonical trie [t] *)
| fmdesc_closed : ctx -> qname -> ctx -> forall t : ftrie, canon_trie t -> list exp -> fmdesc
(** [mdesc_dm Θd A M Rm] *)
| fmdesc_dm : ctx -> typ -> exp -> fmdesc -> fmdesc.

(** The Core description a fast one stands for, for types only *)
Fixpoint dec_desc (R : fmdesc) : mdesc :=
  match R with
  | fmdesc_term A om => mdesc_term A om
  | fmdesc_open Δ Φ Φx => mdesc_open Δ Φ Φx
  | fmdesc_closed Θ' p T t _ Ns => mdesc_closed Θ' p T (dec_mod t) Ns
  | fmdesc_dm Θd A M Rm => mdesc_dm Θd A M (dec_desc Rm)
  end.

(** [mdesc_type]'s twin *)
Definition fmdesc_type (R : fmdesc) : option typ :=
  match R with
  | fmdesc_term A _ => Some A
  | fmdesc_dm Θd A _ _ => Some (ctx_pi Θd A)
  | _ => None
  end.

Lemma fmdesc_type_dec : forall R, mdesc_type (dec_desc R) = fmdesc_type R.
Proof. intros []; reflexivity. Qed.

(** [mdesc_reduct]'s twin *)
Definition fmdesc_reduct (R : fmdesc) : option exp :=
  match R with
  | fmdesc_term _ om => om
  | fmdesc_dm Θd _ M _ => Some (ctx_fn Θd M)
  | _ => None
  end.

Lemma fmdesc_reduct_dec : forall R, mdesc_reduct (dec_desc R) = fmdesc_reduct R.
Proof. intros []; reflexivity. Qed.

(** [mdesc_mod]'s twin *)
Fixpoint fmdesc_mod (R : fmdesc) : option fmdesc :=
  match R with
  | fmdesc_open _ _ _ | fmdesc_closed _ _ _ _ _ _ => Some R
  | fmdesc_dm _ _ _ Rm => fmdesc_mod Rm
  | fmdesc_term _ _ => None
  end.

Lemma fmdesc_mod_dec : forall R, mdesc_mod (dec_desc R) = option_map dec_desc (fmdesc_mod R).
Proof. induction R; cbn; auto. Qed.

(** [mdesc_is_mod], decided *)
Definition fmdesc_is_modb (R : fmdesc) : bool :=
  match R with
  | fmdesc_open _ _ _ | fmdesc_closed _ _ _ _ _ _ => true
  | _ => false
  end.

Lemma fmdesc_is_modb_spec : forall R, fmdesc_is_modb R = true <-> mdesc_is_mod (dec_desc R).
Proof. intros []; cbn; split; intros; first [ exact I | reflexivity | discriminate | contradiction ]. Qed.

(** [mdesc_tele]'s twin *)
Definition fmdesc_tele (R : fmdesc) : option ctx :=
  match R with
  | fmdesc_open Δ _ _ => Some Δ
  | fmdesc_closed Θ' _ T _ _ Ns =>
      if Nat.leb (List.length Ns) (List.length T)
      then Some (tele_sub (List.firstn (List.length T - List.length Ns) T) (sb_of_list Id Ns) ++ Θ')
      else None
  | _ => None
  end.

Lemma fmdesc_tele_dec : forall R, mdesc_tele (dec_desc R) = fmdesc_tele R.
Proof. intros []; reflexivity. Qed.

(** [mdesc_mod_tele]'s twin *)
Definition fmdesc_mod_tele (R : fmdesc) : option ctx :=
  match fmdesc_mod R with
  | Some Rm => fmdesc_tele Rm
  | None => None
  end.

Lemma fmdesc_mod_tele_dec : forall R, mdesc_mod_tele (dec_desc R) = fmdesc_mod_tele R.
Proof.
  intros R; unfold mdesc_mod_tele, fmdesc_mod_tele; rewrite fmdesc_mod_dec.
  destruct (fmdesc_mod R); cbn [option_map]; [ apply fmdesc_tele_dec | reflexivity ].
Qed.

(** [mdesc_up]'s twin *)
Fixpoint fmdesc_up (Θ' : ctx) (R : fmdesc) : fmdesc :=
  match R with
  | fmdesc_term A om => fmdesc_term (ctx_pi Θ' A) (option_map (ctx_fn Θ') om)
  | fmdesc_open Δ Φ Φx => fmdesc_open (Δ ++ Θ') Φ Φx
  | fmdesc_closed Θ p T t Ht Ns => fmdesc_closed (Θ ++ Θ') p T t Ht Ns
  | fmdesc_dm Θd A M Rm => fmdesc_dm (Θd ++ Θ') A M (fmdesc_up Θ' Rm)
  end.

Lemma fmdesc_up_dec : forall Θ' R, dec_desc (fmdesc_up Θ' R) = mdesc_up Θ' (dec_desc R).
Proof. intros Θ'; induction R; cbn; f_equal; auto. Qed.

(** [mdesc_at]'s twin *)
Fixpoint fmdesc_at (R : fmdesc) (N : exp) : option fmdesc :=
  match R with
  | fmdesc_term A om =>
      match pi_view A with
      | Some (_, C) =>
          match om with
          | None => Some (fmdesc_term C[Id,,N] None)
          | Some M =>
              match fn_view M with
              | Some M' => Some (fmdesc_term C[Id,,N] (Some M'[Id,,N]))
              | None => None
              end
          end
      | None => None
      end
  | fmdesc_open Δ Φ Φx =>
      match tele_split (rev Δ) with
      | inl (_, Δ', τ) =>
          Some (fmdesc_open (tele_sub Δ' (Id,,N)) (gmod_sub Φ (τ ⨟ sb_qn (List.length Δ') (Id,,N)))
                  (gmod_sub Φx (τ ⨟ sb_qn (List.length Δ') (Id,,N))))
      | inr _ => None
      end
  | fmdesc_closed Θ p T t Ht Ns =>
      match tele_split (rev Θ) with
      | inl (_, Θ', τ) =>
          Some (fmdesc_closed (tele_sub Θ' (Id,,N)) p T t Ht (List.map (fun M => M[τ ⨟ sb_qn (List.length Θ') (Id,,N)]) Ns))
      | inr τ => Some (fmdesc_closed nil p T t Ht (List.map (fun M => M[τ]) Ns ++ N :: nil))
      end
  | fmdesc_dm Θ A M Rm =>
      match fmdesc_at Rm N with
      | None => None
      | Some Rm' =>
          match tele_split (rev Θ) with
          | inl (_, Θ', τ) =>
              Some (fmdesc_dm (tele_sub Θ' (Id,,N)) A[τ ⨟ sb_qn (List.length Θ') (Id,,N)] M[τ ⨟ sb_qn (List.length Θ') (Id,,N)] Rm')
          | inr _ => Some Rm'
          end
      end
  end.

Lemma fmdesc_at_dec : forall R N, mdesc_at (dec_desc R) N = option_map dec_desc (fmdesc_at R N).
Proof.
  induction R as [A om | Δ Φ Φx | Θ p T t Ht Ns | Θ A M Rm IH]; intros N; cbn [fmdesc_at mdesc_at dec_desc].
  - destruct (pi_view A) as [[? C] |]; [| reflexivity ].
    destruct om as [M |]; [| reflexivity ]; destruct (fn_view M); reflexivity.
  - destruct (tele_split (rev Δ)) as [[[? ?] ?] | ?]; reflexivity.
  - destruct (tele_split (rev Θ)) as [[[? ?] ?] | ?]; reflexivity.
  - rewrite IH; destruct (fmdesc_at Rm N); cbn [option_map]; [| reflexivity ].
    destruct (tele_split (rev Θ)) as [[[? ?] ?] | ?]; reflexivity.
Qed.

(** [mdesc_ats]'s twin *)
Fixpoint fmdesc_ats (R : fmdesc) (Ns : list exp) : option fmdesc :=
  match Ns with
  | nil => Some R
  | N :: Ns' =>
      match fmdesc_at R N with
      | Some R' => fmdesc_ats R' Ns'
      | None => None
      end
  end.

Lemma fmdesc_ats_dec : forall Ns R, mdesc_ats (dec_desc R) Ns = option_map dec_desc (fmdesc_ats R Ns).
Proof.
  induction Ns as [| N Ns IH]; intros R; cbn [fmdesc_ats mdesc_ats]; [ reflexivity |].
  rewrite fmdesc_at_dec; destruct (fmdesc_at R N); cbn [option_map]; [ apply IH | reflexivity ].
Qed.

(** [mdesc_sub]'s twin *)
Fixpoint fmdesc_sub (R : fmdesc) (σ : sub) : fmdesc :=
  match R with
  | fmdesc_term A om => fmdesc_term A[σ] (option_map (fun M => M[σ]) om)
  | fmdesc_open Δ Φ Φx => fmdesc_open (tele_sub Δ σ) (gmod_sub Φ (sb_qn (List.length Δ) σ)) (gmod_sub Φx (sb_qn (List.length Δ) σ))
  | fmdesc_closed Θ p T t Ht Ns => fmdesc_closed (tele_sub Θ σ) p T t Ht (List.map (fun M => M[sb_qn (List.length Θ) σ]) Ns)
  | fmdesc_dm Θd A M Rm => fmdesc_dm (tele_sub Θd σ) A[sb_qn (List.length Θd) σ] M[sb_qn (List.length Θd) σ] (fmdesc_sub Rm σ)
  end.

Lemma fmdesc_sub_dec : forall R σ, dec_desc (fmdesc_sub R σ) = mdesc_sub (dec_desc R) σ.
Proof. induction R; intros σ; cbn; f_equal; auto. Qed.

(** [mdesc_self]'s twin *)
Definition fmdesc_self (M : exp) (R : fmdesc) : fmdesc :=
  match R with
  | fmdesc_term A None => fmdesc_term A (Some M)
  | _ => R
  end.

Lemma fmdesc_self_dec : forall M R, dec_desc (fmdesc_self M R) = mdesc_self M (dec_desc R).
Proof. intros M [A [|] | | | ]; reflexivity. Qed.

(** [mdesc_named]'s twin *)
Definition fmdesc_named (Θ : ctx) (Ns : list exp) (M : exp) (R : fmdesc) : fmdesc :=
  match Θ, Ns with
  | nil, nil => R
  | _, _ => fmdesc_self M R
  end.

Lemma fmdesc_named_dec : forall Θ Ns M R, dec_desc (fmdesc_named Θ Ns M R) = mdesc_named Θ Ns M (dec_desc R).
Proof. intros [|] [|] M R; unfold fmdesc_named, mdesc_named; first [ reflexivity | apply fmdesc_self_dec ]. Qed.

(** [mdesc_term_part_at]'s twin *)
Definition fmdesc_term_part_at (R : fmdesc) (N : exp) : option fmdesc :=
  match R with
  | fmdesc_term A (Some M) =>
      match pi_view A with
      | Some (_, C) =>
          match fn_view M with
          | Some M' => Some (fmdesc_term C[Id,,N] (Some M'[Id,,N]))
          | None => if app_const M then Some (fmdesc_term C[Id,,N] (Some (a_app M N))) else None
          end
      | None => None
      end
  | _ => fmdesc_at R N
  end.

Lemma fmdesc_term_part_at_dec : forall R N, mdesc_term_part_at (dec_desc R) N = option_map dec_desc (fmdesc_term_part_at R N).
Proof.
  intros R N; destruct R as [A [M |] | | | ];
    try (match goal with |- mdesc_term_part_at (dec_desc ?R) ?N = _ => exact (fmdesc_at_dec R N) end).
  cbn [fmdesc_term_part_at mdesc_term_part_at dec_desc].
  destruct (pi_view A) as [[? C] |]; [| reflexivity ].
  destruct (fn_view M); [ reflexivity |]; destruct (app_const M); reflexivity.
Qed.

(** [mdesc_term_part_ats]'s twin *)
Fixpoint fmdesc_term_part_ats (R : fmdesc) (Ns : list exp) : option fmdesc :=
  match Ns with
  | nil => Some R
  | N :: Ns' =>
      match fmdesc_term_part_at R N with
      | Some R' => fmdesc_term_part_ats R' Ns'
      | None => None
      end
  end.

Lemma fmdesc_term_part_ats_dec : forall Ns R, mdesc_term_part_ats (dec_desc R) Ns = option_map dec_desc (fmdesc_term_part_ats R Ns).
Proof.
  induction Ns as [| N Ns IH]; intros R; cbn [fmdesc_term_part_ats mdesc_term_part_ats]; [ reflexivity |].
  rewrite fmdesc_term_part_at_dec; destruct (fmdesc_term_part_at R N); cbn [option_map]; [ apply IH | reflexivity ].
Qed.

(** [mdesc_ats_read]'s twin *)
Definition fmdesc_ats_read (R : fmdesc) (Ns : list exp) : option fmdesc :=
  match R with
  | fmdesc_dm nil A M Rm =>
      match fmdesc_term_part_ats (fmdesc_term A (Some M)) Ns, fmdesc_ats Rm Ns with
      | Some (fmdesc_term B (Some M')), Some Rm' => Some (fmdesc_dm nil B M' Rm')
      | _, _ => None
      end
  | _ => fmdesc_ats R Ns
  end.

Lemma fmdesc_ats_read_dec : forall R Ns, mdesc_ats_read (dec_desc R) Ns = option_map dec_desc (fmdesc_ats_read R Ns).
Proof.
  intros R Ns; destruct R as [| | | [| e Θd] A M Rm];
    try (match goal with |- mdesc_ats_read (dec_desc ?R) ?Ns = _ => exact (fmdesc_ats_dec Ns R) end).
  cbn [fmdesc_ats_read mdesc_ats_read dec_desc].
  change (mdesc_term A (Some M)) with (dec_desc (fmdesc_term A (Some M))).
  rewrite fmdesc_term_part_ats_dec, fmdesc_ats_dec.
  destruct (fmdesc_term_part_ats (fmdesc_term A (Some M)) Ns) as [[B [M' |] | | | ] |]; cbn [option_map dec_desc];
    destruct (fmdesc_ats Rm Ns); reflexivity.
Qed.

(** [mdesc_read]'s twin *)
Definition fmdesc_read (rd : reader) (R : fmdesc) : option fmdesc :=
  match rd with
  | reader_open Δ Φ' => option_map (fun σ => fmdesc_up Δ (fmdesc_sub R σ)) (gm_fill Φ')
  | reader_closed Θ Ns M => option_map (fun R1 => fmdesc_up Θ (fmdesc_named Θ Ns M R1)) (fmdesc_ats_read R Ns)
  end.

Lemma fmdesc_read_dec : forall rd R, mdesc_read rd (dec_desc R) = option_map dec_desc (fmdesc_read rd R).
Proof.
  intros [Δ Φ' | Θ Ns M] R; cbn [fmdesc_read mdesc_read].
  - destruct (gm_fill Φ'); cbn [option_map]; [ rewrite fmdesc_up_dec, fmdesc_sub_dec |]; reflexivity.
  - rewrite fmdesc_ats_read_dec; destruct (fmdesc_ats_read R Ns); cbn [option_map]; [ rewrite fmdesc_up_dec, fmdesc_named_dec |]; reflexivity.
Qed.

(** ** Entries of a Description *)

(** Where an entry of a description comes from: a local body, as Core's
    entry, read at no path; or a closed body stored at [p], as a canonical
    fast entry. *)
Inductive entry_source : Type :=
(** An entry of a local body *)
| entry_source_core : gentry -> entry_source
(** The entry stored at the path, fast *)
| entry_source_fast : qname -> forall e : fentry, canon_fentry e -> entry_source.

(** The Core entry, for types only *)
Definition dec_entry_source (s : entry_source) : gentry :=
  match s with
  | entry_source_core E => E
  | entry_source_fast _ e _ => dec_entry e
  end.

(** The path the entry is read at *)
Definition entry_source_path (s : entry_source) : option qname :=
  match s with
  | entry_source_core _ => None
  | entry_source_fast p _ _ => Some p
  end.

(** In a canonical body, the prefix up to a name ends with its newest
    entry. *)
Lemma prefix_newest : forall Φ y, canon_mod Φ ->
    match gm_prefix_upto Φ y with
    | Some (gm_ext _ x E) => x = y /\ gm_newest Φ y = Some E
    | Some _ => False
    | None => gm_newest Φ y = None
    end.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros y Hc; cbn in *; [ reflexivity | | contradiction ].
  destruct Hc as (_ & HΦ & _); destruct (String.eqb_spec y x) as [-> | Hn]; [ split; reflexivity |].
  exact (IH y HΦ).
Qed.

(** [mdesc_entry]'s twin: a closed body is read by one lookup *)
Definition fmdesc_entry (R : fmdesc) (y : string) : option (ctx * entry_source * reader) :=
  match R with
  | fmdesc_open Δ _ Φx =>
      match gm_prefix_upto Φx y with
      | Some (gm_ext Φ' _ E) =>
          match E with
          | ge_ind _ _ _ _ _ | ge_record _ _ _ _ | ge_def _ _ _ None | ge_def false _ _ _ => None
          | _ => Some (body_ctx Φ' ++ Δ, entry_source_core E, reader_open Δ Φ')
          end
      | _ => None
      end
  | fmdesc_closed Θ p T t Ht Ns =>
      match inspect (ft_find t y) with
      | exist _ (Some e) Ee =>
          Some (nil, entry_source_fast (qname_in p y) (fe_read T e) (canon_fe_read T e (canon_trie_find t y e Ht Ee)),
                reader_closed Θ Ns (apps (a_mem (qname_mod p) y) Ns))
      | exist _ None _ => None
      end
  | _ => None
  end.

(** It finds the decoding of what [mdesc_entry] finds, read at the path
    [mdesc_entry_path] gives. *)
Lemma fmdesc_entry_dec : forall R y,
    mdesc_entry (dec_desc R) y = option_map (fun r => (fst (fst r), dec_entry_source (snd (fst r)), snd r)) (fmdesc_entry R y).
Proof.
  intros [| Δ Φ Φx | Θ p T t Ht Ns |] y; cbn [fmdesc_entry mdesc_entry dec_desc]; try reflexivity.
  - destruct (gm_prefix_upto Φx y) as [[| Φ' x E | ? ? ?] |]; try reflexivity.
    destruct E as [[|] ? ? [|] | | | |]; reflexivity.
  - pose proof Ht as (Φ0 & Ht0 & Hc).
    pose proof (prefix_newest Φ0 y Hc) as Hp.
    pose proof (tr_mod_find Φ0 y) as Hf; rewrite <- Ht0 in Hf.
    rewrite Ht0 at 1; rewrite dec_tr_mod by exact Hc.
    destruct (inspect (ft_find t y)) as [[e |] Ee]; cbn [option_map fst snd dec_entry_source].
    + rewrite Ee in Hf; destruct (gm_newest Φ0 y) as [E |] eqn:En; [| discriminate ]; injection Hf as Hf.
      destruct (gm_prefix_upto Φ0 y) as [[| Φ' x E' | ? ? ?] |]; try contradiction; [| congruence ].
      destruct Hp as [-> HE]; injection HE as <-.
      rewrite fe_read_dec by (exists E; split; [ exact Hf | exact (canon_newest _ _ _ Hc En) ]).
      rewrite Hf, dec_tr_entry by exact (canon_newest _ _ _ Hc En); reflexivity.
    + rewrite Ee in Hf; destruct (gm_newest Φ0 y) eqn:En; [ discriminate |].
      destruct (gm_prefix_upto Φ0 y) as [[| Φ' x E' | ? ? ?] |]; try contradiction; [| reflexivity ].
      destruct Hp as [-> Hn]; congruence.
Qed.

(** [mdesc_entry_path]'s twin *)
Definition fmdesc_entry_path (R : fmdesc) (y : string) : option qname :=
  match R with
  | fmdesc_closed _ p _ _ _ _ => Some (qname_in p y)
  | _ => None
  end.

Lemma fmdesc_entry_path_dec : forall R y, mdesc_entry_path (dec_desc R) y = fmdesc_entry_path R y.
Proof. intros []; reflexivity. Qed.

(** An entry found is read at the path of the description's entries. *)
Lemma fmdesc_entry_source_path : forall R y Γy s rd, fmdesc_entry R y = Some (Γy, s, rd) -> entry_source_path s = fmdesc_entry_path R y.
Proof.
  intros [| Δ Φ Φx | Θ p T t Ht Ns |] y * He; cbn [fmdesc_entry] in He; try discriminate.
  - destruct (gm_prefix_upto Φx y) as [[| Φ' x E | ? ? ?] |]; try discriminate.
    destruct E as [[|] ? ? [|] | | | |]; try discriminate; injection He as _ <- _; reflexivity.
  - destruct (inspect (ft_find t y)) as [[e |] Ee]; [ injection He as _ <- _; reflexivity | discriminate ].
Qed.

(** [mdesc_unit]'s twin *)
Definition fmdesc_unit (R : fmdesc) : modexp :=
  match R with
  | fmdesc_open Δ Φ _ => me_lit (gu_mk Δ (md_body sm_open Φ))
  | fmdesc_closed nil p _ _ _ Ns => me_apps (qname_mod p) Ns
  | fmdesc_closed Θ' p _ _ _ Ns => me_lit (gu_mk Θ' (md_alias (me_apps (qname_mod p) Ns)))
  | _ => me_lit (gu_mk nil (md_body sm_open gm_nil))
  end.

Lemma fmdesc_unit_dec : forall R, mdesc_unit (dec_desc R) = fmdesc_unit R.
Proof. intros [| | [|] | ]; reflexivity. Qed.

(** [ind_former_desc]'s twin *)
Definition fast_ind_former_desc (pq : qname) (k : nat) (D : ind_decl) (Mk : imember) (Rm : fmdesc) : fmdesc :=
  fmdesc_dm nil (ctx_pi (im_params D Mk) (exp_wk (ind_sort D) (wk_shiftn (im_nn Mk)))) (a_ind pq k) Rm.

Lemma fast_ind_former_desc_dec : forall pq k D Mk Rm,
    dec_desc (fast_ind_former_desc pq k D Mk Rm) = ind_former_desc pq k D Mk (dec_desc Rm).
Proof. reflexivity. Qed.

(** [record_former_desc]'s twin *)
Definition fast_record_former_desc (p : qname) (R : record_decl) (Rm : fmdesc) : fmdesc :=
  fmdesc_dm nil (ctx_pi (record_params R) (record_sort R)) (a_record p) Rm.

Lemma fast_record_former_desc_dec : forall p R Rm,
    dec_desc (fast_record_former_desc p R Rm) = record_former_desc p R (dec_desc Rm).
Proof. reflexivity. Qed.

(** ** Located Bodies, Canonical *)

(** The located bodies of a fast context, with their tries canonical *)
Section Located.
  Variable F : FCtx.

  #[local] Ltac canon_open :=
    destruct (fc_ok F) as [Θ Ξ HcΘ HcΞ Hu Hv Hf];
    unfold fc_unit_at in *; rewrite ?Hf in *;
    pose proof (fun fp => fv_find_ok (fc_view F) Θ fp Hu Hv) as Huf;
    pose proof (canon_restrict (fv_dom (fc_view F)) Θ HcΘ) as HcR.

  (** Where a module is stored: its trie is canonical. *)
  Lemma fc_loc_canon : forall p T t, fc_loc F p = Some (T, t) -> canon_trie t.
  Proof.
    intros * Hl; unfold fc_loc in Hl; canon_open; rewrite (fgc_loc_ok _ _ Huf HcR _ _ HcΞ) in Hl.
    destruct (gc_loc _ _ p) as [[T0 Φ] |] eqn:E; [| discriminate ]; injection Hl as _ <-.
    exists Φ; split; [ reflexivity | exact (canon_gc_loc _ _ HcR HcΞ _ _ _ E) ].
  Qed.

  (** A stored unit: its trie is canonical. *)
  Lemma fc_unit_canon : forall H T t, fc_unit F H = Some (T, t) -> canon_trie t.
  Proof.
    intros * Hl; unfold fc_unit in Hl; canon_open; rewrite (fgc_unit_ok _ _ Huf _ _ HcΞ) in Hl.
    destruct (gc_unit _ _ H) as [[T0 Φ] |] eqn:E; [| discriminate ]; injection Hl as _ <-.
    exists Φ; split; [ reflexivity | exact (canon_gc_unit _ _ HcR HcΞ _ _ _ E) ].
  Qed.

  (** An entry: canonical *)
  Lemma fc_entry_canon : forall p e, fc_entry F p = Some e -> canon_fentry e.
  Proof.
    intros * He; unfold fc_entry in He; canon_open; rewrite (fgc_entry_ok _ _ Huf HcR _ _ HcΞ) in He.
    destruct (gc_entry _ _ p) as [E |] eqn:E0; [| discriminate ]; injection He as <-.
    exists E; split; [ reflexivity | exact (canon_gc_entry _ _ HcR HcΞ _ _ E0) ].
  Qed.

  (** [gc_loc], with the canonicity of the trie found *)
  Definition gc_loc_cf p :
      { o | gc_loc (fc_deps F) (fc_stack F) p = option_map dec_loc o /\ forall T t, o = Some (T, t) -> canon_trie t } :=
    exist _ (fc_loc F p) (conj (fc_loc_ok F p) (fun T t E => fc_loc_canon p T t E)).

  (** [gc_unit], alike *)
  Definition gc_unit_cf H :
      { o | gc_unit (fc_deps F) (fc_stack F) H = option_map dec_loc o /\ forall T t, o = Some (T, t) -> canon_trie t } :=
    exist _ (fc_unit F H) (conj (fc_unit_ok F H) (fun T t E => fc_unit_canon H T t E)).
End Located.
