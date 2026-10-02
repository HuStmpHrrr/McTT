(** Extraction helpers in a (pseudo-)monadic style. *)
From Stdlib Require Extraction.

(** These definitions cannot be generalized with type classes, as Rocq does
    not support extractable polymorphism across [Prop] and [Set]
    (#<a href="https://github.com/coq/coq/issues/19452">coq/coq#19452</a>#). *)

Definition sumbool_failable_bind {A B} (ab : {A} + {B}) {C D : Prop} (fail : B -> D) (next : A -> {C} + {D}) :=
  match ab with
  | left a => next a
  | right b => right (fail b)
  end.
Transparent sumbool_failable_bind.
Arguments sumbool_failable_bind /.

Notation "'let*b' a ':=' ab 'while' fail 'in' next" := (sumbool_failable_bind ab fail (fun a => next)) (at level 200, a pattern, next at level 200, right associativity, only parsing).
Notation "'pureb' a" := (left a) (at level 10, a at next level, only parsing).

Definition sumor_failable_bind {A B} (ab : A + {B}) {C} {D : Prop} (fail : B -> D) (next : A -> C + {D}) :=
  match ab with
  | inleft a => next a
  | inright b => inright (fail b)
  end.
Transparent sumor_failable_bind.
Arguments sumor_failable_bind /.

Notation "'let*o' a ':=' ab 'while' fail 'in' next" := (sumor_failable_bind ab fail (fun a => next)) (at level 200, a pattern, next at level 200, right associativity, only parsing).
Notation "'pureo' a" := (inleft a) (at level 10, a at next level, only parsing).

Definition sumbool_sumor_failable_bind {A B} (ab : {A} + {B}) {C} {D : Prop} (fail : B -> D) (next : A -> C + {D}) :=
  match ab with
  | left a => next a
  | right b => inright (fail b)
  end.
Transparent sumbool_sumor_failable_bind.
Arguments sumbool_sumor_failable_bind /.

Notation "'let*b->o' a ':=' ab 'while' fail 'in' next" := (sumbool_sumor_failable_bind ab fail (fun a => next)) (at level 200, a pattern, next at level 200, right associativity, only parsing).

Definition sumor_sumbool_failable_bind {A B} (ab : A + {B}) {C} {D : Prop} (fail : B -> D) (next : A -> {C} + {D}) :=
  match ab with
  | inleft a => next a
  | inright b => right (fail b)
  end.
Transparent sumor_sumbool_failable_bind.
Arguments sumor_sumbool_failable_bind /.

Notation "'let*o->b' a ':=' ab 'while' fail 'in' next" := (sumor_sumbool_failable_bind ab fail (fun a => next)) (at level 200, a pattern, next at level 200, right associativity, only parsing).

Extraction Inline sumbool_failable_bind sumor_failable_bind sumbool_sumor_failable_bind sumor_sumbool_failable_bind.
