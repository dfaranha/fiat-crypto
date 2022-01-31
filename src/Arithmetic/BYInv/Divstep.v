Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Local Open Scope Z_scope.

Definition divstep_spec d f g :=
  if (0 <? d) && Z.odd g
  then (1 - d, g, (g - f) / 2)
  else (1 + d, f, (g + (g mod 2) * f) / 2 ).

Definition divstep_spec2 m d g v r :=
  if (0 <? d) && Z.odd g
  then (2 * r mod m, (r - v) mod m)
  else (2 * v mod m, (r + (g mod 2) * v) mod m).

Definition divstep_spec_full m d f g v r :=
  if (0 <? d) && Z.odd g
  then (1 - d, g, (g - f) / 2, 2 * r mod m, (r - v) mod m)
  else (1 + d, f, (g + (g mod 2) * f) / 2, 2 * v mod m, (r + (g mod 2) * v) mod m).

Definition divstep_spec_full' d f g u v q r :=
  if (0 <? d) && Z.odd g
  then (1 - d, g, (g - f) / 2,
        2 * q, 2 * r, q - u, r - v)
  else (1 + d, f, (g + (g mod 2) * f) / 2,
        2 * u, 2 * v, q + (g mod 2) * u, r + (g mod 2) * v).

Fixpoint divstep_spec_full'_iter d f g u v q r n :=
  match n with
  | 0%nat => (d, f, g, u, v, q, r)
  | S n => let '(d, f, g, u, v, q, r) := divstep_spec_full'_iter d f g u v q r n in divstep_spec_full' d f g u v q r
  end.

Fixpoint divstep_full_iter m d f g v r n :=
  match n with
  | 0%nat => (d, f, g, v, r)
  | S n => let '(d, f, g, v, r) := divstep_full_iter m d f g v r n in divstep_spec_full m d f g v r
  end.
