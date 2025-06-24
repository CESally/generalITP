hide "K"; hide "S";

Datatype: cl = K | S | # cl cl
End

set_fixity "#" (Infixl 1100);

set_mapped_fixity {fixity = Infix(NONASSOC, 450),
tok = "-->", term_name = "redn"};

Inductive redn:
[A:] !x y f .   x --> y ==>     f # x           -->   f # y
[B:] !f g x .   f --> g ==>     f # x           -->   g # x
[C:] !x y   .                   K # x # y       -->   x
[D:] !f g x .                   S # f # g # x   -->   (f # x) # (g # x)
End

(* PROVE [redn_rules] ``S # (K # x # x) --> S # x``; *)

val _ = hide "RTC";

Inductive RTC:
[~refl:] !x     .                        RTC R x x
[~trns:] !x y z . R x y /\ RTC R y z ==> RTC R x z
End

Definition confluent_def:
  confluent R =
    !x y z. RTC R x y /\ RTC R x z ==>
    ?u. RTC R y u /\ RTC R z u
End

Definition normal_def: normal R x = !y. ~R x y
End

Theorem confluent_normforms_unique:
  !R. confluent R ==>
  !x y z.
  RTC R x y /\ normal R y /\
  RTC R x z /\ normal R z ==> (y = z)
Proof
  rw[confluent_def] >>
  `?u. RTC R y u /\ RTC R z u` by metis_tac [] >>
  metis_tac [normal_def, RTC_cases]
QED

val _ = hide "diamond";

Definition diamond_def:
  diamond R = !x y z. R x y /\ R x z ==> ?u. R y u /\ R z u
End

Theorem confluent_diamond_RTC:
  !R. confluent R = diamond (RTC R)
Proof rw[confluent_def, diamond_def]
QED

g `

!R. diamond R ==>
!x p z. RTC R x p /\ R x z ==>
?u. RTC R p u /\ RTC R z u

`;
e (strip_tac>> strip_tac);