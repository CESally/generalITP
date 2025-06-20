(* load "intLib"; *)

Datatype: term
  = Ttrue
  | Tfalse
  | T0
  | Tsucc term
  | Tif term term term
  | Tpred term
  | Tis0 term
End

(* Definition ONE_def: ONE(out:num->bool) = !t. out t = T
End *)

(* Definition valN_def: valN(t:term -> bool) =  what is this notation?
  (valN T0 = T) /\
  (valN (Tsucc t) = valN t) /\
  (valN _ = F)
End *)

Definition valN_def:
  (valN T0 = T) /\
  (valN (Tsucc t) = valN t) /\
  (valN _ = F)
End

Definition val_def:
  (val Ttrue  = T) /\
  (val Tfalse = T) /\
  (val t = valN t)
End



(* EVAL ``valN T0`` gives ⊢ valN T0 ⇔ T: thm (* shouldn't this be a bool??? *) *)
(* so... what is valN_def? just a name? *)
(* this defines a function valN right? is it a function from term to bool? *)
(* that's what the type_of ``valN`` tells me *)

Definition const_def:
  (const (Tsucc t  ) = const t) /\
  (const (Tpred t  ) = const t) /\
  (const (Tis0  t  ) = const t) /\
  (const (Tif b t e) = const b ++ const t ++ const e) /\
  (const t = [t])
End

Definition max_def: (* working example of an num->num *)
  max x y = if x < y then y else x
End

Definition maxlAux_def:
  (maxlAux res [     ] = res) /\
  (maxlAux res (x::xs) = maxlAux (max res x) xs)
End

Definition maxl_def:
  maxl xs = maxlAux 0 xs
End

Definition depth_def:
  (depth Ttrue  = 1) /\
  (depth Tfalse = 1) /\
  (depth T0     = 1) /\
  (depth (Tsucc t) = 1 + depth t) /\
  (depth (Tpred t) = 1 + depth t) /\
  (depth (Tis0  t) = 1 + depth t) /\
  (depth (Tif b t e) = 1 + maxl [depth b; depth t; depth e])
End

Definition size_def:
  (size Ttrue  = 1) /\
  (size Tfalse = 1) /\
  (size T0     = 1) /\
  (size (Tsucc t) = 1 + size t) /\
  (size (Tpred t) = 1 + size t) /\
  (size (Tis0  t) = 1 + size t) /\
  (size (Tif b t e) = 1 + size b + size t + size e)
End

Definition reduces_def:

  (reduces (Tsucc t)            (Tsucc u)   = reduces t u                 ) /\

  (reduces (Tpred t)             T0         = T                           ) /\
  (reduces (Tpred (Tsucc t))     u          = (valN t) and (t == u)            ) 
(* 
  (reduces (Tpred t)            (Tpred u)   = reduces t u && not (valN t) ) /\

  (reduces (Tis0 t)              T0         = T                           ) /\
  (reduces (Tis0  (Tsucc t))     Tfalse     = valN t                      ) /\
  (reduces (Tis0 t)             (Tis0  u)   = reduces t u && not (valN t) ) /\

  (reduces (Tif Ttrue  t _)      u          = t == u                      ) /\
  (reduces (Tif Tfalse _ e)      u          = e == u                      ) /\
  (reduces (Tif b      t e)     (Tif c t e) = e == u                      ) /\

  (reduces _ _  = F) *)
End
