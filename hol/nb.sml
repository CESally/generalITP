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

(* Inductive reduce:
  [reduce_Succ:] (reduce (Tpred T0) T0) *)
  (* [ E_Succ      :] !t u     . reduce t u  ==>  reduce (Tpred t)                 T0 *)
(* 
  [~ E_PredZero  :]                             reduce (Tpred T0        )        T0
  [~ E_PredSucc  :] ! nv     . valN nv     ==>  reduce (Tpred (Tsucc nv))        nv
  [~ E_Pred      :] ! nv u   . reduce nv u ==>  reduce (Tpred nv        )       (Tpred u)
    
  [~ E_iszeroZero:]                             reduce (Tis0 T0)                 Ttrue
  [~ E_iszeroSucc:] ! nv     . valN nv     ==>  reduce (Tis0 (Tsucc nv) )        Tfalse
  [~ E_iszero    :] ! nv u   . reduce nv u ==>  reduce (Tis0 nv         )       (Tis0 u)
    
  [~ E_ifTrue    :] ! t e    .                  reduce (Tif Ttrue  t e  )        t
  [~ E_iffalse   :] ! t e    .                  reduce (Tif Tfalse t e  )        e
  [~ E_if        :] ! b c t e. reduce b  c ==>  reduce (Tif b      t e  )       (Tif c t e) *)
(* End *)


Inductive foo:
[foo_A:]
  foo 1 2
End