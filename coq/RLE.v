From Stdlib Require Import List Lia.
Import ListNotations.

Fixpoint revApp {X:Type} (xs ys: list X) := match xs with
  | x :: xs => revApp xs (x::ys)
  | []      => ys
  end.

  (* In revApp <-> In (xs ++ ys) *)


Definition rev {X:Type} (xs: list X) := revApp xs [].

Fixpoint pack {X:Type} (test: X -> bool) (acc xs: list X) := match xs with
  | y :: ys => if test y then pack test (y::acc) ys else (rev acc, xs)
  | []      => (rev acc, [])
  end.

Theorem pack_shortens_list : forall {X} test (acc xs accN xsN: list X),
    pack test acc xs = (accN, xsN) ->
  length xsN <= length xs.
Proof with solve [auto|simpl;lia]. intros.
  induction xs as [| x xss IH] in acc, accN, xsN, H |- *;
  [ inversion H; subst
  | simpl in *; destruct (test x);
    [ apply IH in H
    | inversion H; subst]]...
Qed.

Theorem foo : forall {X} x (xs: list X), length xs < length (x::xs).
Proof ltac:(simpl; lia). 


(* Function findDups {X} (eqG : X -> X -> bool) (acc: list (list X)) (xs: list X) := match xs with
  | [] => acc
  | x :: y :: ys => if eqG x y
      then let (packed,xsLeft) := pack (eqG x) [] xs in findDups eqG (packed::acc) xsLeft _
      else findDups eqG ([x]::acc) (y::ys) _
  | x :: ys => findDups eqG ([x]::acc) ys (Acc_inv ACC (foo x ys))
  end. *)

Fixpoint findDups {X} (eqG : X -> X -> bool) (acc: list (list X)) (xs: list X)
          (ACC: Acc lt (length xs)) {struct ACC} := match xs with
  | [] => acc
  | x :: y :: ys => if eqG x y
      then let (packed,xsLeft) := pack (eqG x) [] xs in findDups eqG (packed::acc) xsLeft _
      else findDups eqG ([x]::acc) (y::ys) _
  | x :: ys => findDups eqG ([x]::acc) ys (Acc_inv ACC (foo x ys))
  end.




Module Type RLE.

  Parameters t res : Type.
  Parameters collection : Type -> Type.
  Parameters init : res.
  Parameters single : t -> res -> res.
  Parameters multip : res -> (t -> bool) -> collection t -> (res, collection t).
  Parameters test : t -> t -> bool.
End RLE.

Module rleGen (Import X : RLE).

  Fixpoint findDups acc xs := match xs with
    | [] => acc
    | x::y::_ => if test x y then multiple

  Definition rle = 

    
rleGen ::
  res                                      ->
  (a -> res -> res)                        ->
  (res -> (a -> Bool) -> [a] -> (res,[a])) ->
  (a -> a -> Bool)                         ->
  [a] -> res
rleGen init singleton multiple eqG = findDups init where
  findDups res []                   = res
  findDups acc xs@(x:y:_) | eqG x y = findDups accN xsN where (accN,xsN) = multiple acc (eqG x) xs
  findDups acc (x:xs)               = findDups (singleton x acc) xs



rle :: Eq a => [a] -> [[a]]
rle = findDups [] where
-----------------------------------------------------------------------------------------------------------------------
  findDups :: Eq a => [[a]] -> [a] -> [[a]]
  findDups acc [] = rev acc
  findDups acc (x:y:xs) | x == y = findDups (packed:acc) xsLeft where (packed,xsLeft) = pack (x ==) [y,x] xs
  findDups acc (x:xs) = findDups ([x]:acc) xs
  ---------------------------------------------------------------------------------------------------------------------
  pack test acc (x:xs) | test x = pack test (x:acc) xs
  pack _    acc    xs           = (rev acc, xs)