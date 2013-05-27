
Require Import Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Set Implicit Arguments .



Check 1::2::3::nil.

Eval compute in (1::2::3::nil) ++ (4::5::nil).

Eval compute in length (1::2::nil).

Eval compute in map (fun x => x + 1) (1::2::3::nil).

Eval compute in
fold_right (fun x y => x + y) 0 (1::2::3::nil).


Definition ss :=
fold_right (fun x y => x /\ y) True (True::True::True::nil).

Eval compute in ss.

Check true.
Check andb.
Eval compute in
fold_right (fun x y => (andb x y)) false (true::nil).

Inductive nonemptylist (X: Set): Set :=
  | Single : X -> nonemptylist X
  | NewList : X -> nonemptylist X -> nonemptylist X.

Check andb.
Definition ne2 := Single 2.

Check Single 2.

(*
Section Process_Lists.

Variable combiner : nat -> nat -> nat.
*)

Fixpoint process_two_lists (l1 l2 : nonemptylist nat) (combiner : nat -> nat -> nat) {struct l1}:  nonemptylist nat := 

let process_element_list := (fix process_element_list (e1 : nat) (l2 : nonemptylist nat) 
                                                      (combiner : nat -> nat -> nat) {struct l2}:  nonemptylist nat := 
  match l2 with
    | Single s => Single (combiner e1 s)
    | NewList s rest => process_two_lists (Single (combiner e1 s)) (process_element_list e1 rest combiner) combiner
  end) in
  

  match l1 with
    | Single s => process_element_list s l2 combiner
    | NewList s rest => process_two_lists (process_element_list s l2 combiner) (process_two_lists rest l2 combiner) combiner
  end.
(*
End Process_Lists.
*)