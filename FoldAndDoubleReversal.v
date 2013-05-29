
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

Section nonemptylist.

Variable X : Set.

Inductive nonemptylist : Set :=
  | Single : X -> nonemptylist 
  | NewList : X -> nonemptylist -> nonemptylist.


Fixpoint app_nonempty (l1 l2 : nonemptylist) : nonemptylist := 
  match l1 with
  | Single s  => NewList s l2
  | NewList s rest => NewList s (app_nonempty rest l2)
  end.

End nonemptylist.

Section Fold_Nonempty.
  Variables A B : Set.
  Variable f : B -> A -> A.
  Variable a0 : A.

  Fixpoint fold_nonempty (l:nonemptylist B) : A :=
    match l with
      | Single s => f s a0
      | NewList s rest => f s (fold_nonempty rest)
    end.

End Fold_Nonempty.

Check andb.
Definition ne2 := Single 2.

Check Single 2.

Check app.

Section Process_Lists.

Variable X : Set.
Variable Y : Set.
Variable Z : Set.
Variable combiner : X -> Y -> Z.


Fixpoint process_two_lists (l1 : nonemptylist X) (l2 : nonemptylist Y) :  nonemptylist Z := 

let process_element_list := (fix process_element_list (e1 : X) (l2 : nonemptylist Y) :  nonemptylist Z :=
  match l2 with
    | Single s => Single (combiner e1 s)
    | NewList s rest => app_nonempty (Single (combiner e1 s)) (process_element_list e1 rest) 
  end) in

  match l1 with
    | Single s => process_element_list s l2 
    | NewList s rest => app_nonempty (process_element_list s l2) (process_two_lists rest l2) 
  end.


  

End Process_Lists.

Definition lst1 := process_two_lists (fun x y => x + y)(NewList 4 (NewList 8 (Single 8))) (NewList 3 (NewList 2 (Single 1))).
Eval compute in lst1.

Eval compute in
fold_nonempty (fun x y => x + y) 0 lst1.

Definition lst2 := process_two_lists (fun x y => (x::y::nil)) (NewList 91 (Single 92)) (NewList 3 (NewList 2 (Single 1))).
Eval compute in lst2.