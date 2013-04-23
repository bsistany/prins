Module ODRL.

Require Import Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Set Implicit Arguments .



Definition l23 : list nat
  := 2 :: 3 :: nil.

Locate pair.

(*
Inductive triple M := Triple : M -> M -> M -> triple M. 
Notation "[ x , y , z ]" := (Triple x y z). 
Definition triple1 := [1,2,3].
*)

(*
Inductive C : sort := 

| c1 : C1           c1 is the constructor, and C1 is the type of the c1
| ...
| cn : Cn.

Naming convention: Constructors start with Capital letter, types with lower case.

where name is the name of the type to be defined; sort is one of Set or Type(or even Prop); ci are the names of the constructors and Ci is the type of theconstructor ci.The declaration of an inductive definition introduces new primitive objectsfor the type itself and its constructors; it also generates theorems which areabbreviations for more complex terms expressing that name is the smallest setcontaining the terms build with constructors. These theorems provide inductionprinciples to reason on objects in inductive types.
*)

Inductive nonemptylist : Set :=
  | Single : nat -> nonemptylist
  | NewList : nat -> nonemptylist -> nonemptylist.

Definition ne2 := Single 2.
Definition ne3 := NewList 3 ne2.
Definition ne4 := NewList 4 (NewList 8 (Single 8)).

Notation "x , l" := (NewList x l) (at level 60, right associativity).
Notation "[ x ]" := (Single x).

Definition mylist2 := 1 , 2 , [3].



Inductive prin : Set :=
  | Prin : nat -> prin 
  | Prins : nonemptylist -> prin. 

Definition myprins := Prins (2 , 3 , [5]).
Definition myprins1 := Prin 5.

(*
Inductive act : Set :=
  | Play : act
  | Print : act
  | Display : act.
*)
Definition act := nat.
Definition Play := 1.
Definition Print := 2.
Definition Display := 3.

(*
Inductive asset : Set :=
  | FindingNemo : asset
  | Alien : asset
  | Beatles : asset
  | LoveAndPeace : asset.
*)
Definition asset := nat.
Definition FindingNemo := 1.
Definition Alien := 2.
Definition Beatles := 3.
Definition LoveAndPeace := 4.



Inductive subject (X:Set) : Set :=
  | Subject : X -> subject X.

(*
Inductive money : Set :=
  | Money : nat -> money.
*)
Definition money := nat.
Definition m1 := 3.


Inductive requirement : Set :=
  | PrePay : money -> requirement
  | Attribution : subject nat -> requirement
  | InSequence : list requirement -> requirement
  | AnySequence : list requirement -> requirement.

(* Mutually recursive types:
Inductive A: Set :=
 | A1
 | A2 (x: B)

with B: Set :=
 | B1
 | B2 (x: A).
*)

Inductive constraint : Set :=
  | Principal : prin  -> constraint 
  | ForEachMember : prin  -> list (constraint ) -> constraint 
  | Count : nat -> constraint .

Inductive policyId : Set :=
  | PolicyId : nat -> policyId.
  
Inductive preRequisite : Set :=
  | Constraint : constraint -> preRequisite 
  | Requirement : requirement -> preRequisite 
  | Condition : cond -> preRequisite 

with cond : Set :=
  | SuspendPS : policySet -> cond
  | SuspendConstrint : constraint -> cond

with policySet : Set :=
  | PrimitivePolicySet : list (preRequisite) -> policy -> policySet 
  | PrimitiveExclusivePolicySet : list (preRequisite) -> policy  -> policySet 
  | AndPolicySet : list (policySet) -> policySet 
  | OrPolicySet : list (policySet) -> policySet 
  | XorPolicySet : list (policySet) -> policySet 

with policy : Set :=
  | PrimitivePolicy : list (preRequisite) -> policyId -> act -> policy 
  | AndPolicy : list (policy) -> policy 
  | OrPolicy : list (policy ) -> policy
  | XorPolicy : list (policy ) -> policy.



Inductive agreement : Set :=
  | Agreement : prin -> prin -> asset -> policySet -> agreement.

Definition const1 := Count 5.
Definition preReq1 := Constraint const1.
Definition policyId1 := PolicyId 12.
Definition act1 := Print.
Check preReq1.
Check PrimitivePolicy.
Check (Constraint (Count 5)).

Definition lis2 := (Constraint (Count 5)) :: nil.
Check lis2.

(*  
preReq1 : preRequisite nat
PrimitivePolicy : forall X : Type, list (preRequisite X) -> policyId -> act -> policy X 
Constraint : forall X : Type, constraint X -> preRequisite X
*)
Definition p1 := PrimitivePolicy lis2 policyId1 act1.

Check length.
Print length.

Definition makePrimitivePolicy (prqs : list (preRequisite)) (id : policyId) (ac : act) : policy :=
  PrimitivePolicy prqs id ac.
  

Definition p2 := makePrimitivePolicy ((Constraint (Count 7)) :: nil) (PolicyId 22) Print.

Definition p3 := makePrimitivePolicy ((Constraint (Count 8)) :: nil) (PolicyId 23) Display.

Inductive user : Set :=
  | Alice : user
  | Bob : user
  | Charlie : user
  | David : user
  | Alex : user.


 
End ODRL.




  


























