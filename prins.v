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




Inductive prin (X:Set) : Set :=
  | Prin : X -> prin X
  | Prins : list X -> prin X. 

Definition myprins := Prins (2 :: 3 :: nil).
Definition myprins1 := Prin 5.


Inductive act : Set :=
  | Play : act
  | Print : act
  | Display : act.

(*
Inductive asset : Set :=
  | FindingNemo : asset
  | Alien : asset
  | Beatles : asset
  | LoveAndPeace : asset.
*)

Definition findingNemo := 1.
Definition alien := 2.
Definition beatles := 3.
Definition LoveAndPeace := 4.



Inductive subject (X:Set) : Set :=
  | Subject : X -> subject X.

Inductive money : Set :=
  | Money : nat -> money.

Definition m1 := Money 3.


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

Inductive constraint (X:Set) : Set :=
  | Principal : prin X -> constraint X
  | ForEachMember : prin X -> list (constraint X) -> constraint X
  | Count : nat -> constraint X.

Inductive policyId : Set :=
  | PolicyId : nat -> policyId.
  
Inductive preRequisite (X:Set) : Set :=
  | Constraint : constraint X -> preRequisite X
  | Requirement : requirement -> preRequisite X
  | Condition : cond X -> preRequisite X

with cond (X:Set) : Set :=
  | SuspendPS : policySet X -> cond X
  | SuspendConstrint : constraint X -> cond X

with policySet (X:Set) : Set :=
  | PrimitivePolicySet : list (preRequisite X) -> policy X -> policySet X
  | PrimitiveExclusivePolicySet : list (preRequisite X) -> policy X -> policySet X
  | AndPolicySet : list (policySet X) -> policySet X
  | OrPolicySet : list (policySet X) -> policySet X
  | XorPolicySet : list (policySet X) -> policySet X

with policy (X:Set) : Set :=
  | PrimitivePolicy : list (preRequisite X) -> policyId -> act -> policy X
  | AndPolicy : list (policy X) -> policy X
  | OrPolicy : list (policy X) -> policy X
  | XorPolicy : list (policy X) -> policy X.

Inductive agreement (X:Set) : Set :=
  | Agreement : prin X -> prin X -> asset -> policySet X -> agreement X.

Definition const1 := Count nat 5.
Definition preReq1 := Constraint const1.
Definition policyId1 := PolicyId 12.
Definition act1 := Print.
Check preReq1.
Check PrimitivePolicy.
Check (Constraint (Count nat 5)).

Definition lis2 := (Constraint (Count nat 5)) :: nil.
Check lis2.

(*  
preReq1 : preRequisite nat
PrimitivePolicy : forall X : Type, list (preRequisite X) -> policyId -> act -> policy X 
Constraint : forall X : Type, constraint X -> preRequisite X
*)
Definition p1 := PrimitivePolicy lis2 policyId1 act1.

Check length.
Print length.

Definition makePrimitivePolicy (X:Set) (prqs : list (preRequisite X)) (id : policyId) (ac : act) : policy X :=
  PrimitivePolicy prqs id ac.
  

Definition p2 := makePrimitivePolicy ((Constraint (Count nat 7)) :: nil) (PolicyId 22) Print.

Definition p3 := makePrimitivePolicy ((Constraint (Count nat 8)) :: nil) (PolicyId 23) Display.

Inductive user : Set :=
  | Alice : user
  | Bob : user
  | Charlie : user
  | David : user
  | Alex : user.


 
End ODRL.




  


























