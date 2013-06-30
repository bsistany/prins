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

where name is the name of the type to be defined; sort is one of Set or Type
(or even Prop); ci are the names of the constructors and Ci is the type of the
constructor ci.
The declaration of an inductive definition introduces new primitive objects
for the type itself and its constructors; it also generates theorems which are
abbreviations for more complex terms expressing that name is the smallest set
containing the terms build with constructors. These theorems provide induction
principles to reason on objects in inductive types.
*)


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

Definition ne2 := Single 2.
Definition ne3 := NewList 3 ne2.
Definition ne4 := NewList 4 (NewList 8 (Single 8)).

Notation "x , l" := (NewList x l) (at level 60, right associativity).
Notation "[ x ]" := (Single x).

Definition subject := nat.

(* simplified *)
Definition prin := nonemptylist subject.

Definition act := nat.
Definition Play : act := 1.
Definition Print : act := 2.
Definition Display : act := 3.

Definition asset := nat.
Definition FindingNemo : asset := 1.
Definition Alien : asset := 2.
Definition Beatles : asset := 3.
Definition LoveAndPeace : asset := 4.

Definition money := nat.

Definition policyId := nat.

Inductive requirement : Set :=
  | PrePay : money -> requirement
  | Attribution : subject -> requirement
  | InSequence : nonemptylist requirement -> requirement
  | AnySequence : nonemptylist requirement -> requirement.

Inductive constraint : Set :=
  | Principal : prin  -> constraint 
  | ForEachMember : prin  -> nonemptylist constraint -> constraint 
  | Count : nat -> constraint 
  | CountByPrin : prin -> nat -> constraint.

(* taking out Condition, replacing with NotCons *)
Inductive preRequisite : Set :=
  | TruePrq : preRequisite
  | Constraint : constraint -> preRequisite 
  | Requirement : requirement -> preRequisite 
  | NotCons : constraint -> preRequisite 
  | AndPrqs : nonemptylist preRequisite -> preRequisite
  | OrPrqs : nonemptylist preRequisite -> preRequisite
  | XorPrqs : nonemptylist preRequisite -> preRequisite.

Check nonemptylist requirement.
Check nonemptylist (requirement).

Inductive policy : Set :=
  | PrimitivePolicy : preRequisite -> policyId -> act -> policy 
  | AndPolicy : nonemptylist policy -> policy.

Inductive policySet : Set :=
  | PrimitivePolicySet : preRequisite -> policy -> policySet 
  | PrimitiveExclusivePolicySet : preRequisite -> policy  -> policySet 
  | AndPolicySet : nonemptylist policySet -> policySet.

Inductive agreement : Set :=
  | Agreement : prin -> asset -> policySet -> agreement.

(* Example 2.1 *)
Definition Alice:subject := 1.
Definition Bob:subject := 2.

Definition TheReport:asset := 5.

Definition p1A1:policySet :=
  PrimitivePolicySet
    TruePrq
    (PrimitivePolicy (Constraint (Count  5)) 1 Print).

Definition p2A1prq1:preRequisite := (Constraint (Principal (Single Alice))).
Definition p2A1prq2:preRequisite := (Constraint (Count 2)).

Definition p2A1:policySet :=
  PrimitivePolicySet
    TruePrq
    (PrimitivePolicy (AndPrqs (NewList p2A1prq1 (Single p2A1prq2))) 2 Print).

Definition A1 := Agreement (NewList Alice (Single Bob)) TheReport
                  (AndPolicySet (NewList p1A1 (Single p2A1))).

(******* Semantics ********)

Parameter Permitted : subject -> act -> asset -> Prop.

(* is x in prin? *)
(** Definition prin := nonemptylist subject. **)
Fixpoint trans_prin
  (x: subject)(p: prin) : Prop :=

  match p with
    | Single s => (x=s)
    | NewList s rest => ((x=s) \/ trans_prin x rest)
  end.



End ODRL.
