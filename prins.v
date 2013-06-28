Module ODRL.

Require Import Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Set Implicit Arguments .

Inductive nonemptylist (X: Set): Set :=
  | Single : X -> nonemptylist X
  | NewList : X -> nonemptylist X -> nonemptylist X.

Notation "x , l" := (NewList x l) (at level 60, right associativity).
Notation "[ x ]" := (Single x).

Definition subject := nat.

(* simplified *)
Definition prin := nonemptylist subject.

Definition act := nat.
Definition Play:act := 1.
Definition Print:act := 2.
Definition Display:act := 3.

Definition asset := nat.
Definition FindingNemo := 1.
Definition Alien := 2.
Definition Beatles := 3.
Definition LoveAndPeace := 4.

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
  | AndPrqs : nonemptylist (preRequisite) -> preRequisite
  | OrPrqs : nonemptylist (preRequisite) -> preRequisite
  | XorPrqs : nonemptylist (preRequisite) -> preRequisite.

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

End ODRL.
