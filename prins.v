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

Section MyPair.
  Variable X : Set.
  Variable Y : Set.

  Record Twos : Set := 
  mkTwos 
  {
    left    : X;
    right   : Y
  }.
End MyPair.

Definition half := (mkTwos 2 5).

Eval compute in (left half).
Check half.
Check Twos.

Section Process_Lists.

Variable X : Set.
Variable Y : Set.
Variable Z : Set.


Fixpoint process_two_lists (l1 : nonemptylist X) (l2 : nonemptylist Y) :  nonemptylist (Twos X Y) := 

let process_element_list := (fix process_element_list (e1 : X) (l2 : nonemptylist Y) :  nonemptylist (Twos X Y) :=
  match l2 with
    | Single s => Single (mkTwos e1 s)
    | NewList s rest => app_nonempty (Single (mkTwos e1 s)) (process_element_list e1 rest) 
  end) in

  match l1 with
    | Single s => process_element_list s l2 
    | NewList s rest => app_nonempty (process_element_list s l2) (process_two_lists rest l2) 
  end.


  

End Process_Lists.

Definition lst1 := process_two_lists (NewList 4 (NewList 8 (Single 8))) (NewList 3 (NewList 2 (Single 1))).
Eval compute in lst1.



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


Definition getIds (p:policy) : nonemptylist policyId := Single 2.

(*
subjects(s) => {s}
subjects({prin1, . . . , prink}) => subjects(prin1) + ... + subjects(prink)
*)


Definition getCount (s:subject) (id: policyId) : nat :=
2.


Fixpoint trans_count 
  (x:subject)(n:nat)(IDs:nonemptylist policyId)
  (prin_u:prin)(a:asset) : Prop := 


  let trans_count_aux 
    := (fix trans_count_aux
         (ids_and_subjects : nonemptylist (Twos policyId subject)) : nat :=
     match ids_and_subjects with
        | Single pair1 => getCount (right pair1) (left pair1)
        | NewList pair1 rest_pairs =>
            (getCount (right pair1)(left pair1)) +
            (trans_count_aux rest_pairs)
      end) in
  
  let ids_and_subjects := process_two_lists IDs prin_u in
  let running_total := trans_count_aux ids_and_subjects in
  running_total < n.

Fixpoint trans_constraint 
  (x:subject)(const:constraint)(IDs:nonemptylist policyId)
  (prin_u:prin)(a:asset){struct const} : Prop := 
  match const with
    | Principal prn => trans_prin x prn

    | ForEachMember prn const_list => True (*trans_forEachMember x (getPrincipals prn) const_list IDs a*)
  
    | Count n => trans_count x n IDs prin_u a

    | CountByPrin prn n => True

  end.


Definition trans_preRequisite
  (x:subject)(prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin)(a:asset) : Prop := 
  match prq with
    | TruePrq => True
    | Constraint const => trans_constraint x const IDs prin_u a 
    | Requirement req => True (*trans_requirment x prq IDs prin_u a*)
    | NotCons const => True (*trans_notCons x const IDs prin_u a*)
    | AndPrqs prqs => True (*trans_andPrqs x prq IDs prin_u a*)
    | OrPrqs prqs => True (*trans_orPrqs x prq IDs prin_u a*)
    | XorPrqs prqs => True (*trans_xorPrqs x prq IDs prin_u a*)
  end.

Fixpoint trans_policy_positive
  (x:subject)(p:policy)(prin_u:prin)(a:asset){struct p} : Prop :=

let trans_p_list := (fix trans_p_list (x:subject)(p_list:nonemptylist policy)(prin_u:prin)(a:asset){struct p_list}:=
                  match p_list with
                    | Single p1 => trans_policy_positive x p1 prin_u a
                    | NewList p p_list' => ((trans_policy_positive x p prin_u a) /\ (trans_p_list x p_list' prin_u a))
                  end) in


  match p with
    | PrimitivePolicy prq policyId action => ((trans_preRequisite x prq (Single policyId) prin_u a) ->
                                              (Permitted x action a))
    | AndPolicy p_list => trans_p_list x p_list prin_u a
  end.

Fixpoint trans_policy_negative
  (x:subject)(p:policy)(a:asset){struct p} : Prop :=
let trans_p_list := (fix trans_p_list (x:subject)(p_list:nonemptylist policy)(a:asset){struct p_list}:=
                  match p_list with
                    | Single p1 => trans_policy_negative x p1 a
                    | NewList p p_list' => ((trans_policy_negative x p a) /\ (trans_p_list x p_list' a))
                  end) in


  match p with
    | PrimitivePolicy prq policyId action => not (Permitted x action a)
    | AndPolicy p_list => trans_p_list x p_list a
  end.



Fixpoint trans_ps
  (x:subject)(ps:policySet)(prin_u:prin)(a:asset){struct ps} : Prop :=

let trans_ps_list := (fix trans_ps_list (x:subject)(ps_list:nonemptylist policySet)(prin_u:prin)(a:asset){struct ps_list}:=
                  match ps_list with
                    | Single ps1 => trans_ps x ps1 prin_u a
                    | NewList ps ps_list' => ((trans_ps x ps prin_u a) /\ (trans_ps_list x ps_list' prin_u a))
                  end) in
  match ps with
    | PrimitivePolicySet prq p => ((trans_prin x prin_u) /\ 
                                   (trans_preRequisite x prq (getIds p) prin_u a)) -> 
                                   (trans_policy_positive x p prin_u a)

    | PrimitiveExclusivePolicySet prq p => ((((trans_prin x prin_u) /\ 
                                              (trans_preRequisite x prq (getIds p) prin_u a)) -> 
                                             (trans_policy_positive x p prin_u a)) /\

                                            ((not (trans_prin x prin_u)) -> (trans_policy_negative x p a)))
                   
    | AndPolicySet ps_list => trans_ps_list x ps_list prin_u a
  end.




End ODRL.
