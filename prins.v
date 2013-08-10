Module ODRL.

Require Import Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.Ascii.
Set Implicit Arguments.

Open Scope string_scope.



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

Fixpoint length_nonempty (l1 : nonemptylist) : nat := 
  match l1 with
  | Single s  => 1
  | NewList s rest => 1 + (length_nonempty rest)
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



Definition subject := string.

(* simplified *)
Definition prin := nonemptylist subject.

Definition act := string.
Definition Play : act := "Play".
Definition Print : act := "Print".
Definition Display : act := "Display".

Definition asset := string.
Definition FindingNemo : asset := "FindingNemo".
Definition Alien : asset := "Alien".
Definition Beatles : asset := "Beatles".
Definition LoveAndPeace : asset := "LoveAndPeace".

Definition money := string.

Definition policyId := string.

Section times.

Definition time := nat.

Inductive timeprod : Set :=
  | Timepair : time -> time -> timeprod.

Definition rangestart (p : timeprod) : time := 
  match p with
  | Timepair x y => x
  end.
Definition rangeend (p : timeprod) : time := 
  match p with
  | Timepair x y => y
  end.

Definition inRange (t: time) (p : timeprod) : Prop := 
  ((rangestart p) <= t) /\ (t <= (rangeend p)).

Definition MAX_TIME : time := 99. (* Hack for now *)

End times.



Eval simpl in (Timepair 2 5). 

Eval simpl in (inRange 2 (Timepair 2 5)).

Inductive requirement : Set :=
  | PrePay : money -> timeprod -> requirement
  | Attribution : subject -> timeprod -> requirement.
(* Moved out to prereq level
  | InSequence : nonemptylist requirement -> timeprod -> requirement
  | AnySequence : nonemptylist requirement -> timeprod -> requirement.
*)
Inductive constraint : Set :=
  | Principal : prin  -> constraint 
  (*| ForEachMember : prin  -> nonemptylist constraint -> constraint *)
  | Count : nat -> constraint 
  | CountByPrin : prin -> nat -> constraint.

(* taking out Condition, replacing with NotCons *)
Inductive preRequisite : Set :=
  | TruePrq : preRequisite
  | Constraint : constraint -> preRequisite 
  | ForEachMember : prin  -> nonemptylist constraint -> preRequisite
  | Requirement : requirement -> preRequisite 
  | InSequence : nonemptylist requirement -> timeprod -> preRequisite
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
Definition Alice:subject := "Alice".
Definition Bob:subject := "Bob".

Definition TheReport:asset := "TheReport".

Definition p1A1:policySet :=
  PrimitivePolicySet
    TruePrq
    (PrimitivePolicy (Constraint (Count  5)) "id1" Print).

Definition p2A1prq1:preRequisite := (Constraint (Principal (Single Alice))).
Definition p2A1prq2:preRequisite := (Constraint (Count 2)).

Definition p2A1:policySet :=
  PrimitivePolicySet
    TruePrq
    (PrimitivePolicy (AndPrqs (NewList p2A1prq1 (Single p2A1prq2))) "id2" Print).

Definition A1 := Agreement (NewList Alice (Single Bob)) TheReport
                  (AndPolicySet (NewList p1A1 (Single p2A1))).

(* Example 2.5 *)
Definition ebook:asset := "ebook".
Definition tenCount:preRequisite := (Constraint (Count 10)).
Definition fiveCount:constraint := (Count 5).
Definition oneCount:constraint := (Count 1).

Definition prins2_5 := (NewList Alice (Single Bob)).

Check ForEachMember prins2_5 (Single fiveCount).
Definition forEach_display:preRequisite := ForEachMember prins2_5 (Single fiveCount).
Definition forEach_print:preRequisite := ForEachMember prins2_5 (Single oneCount).

Definition primPolicy1:policy := PrimitivePolicy forEach_display "id1" Display.
Definition primPolicy2:policy := PrimitivePolicy forEach_print "id2" Print.

Definition policySet2_5:policySet :=
  PrimitivePolicySet tenCount (AndPolicy (NewList primPolicy1 (Single primPolicy2))).
                     

Definition A2_5 := Agreement prins2_5 ebook policySet2_5.

(*** 2.6 ***)
Definition prins2_6 := prins2_5.
Definition Charlie:subject := "Charlie".
Definition aliceCount10:preRequisite := Constraint (CountByPrin prins2_6 10).
Definition primPolicy2_6:policy := PrimitivePolicy aliceCount10 "id3" Play.

Definition prePay2_6:requirement := PrePay "5.00" (Timepair 0 MAX_TIME).
Definition attrib2_6:requirement := Attribution Charlie (Timepair 0 MAX_TIME).
Definition inSeq2_6_preReq:preRequisite := 
  InSequence (NewList prePay2_6 (Single attrib2_6)) (Timepair 0 MAX_TIME).


Definition policySet2_6:policySet := PrimitiveExclusivePolicySet inSeq2_6_preReq primPolicy2_6.
  

Definition latestJingle:asset := "LatestJingle".
Definition A2_6 := Agreement prins2_6 latestJingle policySet2_6.


(******* Semantics ********)

Section Sems.

   Variable x:subject.


Inductive permitted : subject -> act -> asset -> Prop :=
  | Permitted : forall s a1 a2, permitted s a1 a2.

Inductive paid : money -> nonemptylist policyId -> time -> Prop :=
  | Paid : forall m ids t, paid m ids t.

Inductive attributed : subject -> time -> Prop :=
  | Attributed : forall s t, attributed s t.

(* is x in prin? *)
(** Definition prin := nonemptylist subject. **)
Fixpoint trans_prin
  (p: prin) : Prop :=

  match p with
    | Single s => (x=s)
    | NewList s rest => ((x=s) \/ trans_prin rest)
  end.

  
Fixpoint getId (p:policy) : nonemptylist policyId := 

 let getIds 
    := (fix getIds (policies: nonemptylist policy) : nonemptylist policyId :=
          match policies with
            | Single p => getId p
            | NewList p rest => app_nonempty (getId p) (getIds rest)
          end) in
  
  match p with
    | PrimitivePolicy prereq pid action => Single pid
    | AndPolicy policies => getIds policies
  end.
  
(*
subjects(s) => {s}
subjects({prin1, . . . , prink}) => subjects(prin1) + ... + subjects(prink)
*)



Definition getCount (s:subject) (id: policyId) : nat := 3.




Fixpoint trans_count 
  (n:nat)(IDs:nonemptylist policyId)
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
  (const:constraint)(IDs:nonemptylist policyId)
  (prin_u:prin)(a:asset){struct const} : Prop := 
(*************************************************)
(*************************************************)
  match const with
    | Principal prn => trans_prin prn
  
    | Count n => trans_count n IDs prin_u a

    | CountByPrin prn n => trans_count n IDs prn a

  end.




Fixpoint trans_forEachMember
         (principals: nonemptylist subject)(const_list:nonemptylist constraint)
         (IDs:nonemptylist policyId)(a:asset){struct const_list} : Prop := 

let trans_forEachMember_Aux   
  := (fix trans_forEachMember_Aux
         (prins_and_constraints : nonemptylist (Twos subject constraint))
         (IDs:nonemptylist policyId)(a:asset) {struct prins_and_constraints} : Prop :=

      match prins_and_constraints with
        | Single pair1 => trans_constraint (right pair1) IDs (Single (left pair1)) a
        | NewList pair1 rest_pairs =>
            (trans_constraint (right pair1) IDs (Single (left pair1)) a) /\
            (trans_forEachMember_Aux rest_pairs IDs a)
      end) in

      let prins_and_constraints := process_two_lists principals const_list in
      trans_forEachMember_Aux prins_and_constraints IDs a.


(*************

Parameter Perm : nat -> Prop.


Check (ex Perm). (* gives you exists x, Perm x *)
Definition ff3 : Prop :=
ex Perm.
**************)

(*
Definition trans_prepay2
  (amount:money)(tp:timeprod)(IDs:nonemptylist policyId) : Prop := 
  ex ((inRange tp) /\ (Paid amount IDs)).

*)

Definition trans_prepay
  (amount:money)(t'':time)(tp:timeprod)(IDs:nonemptylist policyId) : Prop :=
  ((inRange t'' tp) /\ (paid amount IDs t'')).
 


Definition trans_attribution
  (s:subject)(t'':time)(tp:timeprod) : Prop := 
  (inRange t'' tp) /\ (attributed s t'').

(*
Definition trans_attribution
  (s:subject)(tp:timeprod) : Prop := 
  exists t'', ((inRange t'' tp) /\ (Attributed s t'')).
*)
(*
Fixpoint separated 
   (t t' len : nat)
   (reqs: nonemptylist requirement)
   (IDs:nonemptylist policyId)(prin_u:prin)(a:asset) : Prop :=

  match len with
    | O => 
         match reqs with          
           | NewList req1 (Single req2) =>           
                exists n, t < n < t' /\ 
                trans_requirment req1 (Timepair t n) IDs prin_u a /\ 
                trans_requirment req2 (Timepair n t') IDs prin_u a
           | _  => error   
        
    | S len' => 
         match reqs with
           | NewList req rest => 
                exists n, t < n /\ 
                trans_requirment req (Timepair t n) IDs prin_u a /\ 
                separated n t' len'
           | _ => error
  end.
  
*)
Fixpoint trans_requirment
  (req:requirement)(tp:timeprod)
  (IDs:nonemptylist policyId)(prin_u:prin)(a:asset){struct req} : Prop := 
(*
let trans_InSequence2 := 
  (fix trans_InSequence2 
      (t t' len: nat)
      (reqs: nonemptylist requirement)
      (IDs:nonemptylist policyId)
      (prin_u:prin)(a:asset){struct len} : Prop := 

  
  match len with
    | O => 
         match reqs with          
           | NewList req10 (Single req2) =>           
                exists n, t < n < t' /\ 
                trans_requirment req10 (Timepair t n) IDs prin_u a /\ 
                trans_requirment req2 (Timepair n t') IDs prin_u a
           | _  => True 
         end   
    | S len' => 
         match reqs with
           | NewList req rest => 
                exists n, t < n /\ 
                trans_requirment req (Timepair t n) IDs prin_u a /\ 
                trans_InSequence2 n t' len' rest IDs prin_u a
           | _ => True
         end
  end) in

*)
(*
let trans_InSequence := 
  (fix trans_InSequence 
      (reqs: nonemptylist requirement)(tp:timeprod)
      (IDs:nonemptylist policyId)
      (prin_u:prin)(a:asset){struct reqs} := 

  let reqs_len := (length_nonempty reqs - 2) in
     match reqs with
       | Single req  => trans_requirment req IDs prin_u a
       | NewList req rest => 
            (trans_requirment req IDs prin_u a) /\
            (trans_InSequence rest IDs prin_u a) 
     end) in
*)

  match req with
  | PrePay amount tp => exists s'', trans_prepay amount s'' tp IDs
  | Attribution subj tp => exists t'', trans_attribution subj t'' tp
  (* The two cases below will probably have to be moved out of here like forEachMember *)
  (*
  | InSequence reqs tp => 
      let len := (length_nonempty reqs - 2) in
       trans_InSequence2 (rangestart tp) (rangeend tp) len reqs IDs prin_u a
  | AnySequence reqs tp => True
  *)
  end.

Fixpoint trans_InSequence
      (t t' len: nat)
      (reqs: nonemptylist requirement)
      (IDs:nonemptylist policyId)
      (prin_u:prin)(a:asset){struct len} : Prop := 

  
  match len with
    | O => 
         match reqs with          
           | NewList req10 (Single req2) =>           
                exists n, t < n < t' /\ 
                trans_requirment req10 (Timepair t n) IDs prin_u a /\ 
                trans_requirment req2 (Timepair n t') IDs prin_u a
           | _  => True 
         end   
    | S len' => 
         match reqs with
           | NewList req rest => 
                exists n, t < n /\ 
                trans_requirment req (Timepair t n) IDs prin_u a /\ 
                trans_InSequence n t' len' rest IDs prin_u a
           | _ => True
         end
  end.


Definition trans_notCons
  (const:constraint)(IDs:nonemptylist policyId)(prin_u:prin)(a:asset) : Prop :=
  ~ (trans_constraint const IDs prin_u a).




Definition trans_preRequisite
  (prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin)(a:asset) : Prop := 

  match prq with
    | TruePrq => True
    | Constraint const => trans_constraint const IDs prin_u a 
    | ForEachMember prn const_list => trans_forEachMember prn const_list IDs a
    | Requirement req => trans_requirment req (Timepair 0 MAX_TIME) IDs prin_u a
    | InSequence reqs tp => 
      let len := (length_nonempty reqs - 2) in
       trans_InSequence (rangestart tp) (rangeend tp) len reqs IDs prin_u a
    | NotCons const => trans_notCons const IDs prin_u a
    | AndPrqs prqs => True (*trans_andPrqs x prq IDs prin_u a*)
    | OrPrqs prqs => True (*trans_orPrqs x prq IDs prin_u a*)
    | XorPrqs prqs => True (*trans_xorPrqs x prq IDs prin_u a*)
  end.

Fixpoint trans_policy_positive
  (p:policy)(prin_u:prin)(a:asset){struct p} : Prop :=

let trans_p_list := (fix trans_p_list (p_list:nonemptylist policy)(prin_u:prin)(a:asset){struct p_list}:=
                  match p_list with
                    | Single p1 => trans_policy_positive p1 prin_u a
                    | NewList p p_list' => ((trans_policy_positive p prin_u a) /\ (trans_p_list p_list' prin_u a))
                  end) in


  match p with
    | PrimitivePolicy prq policyId action => ((trans_preRequisite prq (Single policyId) prin_u a) ->
                                              (permitted x action a))
    | AndPolicy p_list => trans_p_list p_list prin_u a
  end.

Fixpoint trans_policy_negative
  (p:policy)(a:asset){struct p} : Prop :=
let trans_p_list := (fix trans_p_list (p_list:nonemptylist policy)(a:asset){struct p_list}:=
                  match p_list with
                    | Single p1 => trans_policy_negative p1 a
                    | NewList p p_list' => ((trans_policy_negative p a) /\ (trans_p_list p_list' a))
                  end) in


  match p with
    | PrimitivePolicy prq policyId action => not (permitted x action a)
    | AndPolicy p_list => trans_p_list p_list a
  end.



Fixpoint trans_ps
  (ps:policySet)(prin_u:prin)(a:asset){struct ps} : Prop :=

let trans_ps_list := (fix trans_ps_list (ps_list:nonemptylist policySet)(prin_u:prin)(a:asset){struct ps_list}:=
                  match ps_list with
                    | Single ps1 => trans_ps ps1 prin_u a
                    | NewList ps ps_list' => ((trans_ps ps prin_u a) /\ (trans_ps_list ps_list' prin_u a))
                  end) in
  match ps with
    | PrimitivePolicySet prq p => ((trans_prin prin_u) /\ 
                                   (trans_preRequisite prq (getId p) prin_u a)) -> 
                                   (trans_policy_positive p prin_u a)

    | PrimitiveExclusivePolicySet prq p => ((((trans_prin prin_u) /\ 
                                              (trans_preRequisite prq (getId p) prin_u a)) -> 
                                             (trans_policy_positive p prin_u a)) /\

                                            ((not (trans_prin prin_u)) -> (trans_policy_negative p a)))
                   
    | AndPolicySet ps_list => trans_ps_list ps_list prin_u a
  end.


(***** 3.1 *****)

Eval compute in (trans_ps policySet2_5 prins2_5 ebook).

(***** 3.2 *****)
Eval compute in (trans_ps policySet2_6 prins2_6 latestJingle).

End Sems.



End ODRL.
