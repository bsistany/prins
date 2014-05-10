Module ODRL.

Require Import Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.Ascii.
Require Import Omega.

Set Implicit Arguments.

Open Scope string_scope.



Definition l23 : list nat
  := 2 :: 3 :: nil.

Locate pair.



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


Definition subject := nat.
Definition NullSubject:subject := 100.
Definition Alice:subject := 101.
Definition Bob:subject := 102.
Definition Charlie:subject := 103.
Definition Bahman:subject := 104.


(* simplified *)
Definition prin := nonemptylist subject.

Definition act := nat.
Definition NullAct := 300.
Definition Play : act := 301.
Definition Print : act := 302.
Definition Display : act := 303.

Definition asset := nat.
Definition NullAsset := 900.
Definition FindingNemo : asset := 901.
Definition Alien : asset := 902.
Definition Beatles : asset := 903.
Definition LoveAndPeace : asset := 904.
Definition TheReport:asset := 905.
Definition ebook:asset := 906.

Definition money := string.

Definition policyId := nat.
Definition NullId:subject := 200.
Definition id1:policyId := 201.
Definition id2:policyId := 202.
Definition id3:policyId := 203.
Definition id4:policyId := 204.

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
  | NotCons : constraint -> preRequisite 
  | AndPrqs : nonemptylist preRequisite -> preRequisite
  | OrPrqs : nonemptylist preRequisite -> preRequisite
  | XorPrqs : nonemptylist preRequisite -> preRequisite.


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


Definition p1A1:policySet :=
  PrimitivePolicySet
    TruePrq
    (PrimitivePolicy (Constraint (Count  5)) id1 Print).

Definition p2A1prq1:preRequisite := (Constraint (Principal (Single Alice))).
Definition p2A1prq2:preRequisite := (Constraint (Count 2)).

Definition p2A1:policySet :=
  PrimitivePolicySet
    TruePrq
    (PrimitivePolicy (AndPrqs (NewList p2A1prq1 (Single p2A1prq2))) id2 Print).

Definition A1 := Agreement (NewList Alice (Single Bob)) TheReport
                  (AndPolicySet (NewList p1A1 (Single p2A1))).

(* Example 2.5 *)

Definition tenCount:preRequisite := (Constraint (Count 10)).
Definition fiveCount:constraint := (Count 5).
Definition oneCount:constraint := (Count 1).

Definition prins2_5 := (NewList Alice (Single Bob)).

Check ForEachMember prins2_5 (Single fiveCount).
Definition forEach_display:preRequisite := ForEachMember prins2_5 (Single fiveCount).
Definition forEach_print:preRequisite := ForEachMember prins2_5 (Single oneCount).

Definition primPolicy1:policy := PrimitivePolicy forEach_display id1 Display.
Definition primPolicy2:policy := PrimitivePolicy forEach_print id2 Print.

Definition policySet2_5:policySet :=
  PrimitivePolicySet tenCount (AndPolicy (NewList primPolicy1 (Single primPolicy2))).
                     

Definition A2_5 := Agreement prins2_5 ebook policySet2_5.

(*** 2.6 ***)
Definition prins2_6 := prins2_5.

Definition aliceCount10:preRequisite := Constraint (CountByPrin (Single Alice) 10).
Definition primPolicy2_6:policy := PrimitivePolicy aliceCount10 id3 Play.
Definition policySet2_6_modified:= PrimitiveExclusivePolicySet TruePrq primPolicy2_6.


(****** Environments ******)
Section Environment.

  
Inductive count_equality : Set := 
   | CountEquality : subject -> policyId -> nat -> count_equality.

Check count_equality.


Definition make_count_equality
  (s:subject)(id:policyId)(n:nat): count_equality :=
  CountEquality s id n.


Definition environment := nonemptylist count_equality.

(** Looks for count of a (subject, id) pair.
    Assumes e is consistent, so it returns the first count it sees for a (subject, id) pair.
	If a count for a (subject, id) pair is not found it returns 0. **)
	



Fixpoint getCount 
  (e:environment)(s:subject)(id: policyId): nat :=
  match e with
  | Single f  => 
      match f with 
	  | CountEquality s1 id1 n1 => 
          if (beq_nat s s1) 
          then if (beq_nat id id1) then n1 else 0 
          else 0  
      end			
  | NewList f rest =>
      match f with 
	  | CountEquality s1 id1 n1 => 
          if (beq_nat s s1)
          then if (beq_nat id id1) then n1 else (getCount rest s id)  
          else (getCount rest s id)
      end
  end.




Definition f1:count_equality := make_count_equality Alice id2 6.
Definition f2:count_equality := make_count_equality Alice id2 7.


Definition inconsistent (f1 f2 : count_equality) : Prop :=
   match f1 with (CountEquality s1 id1 n1) =>
     match f2 with (CountEquality s2 id2 n2) =>       
       s1 = s2 -> id1 = id2 -> n1 <> n2
     end 
   end.

Eval compute in (inconsistent f1 f2).

Eval compute in (6 <> 7).



Fixpoint get_list_of_pairs_of_count_formulas (e : environment) : 
  nonemptylist (Twos count_equality count_equality) := 
    let nullCountFormula:count_equality := make_count_equality NullSubject NullId 0 in
      let list_of_pairs_of_null : nonemptylist (Twos count_equality count_equality) 
        :=  Single (mkTwos nullCountFormula nullCountFormula) in
  
          match e with
            | Single f => list_of_pairs_of_null
            | NewList first (Single f) => Single (mkTwos first f)
            | NewList first rest => 
          
              let twos := process_two_lists (Single first) rest in
                app_nonempty twos (get_list_of_pairs_of_count_formulas rest)

          end.

(* test the first clause: single count formula should return a pair of null count formulas *)    
Definition e1 : environment := 
  (Single (make_count_equality Alice id1 8)).
Eval compute in (get_list_of_pairs_of_count_formulas e1).

(* test the second clause: two count formulas should return a pair of the two count formulas *)    
Definition e2 : environment := (NewList f1 (Single f2)).
Eval compute in (get_list_of_pairs_of_count_formulas e2).

(* test the third case: three count formulas should return a list of 3 pairs of count formulas *)    
Definition e3 : environment := 
  (NewList (make_count_equality Alice id1 8) 
     (NewList (make_count_equality Bob id2 9) (Single (make_count_equality Charlie id3 10)))).
Eval compute in (get_list_of_pairs_of_count_formulas e3).

(* test the third case with 4 count formulas: should return a list of 6 pairs of count formulas *)    
Definition e4 : environment := 
  (NewList (make_count_equality Alice id1 8) 
     (NewList (make_count_equality Bob id2 9) 
        (NewList (make_count_equality Charlie id3 10)
          (Single (make_count_equality Bahman id4 11))))).

Eval compute in (get_list_of_pairs_of_count_formulas e4).

(****************************************)
(****************************************)

Fixpoint env_consistent (e : environment) : Prop :=
  let pairs : nonemptylist (Twos count_equality count_equality) := (get_list_of_pairs_of_count_formulas e) in
    let pairs_consistent := 
      (fix pairs_consistent (pairs : nonemptylist (Twos count_equality count_equality)) : Prop :=
        match pairs with
          | Single p => inconsistent (left p) (right p) 
          | NewList p rest =>  inconsistent (left p) (right p) /\ (pairs_consistent rest)
        end) in 
  pairs_consistent pairs.

Eval compute in (env_consistent e2).


End Environment.



(******* Semantics ********)

Section Sems.

Parameter Permitted : subject -> act -> asset -> Prop.
(* Parameter getCount : subject -> policyId -> nat. *)


(*** Environments: in odrl0 are simply a conjunction of positive ground literals of the form count(s, id)= n ***)

(** A clause is a list (disjunction) of literals. *)
(* Definition formula := Prop. *)


(** A formula is a list (conjunction) of clauses. *)
(* Definition formula := list clause. *)(** conjuction *)


Check eq_nat.

Definition eq_type := nat -> nat -> Prop.

Check Twos.


Check prod.





(* is x in prin? *)
(** Definition prin := nonemptylist subject. **)
Fixpoint trans_prin
  (x:subject)(p: prin): Prop :=

  match p with
    | Single s => (x=s)
    | NewList s rest => ((x=s) \/ trans_prin x rest)
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
  


Fixpoint trans_count 
  (e:environment)(n:nat)(IDs:nonemptylist policyId)
  (prin_u:prin) : Prop := 

  let trans_count_aux 
    := (fix trans_count_aux
         (ids_and_subjects : nonemptylist (Twos policyId subject)) : nat :=
     match ids_and_subjects with
        | Single pair1 => getCount e (right pair1) (left pair1)
        | NewList pair1 rest_pairs =>
            (getCount e (right pair1)(left pair1)) +
            (trans_count_aux rest_pairs)
      end) in
  
  let ids_and_subjects := process_two_lists IDs prin_u in
  let running_total := trans_count_aux ids_and_subjects in
  running_total < n.


Fixpoint trans_constraint 
  (e:environment)(x:subject)(const:constraint)(IDs:nonemptylist policyId)
  (prin_u:prin){struct const} : Prop := 
(*************************************************)
(*************************************************)
  match const with
    | Principal prn => trans_prin x prn
  
    | Count n => trans_count e n IDs prin_u 

    | CountByPrin prn n => trans_count e n IDs prn 

  end.




Fixpoint trans_forEachMember
         (e:environment)(x:subject)(principals: nonemptylist subject)(const_list:nonemptylist constraint)
         (IDs:nonemptylist policyId){struct const_list} : Prop := 

let trans_forEachMember_Aux   
  := (fix trans_forEachMember_Aux
         (prins_and_constraints : nonemptylist (Twos subject constraint))
         (IDs:nonemptylist policyId){struct prins_and_constraints} : Prop :=

      match prins_and_constraints with
        | Single pair1 => trans_constraint e x (right pair1) IDs (Single (left pair1)) 
        | NewList pair1 rest_pairs =>
            (trans_constraint e x (right pair1) IDs (Single (left pair1))) /\
            (trans_forEachMember_Aux rest_pairs IDs)
      end) in

      let prins_and_constraints := process_two_lists principals const_list in
      trans_forEachMember_Aux prins_and_constraints IDs.


(*************

Parameter Perm : nat -> Prop.


Check (ex Perm). (* gives you exists x, Perm x *)
Definition ff3 : Prop :=
ex Perm.
**************)




Definition trans_notCons
  (e:environment)(x:subject)(const:constraint)(IDs:nonemptylist policyId)(prin_u:prin) : Prop :=
  ~ (trans_constraint e x const IDs prin_u).

Definition trans_preRequisite
  (e:environment)(x:subject)(prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin)(a:asset) : Prop := 

  match prq with
    | TruePrq => True
    | Constraint const => trans_constraint e x const IDs prin_u 
    | ForEachMember prn const_list => trans_forEachMember e x prn const_list IDs 
    | NotCons const => trans_notCons e x const IDs prin_u 
    | AndPrqs prqs => True (*trans_andPrqs x prq IDs prin_u a*)
    | OrPrqs prqs => True (*trans_orPrqs x prq IDs prin_u a*)
    | XorPrqs prqs => True (*trans_xorPrqs x prq IDs prin_u a*)
  end.

Fixpoint trans_policy_positive
  (e:environment)(x:subject)(p:policy)(prin_u:prin)(a:asset){struct p} : Prop :=

let trans_p_list := (fix trans_p_list (p_list:nonemptylist policy)(prin_u:prin)(a:asset){struct p_list}:=
                  match p_list with
                    | Single p1 => trans_policy_positive e x p1 prin_u a
                    | NewList p p_list' => 
                        ((trans_policy_positive e x p prin_u a) /\ 
                         (trans_p_list p_list' prin_u a))
                  end) in


  match p with
    | PrimitivePolicy prq policyId action => ((trans_preRequisite e x prq (Single policyId) prin_u a) ->
                                              (Permitted x action a))
    | AndPolicy p_list => trans_p_list p_list prin_u a
  end.

Fixpoint trans_policy_negative
  (e:environment)(x:subject)(p:policy)(a:asset){struct p} : Prop :=
let trans_p_list := (fix trans_p_list (p_list:nonemptylist policy)(a:asset){struct p_list}:=
                  match p_list with
                    | Single p1 => trans_policy_negative e x p1 a
                    | NewList p p_list' => ((trans_policy_negative e x p a) /\ 
                                            (trans_p_list p_list' a))
                  end) in


  match p with
    | PrimitivePolicy prq policyId action => not (Permitted x action a)
    | AndPolicy p_list => trans_p_list p_list a
  end.



Fixpoint trans_ps
  (e:environment)(ps:policySet)(prin_u:prin)(a:asset){struct ps} : Prop :=

let trans_ps_list := (fix trans_ps_list (ps_list:nonemptylist policySet)(prin_u:prin)(a:asset){struct ps_list}:=
                  match ps_list with
                    | Single ps1 => trans_ps e ps1 prin_u a
                    | NewList ps ps_list' => ((trans_ps e ps prin_u a) /\ (trans_ps_list ps_list' prin_u a))
                  end) in
  match ps with
    | PrimitivePolicySet prq p => forall x, (((trans_prin x prin_u) /\ 
                                   (trans_preRequisite e x prq (getId p) prin_u a)) -> 
                                   (trans_policy_positive e x p prin_u a))  

    | PrimitiveExclusivePolicySet prq p => forall x, ((((trans_prin x prin_u) /\ 
                                              (trans_preRequisite e x prq (getId p) prin_u a)) -> 
                                             (trans_policy_positive e x p prin_u a)) /\
                                            ((not (trans_prin x prin_u)) -> (trans_policy_negative e x p a)))
                   
    | AndPolicySet ps_list => trans_ps_list ps_list prin_u a
  end.


Fixpoint trans_agreement
   (e:environment)(ag:agreement) : Prop :=
   match ag with 
   | Agreement prin_u a ps => trans_ps e ps prin_u a
   end.

  
(***** 3.1 *****)


Eval simpl in (trans_ps e1 policySet2_5 prins2_5 ebook).

Eval compute in (trans_ps e2 policySet2_5 prins2_5 ebook).




(*** Canonical Agreement example ***)
Section A1.

Definition psA1:policySet :=
  PrimitivePolicySet
    TruePrq
    (PrimitivePolicy (Constraint (Count  5)) id1 Print).

Definition AgreeCan := Agreement (Single Alice) TheReport psA1.
Definition eA1 : environment := 
  (Single (make_count_equality Alice id1 2)).

Eval compute in (trans_agreement eA1 AgreeCan).

Hypothesis H: trans_agreement eA1 AgreeCan.
(* Hypothesis AliceCount : getCount Alice "id1" = 2. *)
Theorem SSS: Permitted Alice Print TheReport.
Proof. simpl in H. apply H. split. reflexivity. auto. omega. Qed.
End A1.



Section A2.

(**  getCount Alice "id1" = 5,  and see if you can prove ~(Permitted Alice ...). **)
Definition eA2 : environment := 
  (Single (make_count_equality Alice id1 5)).

Definition psA2:policySet :=
  PrimitivePolicySet
    TruePrq
    (PrimitivePolicy (Constraint (Count  5)) id1 Print).

Definition AgreeA2 := Agreement (Single Alice) TheReport psA2.

Eval compute in (trans_agreement eA2 AgreeA2).

(* Hypothesis AliceCount : getCount Alice "id1" = 5. *)
Hypothesis H: trans_agreement eA2 AgreeA2.

Theorem SS1: (getCount eA2 Alice id1) < 5 -> (Permitted Alice Print TheReport).
Proof. simpl in H. apply H. split. reflexivity. apply I. Qed.

Theorem SSS: ~(Permitted Alice Print TheReport).
Proof. simpl in H. unfold not.  generalize H. Abort.
(*
intro H'. generalize H. Abort.
*)

End A2.



Section A3.

(***
Theorem FFF: 8<10.
Proof. apply le_S. apply le_n. Qed.
 
le_n : forall n : nat, n <= n
le_S : : forall n m : nat, n <= m -> n <= S m.
***)


Definition AgreeA3 := Agreement prins2_5 ebook policySet2_5.
(**
Definition eA3 : environment := 
  (NewList (make_count_equality Alice id1 3) 
     (NewList (make_count_equality Alice id2 11) 
        (NewList (make_count_equality Bob id1 6) 
          (Single (make_count_equality Bob id2 1))))).
Eval compute in (trans_agreement eA3 AgreeA3).

forall x : nat,
       (x = 101 \/ x = 102) /\ 22 <= 10 ->
       (4 <= 5 /\ 7 <= 5 -> Permitted x "Display" "ebook") /\
       (12 <= 1 /\ 2 <= 1 -> Permitted x "Print" "ebook")
     : Prop

**)
Definition eA3 : environment := 
  (NewList (make_count_equality Alice id1 3) 
     (NewList (make_count_equality Alice id2 0) 
        (NewList (make_count_equality Bob id1 4) 
          (Single (make_count_equality Bob id2 0))))).

Eval compute in (trans_agreement eA3 AgreeA3).

Hypothesis H: trans_agreement eA3 AgreeA3.

Theorem T1_A3: Permitted Alice Print ebook.
Proof. simpl in H. apply H. intuition. intuition. Qed.

End A3.



Section A5.

Definition prin_bob := (Single Bob).
Definition pol:policy := PrimitivePolicy TruePrq id3 Print.
Definition pol_set:policySet := PrimitiveExclusivePolicySet TruePrq pol.
Definition AgreeA5 := Agreement prin_bob LoveAndPeace pol_set.
Definition eA5 : environment := (Single (make_count_equality NullSubject NullId 0)).
Eval compute in (trans_agreement eA5 AgreeA5).

Hypothesis H: trans_agreement eA5 AgreeA5.


Theorem T1_A5: forall x, x<>Bob -> ~Permitted x Print LoveAndPeace.
Proof. simpl in H. apply H. Qed.

(*
Theorem not_eq_S : forall n m:nat, n <> m -> S n <> S m.
*)
Theorem T2_A5: ~Permitted Alice Print LoveAndPeace.
Proof. simpl in H. apply T1_A5. apply not_eq_S. omega. Qed.


End A5.




End Sems.


Section Query.

(* a query is a tuple: (agreements * subject * act * asset * environment)  *)
Inductive query : Set := 
   | SingletonQuery : agreement -> subject -> act -> asset -> environment -> query
   | GeneralQuery : nonemptylist agreement -> subject -> act -> asset -> environment -> query.

Definition make_query 
  (agrs:nonemptylist agreement)(s:subject)(myact:act)(a:asset)(e:environment) : query :=
  match agrs with
  | Single agr  => SingletonQuery agr s myact a e
  | _ => GeneralQuery agrs s myact a e
  end.

Definition q1: query := make_query (Single AgreeA5) Alice Display TheReport e1. 
End Query.



Section AAA.

Fixpoint trans_agreements (e:environment)(agrs:nonemptylist agreement) : Prop :=
  match agrs with
    | Single agr => trans_agreement e agr 
    | NewList agr rest => trans_agreement e agr  /\ (trans_agreements e rest)
  end.

Definition make_fplus (e:environment)(q: query) : Prop := 
  match q with
    | GeneralQuery agreements s action a e => trans_agreements e agreements -> (Permitted s action a)
    | SingletonQuery agr s action a e => trans_agreements e (Single agr) -> (Permitted s action a)
  end.


Definition make_fminus (e:environment)(q: query) : Prop := 
  match q with 
    | GeneralQuery agreements s action a e => trans_agreements e agreements -> ~(Permitted s action a)
    | SingletonQuery agr s action a e => trans_agreements e (Single agr) -> ~(Permitted s action a)
  end.


Definition fp1 : Prop := make_fplus e1 q1.
Definition fn1 : Prop := make_fminus e1 q1.

Eval compute in fp1.

Eval compute in fn1.


Inductive answer : Set :=
  | QueryInconsistent : answer
  | PermissionGranted : answer
  | PermissionDenied : answer
  | PermissionUnregulated : answer.

Check Permitted.

Fixpoint is_subject_in_prin (s:subject)(p:prin): Prop :=
  match p with
  | Single s'  => s=s'
  | NewList s' rest => s=s' \/ (is_subject_in_prin s rest)
  end.


(******
http://adam.chlipala.net/cpdt/html/Predicates.html

Note that definition isZero makes the predicate provable only when the argument is 0.

Inductive isZero : nat -> Prop :=
| IsZero : isZero 0.

Theorem isZero_zero : isZero 0.
  constructor.
Qed.


Inductive isPermitted : subject -> act -> asset -> Prop :=
  | IsPermitted : 

*******)


Inductive prereqs : Set :=
  | Prereqs : nonemptylist preRequisite -> prereqs.

Inductive implication2 : Type :=
  | Implication2 : (nonemptylist preRequisite) -> (subject -> act -> asset -> Prop) -> implication2.

Definition imp2 := Implication2 (Single p2A1prq2) Permitted.



Inductive implication1 : Type :=
  | Implication1 : (subject -> (nonemptylist preRequisite) -> implication2) -> implication1.

Definition imp1 := 
  Implication1 (fun (x:subject)(prqs:nonemptylist preRequisite) => imp2).

Inductive formula : Type :=
  | Forall : (subject -> implication1) -> formula.

Definition forall_refl : formula := Forall (fun x:subject => imp1).

Print formula.



(** E-relevant Models **)

Parameter evalid: formula -> Prop.
 
(***** TODO 
Definition decision (q:query) : answer :=
 (evalid (make_fplus q)) /\ (evalid (make_fminus q))  


Fixpoint get_list_of_subject_id_pairs (agrs:nonemptylist agreement) : 
  nonemptylist (Twos subject policyId) := 
    let nullPair:Twos subject policyId := mkTwos "Null" "0" in
    match agrs with
      | Single agr => 
          match agr with 
            | Agreement prin_u a ps => 
                match ps with                  
                    | PrimitivePolicySet prq p => 
                        match prq with                    
                          | Constraint const => 
                              match const with                                 
                                | Principal prn => Single nullPair
                                | Count n => trans_count n IDs prin_u a
                                | CountByPrin prn n => *******
                          | _ => Single nullPair   
                    | PrimitiveExclusivePolicySet prq p => ************
                    | AndPolicySet ps_list => ************
                end
          end
      | NewList agr rest => trans_agreement agr  /\ (trans_agreements rest)
    end.

******)


(** Theorem 4.6 **)
Definition answer_query (q: query) : answer := QueryInconsistent.

Section TheSplus.
 
Record fourTuple : Set := 
  mkFourTuple 
  {
    tt_I : nonemptylist policyId;
    tt_prq' : preRequisite;
    tt_id : policyId;
    tt_act' : act 
  }.
Inductive splus : Set :=
  | Splus : nonemptylist (Twos preRequisite fourTuple) -> splus.



Fixpoint getIPrqIdAct (p:policy): nonemptylist fourTuple := 
  let process_policies := (fix process_policies (policies:nonemptylist policy){struct policies}:=
    match policies with
      | Single p1 => getIPrqIdAct p1
      | NewList p1 rest => app_nonempty (getIPrqIdAct p1) (process_policies rest)
    end) in

  match p with
    | PrimitivePolicy prq' id act' => Single (mkFourTuple (getId p) prq' id act')
    | AndPolicy policies => process_policies policies
  end.

Fixpoint getCrossProductOfprqAndFourTuple (prq:preRequisite)(fours:nonemptylist fourTuple): 
  nonemptylist (Twos preRequisite fourTuple) := 
  match fours with
    | Single f1 => Single (mkTwos prq f1)
    | NewList f1 rest => app_nonempty (Single (mkTwos prq f1)) 
                                             (getCrossProductOfprqAndFourTuple prq rest)
  end.



Fixpoint getSplusFromList (tuples: nonemptylist (Twos preRequisite fourTuple)) : splus :=
  match tuples with
    | Single tuple => Splus (Single tuple)
    | NewList tuple rest => Splus (app_nonempty (Single tuple) rest)                                             
  end.


Fixpoint getPrqAndTheRestTuple (ps : policySet) : nonemptylist (Twos preRequisite fourTuple) :=

  let process_ps_list := (fix process_ps_list (ps_list:nonemptylist policySet){struct ps_list}:=
    match ps_list with
      | Single ps1 => getPrqAndTheRestTuple ps1
      | NewList ps ps_list' => app_nonempty (getPrqAndTheRestTuple ps) (process_ps_list ps_list')
    end) in

  match ps with
    | PrimitivePolicySet prq p => getCrossProductOfprqAndFourTuple prq (getIPrqIdAct p)
    | PrimitiveExclusivePolicySet prq p => getCrossProductOfprqAndFourTuple prq (getIPrqIdAct p)                 
    | AndPolicySet ps_list => process_ps_list ps_list
  end.

Fixpoint getSplus (ps : policySet) : splus :=
  let prqAndTheRestTuples := getPrqAndTheRestTuple ps in 
    getSplusFromList prqAndTheRestTuples.

End TheSplus.

Section TheSminus.

Fixpoint getActionsFromPolicy (p:policy): nonemptylist act := 
  let process_policies := (fix process_policies (policies:nonemptylist policy){struct policies}:=
    match policies with
      | Single p1 => getActionsFromPolicy p1
      | NewList p1 rest => app_nonempty (getActionsFromPolicy p1) (process_policies rest)
    end) in

  match p with
    | PrimitivePolicy prq id act => Single act
    | AndPolicy policies => process_policies policies
  end.

Fixpoint getSminus (ps : policySet) : nonemptylist act :=
  let process_ps_list := (fix process_ps_list (ps_list:nonemptylist policySet){struct ps_list}:=
    match ps_list with
      | Single ps1 => getSminus ps1
      | NewList ps ps_list' => app_nonempty (getSminus ps) (process_ps_list ps_list')
    end) in

  match ps with
    | PrimitivePolicySet prq p => Single NullAct
    | PrimitiveExclusivePolicySet prq p => getActionsFromPolicy p                 
    | AndPolicySet ps_list => process_ps_list ps_list
  end.

End TheSminus.

Eval compute in (getIPrqIdAct pol).
Eval compute in (getSplus pol_set).
Eval compute in (getPrqAndTheRestTuple policySet2_5).
Eval compute in (getSplus policySet2_5).
Eval compute in (getIPrqIdAct (AndPolicy (NewList primPolicy1 (Single primPolicy2)))).

Eval compute in (getSminus policySet2_6_modified).


Fixpoint isPrqs_evalid (e:environment)(s:subject)(pr: prin)(a:asset)(tups:nonemptylist (Twos preRequisite fourTuple)) : Prop :=
  let isPrqAndPrq'_evalid 
    := (fix isPrqAndPrq'_evalid 
            (e:environment)(s:subject)(t:Twos preRequisite fourTuple)(pr: prin)(a:asset): Prop :=
          (trans_preRequisite e s (left t)            (tt_I (right t))           pr a) /\
          (trans_preRequisite e s (tt_prq' (right t)) (Single (tt_id (right t))) pr a) 
          ) in
  match tups with
    | Single t =>  isPrqAndPrq'_evalid e s t pr a 
    | NewList t lst' => (isPrqAndPrq'_evalid e s t pr a) \/ (isPrqs_evalid e s pr a lst')
  end.

Definition is_fplusq_evalid (q: query) : Prop :=  
  match q with    
    | SingletonQuery agr s action a e => 
      match agr with 
        | Agreement prn a' ps => 
            (env_consistent e) \/
            ((is_subject_in_prin s prn) /\ (a=a') /\ 
              (* There is a Tuple in Splus s.t. is_evalid (prq/\prq') *)
              let sp := getSplus ps in
                match sp with
                  | Splus lst => isPrqs_evalid e s prn Beatles lst
                end)
      end
                
    | GeneralQuery agreements s action a e => True (*** TODO ***)
  end.

(*** 
     Agreement says that TheReport may be printed a total of 5 times by Alice
     The Env says that Alice has already printed TheReport 2 times.
     So the answer to query: May Alice print TheReport should be YES or another 
     way of saying that is that fqplus is evalid (well not quite, as we need to 
     follow the whole algorithms and look at fqminus as well) 
***)
Definition q2: query := make_query (Single AgreeCan) Alice Print TheReport eA1.
Eval compute in (eA1). 
Eval compute in (env_consistent eA1).
Eval compute in (is_fplusq_evalid q2).





   







End AAA.




(*

Parameter even: nat -> Prop.
Parameter divides: nat -> nat -> Prop.

Theorem th1 : forall (x y: nat), 
 (even x) -> (divides x y) -> (even y).

Theorem th2 : forall (x y: nat), divides x (x * y).

Check even.

Check fun (x:nat) => fun (h: even x) => h.

Definition evenn (x:nat) : Prop :=
  forall (P: nat -> Prop), forall (y:nat), P(2*y)-> P x.

Check evenn.

Theorem th3: forall (x:nat), evenn 2.
Proof. unfold evenn. intros. apply H.
*)
(********* TODO *********)
Example test_inconsistent: (inconsistent f1 f2) = (6<>7).
(* Proof. unfold inconsistent. simpl. intuition. *) Admitted. 




End ODRL.
