Module ODRL.

Require Import Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.Ascii.
Require Import Omega.
(** 
Require Import Coq.Logic.Classical_Prop.
**)

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

Definition primPolicy2222:policy := PrimitivePolicy (Constraint (Principal (Single Alice))) id1 Display.
Definition primPolicy3333:policy := PrimitivePolicy (Constraint (Count 2)) id2 Print.
Definition policySet2222:policySet:= 
 PrimitivePolicySet (Constraint (Count 2222))
 (AndPolicy (NewList (PrimitivePolicy (Constraint (Principal (Single Alice))) id1 Display)
            (Single (PrimitivePolicy (Constraint (Count 2)) id2 Print)))).
Definition agree1 := Agreement (Single Bob) ebook (PrimitivePolicySet (Constraint (Count 2222))
 (AndPolicy (NewList (PrimitivePolicy (Constraint (Principal (Single Alice))) id1 Display)
            (Single (PrimitivePolicy (Constraint (Count 2)) id2 Print))))).

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



Inductive environment : Set := 
  | SingleEnv : count_equality -> environment
  | ConsEnv :  count_equality ->  environment -> environment.

(*
Definition environment := nonemptylist count_equality.
*)

(** Looks for count of a (subject, id) pair.
    Assumes e is consistent, so it returns the first count it sees for a (subject, id) pair.
	If a count for a (subject, id) pair is not found it returns 0. **)

Fixpoint getCount 
  (e:environment)(s:subject)(id: policyId): nat :=
  match e with
  | SingleEnv f  => 
      match f with 
	  | CountEquality s1 id1 n1 => 
          if (beq_nat s s1) 
          then if (beq_nat id id1) then n1 else 0 
          else 0  
      end			
  | ConsEnv f rest =>
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

Check inconsistent.

Eval compute in (inconsistent f1 f2).


Eval compute in (6 <> 7).
(*
Inductive sorted : list nat -> Prop :=
  snil : sorted nil
| s1 : forall x, sorted (x::nil)
| s2 : forall x y l, sorted (y::l) -> x <= y ->
    sorted (x::y::l).
*)


Fixpoint formula_inconsistent_with_env (f: count_equality)
                          (e : environment) : Prop :=
  match e with
    | SingleEnv g =>  inconsistent f g
    | ConsEnv g rest => (inconsistent f g) \/ (formula_inconsistent_with_env f rest)
  end.



Inductive env_consistent : environment -> Prop :=
| consis_1 : forall f, env_consistent (SingleEnv f)
| consis_2 : forall f g, ~(inconsistent f g) -> env_consistent (ConsEnv f (SingleEnv g))
| consis_more : forall f e, 
   env_consistent e -> ~(formula_inconsistent_with_env f e) -> env_consistent (ConsEnv f e). 


(*
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
*)
(* test the first clause: single count formula should return a pair of null count formulas *)    
Definition e1 : environment := 
  (SingleEnv (make_count_equality Alice id1 8)).
(*
Eval compute in (get_list_of_pairs_of_count_formulas e1).
*)

(* test the second clause: two count formulas should return a pair of the two count formulas *)    
Definition e2 : environment := (ConsEnv f1 (SingleEnv f2)).
(*
Eval compute in (get_list_of_pairs_of_count_formulas e2).
*)

(* test the third case: three count formulas should return a list of 3 pairs of count formulas *)    
Definition e3 : environment := 
  (ConsEnv (make_count_equality Alice id1 8) 
     (ConsEnv (make_count_equality Bob id2 9) (SingleEnv (make_count_equality Charlie id3 10)))).
(*
Eval compute in (get_list_of_pairs_of_count_formulas e3).
*)
(* test the third case with 4 count formulas: should return a list of 6 pairs of count formulas *)    
Definition e4 : environment := 
  (ConsEnv (make_count_equality Alice id1 8) 
     (ConsEnv (make_count_equality Bob id2 9) 
        (ConsEnv (make_count_equality Charlie id3 10)
          (SingleEnv (make_count_equality Bahman id4 11))))).
(*
Eval compute in (get_list_of_pairs_of_count_formulas e4).
*)
(****************************************)
(****************************************)

(*** set of E-relevant models is Empty <=> e is inconsistent ***)
(*** set of E-relevant models is Non-Empty <=> e is consistent ***)
(*
Fixpoint env_consistent_old (e : environment) : Prop :=
  let pairs : nonemptylist (Twos count_equality count_equality) := (get_list_of_pairs_of_count_formulas e) in
    let pairs_consistent := 
      (fix pairs_consistent (pairs : nonemptylist (Twos count_equality count_equality)) : Prop :=
        match pairs with
          | Single p => inconsistent (left p) (right p) 
          | NewList p rest =>  inconsistent (left p) (right p) /\ (pairs_consistent rest)
        end) in 
  pairs_consistent pairs.
*)


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
  (e:environment)(x:subject)(prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin) : Prop := 

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
    | PrimitivePolicy prq policyId action => ((trans_preRequisite e x prq (Single policyId) prin_u) ->
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
                                   (trans_preRequisite e x prq (getId p) prin_u)) -> 
                                   (trans_policy_positive e x p prin_u a))  

    | PrimitiveExclusivePolicySet prq p => forall x, ((((trans_prin x prin_u) /\ 
                                              (trans_preRequisite e x prq (getId p) prin_u)) -> 
                                             (trans_policy_positive e x p prin_u a)) /\
                                            ((not (trans_prin x prin_u)) -> (trans_policy_negative e x p a)))
                   
    | AndPolicySet ps_list => trans_ps_list ps_list prin_u a
  end.


Definition trans_agreement
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
  (SingleEnv (make_count_equality Alice id1 2)).

Eval compute in (trans_agreement eA1 AgreeCan).

Hypothesis H: trans_agreement eA1 AgreeCan.
(* Hypothesis AliceCount : getCount Alice "id1" = 2. *)
Theorem SSS: Permitted Alice Print TheReport.
Proof. simpl in H. apply H. split. reflexivity. auto. omega. Qed.
End A1.

Section Example4_3.

Definition ps_alice:policySet := PrimitivePolicySet TruePrq (PrimitivePolicy TruePrq id1 Print).
Definition agr := Agreement (Single Alice) TheReport ps_alice.
Definition e_agr : environment := (SingleEnv (make_count_equality NullSubject NullId 0)).
Eval compute in (trans_agreement e_agr agr).

Definition ps_bob:policySet := PrimitiveExclusivePolicySet TruePrq (PrimitivePolicy TruePrq id2 Print).
Definition agr' := Agreement (Single Bob) TheReport ps_bob.
Definition e_agr' : environment := (SingleEnv (make_count_equality NullSubject NullId 0)).
Eval compute in (trans_agreement e_agr' agr').

End Example4_3.

Section A2.

(**  getCount Alice "id1" = 5,  and see if you can prove ~(Permitted Alice ...). **)
Definition eA2 : environment := 
  (SingleEnv (make_count_equality Alice id1 5)).

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
  (ConsEnv (make_count_equality Alice id1 3) 
     (ConsEnv (make_count_equality Alice id2 0) 
        (ConsEnv (make_count_equality Bob id1 4) 
          (SingleEnv (make_count_equality Bob id2 0))))).

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
Definition eA5 : environment := (SingleEnv (make_count_equality NullSubject NullId 0)).
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

Inductive single_query : Set := 
   | SingletonQuery : agreement -> subject -> act -> asset -> environment -> single_query.
   

Inductive general_query : Set := 
   | GeneralQuery : nonemptylist agreement -> subject -> act -> asset -> environment -> general_query.


Definition make_general_query 
  (agrs:nonemptylist agreement)(s:subject)(myact:act)(a:asset)(e:environment) : general_query :=
  GeneralQuery agrs s myact a e.
  
Definition make_single_query 
  (agr: agreement)(s:subject)(myact:act)(a:asset)(e:environment) : single_query :=
  SingletonQuery agr s myact a e.

Definition general_q1: general_query := make_general_query (Single AgreeA5) Alice Display TheReport e1. 
Definition single_q1: single_query := make_single_query AgreeA5 Alice Display TheReport e1. 
End Query.



Section AAA.

Fixpoint trans_agreements (e:environment)(agrs:nonemptylist agreement) : Prop :=
  match agrs with
    | Single agr => trans_agreement e agr 
    | NewList agr rest => trans_agreement e agr  /\ (trans_agreements e rest)
  end.


Definition make_fplus (e:environment)(q: general_query) : Prop := 
  match q with
    | GeneralQuery agreements s action a e => trans_agreements e agreements -> (Permitted s action a)
  end.


Definition make_fminus (e:environment)(q: general_query) : Prop := 
  match q with 
    | GeneralQuery agreements s action a e => trans_agreements e agreements -> ~(Permitted s action a)
  end.


Definition fp1 : Prop := make_fplus e1 general_q1.
Definition fn1 : Prop := make_fminus e1 general_q1.

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
Definition answer_query (q: general_query) : answer := QueryInconsistent.

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

Definition getSplusAsList(ps: policySet) : nonemptylist (Twos preRequisite fourTuple) :=
  let sp := (getSplus ps) in 
    match sp with
      | Splus list_of_prqAndFourTyples => list_of_prqAndFourTyples
    end.

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

Section Lemma45.

(** This is a partial function in that to make a pair of agreements we need at least
    two agreements: [agr1 agr2] -> [(agr1 agr2)]. However it is possible that 
    this function recevies a list of agreements of length 1. In that case, we make
    a trivial/null list_of_pairs where we repeat the agr. So:
    [agr1] -> [(agr1 agr1)]. The calling function must either call this function 
    and then check for this case or check the length of the list of agreements
    and don't call this function.
    We had a similat case eailer (function get_list_of_pairs_of_count_formulas) 
    where we would make a list of pair of null count formulas...
    ultimately these are ugly solutions and we will eventually use one of:
    option type, subset type, use a relation instead of a function 
    (x->y->Prop instead of x->y), dependent types, etc

Update: May 30, 2014. See my email to Amy...turns out we need all pairs of 
                      agreements starting from length 1.
We have(size of A)^2 pairs of agreements. 

So we get the following for lists of size 1 and 2:  

[a1] --> (a1 a1)
[a1 a2] -> (a1 a1)(a1 a2)(a2 a1)(a2 a2)

In practice, the way I have it (and I think this is correct), the first case can never happen.
Since SingletonQuery case in Theorem 4.6 will  take care of the case where we only have 1 agreement.
So the very first case of GeneralQuery is [a1 a2] which will result in 4 pairs as outlined above
**)
    
Fixpoint get_list_of_pairs_of_agreements (agrs:nonemptylist agreement) : 
  nonemptylist (Twos agreement agreement) :=   
    process_two_lists agrs agrs.
          

(** Usual problem: the difference could be empty but have to use nonemptylist 
    to be compatible with all other functions. We will use NullSubject which 
    the caller needs to filter out or ignore somehow
**)

Fixpoint getPrinsSetDifference (p p':prin){struct p}: nonemptylist subject :=

  let process_element_list := (fix process_element_list (s : subject) (p' : nonemptylist subject) :  nonemptylist subject :=
    match p' with
    | Single s' => if beq_nat s s' then Single NullSubject else Single s
    | NewList s' rest' => 
      app_nonempty (if beq_nat s s' then Single NullSubject else Single s) 
                   (process_element_list s rest') 
  end) in

  match p with
  | Single s => process_element_list s p' 
  | NewList s rest => app_nonempty (process_element_list s p') (getPrinsSetDifference rest p') 
  end.


Fixpoint process_act_tuple_subject_pairs 
        (e:environment)
        (prin_u': prin)
        (act_tuple_subject_pairs : nonemptylist (Twos act (Twos (Twos preRequisite fourTuple) subject))) : Prop :=

  let isPrqAndPrq'_evalid 
    := (fix isPrqAndPrq'_evalid 
            (e:environment)(s:subject)(t:Twos preRequisite fourTuple)(pr: prin): Prop :=
          (trans_preRequisite e s (left t)            (tt_I (right t))           pr) /\
          (trans_preRequisite e s (tt_prq' (right t)) (Single (tt_id (right t))) pr) 
          ) in

  match act_tuple_subject_pairs with
    | Single f => isPrqAndPrq'_evalid e (right (right f)) (left (right f)) prin_u'
    | NewList f rest => (isPrqAndPrq'_evalid e (right (right f)) (left (right f)) prin_u') \/
                            (process_act_tuple_subject_pairs e prin_u' rest)
  end.


Definition process_pair_of_agreements (e:environment)(agr1 agr2: agreement) : Prop :=

  match agr1 with
  | Agreement prin_u a ps => 
      match agr2 with
      | Agreement prin_u' a' ps' => 
          (a<>a') \/ 
      let acts : nonemptylist act := getSminus ps in
      let sp_tuples : nonemptylist (Twos preRequisite fourTuple) := getSplusAsList ps' in
      let prin_diff : nonemptylist subject := getPrinsSetDifference prin_u' prin_u in   
      let sp_tuples_prin_u_list := process_two_lists sp_tuples prin_diff in
      let act_sp_tuples_prin_u_list := process_two_lists acts sp_tuples_prin_u_list in

      process_act_tuple_subject_pairs e prin_u' act_sp_tuples_prin_u_list

      end
  end.

Fixpoint agreements_hold_in_at_least_one_E_relevant_model 
           (e:environment)
           (pairs_of_agreements : nonemptylist (Twos agreement agreement))
           (s:subject)(myact:act)(a:asset) : Prop :=

  (env_consistent e) /\

  match pairs_of_agreements with 
    | Single agr_pair  => process_pair_of_agreements e (left agr_pair) (right agr_pair)
    | NewList agr_pair rest_pairs => (process_pair_of_agreements e (left agr_pair) (right agr_pair) \/
                                      agreements_hold_in_at_least_one_E_relevant_model e rest_pairs s myact a)
  end.


End Lemma45.


Fixpoint isPrqs_evalid (e:environment)(s:subject)(pr: prin)
                       (tups:nonemptylist (Twos preRequisite fourTuple)) : Prop :=
  let isPrqAndPrq'_evalid 
    := (fix isPrqAndPrq'_evalid 
            (e:environment)(s:subject)(t:Twos preRequisite fourTuple)(pr: prin): Prop :=
          (trans_preRequisite e s (left t)            (tt_I (right t))           pr) /\
          (trans_preRequisite e s (tt_prq' (right t)) (Single (tt_id (right t))) pr) 
          ) in
  match tups with
    | Single t =>  isPrqAndPrq'_evalid e s t pr
    | NewList t lst' => (isPrqAndPrq'_evalid e s t pr) \/ (isPrqs_evalid e s pr lst')
  end.


(** Use Lemma 4.2 to decide evalidity when there is one agreement only (the SingletonQuery case)
    Otherwise, we fall into Theorem 4.6: Run Lemma 4.5. If set of agreememnts do not hold 
    in any E-relevant model, return "Query Inconsistent". If they do, then run Lemma 4.2 recursively 
    for each agreement until either fplus is evalid for SOME agreement or NONE is evalid in which
    case, fplusq for A is not evalid
**)


Definition is_fplus_single_query_evalid (q: single_query) : Prop :=  
  match q with    
    | SingletonQuery agr s action a e => 
      match agr with 
        | Agreement prn a' ps => 
            ((~env_consistent e) \/
             ((is_subject_in_prin s prn) /\ (a=a') /\ 
              (* There is a Tuple in Splus s.t. is_evalid (prq/\prq') *)
              let sp := getSplus ps in
                match sp with
                  | Splus lst => (isPrqs_evalid e s prn lst)
                end))
      end                
  end.




Definition is_fminus_single_query_evalid (q: single_query) : Prop :=  

  let getExclusivePolicySet := 
    (fix getExclusivePolicySet (agr: agreement) : Prop :=
      match agr with
        | Agreement prin_u a ps => 
            match ps with                                               
              | PrimitiveExclusivePolicySet prq p => 
                  match p with
                    | PrimitivePolicy prereq pid action => True
                    | _ => False
                  end
              | _ => False
            end
      end) in

  match q with    
    | SingletonQuery agr s action a e => 
      match agr with 
        | Agreement prn a' ps => 
            (** Note that X -> False is the same as ~X **)
            (~env_consistent e) \/
            (~(is_subject_in_prin s prn) /\ (a=a') /\ 
              (* agr includes an exclusive policy set that mentions a policy of the form prq=>act *)
              (getExclusivePolicySet agr))
      end                              
  end.

(*** 
     Agreement says that TheReport may be printed a total of 5 times by Alice
     The Env says that Alice has already printed TheReport 2 times.
     So the answer to query: May Alice print TheReport should be YES or another 
     way of saying that is that fqplus is evalid (well not quite, as we need to 
     follow the whole algorithms and look at fqminus as well) 
***)


Definition single_q2: single_query := make_single_query AgreeCan Alice Print TheReport eA1.
Eval compute in (eA1). 
Eval compute in (env_consistent eA1).
Eval compute in (is_fplus_single_query_evalid single_q2).


Definition q_May_Bob_Print_LoveAndPeace: single_query := 
  make_single_query AgreeA5 Bob Print LoveAndPeace eA5.

Definition q_May_Alice_Print_LoveAndPeace: single_query := 
  make_single_query AgreeA5 Alice Print LoveAndPeace eA5.

Definition q_May_Bob_Print_FindingNemo: single_query := 
  make_single_query AgreeA5 Bob Print FindingNemo eA5.


Eval compute in (eA5).
Eval compute in (env_consistent eA5).
(* fminusq is NOT evalid *)
Eval compute in (is_fminus_single_query_evalid q_May_Bob_Print_LoveAndPeace). 

(* fminusq is evalid *)
Eval compute in (is_fminus_single_query_evalid q_May_Alice_Print_LoveAndPeace). 

(**** since both fminusq and fplusq are NOT evalid, permission is UNREGULATED ***)
(* fminusq is NOT evalid  *)
Eval compute in (is_fminus_single_query_evalid q_May_Bob_Print_FindingNemo). 
(* fplusq is NOT evalid  *)
Eval compute in (is_fplus_single_query_evalid q_May_Bob_Print_FindingNemo). 


Definition queryInconsistent (e:environment)
                               (agrs: nonemptylist agreement)
                               (s:subject)(action:act)(a:asset) : Prop :=
  ~agreements_hold_in_at_least_one_E_relevant_model e (get_list_of_pairs_of_agreements agrs) s action a.

(** 
 permissionGranted and permissionDenied are very inefficient right now 
 since they do the same computation but it is ok for now as efficiency 
 is the not the main point
**)

(**

Single agr => fplus /\ ~fminus
Newlist agr rest => (fplus \/ Granted) /\ (~(fminus \/ Granted))

**)
Fixpoint permissionGranted (e:environment)
                           (agrs: nonemptylist agreement)
                           (s:subject)(action:act)(a:asset) : Prop :=
      match agrs with
           | Single agr  =>  
		       is_fplus_single_query_evalid (SingletonQuery agr s action a e) /\ 
			  (~is_fminus_single_query_evalid (SingletonQuery agr s action a e))
			  
           | NewList agr rest => 
		       (((is_fplus_single_query_evalid (SingletonQuery agr s action a e)) \/ 
                         (permissionGranted e rest s action a)) /\
			~((is_fminus_single_query_evalid (SingletonQuery agr s action a e)) \/
                         (permissionGranted e rest s action a)))
      end.    

(**

Single agr => ~fplus /\ fminus
Newlist agr rest => (~(fplus \/ Denied)) /\ (fminus \/ Denied)

**)

Fixpoint permissionDenied (e:environment)
                          (agrs: nonemptylist agreement)
                          (s:subject)(action:act)(a:asset) : Prop :=
      match agrs with
           | Single agr  =>  
		       (~is_fplus_single_query_evalid (SingletonQuery agr s action a e) /\ 
			 is_fminus_single_query_evalid (SingletonQuery agr s action a e))
			  
           | NewList agr rest => 
		       (~((is_fplus_single_query_evalid (SingletonQuery agr s action a e)) \/ 
                         (permissionDenied e rest s action a)) /\
			((is_fminus_single_query_evalid (SingletonQuery agr s action a e)) \/
                         (permissionDenied e rest s action a)))
      end.    





Definition permissionUnregulated (e:environment)
                                 (agrs: nonemptylist agreement)
                                 (s:subject)(action:act)(a:asset) : Prop :=

~((queryInconsistent e agrs s action a) \/
  (permissionGranted e agrs s action a) \/
  (permissionDenied e agrs s action a)).

(** 
Now for the real hard stuff:
We can start theorems like : query q56 results in permissionUnregulated or permissionGranted
Or more generally: we want to state and prove that all queries in ODRL0 result in one of 
permissionGranted, permissionDenied, permissionUnregulated or queryInconsistent
**)   

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



Section Sanity1.

Theorem f1_and_f2_are_inconsistent: inconsistent f1 f2.
Proof. unfold inconsistent. simpl. omega. Qed.

Theorem f1_and___env_of_f2_inconsistent: formula_inconsistent_with_env f1 (SingleEnv f2).
Proof. unfold formula_inconsistent_with_env. apply f1_and_f2_are_inconsistent. Qed.


Theorem two_inconsistent_formulas_imply_env_inconsistent: 
  forall f g, inconsistent f g -> ~env_consistent (ConsEnv f (SingleEnv g)).
Proof. intros. unfold not. intros H'. 
inversion H'. intuition. intuition. Qed.


Theorem e2_is_inconsistent: ~env_consistent e2.
Proof.

apply two_inconsistent_formulas_imply_env_inconsistent. 
apply f1_and_f2_are_inconsistent. Qed.

Lemma NPeirce : forall (P : Prop), (P -> ~P) -> ~P.
auto. 
Qed.

Theorem env_consistent_implies_two_consistent_formulas: 
  forall (f g: count_equality), 
    env_consistent (ConsEnv f (SingleEnv g))-> ~inconsistent f g.
Proof. intros. inversion H. exact H1. intuition. Qed.

Theorem two_consistent_formulas_imply_env_consistent: 
  forall (f g: count_equality), 
    ~inconsistent f g -> env_consistent (ConsEnv f (SingleEnv g)).
Proof. intros. apply consis_2. exact H. Qed.

SearchAbout count_equality.

Check count_equality_ind.

Theorem env_inconsistent_implies_two_inconsistent_formulas: 
  forall (f g: count_equality), 
    ~env_consistent (ConsEnv f (SingleEnv g))-> inconsistent f g.
(** using elim on an hypothesis of the shape ~ P, 
    you say to Coq "I know that P holds, so using P -> False, 
    I can derive a proof of False" which closes the goal by contradiction. 
    That's why each time you elim a ~ P, Coq asks you to provide a proof of P.
**)
Proof.
induction f.
induction g.
unfold inconsistent.
intros.
subst.
generalize (dec_eq_nat n n0).
intro h; elim h.
intro; subst.
elim H.
apply consis_2.
unfold inconsistent.
intro.
assert (s0=s0); auto.
assert (p0=p0); auto.
specialize H0 with (1:=H1) (2:=H2).
elim H0; auto.
auto.
Qed.


Theorem theo1 : forall (s1 s2: subject),
                forall (id1 id2: policyId),
                forall (n1 n2: nat),

  (s1 = s2 /\ id1 = id2 /\ n1 <> n2) -> 
  inconsistent (CountEquality s1 id1 n1) (CountEquality s2 id2 n2).

Proof. intros. unfold inconsistent. intros. intuition. Qed.

Fixpoint app_envs (e e' : environment) : environment := 
  match e with
  | SingleEnv f  => ConsEnv f e'
  | ConsEnv f rest_env => ConsEnv f (app_envs rest_env e')
  end.

Definition count_equality_equal (f1 f2:count_equality) : Prop :=
  match f1 with (CountEquality s1 id1 n1) =>
     match f2 with (CountEquality s2 id2 n2) =>       
       s1 = s2 -> id1 = id2 -> n1 = n2
     end 
   end.
    

Theorem count_equality_equal_refl: forall (a : count_equality), count_equality_equal a a.
Proof. intros. destruct a. simpl. intuition. Qed. 



Fixpoint mem_countform_in_env (a:count_equality)(e : environment) : Prop :=
 match e with
  | SingleEnv f  => count_equality_equal f a
  | ConsEnv f rest_env => (count_equality_equal f a) \/ 
                          (mem_countform_in_env a rest_env)
  end.
  
SearchAbout env_consistent.


Theorem theo4_1: forall (c: count_equality), mem_countform_in_env c (SingleEnv c).
Proof. induction c. unfold mem_countform_in_env. apply count_equality_equal_refl. Qed.

(***
Theorem theo4_2: forall (e : environment),
                 forall (a : count_equality), mem_countform_in_env a (ConsEnv a e).
Proof. Abort.

Theorem theo4: forall (e : environment),
               forall (a: count_equality),
               ~(env_consistent (ConsEnv a e)) -> 
                (env_consistent e) \/ (~(env_consistent e)).

Proof. induction e. intros. 

left. apply consis_1. intros. right. case 


left. specialize (IHe c). 
apply consis_more. generalize H. apply H. 

apply env_inconsistent_implies_two_inconsistent_formulas in H.  

exists c. intuition. intros. left. exists c. induction e in IHe. 

apply .


destruct H. apply consis_more. .

apply env_inconsistent_implies_two_inconsistent_formulas in H. 
apply theo4_1. 

split. simpl. left. apply count_equality_equal_refl.
split. simpl. right. apply count_equality_equal_refl.  
unfold not in H. Abort.



Theorem theo5: forall (e e': environment),
               ~(env_consistent e) ->
               ~(env_consistent (app_envs e e')).

Proof. intros e. induction e'. intros H. Abort.


Theorem theo6: forall (f g: count_equality),
               forall (e: environment), 
inconsistent f g -> ~env_consistent (ConsEnv f ((ConsEnv g) e)).

Proof. intros. unfold not. intros H'. 

inversion H'. intuition. intuition. Abort.


*)

Axiom e_is_consistent: forall (e:environment), env_consistent e.


Theorem theo9_1 : forall (e:environment), 
                forall (agr: agreement),
                forall (s:subject),
                forall (action:act),
                forall (a:asset),

(is_fplus_single_query_evalid (SingletonQuery agr s action a e) /\
~is_fminus_single_query_evalid (SingletonQuery agr s action a e)) ->

~
(~ is_fplus_single_query_evalid (SingletonQuery agr s action a e) /\
 is_fminus_single_query_evalid (SingletonQuery agr s action a e)).


Proof. intros. unfold not. intro. 
destruct H as [H11 H12]. destruct H0 as [H01 H02]. unfold not in H12. elim H12. exact H02. Qed.


(***

'Functional Scheme' is used with 
'functional induction' in a proof script as in

Functional Scheme permissionGranted_ind := Induction for permissionGranted Sort Prop.

Proof.
...
functional induction permissionGranted e agrs s action a.
...
Qed.

***)

Functional Scheme is_subject_in_prin_ind := Induction for is_subject_in_prin Sort Prop. 
Functional Scheme permissionGranted_ind := Induction for permissionGranted Sort Prop.
Functional Scheme permissionDenied_ind := Induction for permissionDenied Sort Prop.

Theorem theo9_2: forall (e:environment), 
                forall (agr: agreement),
                forall (s:subject),
                forall (action:act),
                forall (a:asset),

((permissionDenied e [agr] s action a) ->
(~is_fplus_single_query_evalid (SingletonQuery agr s action a e) /\ 
 is_fminus_single_query_evalid (SingletonQuery agr s action a e)))

/\

((~is_fplus_single_query_evalid (SingletonQuery agr s action a e) /\ 
 is_fminus_single_query_evalid (SingletonQuery agr s action a e)) ->

(permissionDenied e [agr] s action a)).

Proof. intros. split. 

unfold permissionDenied. apply iff_refl.
unfold permissionDenied. apply iff_refl. Qed.

Theorem theo9_2_A: forall (e:environment), 
                forall (agr: agreement),
                forall (s:subject),
                forall (action:act),
                forall (a:asset),

((permissionDenied e [agr] s action a) ->
(~is_fplus_single_query_evalid (SingletonQuery agr s action a e) /\ 
 is_fminus_single_query_evalid (SingletonQuery agr s action a e))).

Proof. unfold permissionDenied. intros. exact H. Qed.

Theorem theo9_2_B: forall (e:environment), 
                forall (agr: agreement),
                forall (s:subject),
                forall (action:act),
                forall (a:asset),

((~is_fplus_single_query_evalid (SingletonQuery agr s action a e) /\ 
 is_fminus_single_query_evalid (SingletonQuery agr s action a e)) ->
(permissionDenied e [agr] s action a)).
Proof. unfold permissionDenied. intros. exact H. Qed.

Theorem theo9_3: forall (e:environment), 
                forall (agr: agreement),
                forall (s:subject),
                forall (action:act),
                forall (a:asset),

((permissionGranted e [agr] s action a) ->
(is_fplus_single_query_evalid (SingletonQuery agr s action a e) /\ 
 ~is_fminus_single_query_evalid (SingletonQuery agr s action a e)))

/\

((is_fplus_single_query_evalid (SingletonQuery agr s action a e) /\ 
 ~is_fminus_single_query_evalid (SingletonQuery agr s action a e)) ->
(permissionGranted e [agr] s action a)).

Proof. intros. split. 

unfold permissionGranted. apply iff_refl.
unfold permissionGranted. apply iff_refl. Qed.

Theorem theo9_3_A: forall (e:environment), 
                forall (agr: agreement),
                forall (s:subject),
                forall (action:act),
                forall (a:asset),

((permissionGranted e [agr] s action a) ->
(is_fplus_single_query_evalid (SingletonQuery agr s action a e) /\ 
 ~is_fminus_single_query_evalid (SingletonQuery agr s action a e))).
Proof. unfold permissionGranted. intros. exact H. Qed.


Theorem theo9_3_B: forall (e:environment), 
                forall (agr: agreement),
                forall (s:subject),
                forall (action:act),
                forall (a:asset),

((is_fplus_single_query_evalid (SingletonQuery agr s action a e) /\ 
 ~is_fminus_single_query_evalid (SingletonQuery agr s action a e)) ->
(permissionGranted e [agr] s action a)).
Proof. unfold permissionGranted. intros. exact H. Qed.

Theorem theo9_4_A : forall (e:environment), 
                forall (agr: agreement),
                forall (s:subject),
                forall (action:act),
                forall (a:asset),
 
(permissionGranted e [agr] s action a) -> ~(permissionDenied e [agr] s action a).

Proof.

intros e agr s action a. intro. apply theo9_3_A in H. unfold not. intro.
apply theo9_2_A in H0. intuition. Qed. 

Theorem theo9_4_B : forall (e:environment), 
                forall (agr: agreement),
                forall (s:subject),
                forall (action:act),
                forall (a:asset),
 
(permissionDenied e [agr] s action a) -> ~(permissionGranted e [agr] s action a).

Proof.
Show Proof.
intros e agr s action a. 
Show Proof.
intro. 
Show Proof.
apply theo9_2_A in H. 
Show Proof.
unfold not.
Show Proof. 
intro.
Show Proof.
apply theo9_3_A in H0. 
Show Proof.
intuition. 
Show Proof.
Qed. 


Theorem theo10 : forall (e:environment), 
                forall (agrs: nonemptylist agreement),
                forall (s:subject),
                forall (action:act),
                forall (a:asset),
 
(permissionGranted e agrs s action a) -> ~(permissionDenied e agrs s action a).

Proof.

induction agrs as [| agr rest]. 

(*

apply theo9_4_A.

OR

intros.intuition.unfold permissionDenied in H0.unfold permissionGranted in H.intuition.

Both work.
*)

apply theo9_4_A.


intros.
intuition.
unfold permissionDenied in H0.
unfold permissionGranted in H.
intuition.
Qed.


(*
intros e agrs s action a.
functional induction permissionGranted e agrs s action a.

intros.

inversion e5. rewrite <- H1 in H. rewrite <- H1.

functional induction permissionDenied e [agr] s action a. inversion e6. rewrite <- H2. inversion e5. 
rewrite <- H1 in H3. rewrite <- H2 in H3. rewrite -> H3. 

unfold not. destruct H as [H11 H12]. intro. destruct H as [H21 H22]. elim H21. exact H11.

unfold not. intro. destruct H0 as [H01 H02]. elim H01. inversion e6.

unfold not. intro. destruct H0 as [H01 H02]. apply H01. inversion e6.

unfold not. intro. destruct H0 as [H01 H02]. apply H01. inversion e5.

intro. inversion e5. 

intro. inversion e5.

intro. inversion e5. destruct H as [H11 H12]. Admitted.
*)

Theorem aliceMayPrintTheReportGivenAgreeCan : (trans_agreement eA1 AgreeCan) -> permissionGranted eA1 [AgreeCan] Alice Print TheReport.
Proof. 

simpl. intro.

intuition. elim H1. apply e_is_consistent. Qed.



Functional Scheme agreements_hold_in_at_least_one_E_relevant_model_ind := 
  Induction for agreements_hold_in_at_least_one_E_relevant_model Sort Prop.
(*
Functional Scheme trans_ps_ind := 
  Induction for trans_ps Sort Prop.
*)

Theorem PP1: forall (P Q:Prop), (P->True->True->Q) -> (P->Q).                              
Proof. intros. apply H. exact H0. auto. auto. Qed.


Theorem PP2: forall (P Q:Prop), (P->Q) -> (P->True->True->Q).
Proof. intros. apply H. exact H0. Qed.
(** 
If p -> q, we know two things: 
modus ponens says that if p is true, then q must be true. 
Modus tollens (MT) says that if q is false, then p must be false.
**)

Theorem ModesT: forall (P Q: Prop), ~Q /\ (P -> Q) -> ~P.
Proof.
intro P.
intro Q.
intro HNQPQ.
destruct HNQPQ as [HNQ HPQ].
intro HP.
(**
The tactic generalize takes as input a term t (for instance, 
a proof of some proposition) and then changes the conclusion 
from G to T -> G, 
where T is the type of t (for instance, the proposition proved by the proof t).

Here 'generalize (HPQ HP)' applies HPQ to HP resulting in Q. the generlize changes the 
goal from False to Q -> False.
**)
generalize (HPQ HP).
intro HQ. 
contradiction.
Qed.


Hypothesis Q: Charlie <> Alice.
Hypothesis T: Charlie <> Bob.

(****
Theorem example4_3_is_QueryInconsistent : 
(((trans_agreement e_agr agr) /\ (trans_agreement e_agr agr')) -> 
permissionGranted e_agr (NewList agr (Single agr')) Charlie Print TheReport) /\
(((trans_agreement e_agr agr) /\ (trans_agreement e_agr agr')) -> 
permissionDenied e_agr (NewList agr (Single agr')) Charlie Print TheReport).



Proof.  intuition.

destruct agr in H0. unfold trans_agreement in H0. 
destruct agr' in H1. unfold trans_agreement in H1.


functional induction permissionGranted e_agr (agr, [agr']) Charlie Print TheReport.

split.


unfold is_fplus_single_query_evalid. induction agr0. induction getSplus.
intuition. right. intuition.
generalize (H0).
functional induction trans_agreement e_agr agr.

specialize (H0 Charlie). specialize (H1 Charlie). intuition. 

right. intuition. 
apply PP1 with (P:=(Charlie = Alice)) (Q:=(Permitted Charlie Print TheReport)) in H2. 
apply PP1 with (P:=(Charlie = Bob)) (Q:=(Permitted Charlie Print TheReport)) in H0.
clear H0. right. split.

generalize (T). 

intuition. intuition. intuition. 

elim H1. simpl.
generalize (Q).

apply (ModesT (Charlie = Bob) (Permitted Charlie Print TheReport) (conj H1 H0)). 
apply H2. 
intuition.

****)


(****

Theorem example4_3_is_QueryInconsistent2 : 
(trans_agreement e_agr agr) -> (trans_agreement e_agr agr') -> 
queryInconsistent e_agr (NewList agr (Single agr')) Charlie Print TheReport.
Proof.


unfold queryInconsistent. intros Q T.



unfold not. 

functional induction agreements_hold_in_at_least_one_E_relevant_model e_agr
 (get_list_of_pairs_of_agreements (agr, [agr'])) Charlie Print TheReport. 

intro.

destruct H as [H1 H2].  

simpl.
auto. intuition.
unfold trans_agreement in Q.






simpl. intros Q T. intuition. 
unfold queryInconsistent. unfold not. unfold agreements_hold_in_at_least_one_E_relevant_model. 
simpl. intro. Show Proof.
destruct H as [H1 H2]. intuition. Show Proof.
specialize (Q Charlie). specialize (T Charlie).
intuition.

elim H3.

intro. intuition. 
assert (Charlie <> Bob). eauto. 

destruct H0 as [H01 H02].
****)

End Sanity1.

Theorem allQueriesWillGetAnAnswer: forall (e:environment), 
                forall (agr: agreement),
                forall (s:subject),
                forall (action:act),
                forall (a:asset),

(permissionGranted e [agr] s action a) \/
(permissionDenied e [agr] s action a)  \/
(queryInconsistent e [agr] s action a) \/
(permissionUnregulated e [agr] s action a).
                                 

End ODRL.
