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
(** Definition aliceCount10:preRequisite := Constraint (CountByPrin prins2_6 10). **)
Definition aliceCount10:preRequisite := Constraint (CountByPrin (Single Alice) 10).
Definition primPolicy2_6:policy := PrimitivePolicy aliceCount10 "id3" Play.




(******* Semantics ********)

Section Sems.

Parameter Permitted : subject -> act -> asset -> Prop.
Parameter getCount : subject -> policyId -> nat.


(*** Environments: in odrl0 are simply a conjunction of positive ground literals of the form count(s, id)= n ***)


Definition clause := Prop.
(** A clause is a list (disjunction) of literals. *)

Definition formula := list clause. (** conjuction *)
(** A formula is a list (conjunction) of clauses. *)

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
  (x:subject)(const:constraint)(IDs:nonemptylist policyId)
  (prin_u:prin)(a:asset){struct const} : Prop := 
(*************************************************)
(*************************************************)
  match const with
    | Principal prn => trans_prin x prn
  
    | Count n => trans_count n IDs prin_u a

    | CountByPrin prn n => trans_count n IDs prn a

  end.




Fixpoint trans_forEachMember
         (x:subject)(principals: nonemptylist subject)(const_list:nonemptylist constraint)
         (IDs:nonemptylist policyId)(a:asset){struct const_list} : Prop := 

let trans_forEachMember_Aux   
  := (fix trans_forEachMember_Aux
         (prins_and_constraints : nonemptylist (Twos subject constraint))
         (IDs:nonemptylist policyId)(a:asset) {struct prins_and_constraints} : Prop :=

      match prins_and_constraints with
        | Single pair1 => trans_constraint x (right pair1) IDs (Single (left pair1)) a
        | NewList pair1 rest_pairs =>
            (trans_constraint x (right pair1) IDs (Single (left pair1)) a) /\
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




Definition trans_notCons
  (x:subject)(const:constraint)(IDs:nonemptylist policyId)(prin_u:prin)(a:asset) : Prop :=
  ~ (trans_constraint x const IDs prin_u a).

Definition trans_preRequisite
  (x:subject)(prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin)(a:asset) : Prop := 

  match prq with
    | TruePrq => True
    | Constraint const => trans_constraint x const IDs prin_u a 
    | ForEachMember prn const_list => trans_forEachMember x prn const_list IDs a
    | NotCons const => trans_notCons x const IDs prin_u a
    | AndPrqs prqs => True (*trans_andPrqs x prq IDs prin_u a*)
    | OrPrqs prqs => True (*trans_orPrqs x prq IDs prin_u a*)
    | XorPrqs prqs => True (*trans_xorPrqs x prq IDs prin_u a*)
  end.

Fixpoint trans_policy_positive
  (x:subject)(p:policy)(prin_u:prin)(a:asset){struct p} : Prop :=

let trans_p_list := (fix trans_p_list (p_list:nonemptylist policy)(prin_u:prin)(a:asset){struct p_list}:=
                  match p_list with
                    | Single p1 => trans_policy_positive x p1 prin_u a
                    | NewList p p_list' => 
                        ((trans_policy_positive x p prin_u a) /\ 
                         (trans_p_list p_list' prin_u a))
                  end) in


  match p with
    | PrimitivePolicy prq policyId action => ((trans_preRequisite x prq (Single policyId) prin_u a) ->
                                              (Permitted x action a))
    | AndPolicy p_list => trans_p_list p_list prin_u a
  end.

Fixpoint trans_policy_negative
  (x:subject)(p:policy)(a:asset){struct p} : Prop :=
let trans_p_list := (fix trans_p_list (p_list:nonemptylist policy)(a:asset){struct p_list}:=
                  match p_list with
                    | Single p1 => trans_policy_negative x p1 a
                    | NewList p p_list' => ((trans_policy_negative x p a) /\ 
                                            (trans_p_list p_list' a))
                  end) in


  match p with
    | PrimitivePolicy prq policyId action => not (Permitted x action a)
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
    | PrimitivePolicySet prq p => forall x, (((trans_prin x prin_u) /\ 
                                   (trans_preRequisite x prq (getId p) prin_u a)) -> 
                                   (trans_policy_positive x p prin_u a))  

    | PrimitiveExclusivePolicySet prq p => forall x, ((((trans_prin x prin_u) /\ 
                                              (trans_preRequisite x prq (getId p) prin_u a)) -> 
                                             (trans_policy_positive x p prin_u a)) /\
                                            ((not (trans_prin x prin_u)) -> (trans_policy_negative x p a)))
                   
    | AndPolicySet ps_list => trans_ps_list ps_list prin_u a
  end.


Fixpoint trans_agreement
   (ag:agreement) : Prop :=
   match ag with 
   | Agreement prin_u a ps => trans_ps ps prin_u a
   end.

  
(***** 3.1 *****)


Eval simpl in (trans_ps policySet2_5 prins2_5 ebook).

Eval compute in (trans_ps policySet2_5 prins2_5 ebook).




(*** Canonical Agreement example ***)
Section A1.

Definition psA1:policySet :=
  PrimitivePolicySet
    TruePrq
    (PrimitivePolicy (Constraint (Count  5)) "id1" Print).

Definition AgreeCan := Agreement (Single Alice) TheReport psA1.

Eval compute in (trans_agreement AgreeCan).

Hypothesis H: trans_agreement AgreeCan.
Hypothesis AliceCount : getCount Alice "id1" = 2.
Theorem SSS: Permitted Alice Print TheReport.
Proof. simpl in H. apply H. split. reflexivity. auto. rewrite AliceCount. auto. Qed.
End A1.



Section A2.

(**  getCount Alice "id1" = 5,  and see if you can prove ~(Permitted Alice ...). **)

Definition psA2:policySet :=
  PrimitivePolicySet
    TruePrq
    (PrimitivePolicy (Constraint (Count  5)) "id1" Print).

Definition AgreeA2 := Agreement (Single Alice) TheReport psA2.

Eval compute in (trans_agreement AgreeA2).

Hypothesis AliceCount : getCount Alice "id1" = 5.
Hypothesis H: trans_agreement AgreeA2.

Theorem SS1: (getCount "Alice" "id1") < 5 -> (Permitted Alice Print TheReport).
Proof. simpl in H. apply H. split. reflexivity. apply I. Qed.

Theorem SSS: ~(Permitted Alice Print TheReport).
Proof. simpl in H. rewrite AliceCount in H. unfold not.   

intro H'. generalize H. Abort.

End A2.



Section A3.

(***
Theorem FFF: 8<10.
Proof. apply le_S. apply le_n. Qed.
 
le_n : forall n : nat, n <= n
le_S : : forall n m : nat, n <= m -> n <= S m.
***)


Definition AgreeA3 := Agreement prins2_5 ebook policySet2_5.
Eval compute in (trans_agreement AgreeA3).

Hypothesis AliceDisplayCount : getCount Alice "id1" = 3.
Hypothesis AlicePrintCount : getCount Alice "id2" = 0.
Hypothesis BobDisplayCount : getCount Bob "id1" = 4.
Hypothesis BobPrintCount : getCount Bob "id2" = 0.
Hypothesis H: trans_agreement AgreeA3.

Theorem T1_A3: Permitted Alice Print ebook.
Proof. simpl in H. 
rewrite AliceDisplayCount in H.
rewrite AlicePrintCount in H.
rewrite BobDisplayCount in H.
rewrite BobPrintCount in H. simpl in H. apply H. intuition. intuition. Qed.


End A3.



Section A5.

Definition prin_bob := (Single Bob).
Definition pol:policy := PrimitivePolicy TruePrq "id3" Print.
Definition pol_set:policySet := PrimitiveExclusivePolicySet TruePrq pol.
Definition AgreeA5 := Agreement prin_bob LoveAndPeace pol_set.
Eval compute in (trans_agreement AgreeA5).

(* Not sure how to prove Alice<>Bob so for now, making it a hypo *)
Hypothesis H0: Alice <> Bob.

Hypothesis H: trans_agreement AgreeA5.


Theorem T1_A5: forall x, x<>Bob -> ~Permitted x Print LoveAndPeace.
Proof. simpl in H. apply H. Qed.

(*
Theorem T2_A5: ~Permitted Alice Print LoveAndPeace.
Proof. simpl in H. apply H. apply H0. Qed. 
*)
Theorem T2_A5: ~Permitted Alice Print LoveAndPeace.
Proof. apply T1_A5. apply H0. Qed. 

End A5.




End Sems.

Section Query.


(*
Definition env := list ((subject*policyId)*nat).


Fixpoint getCountFromEnv (e : env) (s : subject) (id:policyId) : nat :=
  match e with
    | nil => 0
    | cons first rest => (getCount s id) eq_nat (fst first) (snd first)) /\ (trans_env rest)
  end.
  getCount(.




Fixpoint trans_env (e : env) : Prop :=
  match e with
    | nil => True
    | cons first rest => (eq_nat (fst first) (snd first)) /\ (trans_env rest)
  end.


*)

Set Impicit Arguments.
Require Import Coq.Lists.List.
Require Omega.


(*

Definition subject := nat.


Check subject.
Check nat.

Definition Math := subject.

Check Math.

Definition A : Math := 7.

Check A.

*)

Inductive count_equality : Set := 
   | CountEquality : subject -> policyId -> nat -> count_equality.

Check count_equality.


Definition make_count_equality
  (s:subject)(id:policyId)(n:nat): count_equality :=
  CountEquality s id n.


Definition environment := list count_equality.


Definition f1:count_equality := make_count_equality "Alice" "4" 6.
Definition f2:count_equality := make_count_equality "Alice" "4" 7.


Definition inconsistent (f1 f2 : count_equality) : Prop :=
   match f1 with (CountEquality s1 id1 n1) =>
     match f2 with (CountEquality s2 id2 n2) =>       
       s1 = s2 -> id1 = id2 -> n1 <> n2
     end 
   end.

Eval compute in (inconsistent f1 f2).

Eval compute in (6 <> 7).

Definition E1 : environment := f1::f2::nil.



Inductive query : Set := 
   | Query : nonemptylist agreement -> subject -> act -> asset -> environment -> query.
(* a query is a tuple: (agreement * subject * act * asset * environment)  *)


Definition make_query 
  (agrs:nonemptylist agreement)(s:subject)(myact:act)(a:asset)(e:environment) : query :=
  Query agrs s myact a e.

Definition q1: query := make_query (Single AgreeA5) Alice Display TheReport E1. 

Check count_equality.

(********* TODO *********)
Example test_inconsistent: (inconsistent f1 f2) = (6<>7).
(* Proof. unfold inconsistent. simpl. intuition. *) Admitted. 


End Query.

End ODRL.
