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

Definition mylist2 := 1 , 2 , [3].

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

(*
Eval compute in
fold_nonempty (fun x y => x + y) 0 lst1.
*)

Definition lst2 := process_two_lists (NewList 91 (Single 92)) (NewList 3 (NewList 2 (Single 1))).
Eval compute in lst2.





Definition subject := nat.


Inductive prin : Set :=
  | Prin : subject -> prin 
  | Prins : nonemptylist prin -> prin. 


Definition myprin1 := Prin 5.
Check myprin1.
Definition myprin_list := NewList myprin1 (Single (Prin 2)).
Definition myprins := Prins myprin_list.
Check myprins.

Definition act := nat.
Definition Play := 1.
Definition Print := 2.
Definition Display := 3.

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
  | ForEachMember : prin  -> nonemptylist (constraint ) -> constraint 
  | Count : nat -> constraint 
  | CountByPrin : prin -> nat -> constraint.

(*
Inductive policyId : Set :=
  | PolicyId : nat -> policyId.
*)
  
Inductive preRequisite : Set :=
  | TruePrq : preRequisite
  | Constraint : constraint -> preRequisite 
  | Requirement : requirement -> preRequisite 
  | Condition : cond -> preRequisite 
  | AndPrqs : nonemptylist (preRequisite) -> preRequisite
  | OrPrqs : nonemptylist (preRequisite) -> preRequisite
  | XorPrqs : nonemptylist (preRequisite) -> preRequisite

with cond : Set :=
  | SuspendPS : policySet -> cond
  | SuspendConstrint : constraint -> cond

with policySet : Set :=
  | PrimitivePolicySet : preRequisite -> policy -> policySet 
  | PrimitiveExclusivePolicySet : preRequisite -> policy  -> policySet 
  | AndPolicySet : nonemptylist (policySet) -> policySet

with policy : Set :=
  | PrimitivePolicy : preRequisite -> policyId -> act -> policy 
  | AndPolicy : nonemptylist (policy) -> policy.


Inductive agreement : Set :=
  | Agreement : prin -> asset -> policySet -> agreement.

Definition const1 := Count 5.
Definition preReq1 := Constraint const1.
Definition policyId1 := 12.
Definition act1 := Print.
Check preReq1.
Check PrimitivePolicy.
Check (Constraint (Count 5)).



(*  
preReq1 : preRequisite nat
PrimitivePolicy : forall X : Type, list (preRequisite X) -> policyId -> act -> policy X 
Constraint : forall X : Type, constraint X -> preRequisite X
*)
Definition p1 := PrimitivePolicy (Constraint (Count 5)) policyId1 act1.

Check length.
Print length.

Definition makePrimitivePolicy (prq : preRequisite) (id : policyId) (ac : act) : policy :=
  PrimitivePolicy prq id ac.
  

Definition p2 := makePrimitivePolicy (Constraint (Count 7)) 22 Print.

Definition p3 := makePrimitivePolicy (Constraint (Count 8)) 23 Display.

Inductive user : Set :=
  | Alice : user
  | Bob : user
  | Charlie : user
  | David : user
  | Alex : user.




(* First, you need to introduce the predicates.  Here is one example. *)

(* 
Assumptions extend the environment with axioms, parameters, hypotheses or variables. An assumption binds an ident to a type. It is accepted by Coq if and only if this type is a correct type in the environment preexisting the declaration and if ident was not previously defined in the same module. This type is considered to be the type (or specification, or statement) assumed by ident and we say that ident has type type.

Axiom ident :term .

This command links term to the name ident as its specification in the global context. The fact asserted by term is thus assumed as a postulate.


Parameter ident :term. 
Is equivalent to Axiom ident : term
*)

Parameter Permitted : subject -> act -> asset -> Prop.


(* The following 2 definitions implement the translation of a
   principle to a formula.  I implemented these 2 in full to give you
   a complete example.  The first illustrates recursive function definitions
   in Coq. *)

(******
If a fixpoint is not written with an explicit { struct ... }, then 
all arguments are tried successively (from left to right) until one is 
found that satisfies the structural decreasing condition.
*******)


(* is x in prin? *)
Fixpoint trans_prin
  (x: subject)(p: prin) : Prop :=

let trans_prin_list := (fix trans_prin_list (x: subject)(prins: nonemptylist prin){struct prins} : Prop :=
  match prins with
    | Single s => trans_prin x s
    | NewList s prins' => ((trans_prin x s) \/ trans_prin_list x prins')
  end) in

  match p with
    | Prin s => (x=s)      
    | Prins prins => trans_prin_list x prins
  end.





(* This definition is what needs to be filled in.  It shows the
   general structure of mutually recursive functions in Coq.  It
   defines 6 functions mutually recursively, but I didn't try to get
   them all.  There are probably some missing.  You will also probably
   want to implement some helper functions outside the structure of
   this recursive definition.  In each case there are a bunch of
   arguments in parentheses, followed by a "struct" declaration, which
   indicates which argument the recursion will be on.  The result
   "True" must be filled in with the real definition.  Notice that
   some functions have a regular and a list version.  The list version
   needs to call the regular version on every element of the list,
   similar to how trans_prin_list above works. *)


Definition getIds (p:policy) : nonemptylist policyId := Single 2.
                 
Check getIds.

Definition getPrincipals (prn : prin) : nonemptylist prin :=
  match prn with
    | Prin s => Single prn
    | Prins prin_list => prin_list
  end.

Check getPrincipals.





Fixpoint trans_preRequisite_list
  (x:subject)(preReqs:nonemptylist preRequisite)(IDs:list policyId)
  (Ss:list subject){struct preReqs} : Prop := 
  True.


(* 
Fixpoint trans_forEachMember
  (x:subject)(principals: nonemptylist prin)(const_list:nonemptylist constraint)
  (IDs:nonemptylist policyId)(a:asset){struct const_list} : Prop := 
  True
*)

(*
subjects(s) => {s}
subjects({prin1, . . . , prink}) => subjects(prin1) + ... + subjects(prink)
*)

Fixpoint getSubjects (prn : prin) : nonemptylist subject :=
let getSubjectsAux 
  := (fix getSubjectsAux 
        (prins_list : nonemptylist prin) :=
            match prins_list with
              | Single prn => getSubjects prn
              | NewList prn prn_list =>  app_nonempty (getSubjects prn) (getSubjectsAux prn_list)
            end) in

  match prn with
    | Prin s => Single s
    | Prins prin_list => getSubjectsAux prin_list
  end.


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
  
  let ids_and_subjects := process_two_lists IDs (getSubjects prin_u) in
  let running_total := trans_count_aux ids_and_subjects in
  running_total < n.
  
Fixpoint trans_constraint 
  (x:subject)(const:constraint)(IDs:nonemptylist policyId)
  (prin_u:prin)(a:asset){struct const} : Prop := 
  
  
  let trans_const_list 
    := (fix trans_const_list 
         (x:subject)(const_list:nonemptylist constraint)
	 (IDs:nonemptylist policyId)(prin_u:prin)(a:asset){struct const_list} :=
     match const_list with
       | Single const1 => trans_constraint x const1 IDs prin_u a
       | NewList const const_list' => ((trans_constraint x const IDs prin_u a) /\ (trans_const_list x const_list' IDs prin_u a))
     end) in
(*
let trans_forEachMember_Aux   
  := (fix trans_forEachMember_Aux
         (x:subject)(prins_and_constraints : nonemptylist (Twos prin constraint))
         (IDs:nonemptylist policyId)(a:asset) {struct prins_and_constraints} : Prop :=

      match prins_and_constraints with
        | Single pair1 => trans_constraint x (right pair1) IDs (left pair1) a
        | NewList pair1 rest_pairs =>
            (trans_constraint x (right pair1) IDs (left pair1) a) /\
            (trans_forEachMember_Aux x rest_pairs IDs a)
      end) in

let trans_forEachMember
  := (fix trans_forEachMember
         (x:subject)(principals: nonemptylist prin)(const_list:nonemptylist constraint)
         (IDs:nonemptylist policyId)(a:asset){struct const_list} : Prop := 

      let prins_and_constraints := process_two_lists principals const_list in
      trans_forEachMember_Aux x prins_and_constraints IDs a) in

*)    
  match const with
    | Principal prn => trans_prin x prn

    | ForEachMember prn const_list => True (*trans_forEachMember x (getPrincipals prn) const_list IDs a*)
  
    | Count n => trans_count x n IDs prin_u a

    | CountByPrin prn n => True

  end.

(*
with trans_requirment
(x:subject)(prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin)(a:asset){struct prq} : Prop := 
  True
with trans_condition
(x:subject)(prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin)(a:asset){struct prq} : Prop := 
  True
with trans_andPrqs
(x:subject)(prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin)(a:asset){struct prq} : Prop := 
  True
with trans_orPrqs
(x:subject)(prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin)(a:asset){struct prq} : Prop := 
  True
with trans_xorPrqs
(x:subject)(prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin)(a:asset){struct prq} : Prop := 
  True
*)
Fixpoint trans_preRequisite
  (x:subject)(prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin)(a:asset){struct prq} : Prop := 
  match prq with
    | TruePrq => True
    | Constraint const => trans_constraint x const IDs prin_u a 
    | Requirement req => True (*trans_requirment x prq IDs prin_u a*)
    | Condition cond => True (*trans_condition x prq IDs prin_u a*)
    | AndPrqs prqs => True (*trans_andPrqs x prq IDs prin_u a*)
    | OrPrqs prqs => True (*trans_orPrqs x prq IDs prin_u a*)
    | XorPrqs prqs => True (*trans_xorPrqs x prq IDs prin_u a*)
  end

   
with trans_policy_positive
  (x:subject)(p:policy)(prin_u:prin)(a:asset){struct p} :=

let trans_p_list := (fix trans_p_list (x:subject)(p_list:nonemptylist policy)(prin_u:prin)(a:asset){struct p_list}:=
                  match p_list with
                    | Single p1 => trans_policy_positive x p1 prin_u a
                    | NewList p p_list' => ((trans_policy_positive x p prin_u a) /\ (trans_p_list x p_list' prin_u a))
                  end) in


  match p with
    | PrimitivePolicy prq policyId action => ((trans_preRequisite x prq (Single policyId) prin_u a) ->
                                              (Permitted x action a))
    | AndPolicy p_list => trans_p_list x p_list prin_u a
  end




with trans_policy_negative
  (x:subject)(p:policy)(a:asset){struct p} :=
let trans_p_list := (fix trans_p_list (x:subject)(p_list:nonemptylist policy)(a:asset){struct p_list}:=
                  match p_list with
                    | Single p1 => trans_policy_negative x p1 a
                    | NewList p p_list' => ((trans_policy_negative x p a) /\ (trans_p_list x p_list' a))
                  end) in


  match p with
    | PrimitivePolicy prq policyId action => not (Permitted x action a)
    | AndPolicy p_list => trans_p_list x p_list a
  end

(*
I had to define trans_ps_list as a 'let' inside of trans_ps otherwise I was getting the:
"Recursive call to trans_ps has principal argument equal to "ps1" instead of
a subterm of "ps_list"." error.

This solution was found here: 
http://cs.stackexchange.com/questions/104/recursive-definitions-over-an-inductive-type-with-nested-components

*)
with trans_ps
  (x:subject)(ps:policySet)(prin_u:prin)(a:asset){struct ps} :=

let trans_ps_list := (fix trans_ps_list (x:subject)(ps_list:nonemptylist policySet)(prin_u:prin)(a:asset){struct ps_list}:=
                  match ps_list with
                    | Single ps1 => trans_ps x ps1 prin_u a
                    | NewList ps ps_list' => ((trans_ps x ps prin_u a) /\ (trans_ps_list x ps_list' prin_u a))
                  end) in
  match ps with
    | PrimitivePolicySet prq p => (((trans_prin x prin_u) /\ 
                                    (trans_preRequisite x prq (getIds p) prin_u a)) -> 
                                   (trans_policy_positive x p prin_u a))
    | PrimitiveExclusivePolicySet prq p => ((((trans_prin x prin_u) /\ 
                                              (trans_preRequisite x prq (getIds p) prin_u a)) -> 
                                             (trans_policy_positive x p prin_u a)) /\

                                            ((not (trans_prin x prin_u)) -> (trans_policy_negative x p a)))
                   
    | AndPolicySet ps_list => trans_ps_list x ps_list prin_u a
  end.



Definition trans_agreement_aux :
  subject -> agreement -> Prop :=
    fun x a =>
      match a with 
        | Agreement prin_u a ps => trans_ps x ps prin_u a
      end.

(* This is the top level translation function.  It calls the one above *)
Definition trans_agreement : agreement -> Prop :=
  fun a =>
    forall (x:subject), trans_agreement_aux x a.

 
End ODRL.
