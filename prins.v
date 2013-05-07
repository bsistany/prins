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


(*
Inductive subject (X:Set) : Set :=
  | Subject : X -> subject X.
*)
Definition subject := nat.


(*
Inductive money : Set :=
  | Money : nat -> money.
*)
Definition money := nat.



Inductive requirement : Set :=
  | PrePay : money -> requirement
  | Attribution : subject -> requirement
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


Fixpoint trans_prin_list
  (x:subject)(prins:nonemptylist){struct prins} : Prop :=
  match prins with
    | Single s => (x=s)      
    | NewList s prins' => (x=s \/ trans_prin_list x prins')      
  end.

Definition trans_prin
  (x:subject)(p:prin) : Prop :=
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

Fixpoint trans_preRequisite_list
  (x:subject)(preReqs:list preRequisite)(IDs:list policyId)
  (Ss:list subject){struct preReqs} : Prop := True
with trans_preRequisite
  (x:subject)(preReq:preRequisite)(IDs:list policyId)
  (Ss:list subject){struct preReq} : Prop := True
with trans_ps_list
  (x:subject)(pss:list policySet)(prin_u:prin)(a:asset){struct pss} :=
  True
with trans_ps
  (x:subject)(ps:policySet)(prin_u:prin)(a:asset){struct ps} :=
  True
with trans_policy_positive
  (x:subject)(p:policy)(prin_u:prin)(a:asset){struct p} :=
  True
with trans_policy_negative
  (x:subject)(p:policy)(prin_u:prin)(a:asset){struct p} :=
  True.

Definition trans_agreement_aux :
  subject nat -> agreement -> Prop :=
    fun x a =>
      match a with Agreement prin_o prin_u a ps => trans_ps x ps prin_u a
      end.

(* This is the top level translation function.  It calls the one above *)
Definition trans_agreement : agreement -> Prop :=
  fun a =>
    forall (x:subject nat), trans_agreement_aux x a.

 
End ODRL.
