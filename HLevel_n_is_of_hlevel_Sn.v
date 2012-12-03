

(** ** Ahrens, Kapulkin,  December 2012 *)


Require Import auxiliary_lemmas.
Require Import hProp.
Require Import funextfun.


Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).


(** We get a weak equivalence from univalence, which we wrap up in 
    a sigma-package *)

Definition univalenceweq (X X' : UU) : weq (X == X') (weq X X') :=
    tpair _ _ (univalenceaxiom X X').


(** ** Lemma: if [X] and [X'] are of hlevel [n], then so is their 
      identity type [X == X'] *)
(** The proof works differently for [n == 0] and [n == S n'],
    so we treat these two cases in separate lemmas and package
    everything nicely in the end. *)

(** *** The case [n == 0] *)

Lemma isofhlevel0weq (X Y : UU) :
    iscontr X -> iscontr Y -> weq X Y.
Proof.
  intros pX pY.
  set (wX := wequnittocontr pX).
  set (wY := wequnittocontr pY).
  exact (weqcomp (invweq wX) wY).
Defined.


Lemma isofhlevel0pathspace (X Y : UU) :
    iscontr X -> iscontr Y -> iscontr (X == Y).
Proof.
  intros pX pY.
  set (H := isofhlevelweqb 0 (univalenceweq X Y)).
  apply H.
  exists (isofhlevel0weq _ _ pX pY ).
  intro f.
  assert (H' : pr1 f == pr1 (isofhlevel0weq X Y pX pY)).
    apply funextfun.
    simpl. intro x. 
    apply (pr2 pY).
  apply (total2_paths H').
  apply proofirrelevance.
  apply isapropisweq.
Defined.



(** *** The case [n == S n'] *)

Lemma isofhlevelSnpathspace : forall n : nat, forall X Y : UU,
      isofhlevel (S n) X -> isofhlevel (S n) Y ->
          isofhlevel (S n) (X == Y).
Proof.
  intros n X Y pX pY.
  set (H:=isofhlevelweqb (S n) (univalenceweq X Y)).
  apply H.
  assert (H' : isofhlevel (S n) (X -> Y)).
    apply impred.
    intro x. assumption.
  assert (H2 : isincl (@pr1 (X -> Y) (fun f => isweq f))).
    apply isofhlevelfpr1.
    intro f. apply isapropisweq.
  apply (isofhlevelsninclb _ _ H2).
  assumption.
Qed.


(** ** The lemma itself *)

Lemma isofhlevelpathspace : forall n : nat, forall X Y : UU,
      isofhlevel n X -> isofhlevel n Y -> isofhlevel n (X == Y).
Proof.
  intros n.
  case n.
    intros X Y pX pY.
    apply isofhlevel0pathspace;
    assumption.
    apply isofhlevelSnpathspace.
Qed.


(** ** Weak equivalence between identity types in [HLevel] and [U] *)

(** Identity of Sigmas <~> Sigma of Identities <~> Identities in [U] ,
   where the first equivalence is called [weq1] and the second one
   is called [weq2]
*)

Lemma weq1  (P : UU -> hProp) (X X' : UU) 
      (pX : P X) (pX' : P X') : 
     weq ((tpair _ X pX) == (tpair (fun x => P x) X' pX'))
         (total2 (fun w : X == X' => 
              transportf (fun x => P x) w pX == pX')).
Proof.
  apply total_paths_equiv.
Defined.


Definition ident_is_prop : 
 forall (P : UU -> hProp) (X X' : UU)(pX : P X) (pX' : P X')
       (w : X == X'),
   isaprop (transportf (fun X => P X) w pX == pX').
Proof.
  intros P X X' pX pX' w.
  apply isapropifcontr.
  apply (P X').
Defined.

Lemma isweqpr1_UU (X X' : UU) (B : X == X' -> hProp) 
   (is1 : forall z , iscontr (B z)) : isweq (@pr1 _ B).
Proof. 
  intros. 
  unfold isweq. 
  intro y. 
  set (isy := is1 y). 
  apply (iscontrweqf (ezweqpr1 B y)). 
  assumption. 
Defined.

Lemma weq2 (P : UU -> hProp) (X X' : UU) 
      (pX : P X) (pX' : P X') :
  weq (total2 (fun w : X == X' => 
              transportf (fun x => P x) w pX == pX'))
      (X == X').
Proof.
  exists (@pr1 (X == X') (fun w : X == X' => 
            (transportf (fun x : UU => P x) w pX)  == pX' )).
  set (H' := isweqpr1_UU X X'
        (fun w : X == X' => 
     tpair _ (transportf (fun X => P X) w pX == pX') 
             (ident_is_prop P X X' pX pX' w) )).
  simpl in H'.
  apply H'.
  intro z.
  apply (P X').
Defined.
 
Lemma Id_p_weq_Id (P : UU -> hProp) (X X' : UU) 
      (pX : P X) (pX' : P X') : 
 weq ((tpair _ X pX) == (tpair (fun x => P x) X' pX')) (X == X').
Proof.
  set (f := weq1 P X X' pX pX').
  set (g := weq2 P X X' pX pX').
  set (fg := weqcomp f g).
  exact fg.
Defined.


(** ** HLevel *)

Definition HLevel n := total2 (fun X : UU => isofhlevel n X).

(** * Main theorem *)

(** the type of types of hlevel [n] has hlevel [S n] *)

Lemma hlevel_of_hlevels : forall n,
      isofhlevel (S n) (HLevel n).
Proof.
  intro n.
  simpl.
  intros [X pX] [X' pX'].
  set (H := isofhlevelweqb n 
       (Id_p_weq_Id (fun X => tpair (fun X => isaprop X) (isofhlevel n X) 
                               (isapropisofhlevel _ _)) X X' pX pX')).
  apply H.
  apply isofhlevelpathspace;
  assumption.
Defined.   



Lemma UA_for_Predicates (P : UU -> hProp) (X X' : UU)
     (pX : P X) (pX' : P X') :
  weq ((tpair _ X pX) == (tpair (fun x => P x) X' pX')) (weq X X').
Proof.
  set (f := Id_p_weq_Id P X X' pX pX').
  set (g := univalenceweq X X').
  exact (weqcomp f g).
Defined.

Corollary UA_for_HLevels : forall (n : nat)
      (X X' : HLevel n), 
     weq (X == X') (weq (pr1 X) (pr1 X')).
Proof.
  intros n [X pX] [X' pX'].
  simpl.
  apply (UA_for_Predicates 
       (fun X => tpair (fun X => isaprop X) (isofhlevel n X) 
                                      (isapropisofhlevel _ _))).
Defined.
  
