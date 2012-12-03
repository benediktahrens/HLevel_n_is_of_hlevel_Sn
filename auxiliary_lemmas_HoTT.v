
(** * [HLevel(n)] is of hlevel n+1 *)

(** 
   Authors: Benedikt Ahrens, Chris Kapulkin
   Title: HLevel(n) is of hlevel n+1 
   Date: December 2012 
*)

(** In this file we translate some results from the HoTT library
    https://github.com/HoTT/HoTT
    from the files Fibrations.v and UsefulEquivalences.v	
    to Voevodsky's Foundations library.
    We do not claim any originality; these lemmas were previously 
    proved by the HoTT team.
*)

(** The main result we will use in the following is the theorem 
    [total_paths_equiv], the last statement of this file.
*)

Require Import uu0.
Require Import hProp.

(** For convenience we use an infix notation for the path space. *)

Notation "a == b" := (paths a b) (at level 70, no associativity).


(** * Paths in total spaces are equivalent to pairs of paths *)

(** some of the lemmas are proved for similar fibrations twice:
    once we consider fibrations over a type in universe [UU], 
    once we consider fibrations over the universe [UU] itself *)

(** ** Path in the total space from a pair of paths *)
(** The following two lemmas give a way to construct a path in the
    total space of a fibration, given two paths:
    a path in the base space and a path in one of the fibers *)

Lemma total2_paths {A : UU} {B : A -> UU} {s s' : total2 (fun x => B x)} 
    (p : pr1 s == pr1 s') (q : transportf (fun x => B x) p (pr2 s) == pr2 s') :
               s == s'.
Proof.
  destruct s as [a b]; destruct s' as [a' b'].
  simpl in p; destruct p.
  simpl in q; destruct q.
  apply idpath.
Defined.

Lemma total2_paths2 {A : UU} {B : A -> UU} {a1 : A} {b1 : B a1} 
    {a2 : A} {b2 : B a2} (p : a1 == a2) 
    (q : transportf (fun x => B x) p b1 == b2) : 
    tpair (fun x => B x) a1 b1 == tpair (fun x => B x) a2 b2.
Proof.
  set (H := @total2_paths _ _  
    (tpair (fun x => B x) a1 b1)(tpair (fun x => B x) a2 b2)).
  simpl in H.
  apply (H p q).
Defined.

(** The following lemma is analogous to the previous two;
    and gives a way to construct a path in the total space of 
    a fibration [B : UU -> hProp]
*)

Lemma total2_paths_UU  {B : UU -> hProp} {s s' : total2 (fun x => B x)} 
    (p : pr1 s == pr1 s') 
    (q : transportf (fun x => B x) p (pr2 s) == pr2 s') : 
               s == s'.
Proof.
  destruct s as [a b]; destruct s' as [a' b'].
  simpl in p; destruct p.
  simpl in q; destruct q.
  apply idpath.
Defined.

(** Conversely, from a path in the total space of [B : UU -> hProp]
    we obtain a path in the base space and a path in one of the fibers 
*)

Lemma base_paths_UU {B : UU -> hProp}(a b : total2 B) :
  a == b -> pr1 a == pr1 b.
Proof.
  intro H.
  apply (maponpaths  (@pr1 _ _) H).
Defined.


Definition fiber_path {B : UU -> hProp} {u v : total2 (fun x => B x)} 
  (p : u == v) :  
     transportf (fun x => B x) (base_paths_UU _ _ p) (pr2 u) == pr2 v.
Proof.
  destruct p.
  apply idpath.
Defined.

(** The previous constructions are each others' inverses.
    This gives an equivalence between paths in a total space
    and the total space of the corresponding path spaces.  
*)


Lemma total_path_reconstruction {B : UU -> hProp} 
    {x y : total2 (fun x => B x)} (p : x == y) :
  total2_paths_UU  _ (fiber_path p) == p.
Proof.
  induction p.
  destruct x.
  apply idpath.
Defined.


Lemma base_total_path {B : UU -> hProp} {x y : total2 (fun x => B x)}
  {p : pr1 x == pr1 y} (q : transportf _ p (pr2 x) == pr2 y) :
  (base_paths_UU _ _ (total2_paths_UU _ q)) == p.
Proof.
  destruct x as [x H]. destruct y as [y K].
  simpl in p. induction p. simpl in q. induction q.
  apply idpath.
Defined.



Lemma fiber_total_path (B : UU -> hProp) (x y : total2 (fun x => B x))
  (p : pr1 x == pr1 y) (q : transportf _ p (pr2 x) == pr2 y) :
  transportf (fun p' : pr1 x == pr1 y => transportf _ p' (pr2 x) == pr2 y)
  (base_total_path q)  (fiber_path (total2_paths_UU _ q))
  == q.
Proof.
  destruct x as [x H]. destruct y as [y K].
  simpl in p. induction p. simpl in q. induction q.
  apply idpath.
Defined.

(** We now give the main result of this file.
    The equivalence is established by showing that the previously 
    defined maps are inverse to each other.
*)

Theorem total_paths_equiv (B : UU -> hProp) (x y : total2 (fun x => B x)) :
  weq (x == y) (total2 (fun p : pr1 x == pr1 y => 
                            transportf _ p (pr2 x) == pr2 y )).
Proof.
  exists (fun r : x == y =>  
            tpair (fun p : pr1 x == pr1 y => 
       transportf _ p (pr2 x) == pr2 y) (base_paths_UU _ _ r) (fiber_path r)).
  apply (gradth _
  (fun pq : total2 (fun p : pr1 x == pr1 y => transportf _ p (pr2 x) == pr2 y)
          => total2_paths_UU (pr1 pq) (pr2 pq))).
  intro p.
  simpl.
  apply total_path_reconstruction.
  intros [p q].
  simpl.
  set (H':= base_total_path q).
  apply ( total2_paths2 
    (B := fun p : pr1 x == pr1 y => transportf (fun x : UU => B x) p (pr2 x) 
      == pr2 y) H').
  apply fiber_total_path.
Defined.











