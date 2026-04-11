From Stdlib Require Import Arith Strings.Byte List Lia.
Import ListNotations.

Section Substring.
    
    (* returns s[p:p + l) *)
    Fixpoint slice {A : Type} (p l : nat) (s : list A) : list A := 
        match s, p with 
        | cons hd tl, S q => slice q l tl
        | cons hd tl, 0 => match l with
                | 0 => nil
                | S k => hd :: (slice 0 k tl)
            end
        | _, _ => nil
    end.

    Compute slice 1 2 [1;2;3;4;5;6].
    Compute slice 1 20 [1;2;3;4;5;6].

    Fixpoint list_eqb {A : Type} (eqb : A -> A -> bool) (s t : list A) : bool := 
        match (s, t) with
            | (cons s1 s2, cons t1 t2) => (eqb s1 t1) && (list_eqb eqb s2 t2)
            | (nil, nil) => true
            | _ => false
        end.

    Lemma equality_implies_length_eq {A : Type} (eqb : A -> A -> bool) (s t : list A) :
        list_eqb eqb s t = true -> length s = length t.
    Proof.
    Admitted.

    Lemma slice_size {A : Type} (s : list A) (p l : nat) :
        length (slice p l s) = min l (length s - p).
    Proof.
    Admitted.

    Lemma slice_slice {A : Type} (s : list A) (p1 l1 p2 l2 : nat) :
        slice p2 l2 (slice p1 l1 s) = slice (p1 + p2) (min l2 (l1 - p2)) s.
    Proof.
    Admitted.

    Fixpoint find_match' {A : Type} (eqb : A -> A -> bool) (s t : list A) (p : nat) : option nat := 
        if (list_eqb eqb (slice p (length t) s) t)
        then Some p
        else match p with
            | S q => find_match' eqb s t q
            | 0 => None
            end.

    Definition find_match {A : Type} (eqb : A -> A -> bool) (s t : list A) : option nat :=
        find_match' eqb s t (length s).
  
    Compute find_match (Nat.eqb) [1;2;3;4;5] [2;3;4].

    Lemma find_match_corr' {A : Type} (eqb : A -> A -> bool) (s t : list A) (n p : nat) :
        find_match' eqb s t p = Some n ->
        list_eqb eqb (slice n (length t) s) t = true.
    Proof.
        intros.
        induction p. simpl in H.  destruct (list_eqb eqb (slice 0 (length t) s) t) eqn:Heq.
        inversion H. subst. assumption. inversion H.

        simpl in H. destruct (list_eqb eqb (slice (S p) (length t) s) t) eqn:Hd.
        inversion H. subst. assumption.

        eapply IHp. assumption.
    Qed.

    Lemma find_match_corr {A : Type} (eqb : A -> A -> bool) (s t : list A) (n : nat) :
        find_match eqb s t = Some n
            -> list_eqb eqb (slice n (length t) s) t = true /\ ((length t >= 1) -> n <= length s - length t).
    Proof.
        assert (find_match eqb s t = Some n
            ->list_eqb eqb (slice n (length t) s) t = true).
        intros. eapply find_match_corr'. unfold find_match in H. exact H.
        split. apply H. apply H0.

        intros.
        specialize (H H0).  
        specialize (equality_implies_length_eq eqb (slice n (length t) s) t H) as H2.
        rewrite slice_size in H2. lia.
    Qed.

End Substring.