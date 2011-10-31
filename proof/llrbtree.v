(* 
 * $ coqc --version
 * The Coq Proof Assistant, version 8.3pl2 (August 2011)
 * compiled on Aug 25 2011 04:21:44 with OCaml 3.12.0
 *)

Inductive Color : Set := R | B.

Section RB.

  Parameter a : Set.
  
  Inductive RBTree :=
  | Leaf
  | Node : Color -> RBTree -> a -> RBTree -> RBTree.

  Definition empty := Leaf.

  Inductive hasSameBlackDepth : nat -> RBTree -> Prop :=
  | Oleaf : hasSameBlackDepth O Leaf
  | SforkB : forall (l r: RBTree) (m: nat) (x: a),
    hasSameBlackDepth m l -> hasSameBlackDepth m r ->
    hasSameBlackDepth (S m) (Node B l x r)
  | SforkR : forall (l r: RBTree) (m: nat) (x: a),
    hasSameBlackDepth m l -> hasSameBlackDepth m r ->
    hasSameBlackDepth m (Node R l x r).

  Definition isBlackSame (t: RBTree): Prop :=
    exists n: nat, hasSameBlackDepth n t.

  
  Fixpoint reds (c: Color) (t: RBTree) : bool :=
    match (c, t) with
      | (_, Leaf) => true
      | (R, Node R _ _ _) => false
      | (_, Node c l _ r) => andb (reds c l) (reds c r)
    end.

  Definition isRedSeparate (t: RBTree) :=
    is_true (reds B t).
    
  Definition isBalanced (t: RBTree): Prop :=
    isBlackSame t /\ isRedSeparate t.

  Inductive cmp := LT | GT | EQ.
  Parameter compare : a -> a -> cmp.

  Definition balanceL c l x r :=
    match (c,l,x,r) with
      | (B, (Node R (Node R a x b) y c), z, d) =>
        Node R (Node B a x b) y (Node B c z d)
      | (c, a, x, b) => Node c a x b
    end.

  Definition balanceR c l x r :=
    match (c,l,x,r) with
      | (B, (Node R a x b), y, (Node R c z d)) =>
        Node R (Node B a x b) y (Node B c z d)
      | (k, x, y, (Node R c z d)) =>
        Node k (Node R x y c) z d
      | (c, a, x, b) => Node c a x b
    end.

  Fixpoint ins x t :=
    match t with
      | Leaf => Node R Leaf x Leaf
      | Node c l y r =>
        match compare x y with
          | LT => balanceL c (ins x l) y r
          | GT => balanceR c l y (ins x r)
          | EQ => t
        end
    end.

  Definition insert a b :=
    match ins a b with
      | Node _ d e f =>  Node B d e f
      | Leaf => (* never reached *) Leaf
    end.

  Definition isBlackBlack t :=
    match t with
      | (Node B (Node B _ _ _) _ _) => true
      | (Node B Leaf _ _)           => true
      | _                           => false
    end.
  
  Definition isBlackRed t :=
    match t with
      | (Node B (Node R _ _ _) _ _) => true
      | _                           => false
    end.
  
  Definition turnR t :=
    match t with
      | Leaf           => (* not reached *) t
      | (Node _ l x r) => Node R l x r
    end.

  Require Import Arith.Wf_nat.

  Fixpoint hight t :=
    match t with
      | Leaf => O
      | Node _ l _ _ => S (hight l)
    end.

  Require Import Recdef.

  Require Program.Wf.
  Require Program.Program.

  Program Fixpoint deleteMin' (t: RBTree) {measure (hight t)}: RBTree :=
    match t with
      | (Node R Leaf _ Leaf) => Leaf
      | (Node R l x r) =>
        match (isBlackBlack l, isBlackRed r) with
          | (true, true) =>
            match r with
              | Node B (Node R b y c) z d => 
                Node R (Node B (deleteMin' (turnR l)) x b) y (Node B c z d)
              | _ => t (* not reached *)
            end
          | (true, _)    => balanceR B (deleteMin' (turnR l)) x (turnR r)
          | _            => t (* not reached *)
        end
      | (Node c l x r) => Node c (deleteMin' l) x r
      | _ => t (* not reached *)
    end.
  Next Obligation.
    destruct l.
    inversion H1.

    destruct l1.
    inversion H1; clear H1; subst.
    simpl.
    auto.

    simpl.
    auto.
  Defined.
  Next Obligation.
    destruct l.
    simpl.
    auto.

    simpl.
    auto.
  Defined.
  Next Obligation.
    intuition.
    inversion H0.
    inversion H0.
  Defined.
  Next Obligation.
    intuition.
    congruence.
    congruence.
    congruence.
  Defined.
  Next Obligation.
    intuition.
    congruence.
    congruence.
  Defined.

  Definition turnB t :=
    match t with
      | Leaf           => (* not reached *) t
      | (Node _ l x r) => Node B l x r
    end.

  Definition deleteMin t :=
    match deleteMin' (turnR t) with
      | Leaf => Leaf
      | t'   => turnB t'
    end.

  Definition isBlackLeftBlack t :=
    match t with
      | (Node B Leaf _ _)           => true
      |  (Node B (Node B _ _ _) _ _) => true
      | _                           => false
    end.

  Definition isBlackLeftRed t :=
    match t with
      | (Node B (Node R _ _ _) _ _) => true
      | _                           => false
    end.

  Fixpoint minimum t :=
    match t with
      | (Node _ Leaf x _) => inl x
      | (Node _ l _ _) => minimum l
      | _ => inr tt
    end.

  Program Fixpoint
    delete' kx t {measure t} :=
    match t with
      | (Node c l x r) => 
        match compare kx x with
          | LT => deleteLT kx c l x r
          | GT => deleteGT kx c l x r
          | EQ => deleteEQ kx c l x r
        end
      | Leaf => t (* not reached *)
    end
  with
    deleteLT kx c l x r :=
    match (kx, c, l, x, r, isBlackLeftBlack l, isBlackLeftRed r) with
      | (_, R, _, _, _, true, true) =>
        match r with
          | Node B (Node R rll rlx rlr) rx rr => 
            Node R (Node B (delete' kx (turnR l)) x rll) rlx (Node B rlr rx rr)
          | _ => l (* not reached *)
        end
      | (_, R, _, _, _, true, _) => balanceR B (delete' kx (turnR l)) x (turnR r)
      | _ => Node c (delete' kx l) x r
    end
  with
    deleteGT kx c l x r :=
    match (kx, c, l, x, r, isBlackLeftBlack r, isBlackLeftRed l) with
      | (kx, c, (Node R ll lx lr), x, r, _, _) =>
        balanceR c ll lx (delete' kx (Node R lr x r))
      | (kx, R, l, x, r, true, true) =>
        match l with
          | Node B ll lx lr => 
            Node R (turnB ll) lx (balanceR B lr x (delete' kx (turnR r)))
          | _ => l (* never reached *)
        end
      | (kx, R, l, x, r, true, _) =>
        balanceR B (turnR l) x (delete' kx (turnR r))
      | (kx, R, l, x, r, _, _) =>
        Node R l x (delete' kx r)
      | _ => l (* not reached *)
    end
  with
    deleteEQ kx c l x r :=
    match (kx, c, l, x, r, isBlackLeftBlack r, isBlackLeftRed l) with
      | (_, R, Leaf, _, Leaf, _, _) => Leaf
      | (kx, c, (Node R ll lx lr), x, r, _, _) =>
        balanceR c ll lx (delete' kx (Node R lr x r))
      | (_, R, l, _, r, true, true) =>
        match minimum r with
          | inl m =>
            match l with             
              | Node B ll lx lr =>
                balanceR R (turnB ll) lx (balanceR B lr m (deleteMin' (turnR r)))
              | _ => (* never reached *) l
            end
          | inr tt => (* never reached *) l
        end
      | (_, R, l, _, r, true, _) =>
        match minimum r with
          | inl m => 
            balanceR B (turnR l) m (deleteMin' (turnR r))
          | _ => (* never reached *) l
        end
      | (_, R, l, _, (Node B rl rx rr), _, _) =>
        match minimum r with
          | inl m => 
            Node R l m (Node B (deleteMin' rl) rx rr)
          | _ => (* never reached *) l
        end
      | _ => l (* not reached *)
    end.
        





  
  Definition delete kx t :=
    match delete' kx (turnR t) with
      | Leaf => Leaf
      | t'   => turnB t'
    end.

  Fixpoint isLeftLean t :=
    match t with
      | Leaf => true
      | (Node B _ _ (Node R _ _ _)) => false
      | (Node _ r _ l) => andb (isLeftLean r) (isLeftLean l)
    end.

  Definition valid t :=
    isBalanced t /\ is_true (isLeftLean t).

  Lemma redsRB: forall t1,
    reds R t1 = true -> reds B t1 = true.
    destruct t1; intuition.
    inversion H.
    case_eq c.
    intro.
    subst.
    congruence.

    intro.
    subst.
    apply andb_prop in H1.
    destruct H1.
    simpl.
    reflexivity.

    Qed.
    
  Lemma hasSameFunctional: forall t m m0,
    hasSameBlackDepth m t -> 
    hasSameBlackDepth m0 t -> m = m0.
    induction t.
    intuition.
    inversion H.
    inversion H0.
    auto.

    intros.
    inversion H; subst.
    inversion H0; subst.

    intuition.

    inversion H; subst.
    inversion H0; subst.

    intuition.

    Qed.
    
    Lemma ins_result_not_leaf: forall x t, ins x t = Leaf -> False.
      intro x.
      induction t.
      simpl.
      congruence.
      simpl.
      destruct (compare x a0).
      case (ins x t1).
      unfold balanceL.
      case c.
      congruence.
      congruence.
      intro.

      intro.
      intro.
      intro.
      unfold balanceL.
      case c.
      congruence.
      case c0.
      case r.
      congruence.
      intros.
      destruct c1.
      congruence.
      congruence.
      congruence.
      unfold balanceR.
      destruct c.
      destruct (ins x t2); try congruence.
      destruct c; try congruence.
      destruct t2; try destruct (ins x t2); try destruct t1; try congruence.
      simpl.
      congruence.
      destruct c.
      simpl.
      congruence.
      simpl; congruence.
      destruct c; simpl; try congruence.
      destruct (compare x a1).
      destruct (balanceL R (ins x t2_1) a1 t2_2).
      congruence.
      destruct c.
      congruence.
      congruence.
      destruct (balanceR R t2_1 a1 (ins x t2_2)); try destruct c; try congruence.
      congruence.
      destruct (compare x a1); try destruct (balanceL B (ins x t2_1) a1 t2_2); try destruct (balanceR B t2_1 a1 (ins x t2_2)); try destruct c; try destruct c0; try congruence.
      destruct c0.
      destruct (ins x (Node c t2_1 a1 t2_2)); try destruct c0; try congruence.
      destruct (ins x (Node c t2_1 a1 t2_2)); try destruct c0; try congruence.
      congruence.

      Qed.
End RB.
