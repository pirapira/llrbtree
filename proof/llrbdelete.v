Require Import llrbtree.

  Ltac pira :=
    unfold reds, turnR, is_true, empty, isBalanced, isBlackSame, isRedSeparate, balanceL, balanceR in *;  auto; try congruence; 
    match goal with
      (* killing *)
      | [|- hasSameBlackDepth O Leaf] => apply Oleaf
      | [H :ins ?x ?t1 = Leaf |- _] => clear - H; apply False_ind; apply ins_result_not_leaf with x t1
      (* context_non_splitting *)
      | [H: ?m = ?m, H1: ?m = ?m |- _] =>
        clear H1
      | [|- _ -> _] => intro
      | [IH : valid ?t -> _ |- _] => destruct IH
      | [IH : context[valid _] |- _] => unfold valid in IH
      | [|- context[valid _] ] => unfold valid
      | [IH : context[delete _ _] |- _] => unfold delete in IH
      | [|- context[delete _ _] ] => unfold delete
      | [IH : context[delete' _ _] |- _] => unfold delete' in IH
      | [|- context[delete' _ _] ] => unfold delete'
      | [H: exists n, _ |- _] => destruct H
      | [|- exists m: nat, hasSameBlackDepth m Leaf] => exists O
      | [|- exists n : nat, hasSameBlackDepth n (Node R Leaf _ _)] => exists O
      | [|- exists n : nat, hasSameBlackDepth n (Node B Leaf _ _)] => exists (S O)
      | [|- exists n : nat, hasSameBlackDepth n (Node R _ _ Leaf)] => exists O
      | [|- exists n : nat, hasSameBlackDepth n (Node B _ _ Leaf)] => exists (S O)
      | [|- exists n : nat, hasSameBlackDepth n (Node B (Node R Leaf _ _) _ _)] =>
        exists (S O)
      | [|- exists n : nat, hasSameBlackDepth n (Node B (Node R _ _ Leaf) _ _)] =>
        exists (S O)
      | [|- exists n : nat, hasSameBlackDepth n
        (Node R (Node B (Node R Leaf _ _) _ _) _ _)] => exists (S O)
      | [|- exists n : nat, hasSameBlackDepth n
        (Node R (Node B (Node R _ _ Leaf) _ _) _ _)] => exists (S O)
      | [|- context[reds _ Leaf]] => simpl
      | [H: _ /\ _ |- _] => destruct H
      | [H: hasSameBlackDepth ?x0 ?t1 |- exists n, hasSameBlackDepth n ?t1]
        => exists x0
      | [H: (?a && ?b)%bool = true |- _] => apply andb_prop in H
(*      | [H: ?a = true |- _] => rewrite H in * *)
      | [H : reds R ?t1 = true |- reds B ?t1 = true] => apply redsRB
      | [H: hasSameBlackDepth ?m ?t, H0: hasSameBlackDepth ?n ?t |- _] =>
        progress (
          first[
            match goal with
              | [H1: m = n |- _] => idtac
            end |
            (assert (m = n) by (apply hasSameFunctional with t; auto); subst)])
      | [H :ins ?x ?t = Node _ _ _ _ |- _] => rewrite H in *
      |  [ H: hasSameBlackDepth ?x ?t1 |-
          exists n : nat, hasSameBlackDepth n (Node R (Node R ?t1 _ _) _ _)]
        =>
        exists x
      | [ |- exists n : nat, hasSameBlackDepth n (Node R (Node R Leaf _ Leaf) _ Leaf)] =>
        exists O
      | [ H31 : hasSameBlackDepth ?x ?r1 |- exists n : nat,
        hasSameBlackDepth n
        (Node B (Node R (Node B ?r1 _ _) _ _)_ _)] =>
        exists (S (S x))
      | [ H31 : hasSameBlackDepth ?m1 ?r2 |-
        exists n : nat,
          hasSameBlackDepth n
          (Node B (Node R _ _ (Node B _ _ ?r2)) _ _)] =>
        exists (S (S m1))
      | [ H31 : hasSameBlackDepth ?x ?r1 |- exists n : nat,
        hasSameBlackDepth n
        (Node R (Node B (Node B ?r1 _ _) _ _)_ _)] =>
        exists (S (S x))
      | [ H33 : hasSameBlackDepth ?x ?r1 |-
        exists n : nat,
          hasSameBlackDepth n
          (Node B (Node B _ _ ?r1) _ _)] =>
        exists (S (S x))
      | [ H31 : hasSameBlackDepth ?x ?r1 |- exists n : nat,
        hasSameBlackDepth n
        (Node B (Node B (Node R ?r1 _ _) _ _)_ _)] =>
        exists (S (S x))
      | [ H31 : hasSameBlackDepth ?x ?r1 |- exists n : nat,
        hasSameBlackDepth n
        (Node B (Node B (Node B ?r1 _ _) _ _)_ _)] =>
        exists (S (S (S x)))
      | [H: hasSameBlackDepth _ (Node _ _ _ _) |- _] =>
        inversion H; clear H; subst
      | [H: reds _ (Node _ _ _ _) = _ |- _] =>
        inversion H; clear H; subst
      | [H: (isLeftLean (Node _ _ _ _)) = true |- _] =>
        inversion H; clear H; subst
      | [H14 : hasSameBlackDepth _ Leaf |- _] =>
        inversion H14; clear H14; subst
      | [ H11 : Node _ _ _ _ = Node _ _ _ _ |- _] =>
        inversion H11; clear H11; subst
      (* context_splitting *)
      | [|- andb _ _ = true] => apply andb_true_intro
      | [|- _ /\ _] => split
      | [c : Color |-_] => case_eq c; subst
      | [H : hasSameBlackDepth ?x ?t |- exists n : nat, hasSameBlackDepth n (Node B ?t _ _)] => exists (S x)
      | [H : hasSameBlackDepth ?x ?t |- exists n : nat, hasSameBlackDepth n (Node R ?t _ _)] => exists x
      | [|- hasSameBlackDepth (S _) (Node B _ _ _)] => apply SforkB
      | [H := ?x : nat |- hasSameBlackDepth ?x (Node B _ _ _)] => destruct x
      | [|- hasSameBlackDepth _ (Node R _ _ _)] => apply SforkR
      | [H := ?x : nat |- hasSameBlackDepth ?x Leaf] => destruct x
      | [|- context[compare ?a ?b]] => destruct (compare a b)
      | [H: context[compare ?a ?b] |- _ ] => destruct (compare a b)
      | [|- context [isLeftLean Leaf]] => simpl
      | [|- context [isLeftLean (Node _ _ _)] ] => simpl
      (* too heavy *)
      (* undecided *)
(*       | [H14 : hasSameBlackDepth 0 _ |- _] =>
        inversion H14; clear H14; subst  causes inf loop *) 
    end
  .

  Ltac pirapira := progress (repeat pira).

Ltac finish := abstract pirapira.
Ltac c x t :=                                                                        
  case_eq (ins x t).                                                               
                                                                                         
Ltac d t :=                                                                          
  destruct t.

Ltac a :=
  try finish; pirapira.

Lemma valid_insert: forall x t, valid t -> isRedSeparate (delete x t).
intro x.
induction t.
finish.
pira.
pira.
pira.
pira.
pira.
pira.
pira.
pira.
pira.
pira.
pira.
