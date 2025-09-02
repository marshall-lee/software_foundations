Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From PLF Require Import Hoare.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From PLF Require Import Hoare.
Import Check.

Goal True.

idtac "-------------------  hoare_post_true  --------------------".
idtac " ".

idtac "#> hoare_post_true".
idtac "Possible points: 1".
check_type @hoare_post_true (
(forall (P Q : Assertion) (c : com) (_ : forall st : state, Q st),
 valid_hoare_triple P c Q)).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_post_true.
Goal True.
idtac " ".

idtac "-------------------  hoare_pre_false  --------------------".
idtac " ".

idtac "#> hoare_pre_false".
idtac "Possible points: 1".
check_type @hoare_pre_false (
(forall (P Q : Assertion) (c : com) (_ : forall st : state, not (P st)),
 valid_hoare_triple P c Q)).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_pre_false.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_wrong  --------------------".
idtac " ".

idtac "#> hoare_asgn_wrong".
idtac "Possible points: 2".
check_type @hoare_asgn_wrong (
(@ex aexp
   (fun a : aexp =>
    not
      (valid_hoare_triple (fun _ : state => True)
         (CAsgn X a)
         (fun st : state =>
          @eq nat ((Aexp_of_aexp (AId X) : Aexp) st)
            ((Aexp_of_aexp a : Aexp) st)))))).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_wrong.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_fwd  --------------------".
idtac " ".

idtac "#> hoare_asgn_fwd".
idtac "Advanced".
idtac "Possible points: 3".
check_type @hoare_asgn_fwd (
(forall (m : nat) (a : aexp) (P : Assertion),
 valid_hoare_triple
   (fun st : state =>
    and ((P : Assertion) st)
      (((fun st0 : state =>
         @eq nat ((Aexp_of_aexp (AId X) : Aexp) st0)
           ((Aexp_of_nat m : Aexp) st0))
        :
        Assertion) st))
   (CAsgn X a)
   (fun st : state =>
    and (P (@Maps.t_update nat st X m))
      (@eq nat (st X) (aeval (@Maps.t_update nat st X m) a))))).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_fwd.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_examples_2  --------------------".
idtac " ".

idtac "#> assertion_sub_ex1'".
idtac "Possible points: 1".
check_type @assertion_sub_ex1' (
(valid_hoare_triple
   (fun st : state =>
    le ((Aexp_of_aexp (AId X) : Aexp) st) ((Aexp_of_nat 5 : Aexp) st))
   (CAsgn X (AMult (ANum 2) (AId X)))
   (fun st : state =>
    le ((Aexp_of_aexp (AId X) : Aexp) st) ((Aexp_of_nat 10 : Aexp) st)))).
idtac "Assumptions:".
Abort.
Print Assumptions assertion_sub_ex1'.
Goal True.
idtac " ".

idtac "#> assertion_sub_ex2'".
idtac "Possible points: 1".
check_type @assertion_sub_ex2' (
(valid_hoare_triple
   (fun st : state =>
    and
      (((fun st0 : state =>
         le ((Aexp_of_nat 0 : Aexp) st0) ((Aexp_of_nat 3 : Aexp) st0))
        :
        Assertion) st)
      (((fun st0 : state =>
         le ((Aexp_of_nat 3 : Aexp) st0) ((Aexp_of_nat 5 : Aexp) st0))
        :
        Assertion) st))
   (CAsgn X (ANum 3))
   (fun st : state =>
    and
      (((fun st0 : state =>
         le ((Aexp_of_nat 0 : Aexp) st0) ((Aexp_of_aexp (AId X) : Aexp) st0))
        :
        Assertion) st)
      (((fun st0 : state =>
         le ((Aexp_of_aexp (AId X) : Aexp) st0) ((Aexp_of_nat 5 : Aexp) st0))
        :
        Assertion) st)))).
idtac "Assumptions:".
Abort.
Print Assumptions assertion_sub_ex2'.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_example4  --------------------".
idtac " ".

idtac "#> hoare_asgn_example4".
idtac "Possible points: 2".
check_type @hoare_asgn_example4 (
(valid_hoare_triple (fun _ : state => True)
   (CSeq (CAsgn X (ANum 1)) (CAsgn Y (ANum 2)))
   (fun st : state =>
    and
      (((fun st0 : state =>
         @eq nat ((Aexp_of_aexp (AId X) : Aexp) st0)
           ((Aexp_of_nat 1 : Aexp) st0))
        :
        Assertion) st)
      (((fun st0 : state =>
         @eq nat ((Aexp_of_aexp (AId Y) : Aexp) st0)
           ((Aexp_of_nat 2 : Aexp) st0))
        :
        Assertion) st)))).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_example4.
Goal True.
idtac " ".

idtac "-------------------  swap_exercise  --------------------".
idtac " ".

idtac "#> swap_exercise".
idtac "Possible points: 3".
check_type @swap_exercise (
(valid_hoare_triple
   (fun st : state =>
    le ((Aexp_of_aexp (AId X) : Aexp) st) ((Aexp_of_aexp (AId Y) : Aexp) st))
   swap_program
   (fun st : state =>
    le ((Aexp_of_aexp (AId Y) : Aexp) st) ((Aexp_of_aexp (AId X) : Aexp) st)))).
idtac "Assumptions:".
Abort.
Print Assumptions swap_exercise.
Goal True.
idtac " ".

idtac "-------------------  invalid_triple  --------------------".
idtac " ".

idtac "#> invalid_triple".
idtac "Advanced".
idtac "Possible points: 6".
check_type @invalid_triple (
(not
   (forall (a : aexp) (n : nat),
    valid_hoare_triple
      (fun st : state =>
       @eq nat ((Aexp_of_aexp a : Aexp) st) ((Aexp_of_nat n : Aexp) st))
      (CSeq (CAsgn X (ANum 3)) (CAsgn Y a))
      (fun st : state =>
       @eq nat ((Aexp_of_aexp (AId Y) : Aexp) st) ((Aexp_of_nat n : Aexp) st))))).
idtac "Assumptions:".
Abort.
Print Assumptions invalid_triple.
Goal True.
idtac " ".

idtac "-------------------  if_minus_plus  --------------------".
idtac " ".

idtac "#> if_minus_plus".
idtac "Possible points: 2".
check_type @if_minus_plus (
(valid_hoare_triple (fun _ : state => True)
   (CIf (BLe (AId X) (AId Y)) (CAsgn Z (AMinus (AId Y) (AId X)))
      (CAsgn Y (APlus (AId X) (AId Z))))
   (fun st : state =>
    @eq nat ((Aexp_of_aexp (AId Y) : Aexp) st)
      (((fun st0 : state =>
         PeanoNat.Nat.add ((Aexp_of_aexp (AId X) : Aexp) st0)
           ((Aexp_of_aexp (AId Z) : Aexp) st0))
        :
        Aexp) st)))).
idtac "Assumptions:".
Abort.
Print Assumptions if_minus_plus.
Goal True.
idtac " ".

idtac "-------------------  if1_ceval  --------------------".
idtac " ".

idtac "#> If1.if1true_test".
idtac "Possible points: 1".
check_type @If1.if1true_test (
(If1.ceval (If1.CIf1 (BEq (AId X) (ANum 0)) (If1.CAsgn X (ANum 1))) empty_st
   (@Maps.t_update nat empty_st X 1))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.if1true_test.
Goal True.
idtac " ".

idtac "#> If1.if1false_test".
idtac "Possible points: 1".
check_type @If1.if1false_test (
(If1.ceval (If1.CIf1 (BEq (AId X) (ANum 0)) (If1.CAsgn X (ANum 1)))
   (@Maps.t_update nat empty_st X 2) (@Maps.t_update nat empty_st X 2))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.if1false_test.
Goal True.
idtac " ".

idtac "-------------------  hoare_if1  --------------------".
idtac " ".

idtac "#> Manually graded: If1.hoare_if1".
idtac "Possible points: 2".
print_manual_grade If1.manual_grade_for_hoare_if1.
idtac " ".

idtac "-------------------  hoare_if1_good  --------------------".
idtac " ".

idtac "#> If1.hoare_if1_good".
idtac "Possible points: 2".
check_type @If1.hoare_if1_good (
(If1.valid_hoare_triple
   (fun st : state =>
    @eq nat
      (((fun st0 : state =>
         PeanoNat.Nat.add ((Aexp_of_aexp (AId X) : Aexp) st0)
           ((Aexp_of_aexp (AId Y) : Aexp) st0))
        :
        Aexp) st)
      ((Aexp_of_aexp (AId Z) : Aexp) st))
   (If1.CIf1 (BNeq (AId Y) (ANum 0)) (If1.CAsgn X (APlus (AId X) (AId Y))))
   (fun st : state =>
    @eq nat ((Aexp_of_aexp (AId X) : Aexp) st)
      ((Aexp_of_aexp (AId Z) : Aexp) st)))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.hoare_if1_good.
Goal True.
idtac " ".

idtac "-------------------  hoare_havoc  --------------------".
idtac " ".

idtac "#> Himp.hoare_havoc".
idtac "Advanced".
idtac "Possible points: 3".
check_type @Himp.hoare_havoc (
(forall (Q : Assertion) (X : String.string),
 Himp.valid_hoare_triple (Himp.havoc_pre X Q) (Himp.CHavoc X) Q)).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.hoare_havoc.
Goal True.
idtac " ".

idtac "-------------------  havoc_post  --------------------".
idtac " ".

idtac "#> Himp.havoc_post".
idtac "Advanced".
idtac "Possible points: 3".
check_type @Himp.havoc_post (
(forall (P : Assertion) (X : String.string),
 Himp.valid_hoare_triple P (Himp.CHavoc X)
   (fun st : state => @ex nat (fun n : nat => assertion_sub X (ANum n) P st)))).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.havoc_post.
Goal True.
idtac " ".

idtac "-------------------  assert_vs_assume  --------------------".
idtac " ".

idtac "#> HoareAssertAssume.assert_assume_differ".
idtac "Possible points: 1".
check_type @HoareAssertAssume.assert_assume_differ (
(@ex Assertion
   (fun P : Assertion =>
    @ex bexp
      (fun b : bexp =>
       @ex Assertion
         (fun Q : Assertion =>
          and
            (HoareAssertAssume.valid_hoare_triple P
               (HoareAssertAssume.CAssume b) Q)
            (not
               (HoareAssertAssume.valid_hoare_triple P
                  (HoareAssertAssume.CAssert b) Q))))))).
idtac "Assumptions:".
Abort.
Print Assumptions HoareAssertAssume.assert_assume_differ.
Goal True.
idtac " ".

idtac "#> HoareAssertAssume.assert_implies_assume".
idtac "Possible points: 1".
check_type @HoareAssertAssume.assert_implies_assume (
(forall (P : Assertion) (b : bexp) (Q : Assertion)
   (_ : HoareAssertAssume.valid_hoare_triple P (HoareAssertAssume.CAssert b)
          Q),
 HoareAssertAssume.valid_hoare_triple P (HoareAssertAssume.CAssume b) Q)).
idtac "Assumptions:".
Abort.
Print Assumptions HoareAssertAssume.assert_implies_assume.
Goal True.
idtac " ".

idtac "#> HoareAssertAssume.assert_assume_example".
idtac "Possible points: 4".
check_type @HoareAssertAssume.assert_assume_example (
(HoareAssertAssume.valid_hoare_triple (fun _ : state => True)
   (HoareAssertAssume.CSeq (HoareAssertAssume.CAssume (BEq (AId X) (ANum 1)))
      (HoareAssertAssume.CSeq
         (HoareAssertAssume.CAsgn X (APlus (AId X) (ANum 1)))
         (HoareAssertAssume.CAssert (BEq (AId X) (ANum 2)))))
   (fun _ : state => True))).
idtac "Assumptions:".
Abort.
Print Assumptions HoareAssertAssume.assert_assume_example.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 25".
idtac "Max points - advanced: 40".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "CSeq_congruence".
idtac "fold_constants_bexp_sound".
idtac "succ_hastype_nat__hastype_nat".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- hoare_post_true ---------".
Print Assumptions hoare_post_true.
idtac "---------- hoare_pre_false ---------".
Print Assumptions hoare_pre_false.
idtac "---------- hoare_asgn_wrong ---------".
Print Assumptions hoare_asgn_wrong.
idtac "---------- assertion_sub_ex1' ---------".
Print Assumptions assertion_sub_ex1'.
idtac "---------- assertion_sub_ex2' ---------".
Print Assumptions assertion_sub_ex2'.
idtac "---------- hoare_asgn_example4 ---------".
Print Assumptions hoare_asgn_example4.
idtac "---------- swap_exercise ---------".
Print Assumptions swap_exercise.
idtac "---------- if_minus_plus ---------".
Print Assumptions if_minus_plus.
idtac "---------- If1.if1true_test ---------".
Print Assumptions If1.if1true_test.
idtac "---------- If1.if1false_test ---------".
Print Assumptions If1.if1false_test.
idtac "---------- hoare_if1 ---------".
idtac "MANUAL".
idtac "---------- If1.hoare_if1_good ---------".
Print Assumptions If1.hoare_if1_good.
idtac "---------- HoareAssertAssume.assert_assume_differ ---------".
Print Assumptions HoareAssertAssume.assert_assume_differ.
idtac "---------- HoareAssertAssume.assert_implies_assume ---------".
Print Assumptions HoareAssertAssume.assert_implies_assume.
idtac "---------- HoareAssertAssume.assert_assume_example ---------".
Print Assumptions HoareAssertAssume.assert_assume_example.
idtac "".
idtac "********** Advanced **********".
idtac "---------- hoare_asgn_fwd ---------".
Print Assumptions hoare_asgn_fwd.
idtac "---------- invalid_triple ---------".
Print Assumptions invalid_triple.
idtac "---------- Himp.hoare_havoc ---------".
Print Assumptions Himp.hoare_havoc.
idtac "---------- Himp.havoc_post ---------".
Print Assumptions Himp.havoc_post.
Abort.

(* 2025-08-24 14:28 *)

(* 2025-08-24 14:29 *)
