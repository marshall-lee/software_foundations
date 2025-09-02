Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From PLF Require Import Equiv.

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

From PLF Require Import Equiv.
Import Check.

Goal True.

idtac "-------------------  skip_right  --------------------".
idtac " ".

idtac "#> skip_right".
idtac "Possible points: 2".
check_type @skip_right ((forall c : com, cequiv (CSeq c CSkip) c)).
idtac "Assumptions:".
Abort.
Print Assumptions skip_right.
Goal True.
idtac " ".

idtac "-------------------  if_false  --------------------".
idtac " ".

idtac "#> if_false".
idtac "Possible points: 2".
check_type @if_false (
(forall (b : bexp) (c1 c2 : com) (_ : bequiv b BFalse),
 cequiv (CIf b c1 c2) c2)).
idtac "Assumptions:".
Abort.
Print Assumptions if_false.
Goal True.
idtac " ".

idtac "-------------------  swap_if_branches  --------------------".
idtac " ".

idtac "#> swap_if_branches".
idtac "Possible points: 3".
check_type @swap_if_branches (
(forall (b : bexp) (c1 c2 : com), cequiv (CIf b c1 c2) (CIf (BNot b) c2 c1))).
idtac "Assumptions:".
Abort.
Print Assumptions swap_if_branches.
Goal True.
idtac " ".

idtac "-------------------  while_true  --------------------".
idtac " ".

idtac "#> while_true".
idtac "Possible points: 2".
check_type @while_true (
(forall (b : bexp) (c : com) (_ : bequiv b BTrue),
 cequiv (CWhile b c) (CWhile BTrue CSkip))).
idtac "Assumptions:".
Abort.
Print Assumptions while_true.
Goal True.
idtac " ".

idtac "-------------------  assign_aequiv  --------------------".
idtac " ".

idtac "#> assign_aequiv".
idtac "Possible points: 2".
check_type @assign_aequiv (
(forall (X : String.string) (a : aexp) (_ : aequiv (AId X) a),
 cequiv CSkip (CAsgn X a))).
idtac "Assumptions:".
Abort.
Print Assumptions assign_aequiv.
Goal True.
idtac " ".

idtac "-------------------  equiv_classes  --------------------".
idtac " ".

idtac "#> Manually graded: equiv_classes".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_equiv_classes.
idtac " ".

idtac "-------------------  CIf_congruence  --------------------".
idtac " ".

idtac "#> CIf_congruence".
idtac "Possible points: 3".
check_type @CIf_congruence (
(forall (b b' : bexp) (c1 c1' c2 c2' : com) (_ : bequiv b b')
   (_ : cequiv c1 c1') (_ : cequiv c2 c2'),
 cequiv (CIf b c1 c2) (CIf b' c1' c2'))).
idtac "Assumptions:".
Abort.
Print Assumptions CIf_congruence.
Goal True.
idtac " ".

idtac "-------------------  not_congr  --------------------".
idtac " ".

idtac "#> Manually graded: not_congr".
idtac "Advanced".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_not_congr.
idtac " ".

idtac "-------------------  fold_constants_com_sound  --------------------".
idtac " ".

idtac "#> fold_constants_com_sound".
idtac "Possible points: 3".
check_type @fold_constants_com_sound ((ctrans_sound fold_constants_com)).
idtac "Assumptions:".
Abort.
Print Assumptions fold_constants_com_sound.
Goal True.
idtac " ".

idtac "-------------------  inequiv_exercise  --------------------".
idtac " ".

idtac "#> inequiv_exercise".
idtac "Possible points: 3".
check_type @inequiv_exercise ((not (cequiv (CWhile BTrue CSkip) CSkip))).
idtac "Assumptions:".
Abort.
Print Assumptions inequiv_exercise.
Goal True.
idtac " ".

idtac "-------------------  himp_ceval  --------------------".
idtac " ".

idtac "#> Manually graded: Himp.Check_rule_for_HAVOC".
idtac "Possible points: 2".
print_manual_grade Himp.manual_grade_for_Check_rule_for_HAVOC.
idtac " ".

idtac "-------------------  havoc_swap  --------------------".
idtac " ".

idtac "#> Himp.pXY_cequiv_pYX".
idtac "Possible points: 3".
check_type @Himp.pXY_cequiv_pYX (
(or (Himp.cequiv Himp.pXY Himp.pYX) (not (Himp.cequiv Himp.pXY Himp.pYX)))).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.pXY_cequiv_pYX.
Goal True.
idtac " ".

idtac "-------------------  p1_p2_term  --------------------".
idtac " ".

idtac "#> Himp.p1_may_diverge".
idtac "Advanced".
idtac "Possible points: 3".
check_type @Himp.p1_may_diverge (
(forall (st : forall _ : String.string, nat) (st' : state)
   (_ : not (@eq nat (st X) 0)),
 not (Himp.ceval Himp.p1 st st'))).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.p1_may_diverge.
Goal True.
idtac " ".

idtac "#> Himp.p2_may_diverge".
idtac "Advanced".
idtac "Possible points: 3".
check_type @Himp.p2_may_diverge (
(forall (st : forall _ : String.string, nat) (st' : state)
   (_ : not (@eq nat (st X) 0)),
 not (Himp.ceval Himp.p2 st st'))).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.p2_may_diverge.
Goal True.
idtac " ".

idtac "-------------------  p1_p2_equiv  --------------------".
idtac " ".

idtac "#> Himp.p1_p2_equiv".
idtac "Advanced".
idtac "Possible points: 6".
check_type @Himp.p1_p2_equiv ((Himp.cequiv Himp.p1 Himp.p2)).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.p1_p2_equiv.
Goal True.
idtac " ".

idtac "-------------------  p3_p4_inequiv  --------------------".
idtac " ".

idtac "#> Himp.p3_p4_inequiv".
idtac "Advanced".
idtac "Possible points: 6".
check_type @Himp.p3_p4_inequiv ((not (Himp.cequiv Himp.p3 Himp.p4))).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.p3_p4_inequiv.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 27".
idtac "Max points - advanced: 48".
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
idtac "---------- skip_right ---------".
Print Assumptions skip_right.
idtac "---------- if_false ---------".
Print Assumptions if_false.
idtac "---------- swap_if_branches ---------".
Print Assumptions swap_if_branches.
idtac "---------- while_true ---------".
Print Assumptions while_true.
idtac "---------- assign_aequiv ---------".
Print Assumptions assign_aequiv.
idtac "---------- equiv_classes ---------".
idtac "MANUAL".
idtac "---------- CIf_congruence ---------".
Print Assumptions CIf_congruence.
idtac "---------- fold_constants_com_sound ---------".
Print Assumptions fold_constants_com_sound.
idtac "---------- inequiv_exercise ---------".
Print Assumptions inequiv_exercise.
idtac "---------- Check_rule_for_HAVOC ---------".
idtac "MANUAL".
idtac "---------- Himp.pXY_cequiv_pYX ---------".
Print Assumptions Himp.pXY_cequiv_pYX.
idtac "".
idtac "********** Advanced **********".
idtac "---------- not_congr ---------".
idtac "MANUAL".
idtac "---------- Himp.p1_may_diverge ---------".
Print Assumptions Himp.p1_may_diverge.
idtac "---------- Himp.p2_may_diverge ---------".
Print Assumptions Himp.p2_may_diverge.
idtac "---------- Himp.p1_p2_equiv ---------".
Print Assumptions Himp.p1_p2_equiv.
idtac "---------- Himp.p3_p4_inequiv ---------".
Print Assumptions Himp.p3_p4_inequiv.
Abort.

(* 2025-08-24 14:28 *)

(* 2025-08-24 14:29 *)
