Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From PLF Require Import Hoare2.

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

From PLF Require Import Hoare2.
Import Check.

Goal True.

idtac "-------------------  if_minus_plus_correct  --------------------".
idtac " ".

idtac "#> if_minus_plus_correct".
idtac "Possible points: 2".
check_type @if_minus_plus_correct ((outer_triple_valid if_minus_plus_dec)).
idtac "Assumptions:".
Abort.
Print Assumptions if_minus_plus_correct.
Goal True.
idtac " ".

idtac "-------------------  slow_assignment  --------------------".
idtac " ".

idtac "#> slow_assignment".
idtac "Possible points: 2".
check_type @slow_assignment (
(forall m : nat, outer_triple_valid (slow_assignment_dec m))).
idtac "Assumptions:".
Abort.
Print Assumptions slow_assignment.
Goal True.
idtac " ".

idtac "-------------------  factorial_correct  --------------------".
idtac " ".

idtac "#> factorial_correct".
idtac "Advanced".
idtac "Possible points: 6".
check_type @factorial_correct ((forall m : nat, outer_triple_valid (factorial_dec m))).
idtac "Assumptions:".
Abort.
Print Assumptions factorial_correct.
Goal True.
idtac " ".

idtac "-------------------  minimum_correct  --------------------".
idtac " ".

idtac "#> minimum_correct".
idtac "Possible points: 3".
check_type @minimum_correct ((forall a b : nat, outer_triple_valid (minimum_dec a b))).
idtac "Assumptions:".
Abort.
Print Assumptions minimum_correct.
Goal True.
idtac " ".

idtac "-------------------  two_loops  --------------------".
idtac " ".

idtac "#> two_loops".
idtac "Possible points: 3".
check_type @two_loops ((forall a b c : nat, outer_triple_valid (two_loops_dec a b c))).
idtac "Assumptions:".
Abort.
Print Assumptions two_loops.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 10".
idtac "Max points - advanced: 16".
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
idtac "---------- if_minus_plus_correct ---------".
Print Assumptions if_minus_plus_correct.
idtac "---------- slow_assignment ---------".
Print Assumptions slow_assignment.
idtac "---------- minimum_correct ---------".
Print Assumptions minimum_correct.
idtac "---------- two_loops ---------".
Print Assumptions two_loops.
idtac "".
idtac "********** Advanced **********".
idtac "---------- factorial_correct ---------".
Print Assumptions factorial_correct.
Abort.

(* 2025-08-24 14:29 *)

(* 2025-08-24 14:29 *)
