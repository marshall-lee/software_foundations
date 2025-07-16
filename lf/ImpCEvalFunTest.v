Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import ImpCEvalFun.

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

From LF Require Import ImpCEvalFun.
Import Check.

Goal True.

idtac "-------------------  ceval_step__ceval_inf  --------------------".
idtac " ".

idtac "#> Manually graded: ceval_step__ceval_inf".
idtac "Advanced".
idtac "Possible points: 6".
print_manual_grade manual_grade_for_ceval_step__ceval_inf.
idtac " ".

idtac "-------------------  ceval__ceval_step  --------------------".
idtac " ".

idtac "#> ceval__ceval_step".
idtac "Possible points: 3".
check_type @ceval__ceval_step (
(forall (c : Imp.com) (st st' : Imp.state),
 Imp.ceval c st st' ->
 exists i : nat, ceval_step st c i = @Some Imp.state st')).
idtac "Assumptions:".
Abort.
Print Assumptions ceval__ceval_step.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 3".
idtac "Max points - advanced: 9".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "plus_le".
idtac "le_trans".
idtac "le_plus_l".
idtac "add_le_cases".
idtac "Sn_le_Sm__n_le_m".
idtac "O_le_n".
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
idtac "---------- ceval__ceval_step ---------".
Print Assumptions ceval__ceval_step.
idtac "".
idtac "********** Advanced **********".
idtac "---------- ceval_step__ceval_inf ---------".
idtac "MANUAL".
Abort.

(* 2025-01-13 16:00 *)

(* 2025-01-13 16:00 *)
