Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From PLF Require Import Types.

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

From PLF Require Import Types.
Import Check.

Goal True.

idtac "-------------------  some_term_is_stuck  --------------------".
idtac " ".

idtac "#> TM.some_term_is_stuck".
idtac "Possible points: 2".
check_type @TM.some_term_is_stuck ((@ex TM.tm (fun t : TM.tm => TM.stuck t))).
idtac "Assumptions:".
Abort.
Print Assumptions TM.some_term_is_stuck.
Goal True.
idtac " ".

idtac "-------------------  value_is_nf  --------------------".
idtac " ".

idtac "#> TM.value_is_nf".
idtac "Possible points: 3".
check_type @TM.value_is_nf (
(forall (t : TM.tm) (_ : TM.value t), @Smallstep.normal_form TM.tm TM.step t)).
idtac "Assumptions:".
Abort.
Print Assumptions TM.value_is_nf.
Goal True.
idtac " ".

idtac "-------------------  finish_progress  --------------------".
idtac " ".

idtac "#> TM.progress".
idtac "Possible points: 3".
check_type @TM.progress (
(forall (t : TM.tm) (T : TM.ty) (_ : TM.has_type t T),
 or (TM.value t) (@ex TM.tm (fun t' : TM.tm => TM.step t t')))).
idtac "Assumptions:".
Abort.
Print Assumptions TM.progress.
Goal True.
idtac " ".

idtac "-------------------  finish_progress_informal  --------------------".
idtac " ".

idtac "#> Manually graded: TM.finish_progress_informal".
idtac "Advanced".
idtac "Possible points: 3".
print_manual_grade TM.manual_grade_for_finish_progress_informal.
idtac " ".

idtac "-------------------  finish_preservation  --------------------".
idtac " ".

idtac "#> TM.preservation".
idtac "Possible points: 2".
check_type @TM.preservation (
(forall (t t' : TM.tm) (T : TM.ty) (_ : TM.has_type t T) (_ : TM.step t t'),
 TM.has_type t' T)).
idtac "Assumptions:".
Abort.
Print Assumptions TM.preservation.
Goal True.
idtac " ".

idtac "-------------------  finish_preservation_informal  --------------------".
idtac " ".

idtac "#> Manually graded: TM.finish_preservation_informal".
idtac "Advanced".
idtac "Possible points: 3".
print_manual_grade TM.manual_grade_for_finish_preservation_informal.
idtac " ".

idtac "-------------------  preservation_alternate_proof  --------------------".
idtac " ".

idtac "#> TM.preservation'".
idtac "Possible points: 3".
check_type @TM.preservation' (
(forall (t t' : TM.tm) (T : TM.ty) (_ : TM.has_type t T) (_ : TM.step t t'),
 TM.has_type t' T)).
idtac "Assumptions:".
Abort.
Print Assumptions TM.preservation'.
Goal True.
idtac " ".

idtac "-------------------  subject_expansion  --------------------".
idtac " ".

idtac "#> TM.subject_expansion".
idtac "Possible points: 3".
check_type @TM.subject_expansion (
(or
   (forall (t t' : TM.tm) (T : TM.ty)
      (_ : and (TM.step t t') (TM.has_type t' T)),
    TM.has_type t T)
   (not
      (forall (t t' : TM.tm) (T : TM.ty)
         (_ : and (TM.step t t') (TM.has_type t' T)),
       TM.has_type t T)))).
idtac "Assumptions:".
Abort.
Print Assumptions TM.subject_expansion.
Goal True.
idtac " ".

idtac "-------------------  variation1  --------------------".
idtac " ".

idtac "#> Manually graded: TM.variation1".
idtac "Possible points: 2".
print_manual_grade TM.manual_grade_for_variation1.
idtac " ".

idtac "-------------------  variation2  --------------------".
idtac " ".

idtac "#> Manually graded: TM.variation2".
idtac "Possible points: 2".
print_manual_grade TM.manual_grade_for_variation2.
idtac " ".

idtac "-------------------  remove_pred0  --------------------".
idtac " ".

idtac "#> Manually graded: TM.remove_pred0".
idtac "Possible points: 1".
print_manual_grade TM.manual_grade_for_remove_pred0.
idtac " ".

idtac "-------------------  prog_pres_bigstep  --------------------".
idtac " ".

idtac "#> Manually graded: TM.prog_pres_bigstep".
idtac "Advanced".
idtac "Possible points: 6".
print_manual_grade TM.manual_grade_for_prog_pres_bigstep.
idtac " ".

idtac " ".

idtac "Max points - standard: 21".
idtac "Max points - advanced: 33".
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
idtac "---------- TM.some_term_is_stuck ---------".
Print Assumptions TM.some_term_is_stuck.
idtac "---------- TM.value_is_nf ---------".
Print Assumptions TM.value_is_nf.
idtac "---------- TM.progress ---------".
Print Assumptions TM.progress.
idtac "---------- TM.preservation ---------".
Print Assumptions TM.preservation.
idtac "---------- TM.preservation' ---------".
Print Assumptions TM.preservation'.
idtac "---------- TM.subject_expansion ---------".
Print Assumptions TM.subject_expansion.
idtac "---------- variation1 ---------".
idtac "MANUAL".
idtac "---------- variation2 ---------".
idtac "MANUAL".
idtac "---------- remove_pred0 ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- finish_progress_informal ---------".
idtac "MANUAL".
idtac "---------- finish_preservation_informal ---------".
idtac "MANUAL".
idtac "---------- prog_pres_bigstep ---------".
idtac "MANUAL".
Abort.

(* 2025-08-24 14:29 *)

(* 2025-08-24 14:29 *)
