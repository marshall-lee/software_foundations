Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From PLF Require Import Typechecking.

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

From PLF Require Import Typechecking.
Import Check.

Goal True.

idtac "-------------------  type_check_defn  --------------------".
idtac " ".

idtac "#> Manually graded: TypecheckerExtensions.type_check_defn".
idtac "Possible points: 6".
print_manual_grade TypecheckerExtensions.manual_grade_for_type_check_defn.
idtac " ".

idtac "-------------------  ext_type_checking_sound  --------------------".
idtac " ".

idtac "#> TypecheckerExtensions.type_checking_sound".
idtac "Possible points: 2".
check_type @TypecheckerExtensions.type_checking_sound (
(forall (Gamma : MoreStlc.STLCExtended.context)
   (t : MoreStlc.STLCExtended.tm) (T : MoreStlc.STLCExtended.ty)
   (_ : @eq (option MoreStlc.STLCExtended.ty)
          (TypecheckerExtensions.type_check Gamma t)
          (@Some MoreStlc.STLCExtended.ty T)),
 MoreStlc.STLCExtended.has_type Gamma t T)).
idtac "Assumptions:".
Abort.
Print Assumptions TypecheckerExtensions.type_checking_sound.
Goal True.
idtac " ".

idtac "-------------------  ext_type_checking_complete  --------------------".
idtac " ".

idtac "#> TypecheckerExtensions.type_checking_complete".
idtac "Possible points: 2".
check_type @TypecheckerExtensions.type_checking_complete (
(forall (Gamma : MoreStlc.STLCExtended.context)
   (t : MoreStlc.STLCExtended.tm) (T : MoreStlc.STLCExtended.ty)
   (_ : MoreStlc.STLCExtended.has_type Gamma t T),
 @eq (option MoreStlc.STLCExtended.ty)
   (TypecheckerExtensions.type_check Gamma t)
   (@Some MoreStlc.STLCExtended.ty T))).
idtac "Assumptions:".
Abort.
Print Assumptions TypecheckerExtensions.type_checking_complete.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 10".
idtac "Max points - advanced: 10".
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
idtac "---------- type_check_defn ---------".
idtac "MANUAL".
idtac "---------- TypecheckerExtensions.type_checking_sound ---------".
Print Assumptions TypecheckerExtensions.type_checking_sound.
idtac "---------- TypecheckerExtensions.type_checking_complete ---------".
Print Assumptions TypecheckerExtensions.type_checking_complete.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2025-08-24 14:29 *)

(* 2025-08-24 14:29 *)
