Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From PLF Require Import References.

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

From PLF Require Import References.
Import Check.

Goal True.

idtac "-------------------  compact_update  --------------------".
idtac " ".

idtac "#> Manually graded: STLCRef.compact_update".
idtac "Possible points: 2".
print_manual_grade STLCRef.manual_grade_for_compact_update.
idtac " ".

idtac "-------------------  type_safety_violation  --------------------".
idtac " ".

idtac "#> Manually graded: STLCRef.type_safety_violation".
idtac "Possible points: 2".
print_manual_grade STLCRef.manual_grade_for_type_safety_violation.
idtac " ".

idtac "-------------------  cyclic_store  --------------------".
idtac " ".

idtac "#> STLCRef.cyclic_store".
idtac "Possible points: 3".
check_type @STLCRef.cyclic_store (
(@ex STLCRef.tm
   (fun t : STLCRef.tm =>
    STLCRef.multistep
      (@pair STLCRef.tm (list STLCRef.tm) t (@nil STLCRef.tm))
      (@pair STLCRef.tm (list STLCRef.tm) STLCRef.tm_unit
         (@cons STLCRef.tm
            (STLCRef.tm_abs STLCRef.x STLCRef.Ty_Nat
               (STLCRef.tm_app (STLCRef.tm_deref (STLCRef.tm_loc 1))
                  (STLCRef.tm_var STLCRef.x)))
            (@cons STLCRef.tm
               (STLCRef.tm_abs STLCRef.x STLCRef.Ty_Nat
                  (STLCRef.tm_app (STLCRef.tm_deref (STLCRef.tm_loc 0))
                     (STLCRef.tm_var STLCRef.x)))
               (@nil STLCRef.tm))))))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCRef.cyclic_store.
Goal True.
idtac " ".

idtac "-------------------  store_not_unique  --------------------".
idtac " ".

idtac "#> STLCRef.store_not_unique".
idtac "Possible points: 3".
check_type @STLCRef.store_not_unique (
(@ex STLCRef.store
   (fun st : STLCRef.store =>
    @ex STLCRef.store_ty
      (fun ST1 : STLCRef.store_ty =>
       @ex STLCRef.store_ty
         (fun ST2 : STLCRef.store_ty =>
          and (STLCRef.store_well_typed ST1 st)
            (and (STLCRef.store_well_typed ST2 st)
               (not (@eq STLCRef.store_ty ST1 ST2)))))))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCRef.store_not_unique.
Goal True.
idtac " ".

idtac "-------------------  preservation_informal  --------------------".
idtac " ".

idtac "#> Manually graded: STLCRef.preservation_informal".
idtac "Possible points: 3".
print_manual_grade STLCRef.manual_grade_for_preservation_informal.
idtac " ".

idtac "-------------------  factorial_ref  --------------------".
idtac " ".

idtac "#> STLCRef.RefsAndNontermination.factorial".
idtac "Possible points: 3".
check_type @STLCRef.RefsAndNontermination.factorial (STLCRef.tm).
idtac "Assumptions:".
Abort.
Print Assumptions STLCRef.RefsAndNontermination.factorial.
Goal True.
idtac " ".

idtac "#> STLCRef.RefsAndNontermination.factorial_type".
idtac "Possible points: 3".
check_type @STLCRef.RefsAndNontermination.factorial_type (
(STLCRef.has_type (@nil STLCRef.ty) (@Maps.empty STLCRef.ty)
   STLCRef.RefsAndNontermination.factorial
   (STLCRef.Ty_Arrow STLCRef.Ty_Nat STLCRef.Ty_Nat))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCRef.RefsAndNontermination.factorial_type.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 19".
idtac "Max points - advanced: 19".
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
idtac "---------- compact_update ---------".
idtac "MANUAL".
idtac "---------- type_safety_violation ---------".
idtac "MANUAL".
idtac "---------- STLCRef.cyclic_store ---------".
Print Assumptions STLCRef.cyclic_store.
idtac "---------- STLCRef.store_not_unique ---------".
Print Assumptions STLCRef.store_not_unique.
idtac "---------- preservation_informal ---------".
idtac "MANUAL".
idtac "---------- STLCRef.RefsAndNontermination.factorial ---------".
Print Assumptions STLCRef.RefsAndNontermination.factorial.
idtac "---------- STLCRef.RefsAndNontermination.factorial_type ---------".
Print Assumptions STLCRef.RefsAndNontermination.factorial_type.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2025-08-24 14:29 *)

(* 2025-08-24 14:29 *)
