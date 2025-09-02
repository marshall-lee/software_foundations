Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From PLF Require Import MoreStlc.

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

From PLF Require Import MoreStlc.
Import Check.

Goal True.

idtac "-------------------  STLCExtended.subst  --------------------".
idtac " ".

idtac "#> STLCExtended.subst".
idtac "Possible points: 3".
check_type @STLCExtended.subst (
(forall (_ : String.string) (_ : STLCExtended.tm) (_ : STLCExtended.tm),
 STLCExtended.tm)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.subst.
Goal True.
idtac " ".

idtac "-------------------  STLCExtended.step  --------------------".
idtac " ".

idtac "#> STLCExtended.step".
idtac "Possible points: 3".
check_type @STLCExtended.step (
(forall (_ : STLCExtended.tm) (_ : STLCExtended.tm), Prop)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.step.
Goal True.
idtac " ".

idtac "-------------------  STLCExtended.has_type  --------------------".
idtac " ".

idtac "#> STLCExtended.has_type".
idtac "Possible points: 3".
check_type @STLCExtended.has_type (
(forall (_ : STLCExtended.context) (_ : STLCExtended.tm)
   (_ : STLCExtended.ty),
 Prop)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.has_type.
Goal True.
idtac " ".

idtac "-------------------  STLCExtended.progress  --------------------".
idtac " ".

idtac "#> STLCExtended.progress".
idtac "Possible points: 3".
check_type @STLCExtended.progress (
(forall (t : STLCExtended.tm) (T : STLCExtended.ty)
   (_ : STLCExtended.has_type (@Maps.empty STLCExtended.ty) t T),
 or (STLCExtended.value t)
   (@ex STLCExtended.tm (fun t' : STLCExtended.tm => STLCExtended.step t t')))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.progress.
Goal True.
idtac " ".

idtac "-------------------  STLCExtended.substitution_preserves_typing  --------------------".
idtac " ".

idtac "#> STLCExtended.substitution_preserves_typing".
idtac "Possible points: 2".
check_type @STLCExtended.substitution_preserves_typing (
(forall (Gamma : Maps.partial_map STLCExtended.ty)
   (x : String.string) (U : STLCExtended.ty) (t v : STLCExtended.tm)
   (T : STLCExtended.ty)
   (_ : STLCExtended.has_type (@Maps.update STLCExtended.ty Gamma x U) t T)
   (_ : STLCExtended.has_type (@Maps.empty STLCExtended.ty) v U),
 STLCExtended.has_type Gamma (STLCExtended.subst x v t) T)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.substitution_preserves_typing.
Goal True.
idtac " ".

idtac "-------------------  STLCExtended.preservation  --------------------".
idtac " ".

idtac "#> STLCExtended.preservation".
idtac "Possible points: 3".
check_type @STLCExtended.preservation (
(forall (t t' : STLCExtended.tm) (T : STLCExtended.ty)
   (_ : STLCExtended.has_type (@Maps.empty STLCExtended.ty) t T)
   (_ : STLCExtended.step t t'),
 STLCExtended.has_type (@Maps.empty STLCExtended.ty) t' T)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.preservation.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 17".
idtac "Max points - advanced: 17".
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
idtac "---------- STLCExtended.subst ---------".
Print Assumptions STLCExtended.subst.
idtac "---------- STLCExtended.step ---------".
Print Assumptions STLCExtended.step.
idtac "---------- STLCExtended.has_type ---------".
Print Assumptions STLCExtended.has_type.
idtac "---------- STLCExtended.progress ---------".
Print Assumptions STLCExtended.progress.
idtac "---------- STLCExtended.substitution_preserves_typing ---------".
Print Assumptions STLCExtended.substitution_preserves_typing.
idtac "---------- STLCExtended.preservation ---------".
Print Assumptions STLCExtended.preservation.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2025-08-24 14:29 *)

(* 2025-08-24 14:29 *)
