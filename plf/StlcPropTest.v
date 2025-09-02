Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From PLF Require Import StlcProp.

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

From PLF Require Import StlcProp.
Import Check.

Goal True.

idtac "-------------------  progress_from_term_ind  --------------------".
idtac " ".

idtac "#> STLCProp.progress'".
idtac "Advanced".
idtac "Possible points: 3".
check_type @STLCProp.progress' (
(forall (t : Stlc.STLC.tm) (T : Stlc.STLC.ty)
   (_ : Stlc.STLC.has_type (@Maps.empty Stlc.STLC.ty) t T),
 or (Stlc.STLC.value t)
   (@ex Stlc.STLC.tm (fun t' : Stlc.STLC.tm => Stlc.STLC.step t t')))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCProp.progress'.
Goal True.
idtac " ".

idtac "-------------------  substitution_preserves_typing_from_typing_ind  --------------------".
idtac " ".

idtac "#> STLCProp.substitution_preserves_typing_from_typing_ind".
idtac "Advanced".
idtac "Possible points: 3".
check_type @STLCProp.substitution_preserves_typing_from_typing_ind (
(forall (Gamma : Maps.partial_map Stlc.STLC.ty) (x : String.string)
   (U : Stlc.STLC.ty) (t v : Stlc.STLC.tm) (T : Stlc.STLC.ty)
   (_ : Stlc.STLC.has_type (@Maps.update Stlc.STLC.ty Gamma x U) t T)
   (_ : Stlc.STLC.has_type (@Maps.empty Stlc.STLC.ty) v U),
 Stlc.STLC.has_type Gamma (Stlc.STLC.subst x v t) T)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCProp.substitution_preserves_typing_from_typing_ind.
Goal True.
idtac " ".

idtac "-------------------  subject_expansion_stlc  --------------------".
idtac " ".

idtac "#> Manually graded: STLCProp.subject_expansion_stlc".
idtac "Possible points: 2".
print_manual_grade STLCProp.manual_grade_for_subject_expansion_stlc.
idtac " ".

idtac "-------------------  unique_types  --------------------".
idtac " ".

idtac "#> STLCProp.unique_types".
idtac "Possible points: 3".
check_type @STLCProp.unique_types (
(forall (Gamma : Stlc.STLC.context) (e : Stlc.STLC.tm)
   (T T' : Stlc.STLC.ty) (_ : Stlc.STLC.has_type Gamma e T)
   (_ : Stlc.STLC.has_type Gamma e T'),
 @eq Stlc.STLC.ty T T')).
idtac "Assumptions:".
Abort.
Print Assumptions STLCProp.unique_types.
Goal True.
idtac " ".

idtac "-------------------  free_in_context  --------------------".
idtac " ".

idtac "#> STLCProp.free_in_context".
idtac "Possible points: 2".
check_type @STLCProp.free_in_context (
(forall (x : String.string) (t : Stlc.STLC.tm) (T : Stlc.STLC.ty)
   (Gamma : Stlc.STLC.context) (_ : STLCProp.appears_free_in x t)
   (_ : Stlc.STLC.has_type Gamma t T),
 @ex Stlc.STLC.ty
   (fun T' : Stlc.STLC.ty =>
    @eq (option Stlc.STLC.ty) (Gamma x) (@Some Stlc.STLC.ty T')))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCProp.free_in_context.
Goal True.
idtac " ".

idtac "-------------------  stlc_variation1  --------------------".
idtac " ".

idtac "#> Manually graded: STLCProp.stlc_variation1".
idtac "Possible points: 2".
print_manual_grade STLCProp.manual_grade_for_stlc_variation1.
idtac " ".

idtac "-------------------  stlc_variation2  --------------------".
idtac " ".

idtac "#> Manually graded: STLCProp.stlc_variation2".
idtac "Possible points: 2".
print_manual_grade STLCProp.manual_grade_for_stlc_variation2.
idtac " ".

idtac "-------------------  stlc_variation3  --------------------".
idtac " ".

idtac "#> Manually graded: STLCProp.stlc_variation3".
idtac "Possible points: 2".
print_manual_grade STLCProp.manual_grade_for_stlc_variation3.
idtac " ".

idtac "-------------------  STLCArith.subst  --------------------".
idtac " ".

idtac "#> STLCArith.subst".
idtac "Possible points: 10".
check_type @STLCArith.subst (
(forall (_ : String.string) (_ : STLCArith.tm) (_ : STLCArith.tm),
 STLCArith.tm)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCArith.subst.
Goal True.
idtac " ".

idtac "-------------------  STLCArith.weakening  --------------------".
idtac " ".

idtac "#> STLCArith.weakening".
idtac "Possible points: 6".
check_type @STLCArith.weakening (
(forall (Gamma Gamma' : Maps.partial_map STLCArith.ty)
   (t : STLCArith.tm) (T : STLCArith.ty)
   (_ : @Maps.includedin STLCArith.ty Gamma Gamma')
   (_ : STLCArith.has_type Gamma t T),
 STLCArith.has_type Gamma' t T)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCArith.weakening.
Goal True.
idtac " ".

idtac "-------------------  STLCArith.preservation  --------------------".
idtac " ".

idtac "#> STLCArith.preservation".
idtac "Possible points: 6".
check_type @STLCArith.preservation (
(forall (t t' : STLCArith.tm) (T : STLCArith.ty)
   (_ : STLCArith.has_type (@Maps.empty STLCArith.ty) t T)
   (_ : STLCArith.step t t'),
 STLCArith.has_type (@Maps.empty STLCArith.ty) t' T)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCArith.preservation.
Goal True.
idtac " ".

idtac "-------------------  STLCArith.progress  --------------------".
idtac " ".

idtac "#> STLCArith.progress".
idtac "Possible points: 6".
check_type @STLCArith.progress (
(forall (t : STLCArith.tm) (T : STLCArith.ty)
   (_ : STLCArith.has_type (@Maps.empty STLCArith.ty) t T),
 or (STLCArith.value t)
   (@ex STLCArith.tm (fun t' : STLCArith.tm => STLCArith.step t t')))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCArith.progress.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 41".
idtac "Max points - advanced: 47".
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
idtac "---------- subject_expansion_stlc ---------".
idtac "MANUAL".
idtac "---------- STLCProp.unique_types ---------".
Print Assumptions STLCProp.unique_types.
idtac "---------- STLCProp.free_in_context ---------".
Print Assumptions STLCProp.free_in_context.
idtac "---------- stlc_variation1 ---------".
idtac "MANUAL".
idtac "---------- stlc_variation2 ---------".
idtac "MANUAL".
idtac "---------- stlc_variation3 ---------".
idtac "MANUAL".
idtac "---------- STLCArith.subst ---------".
Print Assumptions STLCArith.subst.
idtac "---------- STLCArith.weakening ---------".
Print Assumptions STLCArith.weakening.
idtac "---------- STLCArith.preservation ---------".
Print Assumptions STLCArith.preservation.
idtac "---------- STLCArith.progress ---------".
Print Assumptions STLCArith.progress.
idtac "".
idtac "********** Advanced **********".
idtac "---------- STLCProp.progress' ---------".
Print Assumptions STLCProp.progress'.
idtac "---------- STLCProp.substitution_preserves_typing_from_typing_ind ---------".
Print Assumptions STLCProp.substitution_preserves_typing_from_typing_ind.
Abort.

(* 2025-08-24 14:29 *)

(* 2025-08-24 14:29 *)
