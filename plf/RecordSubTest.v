Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From PLF Require Import RecordSub.

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

From PLF Require Import RecordSub.
Import Check.

Goal True.

idtac "-------------------  subtyping_example_1  --------------------".
idtac " ".

idtac "#> RecordSub.Examples.subtyping_example_1".
idtac "Possible points: 2".
check_type @RecordSub.Examples.subtyping_example_1 (
(RecordSub.subtype RecordSub.Examples.TRcd_kj RecordSub.Examples.TRcd_j)).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.Examples.subtyping_example_1.
Goal True.
idtac " ".

idtac "-------------------  subtyping_example_2  --------------------".
idtac " ".

idtac "#> RecordSub.Examples.subtyping_example_2".
idtac "Possible points: 1".
check_type @RecordSub.Examples.subtyping_example_2 (
(RecordSub.subtype
   (RecordSub.Ty_Arrow RecordSub.Ty_Top RecordSub.Examples.TRcd_kj)
   (RecordSub.Ty_Arrow
      (RecordSub.Ty_Arrow
         (RecordSub.Ty_Base
            (String.String
               (Ascii.Ascii true true false false false false true false)
               String.EmptyString))
         (RecordSub.Ty_Base
            (String.String
               (Ascii.Ascii true true false false false false true false)
               String.EmptyString)))
      RecordSub.Examples.TRcd_j))).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.Examples.subtyping_example_2.
Goal True.
idtac " ".

idtac "-------------------  subtyping_example_3  --------------------".
idtac " ".

idtac "#> RecordSub.Examples.subtyping_example_3".
idtac "Possible points: 1".
check_type @RecordSub.Examples.subtyping_example_3 (
(RecordSub.subtype
   (RecordSub.Ty_Arrow RecordSub.Ty_RNil
      (RecordSub.Ty_RCons
         (String.String
            (Ascii.Ascii false true false true false true true false)
            String.EmptyString)
         (RecordSub.Ty_Base
            (String.String
               (Ascii.Ascii true false false false false false true false)
               String.EmptyString))
         RecordSub.Ty_RNil))
   (RecordSub.Ty_Arrow
      (RecordSub.Ty_RCons
         (String.String
            (Ascii.Ascii true true false true false true true false)
            String.EmptyString)
         (RecordSub.Ty_Base
            (String.String
               (Ascii.Ascii false true false false false false true false)
               String.EmptyString))
         RecordSub.Ty_RNil)
      RecordSub.Ty_RNil))).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.Examples.subtyping_example_3.
Goal True.
idtac " ".

idtac "-------------------  subtyping_example_4  --------------------".
idtac " ".

idtac "#> RecordSub.Examples.subtyping_example_4".
idtac "Possible points: 2".
check_type @RecordSub.Examples.subtyping_example_4 (
(RecordSub.subtype
   (RecordSub.Ty_RCons
      (String.String
         (Ascii.Ascii false false false true true true true false)
         String.EmptyString)
      (RecordSub.Ty_Base
         (String.String
            (Ascii.Ascii true false false false false false true false)
            String.EmptyString))
      (RecordSub.Ty_RCons
         (String.String
            (Ascii.Ascii true false false true true true true false)
            String.EmptyString)
         (RecordSub.Ty_Base
            (String.String
               (Ascii.Ascii false true false false false false true false)
               String.EmptyString))
         (RecordSub.Ty_RCons
            (String.String
               (Ascii.Ascii false true false true true true true false)
               String.EmptyString)
            (RecordSub.Ty_Base
               (String.String
                  (Ascii.Ascii true true false false false false true false)
                  String.EmptyString))
            RecordSub.Ty_RNil)))
   (RecordSub.Ty_RCons
      (String.String (Ascii.Ascii false true false true true true true false)
         String.EmptyString)
      (RecordSub.Ty_Base
         (String.String
            (Ascii.Ascii true true false false false false true false)
            String.EmptyString))
      (RecordSub.Ty_RCons
         (String.String
            (Ascii.Ascii true false false true true true true false)
            String.EmptyString)
         (RecordSub.Ty_Base
            (String.String
               (Ascii.Ascii false true false false false false true false)
               String.EmptyString))
         (RecordSub.Ty_RCons
            (String.String
               (Ascii.Ascii false false false true true true true false)
               String.EmptyString)
            (RecordSub.Ty_Base
               (String.String
                  (Ascii.Ascii true false false false false false true false)
                  String.EmptyString))
            RecordSub.Ty_RNil))))).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.Examples.subtyping_example_4.
Goal True.
idtac " ".

idtac "-------------------  rcd_types_match_informal  --------------------".
idtac " ".

idtac "#> Manually graded: RecordSub.rcd_types_match_informal".
idtac "Possible points: 3".
print_manual_grade RecordSub.manual_grade_for_rcd_types_match_informal.
idtac " ".

idtac "-------------------  typing_example_0  --------------------".
idtac " ".

idtac "#> RecordSub.Examples2.typing_example_0".
idtac "Possible points: 1".
check_type @RecordSub.Examples2.typing_example_0 (
(RecordSub.has_type (@Maps.empty RecordSub.ty) RecordSub.Examples2.trcd_kj
   RecordSub.Examples.TRcd_kj)).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.Examples2.typing_example_0.
Goal True.
idtac " ".

idtac "-------------------  typing_example_1  --------------------".
idtac " ".

idtac "#> RecordSub.Examples2.typing_example_1".
idtac "Possible points: 2".
check_type @RecordSub.Examples2.typing_example_1 (
(RecordSub.has_type (@Maps.empty RecordSub.ty)
   (RecordSub.tm_app
      (RecordSub.tm_abs
         (String.String
            (Ascii.Ascii false false false true true true true false)
            String.EmptyString)
         RecordSub.Examples.TRcd_j
         (RecordSub.tm_rproj
            (RecordSub.tm_var
               (String.String
                  (Ascii.Ascii false false false true true true true false)
                  String.EmptyString))
            (String.String
               (Ascii.Ascii false true false true false true true false)
               String.EmptyString)))
      RecordSub.Examples2.trcd_kj)
   (RecordSub.Ty_Arrow
      (RecordSub.Ty_Base
         (String.String
            (Ascii.Ascii false true false false false false true false)
            String.EmptyString))
      (RecordSub.Ty_Base
         (String.String
            (Ascii.Ascii false true false false false false true false)
            String.EmptyString))))).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.Examples2.typing_example_1.
Goal True.
idtac " ".

idtac "-------------------  canonical_forms_of_arrow_types  --------------------".
idtac " ".

idtac "#> RecordSub.canonical_forms_of_arrow_types".
idtac "Possible points: 3".
check_type @RecordSub.canonical_forms_of_arrow_types (
(forall (Gamma : RecordSub.context) (s : RecordSub.tm)
   (T1 T2 : RecordSub.ty)
   (_ : RecordSub.has_type Gamma s (RecordSub.Ty_Arrow T1 T2))
   (_ : RecordSub.value s),
 @ex String.string
   (fun x : String.string =>
    @ex RecordSub.ty
      (fun S1 : RecordSub.ty =>
       @ex RecordSub.tm
         (fun s2 : RecordSub.tm =>
          @eq RecordSub.tm s (RecordSub.tm_abs x S1 s2)))))).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.canonical_forms_of_arrow_types.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 15".
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
idtac "---------- RecordSub.Examples.subtyping_example_1 ---------".
Print Assumptions RecordSub.Examples.subtyping_example_1.
idtac "---------- RecordSub.Examples.subtyping_example_2 ---------".
Print Assumptions RecordSub.Examples.subtyping_example_2.
idtac "---------- RecordSub.Examples.subtyping_example_3 ---------".
Print Assumptions RecordSub.Examples.subtyping_example_3.
idtac "---------- RecordSub.Examples.subtyping_example_4 ---------".
Print Assumptions RecordSub.Examples.subtyping_example_4.
idtac "---------- rcd_types_match_informal ---------".
idtac "MANUAL".
idtac "---------- RecordSub.Examples2.typing_example_0 ---------".
Print Assumptions RecordSub.Examples2.typing_example_0.
idtac "---------- RecordSub.Examples2.typing_example_1 ---------".
Print Assumptions RecordSub.Examples2.typing_example_1.
idtac "---------- RecordSub.canonical_forms_of_arrow_types ---------".
Print Assumptions RecordSub.canonical_forms_of_arrow_types.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2025-08-24 14:29 *)

(* 2025-08-24 14:29 *)
