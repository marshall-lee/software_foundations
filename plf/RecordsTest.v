Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From PLF Require Import Records.

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

From PLF Require Import Records.
Import Check.

Goal True.

idtac "-------------------  examples  --------------------".
idtac " ".

idtac "#> STLCExtendedRecords.typing_example_2".
idtac "Possible points: 0.5".
check_type @STLCExtendedRecords.typing_example_2 (
(STLCExtendedRecords.has_type (@Maps.empty STLCExtendedRecords.ty)
   (STLCExtendedRecords.tm_app
      (STLCExtendedRecords.tm_abs
         (String.String
            (Ascii.Ascii true false false false false true true false)
            String.EmptyString)
         (STLCExtendedRecords.Ty_RCons
            (String.String
               (Ascii.Ascii true false false true false true true false)
               (String.String
                  (Ascii.Ascii true false false false true true false false)
                  String.EmptyString))
            (STLCExtendedRecords.Ty_Arrow
               (STLCExtendedRecords.Ty_Base
                  (String.String
                     (Ascii.Ascii true false false false false false true
                        false)
                     String.EmptyString))
               (STLCExtendedRecords.Ty_Base
                  (String.String
                     (Ascii.Ascii true false false false false false true
                        false)
                     String.EmptyString)))
            (STLCExtendedRecords.Ty_RCons
               (String.String
                  (Ascii.Ascii true false false true false true true false)
                  (String.String
                     (Ascii.Ascii false true false false true true false
                        false)
                     String.EmptyString))
               (STLCExtendedRecords.Ty_Arrow
                  (STLCExtendedRecords.Ty_Base
                     (String.String
                        (Ascii.Ascii false true false false false false true
                           false)
                        String.EmptyString))
                  (STLCExtendedRecords.Ty_Base
                     (String.String
                        (Ascii.Ascii false true false false false false true
                           false)
                        String.EmptyString)))
               STLCExtendedRecords.Ty_RNil))
         (STLCExtendedRecords.tm_rproj
            (STLCExtendedRecords.tm_var
               (String.String
                  (Ascii.Ascii true false false false false true true false)
                  String.EmptyString))
            (String.String
               (Ascii.Ascii true false false true false true true false)
               (String.String
                  (Ascii.Ascii false true false false true true false false)
                  String.EmptyString))))
      (STLCExtendedRecords.tm_rcons
         (String.String
            (Ascii.Ascii true false false true false true true false)
            (String.String
               (Ascii.Ascii true false false false true true false false)
               String.EmptyString))
         (STLCExtendedRecords.tm_abs
            (String.String
               (Ascii.Ascii true false false false false true true false)
               String.EmptyString)
            (STLCExtendedRecords.Ty_Base
               (String.String
                  (Ascii.Ascii true false false false false false true false)
                  String.EmptyString))
            (STLCExtendedRecords.tm_var
               (String.String
                  (Ascii.Ascii true false false false false true true false)
                  String.EmptyString)))
         (STLCExtendedRecords.tm_rcons
            (String.String
               (Ascii.Ascii true false false true false true true false)
               (String.String
                  (Ascii.Ascii false true false false true true false false)
                  String.EmptyString))
            (STLCExtendedRecords.tm_abs
               (String.String
                  (Ascii.Ascii true false false false false true true false)
                  String.EmptyString)
               (STLCExtendedRecords.Ty_Base
                  (String.String
                     (Ascii.Ascii false true false false false false true
                        false)
                     String.EmptyString))
               (STLCExtendedRecords.tm_var
                  (String.String
                     (Ascii.Ascii true false false false false true true
                        false)
                     String.EmptyString)))
            STLCExtendedRecords.tm_rnil)))
   (STLCExtendedRecords.Ty_Arrow
      (STLCExtendedRecords.Ty_Base
         (String.String
            (Ascii.Ascii false true false false false false true false)
            String.EmptyString))
      (STLCExtendedRecords.Ty_Base
         (String.String
            (Ascii.Ascii false true false false false false true false)
            String.EmptyString))))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtendedRecords.typing_example_2.
Goal True.
idtac " ".

idtac "#> STLCExtendedRecords.typing_nonexample".
idtac "Possible points: 0.5".
check_type @STLCExtendedRecords.typing_nonexample (
(not
   (@ex STLCExtendedRecords.ty
      (fun T : STLCExtendedRecords.ty =>
       STLCExtendedRecords.has_type
         (@Maps.update STLCExtendedRecords.ty
            (@Maps.empty STLCExtendedRecords.ty)
            (String.String
               (Ascii.Ascii true false false false false true true false)
               String.EmptyString)
            (STLCExtendedRecords.Ty_RCons
               (String.String
                  (Ascii.Ascii true false false true false true true false)
                  (String.String
                     (Ascii.Ascii false true false false true true false
                        false)
                     String.EmptyString))
               (STLCExtendedRecords.Ty_Arrow
                  (STLCExtendedRecords.Ty_Base
                     (String.String
                        (Ascii.Ascii true false false false false false true
                           false)
                        String.EmptyString))
                  (STLCExtendedRecords.Ty_Base
                     (String.String
                        (Ascii.Ascii true false false false false false true
                           false)
                        String.EmptyString)))
               STLCExtendedRecords.Ty_RNil))
         (STLCExtendedRecords.tm_rcons
            (String.String
               (Ascii.Ascii true false false true false true true false)
               (String.String
                  (Ascii.Ascii true false false false true true false false)
                  String.EmptyString))
            (STLCExtendedRecords.tm_abs
               (String.String
                  (Ascii.Ascii true false false false false true true false)
                  String.EmptyString)
               (STLCExtendedRecords.Ty_Base
                  (String.String
                     (Ascii.Ascii false true false false false false true
                        false)
                     String.EmptyString))
               (STLCExtendedRecords.tm_var
                  (String.String
                     (Ascii.Ascii true false false false false true true
                        false)
                     String.EmptyString)))
            (STLCExtendedRecords.tm_var
               (String.String
                  (Ascii.Ascii true false false false false true true false)
                  String.EmptyString)))
         T)))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtendedRecords.typing_nonexample.
Goal True.
idtac " ".

idtac "#> STLCExtendedRecords.typing_nonexample_2".
idtac "Possible points: 1".
check_type @STLCExtendedRecords.typing_nonexample_2 (
(forall y : String.string,
 not
   (@ex STLCExtendedRecords.ty
      (fun T : STLCExtendedRecords.ty =>
       STLCExtendedRecords.has_type
         (@Maps.update STLCExtendedRecords.ty
            (@Maps.empty STLCExtendedRecords.ty) y
            (STLCExtendedRecords.Ty_Base
               (String.String
                  (Ascii.Ascii true false false false false false true false)
                  String.EmptyString)))
         (STLCExtendedRecords.tm_app
            (STLCExtendedRecords.tm_abs
               (String.String
                  (Ascii.Ascii true false false false false true true false)
                  String.EmptyString)
               (STLCExtendedRecords.Ty_RCons
                  (String.String
                     (Ascii.Ascii true false false true false true true false)
                     (String.String
                        (Ascii.Ascii true false false false true true false
                           false)
                        String.EmptyString))
                  (STLCExtendedRecords.Ty_Base
                     (String.String
                        (Ascii.Ascii true false false false false false true
                           false)
                        String.EmptyString))
                  STLCExtendedRecords.Ty_RNil)
               (STLCExtendedRecords.tm_rproj
                  (STLCExtendedRecords.tm_var
                     (String.String
                        (Ascii.Ascii true false false false false true true
                           false)
                        String.EmptyString))
                  (String.String
                     (Ascii.Ascii true false false true false true true false)
                     (String.String
                        (Ascii.Ascii true false false false true true false
                           false)
                        String.EmptyString))))
            (STLCExtendedRecords.tm_rcons
               (String.String
                  (Ascii.Ascii true false false true false true true false)
                  (String.String
                     (Ascii.Ascii true false false false true true false
                        false)
                     String.EmptyString))
               (STLCExtendedRecords.tm_var y)
               (STLCExtendedRecords.tm_rcons
                  (String.String
                     (Ascii.Ascii true false false true false true true false)
                     (String.String
                        (Ascii.Ascii false true false false true true false
                           false)
                        String.EmptyString))
                  (STLCExtendedRecords.tm_var y) STLCExtendedRecords.tm_rnil)))
         T)))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtendedRecords.typing_nonexample_2.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 2".
idtac "Max points - advanced: 2".
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
idtac "---------- STLCExtendedRecords.typing_example_2 ---------".
Print Assumptions STLCExtendedRecords.typing_example_2.
idtac "---------- STLCExtendedRecords.typing_nonexample ---------".
Print Assumptions STLCExtendedRecords.typing_nonexample.
idtac "---------- STLCExtendedRecords.typing_nonexample_2 ---------".
Print Assumptions STLCExtendedRecords.typing_nonexample_2.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2025-08-24 14:29 *)

(* 2025-08-24 14:29 *)
