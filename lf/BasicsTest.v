Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import Basics.

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

From LF Require Import Basics.
Import Check.

Goal True.

idtac "-------------------  nandb  --------------------".
idtac " ".

idtac "#> test_nandb4".
idtac "Possible points: 1".
check_type @test_nandb4 ((nandb true true = false)).
idtac "Assumptions:".
Abort.
Print Assumptions test_nandb4.
Goal True.
idtac " ".

idtac "-------------------  andb3  --------------------".
idtac " ".

idtac "#> test_andb34".
idtac "Possible points: 1".
check_type @test_andb34 ((andb3 true true false = false)).
idtac "Assumptions:".
Abort.
Print Assumptions test_andb34.
Goal True.
idtac " ".

idtac "-------------------  factorial  --------------------".
idtac " ".

idtac "#> test_factorial2".
idtac "Possible points: 1".
check_type @test_factorial2 ((factorial 5 = 10 * 12)).
idtac "Assumptions:".
Abort.
Print Assumptions test_factorial2.
Goal True.
idtac " ".

idtac "-------------------  ltb  --------------------".
idtac " ".

idtac "#> test_ltb3".
idtac "Possible points: 1".
check_type @test_ltb3 (((4 <? 2) = false)).
idtac "Assumptions:".
Abort.
Print Assumptions test_ltb3.
Goal True.
idtac " ".

idtac "-------------------  plus_id_exercise  --------------------".
idtac " ".

idtac "#> plus_id_exercise".
idtac "Possible points: 1".
check_type @plus_id_exercise ((forall n m o : nat, n = m -> m = o -> n + m = m + o)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_id_exercise.
Goal True.
idtac " ".

idtac "-------------------  mult_n_1  --------------------".
idtac " ".

idtac "#> mult_n_1".
idtac "Possible points: 1".
check_type @mult_n_1 ((forall p : nat, p * 1 = p)).
idtac "Assumptions:".
Abort.
Print Assumptions mult_n_1.
Goal True.
idtac " ".

idtac "-------------------  andb_true_elim2  --------------------".
idtac " ".

idtac "#> andb_true_elim2".
idtac "Possible points: 2".
check_type @andb_true_elim2 ((forall b c : bool, b && c = true -> c = true)).
idtac "Assumptions:".
Abort.
Print Assumptions andb_true_elim2.
Goal True.
idtac " ".

idtac "-------------------  zero_nbeq_plus_1  --------------------".
idtac " ".

idtac "#> zero_nbeq_plus_1".
idtac "Possible points: 1".
check_type @zero_nbeq_plus_1 ((forall n : nat, (0 =? n + 1) = false)).
idtac "Assumptions:".
Abort.
Print Assumptions zero_nbeq_plus_1.
Goal True.
idtac " ".

idtac "-------------------  identity_fn_applied_twice  --------------------".
idtac " ".

idtac "#> identity_fn_applied_twice".
idtac "Possible points: 1".
check_type @identity_fn_applied_twice (
(forall f : bool -> bool,
 (forall x : bool, f x = x) -> forall b : bool, f (f b) = b)).
idtac "Assumptions:".
Abort.
Print Assumptions identity_fn_applied_twice.
Goal True.
idtac " ".

idtac "-------------------  negation_fn_applied_twice  --------------------".
idtac " ".

idtac "#> Manually graded: negation_fn_applied_twice".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_negation_fn_applied_twice.
idtac " ".

idtac "-------------------  letter_comparison  --------------------".
idtac " ".

idtac "#> LateDays.letter_comparison_Eq".
idtac "Possible points: 1".
check_type @LateDays.letter_comparison_Eq (
(forall l : LateDays.letter, LateDays.letter_comparison l l = LateDays.Eq)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.letter_comparison_Eq.
Goal True.
idtac " ".

idtac "-------------------  grade_comparison  --------------------".
idtac " ".

idtac "#> LateDays.test_grade_comparison1".
idtac "Possible points: 0.5".
check_type @LateDays.test_grade_comparison1 (
(LateDays.grade_comparison (LateDays.Grade LateDays.A LateDays.Minus)
   (LateDays.Grade LateDays.B LateDays.Plus) = LateDays.Gt)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.test_grade_comparison1.
Goal True.
idtac " ".

idtac "#> LateDays.test_grade_comparison2".
idtac "Possible points: 0.5".
check_type @LateDays.test_grade_comparison2 (
(LateDays.grade_comparison (LateDays.Grade LateDays.A LateDays.Minus)
   (LateDays.Grade LateDays.A LateDays.Plus) = LateDays.Lt)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.test_grade_comparison2.
Goal True.
idtac " ".

idtac "#> LateDays.test_grade_comparison3".
idtac "Possible points: 0.5".
check_type @LateDays.test_grade_comparison3 (
(LateDays.grade_comparison (LateDays.Grade LateDays.F LateDays.Plus)
   (LateDays.Grade LateDays.F LateDays.Plus) = LateDays.Eq)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.test_grade_comparison3.
Goal True.
idtac " ".

idtac "#> LateDays.test_grade_comparison4".
idtac "Possible points: 0.5".
check_type @LateDays.test_grade_comparison4 (
(LateDays.grade_comparison (LateDays.Grade LateDays.B LateDays.Minus)
   (LateDays.Grade LateDays.C LateDays.Plus) = LateDays.Gt)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.test_grade_comparison4.
Goal True.
idtac " ".

idtac "-------------------  lower_letter_lowers  --------------------".
idtac " ".

idtac "#> LateDays.lower_letter_lowers".
idtac "Possible points: 2".
check_type @LateDays.lower_letter_lowers (
(forall l : LateDays.letter,
 LateDays.letter_comparison LateDays.F l = LateDays.Lt ->
 LateDays.letter_comparison (LateDays.lower_letter l) l = LateDays.Lt)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.lower_letter_lowers.
Goal True.
idtac " ".

idtac "-------------------  lower_grade  --------------------".
idtac " ".

idtac "#> LateDays.lower_grade_A_Plus".
idtac "Possible points: 0.25".
check_type @LateDays.lower_grade_A_Plus (
(LateDays.lower_grade (LateDays.Grade LateDays.A LateDays.Plus) =
 LateDays.Grade LateDays.A LateDays.Natural)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.lower_grade_A_Plus.
Goal True.
idtac " ".

idtac "#> LateDays.lower_grade_A_Natural".
idtac "Possible points: 0.25".
check_type @LateDays.lower_grade_A_Natural (
(LateDays.lower_grade (LateDays.Grade LateDays.A LateDays.Natural) =
 LateDays.Grade LateDays.A LateDays.Minus)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.lower_grade_A_Natural.
Goal True.
idtac " ".

idtac "#> LateDays.lower_grade_A_Minus".
idtac "Possible points: 0.25".
check_type @LateDays.lower_grade_A_Minus (
(LateDays.lower_grade (LateDays.Grade LateDays.A LateDays.Minus) =
 LateDays.Grade LateDays.B LateDays.Plus)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.lower_grade_A_Minus.
Goal True.
idtac " ".

idtac "#> LateDays.lower_grade_B_Plus".
idtac "Possible points: 0.25".
check_type @LateDays.lower_grade_B_Plus (
(LateDays.lower_grade (LateDays.Grade LateDays.B LateDays.Plus) =
 LateDays.Grade LateDays.B LateDays.Natural)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.lower_grade_B_Plus.
Goal True.
idtac " ".

idtac "#> LateDays.lower_grade_F_Natural".
idtac "Possible points: 0.25".
check_type @LateDays.lower_grade_F_Natural (
(LateDays.lower_grade (LateDays.Grade LateDays.F LateDays.Natural) =
 LateDays.Grade LateDays.F LateDays.Minus)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.lower_grade_F_Natural.
Goal True.
idtac " ".

idtac "#> LateDays.lower_grade_twice".
idtac "Possible points: 0.25".
check_type @LateDays.lower_grade_twice (
(LateDays.lower_grade
   (LateDays.lower_grade (LateDays.Grade LateDays.B LateDays.Minus)) =
 LateDays.Grade LateDays.C LateDays.Natural)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.lower_grade_twice.
Goal True.
idtac " ".

idtac "#> LateDays.lower_grade_thrice".
idtac "Possible points: 0.25".
check_type @LateDays.lower_grade_thrice (
(LateDays.lower_grade
   (LateDays.lower_grade
      (LateDays.lower_grade (LateDays.Grade LateDays.B LateDays.Minus))) =
 LateDays.Grade LateDays.C LateDays.Minus)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.lower_grade_thrice.
Goal True.
idtac " ".

idtac "#> LateDays.lower_grade_F_Minus".
idtac "Possible points: 0.25".
check_type @LateDays.lower_grade_F_Minus (
(LateDays.lower_grade (LateDays.Grade LateDays.F LateDays.Minus) =
 LateDays.Grade LateDays.F LateDays.Minus)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.lower_grade_F_Minus.
Goal True.
idtac " ".

idtac "-------------------  lower_grade_lowers  --------------------".
idtac " ".

idtac "#> LateDays.lower_grade_lowers".
idtac "Possible points: 3".
check_type @LateDays.lower_grade_lowers (
(forall g : LateDays.grade,
 LateDays.grade_comparison (LateDays.Grade LateDays.F LateDays.Minus) g =
 LateDays.Lt ->
 LateDays.grade_comparison (LateDays.lower_grade g) g = LateDays.Lt)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.lower_grade_lowers.
Goal True.
idtac " ".

idtac "-------------------  no_penalty_for_mostly_on_time  --------------------".
idtac " ".

idtac "#> LateDays.no_penalty_for_mostly_on_time".
idtac "Possible points: 2".
check_type @LateDays.no_penalty_for_mostly_on_time (
(forall (late_days : nat) (g : LateDays.grade),
 (late_days <? 9) = true -> LateDays.apply_late_policy late_days g = g)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.no_penalty_for_mostly_on_time.
Goal True.
idtac " ".

idtac "-------------------  graded_lowered_once  --------------------".
idtac " ".

idtac "#> LateDays.grade_lowered_once".
idtac "Possible points: 2".
check_type @LateDays.grade_lowered_once (
(forall (late_days : nat) (g : LateDays.grade),
 (late_days <? 9) = false ->
 (late_days <? 17) = true ->
 LateDays.apply_late_policy late_days g = LateDays.lower_grade g)).
idtac "Assumptions:".
Abort.
Print Assumptions LateDays.grade_lowered_once.
Goal True.
idtac " ".

idtac "-------------------  binary  --------------------".
idtac " ".

idtac "#> test_bin_incr1".
idtac "Possible points: 0.5".
check_type @test_bin_incr1 ((incr (B1 Z) = B0 (B1 Z))).
idtac "Assumptions:".
Abort.
Print Assumptions test_bin_incr1.
Goal True.
idtac " ".

idtac "#> test_bin_incr2".
idtac "Possible points: 0.5".
check_type @test_bin_incr2 ((incr (B0 (B1 Z)) = B1 (B1 Z))).
idtac "Assumptions:".
Abort.
Print Assumptions test_bin_incr2.
Goal True.
idtac " ".

idtac "#> test_bin_incr3".
idtac "Possible points: 0.5".
check_type @test_bin_incr3 ((incr (B1 (B1 Z)) = B0 (B0 (B1 Z)))).
idtac "Assumptions:".
Abort.
Print Assumptions test_bin_incr3.
Goal True.
idtac " ".

idtac "#> test_bin_incr4".
idtac "Possible points: 0.5".
check_type @test_bin_incr4 ((bin_to_nat (B0 (B1 Z)) = 2)).
idtac "Assumptions:".
Abort.
Print Assumptions test_bin_incr4.
Goal True.
idtac " ".

idtac "#> test_bin_incr5".
idtac "Possible points: 0.5".
check_type @test_bin_incr5 ((bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z))).
idtac "Assumptions:".
Abort.
Print Assumptions test_bin_incr5.
Goal True.
idtac " ".

idtac "#> test_bin_incr6".
idtac "Possible points: 0.5".
check_type @test_bin_incr6 ((bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z))).
idtac "Assumptions:".
Abort.
Print Assumptions test_bin_incr6.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 28".
idtac "Max points - advanced: 28".
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
idtac "---------- test_nandb4 ---------".
Print Assumptions test_nandb4.
idtac "---------- test_andb34 ---------".
Print Assumptions test_andb34.
idtac "---------- test_factorial2 ---------".
Print Assumptions test_factorial2.
idtac "---------- test_ltb3 ---------".
Print Assumptions test_ltb3.
idtac "---------- plus_id_exercise ---------".
Print Assumptions plus_id_exercise.
idtac "---------- mult_n_1 ---------".
Print Assumptions mult_n_1.
idtac "---------- andb_true_elim2 ---------".
Print Assumptions andb_true_elim2.
idtac "---------- zero_nbeq_plus_1 ---------".
Print Assumptions zero_nbeq_plus_1.
idtac "---------- identity_fn_applied_twice ---------".
Print Assumptions identity_fn_applied_twice.
idtac "---------- negation_fn_applied_twice ---------".
idtac "MANUAL".
idtac "---------- LateDays.letter_comparison_Eq ---------".
Print Assumptions LateDays.letter_comparison_Eq.
idtac "---------- LateDays.test_grade_comparison1 ---------".
Print Assumptions LateDays.test_grade_comparison1.
idtac "---------- LateDays.test_grade_comparison2 ---------".
Print Assumptions LateDays.test_grade_comparison2.
idtac "---------- LateDays.test_grade_comparison3 ---------".
Print Assumptions LateDays.test_grade_comparison3.
idtac "---------- LateDays.test_grade_comparison4 ---------".
Print Assumptions LateDays.test_grade_comparison4.
idtac "---------- LateDays.lower_letter_lowers ---------".
Print Assumptions LateDays.lower_letter_lowers.
idtac "---------- LateDays.lower_grade_A_Plus ---------".
Print Assumptions LateDays.lower_grade_A_Plus.
idtac "---------- LateDays.lower_grade_A_Natural ---------".
Print Assumptions LateDays.lower_grade_A_Natural.
idtac "---------- LateDays.lower_grade_A_Minus ---------".
Print Assumptions LateDays.lower_grade_A_Minus.
idtac "---------- LateDays.lower_grade_B_Plus ---------".
Print Assumptions LateDays.lower_grade_B_Plus.
idtac "---------- LateDays.lower_grade_F_Natural ---------".
Print Assumptions LateDays.lower_grade_F_Natural.
idtac "---------- LateDays.lower_grade_twice ---------".
Print Assumptions LateDays.lower_grade_twice.
idtac "---------- LateDays.lower_grade_thrice ---------".
Print Assumptions LateDays.lower_grade_thrice.
idtac "---------- LateDays.lower_grade_F_Minus ---------".
Print Assumptions LateDays.lower_grade_F_Minus.
idtac "---------- LateDays.lower_grade_lowers ---------".
Print Assumptions LateDays.lower_grade_lowers.
idtac "---------- LateDays.no_penalty_for_mostly_on_time ---------".
Print Assumptions LateDays.no_penalty_for_mostly_on_time.
idtac "---------- LateDays.grade_lowered_once ---------".
Print Assumptions LateDays.grade_lowered_once.
idtac "---------- test_bin_incr1 ---------".
Print Assumptions test_bin_incr1.
idtac "---------- test_bin_incr2 ---------".
Print Assumptions test_bin_incr2.
idtac "---------- test_bin_incr3 ---------".
Print Assumptions test_bin_incr3.
idtac "---------- test_bin_incr4 ---------".
Print Assumptions test_bin_incr4.
idtac "---------- test_bin_incr5 ---------".
Print Assumptions test_bin_incr5.
idtac "---------- test_bin_incr6 ---------".
Print Assumptions test_bin_incr6.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2025-01-13 16:00 *)

(* 2025-01-13 16:00 *)
