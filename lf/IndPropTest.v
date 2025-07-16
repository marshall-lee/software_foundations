Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import IndProp.

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

From LF Require Import IndProp.
Import Check.

Goal True.

idtac "-------------------  ev_double  --------------------".
idtac " ".

idtac "#> ev_double".
idtac "Possible points: 1".
check_type @ev_double ((forall n : nat, ev (double n))).
idtac "Assumptions:".
Abort.
Print Assumptions ev_double.
Goal True.
idtac " ".

idtac "-------------------  Perm3  --------------------".
idtac " ".

idtac "#> Perm3_ex1".
idtac "Possible points: 0.5".
check_type @Perm3_ex1 ((@Perm3 nat [1; 2; 3] [2; 3; 1])).
idtac "Assumptions:".
Abort.
Print Assumptions Perm3_ex1.
Goal True.
idtac " ".

idtac "#> Perm3_refl".
idtac "Possible points: 0.5".
check_type @Perm3_refl ((forall (X : Type) (a b c : X), @Perm3 X [a; b; c] [a; b; c])).
idtac "Assumptions:".
Abort.
Print Assumptions Perm3_refl.
Goal True.
idtac " ".

idtac "-------------------  le_inversion  --------------------".
idtac " ".

idtac "#> le_inversion".
idtac "Possible points: 1".
check_type @le_inversion (
(forall n m : nat, n <= m -> n = m \/ (exists m' : nat, m = S m' /\ n <= m'))).
idtac "Assumptions:".
Abort.
Print Assumptions le_inversion.
Goal True.
idtac " ".

idtac "-------------------  inversion_practice  --------------------".
idtac " ".

idtac "#> SSSSev__even".
idtac "Possible points: 1".
check_type @SSSSev__even ((forall n : nat, ev (S (S (S (S n)))) -> ev n)).
idtac "Assumptions:".
Abort.
Print Assumptions SSSSev__even.
Goal True.
idtac " ".

idtac "-------------------  ev5_nonsense  --------------------".
idtac " ".

idtac "#> ev5_nonsense".
idtac "Possible points: 1".
check_type @ev5_nonsense ((ev 5 -> 2 + 2 = 9)).
idtac "Assumptions:".
Abort.
Print Assumptions ev5_nonsense.
Goal True.
idtac " ".

idtac "-------------------  ev_sum  --------------------".
idtac " ".

idtac "#> ev_sum".
idtac "Possible points: 2".
check_type @ev_sum ((forall n m : nat, ev n -> ev m -> ev (n + m))).
idtac "Assumptions:".
Abort.
Print Assumptions ev_sum.
Goal True.
idtac " ".

idtac "-------------------  ev_ev__ev  --------------------".
idtac " ".

idtac "#> ev_ev__ev".
idtac "Advanced".
idtac "Possible points: 3".
check_type @ev_ev__ev ((forall n m : nat, ev (n + m) -> ev n -> ev m)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_ev__ev.
Goal True.
idtac " ".

idtac "-------------------  Perm3_In  --------------------".
idtac " ".

idtac "#> Perm3_In".
idtac "Possible points: 2".
check_type @Perm3_In (
(forall (X : Type) (x : X) (l1 l2 : list X),
 @Perm3 X l1 l2 -> @In X x l1 -> @In X x l2)).
idtac "Assumptions:".
Abort.
Print Assumptions Perm3_In.
Goal True.
idtac " ".

idtac "-------------------  le_facts  --------------------".
idtac " ".

idtac "#> le_trans".
idtac "Possible points: 0.5".
check_type @le_trans ((forall m n o : nat, m <= n -> n <= o -> m <= o)).
idtac "Assumptions:".
Abort.
Print Assumptions le_trans.
Goal True.
idtac " ".

idtac "#> O_le_n".
idtac "Possible points: 0.5".
check_type @O_le_n ((forall n : nat, 0 <= n)).
idtac "Assumptions:".
Abort.
Print Assumptions O_le_n.
Goal True.
idtac " ".

idtac "#> n_le_m__Sn_le_Sm".
idtac "Possible points: 0.5".
check_type @n_le_m__Sn_le_Sm ((forall n m : nat, n <= m -> S n <= S m)).
idtac "Assumptions:".
Abort.
Print Assumptions n_le_m__Sn_le_Sm.
Goal True.
idtac " ".

idtac "#> Sn_le_Sm__n_le_m".
idtac "Possible points: 1".
check_type @Sn_le_Sm__n_le_m ((forall n m : nat, S n <= S m -> n <= m)).
idtac "Assumptions:".
Abort.
Print Assumptions Sn_le_Sm__n_le_m.
Goal True.
idtac " ".

idtac "#> le_plus_l".
idtac "Possible points: 0.5".
check_type @le_plus_l ((forall a b : nat, a <= a + b)).
idtac "Assumptions:".
Abort.
Print Assumptions le_plus_l.
Goal True.
idtac " ".

idtac "-------------------  plus_le_facts1  --------------------".
idtac " ".

idtac "#> plus_le".
idtac "Possible points: 1".
check_type @plus_le ((forall n1 n2 m : nat, n1 + n2 <= m -> n1 <= m /\ n2 <= m)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_le.
Goal True.
idtac " ".

idtac "#> plus_le_cases".
idtac "Possible points: 1".
check_type @plus_le_cases ((forall n m p q : nat, n + m <= p + q -> n <= p \/ m <= q)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_le_cases.
Goal True.
idtac " ".

idtac "-------------------  plus_le_facts2  --------------------".
idtac " ".

idtac "#> plus_le_compat_l".
idtac "Possible points: 0.5".
check_type @plus_le_compat_l ((forall n m p : nat, n <= m -> p + n <= p + m)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_le_compat_l.
Goal True.
idtac " ".

idtac "#> plus_le_compat_r".
idtac "Possible points: 0.5".
check_type @plus_le_compat_r ((forall n m p : nat, n <= m -> n + p <= m + p)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_le_compat_r.
Goal True.
idtac " ".

idtac "#> le_plus_trans".
idtac "Possible points: 1".
check_type @le_plus_trans ((forall n m p : nat, n <= m -> n <= m + p)).
idtac "Assumptions:".
Abort.
Print Assumptions le_plus_trans.
Goal True.
idtac " ".

idtac "-------------------  R_provability  --------------------".
idtac " ".

idtac "#> Manually graded: R.R_provability".
idtac "Possible points: 3".
print_manual_grade R.manual_grade_for_R_provability.
idtac " ".

idtac "-------------------  subsequence  --------------------".
idtac " ".

idtac "#> subseq_refl".
idtac "Advanced".
idtac "Possible points: 1".
check_type @subseq_refl ((forall l : list nat, subseq l l)).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_refl.
Goal True.
idtac " ".

idtac "#> subseq_app".
idtac "Advanced".
idtac "Possible points: 2".
check_type @subseq_app (
(forall l1 l2 l3 : list nat, subseq l1 l2 -> subseq l1 (l2 ++ l3))).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_app.
Goal True.
idtac " ".

idtac "#> subseq_trans".
idtac "Advanced".
idtac "Possible points: 3".
check_type @subseq_trans (
(forall l1 l2 l3 : list nat, subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3)).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_trans.
Goal True.
idtac " ".

idtac "-------------------  exp_match_ex1  --------------------".
idtac " ".

idtac "#> EmptySet_is_empty".
idtac "Possible points: 0.5".
check_type @EmptySet_is_empty ((forall (T : Type) (s : list T), ~ (s =~ @EmptySet T))).
idtac "Assumptions:".
Abort.
Print Assumptions EmptySet_is_empty.
Goal True.
idtac " ".

idtac "#> MUnion'".
idtac "Possible points: 0.5".
check_type @MUnion' (
(forall (T : Type) (s : list T) (re1 re2 : reg_exp T),
 s =~ re1 \/ s =~ re2 -> s =~ @Union T re1 re2)).
idtac "Assumptions:".
Abort.
Print Assumptions MUnion'.
Goal True.
idtac " ".

idtac "#> MStar'".
idtac "Possible points: 2".
check_type @MStar' (
(forall (T : Type) (ss : list (list T)) (re : reg_exp T),
 (forall s : list T, @In (list T) s ss -> s =~ re) ->
 @fold (list T) (list T) (@app T) ss [ ] =~ @Star T re)).
idtac "Assumptions:".
Abort.
Print Assumptions MStar'.
Goal True.
idtac " ".

idtac "-------------------  re_not_empty  --------------------".
idtac " ".

idtac "#> re_not_empty".
idtac "Possible points: 3".
check_type @re_not_empty ((forall T : Type, reg_exp T -> bool)).
idtac "Assumptions:".
Abort.
Print Assumptions re_not_empty.
Goal True.
idtac " ".

idtac "#> re_not_empty_correct".
idtac "Possible points: 3".
check_type @re_not_empty_correct (
(forall (T : Type) (re : reg_exp T),
 (exists s : list T, s =~ re) <-> @re_not_empty T re = true)).
idtac "Assumptions:".
Abort.
Print Assumptions re_not_empty_correct.
Goal True.
idtac " ".

idtac "-------------------  weak_pumping  --------------------".
idtac " ".

idtac "#> Pumping.weak_pumping".
idtac "Advanced".
idtac "Possible points: 10".
check_type @Pumping.weak_pumping (
(forall (T : Type) (re : reg_exp T) (s : list T),
 s =~ re ->
 @Pumping.pumping_constant T re <= @length T s ->
 exists s1 s2 s3 : list T,
   s = s1 ++ s2 ++ s3 /\
   s2 <> [ ] /\ (forall m : nat, s1 ++ @Pumping.napp T m s2 ++ s3 =~ re))).
idtac "Assumptions:".
Abort.
Print Assumptions Pumping.weak_pumping.
Goal True.
idtac " ".

idtac "-------------------  reflect_iff  --------------------".
idtac " ".

idtac "#> reflect_iff".
idtac "Possible points: 2".
check_type @reflect_iff ((forall (P : Prop) (b : bool), reflect P b -> P <-> b = true)).
idtac "Assumptions:".
Abort.
Print Assumptions reflect_iff.
Goal True.
idtac " ".

idtac "-------------------  eqbP_practice  --------------------".
idtac " ".

idtac "#> eqbP_practice".
idtac "Possible points: 3".
check_type @eqbP_practice (
(forall (n : nat) (l : list nat), count n l = 0 -> ~ @In nat n l)).
idtac "Assumptions:".
Abort.
Print Assumptions eqbP_practice.
Goal True.
idtac " ".

idtac "-------------------  nostutter_defn  --------------------".
idtac " ".

idtac "#> Manually graded: nostutter".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_nostutter.
idtac " ".

idtac "-------------------  filter_challenge  --------------------".
idtac " ".

idtac "#> merge_filter".
idtac "Advanced".
idtac "Possible points: 6".
check_type @merge_filter (
(forall (X : Set) (test : X -> bool) (l l1 l2 : list X),
 @merge X l1 l2 l ->
 @All X (fun n : X => test n = true) l1 ->
 @All X (fun n : X => test n = false) l2 -> @filter X test l = l1)).
idtac "Assumptions:".
Abort.
Print Assumptions merge_filter.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 36".
idtac "Max points - advanced: 61".
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
idtac "---------- ev_double ---------".
Print Assumptions ev_double.
idtac "---------- Perm3_ex1 ---------".
Print Assumptions Perm3_ex1.
idtac "---------- Perm3_refl ---------".
Print Assumptions Perm3_refl.
idtac "---------- le_inversion ---------".
Print Assumptions le_inversion.
idtac "---------- SSSSev__even ---------".
Print Assumptions SSSSev__even.
idtac "---------- ev5_nonsense ---------".
Print Assumptions ev5_nonsense.
idtac "---------- ev_sum ---------".
Print Assumptions ev_sum.
idtac "---------- Perm3_In ---------".
Print Assumptions Perm3_In.
idtac "---------- le_trans ---------".
Print Assumptions le_trans.
idtac "---------- O_le_n ---------".
Print Assumptions O_le_n.
idtac "---------- n_le_m__Sn_le_Sm ---------".
Print Assumptions n_le_m__Sn_le_Sm.
idtac "---------- Sn_le_Sm__n_le_m ---------".
Print Assumptions Sn_le_Sm__n_le_m.
idtac "---------- le_plus_l ---------".
Print Assumptions le_plus_l.
idtac "---------- plus_le ---------".
Print Assumptions plus_le.
idtac "---------- plus_le_cases ---------".
Print Assumptions plus_le_cases.
idtac "---------- plus_le_compat_l ---------".
Print Assumptions plus_le_compat_l.
idtac "---------- plus_le_compat_r ---------".
Print Assumptions plus_le_compat_r.
idtac "---------- le_plus_trans ---------".
Print Assumptions le_plus_trans.
idtac "---------- R_provability ---------".
idtac "MANUAL".
idtac "---------- EmptySet_is_empty ---------".
Print Assumptions EmptySet_is_empty.
idtac "---------- MUnion' ---------".
Print Assumptions MUnion'.
idtac "---------- MStar' ---------".
Print Assumptions MStar'.
idtac "---------- re_not_empty ---------".
Print Assumptions re_not_empty.
idtac "---------- re_not_empty_correct ---------".
Print Assumptions re_not_empty_correct.
idtac "---------- reflect_iff ---------".
Print Assumptions reflect_iff.
idtac "---------- eqbP_practice ---------".
Print Assumptions eqbP_practice.
idtac "---------- nostutter ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- ev_ev__ev ---------".
Print Assumptions ev_ev__ev.
idtac "---------- subseq_refl ---------".
Print Assumptions subseq_refl.
idtac "---------- subseq_app ---------".
Print Assumptions subseq_app.
idtac "---------- subseq_trans ---------".
Print Assumptions subseq_trans.
idtac "---------- Pumping.weak_pumping ---------".
Print Assumptions Pumping.weak_pumping.
idtac "---------- merge_filter ---------".
Print Assumptions merge_filter.
Abort.

(* 2025-01-13 16:19 *)

(* 2025-01-13 16:19 *)
