(** * IndProp: Inductively Defined Propositions *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.

    In this chapter, we bring yet another new tool into the mix:
    _inductively defined propositions_.

    To begin, some examples... *)

(* ================================================================= *)
(** ** Example: The Collatz Conjecture *)

(** The _Collatz Conjecture_ is a famous open problem in number
    theory.

    Its statement is quite simple.  First, we define a function [csf]
    on numbers, as follows (where [csf] stands for "Collatz step function"): *)

Fixpoint div2 (n : nat) : nat :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition csf (n : nat) : nat :=
  if even n then div2 n
  else (3 * n) + 1.

(** Next, we look at what happens when we repeatedly apply [csf] to
    some given starting number.  For example, [csf 12] is [6], and
    [csf 6] is [3], so by repeatedly applying [csf] we get the
    sequence [12, 6, 3, 10, 5, 16, 8, 4, 2, 1].

    Similarly, if we start with [19], we get the longer sequence [19,
    58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8,
    4, 2, 1].

    Both of these sequences eventually reach [1].  The question posed
    by Collatz was: Is the sequence starting from _any_ positive
    natural number guaranteed to reach [1] eventually? *)

(** To formalize this question in Coq, we might try to define a
    recursive _function_ that calculates the total number of steps
    that it takes for such a sequence to reach [1]. *)

Fail Fixpoint reaches1_in (n : nat) : nat :=
  if n =? 1 then 0
  else 1 + reaches1_in (csf n).

(** You can write this definition in a standard programming language.
    This definition is, however, rejected by Coq's termination
    checker, since the argument to the recursive call, [csf n], is not
    "obviously smaller" than [n].

    Indeed, this isn't just a pointless limitation: functions in Coq
    are required to be total, to ensure logical consistency.

    Moreover, we can't fix it by devising a more clever termination
    checker: deciding whether this particular function is total
    would be equivalent to settling the Collatz conjecture! *)

(** Another idea could be to express the concept of "eventually
    reaches [1] in the Collatz sequence" as an _recursively defined
    property_ of numbers [Collatz_holds_for : nat -> Prop]. *)

Fail Fixpoint Collatz_holds_for (n : nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if even n then Collatz_holds_for (div2 n)
                   else Collatz_holds_for ((3 * n) + 1)
  end.

(** This recursive function is also rejected by the termination
    checker, since while we can in principle convince Coq that
    [div2 n] is smaller than [n], we can't convince it that
    [(3 * n) + 1] is smaller than [n]. Since it's definitely not! *)

(** Fortunately, there is another way to do it: We can express the
    concept "reaches [1] eventually in the Collatz sequence" as an
    _inductively defined property_ of numbers. Intuitively, this
    property is defined by a set of rules:

                  ------------------- (Chf_one)
                  Collatz_holds_for 1

     even n = true      Collatz_holds_for (div2 n)
     --------------------------------------------- (Chf_even)
                     Collatz_holds_for n

     even n = false    Collatz_holds_for ((3 * n) + 1)
     ------------------------------------------------- (Chf_odd)
                    Collatz_holds_for n

    So there are three ways to prove that a number [n] eventually
    reaches 1 in the Collatz sequence:
        - [n] is 1;
        - [n] is even and [div2 n] reaches 1;
        - [n] is odd and [(3 * n) + 1] reaches 1.
*)
(** We can prove that a number reaches 1 by constructing a (finite)
    derivation using these rules. For instance, here is the derivation
    proving that 12 reaches 1 (where we left out the evenness/oddness
    premises):

                    ———————————————————— (Chf_one)
                    Collatz_holds_for 1
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 2
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 4
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 8
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 16
                    ———————————————————— (Chf_odd)
                    Collatz_holds_for 5
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 10
                    ———————————————————— (Chf_odd)
                    Collatz_holds_for 3
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 6
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 12
*)

(** Formally in Coq, the [Collatz_holds_for] property is
    _inductively defined_: *)

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : nat) : even n = true ->
                         Collatz_holds_for (div2 n) ->
                         Collatz_holds_for n
  | Chf_odd (n : nat) :  even n = false ->
                         Collatz_holds_for ((3 * n) + 1) ->
                         Collatz_holds_for n.

(** What we've done here is to use Coq's [Inductive] definition
    mechanism to characterize the property "Collatz holds for..." by
    stating three different ways in which it can hold: (1) Collatz
    holds for [1], (2) if Collatz holds for [div2 n] and [n] is even
    then Collatz holds for [n], and (3) if Collatz holds for [(3 * n)
    + 1] and [n] is even then Collatz holds for [n]. This Coq definition
    directly corresponds to the three rules we wrote informally above. *)

(** For particular numbers, we can now prove that the Collatz sequence
    reaches [1] (we'll go through the details of how it works a bit
    later in the chapter): *)

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_one.
Qed.

(** The Collatz conjecture then states that the sequence beginning
    from _any_ positive number reaches [1]: *)

Conjecture collatz : forall n, n <> 0 -> Collatz_holds_for n.

(** If you succeed in proving this conjecture, you've got a bright
    future as a number theorist!  But don't spend too long on it --
    it's been open since 1937. *)

(* ================================================================= *)
(** ** Example: Binary relation for comparing numbers *)

(** A binary _relation_ on a set [X] has Coq type [X -> X -> Prop].
    This is a family of propositions parameterized by two elements of
    [X] -- i.e., a proposition about pairs of elements of [X]. *)

(** For example, one familiar binary relation on [nat] is [le : nat ->
    nat -> Prop], the less-than-or-equal-to relation, which can be
    inductively defined by the following two rules: *)

(**

                           ------ (le_n)
                           le n n

                           le n m
                         ---------- (le_S)
                         le n (S m)
*)
(** These rules say that there are two ways to show that a
    number is less than or equal to another: either observe that they
    are the same number, or, if the second has the form [S m], give
    evidence that the first is less than or equal to [m]. *)

(** This corresponds to the following inductive definition in Coq: *)

Module LePlayground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)   : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

(** This definition is a bit simpler and more elegant than the Boolean function
    [leb] we defined in [Basics]. As usual, [le] and [leb] are
    equivalent, and there is an exercise about that later. *)

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. Qed.

End LePlayground.

(* ================================================================= *)
(** ** Example: Transitive Closure *)

(** As another example, the _transitive closure_ of a relation [R]
    is the smallest relation that contains [R] and that is transitive.
    This can be defined by the following two rules:

                     R x y
                ---------------- (t_step)
                clos_trans R x y

       clos_trans R x y    clos_trans R y z
       ------------------------------------ (t_trans)
                clos_trans R x z

    In Coq this looks as follows:
*)

Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

(** For example, suppose we define a "parent of" relation on a group
    of people... *)

Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
  po_SC : parent_of Sage Cleo
| po_SR : parent_of Sage Ridley
| po_CM : parent_of Cleo Moss.

(** In this example, [Sage] is a parent of both [Cleo] and
    [Ridley]; and [Cleo] is a parent of [Moss]. *)

(** The [parent_of] relation is not transitive, but we can define
   an "ancestor of" relation as its transitive closure: *)

Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

(** Here is a derivation showing that Sage is an ancestor of Moss:

 ———————————————————(po_SC)     ———————————————————(po_CM)
 parent_of Sage Cleo            parent_of Cleo Moss
—————————————————————(t_step)  —————————————————————(t_step)
ancestor_of Sage Cleo          ancestor_of Cleo Moss
————————————————————————————————————————————————————(t_trans)
                ancestor_of Sage Moss
*)

Example ancestor_of_ex : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of. apply t_trans with Cleo.
  - apply t_step. apply po_SC.
  - apply t_step. apply po_CM. Qed.

(** Computing the transitive closure can be undecidable even for
    a relation R that is decidable (e.g., the [cms] relation below), so in
    general we can't expect to define transitive closure as a boolean
    function. Fortunately, Coq allows us to define transitive closure
    as an inductive relation.

    The transitive closure of a binary relation cannot, in general, be
    expressed in first-order logic. The logic of Coq is, however, much
    more powerful, and can easily define such inductive relations. *)

(* ================================================================= *)
(** ** Example: Reflexive and Transitive Closure *)

(** As another example, the _reflexive and transitive closure_
    of a relation [R] is the
    smallest relation that contains [R] and that is reflexive and
    transitive. This can be defined by the following three rules
    (where we added a reflexivity rule to [clos_trans]):

                        R x y
                --------------------- (rt_step)
                clos_refl_trans R x y

                --------------------- (rt_refl)
                clos_refl_trans R x x

     clos_refl_trans R x y    clos_refl_trans R y z
     ---------------------------------------------- (rt_trans)
                clos_refl_trans R x z
*)

Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_step (x y : X) :
      R x y ->
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.

(** For instance, this enables an equivalent definition of the Collatz
    conjecture.  First we define the binary relation corresponding to
    the Collatz step function [csf]: *)

Definition cs (n m : nat) : Prop := csf n = m.

(** This Collatz step relation can be used in conjunction with the
    reflexive and transitive closure operation to define a Collatz
    multi-step ([cms]) relation, expressing that a number [n]
    reaches another number [m] in zero or more Collatz steps: *)

Definition cms n m := clos_refl_trans cs n m.
Conjecture collatz' : forall n, n <> 0 -> cms n 1.

(** This [cms] relation defined in terms of
    [clos_refl_trans] allows for more interesting derivations than the
    linear ones of the directly-defined [Collatz_holds_for] relation:

csf 16 = 8         csf 8 = 4         csf 4 = 2         csf 2 = 1
————————(rt_step)  ———————(rt_step)  ———————(rt_step)  ———————(rt_step)
cms 16 8           cms 8 4           cms 4 2           cms 2 1
—————————————————————————(rt_trans)  ————————————————————————(rt_trans)
        cms 16 4                              cms 4 1
        —————————————————————————————————————————————(rt_trans)
                           cms 16 1
*)

(** **** Exercise: 1 star, standard, optional (clos_refl_trans_sym)

    How would you modify the [clos_refl_trans] definition above so as
    to define the reflexive, symmetric, and transitive closure? *)

Inductive clos_refl_trans_sym {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rts_step (x y : X) :
      R x y ->
      clos_refl_trans_sym R x y
  | rts_refl (x : X) :
      clos_refl_trans_sym R x x
  | rts_trans (x y z : X) :
      clos_refl_trans_sym R x y ->
      clos_refl_trans_sym R y z ->
      clos_refl_trans_sym R x z
  | rts_sym (x y : X) :
      clos_refl_trans_sym R x y ->
      clos_refl_trans_sym R y x.

(* ================================================================= *)
(** ** Example: Permutations *)

(** The familiar mathematical concept of _permutation_ also has an
    elegant formulation as an inductive relation.  For simplicity,
    let's focus on permutations of lists with exactly three
    elements. We can define them by the following rules:

               --------------------- (perm3_swap12)
               Perm3 [a;b;c] [b;a;c]

               --------------------- (perm3_swap23)
               Perm3 [a;b;c] [a;c;b]

            Perm3 l1 l2       Perm3 l2 l3
            ----------------------------- (perm3_trans)
                     Perm3 l1 l3

    For instance we can derive [Perm3 [1;2;3] [3;2;1]] as follows:

————————(perm_swap12)  —————————————————————(perm_swap23)
Perm3 [1;2;3] [2;1;3]  Perm3 [2;1;3] [2;3;1]
——————————————————————————————(perm_trans)  ————————————(perm_swap12)
    Perm3 [1;2;3] [2;3;1]                   Perm [2;3;1] [3;2;1]
    —————————————————————————————————————————————————————(perm_trans)
                      Perm3 [1;2;3] [3;2;1]
*)

(** This definition says:
      - If [l2] can be obtained from [l1] by swapping the first and
        second elements, then [l2] is a permutation of [l1].
      - If [l2] can be obtained from [l1] by swapping the second and
        third elements, then [l2] is a permutation of [l1].
      - If [l2] is a permutation of [l1] and [l3] is a permutation of
        [l2], then [l3] is a permutation of [l1]. *)

(** In Coq [Perm3] is given the following inductive definition: *)

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(** **** Exercise: 1 star, standard, optional (perm)

    According to this definition, is [[1;2;3]] a permutation of
    itself? *)

(* FILL IN HERE

    [] *)

(* ================================================================= *)
(** ** Example: Evenness (yet again) *)

(** We've already seen two ways of stating a proposition that a number
    [n] is even: We can say

      (1) [even n = true] (using the recursive boolean function [even]), or

      (2) [exists k, n = double k] (using an existential quantifier). *)

(** A third possibility, which we'll use as a simple running example
    here, is to say that a number is even if we can
    _establish_ its evenness from the following two rules:

                          ---- (ev_0)
                          ev 0

                          ev n
                      ------------ (ev_SS)
                      ev (S (S n))
*)

(** Intuitively these rules say that:
       - The number [0] is even.
       - If [n] is even, then [S (S n)] is even. *)

(** (Defining evenness in this way may seem a bit confusing,
    since we have already seen two perfectly good ways of doing
    it. It makes a convenient running example because it is
    simple and compact, but we will soon return to the more compelling
    examples above.) *)

(** To illustrate how this new definition of evenness works, let's
    imagine using it to show that [4] is even:

                           ———— (ev_0)
                           ev 0
                       ———————————— (ev_SS)
                       ev (S (S 0))
                   ———————————————————— (ev_SS)
                   ev (S (S (S (S 0))))
*)

(** In words, to show that [4] is even, by rule [ev_SS], it
   suffices to show that [2] is even. This, in turn, is again
   guaranteed by rule [ev_SS], as long as we can show that [0] is
   even. But this last fact follows directly from the [ev_0] rule. *)

(** We can translate the informal definition of evenness from above
    into a formal [Inductive] declaration, where each "way that a
    number can be even" corresponds to a separate constructor: *)

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** Such definitions are interestingly different from previous uses of
    [Inductive] for defining inductive datatypes like [nat] or [list].
    For one thing, we are defining not a [Type] (like
    [nat]) or a function yielding a [Type] (like [list]), but rather a
    function from [nat] to [Prop] -- that is, a property of numbers.
    But what is really new is that, because the [nat] argument of [ev]
    appears to the _right_ of the colon on the first line, it is
    allowed to take _different_ values in the types of different
    constructors: [0] in the type of [ev_0] and [S (S n)] in the type
    of [ev_SS].  Accordingly, the type of each constructor must be
    specified explicitly (after a colon), and each constructor's type
    must have the form [ev n] for some natural number [n].

    In contrast, recall the definition of [list]:

    Inductive list (X:Type) : Type :=
      | nil
      | cons (x : X) (l : list X).

    or equivalently:

    Inductive list (X:Type) : Type :=
      | nil                       : list X
      | cons (x : X) (l : list X) : list X.

   This definition introduces the [X] parameter _globally_, to the
   _left_ of the colon, forcing the result of [nil] and [cons] to be
   the same type (i.e., [list X]).  But if we had tried to bring [nat]
   to the left of the colon in defining [ev], we would have seen an
   error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]" as 1st
        argument in "[wrong_ev 0]". *)

(** In an [Inductive] definition, an argument to the type constructor
    on the left of the colon is called a "parameter", whereas an
    argument on the right is called an "index" or "annotation."

    For example, in [Inductive list (X : Type) := ...], the [X] is a
    parameter, while in [Inductive ev : nat -> Prop := ...], the
    unnamed [nat] argument is an index. *)

(** Beyond this syntactic distinction, we can think of the inductive
    definition of [ev] as defining a Coq property [ev : nat -> Prop],
    together with two "evidence constructors": *)

Check ev_0 : ev 0.
Check ev_SS : forall (n : nat), ev n -> ev (S (S n)).

(** In fact, Coq also accepts the following equivalent definition of [ev]: *)

Module EvPlayground.

Inductive ev : nat -> Prop :=
  | ev_0  : ev 0
  | ev_SS : forall (n : nat), ev n -> ev (S (S n)).

End EvPlayground.

(** These evidence constructors can be thought of as "primitive
    evidence of evenness", and they can be used just like proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    constructor names to obtain evidence for [ev] of particular
    numbers... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax to combine several
    constructors: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** In this way, we can also prove theorems that have hypotheses
    involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star, standard (ev_double) *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  induction n.
  - apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Constructing Evidence for Permutations *)

(** Similarly we can apply the evidence constructors to obtain
    evidence of [Perm3 [1;2;3] [3;2;1]]: *)

Lemma Perm3_rev : Perm3 [1;2;3] [3;2;1].
Proof.
  apply perm3_trans with (l2:=[2;3;1]).
  - apply perm3_trans with (l2:=[2;1;3]).
    + apply perm3_swap12.
    + apply perm3_swap23.
  - apply perm3_swap12.
Qed.

(** And again we can equivalently use function application syntax to
    combine several constructors. Note that the Coq type checker can
    infer not only types, but also nats and lists. *)

Lemma Perm3_rev' : Perm3 [1;2;3] [3;2;1].
Proof.
  apply (perm3_trans _ [2;3;1] _
          (perm3_trans _ [2;1;3] _
            (perm3_swap12 _ _ _)
            (perm3_swap23 _ _ _))
          (perm3_swap12 _ _ _)).
Qed.

(** So the informal derivation trees we drew above are not too far
    from what's happening formally.  Formally we're using the evidence
    constructors to build _evidence trees_, similar to the finite trees we
    built using the constructors of data types such as nat, list,
    binary trees, etc. *)

(** **** Exercise: 1 star, standard (Perm3) *)
Lemma Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with (l2:=[2;1;3]).
  - apply perm3_swap12.
  - apply perm3_swap23.
Qed.

Lemma Perm3_refl : forall (X : Type) (a b c : X),
  Perm3 [a;b;c] [a;b;c].
Proof.
  intros.
  apply perm3_trans with (l2:=[b;a;c]).
  - apply perm3_swap12.
  - apply perm3_swap12.
Qed.
(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _destruct_ such evidence, reasoning about how it could have been
    built.

    Defining [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is [ev], but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are [ev]. *)

(** In other words, if someone gives us evidence [E] for the proposition
    [ev n], then we know that [E] must be one of two things:

      - [E = ev_0] and [n = O], or
      - [E = ev_SS n' E'], where [n = S (S n')] and [E'] is
        evidence for [ev n']. *)

(** This suggests that it should be possible to analyze a
    hypothesis of the form [ev n] much as we do inductively defined
    data structures; in particular, it should be possible to argue by
    _case analysis_ or by _induction_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Destructing and Inverting Evidence *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [ev n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence for [ev n] _directly_.

    As a tool for such proofs, we can formalize the intuitive
    characterization that we gave above for evidence of [ev n], using
    [destruct]. *)

Theorem ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** Facts like this are often called "inversion lemmas" because they
    allow us to "invert" some given information to reason about all
    the different ways it could have been derived.

    Here, there are two ways to prove [ev n], and the inversion
    lemma makes this explicit. *)

(** **** Exercise: 1 star, standard (le_inversion)

    Let's prove a similar inversion lemma for [le]. *)
Theorem le_inversion : forall (n m : nat),
  le n m ->
  (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
  intros n m E.
  destruct E as [| m' E'] eqn:EE.
  - left. reflexivity.
  - right. exists m'. split. reflexivity. apply E'.
Qed.
(** [] *)

(** We can use the inversion lemma that we proved above to help
    structure proofs: *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. apply ev_inversion in E. destruct E as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnn' E']]. injection Hnn' as Hnn'.
    rewrite Hnn'. apply E'.
Qed.

(** Note how the inversion lemma produces two subgoals, which
    correspond to the two ways of proving [ev].  The first subgoal is
    a contradiction that is discharged with [discriminate].  The
    second subgoal makes use of [injection] and [rewrite].

    Coq provides a handy tactic called [inversion] that factors out
    this common pattern, saving us the trouble of explicitly stating
    and proving an inversion lemma for every [Inductive] definition we
    make.

    Here, the [inversion] tactic can detect (1) that the first case,
    where [n = 0], does not apply and (2) that the [n'] that appears
    in the [ev_SS] case must be the same as [n].  It includes an
    "[as]" annotation similar to [destruct], allowing us to assign
    names rather than have Coq choose them. *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.  inversion E as [| n' E' Hnn'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. Compare: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof. intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (inversion_practice)

    Prove the following result using [inversion].  (For extra
    practice, you can also prove it using the inversion lemma.) *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. inversion H as [| n0 H0 Heq0]. inversion H0 as [| n1 H1 Heq1].
  apply H1.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (ev5_nonsense)

    Prove the following result using [inversion]. *)

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H as [| n0 H0 Heq0].
  inversion H0 as [| n1 H1 Heq1].
  inversion H1.
Qed.
(** [] *)

(** The [inversion] tactic does quite a bit of work. For
    example, when applied to an equality assumption, it does the work
    of both [discriminate] and [injection]. In addition, it carries
    out the [intros] and [rewrite]s that are typically necessary in
    the case of [injection]. It can also be applied to analyze
    evidence for arbitrary inductively defined propositions, not just
    equality.  As examples, we'll use it to re-prove some theorems
    from chapter [Tactics].  (Here we are being a bit lazy by
    omitting the [as] clause from [inversion], thereby asking Coq to
    choose names for the variables and hypotheses that it introduces.) *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** Here's how [inversion] works in general.
      - Suppose the name [H] refers to an assumption [P] in the
        current context, where [P] has been defined by an [Inductive]
        declaration.
      - Then, for each of the constructors of [P], [inversion H]
        generates a subgoal in which [H] has been replaced by the
        specific conditions under which this constructor could have
        been used to prove [P].
      - Some of these subgoals will be self-contradictory; [inversion]
        throws these away.
      - The ones that are left represent the cases that must be proved
        to establish the original goal.  For those, [inversion] adds
        to the proof context all equations that must hold of the
        arguments given to [P] -- e.g., [n' = n] in the proof of
        [evSS_ev]). *)

(** The [ev_double] exercise above allows us to easily show that
    our new notion of evenness is implied by the two earlier ones
    (since, by [even_bool_prop] in chapter [Logic], we already
    know that those are equivalent to each other). To show that all
    three coincide, we just need the following lemma. *)

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  (* WORKED IN CLASS *) unfold Even.

(** We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy seems
    unpromising, because (as we've noted before) the induction
    hypothesis will talk about [n-1] (which is _not_ even!).  Thus, it
    seems better to first try [inversion] on the evidence for [ev].
    Indeed, the first case can be solved trivially. And we can
    seemingly make progress on the second case with a helper lemma. *)

  intros n E. inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *) exists 0. reflexivity.
  - (* E = ev_SS n' E'

    Unfortunately, the second case is harder.  We need to show [exists
    n0, S (S n') = double n0], but the only available assumption is
    [E'], which states that [ev n'] holds.  Since this isn't directly
    useful, it seems that we are stuck and that performing case
    analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to a similar
    one that involves a _different_ piece of evidence for [ev]: namely
    [E'].  More formally, we could finish our proof if we could show
    that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result would suffice. *)
    assert (H: (exists k', n' = double k')
               -> (exists n0, S (S n') = double n0)).
        { intros [k' EQ'']. exists (S k'). simpl.
          rewrite <- EQ''. reflexivity. }
    apply H.

    (** Unfortunately, now we are stuck. To see this clearly, let's
        move [E'] back into the goal from the hypotheses. *)

    generalize dependent E'.

    (** Now it is obvious that we are trying to prove another instance
        of the same theorem we set out to prove -- only here we are
        talking about [n'] instead of [n]. *)
Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this story feels familiar, it is no coincidence: We
    encountered similar problems in the [Induction] chapter, when
    trying to use case analysis to prove results that required
    induction.  And once again the solution is... induction! *)

(** The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have been used to build that evidence, while
    providing an induction hypothesis for each recursive occurrence of
    the property in question.

    To prove that a property of [n] holds for all even numbers (i.e.,
    those for which [ev n] holds), we can use induction on [ev
    n]. This requires us to prove two things, corresponding to the two
    ways in which [ev n] could have been constructed. If it was
    constructed by [ev_0], then [n=0] and the property must hold of
    [0]. If it was constructed by [ev_SS], then the evidence of [ev n]
    is of the form [ev_SS n' E'], where [n = S (S n')] and [E'] is
    evidence for [ev n']. In this case, the inductive hypothesis says
    that the property we are trying to prove holds for [n']. *)

(** Let's try proving that lemma again: *)

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  unfold Even. intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E',  with IH : Even n' *)
    destruct IH as [k Hk]. rewrite Hk.
    exists (S k). simpl. reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas -- in particular for
    formalizing the semantics of programming languages. *)

(** The following exercises provide simpler examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars, standard (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m En Em.
  induction En.
  - apply Em.
  - simpl. apply ev_SS. apply IHEn.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, especially useful (ev_ev__ev) *)
Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  (* Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. *)
Proof.
  intros n m.
  intros E1 E2.
  induction E2.
  - apply E1.
  - simpl in E1. inversion E1 as [| sum E3 H]. apply (IHE2 E3).
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus)

    This exercise can be completed without induction or case analysis.
    But, you will need a clever assertion and some tedious rewriting.
    Hint: Is [(n+m) + (n+p)] even? *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Enm Enp.
  apply ev_ev__ev with (n + n).
  - assert (ev ((n + m) + (n + p))) as H.
    { apply ev_sum. apply Enm. apply Enp. }
    rewrite add_comm with n m in H.
    rewrite <- add_assoc with m n (n + p) in H.
    rewrite add_assoc with n n p in H.
    rewrite add_comm with (n + n) p in H.
    rewrite add_assoc with m p (n + n) in H.
    rewrite add_comm with (m + p) (n + n) in H.
    apply H.
  - rewrite <- double_plus. apply ev_double.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ev'_ev)

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** Prove that this definition is logically equivalent to the old one.
    To streamline the proof, use the technique (from the [Logic]
    chapter) of applying theorems to arguments, and note that the same
    technique works with constructors of inductively defined
    propositions. *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n.
  split.
  - intros H. induction H.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum. apply IHev'1. apply IHev'2.
  - intros H. induction H.
    + apply ev'_0.
    + rewrite <- plus_1_l with (S n). rewrite <- plus_n_Sm. rewrite <- plus_1_l.
      rewrite add_assoc. apply ev'_sum.
      * apply ev'_2.
      * apply IHev.
Qed.
(** [] *)

(** We can do similar inductive proofs on the [Perm3] relation,
    which we defined earlier as follows: *)

Module Perm3Reminder.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

End Perm3Reminder.

Lemma Perm3_symm : forall (X : Type) (l1 l2 : list X),
  Perm3 l1 l2 -> Perm3 l2 l1.
Proof.
  intros X l1 l2 E.
  induction E as [a b c | a b c | l1 l2 l3 E12 IH12 E23 IH23].
  - apply perm3_swap12.
  - apply perm3_swap23.
  - apply (perm3_trans _ l2 _).
    * apply IH23.
    * apply IH12.
Qed.

(** **** Exercise: 2 stars, standard (Perm3_In) *)
Lemma Perm3_In : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> In x l1 -> In x l2.
Proof.
  intros X x l1 l2 HPerm HIn.
  induction HPerm.
  - simpl.
    destruct HIn as [E|HIn'].
    + right. left. apply E.
    + inversion HIn' as [E|HIn''].
      * left. apply E.
      * inversion HIn'' as [E|contra].
        ** right. right. left. apply E.
        ** destruct contra.
  - simpl.
    destruct HIn as [E|HIn'].
    + left. apply E.
    + inversion HIn' as [E|HIn''].
      * right. right. left. apply E.
      * inversion HIn'' as [E|contra].
        ** right. left. apply E.
        ** destruct contra.
  - simpl.
    apply IHHPerm2. apply IHHPerm1. apply HIn.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (Perm3_NotIn) *)
Lemma Perm3_NotIn : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> ~In x l1 -> ~In x l2.
Proof.
  intros X x l1 l2 HPerm HNotIn contra.
  apply HNotIn.
  apply Perm3_In with (l1:=l2).
  - apply Perm3_symm. apply HPerm.
  - apply contra.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (NotPerm3)

    Proving that something is NOT a permutation is quite tricky. Some
    of the lemmas above, like [Perm3_In] can be useful for this. *)
Example Perm3_example2 : ~ Perm3 [1;2;3] [1;2;4].
Proof.
  intros contra.
  assert (H: In 3 [1;2;4]).
  { apply Perm3_In with (l1:=[1;2;3]). apply contra. simpl. right. right. left. reflexivity. }
  destruct H as [|H1]. discriminate.
  destruct H1 as [|H2]. discriminate.
  destruct H2 as [|H3]. discriminate.
  destruct H3.
Qed.
(** [] *)


(* ################################################################# *)
(** * Exercising with Inductive Relations *)

(** A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** Just like properties, relations can be defined inductively.  One
    useful example is the "less than or equal to" relation on numbers
    that we briefly saw above. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

(** (We've written the definition a bit differently this time,
    giving explicit names to the arguments to the constructors and
    moving them to the left of the colons.) *)

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m : nat) := le (S n) m.

Notation "n < m" := (lt n m).

(** The [>=] operation is defined in terms of [<=]. *)

Definition ge (m n : nat) : Prop := le n m.
Notation "m >= n" := (ge m n).

End Playground.


(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n'].
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

(** **** Exercise: 3 stars, standard, especially useful (le_facts) *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Emn Eno.
  induction Eno as [|o Eno IH].
  - apply Emn.
  - apply (le_S m o IH).
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n.
  - apply le_n.
  - apply (le_S 0 n IHn).
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H as [|m H IH].
  - apply le_n.
  - apply (le_S (S n) (S m) IH).
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H.
  induction m.
  - inversion H as [H0 | zero H1 H2]. apply le_n. inversion H1.
  - inversion H as [H0 | Sm H1 H2]. apply le_n. apply (le_S n m (IHm H1)).
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction b.
  - rewrite add_0_r. apply le_n.
  - rewrite <- plus_n_Sm. apply (le_S a (a + b) IHb).
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (plus_le_facts1) *)

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m H.
  induction H.
  - split.
    + apply le_plus_l.
    + rewrite add_comm. apply le_plus_l.
  - destruct IHle as [H1 H2].
    split.
    + apply (le_S n1 m H1).
    + apply (le_S n2 m H2).
Qed.

Theorem plus_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
  (** Hint: May be easiest to prove by induction on [n]. *)
Proof.
  induction n.
  - left. apply O_le_n.
  - intros. destruct p.
    + right. apply plus_le in H.
      destruct H as [H1 H2].
      rewrite plus_O_n in H1.
      apply H2.
    + simpl in H.
      rewrite plus_n_Sm with n m in H.
      rewrite plus_n_Sm with p q in H.
      apply IHn in H. destruct H.
      * left. apply n_le_m__Sn_le_Sm. apply H.
      * right. apply Sn_le_Sm__n_le_m. apply H.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (plus_le_facts2) *)

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  intros n m p.
  induction p.
  - intros. rewrite plus_O_n. rewrite plus_O_n. apply H.
  - intros. simpl. apply n_le_m__Sn_le_Sm. apply (IHp H).
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros n m p H.
  rewrite add_comm with n p.
  rewrite add_comm with m p.
  apply plus_le_compat_l.
  apply H.
Qed.

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  intros n m p.
  generalize dependent n.
  generalize dependent m.
  induction p.
  - intros. rewrite add_comm. rewrite plus_O_n. apply H.
  - intros. destruct H.
    + apply le_plus_l.
    + simpl.
      apply IHp in H.
      apply le_S in H. rewrite plus_n_Sm in H.
      apply (le_S n (m + S p) H).
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (lt_facts) *)
Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros n m.
  destruct m.
  - right. apply O_le_n.
  - induction n.
    + left. apply n_le_m__Sn_le_Sm. apply O_le_n.
    + destruct IHn.
      * destruct H.
        right. apply le_n.
        left. apply n_le_m__Sn_le_Sm. apply H.
      * right. apply le_S. apply H.
Qed.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  intros n m H.
  apply le_S in H.
  apply Sn_le_Sm__n_le_m in H.
  apply H.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m H.
  inversion H as [H12 | n H12 Hm].
  - split.
    + apply n_le_m__Sn_le_Sm. apply le_plus_l.
    + apply n_le_m__Sn_le_Sm. rewrite add_comm. apply le_plus_l.
  - rewrite <- Hm in H. apply Sn_le_Sm__n_le_m in H.
    apply plus_le in H. destruct H as [H1 H2].
    split.
    + apply n_le_m__Sn_le_Sm. apply H1.
    + apply n_le_m__Sn_le_Sm. apply H2.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (leb_le) *)
Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n m.
  generalize dependent m.
  induction n.
  - intros. apply O_le_n.
  - intros. destruct m.
    + discriminate.
    + simpl in H. apply IHn in H. apply n_le_m__Sn_le_Sm. apply H.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  - intros. inversion H. reflexivity.
  - destruct n.
    + reflexivity.
    + intros. apply Sn_le_Sm__n_le_m in H. apply (IHm n H).
Qed.

(** Hint: The next two can easily be proved without using [induction]. *)

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros n m.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o Hnm Hmo.
  apply leb_complete in Hnm.
  apply leb_complete in Hmo.
  apply leb_correct.
  apply le_trans with m.
  apply Hnm. apply Hmo.
Qed.
(** [] *)

Module R.

(** **** Exercise: 3 stars, standard, especially useful (R_provability)

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
  | c1                                     : R 0     0     0
  | c2 m n o (H : R m     n     o        ) : R (S m) n     (S o)
  | c3 m n o (H : R m     n     o        ) : R m     (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m     n     o
  | c5 m n o (H : R m     n     o        ) : R n     m     o
.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact)

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq. *)

Definition fR : nat -> nat -> nat
  := plus.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  split.
  - intros. induction H.
    + reflexivity.
    + simpl. f_equal. apply IHR.
    + rewrite <- plus_n_Sm. f_equal. apply IHR.
    + simpl in IHR.
      apply S_injective in IHR. rewrite <- plus_n_Sm in IHR.
      apply S_injective in IHR.
      apply IHR.
    + rewrite add_comm in IHR. apply IHR.
  - intros.
    rewrite <- H.
    destruct H.
    induction m.
      + induction n. apply c1. apply c3. apply IHn.
      + simpl. apply c2. apply IHm.
Qed.
(** [] *)

End R.

(** **** Exercise: 4 stars, advanced (subsequence)

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3]. *)

Inductive subseq : list nat -> list nat -> Prop :=
  | subseq0 l : subseq [] l
  | subseq1 x l1 l2 (H : subseq l1 l2) : subseq (x :: l1) (x :: l2)
  | subseq2 x l1 l2 (H : subseq l1 l2) : subseq l1 (x :: l2)
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  induction l as [| x l IH].
  - apply subseq0.
  - apply (subseq1 x l l IH).
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H as [| x l1 l2 H IH | x l1 l2 H IH].
  - apply subseq0.
  - simpl. apply (subseq1 x l1 (l2 ++ l3) IH).
  - simpl. apply (subseq2 x l1 (l2 ++ l3) IH).
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  (* Hint: be careful about what you are doing induction on and which
     other things need to be generalized... *)
  intros l1 l2 l3 H12 H23.
  generalize dependent l1.
  induction H23 as [| x l2 l3 H23 IH | x l2 l3 H23 IH].
  - intros.
    assert (l1 = []) as Hl1. inversion H12. reflexivity.
    rewrite Hl1. apply subseq0.
  - intros. inversion H12 as [| x' l1' l2' H12' | x' l1' l2' H12'].
    + apply subseq0.
    + apply (subseq1 x l1' l3 (IH l1' H12')).
    + apply (subseq2 x l1 l3 (IH l1 H12')).
  - intros. apply (subseq2 x l1 l3 (IH l1 H12)).
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (R_provability2)

    Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1                    : R 0     []
      | c2 n l (H: R n     l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n     l.

    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(* FILL IN HERE

    [] *)

(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** Many of the examples above were simple and -- in the case of
    the [ev] property -- even a bit artificial. To give a better sense
    of the power of inductively defined propositions, we now show how
    to use them to model a classic concept in computer science:
    _regular expressions_. *)

(** Regular expressions are a natural language for describing sets of
    strings.  Their syntax is defined as follows: *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- which in this exercise we represent as _lists_ with
    elements from [T]. *)

(** (Technical aside: We depart slightly from standard practice in
    that we do not require the type [T] to be finite.  This results in
    a somewhat different theory of regular expressions, but the
    difference is not significant for present purposes.) *)

(** We connect regular expressions and strings by defining when a
    regular expression _matches_ some string.
    Informally this looks as follows:

      - The expression [EmptySet] does not match any string.

      - The expression [EmptyStr] matches the empty string [[]].

      - The expression [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2],
        then [App re1 re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s],
        then [Union re1 re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation
        of a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i],
        then [Star re] matches [s].

        In particular, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** We can easily translate this intuition into a set of rules,
    where we write [s =~ re] to say that [s] matches [re]:

                        -------------- (MEmpty)
                        [] =~ EmptyStr

                        --------------- (MChar)
                        [x] =~ (Char x)

                    s1 =~ re1     s2 =~ re2
                  --------------------------- (MApp)
                  (s1 ++ s2) =~ (App re1 re2)

                           s1 =~ re1
                     --------------------- (MUnionL)
                     s1 =~ (Union re1 re2)

                           s2 =~ re2
                     --------------------- (MUnionR)
                     s2 =~ (Union re1 re2)

                        --------------- (MStar0)
                        [] =~ (Star re)

                           s1 =~ re
                        s2 =~ (Star re)
                    ----------------------- (MStarApp)
                    (s1 ++ s2) =~ (Star re)
*)

(** This directly corresponds to the following [Inductive] definition.
    We use the notation [s =~ re] in  place of [exp_match s re].
    (By "reserving" the notation before defining the [Inductive],
    we can use it in the definition.) *)

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR s2 re1 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

(** Notice that these rules are not _quite_ the same as the
    intuition that we gave at the beginning of the section.
    First, we don't need to include a rule explicitly stating that no
    string matches [EmptySet]; we just don't happen to include any
    rule that would have the effect of some string matching
    [EmptySet].  (Indeed, the syntax of inductive definitions doesn't
    even _allow_ us to give such a "negative rule.")

    Second, the intuition we gave for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    intuition but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the intuition is indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the string
    [[1]] directly.  Since the goal mentions [[1; 2]] instead of
    [[1] ++ [2]], Coq wouldn't be able to figure out how to split
    the string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the string that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars, standard (exp_match_ex1)

    The following lemmas show that the intuition about matching given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma EmptySet_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  unfold not. intros. inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros.
  destruct H.
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H1.
  induction ss as [| s1 ss IH].
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H1. left. reflexivity.
    + apply IH. intros s2 H2. apply H1. right. apply H2.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (EmptyStr_not_needed)

    It turns out that the [EmptyStr] constructor is actually not
   needed, since the regular expression matching the empty string can
   also be defined from [Star] and [EmptySet]: *)
Definition EmptyStr' {T:Type} := @Star T (EmptySet).

(** State and prove that this [EmptyStr'] definition matches exactly
   the same strings as the [EmptyStr] constructor. *)

Theorem EmptyStr_not_needed : forall T (s : list T),
  s =~ EmptyStr <-> s =~ EmptyStr'.
Proof.
  intros T s.
  split.
  - intros H.
    destruct s.
    + apply MStar0.
    + inversion H.
  - intros H.
    destruct s.
    + apply MEmpty .
    + inversion H as [H1 | | | | o| | ]. inversion H1.
Qed.

(** Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence. *)

(** For example, suppose we want to prove the following intuitive
    result: If a string [s] matches a regular expression [re], then
    all elements of [s] must occur as character literals somewhere in
    [re].

    To state this as a theorem, we first define a function [re_chars]
    that lists all characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** The main theorem: *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.

(** Something interesting happens in the [MApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re1]), and a second one that applies when [x]
    occurs in [s2] (which matches [re2]). *)

    rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.

(** Here again we get two induction hypotheses, and they illustrate
    why we need induction on evidence for [exp_match], rather than
    induction on the regular expression [re]: The latter would only
    provide an induction hypothesis for strings that match [re], which
    would not allow us to reason about the case [In x s2]. *)

    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** Exercise: 4 stars, standard (re_not_empty)

    Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool
  := match re with
     | EmptySet => false
     | EmptyStr => true
     | Char _ => true
     | App re1 re2 => (re_not_empty re1) && (re_not_empty re2)
     | Union re1 re2 => (re_not_empty re1) || (re_not_empty re2)
     | Star _ => true
     end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split.
  - intros H. destruct H as [s Hmatch].
    induction Hmatch.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IHHmatch1. rewrite IHHmatch2. reflexivity.
    + simpl. rewrite IHHmatch. reflexivity.
    + simpl. apply orb_true_iff. right. apply IHHmatch.
    + reflexivity.
    + reflexivity.
  - intros H.
    induction re.
    + inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
      apply IHre1 in H1. destruct H1 as [s1 H1].
      apply IHre2 in H2. destruct H2 as [s2 H2].
      exists (s1 ++ s2). apply MApp. apply H1. apply H2.
    + simpl in H. apply orb_true_iff in H. destruct H as [H1 | H2].
      * apply IHre1 in H1. destruct H1 as [s1 H1].
        exists s1. apply MUnionL. apply H1.
      * apply IHre2 in H2. destruct H2 as [s2 H2].
        exists s2. apply MUnionR. apply H2.
    + exists []. apply MStar0.
Qed.
(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** One potentially confusing feature of the [induction] tactic is
    that it will let you try to perform an induction over a term that
    isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] without an [eqn:] clause can do),
    and leave you unable to complete the proof.  Here's an example: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** Now, just doing an [inversion] on [H1] won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence!). Here is a naive first attempt. *)

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** But now, although we get seven cases (as we would expect
    from the definition of [exp_match]), we have lost a very important
    bit of information from [H1]: the fact that [s1] matched something
    of the form [Star re].  This means that we have to give proofs for
    _all_ seven constructors of this definition, even though all but
    two of them ([MStar0] and [MStarApp]) are contradictory.  We can
    still get the proof to go through for a few constructors, such as
    [MEmpty]... *)

  - (* MEmpty *)
    simpl. intros H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show

      s2     =~ Char x' ->
      x'::s2 =~ Char x'

    which is clearly impossible. *)

  - (* MChar. *) intros H. simpl. (* Stuck... *)
Abort.

(** The problem here is that [induction] over a Prop hypothesis
    only works properly with hypotheses that are "completely
    general," i.e., ones in which all the arguments are variables,
    as opposed to more complex expressions like [Star re].

    (In this respect, [induction] on evidence behaves more like
    [destruct]-without-[eqn:] than like [inversion].)

    A possible, but awkward, way to solve this problem is "manually
    generalizing" over the problematic expressions by adding
    explicit equality hypotheses to the lemma: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** We can now proceed by performing induction over evidence
    directly, because the argument to the first hypothesis is
    sufficiently general, which means that we can discharge most cases
    by inverting the [re' = Star re] equality in the context.

    This works, but it makes the statement of the lemma a bit ugly.
    Fortunately, there is a better way... *)
Abort.

(** The tactic [remember e as x eqn:Eq] causes Coq to (1) replace all
    occurrences of the expression [e] by the variable [x], and (2) add
    an equation [Eq : x = e] to the context.  Here's how we can use it
    to show the above result: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re' eqn:Eq.

(** We now have [Eq : re' = Star re]. *)

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Eq] is contradictory in most cases, allowing us to
    conclude immediately. *)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** The interesting cases are those that correspond to [Star]. *)

  - (* MStar0 *)
    intros H. apply H.

  - (* MStarApp *)
    intros H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * apply Eq.
      * apply H1.

(** Note that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re], which
    results from the equality generated by [remember]. *)
Qed.

(** **** Exercise: 4 stars, standard, optional (exp_match_ex2) *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re Hmatch.
  remember (Star re) as re'.
  induction Hmatch
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists []. split. reflexivity. intros s' contra. inversion contra.
  - destruct (IH2 Heqre') as [ss' [H1 H2]].
    injection Heqre' as Heqre'. destruct Heqre'.
    exists (s1 :: ss'). split.
    + simpl. rewrite <- H1. reflexivity.
    + intros s' HIn. destruct HIn.
      * rewrite <- H. apply Hmatch1.
      * apply H2 in H. apply H.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced (weak_pumping)

    One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].  (For the sake of simplicity in this
    exercise, we consider a slightly weaker theorem than is usually
    stated in courses on automata theory -- hence the name
    [weak_pumping].)

    To get started, we need to define "sufficiently long."  Since we
    are working in a constructive logic, we actually need to be able
    to calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

(** You may find these lemmas about the pumping constant useful when
    proving the pumping lemma below. *)

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
  intros T re. induction re.
  - (* EmptySet *)
    apply le_n.
  - (* EmptyStr *)
    apply le_n.
  - (* Char *)
    apply le_S. apply le_n.
  - (* App *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Union *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Star *)
    simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  rewrite H in Hp1. inversion Hp1.
Qed.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

(** This auxiliary lemma might also be useful in your proof of the
    pumping lemma. *)

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.

(** The (weak) pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3], will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** Complete the proof below. Several of the lemmas about [le] that
    were in an optional exercise earlier in this chapter may also be
    useful. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - (* MChar *)
    intros contra. apply Sn_le_Sm__n_le_m in contra. inversion contra.
  - (* MApp *)
    intros H. simpl in H.
    rewrite app_length in H.
    apply plus_le_cases in H. destruct H.
    + apply IH1 in H.
      destruct H as [s1' [s2' [s3' [Happ [Hne Hnapp]]]]].
      exists s1'. exists s2'. exists (s3' ++ s2).
      split. rewrite Happ.
      rewrite <- app_assoc with T s1' (s2' ++ s3') s2.
      rewrite <- app_assoc with T s2' s3' s2.
      reflexivity.
      split. apply Hne.
      intros m.
      rewrite app_assoc with T s1' (napp m s2') (s3' ++ s2).
      rewrite app_assoc with T (s1' ++ napp m s2') s3' s2.
      rewrite <- app_assoc with T s1' (napp m s2') s3'.
      apply MApp. apply Hnapp. apply Hmatch2.
    + apply IH2 in H.
      destruct H as [s1' [s2' [s3' [Happ [Hne Hnapp]]]]].
      exists (s1 ++ s1'). exists s2'. exists s3'.
      split. rewrite Happ.
      rewrite <- app_assoc with T s1 s1' (s2' ++ s3').
      reflexivity.
      split. apply Hne.
      intros m.
      rewrite <- app_assoc with T s1 s1' (napp m s2' ++ s3').
      apply MApp. apply Hmatch1. apply Hnapp.
  - (* MUnionL *)
    intros H. simpl in H.
    apply plus_le in H. destruct H as [H H'].
    apply IH in H.
    destruct H as [s1' [s2' [s3' [Happ [Hne Hnapp]]]]].
    exists s1'. exists s2'. exists s3'.
    split. apply Happ.
    split. apply Hne.
    intros m. apply MUnionL. apply Hnapp.
  - (* MUnionR *)
    intros H. simpl in H.
    apply plus_le in H. destruct H as [H' H].
    apply IH in H.
    destruct H as [s1' [s2' [s3' [Happ [Hne Hnapp]]]]].
    exists s1'. exists s2'. exists s3'.
    split. apply Happ.
    split. apply Hne.
    intros m. apply MUnionR. apply Hnapp.
  - (* MStar0 *)
    intros H.
    assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
    inversion H as [H0|]. rewrite H0 in Hp. inversion Hp.
  - (* MStarApp *)
    intros H.
    rewrite app_length in H.
    assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
    assert (Hl: (1 <= length s1 \/ 1 <= length s2)).
    { destruct s1. right. apply le_trans with (pumping_constant re). apply Hp. apply H. left. simpl. apply n_le_m__Sn_le_Sm. apply O_le_n. }
    exists []. exists (s1 ++ s2). exists [].
    split. rewrite app_nil_r. reflexivity.
    split. destruct Hl as [Hl | Hl].
    + destruct s1. inversion Hl. discriminate.
    + destruct s2. inversion Hl. destruct s1. discriminate. discriminate.
    + induction m.
      * apply MStar0.
      * simpl in IHm. simpl. rewrite <- app_assoc.
        apply star_app.
        apply (MStarApp s1 s2 re Hmatch1 Hmatch2).
        apply IHm.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (pumping)

    Now here is the usual version of the pumping lemma. In addition to
    requiring that [s2 <> []], it also requires that [length s1 +
    length s2 <= pumping_constant re]. *)

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You may want to copy your proof of weak_pumping below. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - (* MChar *)
    intros contra. apply Sn_le_Sm__n_le_m in contra. inversion contra.
  - (* MApp *)
    intros H.
    assert (le_n_n: forall n : nat, ~ n < n).
    { intros n contra. induction n. inversion contra. apply IHn. apply Sn_le_Sm__n_le_m in contra. apply contra. }
    rewrite app_length in H. simpl in H.
    destruct (lt_ge_cases (length s1) (pumping_constant re1)) as [H1 | H1].
    + destruct (lt_ge_cases (length s2) (pumping_constant re2)) as [H2 | H2].
      * apply plus_le_cases in H. destruct H as [H1' | H2'].
        ** assert (contra: pumping_constant re1 < pumping_constant re1).
           {
             apply le_trans with (n := S (length s1)).
             apply n_le_m__Sn_le_Sm. apply H1'. apply H1.
           }
           apply le_n_n in contra. exfalso. apply contra.
        ** assert (contra: pumping_constant re2 < pumping_constant re2).
           {
             apply le_trans with (n := S (length s2)).
             apply n_le_m__Sn_le_Sm. apply H2'. apply H2.
           }
           apply le_n_n in contra. exfalso. apply contra.
      * apply IH2 in H2.
        destruct H2 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
        exists (s1 ++ s1'). exists s2'. exists s3'.
        split. rewrite Happ.
        rewrite <- app_assoc with T s1 s1' (s2' ++ s3').
        reflexivity.
        split. apply Hne.
        split. simpl. rewrite app_length. rewrite <- add_assoc.
        apply le_trans with (n := length s1 + pumping_constant re2).
        apply plus_le_compat_l. apply Hlen.
        apply plus_le_compat_r. apply n_lt_m__n_le_m in H1. apply H1.
        intros m.
        rewrite <- app_assoc with T s1 s1' (napp m s2' ++ s3').
        apply MApp. apply Hmatch1. apply Hnapp.
    + apply IH1 in H1.
      destruct H1 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
      exists s1'. exists s2'. exists (s3' ++ s2).
      split. rewrite Happ.
      rewrite <- app_assoc with T s1' (s2' ++ s3') s2.
      rewrite <- app_assoc with T s2' s3' s2.
      reflexivity.
      split. apply Hne.
      split. simpl.
      apply le_trans with (n := pumping_constant re1).
      apply Hlen. apply le_plus_l.
      intros m.
      rewrite app_assoc with T s1' (napp m s2') (s3' ++ s2).
      rewrite app_assoc with T (s1' ++ napp m s2') s3' s2.
      rewrite <- app_assoc with T s1' (napp m s2') s3'.
      apply MApp. apply Hnapp. apply Hmatch2.
  - (* MUnionL *)
    intros H. simpl in H.
    apply plus_le in H. destruct H as [H H'].
    apply IH in H.
    destruct H as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
    exists s1'. exists s2'. exists s3'.
    split. apply Happ.
    split. apply Hne.
    split. simpl. apply le_trans with (n := pumping_constant re1). apply Hlen. apply le_plus_l.
    intros m. apply MUnionL. apply Hnapp.
  - (* MUnionR *)
    intros H. simpl in H.
    apply plus_le in H. destruct H as [H' H].
    apply IH in H.
    destruct H as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
    exists s1'. exists s2'. exists s3'.
    split. apply Happ.
    split. apply Hne.
    split. simpl. apply le_trans with (n := pumping_constant re2). apply Hlen. rewrite add_comm. apply le_plus_l.
    intros m. apply MUnionR. apply Hnapp.
  - (* MStar0 *)
    intros H.
    assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
    inversion H as [H0|]. rewrite H0 in Hp. inversion Hp.
  - (* MStarApp *)
    intros H.
    rewrite app_length in H.
    assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
    assert (Hl: (1 <= length s1 \/ 1 <= length s2)).
    { destruct s1. right. apply le_trans with (pumping_constant re). apply Hp. apply H. left. simpl. apply n_le_m__Sn_le_Sm. apply O_le_n. }
    destruct s1 as [| x s11].
    + destruct (lt_ge_cases (length s2) (pumping_constant (Star re))) as [H2 | H2].
      * exists []. exists s2. exists [].
        split. rewrite app_nil_r. reflexivity.
        split. destruct Hl as [Hl | Hl].
        ** inversion Hl.
        ** destruct s2. inversion Hl. discriminate.
        ** split. apply n_lt_m__n_le_m in H2. apply H2.
        induction m. apply MStar0. simpl. rewrite <- app_assoc. apply star_app. apply Hmatch2. apply IHm.
      * apply IH2 in H2.
        destruct H2 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
        exists s1'. exists s2'. exists s3'.
        split. rewrite Happ. reflexivity.
        split. apply Hne.
        split. apply Hlen.
        apply Hnapp.
    + remember (x :: s11) as s1.
      destruct (lt_ge_cases (length s1) (pumping_constant re)) as [H1 | H1].
      * exists []. exists s1. exists s2.
        split. reflexivity.
        split. rewrite Heqs1. discriminate.
        split. apply n_lt_m__n_le_m in H1. apply H1.
        intros m. simpl. apply napp_star. apply Hmatch1. apply Hmatch2.
      * apply IH1 in H1.
        destruct H1 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
        exists s1'. exists s2'. exists (s3' ++ s2).
        split. rewrite Happ. simpl.
        rewrite <- app_assoc with (m := s2' ++ s3').
        rewrite <- app_assoc with (m := s3').
        reflexivity.
        split. apply Hne.
        split. apply Hlen.
        intros m. rewrite app_assoc. rewrite app_assoc. apply MStarApp.
        rewrite <- app_assoc. apply Hnapp. apply Hmatch2.
Qed.

End Pumping.
(** [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

(** We've seen in the [Logic] chapter that we sometimes
    need to relate boolean computations to statements in [Prop].  But
    performing this conversion as we did there can result in tedious
    proof scripts.  Consider the proof of the following theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] -> In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = nil *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly apply
    the [eqb_eq] lemma to the equation generated by
    destructing [n =? m], to convert the assumption [n =? m
    = true] into the assumption [n = m]; then we had to [rewrite]
    using this assumption to complete the case. *)

(** We can streamline this sort of reasoning by defining an inductive
    proposition that yields a better case-analysis principle for [n =?
    m].  Instead of generating the assumption [(n =? m) = true], which
    usually requires some massaging before we can use it, this
    principle gives us right away the assumption we really need: [n =
    m].

    Following the terminology introduced in [Logic], we call this
    the "reflection principle for equality on numbers," and we say
    that the boolean [n =? m] is _reflected in_ the proposition [n =
    m]. *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H :   P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  It states that the property [P]
    _reflects_ (intuitively, is equivalent to) the boolean [b]: that
    is, [P] holds if and only if [b = true].

    To see this, notice that, by definition, the only way we can
    produce evidence for [reflect P true] is by showing [P] and then
    using the [ReflectT] constructor.  If we invert this statement,
    this means that we can extract evidence for [P] from a proof of
    [reflect P true].

    Similarly, the only way to show [reflect P false] is by tagging
    evidence for [~ P] with the [ReflectF] constructor. *)

(** To put this observation to work, we first prove that the
    statements [P <-> b = true] and [reflect P b] are indeed
    equivalent.  First, the left-to-right implication: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(** Now you prove the right-to-left implication: *)

(** **** Exercise: 2 stars, standard, especially useful (reflect_iff) *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b r. destruct r as [HP | HnP].
  - split. reflexivity. intros. apply HP.
  - split.
    + intros HP. exfalso. apply (HnP HP).
    + discriminate.
Qed.
(** [] *)

(** We can think of [reflect] as a variant of the usual "if and only
    if" connective; the advantage of [reflect] is that, by destructing
    a hypothesis or lemma of the form [reflect P b], we can perform
    case analysis on [b] while _at the same time_ generating
    appropriate hypothesis in the two branches ([P] in the first
    subgoal and [~ P] in the second). *)

(** Let's use [reflect] to produce a smoother proof of
    [filter_not_empty_In].

    We begin by recasting the [eqb_eq] lemma in terms of [reflect]: *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** The proof of [filter_not_empty_In] now goes as follows.  Notice
    how the calls to [destruct] and [rewrite] in the earlier proof of
    this theorem are combined here into a single call to
    [destruct]. *)

(** (To see this clearly, execute the two proofs of
    [filter_not_empty_In] with Coq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [EQnm | NEQnm].
    + (* n = m *)
      intros _. rewrite EQnm. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, standard, especially useful (eqbP_practice)

    Use [eqbP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [| m l' IHl'].
  - intros contra. inversion contra.
  - simpl in Hcount. destruct (eqbP n m).
    + inversion Hcount.
    + intros contra. destruct contra as [Heq | HIn].
      * symmetry in Heq. apply (H Heq).
      * apply (IHl' Hcount HIn).
Qed.
(** [] *)

(** This small example shows reflection giving us a small gain in
    convenience; in larger developments, using [reflect] consistently
    can often lead to noticeably shorter and clearer proof scripts.
    We'll see many more examples in later chapters and in _Programming
    Language Foundations_.

    This way of using [reflect] was popularized by _SSReflect_, a Coq
    library that has been used to formalize important results in
    mathematics, including the 4-color theorem and the Feit-Thompson
    theorem.  The name SSReflect stands for _small-scale reflection_,
    i.e., the pervasive use of reflection to streamline small proof
    steps by turning them into boolean computations. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (nostutter_defn)

    Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from not containing duplicates:
    the sequence [[1;4;1]] has two occurrences of the element [1] but
    does not stutter.)  The property "[nostutter mylist]" means that
    [mylist] does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

Inductive nostutter {X:Type} : list X -> Prop :=
  | nostutter0 : nostutter []
  | nostutter1 x : nostutter [x]
  | nostutter2 x y l (P: x <> y) (H: nostutter (y :: l)) : nostutter (x :: y :: l)
.
(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  apply nostutter2. discriminate.
  apply nostutter2. discriminate.
  apply nostutter2. discriminate.
  apply nostutter2. discriminate.
  apply nostutter2. discriminate.
  apply nostutter1.
Qed.
(*
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
*)

Example test_nostutter_2:  nostutter (@nil nat).
Proof. apply nostutter0. Qed.
(*
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
*)

Example test_nostutter_3:  nostutter [5].
Proof. apply nostutter1. Qed.
(*
  Proof. repeat constructor; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof.
  intros contra1.
  inversion contra1 as [| |x1 y1 l1 _ contra2].
  inversion contra2 as [| |x2 y2 l2 contra _].
  apply contra. reflexivity.
Qed.
(*
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. Qed.
*)

(* Do not modify the following line: *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)

    Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    First define what it means for one list to be a merge of two
    others.  Do this with an inductive relation, not a [Fixpoint].  *)

Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  | mergel0 l : merge l [] l
  | merger0 l : merge [] l l
  | mergel1 x l l1 l2 (H: merge l1 l2 l) : merge (x :: l1) l2 (x :: l)
  | merger1 x l l1 l2 (H: merge l1 l2 l) : merge l1 (x :: l2) (x :: l)
.

Theorem merge_filter : forall (X : Set) (test: X->bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l l1 l2 H H1 H2.
  induction H as [| |x l l1 l2 _ IHm|x l l1 l2 _ IHm].
  - induction l.
    + reflexivity.
    + destruct H1 as [Htest H1]. simpl. rewrite Htest. rewrite (IHl H1). reflexivity.
  - induction l.
    + reflexivity.
    + destruct H2 as [Htest H2]. simpl. rewrite Htest. apply (IHl H2).
  - destruct H1 as [Htest H1]. simpl. rewrite Htest. rewrite (IHm H1 H2). reflexivity.
  - destruct H2 as [Htest H2]. simpl. rewrite Htest. rewrite (IHm H1 H2). reflexivity.
Qed.

(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)

    A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

Theorem subs_filter : forall (test: nat->bool) (l1 l2 : list nat),
  subseq l1 l2 ->
  All (fun n => test n = true) l1 ->
  length l1 <= length (filter test l2).
Proof.
  intros test l1 l2 H H1.
  induction H as [| x l1 l2 H IH | x l1 l2 H IH].
  - apply O_le_n.
  - destruct H1 as [Htest H1]. simpl. rewrite Htest. simpl. apply n_le_m__Sn_le_Sm. apply (IH H1).
  - simpl. destruct (test x).
    + simpl. apply le_S. apply (IH H1).
    + apply (IH H1).
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (palindromes)

    A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)

Inductive pal {X:Type} : list X -> Prop :=
  | pal0 : pal []
  | pal1 x : pal [x]
  | pal2 x l (H: pal l) : pal (x :: l ++ [x])
.

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
  intros X l.
  induction l.
  - apply pal0.
  - simpl. rewrite app_assoc. apply pal2. apply IHl.
Qed.

Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
  intros X l H.
  induction H as [| | x l _ IH].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite <- IH. rewrite <- app_assoc. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (palindrome_converse)

    Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)

Theorem palindrome_converse: forall {X: Type} (l: list X),
    l = rev l -> pal l.
Proof.
  intros X.
  assert (rev_length: forall (l: list X), length (rev l) = length l).
  {
    intros l. induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite -> app_length.
      simpl. rewrite -> IHl'. rewrite add_comm.
      reflexivity.
  }
  assert (lemma: forall (n: nat) (l: list X), length l <= n -> l = rev l -> pal l).
  {
    induction n.
    - intros l Hn _. destruct l. apply pal0. inversion Hn.
    - destruct l.
      + intros _ _. apply pal0.
      + intros Hlen Hrev. destruct (rev l) as [| x' l'] eqn:H'.
        * destruct l. apply pal1. apply f_equal with (f:=rev) in H'. rewrite rev_involutive in H'. discriminate.
        * simpl in Hrev. rewrite H' in Hrev. rewrite Hrev. injection Hrev as H0 H. destruct H0. apply pal2.
          apply f_equal with (f:=rev) in H. rewrite rev_app_distr in H. simpl in H. rewrite H' in H. injection H as H.
          apply f_equal with (f:=length) in H'. simpl in H'.
          simpl in Hlen. apply Sn_le_Sm__n_le_m in Hlen.
          rewrite rev_length in H'.
          assert (Hlen': length l' <= n).
          { apply Sn_le_Sm__n_le_m. rewrite <- H'. apply le_S. apply Hlen. }
          apply (IHn l' Hlen' H).
  }
  intros l.
  apply (lemma (length l) l). apply le_n.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (NoDup)

    Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

Module RecallIn.
   Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
     match l with
     | [] => False
     | x' :: l' => x' = x \/ In A x l'
     end.
End RecallIn.

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

Inductive disjoint {X : Type} : list X -> list X -> Prop :=
  | disjoint0 l : disjoint [] l
  | disjoint1 x l1 l2 (P: ~ In x l2) (H: disjoint l1 l2) : disjoint (x :: l1) l2
.

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

Inductive NoDup {X : Type} : list X -> Prop :=
  | NoDup0 : NoDup []
  | NoDup1 x l (P: ~ In x l) (H: NoDup l) : NoDup (x :: l)
.

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

Theorem disjoint_NoDup_app : forall (X:Type) (l1:list X) (l2:list X), NoDup l1 -> NoDup l2 -> disjoint l1 l2 -> NoDup (l1 ++ l2).
Proof.
  intros X l1 l2 H1 H2 H.

  induction H as [| x l1 l2 P2 Hd].
  - apply H2.
  - simpl. apply NoDup1.
    + intros contra. apply In_app_iff in contra. destruct contra as [contra | contra].
      * inversion H1 as [| x1 l1' P1]. apply (P1 contra).
      * apply (P2 contra).
    + inversion H1 as [| x1 l1' P1 H1']. apply (IHHd H1' H2).
Qed.

Theorem NoDup_app : forall (X:Type) (l1:list X) (l2:list X), NoDup (l1 ++ l2) -> NoDup l1 /\ NoDup l2.
Proof.
  intros.
  split.
  - induction l1. apply NoDup0. apply NoDup1.
    + intros contra. inversion H. apply P. apply In_app_iff. left. apply contra.
    + inversion H. apply (IHl1 H1).
  - induction l1.
    + apply H.
    + inversion H. apply (IHl1 H1).
Qed.

Theorem NoDup_app_disjoint : forall (X:Type) (l1:list X) (l2:list X), NoDup (l1 ++ l2) -> disjoint l1 l2.
Proof.
  intros X l1 l2 H.
  induction l1.
  - apply disjoint0.
  - apply disjoint1.
    + inversion H. intros contra. apply P. apply In_app_iff. right. apply contra.
    + inversion H. apply (IHl1 H1).
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle)

    The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy and useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros.
  induction l.
  - inversion H.
  - inversion H.
    + exists []. exists l. rewrite H0. reflexivity.
    + apply IHl in H0. destruct H0 as [l1 [l2 H0]].
      exists (x0 :: l1). exists l2. rewrite H0. reflexivity.
Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | repeats1 x l (P: In x l): repeats (x :: l)
  | repeats2 x l (H: repeats l): repeats (x :: l)
.

(* Do not modify the following line: *)
Definition manual_grade_for_check_repeats : option (nat*string) := None.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)
Theorem pigeonhole_principle: excluded_middle ->
  forall (X:Type) (l1  l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM X l1. induction l1 as [|x l1' IHl1'].
  - intros. inversion H0.
  - intros. destruct (EM (In x l1')) as [HIn | HnIn].
    + apply repeats1. apply HIn.
    + apply repeats2.
      destruct (in_split X x l2) as [l0 [l2' H3]].
      { apply H. simpl. left. reflexivity. }
      apply IHl1' with (l0 ++ l2').
      * intros. apply In_app_iff. assert (In x0 l2). apply H. right. apply H1.
        rewrite H3 in H2. apply In_app_iff in H2. destruct H2. left. apply H2.
        right. destruct H2. rewrite H2 in HnIn. exfalso. apply HnIn. apply H1. apply H2.
      * apply f_equal with (f:=length) in H3. rewrite app_length in H3. rewrite add_comm in H3. simpl in H3. rewrite app_length. rewrite add_comm. rewrite H3 in H0. simpl in H0. apply Sn_le_Sm__n_le_m in H0. apply H0.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match automatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function that reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represented
    as lists of ASCII characters: *)
Require Import Coq.Strings.Ascii.

Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)

(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
  s =~ App re0 re1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, standard, optional (app_ne)

    [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([ ] =~ re0 /\ a :: s =~ re1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H.
    destruct s1.
    + left. split. apply H3. apply H4.
    + right. inversion H1 as [H1']. destruct H1'. exists s1. exists s2. split. reflexivity. split. apply H3. apply H4.
  - intros.
    destruct H as [[H1 H2] | [s1 [s2 [H1 [H2 H3]]]]].
    + assert (silly: a :: s = [] ++ a :: s). reflexivity. rewrite silly. apply MApp. apply H1. apply H2.
    + rewrite H1. assert (silly: a :: s1 ++ s2 = (a :: s1) ++ s2). reflexivity. rewrite silly. apply MApp. apply H2. apply H3.
Qed.
(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
  s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (star_ne)

    [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  split.
  - remember (a :: s) as s'. remember (Star re) as re'.
    intros H. induction H as [| | | | | | s1 s2 re' H1 _ H2 IH].
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + destruct s1.
      * apply (IH Heqs' Heqre').
      * injection Heqre' as Heqre'. destruct Heqre'.
        injection Heqs' as Heqs' Happ. destruct Heqs'.
        exists s1. exists s2.
        split. rewrite Happ. reflexivity.
        split. apply H1. apply H2.
  - intros H. destruct H as [s1 [s2 [H1 [H2 H3]]]].
    rewrite H1.
    assert (silly: a :: s1 ++ s2 = (a :: s1) ++ s2). reflexivity. rewrite silly.
    apply (MStarApp (a :: s1) s2 re H2 H3).
Qed.
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, standard, optional (match_eps)

    Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: reg_exp ascii) : bool
  := match re with
     | EmptySet => false
     | EmptyStr => true
     | Char _ => false
     | App re1 re2 => (match_eps re1) && (match_eps re2)
     | Union re1 re2 => (match_eps re1) || (match_eps re2)
     | Star _ => true
  end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (match_eps_refl)

    Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  intros re.
  induction re.
  - apply ReflectF. intros contra. inversion contra.
  - apply ReflectT. apply MEmpty.
  - apply ReflectF. intros contra. inversion contra.
  - simpl. inversion IHre1 as [H1 Hb1 | H1 Hb1].
    + inversion IHre2 as [H2 Hb2 | H2 Hb2].
      * apply ReflectT. apply (MApp [] re1 [] re2 H1 H2).
      * apply ReflectF.
        intros contra. inversion contra as [| | s1 re1' s2 re2' H1' H2'| | | |].
        destruct s2. apply (H2 H2'). destruct s1. discriminate. discriminate.
    + apply ReflectF.
      intros contra. inversion contra as [| | s1 re1' s2 re2' H1' H2'| | | |].
      destruct s1. apply (H1 H1'). discriminate.
  - simpl. inversion IHre1 as [H1 Hb1 | H1 HB1].
    + apply ReflectT. apply MUnionL. apply H1.
    + inversion IHre2 as [H2 Hb2 | H2 Hb2].
      * apply ReflectT. apply MUnionR. apply H2.
      * apply ReflectF.
        intros contra. inversion contra as [| | | s1 re1' re2' H1' | re1' s1 re2' H2' | |].
        ** apply (H1 H1').
        ** apply (H2 H2').
  - apply ReflectT. apply MStar0.
Qed.
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, standard, optional (derive)

    Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii
  := match re with
     | EmptySet => EmptySet
     | EmptyStr => EmptySet
     | Char x => if eqb x a then EmptyStr else EmptySet
     | App re1 re2 => if match_eps re1 then Union (derive a re2) (App (derive a re1) re2) else App (derive a re1) re2
     | Union re1 re2 => Union (derive a re1) (derive a re2)
     | Star re => App (derive a re) (Star re)
     end.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  reflexivity. Qed.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  reflexivity. Qed.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
  reflexivity. Qed.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  reflexivity. Qed.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  reflexivity. Qed.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  reflexivity. Qed.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  reflexivity. Qed.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  reflexivity. Qed.

(** **** Exercise: 4 stars, standard, optional (derive_corr)

    Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.
  intros a re s.
  split.
  - generalize dependent s. induction re.
    + intros s H. apply null_matches_none in H. destruct H.
    + intros s H. apply empty_nomatch_ne in H. destruct H.
    + intros s H. simpl. destruct (eqb_spec t a) as [HEq | HnEq].
      * destruct HEq. apply char_eps_suffix in H. rewrite H. apply MEmpty.
      * assert (HnEq': a <> t). { intros contra. apply HnEq. rewrite contra. reflexivity. }
        apply (char_nomatch_char t a s HnEq') in H. destruct H.
    + intros s H. simpl. destruct (match_eps_refl re1) as [_ | Hnm].
      * apply app_ne in H. destruct H as [[H1 H2] | [s1 [s2 [H [H1 H2]]]]].
        ** apply MUnionL. apply (IHre2 s H2).
        ** apply MUnionR. rewrite H. apply MApp. apply (IHre1 s1 H1). apply H2.
      * apply app_ne in H. destruct H as [[H1 H2] | [s1 [s2 [H [H1 H2]]]]].
        ** exfalso. apply Hnm. apply H1.
        ** rewrite H. apply MApp. apply (IHre1 s1 H1). apply H2.
    + intros s H. simpl. apply union_disj in H. destruct H as [Hl | Hr].
      * apply MUnionL. apply (IHre1 s Hl).
      * apply MUnionR. apply (IHre2 s Hr).
    + intros s H. simpl. apply star_ne in H. destruct H as [s1 [s2 [H [H1 H2]]]].
      rewrite H. apply MApp. apply (IHre s1 H1). apply H2.
  - generalize dependent s. induction re.
    + intros s H. apply null_matches_none in H. destruct H.
    + intros s H. apply null_matches_none in H. destruct H.
    + intros s H. simpl in H. destruct (eqb_spec t a) as [HEq | HnEq].
      * destruct HEq. apply empty_matches_eps in H. rewrite H. apply MChar.
      * assert (HnEq': a <> t). { intros contra. apply HnEq. rewrite contra. reflexivity. }
        apply (char_nomatch_char t a s HnEq'). apply null_matches_none in H. apply H.
    + intros s H. simpl in H. apply app_ne.
      * destruct (match_eps_refl re1) as [Hm | Hnm].
        ** apply union_disj in H. destruct H as [Hl | Hr].
           *** left. split. apply Hm. apply (IHre2 s Hl).
           *** right. apply app_exists in Hr. destruct Hr as [s1 [s2 [H [H1 H2]]]].
               exists s1. exists s2. split. rewrite H. reflexivity. split. apply (IHre1 s1 H1). apply H2.
        ** right. apply app_exists in H. destruct H as [s1 [s2 [H [H1 H2]]]].
           exists s1. exists s2. split. rewrite H. reflexivity. split. apply (IHre1 s1 H1). apply H2.
    + intros s H. simpl in H. apply union_disj in H. destruct H as [Hl | Hr].
      * apply MUnionL. apply (IHre1 s Hl).
      * apply MUnionR. apply (IHre2 s Hr).
    + intros s H. apply star_ne.
      simpl in H. apply app_exists in H. destruct H as [s1 [s2 [H [H1 H2]]]].
      exists s1. exists s2. split. rewrite H. reflexivity. split. apply (IHre s1 H1). apply H2.
Qed.
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)

(** A function [m] _matches regexes_ if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, standard, optional (regex_match)

    Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool
  := match s with
     | (a :: s) => regex_match s (derive a re)
     | [] => match_eps re
     end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (regex_match_correct)

    Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_match_correct : matches_regex regex_match.
Proof.
  intros s.
  induction s as [|a s].
  - intros re. simpl. destruct (match_eps_refl re). apply ReflectT. apply H. apply ReflectF. apply H.
  - intros re. simpl. destruct (IHs (derive a re)) as [Htrue | Hfalse].
    + apply ReflectT. apply (derive_corr a re s). apply Htrue.
    + apply ReflectF. intros contra. apply Hfalse. apply (derive_corr a re s). apply contra.
Qed.
(** [] *)

(* 2025-01-13 16:19 *)
