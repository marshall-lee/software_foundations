(** * Hoare: Hoare Logic, Part I *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
Set Default Goal Selector "!".

(** In the final chaper of _Logical Foundations_ (_Software
    Foundations_, volume 1), we began applying the mathematical tools
    developed in the first part of the course to studying the theory
    of a small programming language, Imp.

    - We defined a type of _abstract syntax trees_ for Imp, together
      with an _evaluation relation_ (a partial function on states)
      that specifies the _operational semantics_ of programs.

      The language we defined, though small, captures some of the key
      features of full-blown languages like C, C++, and Java,
      including the fundamental notion of mutable state and some
      common control structures.

    - We proved a number of _metatheoretic properties_ -- "meta" in
      the sense that they are properties of the language as a whole,
      rather than of particular programs in the language.  These
      included:

        - determinism of evaluation

        - equivalence of some different ways of writing down the
          definitions (e.g., functional and relational definitions of
          arithmetic expression evaluation)

        - guaranteed termination of certain classes of programs

        - correctness (in the sense of preserving meaning) of a number
          of useful program transformations

        - behavioral equivalence of programs (in the [Equiv]
          chapter). *)

(** If we stopped here, we would already have something useful: a set
    of tools for defining and discussing programming languages and
    language features that are mathematically precise, flexible, and
    easy to work with, applied to a set of key properties.  All of
    these properties are things that language designers, compiler
    writers, and users might care about knowing.  Indeed, many of them
    are so fundamental to our understanding of the programming
    languages we deal with that we might not consciously recognize
    them as "theorems."  But properties that seem intuitively obvious
    can sometimes be quite subtle (sometimes also subtly wrong!).

    We'll return to the theme of metatheoretic properties of whole
    languages later in this volume when we discuss _types_ and _type
    soundness_.  In this chapter, though, we turn to a different set
    of issues.
*)

(** Our goal in this chapter is to carry out some simple examples of
    _program verification_ -- i.e., to use the precise definition of
    Imp to prove formally that particular programs satisfy particular
    specifications of their behavior.

    We'll develop a reasoning system called _Floyd-Hoare Logic_ --
    often shortened to just _Hoare Logic_ -- in which each of the
    syntactic constructs of Imp is equipped with a generic "proof
    rule" that can be used to reason compositionally about the
    correctness of programs involving this construct. *)

(** Hoare Logic originated in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a multitude of tools that are being used in
    academia and industry to specify and verify real software systems. *)

(** Hoare Logic combines two beautiful ideas: a natural way of writing
    down _specifications_ of programs, and a _structured proof
    technique_ for proving that programs are correct with respect to
    such specifications -- where by "structured" we mean that the
    structure of proofs directly mirrors the structure of the programs
    that they are about. *)

(* ################################################################# *)
(** * Assertions *)

(** An _assertion_ is a logical claim about the state of a program's
    memory -- formally, a property of [state]s. *)

Definition Assertion := state -> Prop.

(** For example,

    - [fun st => st X = 3] holds for states [st] in which value of [X]
      is [3],

    - [fun st => True] hold for all states, and

    - [fun st => False] holds for no states. *)

(** **** Exercise: 1 star, standard, optional (assertions)

    Paraphrase the following assertions in English (or your favorite
    natural language). *)

Module ExAssertions.
Definition assertion1 : Assertion := fun st => st X <= st Y.
Definition assertion2 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition assertion3 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition assertion4 : Assertion :=
  fun st => st Z = max (st X) (st Y).
(* FILL IN HERE *)
End ExAssertions.
(** [] *)

(** This way of writing assertions can be a little bit heavy,
    for two reasons: (1) every single assertion that we ever write is
    going to begin with [fun st => ]; and (2) this state [st] is the
    only one that we ever use to look up variables in assertions (we
    will never need to talk about two different memory states at the
    same time).  For discussing examples informally, we'll adopt some
    simplifying conventions: we'll drop the initial [fun st =>], and
    we'll write just [X] to mean [st X].  Thus, instead of writing

      fun st => st X = m

    we'll write just

      X = m.
*)

(** This example also illustrates a convention that we'll use
    throughout the Hoare Logic chapters: in informal assertions,
    capital letters like [X], [Y], and [Z] are Imp variables, while
    lowercase letters like [x], [y], [m], and [n] are ordinary Coq
    variables (of type [nat]).  This is why, when translating from
    informal to formal, we replace [X] with [st X] but leave [m]
    alone. *)

(** Given two assertions [P] and [Q], we say that [P] _implies_ [Q],
    written [P ->> Q], if, whenever [P] holds in some state [st], [Q]
    also holds. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** (The [hoare_spec_scope] annotation here tells Coq that this
    notation is not global but is intended to be used in particular
    contexts.  The [Open Scope] tells Coq that this file is one such
    context.) *)

(** We'll also want the "iff" variant of implication between
    assertions: *)

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                          (at level 80) : hoare_spec_scope.

(* ================================================================= *)
(** ** Notations for Assertions *)

(** The convention described above can be implemented in Coq with a
    little syntax magic, using coercions and annotation scopes, much
    as we did with [%imp] in [Imp], to automatically lift
    [aexp]s, numbers, and [Prop]s into [Assertion]s when they appear
    in the [%assertion] scope or when Coq knows that the type of an
    expression is [Assertion].

    There is no need to understand the details of how these notation
    hacks work. (We barely understand some of it ourselves!) *)

Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).

Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st ->  assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <->  assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

(** One small limitation of this approach is that we don't have
    an automatic way to coerce function applications that appear
    within an assertion to make appropriate use of the state.
    Instead, we use an explicit [ap] operator to lift the function. *)

Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).

Module ExamplePrettyAssertions.
Definition ex1 : Assertion := X = 3.
Definition ex2 : Assertion := True.
Definition ex3 : Assertion := False.

Definition assertion1 : Assertion := X <= Y.
Definition assertion2 : Assertion := X = 3 \/ X <= Y.
Definition assertion3 : Assertion := Z = ap2 max X Y.
Definition assertion4 : Assertion := Z * Z <= X
                            /\  ~ (((ap S Z) * (ap S Z)) <= X).
End ExamplePrettyAssertions.

(* ################################################################# *)
(** * Hoare Triples, Informally *)

(** A _Hoare triple_ is a claim about the state before and
    after executing a command.  The standard notation is

      {P} c {Q}

    meaning:

      - If command [c] begins execution in a state satisfying assertion [P],
      - and if [c] eventually terminates in some final state,
      - then that final state will satisfy the assertion [Q].

    Assertion [P] is called the _precondition_ of the triple, and [Q] is
    the _postcondition_.

    Because single braces are already used for other things in Coq, we'll write
    Hoare triples with double braces:

       {{P}} c {{Q}}
*)
(** For example,

    - [{{X = 0}} X := X + 1 {{X = 1}}] is a valid Hoare triple,
      stating that command [X := X + 1] will transform a state in
      which [X = 0] to a state in which [X = 1].

    - [forall m, {{X = m}} X := X + 1 {{X = m + 1}}] is a
      _proposition_ stating that the Hoare triple [{{X = m}} X := X +
      1 {{X = m + 1}}] is valid for any choice of [m].  Note that [m]
      in the two assertions and the command in the middle is a
      reference to the _Coq_ variable [m], which is bound outside the
      Hoare triple. *)

(** **** Exercise: 1 star, standard, optional (triples)

    Paraphrase the following in English.

     1) {{True}} c {{X = 5}}

     2) forall m, {{X = m}} c {{X = m + 5)}}

     3) {{X <= Y}} c {{Y <= X}}

     4) {{True}} c {{False}}

     5) forall m,
          {{X = m}}
          c
          {{Y = real_fact m}}

     6) forall m,
          {{X = m}}
          c
          {{(Z * Z) <= m /\ ~ (((S Z) * (S Z)) <= m)}}
*)
(* FILL IN HERE

    [] *)

(** **** Exercise: 1 star, standard, optional (valid_triples)

    Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?

   1) {{True}} X := 5 {{X = 5}}

   2) {{X = 2}} X := X + 1 {{X = 3}}

   3) {{True}} X := 5; Y := 0 {{X = 5}}

   4) {{X = 2 /\ X = 3}} X := 5 {{X = 0}}

   5) {{True}} skip {{False}}

   6) {{False}} skip {{True}}

   7) {{True}} while true do skip end {{False}}

   8) {{X = 0}}
        while X = 0 do X := X + 1 end
      {{X = 1}}

   9) {{X = 1}}
        while X <> 0 do X := X + 1 end
      {{X = 100}}
*)
(* FILL IN HERE

    [] *)

(* ################################################################# *)
(** * Hoare Triples, Formally *)

(** We can formalize valid Hoare triples in Coq as follows: *)

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st  ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 90, c custom com at level 99)
    : hoare_spec_scope.
Check ({{True}} X := 0 {{True}}).

(** **** Exercise: 1 star, standard (hoare_post_true) *)

(** Prove that if [Q] holds in every state, then any triple with [Q]
    as its postcondition is valid. *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (hoare_pre_false) *)

(** Prove that if [P] holds in no state, then any triple with [P] as
    its precondition is valid. *)

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Proof Rules *)

(** The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of specific Hoare triples.  That
    is, we want the structure of a program's correctness proof to
    mirror the structure of the program itself.  To this end, in the
    sections below, we'll introduce a rule for reasoning about each of
    the different syntactic forms of commands in Imp -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules for gluing things together.  We
    will then be able to prove programs correct using these proof
    rules, without ever unfolding the definition of [valid_hoare_triple]. *)

(* ================================================================= *)
(** ** Skip *)

(** Since [skip] doesn't change the state, it preserves any
    assertion [P]:

      --------------------  (hoare_skip)
      {{ P }} skip {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H; subst. assumption.
Qed.

(* ================================================================= *)
(** ** Sequencing *)

(** If command [c1] takes any state where [P] holds to a state where
    [Q] holds, and if [c2] takes any state where [Q] holds to one
    where [R] holds, then doing [c1] followed by [c2] will take any
    state where [P] holds to one where [R] holds:

        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ----------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  unfold valid_hoare_triple.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  eauto.
Qed.

(** Note that, in the formal rule [hoare_seq], the premises are
    given in backwards order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule, since the natural way to construct a Hoare-logic
    proof is to begin at the end of the program (with the final
    postcondition) and push postconditions backwards through commands
    until we reach the beginning. *)

(* ================================================================= *)
(** ** Assignment *)

(** The rule for assignment is the most fundamental of the Hoare
    logic proof rules.  Here's how it works.

    Consider this incomplete Hoare triple:

       {{ ??? }}  X := Y  {{ X = 1 }}

    We want to assign [Y] to [X] and finish in a state where [X] is [1].
    What could the precondition be?

    One possibility is [Y = 1], because if [Y] is already [1] then
    assigning it to [X] causes [X] to be [1].  That leads to a valid
    Hoare triple:

       {{ Y = 1 }}  X := Y  {{ X = 1 }}

    It may seem as though coming up with that precondition must have
    taken some clever thought.  But there is a mechanical way we could
    have done it: if we take the postcondition [X = 1] and in it
    replace [X] with [Y]---that is, replace the left-hand side of the
    assignment statement with the right-hand side---we get the
    precondition, [Y = 1]. *)

(** That same idea works in more complicated cases.  For
    example:

       {{ ??? }}  X := X + Y  {{ X = 1 }}

    If we replace the [X] in [X = 1] with [X + Y], we get [X + Y = 1].
    That again leads to a valid Hoare triple:

       {{ X + Y = 1 }}  X := X + Y  {{ X = 1 }}

    Why does this technique work?  The postcondition identifies some
    property [P] that we want to hold of the variable [X] being
    assigned.  In this case, [P] is "equals [1]".  To complete the
    triple and make it valid, we need to identify a precondition that
    guarantees that property will hold of [X].  Such a precondition
    must ensure that the same property holds of _whatever is being
    assigned to_ [X].  So, in the example, we need "equals [1]" to
    hold of [X + Y].  That's exactly what the technique guarantees. *)


(** In general, the postcondition could be some arbitrary assertion
    [Q], and the right-hand side of the assignment could be some
    arbitrary arithmetic expression [a]:

       {{ ??? }}  X := a  {{ Q }}

    The precondition would then be [Q], but with any occurrences of
    [X] in it replaced by [a].

    Let's introduce a notation for this idea of replacing occurrences:
    Define [Q [X |-> a]] to mean "[Q] where [a] is substituted in
    place of [X]".

    This yields the Hoare logic rule for assignment:

      {{ Q [X |-> a] }}  X := a  {{ Q }}

    One way of reading this rule is: If you want statement [X := a]
    to terminate in a state that satisfies assertion [Q], then it
    suffices to start in a state that also satisfies [Q], except
    where [a] is substituted for every occurrence of [X]. *)

(** To many people, this rule seems "backwards" at first, because
    it proceeds from the postcondition to the precondition.  Actually
    it makes good sense to go in this direction: the postcondition is
    often what is more important, because it characterizes what we
    can assume afer running the code.

    Nonetheless, it's also possible to formulate a "forward" assignment
    rule.  We'll do that later in some exercises. *)

(** Here are some valid instances of the assignment rule:

      {{ (X <= 5) [X |-> X + 1] }}   (that is, X + 1 <= 5)
        X := X + 1
      {{ X <= 5 }}

      {{ (X = 3) [X |-> 3] }}        (that is, 3 = 3)
        X := 3
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [X |-> 3]  (that is, 0 <= 3 /\ 3 <= 5)
        X := 3
      {{ 0 <= X /\ X <= 5 }}
*)

(** To formalize the rule, we must first formalize the idea of
    "substituting an expression for an Imp variable in an assertion",
    which we refer to as assertion substitution, or [assertion_sub].  That
    is, intuitively, given a proposition [P], a variable [X], and an
    arithmetic expression [a], we want to derive another proposition
    [P'] that is just the same as [P] except that [P'] should mention
    [a] wherever [P] mentions [X]. *)

(** This operation is related to the idea of substituting Imp
    expressions for Imp variables that we saw in [Equiv]
    ([subst_aexp] and friends). The difference is that, here,
    [P] is an arbitrary Coq assertion, so we can't directly
    "edit" its text. *)

(** However, we can achieve the same effect by evaluating [P] in an
    updated state: *)

Definition assertion_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assertion_sub X a P)
  (at level 10, X at next level, a custom com) : hoare_spec_scope.

(** That is, [P [X |-> a]] stands for an assertion -- let's call it
    [P'] -- that is just like [P] except that, wherever [P] looks up
    the variable [X] in the current state, [P'] instead uses the value
    of the expression [a]. *)

(** To see how this works, let's calculate what happens with a couple
    of examples.  First, suppose [P'] is [(X <= 5) [X |-> 3]] -- that
    is, more formally, [P'] is the Coq expression

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st 3 ; st),

    which simplifies to

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> 3 ; st)

    and further simplifies to

    fun st =>
      ((X !-> 3 ; st) X) <= 5

    and finally to

    fun st =>
      3 <= 5.

    That is, [P'] is the assertion that [3] is less than or equal to
    [5] (as expected). *)

(** For a more interesting example, suppose [P'] is [(X <= 5) [X |->
    X + 1]].  Formally, [P'] is the Coq expression

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st (X + 1) ; st),

    which simplifies to

    fun st =>
      (X !-> aeval st (X + 1) ; st) X <= 5

    and further simplifies to

    fun st =>
      (aeval st (X + 1)) <= 5.

    That is, [P'] is the assertion that [X + 1] is at most [5].
*)

(** Now, using the substitution operation we've just defined, we can
    give the precise proof rule for assignment:

      ---------------------------- (hoare_asgn)
      {{Q [X |-> a]}} X := a {{Q}}
*)

(** We can prove formally that this rule is indeed valid. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold valid_hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assertion_sub in HQ. assumption.  Qed.

(** Here's a first formal proof using this rule. *)

Example assertion_sub_example :
  {{(X < 5) [X |-> X + 1]}}
    X := X + 1
  {{X < 5}}.
Proof.
  apply hoare_asgn.  Qed.

(** Of course, what we'd probably prefer is to prove this
    simpler triple:

      {{X < 4}} X := X + 1 {{X < 5}}

   We will see how to do so in the next section. *)

(** Complete these Hoare triples by providing an appropriate
    precondition using [exists], then prove then with [apply
    hoare_asgn]. If you find that tactic doesn't suffice, double check
    that you have completed the triple properly. *)
(** **** Exercise: 2 stars, standard, optional (hoare_asgn_examples1) *)
Example hoare_asgn_examples1 :
  exists P,
    {{ P }}
      X := 2 * X
    {{ X <= 10 }}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (hoare_asgn_examples2) *)
Example hoare_asgn_examples2 :
  exists P,
    {{ P }}
      X := 3
    {{ 0 <=  X /\ X <= 5 }}.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (hoare_asgn_wrong)

    The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems puzzling to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:

      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X := a {{ X = a }}

    Give a counterexample showing that this rule is incorrect and use
    it to complete the proof belkow, showing that it is really a
    counterexample.  (Hint: The rule universally quantifies over the
    arithmetic expression [a], and your counterexample needs to
    exhibit an [a] for which the rule doesn't work.) *)

Theorem hoare_asgn_wrong : exists a:aexp,
  ~ {{ True }} X := a {{ X = a }}.
Proof.
  (* FILL IN HERE *) Admitted.
(* FILL IN HERE

    [] *)

(** **** Exercise: 3 stars, advanced (hoare_asgn_fwd)

    By using a _parameter_ [m] (a Coq number) to remember the
    original value of [X] we can define a Hoare rule for assignment
    that does, intuitively, "work forwards" rather than backwards.

       ------------------------------------------ (hoare_asgn_fwd)
       {{fun st => P st /\ st X = m}}
         X := a
       {{fun st => P (X !-> m ; st) /\ st X = aeval (X !-> m ; st) a }}

    Note that we need to write out the postcondition in "desugared"
    form, because it needs to talk about two different states: we use
    the original value of [X] to reconstruct the state [st'] before the
    assignment took place.  (Also note that this rule is more complicated
    than [hoare_asgn]!)

    Prove that this rule is correct. *)

Theorem hoare_asgn_fwd :
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X := a
  {{fun st => P (X !-> m ; st)
           /\ st X = aeval (X !-> m ; st) a }}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced, optional (hoare_asgn_fwd_exists)

    Another way to define a forward rule for assignment is to
    existentially quantify over the previous value of the assigned
    variable.  Prove that it is correct.

      ------------------------------------ (hoare_asgn_fwd_exists)
      {{fun st => P st}}
        X := a
      {{fun st => exists m, P (X !-> m ; st) /\
                     st X = aeval (X !-> m ; st) a }}
*)

Theorem hoare_asgn_fwd_exists :
  forall a P,
  {{fun st => P st}}
    X := a
  {{fun st => exists m, P (X !-> m ; st) /\
                st X = aeval (X !-> m ; st) a }}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Consequence *)

(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need. *)

(** For instance,

      {{(X = 3) [X |-> 3]}} X := 3 {{X = 3}},

    follows directly from the assignment rule, but

      {{True}} X := 3 {{X = 3}}

    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [X |-> 3]] are not
    syntactically equal assertions.

    However, they are logically _equivalent_, so if one triple is
    valid, then the other must certainly be as well.  We can capture
    this observation with the following rule:

                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
*)

(** Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.

                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
*)

(** Here are the formal versions: *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P Q Q' c Hhoare Himp st st' Heval Hpre.
  apply Himp.
  apply Hhoare with (st := st).
  - assumption.
  - assumption.
Qed.

(** For example, we can use the first consequence rule like this:

    {{ True }} ->>
    {{ (X = 1) [X |-> 1] }}
      X := 1
    {{ X = 1 }}

    Or, formally... *)

Example hoare_asgn_example1 :
  {{True}} X := 1 {{X = 1}}.
Proof.
  (* WORKED IN CLASS *)
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update.
    intros st _. simpl. reflexivity.
Qed.

(** We can also use it to prove the example mentioned earlier.

    {{ X < 4 }} ->>
    {{ (X < 5)[X |-> X + 1] }}
      X := X + 1
    {{ X < 5 }}

   Or, formally ... *)

Example assertion_sub_example2 :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_consequence_pre with (P' := (X < 5) [X |-> X + 1]).
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update.
    intros st H. simpl in *. lia.
Qed.

(** Finally, here is a combined rule of consequence that allows us to
    vary both the precondition and the postcondition.

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - apply hoare_consequence_post with (Q' := Q').
    + assumption.
    + assumption.
  - assumption.
Qed.

(* ================================================================= *)
(** ** Automation *)

(** Many of the proofs we have done so far with Hoare triples can be
    streamlined using the automation techniques that we introduced in
    the [Auto] chapter of _Logical Foundations_.

    Recall that the [auto] tactic can be told to [unfold] definitions
    as part of its proof search.  Let's give it that hint for the
    definitions and coercions we're using: *)

Hint Unfold assert_implies assertion_sub t_update : core.
Hint Unfold valid_hoare_triple : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

(** Also recall that [auto] will search for a proof involving [intros]
    and [apply].  By default, the theorems that it will apply include
    any of the local hypotheses, as well as theorems in a core
    database. *)

(** The proof of [hoare_consequence_pre], repeated below, looks
    like an opportune place for such automation, because all it does
    is [unfold], [intros], and [apply].  (It uses [assumption], too,
    but that's just application of a hypothesis.) *)

Theorem hoare_consequence_pre' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

(** Merely using [auto], though, doesn't complete the proof. *)

Theorem hoare_consequence_pre'' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  auto. (* no progress *)
Abort.

(** The problem is the [apply Hhoare with...] part of the proof.  Coq
    isn't able to figure out how to instantiate [st] without some help
    from us.  Recall, though, that there are versions of many tactics
    that will use _existential variables_ to make progress even when
    the regular versions of those tactics would get stuck.

    Here, the [eapply] tactic will introduce an existential variable
    [?st] as a placeholder for [st], and [eassumption] will
    instantiate [?st] with [st] when it discovers [st] in assumption
    [Heval].  By using [eapply] we are essentially telling Coq, "Be
    patient: The missing part is going to be filled in later in the
    proof." *)

Theorem hoare_consequence_pre''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  eapply Hhoare.
  - eassumption.
  - apply Himp. assumption.
Qed.

(** The [eauto] tactic will use [eapply] as part of its proof search.
    So, the entire proof can actually be done in just one line. *)

Theorem hoare_consequence_pre'''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

(** Of course, it's hard to predict that [eauto] suffices here
    without having gone through the original proof of
    [hoare_consequence_pre] to see the tactics it used. But now that
    we know [eauto] worked there, it's a good bet that it will also
    work for [hoare_consequence_post]. *)

Theorem hoare_consequence_post' : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

(** We can also use [eapply] to streamline a
    proof ([hoare_asgn_example1]), that we did earlier as an example
    of using the consequence rule: *)

Example hoare_asgn_example1' :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre. (* no need to state an assertion *)
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update.
    intros st _. simpl. reflexivity.
Qed.

(** The final bullet of that proof also looks like a candidate for
    automation. *)

Example hoare_asgn_example1'' :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto.
Qed.

(** Now we have quite a nice proof script: it simply identifies the
    Hoare rules that need to be used and leaves the remaining
    low-level details up to Coq to figure out. *)

(** By now it might be apparent that the _entire_ proof could be
    automated if we added [hoare_consequence_pre] and [hoare_asgn] to
    the hint database.  We won't do that in this chapter, so that we
    can get a better understanding of when and how the Hoare rules are
    used.  In the next chapter, [Hoare2], we'll dive deeper into
    automating entire proofs of Hoare triples. *)

(** The other example of using consequence that we did earlier,
    [hoare_asgn_example2], requires a little more work to automate.
    We can streamline the first line with [eapply], but we can't just use
    [auto] for the final bullet, since it needs [lia]. *)

Example assertion_sub_example2' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto. (* no progress *)
    unfold "->>", assertion_sub, t_update.
    intros st H. simpl in *. lia.
Qed.

(** Let's introduce our own tactic to handle both that bullet and the
    bullet from example 1: *)

Ltac assertion_auto :=
  try auto;  (* as in example 1, above *)
  try (unfold "->>", assertion_sub, t_update;
       intros; simpl in *; lia). (* as in example 2 *)

Example assertion_sub_example2'' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

Example hoare_asgn_example1''':
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

(** Again, we have quite a nice proof script.  All the low-level
    details of proofs about assertions have been taken care of
    automatically. Of course, [assertion_auto] isn't able to prove
    everything we could possibly want to know about assertions --
    there's no magic here! But it's good enough so far. *)

(** **** Exercise: 2 stars, standard (hoare_asgn_examples_2)

    Prove these triples.  Try to make your proof scripts nicely
    automated by following the examples above. *)

Example assertion_sub_ex1' :
  {{ X <= 5 }}
    X := 2 * X
  {{ X <= 10 }}.
Proof.
  (* FILL IN HERE *) Admitted.

Example assertion_sub_ex2' :
  {{ 0 <= 3 /\ 3 <= 5 }}
    X := 3
  {{ 0 <= X /\ X <= 5 }}.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Sequencing + Assignment *)

(** Here's an example of a program involving both sequencing and
    assignment.  Note the use of [hoare_seq] in conjunction with
    [hoare_consequence_pre] and the [eapply] tactic. *)

Example hoare_asgn_example3 : forall (a:aexp) (n:nat),
  {{a = n}}
    X := a;
    skip
  {{X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.

(** Informally, a nice way of displaying a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:

  {{ a = n }}
     X := a
              {{ X = n }};    <--- decoration for Q
     skip
  {{ X = n }}
*)
(** We'll come back to the idea of decorated programs in much more
    detail in the next chapter. *)

(** **** Exercise: 2 stars, standard, especially useful (hoare_asgn_example4)

    Translate this "decorated program" into a formal proof:

                   {{ True }} ->>
                   {{ 1 = 1 }}
    X := 1
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }};
    Y := 2
                   {{ X = 1 /\ Y = 2 }}

   Note the use of "[->>]" decorations, each marking a use of
   [hoare_consequence_pre].

   We've started you off by providing a use of [hoare_seq] that
   explicitly identifies [X = 1] as the intermediate assertion. *)

Example hoare_asgn_example4 :
  {{ True }}
    X := 1;
    Y := 2
  {{ X = 1 /\ Y = 2 }}.
Proof.
  eapply hoare_seq with (Q := (X = 1)%assertion).
  (* The annotation [%assertion] is needed to help Coq parse correctly. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (swap_exercise)

    Write an Imp program [c] that swaps the values of [X] and [Y] and
    show that it satisfies the following specification:

      {{X <= Y}} c {{Y <= X}}

    Your proof should not need to use [unfold valid_hoare_triple].

    Hints:
       - Remember that Imp commands need to be enclosed in <{...}>
         brackets.
       - Remember that the assignment rule works best when it's
         applied "back to front," from the postcondition to the
         precondition.  So your proof will want to start at the end
         and work back to the beginning of your program.
       - Remember that [eapply] is your friend.)  *)

Definition swap_program : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem swap_exercise :
  {{X <= Y}}
    swap_program
  {{Y <= X}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced (invalid_triple)

    Show that

    {{ a = n }} X := 3; Y := a {{ Y = n }}

    is not a valid Hoare triple for some choices of [a] and [n].

    Conceptual hint: Invent a particular [a] and [n] for which the
    triple in invalid, then use those to complete the proof.

    Technical hint: Hypothesis [H] below begins [forall a n, ...].
    You'll want to instantiate that with the particular [a] and [n]
    you've invented.  You can do that with [assert] and [apply], but
    you may remember (from [Tactics.v] in Logical Foundations)
    that Coq offers an even easier tactic: [specialize].  If you write

       specialize H with (a := your_a) (n := your_n)

    the hypothesis will be instantiated on [your_a] and [your_n].

    Having chosen your [a] and [n], proceed as follows:
     - Use the (assumed) validity of the given hoare triple to derive
       a state [st'] in which [Y] has some value [y1]
     - Use the evaluation rules ([E_Seq] and [E_Asgn]) to show that
       [Y] has a _different_ value [y2] in the same final state [st']
     - Since [y1] and [y2] are both equal to [st' Y], they are equal
       to each other. But we chose them to be different, so this is a
       contradiction, which finishes the proof.
 *)

Theorem invalid_triple : ~ forall (a : aexp) (n : nat),
    {{ a = n }}
      X := 3; Y := a
    {{ Y = n }}.
Proof.
  unfold valid_hoare_triple.
  intros H.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?

    Certainly, if the same assertion [Q] holds after executing
    either of the branches, then it holds after the whole conditional.
    So we might be tempted to write:

              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      ---------------------------------
      {{P}} if b then c1 else c2 {{Q}}
*)

(** However, this is rather weak. For example, using this rule,
   we cannot show

     {{ True }}
       if X = 0
         then Y := 2
         else Y := X + 1
       end
     {{ X <= Y }}

   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches. *)

(** Fortunately, we can say something more precise.  In the
    "then" branch, we know that the boolean expression [b] evaluates to
    [true], and in the "else" branch, we know it evaluates to [false].
    Making this information available in the premises of the rule gives
    us more information to work with when reasoning about the behavior
    of [c1] and [c2] (i.e., the reasons why they establish the
    postcondition [Q]).

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}
*)

(** To interpret this rule formally, we need to do a little work.
    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression -- i.e., it
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassertion b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)

Definition bassertion b : Assertion :=
  fun st => (beval st b = true).

Coercion bassertion : bexp >-> Assertion.

Arguments bassertion /.

(** A useful fact about [bassertion]: *)

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassertion b) st).
Proof. congruence. Qed.

Hint Resolve bexp_eval_false : core.

(** We mentioned the [congruence] tactic in passing in
    [Auto] when building the [find_rwd] tactic.  Like
    [find_rwd], [congruence] is able to automatically find that both
    [beval st b = false] and [beval st b = true] are being assumed,
    notice the contradiction, and [discriminate] to complete the
    proof. *)

(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
(** That is (unwrapping the notations):

      Theorem hoare_if : forall P Q b c1 c2,
        {{fun st => P st /\ bassertion b st}} c1 {{Q}} ->
        {{fun st => P st /\ ~ (bassertion b st)}} c2 {{Q}} ->
        {{P}} if b then c1 else c2 end {{Q}}.
*)
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Example *)

(** Here is a formal proof that the program we used to motivate
    the rule satisfies the specification we gave. *)

Example if_example :
  {{True}}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto. (* no progress *)
      unfold "->>", assertion_sub, t_update, bassertion.
      simpl. intros st [_ H]. apply eqb_eq in H.
      rewrite H. lia.
  - (* Else *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.

(** As we did earlier, it would be nice to eliminate all the low-level
    proof script that isn't about the Hoare rules.  Unfortunately, the
    [assertion_auto] tactic we wrote wasn't quite up to the job.  Looking
    at the proof of [if_example], we can see why.  We had to unfold a
    definition ([bassertion]) and use a theorem ([eqb_eq]) that we didn't
    need in earlier proofs.  So, let's add those into our tactic, and
    clean it up a little in the process. *)

Ltac assertion_auto' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.

(** Now the proof is quite streamlined. *)

Example if_example'' :
  {{True}}
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto'.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto'.
Qed.

(** We can even shorten it a little bit more. *)

Example if_example''' :
  {{True}}
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if; eapply hoare_consequence_pre;
    try apply hoare_asgn; try assertion_auto'.
Qed.

(** For later proofs, it will help to extend [assertion_auto'] to handle
    inequalities, too. *)

Ltac assertion_auto'' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *;  (* for inequalities *)
  auto; try lia.

(** **** Exercise: 2 stars, standard (if_minus_plus)

    Prove the theorem below using [hoare_if].  Do not use [unfold
    valid_hoare_triple].  The [assertion_auto''] tactic we just
    defined may be useful. *)

Theorem if_minus_plus :
  {{True}}
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  {{Y = X + Z}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Exercise: One-sided conditionals *)

(** In this exercise we consider extending Imp with "one-sided
    conditionals" of the form [if1 b then c end]. Here [b] is a boolean
    expression, and [c] is a command. If [b] evaluates to [true], then
    command [c] is evaluated. If [b] evaluates to [false], then [if1 b
    then c end] does nothing.

    We recommend that you complete this exercise before attempting the
    ones that follow, as it should help solidify your understanding of
    the material. *)

(** The first step is to extend the syntax of commands and introduce
    the usual notations.  (We've done this for you.  We use a separate
    module to prevent polluting the global name space.) *)

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'if1' x 'then' y 'end'" :=
         (CIf1 x y)
             (in custom com at level 0, x custom com at level 99).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

(** **** Exercise: 2 stars, standard, especially useful (if1_ceval) *)

(** Add two new evaluation rules to relation [ceval], below, for
    [if1]. Let the rules for [if] guide you.*)

Reserved Notation "st '=[' c ']=>'' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
(* FILL IN HERE *)

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

(** The following unit tests should be provable simply by [eauto] if
    you have defined the rules for [if1] correctly. *)

Example if1true_test :
  empty_st =[ if1 X = 0 then X := 1 end ]=> (X !-> 1).
Proof. (* FILL IN HERE *) Admitted.

Example if1false_test :
  (X !-> 2) =[ if1 X = 0 then X := 1 end ]=> (X !-> 2).
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(** Now we have to repeat the definition and notation of Hoare triples,
    so that they will use the updated [com] type. *)

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
       st =[ c ]=> st' ->
       P st  ->
       Q st'.

Hint Unfold valid_hoare_triple : core.

Notation "{{ P }}  c  {{ Q }}" := (valid_hoare_triple P c Q)
                                  (at level 90, c custom com at level 99)
                                  : hoare_spec_scope.

(** **** Exercise: 2 stars, standard (hoare_if1) *)

(** Invent a Hoare logic proof rule for [if1].  State and prove a
    theorem named [hoare_if1] that shows the validity of your rule.
    Use [hoare_if] as a guide. Try to invent a rule that is
    _complete_, meaning it can be used to prove the correctness of as
    many one-sided conditionals as possible.  Also try to keep your
    rule _compositional_, meaning that any Imp command that appears
    in a premise should syntactically be a part of the command
    in the conclusion.

    Hint: if you encounter difficulty getting Coq to parse part of
    your rule as an assertion, try manually indicating that it should
    be in the assertion scope.  For example, if you want [e] to be
    parsed as an assertion, write it as [(e)%assertion]. *)

(* FILL IN HERE *)

(** For full credit, prove formally ([hoare_if1_good]) that your rule is
    precise enough to show the following Hoare triple is valid:

  {{ X + Y = Z }}
    if1 Y <> 0 then
      X := X + Y
    end
  {{ X = Z }}
*)
(* Do not modify the following line: *)
Definition manual_grade_for_hoare_if1 : option (nat*string) := None.
(** [] *)

(** Before the next exercise, we need to restate the Hoare rules of
    consequence (for preconditions) and assignment for the new [com]
    type. *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X := a) {{Q}}.
Proof.
  intros Q X a st st' Heval HQ.
  inversion Heval; subst.
  auto.
Qed.

(** **** Exercise: 2 stars, standard (hoare_if1_good) *)

(** Use your [if1] rule to prove the following (valid) Hoare triple.

    Hint: [assertion_auto''] will once again get you most but not all
    the way to a completely automated proof.  You can finish manually,
    or tweak the tactic further.

    Hint: If you see a message like [Unable to unify "Imp.ceval
    Imp.CSkip st st'" with...], it probably means you are using a
    definition or theorem [e.g., hoare_skip] from above this exercise
    without re-proving it for the new version of Imp with if1. *)

Lemma hoare_if1_good :
  {{ X + Y = Z }}
    if1 Y <> 0 then
      X := X + Y
    end
  {{ X = Z }}.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

End If1.

(* ================================================================= *)
(** ** While Loops *)

(** The Hoare rule for [while] loops is based on the idea of a
    _command invariant_ (or just _invariant_): an assertion whose
    truth is guaranteed after executing a command, assuming it is true
    before.

    That is, an assertion [P] is a command invariant of [c] if

      {{P}} c {{P}}

    holds.  Note that the command invariant might temporarily become
    false in the middle of executing [c], but by the end of [c] it
    must be restored. *)

(**  As a first attempt at a [while] rule, we could try:

             {{P}} c {{P}}
      ---------------------------
      {{P} while b do c end {{P}}

    That rule is valid: if [P] is a command invariant of [c], as the premise
    requires, then no matter how many times the loop body executes,
    [P] is going to be true when the loop finally finishes.

    But the rule also omits two crucial pieces of information.  First,
    the loop terminates when [b] becomes false.  So we can strengthen
    the postcondition in the conclusion:

              {{P}} c {{P}}
      ---------------------------------
      {{P} while b do c end {{P /\ ~b}}

    Second, the loop body will be executed only if [b] is true.  So we
    can also strengthen the precondition in the premise:

            {{P /\ b}} c {{P}}
      --------------------------------- (hoare_while)
      {{P} while b do c end {{P /\ ~b}}
*)

(** That is the Hoare [while] rule.  Note how it combines
    aspects of [skip] and conditionals:

    - If the loop body executes zero times, the rule is like [skip] in
      that the precondition survives to become (part of) the
      postcondition.

    - Like a conditional, we can assume guard [b] holds on entry to
      the subcommand.
*)

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' Heval HP.
  (* We proceed by induction on [Heval], because, in the "keep looping" case,
     its hypotheses talk about the whole loop instead of just [c]. The
     [remember] is used to keep the original command in the hypotheses;
     otherwise, it would be lost in the [induction]. By using [inversion]
     we clear away all the cases except those involving [while]. *)
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval;
    try (inversion Horig; subst; clear Horig);
    eauto.
Qed.

(** We call [P] a _loop invariant_ of [while b do c end] if

      {{P /\ b}} c {{P}}

    is a valid Hoare triple.

    This means that [P] will be true at the end of the loop body
    whenever the loop body executes. If [P] contradicts [b], this
    holds trivially since the precondition is false.

    For instance, [X = 0] is a loop invariant of

      while X = 2 do X := 1 end

    since the program will never enter the loop. *)

(** The program

    while Y > 10 do Y := Y - 1; Z := Z + 1 end

    admits an interesting loop invariant:

    X = Y + Z

    Note that this doesn't contradict the loop guard but neither
    is it a command invariant of

    Y := Y - 1; Z := Z + 1

    since, if X = 5,
    Y = 0 and Z = 5, running the command will set Y + Z to 6. The
    loop guard [Y > 10] guarantees that this will not be the case.
    We will see many such loop invariants in the following chapter.
*)

Example while_example :
  {{X <= 3}}
    while (X <= 2) do
      X := X + 1
    end
  {{X = 3}}.
Proof.
  eapply hoare_consequence_post.
  - apply hoare_while.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - assertion_auto''.
Qed.

(** If the loop never terminates, any postcondition will work. *)

Theorem always_loop_hoare : forall Q,
  {{True}} while true do skip end {{Q}}.
Proof.
  intros Q.
  eapply hoare_consequence_post.
  - apply hoare_while. apply hoare_post_true. auto.
  - simpl. intros st [Hinv Hguard]. congruence.
Qed.

(** Of course, this result is not surprising if we remember that
    the definition of [valid_hoare_triple] asserts that the postcondition
    must hold _only_ when the command terminates.  If the command
    doesn't terminate, we can prove anything we like about the
    post-condition.

    Hoare rules that specify what happens _if_ commands terminate,
    without proving that they do, are said to describe a logic of
    _partial_ correctness.  It is also possible to give Hoare rules
    for _total_ correctness, which additionally specifies that
    commands must terminate. Total correctness is out of the scope of
    this textbook. *)

(* ----------------------------------------------------------------- *)
(** *** Exercise: [REPEAT] *)

(** **** Exercise: 4 stars, advanced, optional (hoare_repeat)

    In this exercise, we'll add a new command to our language of
    commands: [REPEAT] c [until] b [end]. You will write the
    evaluation rule for [REPEAT] and add a new Hoare rule to the
    language for programs involving it.  (You may recall that the
    evaluation rule is given in an example in the [Auto] chapter.
    Try to figure it out yourself here rather than peeking.) *)

Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] behaves like [while], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Notation "'repeat' e1 'until' b2 'end'" :=
          (CRepeat e1 b2)
              (in custom com at level 0,
               e1 custom com at level 99, b2 custom com at level 99).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [while] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true. *)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
(* FILL IN HERE *)

where "st '=[' c ']=>' st'" := (ceval st c st').

(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)

Definition valid_hoare_triple (P : Assertion) (c : com) (Q : Assertion)
                        : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (valid_hoare_triple P c Q) (at level 90, c custom com at level 99).

(** To make sure you've got the evaluation rules for [repeat] right,
    prove that [ex1_repeat] evaluates correctly. *)

Definition ex1_repeat :=
  <{ repeat
       X := 1;
       Y := Y + 1
     until (X = 1) end }>.

Theorem ex1_repeat_works :
  empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now state and prove a theorem, [hoare_repeat], that expresses an
    appropriate proof rule for [repeat] commands.  Use [hoare_while]
    as a model, and try to make your rule as precise as possible. *)

(* FILL IN HERE *)

(** For full credit, make sure (informally) that your rule can be used
    to prove the following valid Hoare triple:

  {{ X > 0 }}
    repeat
      Y := X;
      X := X - 1
    until X = 0 end
  {{ X = 0 /\ Y > 0 }}
*)

End RepeatExercise.

(* Do not modify the following line: *)
Definition manual_grade_for_hoare_repeat : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Summary *)

(** So far, we've introduced Hoare Logic as a tool for reasoning about
    Imp programs.

    The rules of Hoare Logic are:

             --------------------------- (hoare_asgn)
             {{Q [X |-> a]}} X:=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} skip {{ P }}

               {{ P }} c1 {{ Q }}
               {{ Q }} c2 {{ R }}
              ----------------------  (hoare_seq)
              {{ P }} c1;c2 {{ R }}

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} while b do c end {{P /\ ~ b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

(** Our task in this chapter has been to _define_ the rules of Hoare
    logic, and prove that the definitions are sound.  Having done so,
    we can now work _within_ Hoare logic to prove that particular
    programs satisfy particular Hoare triples.  In the next chapter,
    we'll see how Hoare logic is can be used to prove that more
    interesting programs satisfy interesting specifications of their
    behavior.

    Crucially, we will do so without ever again [unfold]ing the
    definition of Hoare triples -- i.e., we will take the rules of
    Hoare logic as a closed world for reasoning about programs. *)

(* ################################################################# *)
(** * Additional Exercises *)

(* ================================================================= *)
(** ** Havoc *)

(** In this exercise, we will derive proof rules for a [HAVOC]
    command, which is similar to the nondeterministic [any] expression
    from the the [Imp] chapter.

    First, we enclose this work in a separate module, and recall the
    syntax and big-step semantics of Himp commands. *)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.

Notation "'havoc' l" := (CHavoc l)
                          (in custom com at level 60, l constr at level 0).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_Havoc : forall st x n,
      st =[ havoc x ]=> (x !-> n ; st)

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

(** The definition of Hoare triples is exactly as before. *)

Definition valid_hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Hint Unfold valid_hoare_triple : core.

Notation "{{ P }}  c  {{ Q }}" := (valid_hoare_triple P c Q)
                                  (at level 90, c custom com at level 99)
                                  : hoare_spec_scope.

(** And the precondition consequence rule is exactly as before. *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof. eauto. Qed.

(** **** Exercise: 3 stars, advanced (hoare_havoc) *)

(** Complete the Hoare rule for [HAVOC] commands below by defining
    [havoc_pre], and prove that the resulting rule is correct. *)

Definition havoc_pre (X : string) (Q : Assertion) (st : total_map nat) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem hoare_havoc : forall (Q : Assertion) (X : string),
  {{ havoc_pre X Q }} havoc X {{ Q }}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (havoc_post)

    Complete the following proof without changing any of the provided
    commands. If you find that it can't be completed, your definition of
    [havoc_pre] is probably too strong. Find a way to relax it so that
    [havoc_post] can be proved.

    Hint: the [assertion_auto] tactics we've built won't help you here.
    You need to proceed manually. *)

Theorem havoc_post : forall (P : Assertion) (X : string),
  {{ P }} havoc X {{ fun st => exists (n:nat), P [X |-> n] st }}.
Proof.
  intros P X. eapply hoare_consequence_pre.
  - apply hoare_havoc.
  - (* FILL IN HERE *) Admitted.

(** [] *)

End Himp.

(* ================================================================= *)
(** ** Assert and Assume *)

(** **** Exercise: 4 stars, standard (assert_vs_assume)

    In this exercise, we will extend IMP with two commands, [assert]
    and [assume]. Both commands are ways to indicate that a certain
    assertion should hold any time this part of the program is
    reached. However they differ as follows:

    - If an [assert] statement fails, it causes the program to go into
      an error state and exit.

    - If an [assume] statement fails, the program fails to evaluate at
      all. In other words, the program gets stuck and has no final
      state.

    The new set of commands is: *)

Module HoareAssertAssume.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAssert : bexp -> com
  | CAssume : bexp -> com.

Notation "'assert' l" := (CAssert l)
                           (in custom com at level 8, l custom com at level 0).
Notation "'assume' l" := (CAssume l)
                          (in custom com at level 8, l custom com at level 0).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

(** To define the behavior of [assert] and [assume], we need to add
    notation for an error, which indicates that an assertion has
    failed. We modify the [ceval] relation, therefore, so that
    it relates a start state to either an end state or to [error].
    The [result] type indicates the end value of a program,
    either a state or an error: *)

Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.

(** Now we are ready to give you the ceval relation for the new language. *)

Inductive ceval : com -> state -> result -> Prop :=
  (* Old rules, several modified *)
  | E_Skip : forall st,
      st =[ skip ]=> RNormal st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st  =[ c ]=> RNormal st' ->
      st' =[ while b do c end ]=> r ->
      st  =[ while b do c end ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ while b do c end ]=> RError
  (* Rules for Assert and Assume *)
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ assert b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ assert b ]=> RError
  | E_Assume : forall st b,
      beval st b = true ->
      st =[ assume b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).

(** We redefine hoare triples: Now, [{{P}} c {{Q}}] means that,
    whenever [c] is started in a state satisfying [P], and terminates
    with result [r], then [r] is not an error and the state of [r]
    satisfies [Q]. *)

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st r,
     st =[ c ]=> r  -> P st  ->
     (exists st', r = RNormal st' /\ Q st').

Notation "{{ P }}  c  {{ Q }}" :=
  (valid_hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

(** To test your understanding of this modification, give an example
    precondition and postcondition that are satisfied by the [assume]
    statement but not by the [assert] statement. *)

Theorem assert_assume_differ : exists (P:Assertion) b (Q:Assertion),
       ({{P}} assume b {{Q}})
  /\ ~ ({{P}} assert b {{Q}}).
(* FILL IN HERE *) Admitted.

(** Then prove that any triple for an [assert] also works when
    [assert] is replaced by [assume]. *)

Theorem assert_implies_assume : forall P b Q,
     ({{P}} assert b {{Q}})
  -> ({{P}} assume b {{Q}}).
Proof.
(* FILL IN HERE *) Admitted.

(** Next, here are proofs for the old hoare rules adapted to the new
    semantics.  You don't need to do anything with these. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold valid_hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  exists (X !-> aeval st a ; st). split; try reflexivity.
  assumption. Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  - assumption.
  - apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st r Hc HP.
  unfold valid_hoare_triple in Hhoare.
  assert (exists st', r = RNormal st' /\ Q' st').
  { apply (Hhoare st); assumption. }
  destruct H as [st' [Hr HQ'] ].
  exists st'. split; try assumption.
  apply Himp. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st r H12 Pre.
  inversion H12; subst.
  - eapply H1.
    + apply H6.
    + apply H2 in H3. apply H3 in Pre.
        destruct Pre as [st'0 [Heq HQ] ].
        inversion Heq; subst. assumption.
  - (* Find contradictory assumption *)
     apply H2 in H5. apply H5 in Pre.
     destruct Pre as [st' [C _] ].
     inversion C.
Qed.

(** Here are the other proof rules (sanity check) *)
Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  eexists. split.
  - reflexivity.
  - assumption.
Qed.

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b}} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
    + assumption.
    + split; assumption.
  - (* b is false *)
    apply (HFalse st st').
    + assumption.
    + split.
      * assumption.
      * apply bexp_eval_false. assumption.
Qed.

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{ P /\ ~b}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember <{while b do c end}> as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    eexists. split.
    + reflexivity.
    + split; try assumption.
      apply bexp_eval_false. assumption.
  - (* E_WhileTrueNormal *)
    clear IHHe1.
    apply IHHe2.
    + reflexivity.
    + clear IHHe2 He2 r.
      unfold valid_hoare_triple in Hhoare.
      apply Hhoare in He1.
      * destruct He1 as [st1 [Heq Hst1] ].
        inversion Heq; subst.
        assumption.
      * split; assumption.
  - (* E_WhileTrueError *)
     exfalso. clear IHHe.
     unfold valid_hoare_triple in Hhoare.
     apply Hhoare in He.
     + destruct He as [st' [C _] ]. inversion C.
     + split; assumption.
Qed.

(** Finally, state Hoare rules for [assert] and [assume] and use them
    to prove a simple program correct.  Name your rules [hoare_assert]
    and [hoare_assume]. *)

(* FILL IN HERE *)

(** Use your rules to prove the following triple. *)

Example assert_assume_example:
  {{True}}
    assume (X = 1);
    X := X + 1;
    assert (X = 2)
  {{True}}.
Proof.
(* FILL IN HERE *) Admitted.

End HoareAssertAssume.
(** [] *)



(* 2024-01-03 15:04 *)
