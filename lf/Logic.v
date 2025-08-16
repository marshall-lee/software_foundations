(** * Logic: Logic in Coq *)

Set Warnings "-notation-overridden,-parsing".
Set Warnings "-deprecated-hint-without-locality".
Require Nat.
From LF Require Export Tactics.

(** We have now seen many examples of factual claims (_propositions_)
    and ways of presenting evidence of their truth (_proofs_).  In
    particular, we have worked extensively with equality
    propositions ([e1 = e2]), implications ([P -> Q]), and quantified
    propositions ([forall x, P]).  In this chapter, we will see how
    Coq can be used to carry out other familiar forms of logical
    reasoning.

    Before diving into details, we should talk a bit about the status of
    mathematical statements in Coq.  Recall that Coq is a _typed_
    language, which means that every sensible expression has an
    associated type.  Logical claims are no exception: any statement
    we might try to prove in Coq has a type, namely [Prop], the type
    of _propositions_.  We can see this with the [Check] command: *)

Check (forall n m : nat, n + m = m + n) : Prop.

(** Note that _all_ syntactically well-formed propositions have type
    [Prop] in Coq, regardless of whether they are true or not.

    Simply _being_ a proposition is one thing; being _provable_ is
    a different thing! *)

Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.

(** Indeed, propositions don't just have types -- they are
    _first-class_ entities that can be manipulated in all the same ways as
    any of the other things in Coq's world. *)

(** So far, we've seen one primary place where propositions can appear:
    in [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But propositions can be used in other ways.  For example, we
    can give a name to a proposition using a [Definition], just as we
    give names to other kinds of expressions. *)

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity.  Qed.

(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. *)

(** For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three: *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

(** In Coq, functions that return propositions are said to define
    _properties_ of their arguments.

    For instance, here's a (polymorphic) property defining the
    familiar notion of an _injective function_. *)

Definition injective {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros x y H. injection H as H1. apply H1.
Qed.

(** The familiar equality operator [=] is a (binary) function that returns
    a [Prop].

    The expression [n = m] is syntactic sugar for [eq n m] (defined in
    Coq's standard library using the [Notation] mechanism).

    Because [eq] can be used with elements of any type, it is also
    polymorphic: *)

Check @eq : forall A : Type, A -> A -> Prop.

(** (Notice that we wrote [@eq] instead of [eq]: The type
    argument [A] to [eq] is declared as implicit, and we need to turn
    off the inference of this implicit argument to see the full type
    of [eq].) *)

(* ################################################################# *)
(** * Logical Connectives *)

(* ================================================================= *)
(** ** Conjunction *)

(** The _conjunction_, or _logical and_, of propositions [A] and [B] is
    written [A /\ B]; it represents the claim that both [A] and [B] are
    true. *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** To prove a conjunction, use the [split] tactic.  This will generate
    two subgoals, one for each part of the statement: *)

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

(** For any propositions [A] and [B], if we assume that [A] is true and
    that [B] is true, we can conclude that [A /\ B] is also true.  The Coq
    library provides a function [conj] that does this. *)

Check @conj : forall A B : Prop, A -> B -> A /\ B.

(** Since applying a theorem with hypotheses to some goal has the effect of
    generating as many subgoals as there are hypotheses for that theorem,
    we can apply [conj] to achieve the same effect as [split]. *)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (plus_is_O) *)

Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - destruct m in H.
    + rewrite <- plus_n_O in H. apply H.
    + rewrite <- plus_n_Sm in H. discriminate H.
  - destruct n in H.
    + rewrite -> plus_n_O in H. apply H.
    + simpl in H. discriminate H.
Qed.
(** [] *)

(** So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to help prove
    something else -- we employ the [destruct] tactic. *)

(** When the current proof context contains a hypothesis [H] of the
    form [A /\ B], writing [destruct H as [HA HB]] will remove [H]
    from the context and replace it with two new hypotheses: [HA],
    stating that [A] is true, and [HB], stating that [B] is true.  *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** As usual, we can also destruct [H] right when we introduce it,
    instead of introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** You may wonder why we bothered packing the two hypotheses [n = 0] and
    [m = 0] into a single conjunction, since we could also have stated the
    theorem with two separate premises: *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** For this specific theorem, both formulations are fine.  But
    it's important to understand how to work with conjunctive
    hypotheses because conjunctions often arise from intermediate
    steps in proofs, especially in larger developments.  Here's a
    simple example: *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  apply plus_is_O in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(** Another common situation is that we know [A /\ B] but in some context
    we need just [A] or just [B].  In such cases we can do a
    [destruct] (possibly as part of an [intros]) and use an underscore
    pattern [_] to indicate that the unneeded conjunct should just be
    thrown away. *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP.  Qed.

(** **** Exercise: 1 star, standard, optional (proj2) *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [_ HQ].
  apply HQ.
Qed.
(** [] *)

(** Finally, we sometimes need to rearrange the order of conjunctions
    and/or the grouping of multi-way conjunctions. We can see this
    at work in the proofs of the following commutativity and
    associativity theorems *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.  Qed.

(** **** Exercise: 1 star, standard (and_assoc)

    (In the following proof of associativity, notice how the _nested_
    [intros] pattern breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP : P], [HQ : Q], and [HR : R].  Finish the proof.) *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  + split. apply HP. apply HQ.
  + apply HR.
Qed.
(** [] *)

(** Finally, the infix notation [/\] is actually just syntactic sugar for
    [and A B].  That is, [and] is a Coq operator that takes two
    propositions as arguments and yields a proposition. *)

Check and : Prop -> Prop -> Prop.

(* ================================================================= *)
(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_,
    of two propositions: [A \/ B] is true when either [A] or [B] is.
    (This infix notation stands for [or A B], where
    [or : Prop -> Prop -> Prop].) *)

(** To use a disjunctive hypothesis in a proof, we proceed by case
    analysis -- which, as with other data types like [nat], can be done
    explicitly with [destruct] or implicitly with an [intros]
    pattern: *)

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** We can see in this example that, when we perform case analysis on a
    disjunction [A \/ B], we must separately discharge two proof
    obligations, each showing that the conclusion holds under a different
    assumption -- [A] in the first subgoal and [B] in the second.

    The case analysis pattern [[Hn | Hm]] allows
    us to name the hypotheses that are generated for the subgoals. *)

(** Conversely, to show that a disjunction holds, it suffices to show that
    one of its sides holds. This can be done via the tactics [left] and
    [right].  As their names imply, the first one requires proving the left
    side of the disjunction, while the second requires proving the right
    side.  Here is a trivial use... *)

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** ... and here is a slightly more interesting example requiring both
    [left] and [right]: *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (mult_is_O) *)
Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  destruct n.
  - left. reflexivity.
  - right. destruct m.
    + reflexivity.
    + discriminate H.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (or_commut) *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Falsehood and Negation

    Up to this point, we have mostly been concerned with proving "positive"
    statements -- addition is commutative, appending lists is associative,
    etc.  Of course, we are sometimes also interested in negative results,
    demonstrating that some given proposition is _not_ true. Such
    statements are expressed with the logical negation operator [~]. *)

(** To see how negation works, recall the _principle of explosion_
    from the [Tactics] chapter, which asserts that, if we assume a
    contradiction, then any other proposition can be derived.

    Following this intuition, we could define [~ P] ("not [P]") as
    [forall Q, P -> Q]. *)

(** Coq actually makes a slightly different (but equivalent) choice,
    defining [~ P] as [P -> False], where [False] is a specific
    un-provable proposition defined in the standard library. *)

Module NotPlayground.

Definition not (P:Prop) := P -> False.

Check not : Prop -> Prop.

Notation "~ x" := (not x) : type_scope.

End NotPlayground.

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we can get [False] into the context,
    we can use [destruct] on it to complete any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)

(** **** Exercise: 2 stars, standard, optional (not_implies_our_not)

    Show that Coq's definition of negation implies the intuitive one
    mentioned above.

    Hint: while getting accustomed to Coq's definition of [not], you might
    find it helpful to [unfold not] near the beginning of proofs. *)

Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P HNP Q contra.
  unfold not in HNP.
  apply HNP in contra. destruct contra.
Qed.
(** [] *)

(** Inequality is a very common form of negated statement, so there is a
    special notation for it:
*)
Notation "x <> y" := (~(x = y)) : type_scope.

(** For example: *)

Theorem zero_not_one : 0 <> 1.
Proof.
  (** The proposition [0 <> 1] is exactly the same as
      [~(0 = 1)] -- that is, [not (0 = 1)] -- which unfolds to
      [(0 = 1) -> False]. (We use [unfold not] explicitly here,
      to illustrate that point, but generally it can be omitted.) *)
  unfold not.
  (** To prove an inequality, we may assume the opposite
      equality... *)
  intros contra.
  (** ... and deduce a contradiction from it. Here, the
      equality [O = S O] contradicts the disjointness of
      constructors [O] and [S], so [discriminate] takes care
      of it. *)
  discriminate contra.
Qed.

(** It takes a little practice to get used to working with negation in Coq.
    Even though _you_ can see perfectly well why a statement involving
    negation is true, it can be a little tricky at first to see how to make
    Coq understand it!

    Here are proofs of a few familiar facts to help get you warmed up. *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNP]. unfold not in HNP.
  apply HNP in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, advanced (double_neg_informal)

    Write an _informal_ proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_double_neg_informal : option (nat*string) := None.
(** [] *)

(** **** Exercise: 1 star, standard, especially useful (contrapositive) *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ HQ HP.
  unfold not in HQ. apply HPQ in HP. apply HQ in HP. apply HP.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P H.
  apply contradiction_implies_anything with (Q:=False) in H.
  apply H.
Qed.
(** [] *)

(** **** Exercise: 1 star, advanced (not_PNP_informal)

    Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_not_PNP_informal : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (de_morgan_not_or)

    _De Morgan's Laws_, named for Augustus De Morgan, describe how
    negation interacts with conjunction and disjunction.  The
    following law says that "the negation of a disjunction is the
    conjunction of the negations." There is a dual law
    [de_morgan_not_and_not] to which we will return at the end of this
    chapter. *)
Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q HPQ.
  unfold not in HPQ.
  split.
  - intros HP. apply or_intro_l  with (B:=Q) in HP. apply HPQ. apply HP.
  - intros HQ. apply or_intro_l  with (B:=P) in HQ. apply or_commut in HQ. apply HPQ. apply HQ.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (not_S_inverse_pred)

    Since we are working with natural numbers, we can disprove that
    [S] and [pred] are inverses of each other: *)
Lemma not_S_pred_n : ~(forall n : nat, S (pred n) = n).
Proof.
  intros H.
  specialize H with (n := 0) as contra. discriminate.
Qed.
(** [] *)

(** Since inequality involves a negation, it also requires a little
    practice to be able to work with it fluently.  Here is one useful
    trick.

    If you are trying to prove a goal that is nonsensical (e.g., the
    goal state is [false = true]), apply [ex_falso_quodlibet] to
    change the goal to [False].

    This makes it easier to use assumptions of the form [~P] that may
    be available in the context -- in particular, assumptions of the
    form [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H. destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(** Since reasoning with [ex_falso_quodlibet] is quite common, Coq
    provides a built-in tactic, [exfalso], for applying it. *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.          (* note implicit [destruct b] here *)
  - (* b = true *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

(* ================================================================= *)
(** ** Truth *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    constant [I : True], which is also defined in the standard
    library: *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** Unlike [False], which is used extensively, [True] is used
    relatively rarely, since it is trivial (and therefore
    uninteresting) to prove as a goal, and conversely it provides no
    interesting information when used as a hypothesis. *)

(** However, [True] can be quite useful when defining complex [Prop]s using
    conditionals or as a parameter to higher-order [Prop]s. We'll come back
    to this later.

    For now, let's take a look at how we can use [True] and [False] to
    achieve an effect similar to that of the [discriminate] tactic, without
    literally using [discriminate]. *)

(** Pattern-matching lets us do different things for different
    constructors.  If the result of applying two different
    constructors were hypothetically equal, then we could use [match]
    to convert an unprovable statement (like [False]) to one that is
    provable (like [True]). *)

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros n contra.
  assert (H : disc_fn O). { simpl. apply I. }
  rewrite contra in H. simpl in H. apply H.
Qed.

(** To generalize this to other constructors, we simply have to provide an
    appropriate variant of [disc_fn]. To generalize it to other
    conclusions, we can use [exfalso] to replace them with [False].

    The built-in [discriminate] tactic takes care of all this for us! *)

(** **** Exercise: 2 stars, advanced, optional (nil_is_not_cons) *)

(** Use the same technique as above to show that [nil <> x :: xs].
    Do not use the [discriminate] tactic. *)

Definition list_disc_fn (X : Type) (n: list X) : Prop :=
  match n with
  | nil => True
  | cons _ _ => False
  end.

Theorem nil_is_not_cons : forall X (x : X) (xs : list X), ~ (nil = x :: xs).
Proof.
  intros X x xs contra.
  assert (H : list_disc_fn X nil). { simpl. apply I. }
  rewrite contra in H. simpl in H. apply H.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Logical Equivalence *)

(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is simply the conjunction
    of two implications. *)

Module IffPlayground.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End IffPlayground.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

(** We can also use [apply] with an [<->] in either direction,
    without explicitly thinking about the fact that it is really an
    [and] underneath. *)

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R Hiff H HP. apply H. apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R Hiff H HQ. apply H. apply Hiff. apply HQ.
Qed.

(** **** Exercise: 1 star, standard, optional (iff_properties)

    Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split. intros H. apply H. intros H. apply H.  Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H1 H2. split.
  - intros H. apply proj1 in H1. apply H1 in H. apply proj1 in H2. apply H2 in H. apply H.
  - intros H. apply proj2 in H2. apply H2 in H. apply proj2 in H1. apply H1 in H. apply H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - (* -> *) intros [HP | [HQ HR]].
    + (* P *) split. left. apply HP. left. apply HP.
    + (* Q R *) split.  right. apply HQ. right. apply HR.
  - (* <- *) intros [[HP1 | HQ] [HP2 | HR]].
    + left. apply HP1.
    + left. apply HP1.
    + left. apply HP2.
    + right. apply conj. apply HQ. apply HR.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Setoids and Logical Equivalence *)

(** Some of Coq's tactics treat [iff] statements specially, avoiding some
    low-level proof-state manipulation.  In particular, [rewrite] and
    [reflexivity] can be used with [iff] statements, not just equalities.
    To enable this behavior, we have to import the Coq library that
    supports it: *)

From Coq Require Import Setoids.Setoid.

(** A "setoid" is a set equipped with an equivalence relation -- that
    is, a relation that is reflexive, symmetric, and transitive.  When two
    elements of a set are equivalent according to the relation, [rewrite]
    can be used to replace one by the other.

    We've seen this already with the equality relation [=] in Coq: when
    [x = y], we can use [rewrite] to replace [x] with [y] or vice-versa.

    Similarly, the logical equivalence relation [<->] is reflexive,
    symmetric, and transitive, so we can use it to replace one part of a
    proposition with another: if [P <-> Q], then we can use [rewrite] to
    replace [P] with [Q], or vice-versa. *)

(** Here is a simple example demonstrating how these tactics work with
    [iff].

    First, let's prove a couple of basic iff equivalences. *)

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** We can now use these facts with [rewrite] and [reflexivity] to
    prove a ternary version of the [mult_eq_0] fact above: *)

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Existential Quantification *)

(** Another basic logical connective is _existential quantification_.
    To say that there is some [x] of type [T] such that some property [P]
    holds of [x], we write [exists x : T, P]. As with [forall], the type
    annotation [: T] can be omitted if Coq is able to infer from the
    context what the type of [x] should be. *)

(** To prove a statement of the form [exists x, P], we must show that [P]
    holds for some specific choice for [x], known as the _witness_ of the
    existential.  This is done in two steps: First, we explicitly tell Coq
    which witness [t] we have in mind by invoking the tactic [exists t].
    Then we prove that [P] holds after all occurrences of [x] are replaced
    by [t]. *)

Definition Even x := exists n : nat, x = double n.
Check Even : nat -> Prop.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note the implicit [destruct] here *)
  exists (2 + m).
  apply Hm.  Qed.

(** **** Exercise: 1 star, standard, especially useful (dist_not_exists)

    Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold."  (Hint: [destruct H as [x E]] works on
    existential assumptions!)  *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H [x E].
  unfold not in E. apply E. apply H.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (dist_exists_or)

    Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (leb_plus_exists) *)
Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n+x.
Proof.
  induction n.
  - intros. exists m. reflexivity.
  - destruct m.
    + simpl. discriminate.
    + simpl.
      intros H. apply IHn in H. destruct H as [x0 H].
      rewrite H. exists x0. reflexivity.
Qed.

Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  intros.
  destruct H.
  generalize dependent m.
  induction n.
  - reflexivity.
  - intros.
    destruct m.
    + discriminate H.
    + rewrite add_comm in H. rewrite <- plus_n_Sm in H. injection H as H.
      rewrite add_comm in H.
      apply IHn in H. apply H.
Qed.

(** [] *)

(* ################################################################# *)
(** * Programming with Propositions *)

(** The logical connectives that we have seen provide a rich
    vocabulary for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express the claim that an
    element [x] occurs in a list [l].  Notice that this property has a
    simple recursive structure:

       - If [l] is the empty list, then [x] cannot occur in it, so the
         property "[x] appears in [l]" is simply false.

       - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
         occurs in [l] if it is equal to [x'] or if it occurs in
         [l']. *)

(** We can translate this directly into a straightforward recursive
    function taking an element and a list and returning a proposition (!): *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.
(** (Notice the use of the empty pattern to discharge the last case
    _en passant_.) *)

(** We can also reason about more generic statements involving [In]. *)

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** (Note here how [In] starts out applied to a variable and only
    gets expanded when we do case analysis on this variable.) *)

(** This way of defining propositions recursively is very convenient in
    some cases, less so in others.  In particular, it is subject to Coq's
    usual restrictions regarding the definition of recursive functions,
    e.g., the requirement that they be "obviously terminating."

    In the next chapter, we will see how to define propositions
    _inductively_ -- a different technique with its own strengths and
    limitations. *)

(** **** Exercise: 2 stars, standard (In_map_iff) *)
Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|x l' IHl'].
    + simpl. intros [].
    + simpl. intros [H | H].
      * (* f x' = y *)
        exists x. split. apply H. left. reflexivity.
      * (* In y (map f l') *)
        apply IHl' in H. destruct H as [x' [H1 H2]].
        exists x'. split. apply H1. right. apply H2.
  - intros [x [H1 H2]]. rewrite <- H1. apply In_map. apply H2.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (In_app_iff) *)
Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  + split. right. apply H. intros [H | H]. destruct H. apply H.
  + split.
    - intros [H | H].
      * left. left. apply H.
      * simpl. apply or_assoc. right. apply IH. apply H.
    - intros [H | H].
      * destruct H as [H' | H'].
        left. apply H'.
        right. apply IH. left. apply H'.
      * right. apply IH. right. apply H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (All)

    We noted above that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] says that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  := match l with
     | [] => True
     | (x :: l') => P x /\ All P l'
     end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l.
  split.
  (* -> *)
  {
    induction l as [|x' l'].
    + intros H. apply I.
    + simpl. intros H.
      split.
      * apply H. left. reflexivity.
      * apply IHl'. intros x. intros H'. apply H. right. apply H'.
  }
  (* <- *)
  {
    induction l as [|x' l'].
    + intros [] _ [].
    + simpl. intros [H1 H2] x [H | H].
      - rewrite <- H. apply H1.
      - apply IHl'.
        apply H2. apply H.
  }
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (combine_odd_even)

    Complete the definition of [combine_odd_even] below.  It takes as
    arguments two properties of numbers, [Podd] and [Peven], and it should
    return a property [P] such that [P n] is equivalent to [Podd n] when
    [n] is [odd] and equivalent to [Peven n] otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  := fun n => if odd n then Podd n else Peven n.

(** To test your definition, prove the following facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n Hodd Heven.
  unfold combine_odd_even.
  destruct (odd n).
  + apply Hodd. reflexivity.
  + apply Heven. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Podd Peven n H.
  induction n.
  + discriminate.
  + unfold combine_odd_even in H. unfold combine_odd_even in IHn.
    destruct (odd (S n)).
    * intros []. apply H.
    * discriminate.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros Podd Peven n H.
  induction n.
  + intros H'. unfold combine_odd_even in H. rewrite -> H' in H. apply H.
  + unfold combine_odd_even in H. unfold combine_odd_even in IHn.
    destruct (odd (S n)).
    - discriminate.
    - intros []. apply H.
Qed.
(** [] *)

(* ################################################################# *)
(** * Applying Theorems to Arguments *)

(** One feature that distinguishes Coq from some other popular proof
    assistants (e.g., ACL2 and Isabelle) is that it treats _proofs_ as
    first-class objects.

    There is a great deal to be said about this, but it is not necessary to
    understand it all in order to use Coq.  This section gives just a
    taste, leaving a deeper exploration for the optional chapters
    [ProofObjects] and [IndPrinciples]. *)

(** We have seen that we can use [Check] to ask Coq to check whether
    an expression has a given type: *)

Check plus : nat -> nat -> nat.
Check @rev : forall X, list X -> list X.

(** We can also use it to check the theorem a particular identifier
    refers to: *)

Check add_comm        : forall n m : nat, n + m = m + n.
Check plus_id_example : forall n m : nat, n = m -> n + n = m + m.

(** Coq checks the _statements_ of the [add_comm] and
    [plus_id_example] theorems in the same way that it checks the
    _type_ of any term (e.g., plus). If we leave off the colon and
    type, Coq will print these types for us.

    Why? *)

(** The reason is that the identifier [add_comm] actually refers to a
    _proof object_ -- a logical derivation establishing the truth of the
    statement [forall n m : nat, n + m = m + n].  The type of this object
    is the proposition that it is a proof of.

    The type of an ordinary function tells us what we can do with it.
       - If we have a term of type [nat -> nat -> nat], we can give it two
         [nat]s as arguments and get a [nat] back.

    Similarly, the statement of a theorem tells us what we can use that
    theorem for.
       - If we have a term of type [forall n m, n = m -> n + n = m + m] and we
         provide it two numbers [n] and [m] and a third "argument" of type
         [n = m], we can derive [n + n = m + m]. *)

(** Operationally, this analogy goes even further: by applying a
    theorem as if it were a function, i.e., applying it to values and
    hypotheses with matching types, we can specialize its result
    without having to resort to intermediate assertions.  For example,
    suppose we wanted to prove the following result: *)

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.

(** It appears at first sight that we ought to be able to prove this by
    rewriting with [add_comm] twice to make the two sides match.  The
    problem is that the second [rewrite] will undo the effect of the
    first. *)

Proof.
  intros x y z.
  rewrite add_comm.
  rewrite add_comm.
  (* We are back where we started... *)
Abort.

(** We encountered similar issues back in [Induction], and we saw
    one way to work around them by using [assert] to derive a specialized
    version of [add_comm] that can be used to rewrite exactly where we
    want. *)

Lemma add_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  assert (H : y + z = z + y).
    { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** A more elegant alternative is to apply [add_comm] directly
    to the arguments we want to instantiate it with, in much the same
    way as we apply a polymorphic function to a type argument. *)

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

(** If we really wanted, we could in fact do it for both rewrites. *)

Lemma add_comm3_take4 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite (add_comm x (y + z)).
  rewrite (add_comm y z).
  reflexivity.
Qed.

(** Here's another example of using a trivial theorem about lists like
    a function.

    The theorem says: if a list [l] contains some
    element [x], then [l] must be nonempty. *)

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

(** What makes this interesting is that one quantified variable
    ([x]) does not appear in the conclusion ([l <> []]). *)

(** Intuitively, we should be able to use this theorem to prove the special
    case where [x] is [42]. However, simply invoking the tactic [apply
    in_not_nil] will fail because it cannot infer the value of [x]. *)

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

(** There are several ways to work around this: *)

(** Use [apply ... with ...] *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(** Use [apply ... in ...] *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(** Explicitly apply the lemma to the value for [x]. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(** Explicitly apply the lemma to a hypothesis (causing the values of the
    other parameters to be inferred). *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

(** You can "use a theorem as a function" in this way with almost any
    tactic that can take a theorem's name as an argument.

    Note, also, that theorem application uses the same inference
    mechanisms as function application; thus, it is possible, for
    example, to supply wildcards as arguments to be inferred, or to
    declare some hypotheses to a theorem as implicit by default.
    These features are illustrated in the proof below. (The details of
    how this proof works are not critical -- the goal here is just to
    illustrate applying theorems to arguments.) *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** We will see many more examples in later chapters. *)

(* ################################################################# *)
(** * Working with Decidable Properties *)

(** We've seen two different ways of expressing logical claims in Coq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

    Here are the key differences between [bool] and [Prop]:

                                           bool     Prop
                                           ====     ====
           decidable?                      yes       no
           useable with match?             yes       no
           works with rewrite tactic?      no        yes
*)

(** The crucial difference between the two worlds is _decidability_.
    Every (closed) Coq expression of type [bool] can be simplified in a
    finite number of steps to either [true] or [false] -- i.e., there is a
    terminating mechanical procedure for deciding whether or not it is
    [true].

    This means that, for example, the type [nat -> bool] is inhabited only
    by functions that, given a [nat], always yield either [true] or [false]
    in finite time; and this, in turn, means (by a standard computability
    argument) that there is _no_ function in [nat -> bool] that checks
    whether a given number is the code of a terminating Turing machine.

    By contrast, the type [Prop] includes both decidable and undecidable
    mathematical propositions; in particular, the type [nat -> Prop] does
    contain functions representing properties like "the nth Turing machine
    halts."

    The second row in the table follows directly from this essential
    difference.  To evaluate a pattern match (or conditional) on a boolean,
    we need to know whether the scrutinee evaluates to [true] or [false];
    this only works for [bool], not [Prop].

    The third row highlights another important practical difference:
    equality functions like [eqb_nat] that return a boolean cannot be used
    directly to justify rewriting with the [rewrite] tactic; propositional
    equality is required for this. *)


(** Since [Prop] includes _both_ decidable and undecidable properties, we
    have two options when we want to formalize a property that happens to
    be decidable: we can express it either as a boolean computation or as a
    function into [Prop]. *)

Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

(** ... or that there exists some [k] such that [n = double k]. *)
Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

(** Of course, it would be pretty strange if these two
    characterizations of evenness did not describe the same set of
    natural numbers!  Fortunately, we can prove that they do... *)

(** We first need two helper lemmas. *)
Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** Exercise: 3 stars, standard (even_double_conv) *)
Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  (* Hint: Use the [even_S] lemma from [Induction.v]. *)
  intros n.
  induction n.
  + exists 0. reflexivity.
  + rewrite -> even_S.
    destruct (even n).
    - simpl. destruct IHn as [k']. exists k'. rewrite -> H. reflexivity.
    - simpl. destruct IHn as [k']. exists (S k'). rewrite -> H. simpl. reflexivity.
Qed.
(** [] *)

(** Now the main theorem: *)
Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

(** In view of this theorem, we can say that the boolean computation
    [even n] is _reflected_ in the truth of the proposition
    [exists k, n = double k]. *)

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either
      - (1) that [n =? m] returns [true], or
      - (2) that [n = m].
    Again, these two notions are equivalent: *)

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

(** Even when the boolean and propositional formulations of a claim are
    interchangeable from a purely logical perspective, it can be more
    convenient to use one over the other. *)

(** For example, there is no effective way to _test_ whether or not a
    [Prop] is true in a function definition; thus the
    following definition is rejected: *)

Fail
Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Coq complains that [n = 2] has type [Prop], while it expects an
    element of [bool] (or some other inductive type with two constructors).
    This has to do with the _computational_ nature of Coq's core language,
    which is designed so that every function it can express is computable
    and total.  One reason for this is to allow the extraction of
    executable programs from Coq developments.  As a consequence, [Prop] in
    Coq does _not_ have a universal case analysis operation telling whether
    any given proposition is true or false, since such an operation would
    allow us to write non-computable functions.  *)

(** Rather, we have to state this definition using a boolean equality
    test. *)

Definition is_even_prime n :=
  if n =? 2 then true
  else false.

(** Beyond the fact that non-computable properties are impossible in
    general to phrase as boolean computations, even many _computable_
    properties are easier to express using [Prop] than [bool], since
    recursive function definitions in Coq are subject to significant
    restrictions.  For instance, the next chapter shows how to define the
    property that a regular expression matches a given string using [Prop].
    Doing the same with [bool] would amount to writing a regular expression
    matching algorithm, which would be more complicated, harder to
    understand, and harder to reason about than a simple (non-algorithmic)
    definition of this property.

    Conversely, an important side benefit of stating facts using booleans
    is enabling some proof automation through computation with Coq terms, a
    technique known as _proof by reflection_.

    Consider the following statement: *)

Example even_1000 : Even 1000.

(** The most direct way to prove this is to give the value of [k]
    explicitly. *)

Proof. unfold Even. exists 500. reflexivity. Qed.

(** The proof of the corresponding boolean statement is simpler, because we
    don't have to invent the witness [500]: Coq's computation mechanism
    does it for us! *)

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

(** Now, the useful observation is that, since the two notions are
    equivalent, we can use the boolean formulation to prove the other one
    without mentioning the value 500 explicitly: *)

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Although we haven't gained much in terms of proof-script
    line count in this case, larger proofs can often be made considerably
    simpler by the use of reflection.  As an extreme example, a famous
    Coq proof of the even more famous _4-color theorem_ uses
    reflection to reduce the analysis of hundreds of different cases
    to a boolean computation. *)

(** Another advantage of booleans is that the negation of a "boolean fact"
    is straightforward to state and prove: simply flip the expected boolean
    result. *)

Example not_even_1001 : even 1001 = false.
Proof.
  reflexivity.
Qed.

(** In contrast, propositional negation can be difficult to work with
    directly.

    For example, suppose we state the non-evenness of [1001]
    propositionally: *)

Example not_even_1001' : ~(Even 1001).

(** Proving this directly -- by assuming that there is some [n] such that
    [1001 = double n] and then somehow reasoning to a contradiction --
    would be rather complicated.

    But if we convert it to a claim about the boolean [even] function, we
    can let Coq do the work for us. *)

Proof.
  (* WORKED IN CLASS *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

(** Conversely, there are complementary situations where it can be easier
    to work with propositions rather than booleans.

    In particular, knowing that [(n =? m) = true] is generally of little
    direct help in the middle of a proof involving [n] and [m], but if we
    convert the statement to the equivalent form [n = m], we can rewrite
    with it. *)

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(** We won't discuss reflection any further for the moment, but
    it serves as a good example showing the different strengths of
    booleans and general propositions.

    Being able to cross back and forth between the boolean and
    propositional worlds will often be convenient in later chapters. *)

(** **** Exercise: 2 stars, standard (logical_connectives)

    The following theorems relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. *)

Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2.
  split.
  + intros H. destruct b1.
    - destruct b2.
      split. reflexivity. reflexivity. discriminate H.
    - destruct b2. discriminate H. discriminate H.
  + intros [H1 H2]. rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2.
  split.
  + intros H.
    destruct b1. left. reflexivity. destruct b2. right. reflexivity. discriminate H.
  + intros [H1 | H2]. rewrite H1. reflexivity. rewrite H2. destruct b1. reflexivity. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (eqb_neq)

    The following theorem is an alternate "negative" formulation of
    [eqb_eq] that is more convenient in certain situations.  (We'll see
    examples in later chapters.)  Hint: [not_true_iff_false]. *)

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y.
  split.
  + intros H.
    destruct (x =? y) eqn:H1.
    - discriminate H.
    - intros contra.
      rewrite <- eqb_eq in contra. rewrite H1 in contra. discriminate contra.
  + intros H.
    destruct (x =? y) eqn:H1.
    - rewrite <- eqb_eq in H. apply H in H1. destruct H1.
    - reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (eqb_list)

    Given a boolean operator [eqb] for testing equality of elements of
    some type [A], we can define a function [eqb_list] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [eqb_list] function below.  To make sure that your
    definition is correct, prove the lemma [eqb_list_true_iff]. *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool
  := match l1, l2 with
     | [], [] => true
     | _, [] => false
     | [], _ => false
     | (x1 :: l1'), (x2 :: l2') => eqb x1 x2 && eqb_list eqb l1' l2'
     end.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb.
  intros H.
  split.
  - (* -> *)
    generalize dependent l2.
    induction l1.
    + destruct l2. reflexivity. discriminate.
    + destruct l2. discriminate.
      simpl.
      intros H'. rewrite andb_true_iff in H'. destruct H'.
      rewrite H in H0. apply IHl1 in H1. rewrite H0. rewrite H1. reflexivity.
  - (* <- *)
    generalize dependent l2.
    induction l1.
    + intros l2. intros H2. rewrite <- H2. reflexivity.
    + destruct l2. discriminate.
      simpl. intros H'. injection H' as Hx Hl. rewrite andb_true_iff. split.
      { rewrite Hx. rewrite H. reflexivity. }
      { apply IHl1. apply Hl. }
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (All_forallb)

    Prove the theorem below, which relates [forallb], from the
    exercise [forall_exists_challenge] in chapter [Tactics], to
    the [All] property defined above. *)

(** Copy the definition of [forallb] from your [Tactics] here
    so that this file can be graded on its own. *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
  := match l with
     | [] => true
     | x :: l' => andb (test x) (forallb test l')
     end.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l.
  split.
  - (* -> *)
    induction l as [|x'].
    + simpl. intros []. apply I.
    + simpl. destruct (test x').
      { simpl. intros H. split. reflexivity. apply IHl in H. apply H. }
      { simpl. discriminate. }
  - (* -> *)
    induction l as [|x'].
    + simpl. reflexivity.
    + simpl. destruct (test x').
      { simpl. intros [_ H]. apply IHl in H. apply H. }
      { simpl. intros [H _]. discriminate H. }
Qed.

(** (Ungraded thought question) Are there any important properties of
    the function [forallb] which are not captured by this
    specification? *)

(* FILL IN HERE

    [] *)

(* ################################################################# *)
(** * The Logic of Coq *)

(** Coq's logical core, the _Calculus of Inductive
    Constructions_, differs in some important ways from other formal
    systems that are used by mathematicians to write down precise and
    rigorous definitions and proofs -- in particular from
    Zermelo-Fraenkel Set Theory (ZFC), the most popular foundation for
    paper-and-pencil mathematics.

    We conclude this chapter with a brief discussion of some of the
    most significant differences between these two worlds. *)

(* ================================================================= *)
(** ** Functional Extensionality *)

(** Coq's logic is quite minimalistic.  This means that one occasionally
    encounters cases where translating standard mathematical reasoning into
    Coq is cumbersome -- or even impossible -- unless we enrich its core
    logic with additional axioms. *)

(** For example, the equality assertions that we have seen so far
    mostly have concerned elements of inductive types ([nat], [bool],
    etc.).  But, since Coq's equality operator is polymorphic, we can use
    it at _any_ type -- in particular, we can write propositions claiming
    that two _functions_ are equal to each other:

    In certain cases Coq can successfully prove equality propositions stating
    that two _functions_ are equal to each other: **)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

(** This works when Coq can simplify the functions to the same expression,
    but this doesn't always happen. **)

(** These two functions are equal just by simplification, but in general
    functions can be equal for more interesting reasons.

    In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same output on every input:

    (forall x, f x = g x) -> f = g

    This is known as the principle of _functional extensionality_. *)

(** (Informally, an "extensional property" is one that pertains to an
    object's observable behavior.  Thus, functional extensionality
    simply means that a function's identity is completely determined
    by what we can observe from it -- i.e., the results we obtain
    after applying it.) *)

(** However, functional extensionality is not part of Coq's built-in logic.
    This means that some intuitively obvious propositions are not
    provable. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  Fail reflexivity. Fail rewrite add_comm.
  (* Stuck *)
Abort.

(** However, if we like, we can add functional extensionality to Coq
    using the [Axiom] command. *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** Defining something as an [Axiom] has the same effect as stating a
    theorem and skipping its proof using [Admitted], but it alerts the
    reader that this isn't just something we're going to come back and
    fill in later! *)

(** We can now invoke functional extensionality in proofs: *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

(** Naturally, we need to be quite careful when adding new axioms into
    Coq's logic, as this can render it _inconsistent_ -- that is, it may
    become possible to prove every proposition, including [False], [2+2=5],
    etc.!

    In general, there is no simple way of telling whether an axiom is safe
    to add: hard work by highly trained mathematicians is often required to
    establish the consistency of any particular combination of axioms.

    Fortunately, it is known that adding functional extensionality, in
    particular, _is_ consistent. *)

(** To check whether a particular proof relies on any additional
    axioms, use the [Print Assumptions] command:

      Print Assumptions function_equality_ex2
*)
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g

    (If you try this yourself, you may also see [add_comm] listed as
    an assumption, depending on whether the copy of [Tactics.v] in the
    local directory has the proof of [add_comm] filled in.) *)

(** **** Exercise: 4 stars, standard (tr_rev_correct)

    One problem with the definition of the list-reversing function [rev]
    that we have is that it performs a call to [app] on each step.  Running
    [app] takes time asymptotically linear in the size of the list, which
    means that [rev] is asymptotically quadratic.

    We can improve this with the following two-argument definition: *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** This version of [rev] is said to be _tail-recursive_, because the
    recursive call to the function is the last operation that needs to be
    performed (i.e., we don't have to execute [++] after the recursive
    call); a decent compiler will generate very efficient code in this
    case.

    Prove that the two definitions are indeed equivalent. *)

Lemma rev_append_nil : forall X (l1 l2 : list X), rev_append l1 l2 = rev_append l1 [] ++ l2.
Proof.
  intros X l1 l2.
  generalize dependent l2.
  induction l1.
  - reflexivity.
  - intros l2.
    simpl.
    rewrite -> IHl1. rewrite -> (IHl1 [x]). rewrite <- app_assoc. reflexivity.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  intros l.
  induction l.
  + reflexivity.
  + simpl. rewrite <- IHl. unfold tr_rev. simpl. apply rev_append_nil.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Classical vs. Constructive Logic *)

(** We have seen that it is not possible to test whether or not a
    proposition [P] holds while defining a Coq function.  You may be
    surprised to learn that a similar restriction applies in _proofs_!
    In other words, the following intuitive reasoning principle is not
    derivable in Coq: *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** To understand operationally why this is the case, recall
    that, to prove a statement of the form [P \/ Q], we use the [left]
    and [right] tactics, which effectively require knowing which side
    of the disjunction holds.  But the universally quantified [P] in
    [excluded_middle] is an _arbitrary_ proposition, which we know
    nothing about.  We don't have enough information to choose which
    of [left] or [right] to apply, just as Coq doesn't have enough
    information to mechanically decide whether [P] holds or not inside
    a function. *)

(** In the special case where we happen to know that [P] is reflected in
    some boolean term [b], knowing whether it holds or not is trivial: we
    just have to check the value of [b]. *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

(** In particular, the excluded middle is valid for equations [n = m],
    between natural numbers [n] and [m]. *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(** Sadly, this trick only works for decidable propositions. *)

(** It may seem strange that the general excluded middle is not
    available by default in Coq, since it is a standard feature of familiar
    logics like ZFC.  But there is a distinct advantage in _not_ assuming
    the excluded middle: statements in Coq make stronger claims than the
    analogous statements in standard mathematics.  Notably, a Coq proof of
    [exists x, P x] always includes a particular value of [x] for which we
    can prove [P x] -- in other words, every proof of existence is
    _constructive_. *)

(** Logics like Coq's, which do not assume the excluded middle, are
    referred to as _constructive logics_.

    More conventional logical systems such as ZFC, in which the
    excluded middle does hold for arbitrary propositions, are referred
    to as _classical_. *)

(** The following example illustrates why assuming the excluded middle may
    lead to non-constructive proofs:

    _Claim_: There exist irrational numbers [a] and [b] such that [a ^
    b] ([a] to the power [b]) is rational.

    _Proof_: It is not difficult to show that [sqrt 2] is irrational.  If
    [sqrt 2 ^ sqrt 2] is rational, it suffices to take [a = b = sqrt 2] and
    we are done.  Otherwise, [sqrt 2 ^ sqrt 2] is irrational.  In this
    case, we can take [a = sqrt 2 ^ sqrt 2] and [b = sqrt 2], since [a ^ b
    = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^ 2 = 2].  []

    Do you see what happened here?  We used the excluded middle to consider
    separately the cases where [sqrt 2 ^ sqrt 2] is rational and where it
    is not, without knowing which one actually holds!  Because of this, we
    finish the proof knowing that such [a] and [b] exist, but not knowing
    their actual values.

    As useful as constructive logic is, it does have its limitations: There
    are many statements that can easily be proven in classical logic but
    that have only much more complicated constructive proofs, and there are
    some that are known to have no constructive proof at all!  Fortunately,
    like functional extensionality, the excluded middle is known to be
    compatible with Coq's logic, allowing us to add it safely as an axiom.
    However, we will not need to do so here: the results that we cover can
    be developed entirely within constructive logic at negligible extra
    cost.

    It takes some practice to understand which proof techniques must be
    avoided in constructive reasoning, but arguments by contradiction, in
    particular, are infamous for leading to non-constructive proofs.
    Here's a typical example: suppose that we want to show that there
    exists [x] with some property [P], i.e., such that [P x].  We start by
    assuming that our conclusion is false; that is, [~ exists x, P x]. From
    this premise, it is not hard to derive [forall x, ~ P x].  If we manage
    to show that this intermediate fact results in a contradiction, we
    arrive at an existence proof without ever exhibiting a value of [x] for
    which [P x] holds!

    The technical flaw here, from a constructive standpoint, is that we
    claimed to prove [exists x, P x] using a proof of [~ ~ (exists x, P x)].
    Allowing ourselves to remove double negations from arbitrary
    statements is equivalent to assuming the excluded middle law, as shown
    in one of the exercises below.  Thus, this line of reasoning cannot be
    encoded in Coq without assuming additional axioms. *)

(** **** Exercise: 3 stars, standard (excluded_middle_irrefutable)

    Proving the consistency of Coq with the general excluded middle
    axiom requires complicated reasoning that cannot be carried out
    within Coq itself.  However, the following theorem implies that it
    is always safe to assume a decidability axiom (i.e., an instance
    of excluded middle) for any _particular_ Prop [P].  Why?  Because
    the negation of such an axiom leads to a contradiction.  If [~ (P
    \/ ~P)] were provable, then by [de_morgan_not_or] as proved above,
    [P /\ ~P] would be provable, which would be a contradiction. So, it
    is safe to add [P \/ ~P] as an axiom for any particular [P].

    Succinctly: for any proposition P,
        [Coq is consistent ==> (Coq + P \/ ~P) is consistent]. *)

Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P. intros H. apply H. right. intros HP. apply H. left. apply HP.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (not_exists_dist)

    It is a theorem of classical logic that the following two
    assertions are equivalent:

    ~ (exists x, ~ P x)
    forall x, P x

    The [dist_not_exists] theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle. *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.
  intros Hem X P Hne.
  intros x.
  destruct (Hem (P x)) as [HPx | HnPx].
  - (* HPx : P x *) apply HPx.
  - (* HnPx : ~P x *) exfalso. apply Hne. exists x. apply HnPx.
Qed.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (classical_axioms)

    For those who like a challenge, here is an exercise adapted from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following five statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.

    Prove that all six propositions (these five plus [excluded_middle])
    are equivalent.

    Hint: Rather than considering all pairs of statements pairwise,
    prove a single circular chain of implications that connects them
    all. *)

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).

Definition consequentia_mirabilis := forall P:Prop,
  (~P -> P) -> P.

Theorem peirce_double_negation_elimination :
  peirce -> double_negation_elimination.
Proof.
  unfold peirce.
  unfold double_negation_elimination.
  unfold not.
  intros Hp P Hnnp.
  apply Hp with (Q:=False).
  intros Hnp. exfalso. apply Hnnp. apply Hnp.
Qed.

Theorem double_negation_elimination_de_morgan_not_and_not :
  double_negation_elimination -> de_morgan_not_and_not.
Proof.
  unfold double_negation_elimination.
  unfold de_morgan_not_and_not.
  unfold not.
  intros Hdne P Q HPQ.
  apply Hdne. intros. apply HPQ. split.
  + intros H'. apply or_intro_l with (B:=Q) in H'. apply H. apply H'.
  + intros H'. apply or_intro_l with (B:=P) in H'. apply or_commut in H'. apply H. apply H'.
Qed.

Theorem de_morgan_not_and_not_implies_to_or :
  de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not.
  unfold implies_to_or.
  intros Hdm P Q HPQ.
  apply Hdm.
  intros H. unfold not in H. destruct H as [HnnP HnQ].
  apply HnnP. intros HP. apply HnQ. apply HPQ. apply HP.
Qed.

Theorem implies_to_or_excluded_middle :
  implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or.
  unfold excluded_middle.
  intros Hi P.
  apply or_commut. apply Hi. intros HP. apply HP.
Qed.

Theorem excluded_middle_consequentia_mirabilis :
  excluded_middle -> consequentia_mirabilis.
Proof.
  unfold excluded_middle.
  unfold consequentia_mirabilis.
  intros Hem P HnPP.
  destruct (Hem P).
  - apply H.
  - apply HnPP. apply H.
Qed.

Theorem consequentia_mirabilis_peirce :
  consequentia_mirabilis -> peirce.
Proof.
  unfold consequentia_mirabilis.
  unfold peirce.
  intros Hcons P Q HPQ.
  assert (HnPQ : ~P -> ~ (P -> Q)). { apply contrapositive. apply HPQ. }
  apply Hcons. intros Hnp. exfalso. apply HnPQ.
  - apply Hnp.
  - intros. contradiction.
Qed.

(* 2025-01-13 16:00 *)
