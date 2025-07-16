(** * ProofObjects: The Curry-Howard Correspondence *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

(** "Algorithms are the computational content of proofs."
    (Robert Harper) *)

(** We have seen that Coq has mechanisms both for _programming_,
    using inductive data types like [nat] or [list] and functions over
    these types, and for _proving_ properties of these programs, using
    inductive propositions (like [ev]), implication, universal
    quantification, and the like.  So far, we have mostly treated
    these mechanisms as if they were quite separate, and for many
    purposes this is a good way to think.  But we have also seen hints
    that Coq's programming and proving facilities are closely related.
    For example, the keyword [Inductive] is used to declare both data
    types and propositions, and [->] is used both to describe the type
    of functions on data and logical implication.  This is not just a
    syntactic accident!  In fact, programs and proofs in Coq are
    almost the same thing.  In this chapter we will study how this
    works.

    We have already seen the fundamental idea: provability in Coq is
    represented by concrete _evidence_.  When we construct the proof
    of a basic proposition, we are actually building a tree of
    evidence, which can be thought of as a data structure.

    If the proposition is an implication like [A -> B], then its proof
    will be an evidence _transformer_: a recipe for converting
    evidence for A into evidence for B.  So at a fundamental level,
    proofs are simply programs that manipulate evidence. *)

(** Question: If evidence is data, what are propositions themselves?

    Answer: They are types! *)

(** Look again at the formal definition of the [ev] property.  *)

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** Suppose we introduce an alternative pronunciation of "[:]".
    Instead of "has type," we can say "is a proof of."  For example,
    the second line in the definition of [ev] declares that [ev_0 : ev
    0].  Instead of "[ev_0] has type [ev 0]," we can say that "[ev_0]
    is a proof of [ev 0]." *)

(** This pun between types and propositions -- between [:] as "has type"
    and [:] as "is a proof of" or "is evidence for" -- is called the
    _Curry-Howard correspondence_.  It proposes a deep connection
    between the world of logic and the world of computation:

                 propositions  ~  types
                 proofs        ~  programs

    See [Wadler 2015] (in Bib.v) for a brief history and up-to-date
    exposition. *)

(** Many useful insights follow from this connection.  To begin with,
    it gives us a natural interpretation of the type of the [ev_SS]
    constructor: *)

Check ev_SS
  : forall n,
    ev n ->
    ev (S (S n)).

(** This can be read "[ev_SS] is a constructor that takes two
    arguments -- a number [n] and evidence for the proposition [ev
    n] -- and yields evidence for the proposition [ev (S (S n))]." *)

(** Now let's look again at a previous proof involving [ev]. *)

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** As with ordinary data values and functions, we can use the [Print]
    command to see the _proof object_ that results from this proof
    script. *)

Print ev_4.
(* ===> ev_4 = ev_SS 2 (ev_SS 0 ev_0)
      : ev 4  *)

(** Indeed, we can also write down this proof object directly,
    without the need for a separate proof script: *)

Check (ev_SS 2 (ev_SS 0 ev_0))
  : ev 4.

(** The expression [ev_SS 2 (ev_SS 0 ev_0)] can be thought of as
    instantiating the parameterized constructor [ev_SS] with the
    specific arguments [2] and [0] plus the corresponding proof
    objects for its premises [ev 2] and [ev 0].  Alternatively, we can
    think of [ev_SS] as a primitive "evidence constructor" that, when
    applied to a particular number, wants to be further applied to
    evidence that this number is even; its type,

      forall n, ev n -> ev (S (S n)),

    expresses this functionality, in the same way that the polymorphic
    type [forall X, list X] expresses the fact that the constructor
    [nil] can be thought of as a function from types to empty lists
    with elements of that type. *)

(** We saw in the [Logic] chapter that we can use function
    application syntax to instantiate universally quantified variables
    in lemmas, as well as to supply evidence for assumptions that
    these lemmas impose.  For instance: *)

Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

(* ################################################################# *)
(** * Proof Scripts *)

(** The _proof objects_ we've been discussing lie at the core of how
    Coq operates.  When Coq is following a proof script, what is
    happening internally is that it is gradually constructing a proof
    object -- a term whose type is the proposition being proved.  The
    tactics between [Proof] and [Qed] tell it how to build up a term
    of the required type.  To see this process in action, let's use
    the [Show Proof] command to display the current state of the proof
    tree at various points in the following tactic proof. *)

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

(** At any given moment, Coq has constructed a term with a
    "hole" (indicated by [?Goal] here, and so on), and it knows what
    type of evidence is needed to fill this hole.

    Each hole corresponds to a subgoal, and the proof is
    finished when there are no more subgoals.  At this point, the
    evidence we've built is stored in the global context under the name
    given in the [Theorem] command. *)

(** Tactic proofs are convenient, but they are not essential in Coq:
    in principle, we can always just construct the required evidence
    by hand. Then we can use [Definition] (rather than [Theorem]) to
    introduce a global name for this evidence. *)

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

(** All these different ways of building the proof lead to exactly the
    same evidence being saved in the global environment. *)

Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)

(** **** Exercise: 2 stars, standard (eight_is_even)

    Give a tactic proof and a proof object showing that [ev 8]. *)

Theorem ev_8 : ev 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition ev_8' : ev 8
  := ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).
(** [] *)

(* ################################################################# *)
(** * Quantifiers, Implications, Functions *)

(** In Coq's computational universe (where data structures and
    programs live), there are two sorts of values that have arrows in
    their types: _constructors_ introduced by [Inductive]ly defined
    data types, and _functions_.

    Similarly, in Coq's logical universe (where we carry out proofs),
    there are two ways of giving evidence for an implication:
    constructors introduced by [Inductive]ly defined propositions,
    and... functions! *)

(** For example, consider this statement: *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

(** What is the proof object corresponding to [ev_plus4]? *)

(** We're looking for an expression whose _type_ is [forall n, ev n ->
    ev (4 + n)] -- that is, a _function_ that takes two arguments (one
    number and a piece of evidence) and returns a piece of evidence!

    Here it is: *)

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

(** Recall that [fun n => blah] means "the function that, given [n],
    yields [blah]," and that Coq treats [4 + n] and [S (S (S (S n)))]
    as synonyms. Another equivalent way to write this definition is: *)

Definition ev_plus4'' (n : nat) (H : ev n)
                    : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4'' : forall n : nat, ev n -> ev (4 + n).

(** When we view the proposition being proved by [ev_plus4] as a
    function type, one interesting point becomes apparent: The second
    argument's type, [ev n], mentions the _value_ of the first
    argument, [n].

    While such _dependent types_ are not found in most mainstream
    programming languages, they can be quite useful in programming
    too, as the flurry of activity in the functional programming
    community over the past couple of decades demonstrates. *)

(** Notice that both implication ([->]) and quantification ([forall])
    correspond to functions on evidence.  In fact, they are really the
    same thing: [->] is just a shorthand for a degenerate use of
    [forall] where there is no dependency, i.e., no need to give a
    name to the type on the left-hand side of the arrow:

           forall (x:nat), nat
        =  forall (_:nat), nat
        =  nat          -> nat
*)

(** For example, consider this proposition: *)

Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

(** A proof term inhabiting this proposition would be a function
    with two arguments: a number [n] and some evidence [E] that [n] is
    even.  But the name [E] for this evidence is not used in the rest
    of the statement of [ev_plus2], so it's a bit silly to bother
    making up a name for it.  We could write it like this instead,
    using the dummy identifier [_] in place of a real name: *)

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).

(** Or, equivalently, we can write it in a more familiar way: *)

Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).

(** In general, "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)

(* ################################################################# *)
(** * Programming with Tactics *)

(** If we can build proofs by giving explicit terms rather than
    executing tactic scripts, you may be wondering whether we can
    build _programs_ using tactics rather than by writing down
    explicit terms.

    Naturally, the answer is yes! *)

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.
(* ==>
    add1 = fun n : nat => S n
         : nat -> nat
*)

Compute add1 2.
(* ==> 3 : nat *)

(** Notice that we terminated the [Definition] with a [.] rather than
    with [:=] followed by a term.  This tells Coq to enter _proof
    scripting mode_ to build an object of type [nat -> nat].  Also, we
    terminate the proof with [Defined] rather than [Qed]; this makes
    the definition _transparent_ so that it can be used in computation
    like a normally-defined function.  ([Qed]-defined objects are
    opaque during computation.)

    This feature is mainly useful for writing functions with dependent
    types, which we won't explore much further in this book.  But it
    does illustrate the uniformity and orthogonality of the basic
    ideas in Coq. *)

(* ################################################################# *)
(** * Logical Connectives as Inductive Types *)

(** Inductive definitions are powerful enough to express most of the
    logical connectives we have seen so far.  Indeed, only universal
    quantification (with implication as a special case) is built into
    Coq; all the others are defined inductively.

    Let's see how. *)

Module Props.

(* ================================================================= *)
(** ** Conjunction *)

(** To prove that [P /\ Q] holds, we must present evidence for both
    [P] and [Q].  Thus, it makes sense to define a proof object for
    [P /\ Q] to consist of a pair of two proofs: one for [P] and
    another one for [Q]. This leads to the following definition. *)

Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

(** Notice the similarity with the definition of the [prod] type,
    given in chapter [Poly]; the only difference is that [prod] takes
    [Type] arguments, whereas [and] takes [Prop] arguments. *)

Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)

(** This similarity should clarify why [destruct] and [intros]
    patterns can be used on a conjunctive hypothesis.  Case analysis
    allows us to consider all possible ways in which [P /\ Q] was
    proved -- here just one (the [conj] constructor). *)

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.

(** Similarly, the [split] tactic actually works for any inductively
    defined proposition with exactly one constructor.  In particular,
    it works for [and]: *)

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

End And.

(** This shows why the inductive definition of [and] can be
    manipulated by tactics as we've been doing.  We can also use it to
    build proofs directly, using pattern-matching.  For instance: *)

Definition proj1'' P Q (HPQ : P /\ Q) : P :=
  match HPQ with
  | conj HP HQ => HP
  end.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(** **** Exercise: 2 stars, standard (conj_fact)

    Construct a proof object for the following proposition. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R
  := fun P Q R HPQ HQR => conj (proj1 P Q HPQ) (proj2 Q R HQR).
(** [] *)

(* ================================================================= *)
(** ** Disjunction *)

(** The inductive definition of disjunction uses two constructors, one
    for each side of the disjunct: *)

Module Or.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q) : type_scope.

(** This declaration explains the behavior of the [destruct] tactic on
    a disjunctive hypothesis, since the generated subgoals match the
    shape of the [or_introl] and [or_intror] constructors. *)

(** Once again, we can also directly write proof objects for theorems
    involving [or], without resorting to tactics. *)

Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.

Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Proof.
  intros P Q HP. left. apply HP.
  Show Proof.
Qed.

Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
Qed.

End Or.

(** **** Exercise: 2 stars, standard (or_commut')

    Construct a proof object for the following proposition. *)

Definition or_commut' : forall P Q, P \/ Q -> Q \/ P
  := fun P Q HPQ =>
       match HPQ with
       | or_introl HP => or_intror HP
       | or_intror HQ => or_introl HQ
       end.
(** [] *)

(* ================================================================= *)
(** ** Existential Quantification *)

(** To give evidence for an existential quantifier, we package a
    witness [x] together with a proof that [x] satisfies the property
    [P]: *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.

End Ex.

(** This probably needs a little unpacking.  The core definition is
    for a type former [ex] that can be used to build propositions of
    the form [ex P], where [P] itself is a _function_ from witness
    values in the type [A] to propositions.  The [ex_intro]
    constructor then offers a way of constructing evidence for [ex P],
    given a witness [x] and a proof of [P x].

    The notation in the standard library is a slight extension of
    the above, enabling syntactic forms such as [exists x y, P x y]. *)

(** The more familiar form [exists x, ev x] desugars to an expression
    involving [ex]: *)

Check ex (fun n => ev n) : Prop.

(** Here's how to define an explicit proof object involving [ex]: *)

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(** **** Exercise: 2 stars, standard (ex_ev_Sn)

    Construct a proof object for the following proposition. *)

Definition ex_ev_Sn : ex (fun n => ev (S n))
  := ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).
(** [] *)

(** To destruct existentials in a proof term we simply use match: *)
Definition dist_exists_or_term (X:Type) (P Q : X -> Prop) :
  (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x) :=
  fun H => match H with
           | ex_intro _ x Hx =>
               match Hx with
               | or_introl HPx => or_introl (ex_intro _ x HPx)
               | or_intror HQx => or_intror (ex_intro _ x HQx)
               end
           end.

(** **** Exercise: 2 stars, standard (ex_match)

    Construct a proof object for the following proposition: *)
Definition ex_match : forall (A : Type) (P Q : A -> Prop),
  (forall x, P x -> Q x) ->
  (exists x, P x) -> (exists x, Q x)
  := fun A P Q H HP =>
       match HP with
         | ex_intro _ x Hx => ex_intro (fun x => Q x) x (H x Hx)
       end.
(** [] *)

(* ================================================================= *)
(** ** [True] and [False] *)

(** The inductive definition of the [True] proposition is simple: *)

Inductive True : Prop :=
  | I : True.

(** It has one constructor (so every proof of [True] is the same, so
    being given a proof of [True] is not informative.) *)

(** **** Exercise: 1 star, standard (p_implies_true)

    Construct a proof object for the following proposition. *)

Definition p_implies_true : forall P, P -> True
  := fun _ _ => I.
(** [] *)

(** [False] is equally simple -- indeed, so simple it may look
    syntactically wrong at first glance! *)

Inductive False : Prop := .

(** That is, [False] is an inductive type with _no_ constructors --
    i.e., no way to build evidence for it. For example, there is
    no way to complete the following definition such that it
    succeeds. *)

Fail
  Definition contra : False :=
  42.

(** But it is possible to destruct [False] by pattern matching. There can
    be no patterns that match it, since it has no constructors.  So
    the pattern match also is so simple it may look syntactically
    wrong at first glance. *)

Definition false_implies_zero_eq_one : False -> 0 = 1 :=
  fun contra => match contra with end.

(** Since there are no branches to evaluate, the [match] expression
    can be considered to have any type we want, including [0 = 1].
    Fortunately, it's impossible to ever cause the [match] to be
    evaluated, because we can never construct a value of type [False]
    to pass to the function. *)

(** **** Exercise: 1 star, standard (ex_falso_quodlibet')

    Construct a proof object for the following proposition. *)

Definition ex_falso_quodlibet' : forall P, False -> P
  := fun _ contra => match contra with end.
(** [] *)

End Props.

(* ################################################################# *)
(** * Equality *)

(** Even Coq's equality relation is not built in.  We can define
    it ourselves: *)

Module EqualityPlayground.

Inductive eq {X:Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                       (at level 70, no associativity)
                     : type_scope.

(** The way to think about this definition (which is just a slight
    variant of the standard library's) is that, given a set [X], it
    defines a _family_ of propositions "[x] is equal to [y]," indexed
    by pairs of values ([x] and [y]) from [X].  There is just one way
    of constructing evidence for members of this family: applying the
    constructor [eq_refl] to a type [X] and a single value [x : X],
    which yields evidence that [x] is equal to [x].

    Other types of the form [eq x y] where [x] and [y] are not the
    same are thus uninhabited. *)

(** We can use [eq_refl] to construct evidence that, for example, [2 =
    2].  Can we also use it to construct evidence that [1 + 1 = 2]?
    Yes, we can.  Indeed, it is the very same piece of evidence!

    The reason is that Coq treats as "the same" any two terms that are
    _convertible_ according to a simple set of computation rules.

    These rules, which are similar to those used by [Compute], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.  *)

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

(** The [reflexivity] tactic that we have used to prove
    equalities up to now is essentially just shorthand for [apply
    eq_refl].

    In tactic-based proofs of equality, the conversion rules are
    normally hidden in uses of [simpl] (either explicit or implicit in
    other tactics such as [reflexivity]).

    But you can see them directly at work in the following explicit
    proof objects: *)

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[]  :=
  fun (X:Type) (x:X) => eq_refl [x].

(** We can also pattern-match on an equality proof: *)
Definition eq_add : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2) :=
  fun n1 n2 Heq =>
    match Heq with
    | eq_refl n => eq_refl (S n)
    end.

(** By pattern-matching against [n1 == n2], we obtain a term [n]
    that replaces [n1] and [n2] in the type we have to produce, so
    instead of [(S n1) == (S n2)], we now have to produce something
    of type [(S n) == (S n)], which we establish by [eq_refl (S n)]. *)

(** A tactic-based proof runs into some difficulties if we try to use
    our usual repertoire of tactics, such as [rewrite] and
    [reflexivity]. Those work with *setoid* relations that Coq knows
    about, such as [=], but not our [==]. We could prove to Coq that
    [==] is a setoid, but a simpler way is to use [destruct] and
    [apply] instead. *)

Theorem eq_add' : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2).
Proof.
  intros n1 n2 Heq.
  Fail rewrite Heq. (* doesn't work for _our_ == relation *)
  destruct Heq as [n]. (* n1 and n2 replaced by n in the goal! *)
  Fail reflexivity. (* doesn't work for _our_ == relation *)
  apply eq_refl.
Qed.

(** **** Exercise: 2 stars, standard (eq_cons)

    Construct the proof object for the following theorem. Use pattern
    matching on the equality hypotheses. *)

Definition eq_cons : forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
    h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2
  := fun X h1 h2 t1 t2 HH HT =>
       match HH with
       | eq_refl h =>
           match HT with
           | eq_refl t => eq_refl (h :: t)
           end
       end.
(** [] *)

(** **** Exercise: 2 stars, standard (equality__leibniz_equality)

    The inductive definition of equality implies _Leibniz equality_:
    what we mean when we say "[x] and [y] are equal" is that every
    property on [P] that is true of [x] is also true of [y]. Prove
    that. *)

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall (P : X -> Prop), P x -> P y.
Proof.
  intros X x y Heq P H.
  destruct Heq. apply H. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (equality__leibniz_equality_term)

    Construct the proof object for the previous exercise.  All it
    requires is anonymous functions and pattern-matching; the large
    proof term constructed by tactics in the previous exercise is
    needessly complicated. Hint: pattern-match as soon as possible. *)
Definition equality__leibniz_equality_term : forall (X : Type) (x y: X),
    x == y -> forall P : (X -> Prop), P x -> P y
  := fun X x y Heq =>
       match Heq with
       | eq_refl x => fun P H => H
       end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (leibniz_equality__equality)

    Show that, in fact, the inductive definition of equality is
    _equivalent_ to Leibniz equality.  Hint: the proof is quite short;
    about all you need to do is to invent a clever property [P] to
    instantiate the antecedent.*)

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
  intros. apply H. apply eq_refl. Qed.
(** [] *)

End EqualityPlayground.

(* ================================================================= *)
(** ** Inversion, Again *)

(** We've seen [inversion] used with both equality hypotheses and
    hypotheses about inductively defined propositions.  Now that we've
    seen that these are actually the same thing, we're in a position
    to take a closer look at how [inversion] behaves.

    In general, the [inversion] tactic...

    - takes a hypothesis [H] whose type [P] is inductively defined,
      and

    - for each constructor [C] in [P]'s definition,

      - generates a new subgoal in which we assume [H] was
        built with [C],

      - adds the arguments (premises) of [C] to the context of
        the subgoal as extra hypotheses,

      - matches the conclusion (result type) of [C] against the
        current goal and calculates a set of equalities that must
        hold in order for [C] to be applicable,

      - adds these equalities to the context (and, for convenience,
        rewrites them in the goal), and

      - if the equalities are not satisfiable (e.g., they involve
        things like [S n = O]), immediately solves the subgoal. *)

(** _Example_: If we invert a hypothesis built with [or], there are
    two constructors, so two subgoals get generated.  The
    conclusion (result type) of the constructor ([P \/ Q]) doesn't
    place any restrictions on the form of [P] or [Q], so we don't get
    any extra equalities in the context of the subgoal. *)

(** _Example_: If we invert a hypothesis built with [and], there is
    only one constructor, so only one subgoal gets generated.  Again,
    the conclusion (result type) of the constructor ([P /\ Q]) doesn't
    place any restrictions on the form of [P] or [Q], so we don't get
    any extra equalities in the context of the subgoal.  The
    constructor does have two arguments, though, and these can be seen
    in the context in the subgoal. *)

(** _Example_: If we invert a hypothesis built with [eq], there is
    again only one constructor, so only one subgoal gets generated.
    Now, though, the form of the [eq_refl] constructor does give us
    some extra information: it tells us that the two arguments to [eq]
    must be the same!  The [inversion] tactic adds this fact to the
    context. *)

(* ################################################################# *)
(** * Coq's Trusted Computing Base *)

(** One question that arises with any automated proof assistant
    is "why should we trust it?" -- i.e., what if there is a bug in
    the implementation that renders all its reasoning suspect?

    While it is impossible to allay such concerns completely, the fact
    that Coq is based on the Curry-Howard correspondence gives it a
    strong foundation. Because propositions are just types and proofs
    are just terms, checking that an alleged proof of a proposition is
    valid just amounts to _type-checking_ the term.  Type checkers are
    relatively small and straightforward programs, so the "trusted
    computing base" for Coq -- the part of the code that we have to
    believe is operating correctly -- is small too.

    What must a typechecker do?  Its primary job is to make sure that
    in each function application the expected and actual argument
    types match, that the arms of a [match] expression are constructor
    patterns belonging to the inductive type being matched over and
    all arms of the [match] return the same type, and so on. *)

(** There are a few additional wrinkles:

    First, since Coq types can themselves be expressions, the checker
    must normalize these (by using the computation rules) before
    comparing them.

    Second, the checker must make sure that [match] expressions are
    _exhaustive_.  That is, there must be an arm for every possible
    constructor.  To see why, consider the following alleged proof
    object: *)

Fail Definition or_bogus : forall P Q, P \/ Q -> P :=
  fun (P Q : Prop) (A : P \/ Q) =>
    match A with
    | or_introl H => H
    end.

(** All the types here match correctly, but the [match] only
    considers one of the possible constructors for [or].  Coq's
    exhaustiveness check will reject this definition.

    Third, the checker must make sure that each recursive function
    terminates.  It does this using a syntactic check to make sure
    that each recursive call is on a subexpression of the original
    argument.  To see why this is essential, consider this alleged
    proof: *)

Fail Fixpoint infinite_loop {X : Type} (n : nat) {struct n} : X :=
  infinite_loop n.

Fail Definition falso : False := infinite_loop 0.

(** Recursive function [infinite_loop] purports to return a
    value of any type [X] that you would like.  (The [struct]
    annotation on the function tells Coq that it recurses on argument
    [n], not [X].)  Were Coq to allow [infinite_loop], then [falso]
    would be definable, thus giving evidence for [False].  So Coq rejects
    [infinite_loop]. *)

(** Note that the soundness of Coq depends only on the
    correctness of this typechecking engine, not on the tactic
    machinery.  If there is a bug in a tactic implementation (and this
    certainly does happen!), that tactic might construct an invalid
    proof term.  But when you type [Qed], Coq checks the term for
    validity from scratch.  Only theorems whose proofs pass the
    type-checker can be used in further proof developments.  *)

(* ################################################################# *)
(** * More Exercises *)

(** Most of the following theorems were already proved with tactics in
    [Logic].  Now construct the proof objects for them
    directly. *)

(** **** Exercise: 2 stars, standard (and_assoc) *)
Definition and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R
  := fun P Q R H =>
       match H with
       | conj HP (conj HQ HR) => conj (conj HP HQ) HR
       end.
(** [] *)

(** **** Exercise: 3 stars, standard (or_distributes_over_and) *)
Definition or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R)
  := fun P Q R =>
       conj (fun H =>
               match H with
               | or_introl HP => conj (or_introl HP) (or_introl HP)
               | or_intror (conj HQ HR) => conj (or_intror HQ) (or_intror HR)
               end)
            (fun H =>
               match H with
               | conj (or_introl HP) _ => or_introl HP
               | conj _ (or_introl HP) => or_introl HP
               | conj (or_intror HQ) (or_intror HR) => or_intror (conj HQ HR)
               end).
(** [] *)

(** **** Exercise: 3 stars, standard (negations) *)
Definition double_neg : forall P : Prop,
    P -> ~~P
  := fun P HP H => H HP.

Definition contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q
  := fun P Q contra =>
       match contra with
       | conj HP HNA => match (HNA HP) with end
       end.

Definition de_morgan_not_or : forall P Q : Prop,
    ~ (P \/ Q) -> ~P /\ ~Q
  := fun P Q HPQ => conj (fun HP => HPQ (or_introl HP)) (fun HQ => HPQ (or_intror HQ)).
(** [] *)

(** **** Exercise: 2 stars, standard (currying) *)
Definition curry : forall P Q R : Prop,
    ((P /\ Q) -> R) -> (P -> (Q -> R))
  := fun P Q R f HP HQ => f (conj HP HQ).

Definition uncurry : forall P Q R : Prop,
    (P -> (Q -> R)) -> ((P /\ Q) -> R)
  := fun P Q R f HPQ =>
       match HPQ with
       | conj HP HQ => f HP HQ
       end.
(** [] *)

(* ################################################################# *)
(** * Proof Irrelevance (Advanced) *)

(** In [Logic] we saw that functional extensionality could be
    added to Coq. A similar notion about propositions can also
    be defined (and added as an axiom, if desired): *)

Definition propositional_extensionality : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

(** Propositional extensionality asserts that if two propositions are
    equivalent -- i.e., each implies the other -- then they are in
    fact equal. The _proof objects_ for the propositions might be
    syntactically different terms. But propositional extensionality
    overlooks that, just as functional extensionality overlooks the
    syntactic differences between functions. *)

(** **** Exercise: 1 star, advanced (pe_implies_or_eq)

    Prove the following consequence of propositional extensionality. *)

Theorem pe_implies_or_eq :
  propositional_extensionality ->
  forall (P Q : Prop), (P \/ Q) = (Q \/ P).
Proof.
  intros PE P Q. apply PE.
  split.
  intros H. apply or_commut. apply H.
  intros H. apply or_commut. apply H.
Qed.
(** [] *)

(** **** Exercise: 1 star, advanced (pe_implies_true_eq)

    Prove that if a proposition [P] is provable, then it is equal to
    [True] -- as a consequence of propositional extensionality. *)

Lemma pe_implies_true_eq :
  propositional_extensionality ->
  forall (P : Prop), P -> True = P.
Proof. intros PE P HP. apply PE. split. intros. apply HP. intros. apply I. Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (pe_implies_pi)

    Acknowledgment: this theorem and its proof technique are inspired
    by Gert Smolka's manuscript Modeling and Proving in Computational
    Type Theory Using the Coq Proof Assistant, 2021. *)

(** Another, perhaps surprising, consequence of propositional
    extensionality is that it implies _proof irrelevance_, which
    asserts that all proof objects for a proposition are equal.*)

Definition proof_irrelevance : Prop :=
  forall (P : Prop) (pf1 pf2 : P), pf1 = pf2.

(** Prove that fact. Use [pe_implies_true_eq] to establish that the
    proposition [P] in [proof_irrelevance] is equal to [True]. Leverage
    that equality to establish that both proof objects [pf1] and
    [pf2] must be just [I]. *)

Theorem pe_implies_pi :
  propositional_extensionality -> proof_irrelevance.
Proof.
  intros PE P pf1 pf2.
  assert (H: True = P). { apply (pe_implies_true_eq PE). apply pf1. }
  destruct H.
  destruct pf1.
  destruct pf2.
  reflexivity.
Qed.
(** [] *)

(* 2025-01-13 16:00 *)
