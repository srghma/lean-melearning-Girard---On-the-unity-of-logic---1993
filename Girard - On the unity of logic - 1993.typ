#import "@preview/curryst:0.6.0": prooftree, rule

#let tensor = math.times.o
#let oplus = math.plus.o
#let simeq = math.tilde.equiv
#let sect = math.inter

#let conf(
  cols: 1,
  margin: (x: 1.25in, y: 1.25in),
  paper: "us-letter",
  lang: "en",
  region: "US",
  font: ("New Computer Modern",),
  fontsize: 10pt,
  sectionnumbering: none,
  doc,
) = {
  set page(
    paper: paper,
    margin: margin,
    numbering: "1",
  )
  set par(justify: true, leading: 0.6em)
  set text(lang: lang, region: region, font: font, size: fontsize)
  set heading(numbering: sectionnumbering)
  doc
}

#show: doc => conf(
  cols: 1,
  doc,
)

// Top Journal Header
#grid(
  columns: (1fr, 1fr),
  [
    Annals of Pure and Applied Logic 59 (1993) 201--217 \
    North-Holland
  ],
  align(right)[201],
)

#v(2.5em)

#align(center)[
  #text(size: 1.7em, weight: "bold")[On the unity of logic]

  #v(1em)
  #text(size: 1.15em)[Jean-Yves Girard]

  #v(0.3em)
  #text(size: 0.9em, style: "italic")[
    Équipe de Logique, UA 753 du CNRS Mathématiques, Université Paris VII, t. 45--55, 5#super[e] étage, \
    2 place Jussieu, 75251 Paris Cedex 05, France
  ]

  #v(0.8em)
  #text(size: 0.9em)[
    Communicated by D. van Dalen \
    Received 20 June 1991
  ]
]

#v(1.2em)

#block(inset: (x: 1.5em))[
  #set text(size: 8.8pt)
  #text(weight: "bold", style: "italic")[Abstract]

  #v(0.2em)
  Girard, J.-Y., On the unity of logic, Annals of Pure and Applied Logic 59 (1993) 201--217

  #v(0.3em)
  We present a single sequent calculus common to classical, intuitionistic and linear logics. The main novelty is that classical, intuitionistic and linear logics appear as _fragments_, i.e. as particular classes of formulas and sequents. For instance, a proof of an intuitionistic formula $A$ may use classical or linear lemmas without any restriction: but after cut-elimination the proof of $A$ is wholly intuitionistic, what is superficially achieved by the subformula property (only intuitionistic formulas are used) and more deeply by a very careful treatment of structural rules. This approach is radically different from the one that consists in "changing the rule of the game" when we want to change logic, e.g. pass from one style of sequent to another: here, there is only one logic, which---depending on its use---may appear classical, intuitionistic or linear.

  #v(0.4em)
  Nous présentons un calcul des séquents unifié, commun aux logiques classique, intuitionniste et linéaire. La principale nouveauté est que les logiques classique, intuitionniste et linéaire apparaissent comme des _fragments_, c'est à dire comme des classes particulières de formules et de séquents. Par exemple la démonstration d'un énoncé intuitionniste pourra utiliser des lemmes classiques ou intuitionnistes sans limitation: simplement après élimination des coupures, la démonstration se fera entièrement dans le fragment intuitionniste, ce qui est superficiellement assuré par la propriété de la sous-formule (seulement des formules intuitionnistes sont utilisées) et plus profondément par un traitement très rigoureux des règles structurelles. Cette approche est radicalement différente de l'approche habituelle qui consiste tout bonnement à changer la règle du jeu quand on veut changer de logique, c'est à dire de style de séquent: ici il n'y a plus qu'une seule logique, qui au gré des utilisations peut apparaître classique, intuitionniste ou linéaire.
]

#v(1em)

By the turn of this century the situation concerning logic was quite simple:
there was basically one logic (classical logic) which could be used (by changing
the set of proper axioms) in various situations. Logic was about _pure_ reasoning.
Brouwer's criticism destroyed this dream of unity: classical logic was not suited for
constructive features and therefore it lost its universality. Now by the end of the
century we are faced with an incredible number of logics---some of them only
named 'logic' by antiphrasis, some of them introduced on serious grounds. Is
logic still about pure reasoning? In other words, could there be a way to reunify
logical systems---let us say those systems with a good sequent calculus---into a
single sequent calculus? Is it possible to handle the (legitimate) distinction
classical/intuitionistic not through a change of system, but through a change of
formulas? Is it possible to obtain classical effects by a restriction to classical
formulas? Etc.

#place(
  bottom,
  clearance: 0pt,
  [
    #line(length: 100%, stroke: 0.4pt)
    #set text(size: 8pt)
    _Correspondence to:_ J.-Y. Girard, Mathématiques Discrètes, UPR A9016, 163 Av. de Luminy, case 930, 13288 Marseille Cedex 09, France. \
    0168-0072/93/\$06.00 © 1993 -- Elsevier Science Publishers B.V. All rights reserved
  ]
)

Of course, there surely are ways to achieve this by cheating, typically
by considering a disjoint union of systems. However, all these jokes
will be made impossible if we insist on the fact that the various
systems represented should communicate freely (and for instance a
classical theorem could have an intuitionistic corollary and vice
versa).

In the unified calculus *LU* that we present in this paper,
classical, linear and intuitionistic logics appear as
_fragments._ This means that one can define notions of
_classical, intuitionistic_ or _linear_
sequents and prove that a cut-free proof of a sequent in one of these
fragments is wholly inside the fragment; of course a proof with cuts has
the right to use arbitrary sequents, i.e., the fragments can freely
communicate.

= 1. Unified sequents

Standard sequent calculi essentially differ by their different maintenances of
sequents:

#set enum(numbering: "(i)", indent: 1em)
+ classical logic accepts weakening and contraction on both sides;
+ intuitionistic (minimal) logic restricts the succedent to one formula---which has the effect of forbidding weakening and contraction to the right;
+ linear logic refuses both, but has special connectives ! and ? which---when prefixed to a formula---allow structural rules on the left (!) and on the right (?).

Our basic unifying idea will be to define two zones in a sequent: a zone with a
'classical' maintenance, and a zone with a linear maintenance; there will be no
zone with an intuitionistic maintenance: intuitionistic maintenance, i.e. 'one
formula on the right', will result from a careful linear maintenance. Typically,
we could use a notation $Gamma; Gamma' tack Delta'; Delta$ to indicate that $Gamma'$
and $Delta'$ behave classically, whereas $Gamma$ and $Delta$ behave linearly. We could
try to identify classical sequents with those where $Gamma$ and $Delta$ are empty,
and intuitionistic ones as those in which $Gamma$ and $Delta'$ are empty, $Delta$
consisting of one formula. This is roughly what will happen, with some difficulties
and some surprises:

#set enum(start: 1)
+ It must be possible to pass between both sides of the semi-colon: surely one
  should be able to enter the central zone (we lose information), and also---with
  some constraint, otherwise the semi-colon would lose its importance---to move
  to the extremes. One of these constraints could be the addition of a symbol, e.g.
  move $A$ from $Gamma'$ to $Gamma$, but now write it as $!A$.

+ This is not quite satisfactory; typically, a formula already starting with '!'
  should be able to pass freely. However, it immediately turns out that those guys
  that can cross the left semi-colon in both ways are closed under the linear
  connectives $tensor$ and $oplus$ and under the quantifier $⋁ x$. The sensible thing to do is
  therefore to distinguish among formulas _positive_ ones, including positive atomic
  formulas for problems of substitution. Symmetrically, one distinguishes _negative_
  formulas, while the remaining ones are called _neutral:_ those must pay at both
  borders.

+ The restatement of the rules of linear logic in this wider context is
  unproblematic and rather satisfactory, especially the treatment of '!' and '?'
  becomes slightly smoother.

+ We now have to define three _polarities_ (classes of formulas) and we can
  toy with the connectives of linear logic to define synthetic connectives, built like
  _chimeras,_ with a head of $tensor$, a tail of $\&$, etc.---only good taste limits the
  possibilities. Typically, if we want to define a conjunction we would like it to be
  associative (at the level of provability, but moreover at the level of denotational
  semantics), hence this imposes some coordination between the various parts of
  our chimera. In fact the connectives built have been chosen under two
  constraints:
  - limitation of the number of connectives: for instance only one conjunction,
    only one disjunction, for classical and intuitionistic logics, but unfortunately two
    distinct implications for these logics;
  - maximisation of the number of remarkable isomorphisms.

+ As far as classical logic is concerned, the results presented here are
  consistent with the previous work of the author [3]; in fact classical logic is
  obtained by limitation to formulas which are (hereditarily) nonneutral. The role
  of classical sequents is played by the sequents of the form $Gamma; Gamma' tack Delta'; Delta$ when the
  nonpermeable part of $Gamma, Delta$ consists of at most one formula (the _stoup_ of [3]). The
  reader is referred to this paper to check the extreme number of isomorphisms
  satisfied by the classical fragment (some of them, typically the De Morgan duality
  between $and$ and $or$, do not extend to neutral polarities). There is only one small
  defect: a single formula $A$ is interpreted by $; tack A;$; whereas for the other logics, it is
  interpreted by $; tack ; A$. However, if $A$ is negative (right permeable) we can replace
  $; tack A;$ by $; tack ; A$, and if $A$ is positive we can replace $; tack A;$ by $; tack ; forall x A$ ($x$ dummy)
  or $; tack ; A or (not bold(V))$.

+ As far as disjunction, existence and negation are ignored, intuitionistic
  logic is a quite even system in proof-theoretic terms, as shown by various
  relations to $lambda$-calculus. The _neutral intuitionistic_ fragment is made of (hereditarily)
  neutral formulas, and basically accepts intuitionistic $supset$, $and$ and $⋀ x$; besides
  sequents $; Gamma' tack ; B$ which were expected, there arise sequents $A; Gamma' tack ; B$
  corresponding to the notion of _headvariable._ Not only the usual intuitionistic
  sequent calculus is recovered, but it is improved!

+ Surely less perfect is the full intuitionistic system with $or$, $exists x$ and $bold(F)$ (i.e.
  negation); the translation of this system into linear logic (the starting point of
  linear logic, see [2]) made use of the combination $!A oplus !B$, which is awfully
  nonassociative (denotationally speaking): compare $!(!A oplus !B) oplus !C$ with $!A oplus
  !(!B oplus !C)$. However, one could use $A$ instead of $!A$ if $A$ were known to be
  positive. Therefore there is room for an associative disjunction provided we
  consider not only neutral formulas, but also positive ones. The resulting
  disjunction is a very complex chimera which manages to be associative and
  commutative, and also works in the classical case. We surely do not get as many
  denotational isomorphisms as we would like (typically there is no unit for the
  disjunction, or $A supset B and C simeq (A supset B) and (A supset C)$ only when $B$ and $C$ are neutral),
  but the situation is incredibly better than expected. In terms of sequents, we lose
  the phenomenon of 'headvariable', since a term may be linear in several of its
  variables if we perform iterated pattern-matchings.

The system presented here is rather big, for the reason that we used a
two-sided version to accommodate intuitionistic features more directly, and
because there are classical, intuitionistic and linear connectives; last, but not least
rules can split into several cases depending on polarities; the rules for disjunction,
for instance, fill a whole page! But this complication is rather superficial: it is
more convenient to use the same symbol for nine 'micro-connectives' corresponding to all possible polarities of the disjuncts. Given $A$ and $B$, we get at most two
possible right rules and only one left rule, as usual. So *LU* has a very big number
of connectives but apart from this it is a quite even sequent calculus.

= 2. Polarities

Each formula is given with a polarity $+1$ (positive), $0$ (neutral), $-1$ (negative).
We use the following notational trick to indicate polarities: $P, Q, R$ for positive
formulas, $S, T, U$ for neutral formulas, $L, M, N$ for negative formulas. When we
want to ignore the polarity, we shall use the letters $A, B, C$.

Semantically speaking, a neutral formula refers to a coherent space; a positive
formula refers to a positive correlation space, and a negative formula to a
negative correlation space (see [3] for a definition). Now remember that a
correlation space is a coherent space plus extra structure (in fact PCS generalise
spaces of the form $!X$, and NCS generalise spaces $?X$; both are about structural
rules: a PCS is a space with left structural rules, a NCS obeys right structural
rules); this explains the polarity table (see Table 1) for linear logic: we first
combine the underlying coherent spaces $S$ and $T$ to get a coherent space $U$ (e.g.
$U = S tensor T$), and if possible we try to endow $U$ with a canonical structure of
correlation space (typically, if $S$ and $T$ are underlying coherent spaces for PCS $P$
and $Q$, we equip $S tensor T$ with a structure of PCS in the obvious way).

Before we start, we have to make a choice about polarity 0: do we consider the
possibility that something of polarity $+1$ (or $-1$) has also polarity $0$? In that case
it would be normal to indicate that we decide to forget the nonzero polarity,
causing complications and more complications. In fact, if we decide to answer
No, we get a quite reasonable answer: in linear logic we can forget negative
polarity by forming $A tensor bold(1)$, and a positive one by forming $A ⅋ bot$, hence if I
replace $A$ by $(A tensor bold(1)) ⅋ bot$, I can change the polarity to 0. (In a similar way,
$bold(V) supset A$ neutralises any intuitionistic formula.)

#v(1em)

#align(center)[
  #text(size: 9pt)[
    Table 1 \
    Polarities for linear connectives

    #v(0.3em)
    #table(
      columns: 16,
      align: center,
      stroke: 0.4pt,
      table.header(
        [$A$], [$B$], [$A tensor B$], [$A ⅋ B$], [$A ⊸ B$], [$A \& B$], [$A oplus B$], [$A^bot$], [$!A$], [$?A$], [$⋀ x A$], [$⋁ x A$], [$bold(1)$], [$bot$], [$top$], [$bold(0)$],
      ),
      [$+1$], [$+1$], [$+1$], [$0$], [$0$], [$0$], [$+1$], [$-1$], [$+1$], [$-1$], [$0$], [$+1$], [$+1$], [$-1$], [$-1$], [$+1$],
      [$0$], [$+1$], [$0$], [$0$], [$0$], [$0$], [$0$], [$0$], [$+1$], [$-1$], [$0$], [$0$], [], [], [], [],
      [$-1$], [$+1$], [$0$], [$0$], [$0$], [$0$], [$0$], [$+1$], [$+1$], [$-1$], [$-1$], [$0$], [], [], [], [],
      [$+1$], [$0$], [$0$], [$0$], [$0$], [$0$], [$0$], [], [], [], [], [], [], [], [], [],
      [$0$], [$0$], [$0$], [$0$], [$0$], [$0$], [$0$], [], [], [], [], [], [], [], [], [],
      [$-1$], [$0$], [$0$], [$0$], [$0$], [$0$], [$0$], [], [], [], [], [], [], [], [], [],
      [$+1$], [$-1$], [$0$], [$0$], [$-1$], [$0$], [$0$], [], [], [], [], [], [], [], [], [],
      [$0$], [$-1$], [$0$], [$0$], [$0$], [$0$], [$0$], [], [], [], [], [], [], [], [], [],
      [$-1$], [$-1$], [$0$], [$-1$], [$0$], [$-1$], [$0$], [], [], [], [], [], [], [], [], [],
    )
  ]
]

#v(1em)

= 3. Sequent calculus: identity and structure

The sequent calculus *LU* is defined as follows: _sequents_ are of the form
$Gamma; Gamma' tack Delta'; Delta$ where $Gamma$, $Gamma'$, $Delta$ and $Delta'$ are sequences of formulas of the language.
The space between the two semi-colons is a space in which the usual structural
rules are available; the intended meaning of such a sequent is that of a proof
which is linear in $Gamma$ and $Delta$, i.e. in terms of linear logic of $Gamma, !Gamma' tack ?Delta', Delta$.

The rules of identity and structure are presented in Fig. 1. They are
independent of any commitment: these rules are meant for all formulas, and do
not refer to any distinction of the form _classical/intuitionistic/linear._ We have
adopted a two-sided version, which has the effect of doubling the number of
rules; a one-sided version would have been more economical, but we would had
to pay for this facility in the discussion of the intuitionistic fragment which would
look slightly artificial when written on the right. To compensate for this
complication, we decided to use an _additive_ maintenance for the central part of
sequents (the same $Gamma'$ and $Delta'$ in binary rules), which is possible since structural
rules are permitted in this area. Another notational trick would be (instead of the
semi-colon) to underline those formulas with a classical maintenance, which
would simplify the schematic writing of our rules, but would not change anything
deep, so this is really a matter of taste.

#v(0.8em)
#line(length: 100%, stroke: 0.5pt)
#v(0.3em)

#align(center)[#text(weight: "bold")[Identity]]

#align(center)[$A; tack ; A$]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, A$,
    $A, Lambda; Gamma' tack Delta'; Pi$,
    $Gamma, Lambda; Gamma' tack Delta'; Delta, Pi$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta', A; Delta$,
    $A; Gamma' tack Delta';$,
    $Gamma; Gamma' tack Delta'; Delta$,
  ))
  #h(2em)
  #prooftree(rule(
    $; Gamma' tack Delta'; A$,
    $Lambda; A, Gamma' tack Delta'; Pi$,
    $Lambda; Gamma' tack Delta'; Pi$,
  ))
]

#align(center)[#text(weight: "bold")[Structure]]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta$,
    $sigma(Gamma); sigma'(Gamma') tack tau'(Delta'); tau(Delta)$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta$,
    $Gamma; Gamma' tack A, Delta'; Delta$,
  ))
  #h(2em)
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta$,
    $Gamma; Gamma', A tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack A, A, Delta'; Delta$,
    $Gamma; Gamma' tack A, Delta'; Delta$,
  ))
  #h(2em)
  #prooftree(rule(
    $Gamma; Gamma', A, A tack Delta'; Delta$,
    $Gamma; Gamma', A tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; A, Delta$,
    $Gamma; Gamma' tack A, Delta'; Delta$,
  ))
  #h(2em)
  #prooftree(rule(
    $Gamma, A; Gamma' tack Delta'; Delta$,
    $Gamma; A, Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta', N; Delta$,
    $Gamma; Gamma' tack Delta'; N, Delta$,
  ))
  #h(2em)
  #prooftree(rule(
    $Gamma; P, Gamma' tack Delta'; Delta$,
    $Gamma, P; Gamma' tack Delta'; Delta$,
  ))
]

#v(0.3em)
#line(length: 100%, stroke: 0.5pt)
#align(center)[Fig. 1.]
#v(0.8em)

As expected, weakening and contraction are freely performed in the central
part of the sequent. Besides the exchange rules, which basically allow permuta-tion of formulas separated by a comma, we get additional _permeability_ rules,
which allow formulas to enter the central zone, and to exit from this zone under
some restriction on polarities. The last group of rules is the only one depending
on polarities.

The identity axiom is written in a pure linear maintenance. The case of cut is
more complex; in fact it falls into two cases, depending on the style of
maintenance for the two occurrences of $A$:
#set enum(start: 1)
+ if they are both linear (i.e. outside the central area), we obtain a rather
  expected rule;
+ if one of them is linear and the other 'classical' we obtain two symmetric
  forms of cut; observe that the premise containing the linear occurrence of $A$ is of
  the form $A; Gamma' tack Delta';$ or $; Gamma' tack Delta'; A$, i.e., the context of $A$ is handled classically.

There is no possibility of defining a cut between two occurrences of $A$ with a
classical maintenance. As a matter of fact, there is no need for that: typically in
classical logic, if we get a cut on $A$, then $A$ has a polarity $+1$ or $-1$, and one of
the two occurrences of $A$ can be handled linearily.

= 4. Logical rules: cases of linear connectives

The calculus presented in Fig. 2 seems rather heavy compared with the usual
formulation of linear logic; but this is just an unpleasant illusion due to the fact
that we have chosen a two-sided version more than twice the size of the one-sided
version.

As expected, the rules for quantifiers (right $⋀ x$ and left $⋁ x$) are subject to the
restriction on variables: $x$ not free in $Gamma; Gamma' tack Delta'; Delta$.

This calculus is equivalent to the usual linear logic; more precisely we can
translate the usual linear logic into this new system by declaring all atomic
propositions to be neutral. Then a sequent $Gamma tack Delta$ in the usual (two-sided) linear
logic becomes $Gamma; tack ; Delta$. It is easy to translate proof to proof, though the rules for
the exponentials ! and ? are translated by a heavy use of structural manipulations.
For instance, to pass from $!Gamma; tack ; ?Delta, A$ to $!Gamma; tack ; ?Delta, !A$, we transit through
$; !Gamma tack ?Delta; A$, then $; !Gamma tack ?Delta; !A$, and the ultimate moves to $!Gamma; tack ; ?Delta, !A$ use the
polarities of $?Delta$ and $!Gamma$.

Conversely, this new calculus (as long as we restrict ourselves to neutral atomic
propositions) can be translated into the usual linear logic as follows: a sequent
$Gamma; Gamma'_+, Gamma'' tack Delta''_?, Delta'_-; Delta$ ($Gamma'_+$ positive, $Delta'_-$ negative) translates as $Gamma, Gamma'_+, !Gamma'' tack ?Delta''_?, Delta'_-, Delta$
in the old syntax for linear logic. Then we have to mimick all rules of the new
calculus in the old one, which offers no difficulty. Of course, we have to prove in
the old calculus a stronger form of the rule for '!', namely that one can pass from
$Gamma tack Delta, A$ to $Gamma tack Delta, !A$, as soon as $Gamma$ is positive and $Delta$ negative. But since our atoms
are neutral, positive formulas are built from 0, 1, and formulas $!A$ by means of
$oplus, tensor$ and $exists x$ (and symmetrically for negative formulas), and we can make an
easy inductive argument.

Of all the logical rules of linear logic, only the rules for exponentials do
something to the central part: the right rule for '!' assumes that the context lies
wholly in the central part, whereas the left rule moves a formula from the central
area to the extreme left, at the price of a symbol '!'; the new formula $!A$ can now
pass the semi-colon in both ways.

#v(0.8em)
#line(length: 100%, stroke: 0.5pt)
#v(0.3em)

#align(center)[$ ; tack ; 1 quad quad bot; tack ; $]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, A$,
    $Lambda; Gamma' tack Delta'; Pi, B$,
    $Gamma, Lambda; Gamma' tack Delta'; Delta, Pi, A tensor B$,
  ))
  #h(2em)
  #prooftree(rule(
    $A, B, Gamma; Gamma' tack Delta'; Delta$,
    $A tensor B, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, A, B$,
    $Gamma; Gamma' tack Delta'; Delta, A ⅋ B$,
  ))
  #h(2em)
  #prooftree(rule(
    $A, Gamma; Gamma' tack Delta'; Delta$,
    $B, Lambda; Gamma' tack Delta'; Pi$,
    $A ⅋ B, Gamma, Lambda; Gamma' tack Delta'; Delta, Pi$,
  ))
]

#align(center)[
  #prooftree(rule(
    $A, Gamma; Gamma' tack Delta'; Delta, B$,
    $Gamma; Gamma' tack Delta'; Delta, A ⊸ B$,
  ))
  #h(2em)
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, A$,
    $B, Lambda; Gamma' tack Delta'; Pi$,
    $A ⊸ B, Gamma, Lambda; Gamma' tack Delta'; Delta, Pi$,
  ))
]

#align(center)[$ Gamma; tack ; Delta, top quad quad 0, Gamma; tack ; Delta $]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, A$,
    $Gamma; Gamma' tack Delta'; Delta, B$,
    $Gamma; Gamma' tack Delta'; Delta, A \& B$,
  ))
  #h(1.5em)
  #prooftree(rule(
    $A, Gamma; Gamma' tack Delta'; Delta$,
    $A \& B, Gamma; Gamma' tack Delta'; Delta$,
  ))
  #h(1.5em)
  #prooftree(rule(
    $B, Gamma; Gamma' tack Delta'; Delta$,
    $A \& B, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, A$,
    $Gamma; Gamma' tack Delta'; Delta, A oplus B$,
  ))
  #h(1em)
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, B$,
    $Gamma; Gamma' tack Delta'; Delta, A oplus B$,
  ))
  #h(1.5em)
  #prooftree(rule(
    $A, Gamma; Gamma' tack Delta'; Delta$,
    $B, Gamma; Gamma' tack Delta'; Delta$,
    $A oplus B, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, A$,
    $A^bot, Gamma; Gamma' tack Delta'; Delta$,
  ))
  #h(2em)
  #prooftree(rule(
    $A, Gamma; Gamma' tack Delta'; Delta$,
    $Gamma; Gamma' tack Delta'; Delta, A^bot$,
  ))
]

#align(center)[
  #prooftree(rule(
    $; Gamma' tack Delta'; A$,
    $; Gamma' tack Delta'; !A$,
  ))
  #h(2em)
  #prooftree(rule(
    $Gamma; A, Gamma' tack Delta'; Delta$,
    $!A, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta', A; Delta$,
    $Gamma; Gamma' tack Delta'; Delta, ?A$,
  ))
  #h(2em)
  #prooftree(rule(
    $A; Gamma' tack Delta';$,
    $?A; Gamma' tack Delta';$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, A$,
    $Gamma; Gamma' tack Delta'; Delta, ⋀ x A$,
  ))
  #h(2em)
  #prooftree(rule(
    $A[t/x], Gamma; Gamma' tack Delta'; Delta$,
    $⋀ x A, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, A[t/x]$,
    $Gamma; Gamma' tack Delta'; Delta, ⋁ x A$,
  ))
  #h(2em)
  #prooftree(rule(
    $A, Gamma; Gamma' tack Delta'; Delta$,
    $⋁ x A, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#v(0.3em)
#line(length: 100%, stroke: 0.5pt)
#align(center)[Fig. 2.]
#v(0.8em)

= 5. Some chimeric connectives

It is possible to define new connectives by pattern matching, i.e. by considering
polarities. Below, we shall consider only those connectives and quantifiers which
are of interest to classical and intuitionistic logics: these connectives are $and, or, =>,
not, bold(V), bold(F), forall x, exists x$ (classical), $sect, union, supset, ~, bold(V), bold(F), (x)$ and $(sans("E")x)$ (intuitionistic).
However, it turns out that $sect, union, bold(V), bold(F), (x)$ and $(sans("E")x)$ can be chosen to coincide
with $and, or, 1, 0, ⋀ x, exists x$; moreover, intuitionistic negation is better handled as
$~A : A supset 0$.

Our tables (see Tables 2 and 3) have been chosen so as to minimize the total
number of connectives, and to get as many denotational isomorphisms as
possible. It has not been possible to keep the same connective for implication
(owing to conflicts of polarities). Our classical implication has been made up from
$not A or B$ and is quite complicated; another one, built on $not(A and not B)$, would be
simpler, but the discussion is rather sterile since the difference cannot be noticed
on classical formulas.

The rules for our new connectives are presented in Fig. 3.

The author can be accused of bureaucracy: even if one regroups rules, their
number remains. . . frightening. Surely the fact that disjunction is defined by nine
independent cases counts for something in this inflation. However, observe that
these rules are always variations of the familiar rules for disjunction, and each
line differs from the other by a slightly different structural maintenance. Given a
concrete disjunction $A or B$, only one of these lines can work, i.e. at most three
rules as usual. Moreover, the usual fragments use at most four lines out of nine.
Also, these rules manage to unify classical and intuitionistic disjunction in the
same _associative_ connective, which is a nontrivial achievement.

#v(1em)

#align(center)[
  #text(size: 9pt)[
    Table 2 \
    Polarities for classical and intuitionistic connectives

    #v(0.3em)
    #table(
      columns: 8,
      align: center,
      stroke: 0.4pt,
      table.header([$A$], [$B$], [$A and B$], [$A or B$], [$A => B$], [$A supset B$], [$forall x A$], [$exists x A$]),
      [$+1$], [$+1$], [$+1$], [$+1$], [$-1$], [$0$], [$-1$], [$+1$],
      [$0$], [$+1$], [$+1$], [$+1$], [$+1$], [$0$], [$-1$], [$+1$],
      [$-1$], [$+1$], [$+1$], [$-1$], [$+1$], [$0$], [$-1$], [$+1$],
      [$+1$], [$0$], [$+1$], [$+1$], [$-1$], [$0$], [], [],
      [$0$], [$0$], [$0$], [$+1$], [$+1$], [$0$], [], [],
      [$-1$], [$0$], [$0$], [$-1$], [$+1$], [$0$], [], [],
      [$+1$], [$-1$], [$+1$], [$-1$], [$-1$], [$-1$], [], [],
      [$0$], [$-1$], [$0$], [$-1$], [$-1$], [$-1$], [], [],
      [$-1$], [$-1$], [$-1$], [$-1$], [$-1$], [$-1$], [], [],
    )
  ]
]

#v(1em)

#align(center)[
  #text(size: 9pt)[
    Table 3 \
    Classical and intuitionistic connectives defined in terms of linear logic

    #v(0.3em)
    #table(
      columns: 8,
      align: center,
      stroke: 0.4pt,
      table.header([$A$], [$B$], [$A and B$], [$A or B$], [$A => B$], [$A supset B$], [$forall x A$], [$exists x A$]),
      [$+1$], [$+1$], [$A tensor B$], [$A oplus B$], [$A ⊸ ?B$], [$A ⊸ B$], [$⋀ x ?A$], [$⋁ x A$],
      [$0$], [$+1$], [$!A tensor B$], [$!A oplus B$], [$!A^bot oplus B$], [$!A ⊸ B$], [$⋀ x ?A$], [$⋁ x !A$],
      [$-1$], [$+1$], [$!A tensor B$], [$A ⅋ ?B$], [$A^bot oplus B$], [$!A ⊸ B$], [$⋀ x A$], [$⋁ x !A$],
      [$+1$], [$0$], [$A tensor !B$], [$A oplus !B$], [$A ⊸ ?!B$], [$A ⊸ B$], [], [],
      [$0$], [$0$], [$A \& B$], [$!A oplus !B$], [$!A^bot oplus !B$], [$!A ⊸ B$], [], [],
      [$-1$], [$0$], [$A \& B$], [$A ⅋ ?!B$], [$A^bot oplus !B$], [$!A ⊸ B$], [], [],
      [$+1$], [$-1$], [$A tensor !B$], [$?A ⅋ B$], [$A ⊸ B$], [$A ⊸ B$], [], [],
      [$0$], [$-1$], [$A \& B$], [$?!A ⅋ B$], [$?!A^bot ⅋ B$], [$!A ⊸ B$], [], [],
      [$-1$], [$-1$], [$A \& B$], [$A ⅋ B$], [$!A ⊸ B$], [$!A ⊸ B$], [], [],
    )
  ]
]

#v(1em)

All other usual connectives coincide with one of those already introduced, with
the exception of intuitionistic negation: it is impossible to write its rules without
using the constant $bold(F)$ (or 0): this minor defect comes from our very cautious
treatment of structural rules; it is therefore better to consider $~$ as defined by
$~A := A supset bold(F)$.

= 6. Some properties of the calculus

First let us fix once for all a reasonable language:
- atomic predicates are given with their polarity ($+1, 0, -1$);
- two constants 0 and 1, both positive (also denoted $bold(F)$ and $bold(V)$);
- unary connectives: $!, (dot)^bot$ (also denoted $not$);
- binary connectives: $and, or, =>, supset, tensor, ⅋, ⊸, oplus, \&$;
- quantifiers: $forall x, exists x, ⋀ x, ⋁ x$.

#v(0.8em)
#line(length: 100%, stroke: 0.5pt)
#v(0.3em)

#align(center)[#text(weight: "bold")[Rules for conjunction]]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, P$,
    $Lambda; Gamma' tack Delta'; Pi, Q$,
    $Gamma, Lambda; Gamma' tack Delta'; Delta, Pi, P and Q$,
  ))
  #h(2em)
  #prooftree(rule(
    $P, Q, Gamma; Gamma' tack Delta'; Delta$,
    $P and Q, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $; Gamma' tack Delta'; A$,
    $Lambda; Gamma' tack Delta'; Pi, Q$,
    $Lambda; Gamma' tack Delta'; Pi, A and Q$,
  ))
  #h(2em)
  #prooftree(rule(
    $Q, Gamma; Gamma', A tack Delta'; Delta$,
    $A and Q, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, P$,
    $; Gamma' tack Delta'; B$,
    $Gamma; Gamma' tack Delta'; Delta, P and B$,
  ))
  #h(2em)
  #prooftree(rule(
    $P, Gamma; Gamma', B tack Delta'; Delta$,
    $P and B, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, A$,
    $Gamma; Gamma' tack Delta'; Delta, B$,
    $Gamma; Gamma' tack Delta'; Delta, A and B$,
  ))
  #h(1.5em)
  #prooftree(rule(
    $A, Gamma; Gamma' tack Delta'; Delta$,
    $A and B, Gamma; Gamma' tack Delta'; Delta$,
  ))
  #h(1.5em)
  #prooftree(rule(
    $B, Gamma; Gamma' tack Delta'; Delta$,
    $A and B, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[#text(size: 9pt, style: "italic")[Comments: $P, Q$ positive; $A, B$ not positive.]]

#align(center)[#text(weight: "bold")[Rules for intuitionistic implication]]

#align(center)[
  #prooftree(rule(
    $P, Gamma; Gamma' tack Delta'; Delta, B$,
    $Gamma; Gamma' tack Delta'; Delta, P supset B$,
  ))
  #h(2em)
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, P$,
    $B, Lambda; Gamma' tack Delta'; Pi$,
    $P supset B, Gamma, Lambda; Gamma' tack Delta'; Delta, Pi$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma', A tack Delta'; Delta, B$,
    $Gamma; Gamma' tack Delta'; Delta, A supset B$,
  ))
  #h(2em)
  #prooftree(rule(
    $; Gamma' tack Delta'; A$,
    $B, Lambda; Gamma' tack Delta'; Pi$,
    $A supset B, Lambda; Gamma' tack Delta'; Pi$,
  ))
]

#align(center)[#text(size: 9pt, style: "italic")[Comments: $P$ positive; $A$ not positive; $B$ arbitrary.]]

#align(center)[#text(weight: "bold")[Rules for "$forall$"]]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta', A; Delta$,
    $Gamma; Gamma' tack Delta'; Delta, forall x A$,
  ))
  #h(2em)
  #prooftree(rule(
    $A[t/x]; Lambda' tack Pi';$,
    $forall x A; Lambda' tack Pi';$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, N$,
    $Gamma; Gamma' tack Delta'; Delta, forall x N$,
  ))
  #h(2em)
  #prooftree(rule(
    $N[t/x], Lambda; Lambda' tack Pi'; Pi$,
    $forall x N, Lambda; Lambda' tack Pi'; Pi$,
  ))
]

#align(center)[#text(size: 9pt, style: "italic")[Comments: $A$ not negative; $N$ negative; $x$ not free in $Gamma; Gamma' tack Delta'; Delta$.]]

#v(0.3em)
#line(length: 100%, stroke: 0.5pt)
#align(center)[Fig. 3.]
#v(0.8em)

#line(length: 100%, stroke: 0.5pt)
#v(0.3em)

#align(center)[#text(weight: "bold")[Rules for disjunction]]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, P$,
    $Gamma; Gamma' tack Delta'; Delta, P or Q$,
  ))
  #h(1em)
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, Q$,
    $Gamma; Gamma' tack Delta'; Delta, P or Q$,
  ))
  #h(1.5em)
  #prooftree(rule(
    $P, Gamma; Gamma' tack Delta'; Delta$,
    $Q, Gamma; Gamma' tack Delta'; Delta$,
    $P or Q, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $; Gamma' tack Delta'; S$,
    $; Gamma' tack Delta'; S or Q$,
  ))
  #h(1em)
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, Q$,
    $Gamma; Gamma' tack Delta'; Delta, S or Q$,
  ))
  #h(1.5em)
  #prooftree(rule(
    $Gamma; S, Gamma' tack Delta'; Delta$,
    $Q, Gamma; Gamma' tack Delta'; Delta$,
    $S or Q, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta', Q; Delta, M$,
    $Gamma; Gamma' tack Delta'; Delta, M or Q$,
  ))
  #h(2em)
  #prooftree(rule(
    $M, Gamma; Gamma' tack Delta'; Delta$,
    $; Gamma', Q tack Delta';$,
    $M or Q, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, P$,
    $Gamma; Gamma' tack Delta'; Delta, P or T$,
  ))
  #h(1em)
  #prooftree(rule(
    $; Gamma' tack Delta'; T$,
    $; Gamma' tack Delta'; P or T$,
  ))
  #h(1.5em)
  #prooftree(rule(
    $P, Gamma; Gamma' tack Delta'; Delta$,
    $Gamma; Gamma', T tack Delta'; Delta$,
    $P or T, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $; Gamma' tack Delta'; S$,
    $; Gamma' tack Delta'; S or T$,
  ))
  #h(1em)
  #prooftree(rule(
    $; Gamma' tack Delta'; T$,
    $; Gamma' tack Delta'; S or T$,
  ))
  #h(1.5em)
  #prooftree(rule(
    $Gamma; S, Gamma' tack Delta'; Delta$,
    $Gamma; Gamma', T tack Delta'; Delta$,
    $S or T, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, M$,
    $Gamma; Gamma' tack Delta'; Delta, M or T$,
  ))
  #h(1em)
  #prooftree(rule(
    $; Gamma' tack Delta'; M, T$,
    $; Gamma' tack Delta'; M or T$,
  ))
  #h(1.5em)
  #prooftree(rule(
    $M, Gamma; Gamma' tack Delta'; Delta$,
    $; Gamma', T tack Delta';$,
    $M or T, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack P, Delta'; Delta, N$,
    $Gamma; Gamma' tack Delta'; Delta, P or N$,
  ))
  #h(2em)
  #prooftree(rule(
    $P; Gamma' tack Delta';$,
    $N, Lambda; Gamma' tack Delta'; Pi$,
    $P or N, Lambda; Gamma' tack Delta'; Pi$,
  ))
]

#align(center)[
  #prooftree(rule(
    $; Gamma' tack Delta'; S, N$,
    $; Gamma' tack Delta'; S or N$,
  ))
  #h(1em)
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, N$,
    $Gamma; Gamma' tack Delta'; Delta, S or N$,
  ))
  #h(1.5em)
  #prooftree(rule(
    $; Gamma', S tack Delta';$,
    $N, Lambda; Gamma' tack Delta'; Pi$,
    $S or N, Lambda; Gamma' tack Delta'; Pi$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, M, N$,
    $Gamma; Gamma' tack Delta'; Delta, M or N$,
  ))
  #h(2em)
  #prooftree(rule(
    $M, Gamma; Gamma' tack Delta'; Delta$,
    $N, Lambda; Gamma' tack Delta'; Pi$,
    $M or N, Gamma, Lambda; Gamma' tack Delta'; Delta, Pi$,
  ))
]

#align(center)[#text(size: 9pt, style: "italic")[Comments: $P, Q$ positive; $M, N$ negative; $S, T$ neutral.]]

#align(center)[#text(weight: "bold")[Rules for "$exists$"]]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, P[t/x]$,
    $Gamma; Gamma' tack Delta'; Delta, exists x P$,
  ))
  #h(2em)
  #prooftree(rule(
    $P, Lambda; Lambda' tack Pi'; Pi$,
    $exists x P, Lambda; Lambda' tack Pi'; Pi$,
  ))
]

#align(center)[
  #prooftree(rule(
    $; Gamma' tack Delta'; A[t/x]$,
    $; Gamma' tack Delta'; exists x A$,
  ))
  #h(2em)
  #prooftree(rule(
    $Lambda; A, Lambda' tack Pi'; Pi$,
    $exists x A, Lambda; Lambda' tack Pi'; Pi$,
  ))
]

#align(center)[#text(size: 9pt, style: "italic")[Comments: $P$ positive, $A$ not positive, $x$ not free in $Lambda; Lambda' tack Pi'; Pi$.]]

#v(0.3em)
#line(length: 100%, stroke: 0.5pt)
#align(center)[Fig. 3 (contd.).]
#v(0.8em)

#line(length: 100%, stroke: 0.5pt)
#v(0.3em)

#align(center)[#text(weight: "bold")[Rules for classical implication]]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, P$,
    $Gamma; Gamma' tack Delta'; Delta, N => P$,
  ))
  #h(1em)
  #prooftree(rule(
    $N, Gamma; Gamma' tack Delta'; Delta$,
    $Gamma; Gamma' tack Delta'; Delta, N => P$,
  ))
  #h(1.5em)
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, N$,
    $P, Gamma; Gamma' tack Delta'; Delta$,
    $N => P, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $P, Gamma; Gamma' tack Q, Delta'; Delta$,
    $Gamma; Gamma' tack Delta'; Delta, P => Q$,
  ))
  #h(2em)
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, P$,
    $Q; Gamma' tack Delta';$,
    $P => Q, Gamma; Gamma' tack Delta'; Delta$,
  ))
]

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma', M tack Delta'; Delta, N$,
    $Gamma; Gamma' tack Delta'; Delta, M => N$,
  ))
  #h(2em)
  #prooftree(rule(
    $; Gamma' tack Delta'; M$,
    $N, Lambda; Gamma' tack Delta'; Pi$,
    $M => N, Lambda; Gamma' tack Delta'; Pi$,
  ))
]

#align(center)[
  #prooftree(rule(
    $P, Gamma; Gamma' tack Delta'; Delta, N$,
    $Gamma; Gamma' tack Delta'; Delta, P => N$,
  ))
  #h(2em)
  #prooftree(rule(
    $Gamma; Gamma' tack Delta'; Delta, P$,
    $N, Lambda; Gamma' tack Delta'; Pi$,
    $P => N, Gamma, Lambda; Gamma' tack Delta'; Delta, Pi$,
  ))
]

#v(0.3em)
#text(size: 9pt)[
  _Comments:_ $P, Q$ positive, $M, N$ negative; this set of rules is incomplete (we have omitted the rules
  involving neutral formulas, for which there is no use at present; the reader may reconstitute them
  from the rules of disjunction). Observe that the four rules written would have been the same if
  implication had been defined from conjunction.
]

#v(0.3em)
#line(length: 100%, stroke: 0.5pt)
#align(center)[Fig. 3 (contd.).]
#v(0.8em)

We now define remarkable fragments; they are all defined by a restriction of
the possible atomic formulas and of the possible connectives and quantifiers:

#set enum(numbering: "(1)", indent: 1em, start: 1)
+ *The classical fragment:* \
  positive and negative atoms (including $bold(V)$ and $bold(F)$); closed under $not, and, or, =>, forall x$ and $exists x$.

+ *The intuitionistic fragment:* \
  positive and neutral atoms (including $bold(V)$ and $bold(F)$); closed under $and, or, supset, ⋀ x, exists x$.

+ *The neutral intuitionistic fragment:* \
  neutral atoms; closed under $and, supset, ⋀ x$.

+ *The linear fragment:* \
  all atoms; closed under $(dot)^bot, tensor, ⅋, ⊸, oplus, \&, !, ?, ⋀ x, ⋁ x$.

The interest of these various fragments is that they enable us to formalise
arguments belonging to various logical systems inside *LU*, with the advantage of a
unique proof-maintenance. Each fragment uses a very small part of our _kolossal_
sequent calculus. But *LU* is not the union of its fragments: there must be
interesting formulas outside of these fragments (and also other interesting
fragments; for instance a positive intuitionistic fragment based on the implication
$!(A ⊸ B)$ should be investigated).

The classical fragment is based on the idea of staying within the positive or
negative formulas; the intuitionistic fragment stays within the positive and neutral
formulas; the neutral intuitionistic fragment is wholly neutral; the linear fragment
admits all three polarities.

An important property of these fragments is the _substitution property:_ let $a$ be a
proper predicate symbol of arity $n$, and let $A$ be a formula of the same polarity as
$a$, in which distinct free variables $x_1, dots, x_n$ have been distinguished. Then one
can define for any formula $B$ the substitution $B[lambda x_1, dots, x_n . A / a]$ as the result of
replacing any atom $a t_1 dots t_n$ of $B$ by $A[t_1, dots, t_n]$ (with usual precautions
concerning free and bound variables, comrade Tchenienko). All the fragments
considered are closed under mutual substitution.

Each fragment gets its own notion of sequent: first all formulas must belong to
the fragment; but some additional properties may be required:
#set enum(numbering: "(i)", indent: 1em, start: 1)
+ A classical sequent $Gamma; Gamma' tack Pi'; Pi$ is such that if we make the sum of the
  number of negative formulas in $Gamma$ and of positive formulas in $Pi$, we get the total
  number 0 or 1.
+ An intuitionistic sequent is of the form $Gamma; Gamma' tack ; A$.
+ A neutral intuitionistic sequent is a sequent $Gamma; Gamma' tack ; A$, with at most one
  formula in $Gamma$.

#v(0.5em)
*Theorem.* _If a sequent of one of the fragments considered provable, it is provable within the fragment._
#v(0.5em)

_Proof._ We limit our search to cut-free proofs; by the subformula property, all the
formulas occurring in the proofs belong to the fragment; in particular this is
enough for linear logic, since no additional restriction has been imposed on linear
sequents. Let us consider the remaining cases: in all cases we have to check that
the restriction on the shape of the sequent can be forwarded from the conclusion
to the premise(s).

_Neutral intuitionistic fragment._ First observe that the restriction "$Delta'$ empty"
will be easily forwarded (this holds for both intuitionistic fragments). Then
observe that for any cut-free rule of *LU* ending with a neutral intuitionistic
sequent $Gamma; Gamma' tack ; S$,
- all premises are of the form $Lambda; Lambda' tack ; T$,
- one of these premises, say $Lambda; Lambda' tack ; T$, is such that the number of formulas in $Lambda$
  is greater or equal to the number of formulas in $Gamma$, with only one exception,
  namely the identity axiom. In particular there is no way to prove a sequent
  $Gamma; Gamma' tack ; S$ of formulas in this fragment when $Gamma$ has two formulas or more; the
  formula of $Gamma$ (if there is one) is the analogue of the familiar _headvariable_ of typed
  $lambda$-calculi, which are based on neutral intuitionistic fragments.

This proves that all premises of the rule must be also neutral intuitionistic
sequents.

_Classical fragment._ If $S$ is the sequent $Gamma; Gamma' tack Delta'; Delta$ let us define $mu(S)$ to be the
sum of the number of negative formulas in $Gamma$ and of positive formulas in $Delta$. Now
for any rule with a conclusion $S$ made of classical formulas and such that
$mu(S) > 1$, there is premise $S'$ such that $mu(S') >= mu(S)$, with only one exception:
the axiom $bold(F), Gamma; tack ; Delta$. Furthermore, there are only two rules with a premise $S'$ and
a conclusion $S$ such that $mu(S') > mu(S)$: the two permeability rules enabling a
formula to enter the central zone. Now it is an easy exercise, given any cut-free
proof of a sequent $S$ made of classical formulas with $mu(S) > 1$, to produce another
proof of any sequent $S'$ obtained by removing as many formulas among those
which contribute to $mu(S)$. In particular, a 'bad' permeability rule can be replaced
with a weakening and so we stay among classical sequents.

_Intuitionistic fragment._ If $nu(S)$ counts the number of formulas in the part $Delta$ of a
sequent $S = Gamma; Gamma' tack ; Delta$, then the restriction $nu(S) <= 1$ is forwarded from the
conclusion to the premises of all rules involving intuitionistic formulas but for the
case of a rule

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack ; C, P$,
    $B, Lambda; Gamma' tack ;$,
    $P supset B, Gamma, Lambda; Gamma' tack ; C$,
  ))
]

Easy commutation arguments reduce the use of this rule to the case where $C$ is
positive or atomic. From this it can be ensured that all sequents with $nu(S) > 1$
occurring in the proof of an intuitionistic sequent have a succedent made of
positive or atomic formulas. Now one can easily produce given a proof of a
sequent $Gamma; Gamma' tack ; Delta$ with $nu(Delta) != 1$ (this includes $nu(Delta) = 0$) and all formulas
intuitionistic, another proof of $Gamma; Gamma' tack ; Pi$ where $Pi$ has been obtained from $Delta$ by
adding formulas, or removing atomic or positive ones. In particular, we can
replace the 'bad' rule above by the 'good' one:

#align(center)[
  #prooftree(rule(
    $Gamma; Gamma' tack ; P$,
    $B, Lambda; Gamma' tack ; C$,
    $P supset B, Gamma, Lambda; Gamma' tack ; C$,
  ))
]

and this shows that we can stay within the intuitionistic sequents. #h(1fr) $square$

#v(0.5em)

*Remarks.* (i) We implicitly used a cut-elimination theorem for *LU* that is more
or less obvious (but perhaps a bit too long to write down explicitly).#footnote[See forthcoming paper by J. Vauzeilles to appear in this journal.] \
(ii) The results of the theorem concern not only provability, but also proofs, in
the sense of denotational semantics; there would be nothing to prove in the
classical and the intuitionistic case if the constant 0 were not allowed (only the
axioms involving 0 and its negation prevent us to draw conclusions like in the
neutral fragment). Now the proofs we look at with the wrong $mu(S)$ or $nu(S)$ are in
fact interpreted in a coherent space with an empty web: all proofs of such
sequents are denotationally equal, and we therefore replace a proof by another
one with the same semantics! \
(iii) The paper of Schellinx [4] investigates the faithfulness of the translation
intuitionistic $|->$ linear and our proof is roughly inspired from this paper.

Now, it remains to compare the systems *LU* restricted to various fragments
with the sequent calculi for the corresponding logics:
#set enum(start: 1)
+ The two intuitionistic fragments are OK: just translate $Gamma; Gamma' tack ; A$ as $Gamma, Gamma' tack A$
  and observe that all rules are correct. The other way around might be slightly
  more delicate at least if we investigate cut-free provability.
+ The classical fragment translates not to LK, but to LC (see [3]); more
  precisely besides the superficial difference one-sided/two sided, LC uses the
  semi-colon in a different way: one tries to put as many formulas as possible in the
  central zone: in particular, starting with $Gamma; Gamma' tack Delta'; Delta$, the idea is to move all
  positive formulas from $Gamma$ to the right, and all negative formulas of $Delta$ to the left:
  with the result that $Gamma, Delta$ can consist of at most one formula.

= Conclusion

As a matter of conclusion let us observe that this attempt at unification is
orthogonal to synchretic attempts of the style 'logical framework': too often
unification is at the price of a loss of structure (we lose properties: cut-elimination, nay consistency). Here it goes the other way around. All fragments
considered are better as subsystems of *LU* than they were as isolated systems:
#set enum(start: 1)
+ Classical logic is handled by LC which is much better than LK.
+ The neutral intuitionistic fragment gets a legalisation of the notion of
  _headvariable_ and its normalisation procedure should be of the style 'linear
  head-reduction'.
+ The intuitionistic fragment gets a subtler approach to pattern-matching,
  typically a denotationally associative disjunction.
+ Linear logic gets a smoother sequent calculus, in particular for exponential
  connectives; this formulation has some similarities with the linear sequent calculi
  proposed by Andréoli and Pareschi [1].

. . . Not to speak of the fact that all these systems are part of the same calculus,
i.e., are free to interact . . . .

There is of course the obvious question: is this _LOGIC,_ i.e., did we catch here
all possible logical systems? Surely not, and there are additional parameters on
which one can play to broaden the scope of a unified approach to logic:
#set enum(start: 1)
+ The consideration of additional polarities: a polarity can be abstractly seen
  as the permission to perform certain structural rules on the left or the right of a
  sequent. Many other cocktails (from the absolute noncommutative polarity to
  classical polarities) are possible, and all the combinations between weakening,
  exchange and contraction yield up to 15 possible polarities. Most of these
  combinations presumably make no sense, and one should not hurry to invent
  polarities with no concrete application. However, if one insists on experimenting
  in that way, it seems that a good criterion for the consideration of additional
  polarities could be the possibility of extending the definition of disjunction so as
  to preserve its denotational associativity.
+ The extension of these results to systems which have always been on the
  border line of logic: systems of arithmetic, and more generally inductive
  definitions.
+ The extension to second-order; in particular, it will be possible to cope
  with the loss of subformula property by considering quantifications ranging on
  various fragments (example: for all positive and classical $alpha$).

#v(1.5em)
#align(center)[*NON SI NON LA*]
#v(1.5em)

= References

#set par(hanging-indent: 2em, justify: false)
[1] J.-M. Andréoli and R. Pareschi, Linear objects: logical processes with built-in inheritance, to appear in _New Generation Computing_ (1991).

[2] J.-Y. Girard, Linear logic, _Theoret. Comput. Sci._ 50 (1987) 1--102.

[3] J.-Y. Girard, A new constructive logic: classical logic, Preprint, université Paris VII, March 1991, to appear in _Math. Structures Comput. Sci._ 1(3).

[4] H. Schellinx, Some syntactical observations on linear logic, Preprint 1990, to appear in _J. Logic and Computation,_ 1991.