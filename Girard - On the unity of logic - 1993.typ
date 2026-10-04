// Document setup
#let horizontalrule = [
  #line(start: (25%,0%), end: (75%,0%))
]

#let endnote(num, contents) = [
  #stack(dir: ltr, spacing: 3pt, super[#num], contents)
]
#show terms: it => {
  it.children
    .map(child => [
      #strong[#child.term]
      #block(inset: (left: 1.5em, top: -0.4em))[#child.description]
      ])
    .join()
}

#set table(
  inset: 6pt,
  stroke: none
)

#show figure.where(
  kind: table
): set figure.caption(position: top)

#show figure.where(
  kind: image
): set figure.caption(position: bottom)

#let content-to-string(content) = {
  if content.has("text") {
    content.text
  } else if content.has("children") {
    content.children.map(content-to-string).join("")
  } else if content.has("body") {
    content-to-string(content.body)
  } else if content == [ ] {
    " "
  }
}
#let conf(
  title: none,
  subtitle: none,
  authors: (),
  keywords: (),
  date: none,
  abstract: none,
  cols: 1,
  margin: (x: 1.25in, y: 1.25in),
  paper: "us-letter",
  lang: "en",
  region: "US",
  font: ("New Computer Modern",),
  fontsize: 11pt,
  sectionnumbering: none,
  doc,
) = {
  set document(
    title: title,
    author: authors.map(author => content-to-string(author.name)),
    keywords: keywords,
  )
  set page(
    paper: paper,
    margin: margin,
    numbering: "1",
  )
  set par(justify: true)
  set text(lang: lang,
           region: region,
           font: font,
           size: fontsize)
  set heading(numbering: sectionnumbering)

  if title != none {
    align(center)[#block(inset: 2em)[
      #text(weight: "bold", size: 1.5em)[#title]
      #(if subtitle != none {
        parbreak()
        text(weight: "bold", size: 1.25em)[#subtitle]
      })
    ]]
  }

  if authors != none and authors != [] {
    let count = authors.len()
    let ncols = calc.min(count, 3)
    grid(
      columns: (1fr,) * ncols,
      row-gutter: 1.5em,
      ..authors.map(author =>
          align(center)[
            #author.name \
            #author.affiliation \
            #author.email
          ]
      )
    )
  }

  if date != none {
    align(center)[#block(inset: 1em)[
      #date
    ]]
  }

  if abstract != none {
    block(inset: 2em)[
    #text(weight: "semibold")[Abstract] #h(1em) #abstract
    ]
  }

  if cols == 1 {
    doc
  } else {
    columns(cols, doc)
  }
}
#show: doc => conf(
  cols: 1,
  doc,
)


Logic 59 (1993) 201-217

201

Annals of Pure and Applied North-Holland

= On the unity of logic
<on-the-unity-of-logic>
== Jean-Yves Girard
<jean-yves-girard>
#strong[#emph[gquipe de Logique, UA 753 du CNRS Mathtkatiques,
Universitt? Paris VII, t. 45-55, 5” &age, 2place Jussieu, 75251 Paris
Cedex 05, France];]

Communicated by D. van Dalen Received 20 June 1991

==== #strong[#emph[Abstract];]
<abstract>
Girard, J.-Y., On the unity of logic, Annals of Pure and Applied Logic
59 (1993) 201-217

We present a single sequent calculus common to classical, intuitionistic
and linear logics. The main novelty is that classical, intuitionistic
and linear logics appear as #strong[#emph[fragments,];] i.e.~as
particular classes of formulas and sequents. For instance, a proof of an
intuitionistic formula #strong[#emph[A];] may use classical or linear
lemmas without any restriction: but after cut-elimination the proof of
#strong[#emph[A];] is wholly intuitionistic, what is superficially
achieved by the subformula property (only intuitionistic formulas are
used) and more deeply by a very careful treatment of structural rules.
This approach is radically different from the one that consists in
"changing the rule of the game" when we want to change logic, e.g.~pass
from one style of sequent to another: here, there is only one logic,
which-depending on its use-may appear classical, intuitionistic or
linear.

Nous prtsentons un calcul des sequents unifit, commun aux logiques
classique, intuitionniste et lintaire. La principale nouveaute est que
les logiques classique, intuitionniste et lineaire apparaissent comme
des #strong[#emph[fragments,];] c’est h dire comme des classes
particulieres de formules et de sequents. Par exemple la demonstration
d’un &once intuitionniste pourra utiliser des lemmes classiques ou
intuitionnistes sans limitation: simplement apres elimination des
coupures, la demonstration se fera entierement dans le fragment
intuitionniste, ce qui est superficiellement assure par la propriett de
la sous-formule (seulement des formules intuitionnistes sont utilisees)
et plus profondement par un traitement tres rigoureux des regles
structurelles. Cette approche est radicalement differente de I’approche
habituelle qui consiste tout bonnement a changer la regle du jeu quand
on veut changer de logique, c’est a dire de style de sequent: ici il n’y
a plus qu’une seule logique, qui au grC des utilisations peut apparaitre
classique, intuitionniste ou lineaire.

By the turn of this century the situation concerning logic was quite
simple: there was basically one logic (classical logic) which could be
used (by changing the set of proper axioms) in various situations. Logic
was about #strong[#emph[pure];] reasoning. Brouwer’s criticism destroyed
this dream of unity: classial logic was not suited for constructive
features and therefore it lost its universality. Now by the end of the
#strong[#emph[Correspondence to:];] J.-Y. Girard, Mathematiques Disc&es,
UPR A9016, 163 Av. de Luminy, case 930, 13288 Marseille Cedex 09,
France.

016%0072/93/\$06.00 0 1993 - Elsevier Science Publishers B.V. All rights
reserved

#strong[#emph[J.-Y. Girard];]

#strong[#emph[202];]

century we are faced with an incredible number of logics-some of them
only named 'logic' by antiphrasis, some of them introduced on serious
grounds. Is logic still about pure reasoning? In other words, could
there by a way to reunify logical systems-let us say those systems with
a good sequent calculusinto a single sequent calculus ? Is it possible
to handle the (legitimate) distinction classical/intuitionistic not
through a change of system, but through a change of formulas? Is it
possible to obtain classical effects by a restriction to classical
formulas? Etc.

Of course, there surely are ways to achieve this by cheating, typically
by considering a disjoint union of systems. However, all these jokes
will be made impossible if we insist on the fact that the various
systems represented should communicate freely (and for instance a
classical theorem could have an intuitionistic corollary and vice
versa).

In the unified calculus #strong[LU] that we present in this paper,
classical, linear and intuitionistic logics appear as
#strong[#emph[fragments.];] This means that one can define notions of
#strong[#emph[classical, intuitionistic];] or #strong[#emph[linear];]
sequents and prove that a cut-free proof of a sequent in one of these
fragments is wholly inside the fragment; of course a proof with cuts has
the right to use arbitrary sequents, i.e., the fragments can freely
communicate.

=== #strong[\1. Unified sequents]
<unified-sequents>
Standard sequent calculi essentially differ by their different
maintenances of

sequents:

#block[
#set enum(numbering: "(i)", start: 1)
+ classical logic accepts weakening and contraction on both sides; (ii)
  intuitionistic (minimal) logic restricts the succedent to one
  formulawhich has the effect of forbidding weakening and contraction to
  the right; (iii) linear logic refuses both, but has special
  connectives ! and ? which - when prefixed to a formula - allow
  structural rules on the left (!) and on the right (?). Our basic
  unifying idea will be to define two zones in a sequent: a zone with a
  'classical' maintenance, and a zone with a linear maintenance; there
  will be no zone with an intuitionistic maintenance: intuitionistic
  maintenance, i.e.~'one formula on the right', will result from a
  careful linear maintenance. Typically, we could use a notation T;I” F
  A’;A to indicate that r’ and A’ behave classically, whereas r and A
  behave linearly. We could try to identify classical sequents with
  those where r and A are empty, and intuitionistic ones as those in
  which r and #strong[#emph[A’];] are empty, A consisting of one
  formula. This is roughly what will happen, with some difficulties and
  some surprises:

+ It must be possible to pass between both sides of the semi-colon:
  surely one should be able to enter the central zone (we lose
  information), and alsowith some constraint, otherwise the semi-colon
  would lose its importanceto move to the extremes. One of these
  constraints could be the addition of a symbol, e.g.~move
  #strong[#emph[A];] from I” to r, but now write it as
  #strong[#emph[!A.];]
]

#strong[#emph[On the unity of logic];]

#strong[203]

#block[
#set enum(numbering: "(i)", start: 2)
+ This is not quite satisfactory; typically, a formula already starting
  with '!' should be able to pass freely. However, it immediately turns
  out that those guys that can cross the left semi-colon in both ways
  are closed under the linear connectives 63) and \$ and under the
  quantifier Vx. The sensible thing to do is therefore to distinguish
  among formulas #strong[#emph[positive];] ones, including positive
  atomic formulas for problems of substitution. Symmetrically, one
  distinguishes #strong[#emph[negative];] formulas, while the remaining
  ones are called #strong[#emph[neutral:];] those must pay at both
  borders.

+ The restatement of the rules of linear logic in this wider context is
  unproblematic and rather satisfactory, especially the treatment of '!'
  and '?' becomes slightly smoother. (iv) We now have to define three
  #strong[#emph[polarities];] (classes of formulas) and we can toy with
  the connectives of linear logic to define synthetic connectives, built
  like #strong[#emph[chimeras,];] with a head of 8, a tail of &, etc.
  \-only good taste limits the possibilities. Typically, if we want to
  define a conjunction we would like it to be associative (at the level
  of provability, but moreover at the level of denotational semantics),
  hence this imposes some coordination between the various parts of our
  chimera. In fact the connectives built have been chosen under two
  constraints:
]

\-limitation of the number of connectives: for instance only one
conjunction, only one disjunction, for classical and intuitionistic
logics, but unfortunately two distinct implications for these logics;

- maximimisation of the number of remarkable isomorphisms. (v) As far as
  classical logic is concerned, the results presented here are
  consistent with the previous work of the author \[3\]; in fact
  classical logic is obtained by limitation to formulas which are
  (hereditarily) nonneutral. The role of classical sequents is played by
  the sequents of the form T;T’ t #strong[#emph[A’;A];] when the
  nonpermeable part of r, #strong[#emph[A];] consists of at most one
  formula (the #strong[#emph[stoup];] of \[3\]). The reader is referred
  to this paper to check the extreme number of isomorphisms satisfied by
  the classical fragment (some of them, typically the De Morgan duality
  between A and v, do not extend to neutral polarities). There is only
  one small defect: a single formula #strong[#emph[A];] is interpreted
  by #strong[#emph[; IA;];] whereas for the other logics, it is
  interpreted by #strong[#emph[; t ;A.];] However, if #strong[#emph[A];]
  is negative (right permeable) we can replace #strong[#emph[; t-A;];]
  by ; k ;A, and if #strong[#emph[A];] is positive we can replace
  #strong[#emph[;];] t A; by #strong[#emph[; k ; Vx A (x];] dummy) or
  #strong[#emph[;I-;A v];] (TV).

#block[
#set enum(numbering: "(i)", start: 6)
+ As far as disjunction, existence and negation are ignored,
  intuitionistic logic is a quite even system in proof-theoretic terms,
  as shown by various relations to k-calculus. The #strong[#emph[neutral
  intuitionistic];] fragment is made of (hereditarily) neutral formulas,
  and basically accepts intuitionistic 2, A and Ax; besides sequents
  ;I’t #strong[#emph[;B];] which were expected, there arise sequents
  #strong[#emph[A;Tt ;B];] corresponding to the notion of
  #strong[#emph[headvariable.];] Not only the usual intuitionistic
  sequent calculus is recovered, but it is improved! (vii) Surely less
  perfect is the full intuitionistic system with v, 3x and F (i.e.~
]

#strong[#emph[J.-Y. Girard];]

#strong[#emph[204];]

negation); the translation of this system into linear logic (the
starting point of linear logic, see \[2\]) made use of the combination
#strong[#emph[!A \@ !B,];] which is awfully nonassociative
(denotationally speaking): compare #strong[#emph[!(!A 63 !B) G3 !C];]
with #strong[#emph[!A f?3 !(!B \@ !C).];] However, one could use
#strong[#emph[A];] instead of #strong[#emph[!A];] if #strong[#emph[A];]
were known to be positive. Therefore there is room for an associative
disjunction provided we consider not only neutral formulas, but also
positive ones. The resulting disjunction is a very complex chimera which
manages to be associative and commutative, and also works in the
classical case. We surely do not get as many denotational isomorphisms
as we would like (typically there is no unit for the disjunction, or
#strong[#emph[A I\> B A C ^- (A I B) A (A I C)];] only when
#strong[#emph[B];] and C are neutral), but the situation is incredibly
better than expected. In terms of sequents, we lose the phenomenon of
'headvariable', since a term may be linear in several of its variables
if we perform iterated pattern-matchings. The system presented here is
rather big, for the reason that we used a two-sided version to
accommodate intuitionistic features more directly, and because there are
classical, intuitionistic and linear connectives; last, but not least
rules can split into several cases depending on polarities; the rules
for disjunction, for instance, fill a whole page! But this complication
is rather superficial: it is more convenient to use the same symbol for
nine 'micro-connectives' corresponding to all possible polarities of the
disjuncts. Given #strong[#emph[A];] and #strong[#emph[B, we];] get at
most two possible right rules and only one left rule, as usual. So
#strong[LU] has a very big number of connectives but apart from this it
is a quite even sequent calculus.

=== 2. #strong[Polarities]
<polarities>
Each formula is given with a polarity +1 (positive), 0 (neutral), -1
(negative). We use the following notational trick to indicate
polarities: #strong[#emph[P, Q, R];] for positive formulas, S,
#strong[#emph[T, U];] for neutral formulas, #strong[#emph[L, M, N];] for
negative formulas. When we want to ignore the polarity, we shall use the
letters #strong[#emph[A, B, C.];] Semantically speaking, a neutral
formula refers to a coherent space; a positive formula refers to a
positive correlation space, and a negative formula to a negative
correlation space (see \[3\] for a definition). Now remember that a
correlation space is a coherent space plus extra structure (in fact PCS
generalise spaces of the form !X, and NCS generalise spaces ?X; both are
about structural rules: a PCS is a space with left structural rules, a
NCS obeys right structural rules); this explains the polaritiy table
(see Table 1) for linear logic: we first combine the underlying coherent
spaces S and #strong[#emph[T];] to get a coherent space U (e.g.~U = S 8
#strong[#emph[T),];] and if possible we try to endow U with a canonical
structure of correlation space (typically, if S and #strong[#emph[T];]
are underlying coherent spaces for PCS #strong[#emph[P];] and Q, we
equip S 8 #strong[#emph[T];] with a structure of PCS in the obvious
way). Before we start, we have to make a choice about polarity 0: do we
consider the possibility that something of polarity +1 (or -1) has also
polarity O? In that case

#emph[On the unity of logic]

205

Table 1 Polarities for linear connectives

#figure(
  align(center)[#table(
    columns: 7,
    align: (auto,auto,auto,auto,auto,auto,auto,),
    table.header([#strong[\=];A], [#strong[\=I];B], [#strong[\=-];], [], [], [], [],),
    table.hline(),
    [+l], [+l], [], [], [], [], [],
    [0], [+1], [], [], [], [], [],
    [-1], [+l], [0], [0], [0], [0], [0],
    [+l], [0], [0], [0], [0], [0], [0],
    [0], [0], [0], [0], [0], [0], [0],
    [-1], [0], [0], [0], [0], [0], [0],
    [+1], [-1], [#strong[0];], [0], [-1], [0], [0],
    [0], [-1], [], [], [], [], [],
    [-1], [-1], [], [], [], [], [],
  )]
  , kind: table
  )

it would be normal to indicate that we decide to forget the nonzero
polarity, causing complications and more complications. In fact, if we
decide to answer No, we get a quite reasonable answer: in linear logic
we can forget negative polarity by forming #strong[#emph[A \@ 1,];] and
a positive one by forming #strong[#emph[A 42 I,];] hence if I replace
#strong[#emph[A];] by \*\*\_(A #cite(<_>, form: "prose");\*\* 1);8 I, I
can change the polarity to 0. (In a similar way, V 3 #strong[#emph[A];]
neutralises any intuitionistic formula.)

=== 3. #strong[Sequent calculus: identity and structure]
<sequent-calculus-identity-and-structure>
The sequent calculus LU is defined as follows: #strong[#emph[sequents];]
are of the form T;T’ t- #strong[#emph[A’;A];] where I, r’,
#strong[#emph[A];] and #strong[#emph[A’];] are sequences of formulas of
the language. The space between the two semi-colons is a space in which
the usual structural rules are available; the intended meaning of such a
sequent is that of a proof which is linear in rand #strong[#emph[A,];]
i.e.~in terms of linear logic of r,!r’ t #strong[#emph[?A’,A.];] The
rules of identity and structure are presented in Fig. 1. They are
independent of any commitment: these rules are meant for all formulas,
and do not refer to any distinction of the form
#strong[#emph[classical/intuitionistic/linear.];] We have adopted a
two-sided version, which has the effect of doubling the number of rules;
a one-sided version would have been more economical, but we would had to
pay for this facility in the discussion of the intuitionistic fragment
which would look slightly artificial when written on the right. To
compensate for this complication, we decided to use an
#strong[#emph[additive];] maintenance for the central part of

#strong[#emph[J.-Y. Girard];]

#strong[#emph[206];]

==== #strong[Identity]
<identity>
#strong[A;] c ;A

l-';I” ,- A';A,A A,A;l-” c- A’;II r,h;I” c A’;A,fI

#figure(
  align(center)[#table(
    columns: (50%, 50%),
    align: (auto,auto,),
    table.header([I’;I”I- A’,A;AA;I”], [c A’;;r’,- A’;AA;A,r’c A’;Il],),
    table.hline(),
    [I’;l?’c A’;A], [h;r’c A’;II],
    [], [#strong[Structure];r;r’ cA’;A],
    [a(r)], [;Q’(I-')c T'(A’); r(A)],
    [r;r’ B-A’;A], [r;r’ t-A’;A],
    [rpcA,A’;A], [r;r’,A +A’;A],
    [r;r’c A,A,A’;A], [r;r’,A,AI- A’;A],
    [rpcA,A’;A], [r;r’,A +A’;A],
    [l?;r’c A’;A,A], [r,.4;r’ a-A’;A],
    [J?;r,- A’,A;A], [r;A,r’ +A’;A],
    [r;I”c A’,N;A], [r;P,r’ +A’;A],
    [I’;r’'- A';N,A], [r,p;r’ I-A’;A],
  )]
  , kind: table
  )

Fig.\_l.

sequents (the same r’ and A’ in binary rules), which is possible since
structural rules are permitted in this area. Another notational trick
would be (instead of the semi-colon) to underline those formulas with a
classical maintenance, which would simplify the schematic writing of our
rules, but would not change anything deep, so this is really a matter of
taste.

As expected, weakening and contraction are freely performed in the
central part of the sequent. Besides the exchange rules, which basically
allow permutation of formulas separated by a comma, we get additional
#strong[#emph[permeability];] rules, which allow formulas to enter the
central zone, and to exit from this zone under some restriction on
polarities. The last group of rules is the only one depending on
polarities.

#strong[#emph[On the unity of logic];]

#strong[#emph[207];]

The identity axiom is written in a pure linear maintenance. The case of
cut is more complex; in fact it falls into two cases, depending on the
style of maintenance for the two occurrences of #strong[#emph[A:];] (i)
if they are both 1 inear (i.e.~outside the central area), we obtain a
rather expected rule;

#block[
#set enum(numbering: "(i)", start: 2)
+ if one of them is linear and the other 'classical' we obtain two
  symmetric forms of cut; observe that the premise containing the linear
  occurrence of #strong[#emph[A];] is of the form #strong[#emph[A;T’ t
  A;];] or ;rk #strong[#emph[A’; A,];] i.e., the context of
  #strong[#emph[A];] is handled classically. There is no possibility of
  defining a cut between two occurrences of #strong[#emph[A];] with a
  classical maintenance. As a matter of fact, there is no need for that:
  typically in classical logic, if we get a cut on #strong[#emph[A,];]
  then #strong[#emph[A];] has a polarity +l or -1, and one of the two
  occurrences of #strong[#emph[A];] can be handled linearily.
]

=== 4. #strong[Logical rules: cases of linear connectives]
<logical-rules-cases-of-linear-connectives>
The calculus presented in Fig. 2 seems rather heavy compared with the
usual formulation of linear logic; but this is just an unpleasant
illusion due to the fact that we have chosen a two-sided version more
than twice the size of the one-sided version.

As expected, the rules for quantifiers (right Ax and left VX) are
subject to the restriction on variables: x not free in T;T’ t
#strong[#emph[A;A’.];]

This calculus is equivalent to the usual linear logic; more precisely we
can translate the usual linear logic into this new system by declaring
all atomic propositions to be neutral. Then a sequent rl-
#strong[#emph[A];] in the usual (two-sided) linear logic becomes r; t
#strong[#emph[;A.];] It is easy to translate proof to proof, though the
rules for the exponentials ! and ? are translated by a heavy use of
structural manipulations. For instance, to pass from !r; t
#strong[#emph[;?A,A];] to !r; t #strong[#emph[;?A,!A, we];] transit
through ;!rk #strong[#emph[?A;A,];] then ;!Tt #strong[#emph[?A;!A,];]
and the ultimate moves to :r; t #strong[#emph[;?A, !A];] use the
polarities of #strong[#emph[?A];] and !I’.

Conversely, this new calculus (as long as we restrict ourselves to
neutral atomic propositions) can be translated into the usual linear
logic as follows: a sequent r;r:,r”t #strong[#emph[A”,AL;A (r:];]
positive, AL negative) translates as r,r!+,!r’1 #strong[#emph[?A”,AL,
A];] in the old syntax for linear logic. Then we have to mimick all
rules of the new calculus in the old one, which offers no difficulty. Of
course, we have to prove in the old calculus a stronger form of the rule
for ’!’, namely that one can pass from Tt- #strong[#emph[A,A];] to r1
#strong[#emph[A, !A,];] as soon as Tis positive and #strong[#emph[A];]
negative. But since our atoms are neutral, positive formulas are built
from 0, 1, and formulas #strong[#emph[!A];] by means of \$, 8 and 3x
(and symmetrically for negative formulas), and we can make an easy
inductive argument.

Of all the logical rules of linear logic, only the rules for
exponentials do something to the central part: the right rule for '!'
assumes that the context lies wholly in the central part, whereas the
left rule moves a formula from the central

#strong[#emph[208];]

#strong[#emph[J.-Y. Girard];]

; I- ;l 1; a- ;

r;r’ ,- A’;A,A A;r’ ,- A’;ll,B A,B,r;r’ .- A’;A r,A;r’ c A’;A,II,A\@B
A\@B,r;r’ n- A’;A

r;r’ I- A’;A,A,B A,r;T’ ,- A’;A B,A;r’ ,- A’;Il r;r’ c A’;A,A?8B
AqB,r,A;r’ + A’;A,ll A,r;r’ c A’;A,B r;r’ s- A’;A,A B,h;r’ ,- A’;ll r;r’
n- A’;A,A+B A\*B,r,A;r’ I- A’;A,II

r; e- ;A,T #strong[O,l-’;] c ;A

r;r’ s- A’;A,A r;r’cA’;A,B .4,r;r’ c A’;A B,r;r’ c A’;A r;r’ c A’;A,A&B
A&B,r;r’ c A’;A A&B,r;r’ c A’;A r;r’ + A’;A,A r;r’ + A’;A,B A,r;r’ I-
A’;A B,r;r’ D- A’;A rp + A ';A,A\~B r;r' t A’;A,A\@B A\@B,r;r’ c A’;A
r;r’ N- A’;A,A A,rp I- A’;A Al,r;r’ b A’;A r;r’ c A’;A,Al ;r’ c A’;A
r;.4,r’ t A’;A ;r’ c A’;!A !A,r;r’ t A’;A r;r’ n- A’,A;A A;r’ c A’; r;r’
c A’;A,?A ?A;r’ c A’; r;r’ c A’;A,A A\[t/x\],r;r’ + A’;A ?;I-’ c
A’;A,hxA hx.4,r;r\* c A’;A I-g-9 c A ';A,A\[t/xl A,r;I” c A';A I-;J?’ c
A’;A,VxA VxA,l’-;r’ c A’;A

#strong[Fig. 2.]

209

#strong[#emph[On the unity of logic];]

area to the extreme left, at the price of a symbol ’!’; the new formula
#strong[#emph[!A];] can now pass the semi-colon in both ways.

=== #strong[\5. Some chime& connectives]
<some-chime-connectives>
It is possible to define new connectives by pattern matching, i.e.~by
considering polarities. Below, we shall consider only those connectives
and quantifiers which are of interest to classical and intuitionistic
logics: these connectives are A, v , #strong[j, 1, V, F, vx, 3x]
(classical), fl, U, 3, -, #strong[V, F, (x)] and (Ex) (intuitionistic).
However, it turns out that n, U, #strong[V, F, (x)] and (Ex) can be
chosen to coincide with A, v, 1, 0, Ax, 3x; moreover, intuitionistic
negation is better handled as

#strong[#emph[\-A:AxO.];]

Our tables (see Tables 2 and 3) have been chosen so as to minimize the
total number of connectives, and to get as many denotational
isomorphisms as possible. It has not been possible to keep the same
connective for implication (owing to conflicts of polarities). Our
classical implication has been made up from #strong[#emph[1A v B];] and
is quite complicated; another one, built on #strong[#emph[l(A A lB),];]
would be simpler, but the discussion is rather sterile since the
difference cannot be noticed on classical formulas.

The rules for our new connectives are presented in Fig. 3. The author
can be accused of bureaucracy: even if one regroups rules, their number
remains. . . frightening. Surely the fact that disjunction is defined by
nine

Table 2

Polarities for classical and intuitionistic connectives

J.-Y. #strong[#emph[Girard];]

210

Table 3

Classical and intuitionistic connectives defined in terms of linear
logic

independent cases counts for something in this inflation. However,
observe that these rules are always variations of the familiar rules for
disjunction, and each line differs from the other by a slightly
different structural maintenance. Given a concrete disjunction
#strong[#emph[A v B,];] only one of these lines can work, i.e.~at most
three rules at usual. Moreover, the usual fragments use at most four
lines out of nine. Also, these rules manage to unify classical and
intuitionistic disjunction in the same #strong[#emph[ussocia\~ive];]
connective, which is a nontrivial achievement.

All other usual connectives coincide with one of those already
introduced, with the exception of intuitionistic negation: it is
impossible to write its rules without using the constant #strong[F] (or
0): this minor defect comes from our very cautious treatment of
structural rules; it is therefore better to consider - as defined by
#strong[#emph[\-A:=A] zF.]

=== 6. #strong[Some properties of the calculus]
<some-properties-of-the-calculus>
First let us fix once for all a reasonable language: -atomic predicates
are given with their polarity (+ #strong[1, 0,] -1); -two constants 0
and 1, both positive (also denoted #strong[F] and #strong[V); -] unary
connectives: !, (e)’ (also denoted 1);

- -binary connectives: A, v , ITS, 3, C3,4?, 4, CB, &; -quantifiers: Vx,
  3x, Ax, Vx.

211

#strong[On] #strong[#emph[the unity of logic];]

#strong[Rules for conjunction I’;l?’ I-] A’;A,P A;r’ + A’;II,Q P,Q,r;r’
c A’;A r,A;r’ t- A’;A,II,PAQ PhQ,r;r’ s- A’;A ;r’ + A’;A Air\* c A’;\~,Q
Q,r;r’,A .- A’;A A;r’ c A’;II,AAQ AhQ,r;r’ c A’;A r;r’ \@- A’;A,P ;r’ c
A’;B P,rp,B c A’;A r;r’ c A’;A,PAB #strong[PhB,I’;r + A’;A]

r;r’ c #strong[A’;A,A] r;r’ c #strong[A’;A,B] A,r;r’ + A’;A B,r;r’ \@-
A’;A r;r’ t A’;A,AAB AAB,r;I” c A ';A AAB,r;r' c A’;A

Commenfs: P, Q positive; #strong[#emph[A, B];] not positive.

#strong[Rules for intuitionistic implication]

#strong[#emph[Comments: P];] positive; #strong[#emph[A];] not positive;
B arbitrary.

#strong[Rules for "V"]

#figure(
  align(center)[#table(
    columns: 2,
    align: (auto,auto,),
    table.header([#strong[I-;I-’];#strong[c];A’,A;A], [#strong[A\[t/x\];A’];#strong[\+
      II’;];],),
    table.hline(),
    [#strong[I’;r];#strong[c];A’;A,tlxA], [b&A’c II’;],
    [#strong[F;I-’];#strong[c
    A’;A,N];], [#strong[N\[t/x\]];#strong[,A;A’];#strong[c II’;l-I];],
    [#strong[I’;r’];#strong[c A’;A,VxN];], [#strong[VXN,A;A’];\*\*c
    II\*;II\*\*],
  )]
  , kind: table
  )

Comments: A not negative; N negative; x not free in T;T’ k
#strong[#emph[A’;A.];]

Fig. 3.

#strong[#emph[J.-Y. Girard];]

#strong[#emph[212];]

#strong[Rules for disjunction]

#strong[I’;r’ c] A’;A,P I’;l?’ .- A’;A,Q P,r;r’ I- A’;A p,r;r\* + A’;A
r;r’ + A ';A,PVQ r-p c A';A,PVQ pvrj,r;rp + A’;A

p I- A’;S I’;r’ c A’;A,Q r;s,r’ D- A’;A q,r;r’ k A’.;A ;I-’ c A’;SVQ
l-';I-' c A’;A,SVQ svq,rp c A’;A

;I” a- A’;S ;I” c A’;T rp,s m- A’;A I-;I”,T c A’;A ;I” c A’;SVT ;I” c
A’;SVT svT,r;r’ c- A’;A r;r’ D- A’;A,M ;J?’ s- A’;M,T M,rp b- A’;A ;I”,T
B- A’; I’;l?’ c A’;A,MVT ;r’ n- A’;MVT wT,rp t- A’;A

#strong[#emph[Comments: P, Q];] positive; #strong[#emph[M, N];]
negative; S, #strong[#emph[T];] neutral.

#strong[Rules for "3"]

#strong[#emph[Comments: P];] positive, #strong[#emph[A];] not positive,
x not free in ,\$A t II’;II.

Fig. 3 #strong[#emph[(contd.).];]

On #emph[the unity] #strong[#emph[of logic];]

213

==== #strong[Rules for classical implication]
<rules-for-classical-implication>
#figure(
  align(center)[#table(
    columns: (33.33%, 33.33%, 33.33%),
    align: (auto,auto,auto,),
    table.header([#strong[r;l-”];], [#strong[c];#strong[A’;A,P];#strong[\~,r;r’];#strong[\+
      A’;A];], [r;r’ c-#strong[A’;A,N];#strong[Q,A;r’];#strong[,-];A’;l-I],),
    table.hline(),
    [r;r’], [cA ';A,NJPr;r' c#strong[A’;A,NJP];], [N+P,r,A;r’
    t#strong[A’;A;Il];],
    [], [p,r;r\* I-#strong[Q,A’;A];], [r;r’
    \+#strong[A’;A,P];#strong[Q;r’];#strong[\+ A’;];],
    [], [r;r’ c#strong[A’;A,P+Q];], [pjp,r;r’ +#strong[A’;A];],
    [], [r;r’,M c A’;A,N], [g-9 I- A’;MN,A;r’ c A’;II],
    [], [r;r’ cA’;A,MjN], [M+N,A;p’c A’;II],
    [], [P,r;f”c A’;A,N], [r;r’ t#strong[A’;A,P];N,A;p’c A’;l-l],
    [], [r;l-”c A’;A,P+N], [P+N,r,A;r’\* A’;A,B],
  )]
  , kind: table
  )

Comments: P, Q positive, #strong[#emph[M, N];] negative; this set of
rules is incomplete (we have omitted the rules involving neutral
formulas, for which there is no use at present; the reader may
reconstitute them from the rules of disjunction). Observe that the four
rules written would have been the same if implication had been defined
from conjunction.

Fig. 3 #strong[#emph[(cod.).];]

We now define remarkable fragments; they are all defined by a
restriction of the possible atomic formulas and of the possible
connectives and quantifiers:

- #block[
  #set enum(numbering: "(1)", start: 1)
  + #strong[#emph[The classical fragment:];]
  ]

\-positive and negative atoms (including #strong[V] and #strong[F);]
closed under 1, A, v, +, ’dx and 3x.

- #block[
  #set enum(numbering: "(1)", start: 2)
  + #strong[#emph[The intuitionistic fragment:];]
  ]

- #strong[#emph[\-positive];] and neutral atoms (including #strong[V]
  and #strong[F);] closed under A, v , 3, Ax, 3x.

  - #block[
    #set enum(numbering: "(1)", start: 3)
    + #strong[#emph[The neutral intuitionistic fragment:];]
    ]

- neutral atoms; closed under A, 3, Ax.

  - #block[
    #set enum(numbering: "(1)", start: 4)
    + #strong[#emph[The linear fragment:];]
    ]

#strong[#emph[\-all];] atoms; closed under (.)I, 8, 9, +I, \@, &, !, ?,
Ax, Vx. The interest of these various fragments is that they enable us
to formalise arguments belonging to various logical systems inside
#strong[LU,] with the advantage of a unique proof-maintenance. Each
fragment uses a very small part of our #strong[#emph[kolossal];] sequent
calculus. But #strong[LU] is not the union of its fragments: there must
be interesting formulas outside of these fragments (and also other
interesting fragments; for instance a positive intuitionistic fragment
based on the implication #strong[#emph[!(A XI B)];] should be
investigated).

The classical fragment is based on the idea of staying within the
positive or negative formulas; the intuitionistic fragment stays within
the positive and neutral formulas; the neutral intuitionistic fragment
is wholly neutral; the linear fragment admits all three polarities.

#strong[.I. -Y.] #strong[#emph[Girard];]

#strong[214]

An important property of these fragments is the
#strong[#emph[substitution property:];] let #strong[#emph[a];] be a
proper predicate symbol of arity #strong[#emph[n,];] and let
#strong[#emph[A];] be a formula of the same polarity as
#strong[#emph[a,];] in which distinct free variables x1, . . . , x,,
have been distinguished. Then one can define for any formula
#strong[#emph[B];] the substitution #strong[#emph[B\[IZx,, . . . ,
x,.A/a\]];] as the result of replacing any atom #strong[#emph[at1];] \*
\- - t, of #strong[#emph[B];] by \*\*\_A\[t,,\_\*\* . . . , t,\] (with
usual precautions concerning free and bound variables, comrade
Tchenienko). All the fragments considered are closed under mutual
substitution.

Each fragment gets its own notion of sequent: first all formulas must
belong to the fragment; but some additional properties may be required:

#block[
#set enum(numbering: "(i)", start: 1)
+ A #strong[#emph[classical sequent T;T’ 1 II’;II];] is such that if we
  make the sum of the number of negative formulas in r and of positive
  formulas in II, we get the total number 0 or 1.

+ An #strong[#emph[intuitionistic sequent];] is of the form T;T’ k ;A.

+ A #strong[#emph[neutral intuitionistic sequent];] is a sequent T;T’ t
  #strong[#emph[;A,];] with at most one formula in lY
]

#strong[Theorem.] #strong[#emph[If a sequent of one of the fragments
considered provable, it is provable within the fragment.] Proof.] We
limit our search to cut-free proofs; by the subformula property, all the
#strong[#emph[formulas];] occurring in the proofs belong to the
fragment; in particular this is enough for linear logic, since no
additional restriction has been imposed on linear sequents. Let us
consider the remaining cases: in all cases we have to check that the
restriction on the shape of the sequent can be forwarded from the
conclusion to the premise(s).

#strong[#emph[Neutral intuitionistic fragment.];] First observe that the
restriction #strong[#emph[“A’];] empty” will be easily forwarded (this
holds for both intuitionistic fragments). Then observe that for any
cut-free rule of #strong[LU] ending with a neutral intuitionistic
sequent #strong[#emph[r;r’ I- ;S,];]

#strong[#emph[\-];] all premises are of the form A;A’ k
#strong[#emph[;T,];]

#strong[#emph[\-];] one of these premises, say A;A’ k
#strong[#emph[;T,];] is such that the number of formulas in
#strong[#emph[A];] is greater or equal to the number of formulas in r,
with only one exception, namely the identity axiom. In particular there
is no way to prove a sequent I’\$” I- ;S of formulas in this fragment
when r has two formulas or more; the formula of r (if there is one) is
the analogue of the familiar #strong[#emph[headvariable];] of typed
&calculi, which are based on neutral intuitionistic fragments.

This proves that all premises of the rule must be also neutral
intuitionistic sequents.

#strong[#emph[Classical fragment.];] If S is the sequent r;I” t A’;A let
us define p(S) to be the sum of the number of negative formulas in r and
of positive formulas in #strong[#emph[\A. Now];] for any rule with a
conclusion S made of classical formulas and such that p(S) \> 1, there
is premise S’ such that p(S’) 2 p(S), with only one exception:

#strong[#emph[On the unity of logic];]

215

the axiom #strong[F, r; I-] #emph[;A.] Furthermore, there are only two
rules with a premise S’ and a conclusion S such that p(S’) \> p(S): the
two permeability rules enabling a formula to enter the central zone. Now
it is an easy exercise, given any cut-free proof of a sequent S made of
classical formulas with ,u(S) \> 1, to produce another proof of any
sequent S’ obtained by removing as many formulas among those which
contribute to p(S). In particular, a 'bad' permeability rule can be
replaced with a weakening and so we stay among classical sequents.

#strong[#emph[lntuitionisticfragment.];] If Y(S) counts the number of
formulas in the part #emph[A] of a sequent S = T;T’ !- #emph[;A,] then
the restriction Y(S) 6 1 is forwarded from the conclusion to the
premises of all rules involving intuitionistic formulas but for the case
of a rule

Easy commutation arguments reduce the use of this rule to the case where
C is positive or atomic. From this it can be ensured that all sequents
with Y(S) \> 1 occurring in the proof of an intuitionistic sequent have
a succedent made of positive or atomic formulas. Now one can easily
produce given a proof of a sequent
T$quote.r.double t -_(;) A_w i t h_Y (A) f_1 (t h i s i n c l u d e s_v (A) = 0)_a n d a l l f o r m u l a s i n t u i t i o n i s t i c , a n o t h e r p r o o f o f I quote.r.single$’
t \$7 where n has been obtained from #emph[A] by adding formulas, or
removing atomic or positive ones. In particular, we can replace the
'bad' rule above by the 'good' one:

and this shows that we can stay within the intuitionistic sequents. 0

#strong[Remarks.] (i) We implicitly used a cut-elimination theorem for
#strong[LU] that is more or less obvious (but perhaps a bit too long to
write down explicitly).’ (ii) The results of the theorem concern not
only provability, but also proofs, in the sense of denotational
semantics; there would be nothing to prove in the classical and the
intuitionistic case if the constant 0 were not allowed (only the axioms
involving 0 and its negation prevent us to draw conclusions like in the
neutral fragment). Now the proofs we look at with the wrong p(S) or Y(S)
are in fact interpreted in a coherent space with an empty web: all
proofs of such sequents are denotationally equal, and we therefore
replace a proof by another one with the same semantics!

#block[
#set enum(numbering: "(i)", start: 3)
+ The paper of Schellinx \[4\] investigates the faithfulness of the
  translation intuitionistic I–+ linear and our proof is roughly
  inspired from this paper.
]

#quote(block: true)[
’ See forthcoming paper by J. Vauzeilles to appear in this journal
]

#strong[.I. -Y.] #strong[#emph[Girard];]

#strong[216]

Now, it remains to compare the systems LU restricted to various
fragments with the sequent calculi for the corresponding logics: (i) The
two intuitionistic fragments are OK: just translate T;T’ E
#strong[#emph[;A];] as r,r’ #strong[#emph[FA];] and observe that all
rules are correct. The other way around might be slightly more delicate
at least if we investigate cut-free provability.

#block[
#set enum(numbering: "(i)", start: 2)
+ The classical fragment translates not to LK, but to LC (see \[3\]);
  more precisely besides the superficial difference one-sided/two sided,
  LC uses the semi-colon in a different way: one tries to put as many
  formulas as possible in the central zone: in particular, starting with
  T;T’ t A’;A, the idea is to move all positive formulas from r to the
  right, and all negative formulas of A to the left: with the result
  that T,A can consist of at most one formula.
]

=== Conclusion
<conclusion>
As a matter of conclusion let us observe that this attempt at
unification is orthogonal to synchretic attempts of the style 'logical
framework': too often unification is at the price of a loss of structure
(we lose properties: cutelimination, nay consistency). Here it goes the
other way around. All fragments considered are better as subsystems of
LU than they were as isolated systems: (i) Classical logic is handled by
LC which is much better than LK. (ii) The neutral intuitionistic
fragment gets a legalislation of the notion of
#strong[#emph[headvariable];] and its normalisation procedure should be
of the style 'linear head-reduction'.

#block[
#set enum(numbering: "(i)", start: 3)
+ The intuitionitic fragment gets a subtler approach to
  pattern-matching, typically a denotationally associative disjunction.
  (iv) Linear logic gets a smoother sequent calculus, in particular for
  exponential connectives; this formulation has some similarties with
  the linear sequent calculi proposed by Andreoli and Pareschi \[l\].
]

. . . Not to speak of the fact that all these systems are part of the
same calculus,

i.e., are free to interact . . . .

There is of course the obvious question: is this #strong[#emph[LOGIC,];]
i.e., did we catch here all possible logical systems? Surely not, and
there are additional parameters on which one can play to broaden the
scope of a unified approach to logic: (i) The consideration of
additional polarities: a polarity can be abstractly seen as the
permission to perform certain structural rules on the left or the right
of a sequent. Many other cocktails (from the absolute noncommutative
polarity to classical polarities) are possible, and all the combinations
between weakening, exchange and contraction yield up to 15 possible
polarities. Most of these combinations presumably make no sense, and one
should not hurry to invent polarities with no concrete application.
However, if one insists on experimenting in that way, it seems that a
good criterion for the consideration of additional

#strong[#emph[On];] #emph[the unity] #strong[#emph[of];] #emph[logic]

217

polarities could be the possibility of extending the definition of
disjunction so as to preserve its denotational associativity. (ii) The
extension of these results to systems which have always been on the
border line of logic: systems of arithmetic, and more generally
inductive definitions.

#block[
#set enum(numbering: "(i)", start: 3)
+ The extension to second-order; in particular, it will be possible to
  cope with the loss of subformula property by considering
  quantifications ranging on various fragments (example: for all
  positive and classical (u).
]

NON SI NON LA

=== #strong[References]
<references>
- \[l\] J.-M. Andreoli and R. Pareschi, Linear objects: logical
  processes with built-in inheritance, to appear in New Generation
  Computing (1991).

- \[2\] J.-Y. Girard, Linear logic, Theoret. Comput. Sci. 50 (1987)
  l-102.

- \[3\] J.-Y. Girard, A new constructive logic: classical logic,
  Preprint, universite Paris VII, March 1991, to appear in Math.
  Structures Comput. Sci. l(3).

- \[4\] H. Schellinx, Some syntactical observations on linear logic,
  Preprint 1990, to appear in J. Logic and Computation, 1991.
