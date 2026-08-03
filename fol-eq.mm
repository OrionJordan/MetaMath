
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Predicate calculus with equality:  Tarski's system S2 (1 rule, 6 schemes)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  Here we extend the language of wffs with predicate calculus, which allows
  to talk about individual objects in a domain of discourse (which for us will
  be the universe of all sets, so we call them "setvar variables") and make
  true/false statements about predicates, which are relationships between
  objects, such as whether or not two objects are equal.  In addition, we
  introduce universal quantification ("for all", e.g., ~ ax-4 ) in order to
  make statements about whether a wff holds for every object in the domain of
  discourse.  Later we introduce existential quantification ("there exists",
  ~ df-ex ) which is defined in terms of universal quantification.

  Our axioms are really axiom _schemes_, and our wff and setvar variables are
  metavariables ranging over expressions in an underlying "object language".
  This is explained here:  ~ mmset.html#axiomnote .

  Our axiom system starts with the predicate calculus axiom schemes system S2
  of Tarski defined in his 1965 paper, "A Simplified Formalization of Predicate
  Logic with Identity" [Tarski].  System S2 is defined in the last paragraph on
  p. 77, and repeated on p. 81 of [KalishMontague].  We do not include scheme
  B5 (our ~ sp ) of system S2 since [KalishMontague] shows it to be logically
  redundant (Lemma 9, p. 87, which we prove as Theorem ~ spw below).

  Theorem ~ spw can be used to prove any _instance_ of ~ sp having mutually
  distinct setvar variables and no wff metavariables.  However, it seems that
  ~ sp in its general form cannot be derived from only Tarski's schemes.  We do
  not include B5 i.e. ~ sp as part of what we call "Tarski's system" because we
  want it to be the smallest set of axioms that is logically complete with
  no redundancies.  We later prove ~ sp as Theorem ~ axc5 using the auxiliary
  axiom schemes that make our system metalogically complete.

  Our version of Tarski's system S2 consists of propositional calculus
  ( ~ ax-mp , ~ ax-1 , ~ ax-2 , ~ ax-3 ) plus ~ ax-gen , ~ ax-4 , ~ ax-5 ,
  ~ ax-6 , ~ ax-7 , ~ ax-8 , and ~ ax-9 .  The last three are equality axioms
  that represent three sub-schemes of Tarski's scheme B8.  Due to its
  side-condition ("where ` ph ` is an atomic formula and ` ps ` is obtained by
  replacing an occurrence of the variable ` x ` by the variable ` y ` "), we
  cannot represent his B8 directly without greatly complicating our scheme
  language, but the simpler schemes ~ ax-7 , ~ ax-8 , and ~ ax-9 are sufficient
  for set theory and much easier to work with.

  Tarski's system is exactly equivalent to the traditional axiom system in most
  logic textbooks but has the advantage of being easy to manipulate with a
  computer program, and its simpler metalogic (with no built-in notions of
  "free variable" and "proper substitution") is arguably easier for a
  non-logician human to follow step by step in a proof (where "follow" means
  being able to identify the substitutions that were made, without necessarily
  a higher-level understanding).  In particular, it is logically complete in
  that it can derive all possible object-language theorems of predicate
  calculus with equality, i.e., the same theorems as the traditional system can
  derive.

  However, for efficiency (and indeed a key feature that makes Metamath
  successful), our system is designed to derive reusable theorem schemes
  (rather than object-language theorems) from other schemes.  From this
  "metalogical" point of view, Tarski's S2 is not complete.  For example, we
  cannot derive scheme ~ sp , even though (using ~ spw ) we can derive all
  instances of it that do not involve wff metavariables or bundled setvar
  variables.  (Two setvar variables are "bundled" if they can be substituted
  with the same setvar variable, i.e., do not have a "$d" disjoint variable
  condition.)  Later we will introduce auxiliary axiom schemes ~ ax-10 ,
  ~ ax-11 , ~ ax-12 , and ~ ax-13 that are metatheorems of Tarski's system
  (i.e. are logically redundant) but which give our system the property of
  "scheme completeness", allowing us to prove directly (instead of, say,
  by induction on formula length) all possible schemes that can be expressed in
  our language.

$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Universal quantifier ( From Propositional Calculus )
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Even though it is not ordinarily part of propositional calculus, the
  universal quantifier ` A. ` is introduced here so that the soundness of
  Definition ~ df-tru can be checked by the same algorithm that is used for
  predicate calculus.  Its first real use is in Definition ~ df-ex in the
  predicate calculus section below.  For those who want propositional calculus
  to be self-contained, i.e., to use wff variables only, the alternate
  Definition ~ dftru2 may be adopted and this subsection moved down to the
  start of the subsection with ~ wex below.  However, the use of ~ dftru2 as a
  definition requires a more elaborate definition checking algorithm that we
  prefer to avoid.

$)

  $( Declare new symbols needed for predicate calculus. $)
  $c A. $.  $( "inverted A" universal quantifier (read:  "for all") $)
  $c setvar $.  $( Individual variable type (read:  "the following is an
                   individual (set) variable") $)

  $( Add 'setvar' as a typecode for bound variables. $)
  $( $j syntax 'setvar'; bound 'setvar'; $)

  $( Declare the color of setvar variables. $)
  $( $j
    varcolorcode "setvar" as "FF0000";
    altvarcolorcode "setvar" as "FF0000";
  $)

  ${
    $v x $.
    $( Let ` x ` be an individual variable (temporary declaration). $)
    vx.wal $f setvar x $.
    $( Extend wff definition to include the universal quantifier ("for all").
       ` A. x ph ` is read " ` ph ` (phi) is true for all ` x ` ".  Typically,
       in its final application ` ph ` would be replaced with a wff containing
       a (free) occurrence of the variable ` x ` , for example ` x = y ` .  In
       a universe with a finite number of objects, "for all" is equivalent to a
       big conjunction (AND) with one wff for each possible case of ` x ` .
       When the universe is infinite (as with set theory), such a
       propositional-calculus equivalent is not possible because an infinitely
       long formula has no meaning, but conceptually the idea is the same. $)
    wal $a wff A. x ph $.

    $( Register the universal quantifier 'A.' as a primitive expression
       (lacking a definition). $)
    $( $j primitive 'wal'; $)
  $}


  $( Declare the equality predicate symbol. $)
  $c = $.  $( Equal sign (read:  'is equal to') $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Universal quantifier (continued); define "exists" and "not free"
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The universal quantifier was introduced above in ~ wal for use by ~ df-tru .
  See the comments in that section.  In this section, we continue with the
  first "real" use of it.

$)

  $( Declare some names for individual variables. $)
  $v x $.
  $v y $.
  $v z $.
  $v w $.
  $v v $.
  $v u $.
  $v t $.
  $( Let ` x ` be an individual variable. $)
  vx $f setvar x $.
  $( Let ` y ` be an individual variable. $)
  vy $f setvar y $.
  $( Let ` z ` be an individual variable. $)
  vz $f setvar z $.
  $( Let ` w ` be an individual variable. $)
  vw $f setvar w $.
  $( Let ` v ` be an individual variable. $)
  vv $f setvar v $.
  $( Let ` u ` be an individual variable. $)
  vu $f setvar u $.
  $( Let ` t ` be an individual variable. $)
  vt $f setvar t $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Existential quantifier
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Declare the existential quantifier symbol. $)
  $c E. $.  $( Backwards E (read:  "there exists") $)

  $( Extend wff definition to include the existential quantifier ("there
     exists"). $)
  wex $a wff E. x ph $.

  $( Define existential quantification. ` E. x ph ` means "there exists at
     least one set ` x ` such that ` ph ` is true".  Dual of ~ alex .  See also
     the dual pair ~ alnex / ~ exnal .  Definition of [Margaris] p. 49.
     (Contributed by NM, 10-Jan-1993.) $)
  df-ex $a |- ( E. x ph <-> -. A. x -. ph ) $.

  $( Universal quantification of negation is equivalent to negation of
     existential quantification.  Dual of ~ exnal (but does not depend on
     ~ ax-4 contrary to it).  See also the dual pair ~ df-ex / ~ alex .
     Theorem 19.7 of [Margaris] p. 89.  (Contributed by NM, 12-Mar-1993.) $)
  alnex $p |- ( A. x -. ph <-> -. E. x ph ) $=
    ( wex wn wal df-ex con2bii ) ABCADBEABFG $.

  $( An equivalence between an implication with an existentially quantified
     antecedent and an implication with a universally quantified consequent.
     An interesting case is when the same formula is substituted for both
     ` ph ` and ` ps ` , since then both implications express a type of
     nonfreeness.  See also ~ alimex .  (Contributed by BJ, 12-May-2019.) $)
  eximal $p |- ( ( E. x ph -> ps ) <-> ( -. ps -> A. x -. ph ) ) $=
    ( wex wi wn wal df-ex imbi1i con1b bitri ) ACDZBEAFCGZFZBEBFMELNBACHIMBJK
    $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Nonfreeness predicate
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c F/ $.  $( The not-free symbol. $)

  $( Extend wff definition to include the not-free predicate. $)
  wnf $a wff F/ x ph $.

  $( Define the not-free predicate for wffs.  This is read " ` x ` is not free
     in ` ph ` ".  Not-free means that the value of ` x ` cannot affect the
     value of ` ph ` , e.g., any occurrence of ` x ` in ` ph ` is effectively
     bound by a "for all" or something that expands to one (such as "there
     exists").  In particular, substitution for a variable not free in a wff
     does not affect its value ( ~ sbf ).  An example of where this is used is
     ~ stdpc5 .  See ~ nf5 for an alternate definition which involves nested
     quantifiers on the same variable.

     Not-free is a commonly used constraint, so it is useful to have a notation
     for it.  Surprisingly, there is no common formal notation for it, so here
     we devise one.  Our definition lets us work with the not-free notion
     within the logic itself rather than as a metalogical side condition.

     To be precise, our definition really means "effectively not free", because
     it is slightly less restrictive than the usual textbook definition for
     "not free" (which considers syntactic freedom).  For example, ` x ` is
     effectively not free in the formula ` x = x ` (even though ` x ` is
     syntactically free in it, so would be considered free in the usual
     textbook definition) because the value of ` x ` in the formula ` x = x `
     does not affect the truth of that formula (and thus substitutions will not
     change the result), see ~ nfequid .

     This definition of "not free" tightly ties to the quantifier ` A. x ` .
     At this state (no axioms restricting quantifiers yet) "nonfree" appears
     quite arbitrary.  Its intended semantics expresses single-valuedness
     (constness) across a parameter, but is only evolved as much as later
     axioms assign properties to quantifiers.  It seems the definition here is
     best suited in situations, where axioms are only partially in effect.  In
     particular, this definition more easily carries over to other logic models
     with weaker axiomization.

     The reverse implication of the definiens (the right hand side of the
     biconditional) always holds, see ~ 19.2 .

     This predicate only applies to wffs.  See ~ df-nfc for a not-free
     predicate for class variables.  (Contributed by Mario Carneiro,
     24-Sep-2016.)  Convert to definition.  (Revised by BJ, 6-May-2019.) $)
  df-nf $a |- ( F/ x ph <-> ( E. x ph -> A. x ph ) ) $.

  $( Alternate definition of nonfreeness.  (Contributed by BJ, 16-Sep-2021.) $)
  nf2 $p |- ( F/ x ph <-> ( A. x ph \/ -. E. x ph ) ) $=
    ( wnf wex wal wi wn wo df-nf imor orcom 3bitri ) ABCABDZABEZFMGZNHNOHABIMNJ
    ONKL $.

  $( Alternate definition of nonfreeness.  (Contributed by BJ, 16-Sep-2021.) $)
  nf3 $p |- ( F/ x ph <-> ( A. x ph \/ A. x -. ph ) ) $=
    ( wnf wal wex wn wo nf2 alnex orbi2i bitr4i ) ABCABDZABEFZGLAFBDZGABHNMLABI
    JK $.

  $( Alternate definition of nonfreeness.  This definition uses only primitive
     symbols ( ` -> , -. , A. ` ).  (Contributed by BJ, 16-Sep-2021.) $)
  nf4 $p |- ( F/ x ph <-> ( -. A. x ph -> A. x -. ph ) ) $=
    ( wnf wal wn wo wi nf3 df-or bitri ) ABCABDZAEBDZFKELGABHKLIJ $.

  ${
    nfi.1 $e |- ( E. x ph -> A. x ph ) $.
    $( Deduce that ` x ` is not free in ` ph ` from the definition.
       (Contributed by Wolf Lammen, 15-Sep-2021.) $)
    nfi $p |- F/ x ph $=
      ( wnf wex wal wi df-nf mpbir ) ABDABEABFGCABHI $.
  $}

  ${
    nfri.1 $e |- F/ x ph $.
    $( Consequence of the definition of not-free.  (Contributed by Wolf Lammen,
       16-Sep-2021.) $)
    nfri $p |- ( E. x ph -> A. x ph ) $=
      ( wnf wex wal wi df-nf mpbi ) ABDABEABFGCABHI $.
  $}

  ${
    nfd.1 $e |- ( ph -> ( E. x ps -> A. x ps ) ) $.
    $( Deduce that ` x ` is not free in ` ps ` in a context.  (Contributed by
       Wolf Lammen, 16-Sep-2021.) $)
    nfd $p |- ( ph -> F/ x ps ) $=
      ( wex wal wi wnf df-nf sylibr ) ABCEBCFGBCHDBCIJ $.
  $}

  ${
    nfrd.1 $e |- ( ph -> F/ x ps ) $.
    $( Consequence of the definition of not-free in a context.  (Contributed by
       Wolf Lammen, 15-Oct-2021.) $)
    nfrd $p |- ( ph -> ( E. x ps -> A. x ps ) ) $=
      ( wnf wex wal wi df-nf sylib ) ABCEBCFBCGHDBCIJ $.
  $}

  $( Closed form of ~ nfth .  (Contributed by Wolf Lammen, 19-Aug-2018.)
     (Proof shortened by BJ, 16-Sep-2021.)  (Proof shortened by Wolf Lammen,
     3-Sep-2022.) $)
  nftht $p |- ( A. x ph -> F/ x ph ) $=
    ( wal wex ax-1 nfd ) ABCZABGABDEF $.

  $( Closed form of ~ nfnth .  (Contributed by BJ, 16-Sep-2021.)  (Proof
     shortened by Wolf Lammen, 4-Sep-2022.) $)
  nfntht $p |- ( -. E. x ph -> F/ x ph ) $=
    ( wex wn wal pm2.21 nfd ) ABCZDABHABEFG $.

  $( Closed form of ~ nfnth .  (Contributed by BJ, 16-Sep-2021.)  (Proof
     shortened by Wolf Lammen, 4-Sep-2022.) $)
  nfntht2 $p |- ( A. x -. ph -> F/ x ph ) $=
    ( wn wal wex wnf alnex nfntht sylbi ) ACBDABECABFABGABHI $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Rule scheme ax-gen (Generalization)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    ax-gen.1 $e |- ph $.
    $( Rule of (universal) generalization.  In our axiomatization, this is the
       only postulated (that is, axiomatic) rule of inference of predicate
       calculus (together with the rule of modus ponens ~ ax-mp of
       propositional calculus).  See, e.g., Rule 2 of [Hamilton] p. 74.  This
       rule says that if something is unconditionally true, then it is true for
       all values of a variable.  For example, if we have proved ` x = x ` ,
       then we can conclude ` A. x x = x ` or even ` A. y x = x ` .  Theorem
       ~ altru shows the special case ` A. x T. ` .  The converse rule of
       inference ~ spi (universal instantiation, or universal specialization)
       shows that we can also go the other way: in other words, we can add or
       remove universal quantifiers from the beginning of any theorem as
       required.  Note that the closed form ` ( ph -> A. x ph ) ` need not hold
       (but may hold in special cases, see ~ ax-5 ).  (Contributed by NM,
       3-Jan-1993.) $)
    ax-gen $a |- A. x ph $.
  $}

  ${
    gen2.1 $e |- ph $.
    $( Generalization applied twice.  (Contributed by NM, 30-Apr-1998.) $)
    gen2 $p |- A. x A. y ph $=
      ( wal ax-gen ) ACEBACDFF $.
  $}

  ${
    mpg.1 $e |- ( A. x ph -> ps ) $.
    mpg.2 $e |- ph $.
    $( Modus ponens combined with generalization.  (Contributed by NM,
       24-May-1994.) $)
    mpg $p |- ps $=
      ( wal ax-gen ax-mp ) ACFBACEGDH $.
  $}

  ${
    mpgbi.1 $e |- ( A. x ph <-> ps ) $.
    mpgbi.2 $e |- ph $.
    $( Modus ponens on biconditional combined with generalization.
       (Contributed by NM, 24-May-1994.)  (Proof shortened by Stefan Allan,
       28-Oct-2008.) $)
    mpgbi $p |- ps $=
      ( wal ax-gen mpbi ) ACFBACEGDH $.
  $}

  ${
    mpgbir.1 $e |- ( ph <-> A. x ps ) $.
    mpgbir.2 $e |- ps $.
    $( Modus ponens on biconditional combined with generalization.
       (Contributed by NM, 24-May-1994.)  (Proof shortened by Stefan Allan,
       28-Oct-2008.) $)
    mpgbir $p |- ph $=
      ( wal ax-gen mpbir ) ABCFBCEGDH $.
  $}

  ${
    nex.1 $e |- -. ph $.
    $( Generalization rule for negated wff.  (Contributed by NM,
       18-May-1994.) $)
    nex $p |- -. E. x ph $=
      ( wn wex alnex mpgbi ) ADABEDBABFCG $.
  $}

  ${
    nfth.1 $e |- ph $.
    $( No variable is (effectively) free in a theorem.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) ~ df-nf changed.  (Revised by Wolf Lammen,
       12-Sep-2021.) $)
    nfth $p |- F/ x ph $=
      ( wnf nftht mpg ) AABDBABECF $.
  $}

  ${
    nfnth.1 $e |- -. ph $.
    $( No variable is (effectively) free in a non-theorem.  (Contributed by
       Mario Carneiro, 6-Dec-2016.) ~ df-nf changed.  (Revised by Wolf Lammen,
       12-Sep-2021.) $)
    nfnth $p |- F/ x ph $=
      ( wn wnf nfntht2 mpg ) ADABEBABFCG $.
  $}

  ${
    hbth.1 $e |- ph $.
    $( No variable is (effectively) free in a theorem.

       This and later "hypothesis-building" lemmas, with labels starting
       "hb...", allow to construct proofs of formulas of the form
       ` |- ( ph -> A. x ph ) ` from smaller formulas of this form.  These are
       useful for constructing hypotheses that state " ` x ` is (effectively)
       not free in ` ph ` ".  (Contributed by NM, 11-May-1993.)  This hb* idiom
       is generally being replaced by the nf* idiom (see ~ nfth ), but keeps
       its interest in some cases.  (Revised by BJ, 23-Sep-2022.) $)
    hbth $p |- ( ph -> A. x ph ) $=
      ( wal ax-gen a1i ) ABDAABCEF $.
  $}

  $( The true constant has no free variables.  (This can also be proven in one
     step with ~ nfv , but this proof does not use ~ ax-5 .)  (Contributed by
     Mario Carneiro, 6-Oct-2016.) $)
  nftru $p |- F/ x T. $=
    ( wtru tru nfth ) BACD $.

  $( The false constant has no free variables (see ~ nftru ).  (Contributed by
     BJ, 6-May-2019.) $)
  nffal $p |- F/ x F. $=
    ( wfal fal nfnth ) BACD $.

  ${
    sptruw.1 $e |- ph $.
    $( Version of ~ sp when ` ph ` is true.  Instance of ~ a1i .  Uses only
       Tarski's FOL axiom schemes.  (Contributed by NM, 23-Apr-2017.) $)
    sptruw $p |- ( A. x ph -> ph ) $=
      ( wal a1i ) AABDCE $.
  $}

  $( For all sets, ` T. ` is true.  (Contributed by Anthony Hart,
     13-Sep-2011.) $)
  altru $p |- A. x T. $=
    ( wtru tru ax-gen ) BACD $.

  $( For all sets, ` -. F. ` is true.  (Contributed by Anthony Hart,
     13-Sep-2011.) $)
  alfal $p |- A. x -. F. $=
    ( wfal wn fal ax-gen ) BCADE $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-4 (Quantified Implication)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Implication.  Axiom C4 of [Monk2] p. 105 and Theorem
     19.20 of [Margaris] p. 90.  It is restated as ~ alim for labeling
     consistency.  It should be used only by ~ alim .  (Contributed by NM,
     21-May-2008.)  Use ~ alim instead.  (New usage is discouraged.) $)
  ax-4 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

  $( Restatement of Axiom ~ ax-4 , for labeling consistency.  It should be the
     only theorem using ~ ax-4 .  (Contributed by NM, 10-Jan-1993.) $)
  alim $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( ax-4 ) ABCD $.

  ${
    alimi.1 $e |- ( ph -> ps ) $.
    $( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 5-Jan-1993.) $)
    alimi $p |- ( A. x ph -> A. x ps ) $=
      ( wi wal alim mpg ) ABEACFBCFECABCGDH $.

    $( Inference doubly quantifying both antecedent and consequent.
       (Contributed by NM, 3-Feb-2005.) $)
    2alimi $p |- ( A. x A. y ph -> A. x A. y ps ) $=
      ( wal alimi ) ADFBDFCABDEGG $.
  $}

  $( Add an antecedent in a universally quantified formula.  (Contributed by
     BJ, 6-Oct-2018.) $)
  ala1 $p |- ( A. x ph -> A. x ( ps -> ph ) ) $=
    ( wi ax-1 alimi ) ABADCABEF $.

  $( Closed form of ~ al2imi .  Version of ~ alim for a nested implication.
     (Contributed by Alan Sare, 31-Dec-2011.) $)
  al2im $p |- ( A. x ( ph -> ( ps -> ch ) ) ->
                                     ( A. x ph -> ( A. x ps -> A. x ch ) ) ) $=
    ( wi wal alim syl6 ) ABCEZEDFADFIDFBDFCDFEAIDGBCDGH $.

  ${
    al2imi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference quantifying antecedent, nested antecedent, and consequent.
       (Contributed by NM, 10-Jan-1993.) $)
    al2imi $p |- ( A. x ph -> ( A. x ps -> A. x ch ) ) $=
      ( wi wal al2im mpg ) ABCFFADGBDGCDGFFDABCDHEI $.
  $}

  ${
    alanimi.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Variant of ~ al2imi with conjunctive antecedent.  (Contributed by Andrew
       Salmon, 8-Jun-2011.) $)
    alanimi $p |- ( ( A. x ph /\ A. x ps ) -> A. x ch ) $=
      ( wal ex al2imi imp ) ADFBDFCDFABCDABCEGHI $.
  $}

  ${
    alimdh.1 $e |- ( ph -> A. x ph ) $.
    alimdh.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.20 of [Margaris] p. 90, see ~ alim .
       (Contributed by NM, 4-Jan-2002.) $)
    alimdh $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      ( wal wi al2imi syl ) AADGBDGCDGHEABCDFIJ $.
  $}

  $( Theorem 19.15 of [Margaris] p. 90.  (Contributed by NM, 24-Jan-1993.) $)
  albi $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps ) ) $=
    ( wb wal biimp al2imi biimpr impbid ) ABDZCEACEBCEJABCABFGJBACABHGI $.

  ${
    albii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding universal quantifier to both sides of an equivalence.
       (Contributed by NM, 7-Aug-1994.) $)
    albii $p |- ( A. x ph <-> A. x ps ) $=
      ( wb wal albi mpg ) ABEACFBCFECABCGDH $.

    $( Theorem albii is the congruence law for universal quantification. $)
    $( $j congruence 'albii'; $)

    $( Inference adding two universal quantifiers to both sides of an
       equivalence.  (Contributed by NM, 9-Mar-1997.) $)
    2albii $p |- ( A. x A. y ph <-> A. x A. y ps ) $=
      ( wal albii ) ADFBDFCABDEGG $.

    $( Inference adding three universal quantifiers to both sides of an
       equivalence.  (Contributed by Peter Mazsa, 10-Aug-2018.) $)
    3albii $p |- ( A. x A. y A. z ph <-> A. x A. y A. z ps ) $=
      ( wal 2albii albii ) AEGDGBEGDGCABDEFHI $.
  $}

  $( Closed form of ~ sylg .  (Contributed by BJ, 2-May-2019.) $)
  sylgt $p |- ( A. x ( ps -> ch ) ->
                                ( ( ph -> A. x ps ) -> ( ph -> A. x ch ) ) ) $=
    ( wi wal alim imim2d ) BCEDFBDFCDFABCDGH $.

  ${
    sylg.1 $e |- ( ph -> A. x ps ) $.
    sylg.2 $e |- ( ps -> ch ) $.
    $( A syllogism combined with generalization.  Inference associated with
       ~ sylgt .  General form of ~ alrimih .  (Contributed by NM, 9-Jan-1993.)
       Extract from proof of ~ alrimih .  (Revised by BJ, 4-Oct-2019.) $)
    sylg $p |- ( ph -> A. x ch ) $=
      ( wal alimi syl ) ABDGCDGEBCDFHI $.
  $}

  ${
    alrimih.1 $e |- ( ph -> A. x ph ) $.
    alrimih.2 $e |- ( ph -> ps ) $.
    $( Inference form of Theorem 19.21 of [Margaris] p. 90.  See ~ 19.21 and
       ~ 19.21h .  Instance of ~ sylg .  (Contributed by NM, 9-Jan-1993.) $)
    alrimih $p |- ( ph -> A. x ps ) $=
      ( sylg ) AABCDEF $.
  $}

  ${
    hbxfrbi.1 $e |- ( ph <-> ps ) $.
    hbxfrbi.2 $e |- ( ps -> A. x ps ) $.
    $( A utility lemma to transfer a bound-variable hypothesis builder into a
       definition.  See ~ hbxfreq for equality version.  (Contributed by
       Jonathan Ben-Naim, 3-Jun-2011.) $)
    hbxfrbi $p |- ( ph -> A. x ph ) $=
      ( wal albii 3imtr4i ) BBCFAACFEDABCDGH $.
  $}

  $( Universal quantifier in terms of existential quantifier and negation.
     Dual of ~ df-ex .  See also the dual pair ~ alnex / ~ exnal .  Theorem
     19.6 of [Margaris] p. 89.  (Contributed by NM, 12-Mar-1993.) $)
  alex $p |- ( A. x ph <-> -. E. x -. ph ) $=
    ( wal wn wex notnotb albii alnex bitri ) ABCADZDZBCJBEDAKBAFGJBHI $.

  $( Existential quantification of negation is equivalent to negation of
     universal quantification.  Dual of ~ alnex .  See also the dual pair
     ~ df-ex / ~ alex .  Theorem 19.14 of [Margaris] p. 90.  (Contributed by
     NM, 12-Mar-1993.) $)
  exnal $p |- ( E. x -. ph <-> -. A. x ph ) $=
    ( wal wn wex alex con2bii ) ABCADBEABFG $.

  $( Part of theorem *11.5 in [WhiteheadRussell] p. 164.  (Contributed by
     Andrew Salmon, 24-May-2011.) $)
  2nalexn $p |- ( -. A. x A. y ph <-> E. x E. y -. ph ) $=
    ( wn wex wal df-ex alex albii xchbinxr bicomi ) ADCEZBEZACFZBFZDMLDZBFOLBGN
    PBACHIJK $.

  $( Theorem *11.22 in [WhiteheadRussell] p. 160.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  2exnaln $p |- ( E. x E. y ph <-> -. A. x A. y -. ph ) $=
    ( wex wn wal df-ex alnex albii xchbinxr ) ACDZBDKEZBFAECFZBFKBGMLBACHIJ $.

  $( Theorem *11.25 in [WhiteheadRussell] p. 160.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  2nexaln $p |- ( -. E. x E. y ph <-> A. x A. y -. ph ) $=
    ( wn wal wex 2exnaln bicomi con1bii ) ADCEBEZACFBFZKJDABCGHI $.

  $( An equivalence between an implication with a universally quantified
     consequent and an implication with an existentially quantified antecedent.
     An interesting case is when the same formula is substituted for both
     ` ph ` and ` ps ` , since then both implications express a type of
     nonfreeness.  See also ~ eximal .  (Contributed by BJ, 12-May-2019.) $)
  alimex $p |- ( ( ph -> A. x ps ) <-> ( E. x -. ps -> -. ph ) ) $=
    ( wal wi wn wex alex imbi2i con2b bitri ) ABCDZEABFCGZFZEMAFELNABCHIAMJK $.

  ${
    aleximi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A variant of ~ al2imi : instead of applying ` A. x ` quantifiers to the
       final implication, replace them with ` E. x ` .  A shorter proof is
       possible using ~ nfa1 , ~ sps and ~ eximd , but it depends on more
       axioms.  (Contributed by Wolf Lammen, 18-Aug-2019.) $)
    aleximi $p |- ( A. x ph -> ( E. x ps -> E. x ch ) ) $=
      ( wal wex wn con3d al2imi alnex 3imtr3g con4d ) ADFZCDGZBDGZNCHZDFBHZDFOH
      PHAQRDABCEIJCDKBDKLM $.
  $}

  ${
    alexbii.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Biconditional form of ~ aleximi .  (Contributed by BJ, 16-Nov-2020.) $)
    alexbii $p |- ( A. x ph -> ( E. x ps <-> E. x ch ) ) $=
      ( wal wex biimpd aleximi biimprd impbid ) ADFBDGCDGABCDABCEHIACBDABCEJIK
      $.
  $}

  $( Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM, 10-Jan-1993.)
     (Proof shortened by Wolf Lammen, 4-Jul-2014.) $)
  exim $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $=
    ( wi id aleximi ) ABDZABCGEF $.

  ${
    eximi.1 $e |- ( ph -> ps ) $.
    $( Inference adding existential quantifier to antecedent and consequent.
       (Contributed by NM, 10-Jan-1993.) $)
    eximi $p |- ( E. x ph -> E. x ps ) $=
      ( wi wex exim mpg ) ABEACFBCFECABCGDH $.

    $( Inference adding two existential quantifiers to antecedent and
       consequent.  (Contributed by NM, 3-Feb-2005.) $)
    2eximi $p |- ( E. x E. y ph -> E. x E. y ps ) $=
      ( wex eximi ) ADFBDFCABDEGG $.
  $}

  ${
    eximii.1 $e |- E. x ph $.
    eximii.2 $e |- ( ph -> ps ) $.
    $( Inference associated with ~ eximi .  (Contributed by BJ, 3-Feb-2018.) $)
    eximii $p |- E. x ps $=
      ( wex eximi ax-mp ) ACFBCFDABCEGH $.
  $}

  $( Add an antecedent in an existentially quantified formula.  (Contributed by
     BJ, 6-Oct-2018.) $)
  exa1 $p |- ( E. x ph -> E. x ( ps -> ph ) ) $=
    ( wi ax-1 eximi ) ABADCABEF $.

  $( Theorem 19.38 of [Margaris] p. 90.  The converse holds under nonfreeness
     conditions, see ~ 19.38a and ~ 19.38b .  (Contributed by NM, 12-Mar-1993.)
     Allow a shortening of ~ 19.21t .  (Revised by Wolf Lammen, 2-Jan-2018.) $)
  19.38 $p |- ( ( E. x ph -> A. x ps ) -> A. x ( ph -> ps ) ) $=
    ( wex wal wi wn alnex pm2.21 alimi sylbir ala1 ja ) ACDZBCEABFZCEZNGAGZCEPA
    CHQOCABIJKBACLM $.

  $( Under a nonfreeness hypothesis, the implication ~ 19.38 can be
     strengthened to an equivalence.  See also ~ 19.38b .  (Contributed by BJ,
     3-Nov-2021.)  (Proof shortened by Wolf Lammen, 9-Jul-2022.) $)
  19.38a $p |-
             ( F/ x ph -> ( ( E. x ph -> A. x ps ) <-> A. x ( ph -> ps ) ) ) $=
    ( wnf wex wal wi 19.38 id nfrd alim syl9 impbid2 ) ACDZACEZBCFZGABGCFZABCHN
    OACFQPNACNIJABCKLM $.

  $( Under a nonfreeness hypothesis, the implication ~ 19.38 can be
     strengthened to an equivalence.  See also ~ 19.38a .  (Contributed by BJ,
     3-Nov-2021.)  (Proof shortened by Wolf Lammen, 9-Jul-2022.) $)
  19.38b $p |-
             ( F/ x ps -> ( ( E. x ph -> A. x ps ) <-> A. x ( ph -> ps ) ) ) $=
    ( wnf wex wal wi 19.38 exim id nfrd syl9r impbid2 ) BCDZACEZBCFZGABGCFZABCH
    QOBCENPABCINBCNJKLM $.

  $( Quantified implication in terms of quantified negation of conjunction.
     (Contributed by BJ, 16-Jul-2021.) $)
  imnang $p |- ( A. x ( ph -> -. ps ) <-> A. x -. ( ph /\ ps ) ) $=
    ( wn wi wa imnan albii ) ABDEABFDCABGH $.

  $( A transformation of quantifiers and logical connectives.  (Contributed by
     NM, 19-Aug-1993.) $)
  alinexa $p |- ( A. x ( ph -> -. ps ) <-> -. E. x ( ph /\ ps ) ) $=
    ( wn wi wal wa wex imnang alnex bitri ) ABDECFABGZDCFLCHDABCILCJK $.

  $( Existential quantification of a conjunction expressed with only primitive
     symbols ( ` -> ` , ` -. ` , ` A. ` ).  (Contributed by NM, 10-May-1993.)
     State the most general instance.  (Revised by BJ, 29-Sep-2019.) $)
  exnalimn $p |- ( E. x ( ph /\ ps ) <-> -. A. x ( ph -> -. ps ) ) $=
    ( wn wi wal wa wex alinexa con2bii ) ABDECFABGCHABCIJ $.

  $( A relationship between two quantifiers and negation.  (Contributed by NM,
     18-Aug-1993.) $)
  alexn $p |- ( A. x E. y -. ph <-> -. E. x A. y ph ) $=
    ( wn wex wal exnal albii alnex bitri ) ADCEZBFACFZDZBFLBEDKMBACGHLBIJ $.

  $( Theorem *11.51 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
     Salmon, 24-May-2011.)  (Proof shortened by Wolf Lammen, 25-Sep-2014.) $)
  2exnexn $p |- ( E. x A. y ph <-> -. A. x E. y -. ph ) $=
    ( wn wex wal alexn con2bii ) ADCEBFACFBEABCGH $.

  $( Theorem 19.18 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
  exbi $p |- ( A. x ( ph <-> ps ) -> ( E. x ph <-> E. x ps ) ) $=
    ( wb id alexbii ) ABDZABCGEF $.

  ${
    exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding existential quantifier to both sides of an equivalence.
       (Contributed by NM, 24-May-1994.) $)
    exbii $p |- ( E. x ph <-> E. x ps ) $=
      ( wb wex exbi mpg ) ABEACFBCFECABCGDH $.
  $}

  ${
    2exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding two existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 16-Mar-1995.) $)
    2exbii $p |- ( E. x E. y ph <-> E. x E. y ps ) $=
      ( wex exbii ) ADFBDFCABDEGG $.
  $}

  ${
    3exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding three existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 2-May-1995.) $)
    3exbii $p |- ( E. x E. y E. z ph <-> E. x E. y E. z ps ) $=
      ( wex exbii 2exbii ) AEGBEGCDABEFHI $.
  $}

  $( Equivalence theorem for the nonfreeness predicate.  Closed form of
     ~ nfbii .  (Contributed by Giovanni Mascellani, 10-Apr-2018.)  Reduce
     axiom usage.  (Revised by BJ, 6-May-2019.) $)
  nfbiit $p |- ( A. x ( ph <-> ps ) -> ( F/ x ph <-> F/ x ps ) ) $=
    ( wb wal wex wi wnf exbi albi imbi12d df-nf 3bitr4g ) ABDCEZACFZACEZGBCFZBC
    EZGACHBCHNOQPRABCIABCJKACLBCLM $.

  ${
    nfbii.1 $e |- ( ph <-> ps ) $.
    $( Equality theorem for the nonfreeness predicate.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) ~ df-nf changed.  (Revised by Wolf Lammen,
       12-Sep-2021.) $)
    nfbii $p |- ( F/ x ph <-> F/ x ps ) $=
      ( wb wnf nfbiit mpg ) ABEACFBCFECABCGDH $.

    ${
      nfxfr.2 $e |- F/ x ps $.
      $( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
      nfxfr $p |- F/ x ph $=
        ( wnf nfbii mpbir ) ACFBCFEABCDGH $.
    $}

    ${
      nfxfrd.2 $e |- ( ch -> F/ x ps ) $.
      $( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 24-Sep-2016.) $)
      nfxfrd $p |- ( ch -> F/ x ph ) $=
        ( wnf nfbii sylibr ) CBDGADGFABDEHI $.
    $}
  $}

  $( A variable is nonfree in a proposition if and only if it is so in its
     negation.  (Contributed by BJ, 6-May-2019.)  (Proof shortened by Wolf
     Lammen, 6-Oct-2024.) $)
  nfnbi $p |- ( F/ x ph <-> F/ x -. ph ) $=
    ( wn wex wal wi wnf exnal imbi1i df-nf nf4 3bitr4ri ) ACZBDZMBEZFABECZOFMBG
    ABGNPOABHIMBJABKL $.

  $( If a variable is nonfree in a proposition, then it is nonfree in its
     negation.  (Contributed by Mario Carneiro, 24-Sep-2016.)  (Proof shortened
     by Wolf Lammen, 28-Dec-2017.)  (Revised by BJ, 24-Jul-2019.) ~ df-nf
     changed.  (Revised by Wolf Lammen, 4-Oct-2021.) $)
  nfnt $p |- ( F/ x ph -> F/ x -. ph ) $=
    ( wnf wn nfnbi biimpi ) ABCADBCABEF $.

  ${
    nfn.1 $e |- F/ x ph $.
    $( Inference associated with ~ nfnt .  (Contributed by Mario Carneiro,
       11-Aug-2016.) ~ df-nf changed.  (Revised by Wolf Lammen,
       18-Sep-2021.) $)
    nfn $p |- F/ x -. ph $=
      ( wnf wn nfnt ax-mp ) ABDAEBDCABFG $.
  $}

  ${
    nfnd.1 $e |- ( ph -> F/ x ps ) $.
    $( Deduction associated with ~ nfnt .  (Contributed by Mario Carneiro,
       24-Sep-2016.) $)
    nfnd $p |- ( ph -> F/ x -. ps ) $=
      ( wnf wn nfnt syl ) ABCEBFCEDBCGH $.
  $}

  $( A transformation of quantifiers and logical connectives.  (Contributed by
     NM, 25-Mar-1996.)  (Proof shortened by Wolf Lammen, 4-Sep-2014.) $)
  exanali $p |- ( E. x ( ph /\ -. ps ) <-> -. A. x ( ph -> ps ) ) $=
    ( wn wa wex wi wal annim exbii exnal bitri ) ABDEZCFABGZDZCFNCHDMOCABIJNCKL
    $.

  $( Theorem *11.521 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  2exanali $p |- ( -. E. x E. y ( ph /\ -. ps ) <->
        A. x A. y ( ph -> ps ) ) $=
    ( wi wn wex wal wa 2nalexn con1bii annim 2exbii xchnxbir ) ABEZFZDGCGZODHCH
    ZABFIZDGCGRQOCDJKSPCDABLMN $.

  $( Commutation of conjunction inside an existential quantifier.  (Contributed
     by NM, 18-Aug-1993.) $)
  exancom $p |- ( E. x ( ph /\ ps ) <-> E. x ( ps /\ ph ) ) $=
    ( wa ancom exbii ) ABDBADCABEF $.

  ${
    exan.1 $e |- E. x ph $.
    exan.2 $e |- ps $.
    $( Place a conjunct in the scope of an existential quantifier.
       (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof shortened by Wolf Lammen, 13-Jan-2018.)  Reduce
       axiom dependencies.  (Revised by BJ, 7-Jul-2021.)  (Proof shortened by
       Wolf Lammen, 6-Nov-2022.)  Expand hypothesis.  (Revised by Steven
       Nguyen, 19-Jun-2023.) $)
    exan $p |- E. x ( ph /\ ps ) $=
      ( wa jctr eximii ) AABFCDABEGH $.
  $}

  ${
    alrimdh.1 $e |- ( ph -> A. x ph ) $.
    alrimdh.2 $e |- ( ps -> A. x ps ) $.
    alrimdh.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.21 of [Margaris] p. 90, see ~ 19.21 and
       ~ 19.21h .  (Contributed by NM, 10-Feb-1997.)  (Proof shortened by
       Andrew Salmon, 13-May-2011.) $)
    alrimdh $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( wal alimdh syl5 ) BBDHACDHFABCDEGIJ $.
  $}

  ${
    eximdh.1 $e |- ( ph -> A. x ph ) $.
    eximdh.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       20-May-1996.) $)
    eximdh $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( wal wex wi aleximi syl ) AADGBDHCDHIEABCDFJK $.
  $}

  ${
    nexdh.1 $e |- ( ph -> A. x ph ) $.
    nexdh.2 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by NM,
       2-Jan-2002.) $)
    nexdh $p |- ( ph -> -. E. x ps ) $=
      ( wn wal wex alrimih alnex sylib ) ABFZCGBCHFALCDEIBCJK $.
  $}

  ${
    albidh.1 $e |- ( ph -> A. x ph ) $.
    albidh.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction form).
       (Contributed by NM, 26-May-1993.) $)
    albidh $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( wb wal alrimih albi syl ) ABCGZDHBDHCDHGALDEFIBCDJK $.
  $}

  ${
    exbidh.1 $e |- ( ph -> A. x ph ) $.
    exbidh.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for existential quantifier (deduction form).
       (Contributed by NM, 26-May-1993.) $)
    exbidh $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( wal wex wb alexbii syl ) AADGBDHCDHIEABCDFJK $.
  $}

  $( Simplification of an existentially quantified conjunction.  (Contributed
     by Rodolfo Medina, 25-Sep-2010.)  (Proof shortened by Andrew Salmon,
     29-Jun-2011.) $)
  exsimpl $p |- ( E. x ( ph /\ ps ) -> E. x ph ) $=
    ( wa simpl eximi ) ABDACABEF $.

  $( Simplification of an existentially quantified conjunction.  (Contributed
     by Rodolfo Medina, 25-Sep-2010.)  (Proof shortened by Andrew Salmon,
     29-Jun-2011.) $)
  exsimpr $p |- ( E. x ( ph /\ ps ) -> E. x ps ) $=
    ( wa simpr eximi ) ABDBCABEF $.

  $( Theorem 19.26 of [Margaris] p. 90.  Also Theorem *10.22 of
     [WhiteheadRussell] p. 147.  (Contributed by NM, 12-Mar-1993.)  (Proof
     shortened by Wolf Lammen, 4-Jul-2014.) $)
  19.26 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $=
    ( wa wal simpl alimi simpr jca id alanimi impbii ) ABDZCEZACEZBCEZDNOPMACAB
    FGMBCABHGIABMCMJKL $.

  $( Theorem ~ 19.26 with two quantifiers.  (Contributed by NM, 3-Feb-2005.) $)
  19.26-2 $p |- ( A. x A. y ( ph /\ ps ) <->
                ( A. x A. y ph /\ A. x A. y ps ) ) $=
    ( wa wal 19.26 albii bitri ) ABEDFZCFADFZBDFZEZCFKCFLCFEJMCABDGHKLCGI $.

  $( Theorem ~ 19.26 with triple conjunction.  (Contributed by NM,
     13-Sep-2011.) $)
  19.26-3an $p |- ( A. x ( ph /\ ps /\ ch )
                   <-> ( A. x ph /\ A. x ps /\ A. x ch ) ) $=
    ( wa wal w3a 19.26 anbi1i df-3an albii bitri 3bitr4i ) ABEZDFZCDFZEZADFZBDF
    ZEZPEABCGZDFZRSPGOTPABDHIUBNCEZDFQUAUCDABCJKNCDHLRSPJM $.

  $( Theorem 19.29 of [Margaris] p. 90.  See also ~ 19.29r .  (Contributed by
     NM, 21-Jun-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
  19.29 $p |- ( ( A. x ph /\ E. x ps ) -> E. x ( ph /\ ps ) ) $=
    ( wal wex wa pm3.2 aleximi imp ) ACDBCEABFZCEABJCABGHI $.

  $( Variation of ~ 19.29 .  (Contributed by NM, 18-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 12-Nov-2020.) $)
  19.29r $p |- ( ( E. x ph /\ A. x ps ) -> E. x ( ph /\ ps ) ) $=
    ( wal wex wa pm3.21 aleximi impcom ) BCDACEABFZCEBAJCBAGHI $.

  $( Variation of ~ 19.29r with double quantification.  (Contributed by NM,
     3-Feb-2005.) $)
  19.29r2 $p |- ( ( E. x E. y ph /\ A. x A. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    ( wex wal wa 19.29r eximi syl ) ADEZCEBDFZCFGKLGZCEABGDEZCEKLCHMNCABDHIJ $.

  $( Variation of ~ 19.29 with mixed quantification.  (Contributed by NM,
     11-Feb-2005.) $)
  19.29x $p |- ( ( E. x A. y ph /\ A. x E. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    ( wal wex wa 19.29r 19.29 eximi syl ) ADEZCFBDFZCEGLMGZCFABGDFZCFLMCHNOCABD
    IJK $.

  $( Theorem 19.35 of [Margaris] p. 90.  This theorem is useful for moving an
     implication (in the form of the right-hand side) into the scope of a
     single existential quantifier.  (Contributed by NM, 12-Mar-1993.)  (Proof
     shortened by Wolf Lammen, 27-Jun-2014.) $)
  19.35 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $=
    ( wi wex wal pm2.27 aleximi com12 wn exnal pm2.21 eximi sylbir exa1 impbii
    ja ) ABDZCEZACFZBCEZDTSUAARBCABGHITUASTJAJZCESACKUBRCABLMNBACOQP $.

  ${
    19.35i.1 $e |- E. x ( ph -> ps ) $.
    $( Inference associated with ~ 19.35 .  (Contributed by NM,
       21-Jun-1993.) $)
    19.35i $p |- ( A. x ph -> E. x ps ) $=
      ( wi wex wal 19.35 mpbi ) ABECFACGBCFEDABCHI $.
  $}

  ${
    19.35ri.1 $e |- ( A. x ph -> E. x ps ) $.
    $( Inference associated with ~ 19.35 .  (Contributed by NM,
       12-Mar-1993.) $)
    19.35ri $p |- E. x ( ph -> ps ) $=
      ( wi wex wal 19.35 mpbir ) ABECFACGBCFEDABCHI $.
  $}

  $( Theorem 19.25 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
  19.25 $p |- ( A. y E. x ( ph -> ps ) ->
              ( E. y A. x ph -> E. y E. x ps ) ) $=
    ( wi wex wal 19.35 biimpi aleximi ) ABECFZACGZBCFZDKLMEABCHIJ $.

  $( Theorem 19.30 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.)
     (Proof shortened by Andrew Salmon, 25-May-2011.) $)
  19.30 $p |- ( A. x ( ph \/ ps ) -> ( A. x ph \/ E. x ps ) ) $=
    ( wo wal wex wn exnal pm2.53 aleximi biimtrrid orrd ) ABDZCEZACEZBCFZOGAGZC
    FNPACHMQBCABIJKL $.

  $( Theorem 19.43 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.)
     (Proof shortened by Wolf Lammen, 27-Jun-2014.) $)
  19.43 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    ( wo wex wn wi wal df-or exbii 19.35 alnex imbi1i 3bitri bitr4i ) ABDZCEZAC
    EZFZBCEZGZRTDQAFZBGZCEUBCHZTGUAPUCCABIJUBBCKUDSTACLMNRTIO $.

  $( Obsolete proof of ~ 19.43 .  Do not delete as it is referenced on the
     ~ mmrecent.html page and in ~ conventions-labels .  (Contributed by NM,
     5-Aug-1993.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  19.43OLD $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    ( wo wn wal wex wa ioran albii 19.26 alnex anbi12i 3bitri notbii df-ex oran
    3bitr4i ) ABDZEZCFZEACGZEZBCGZEZHZESCGUBUDDUAUFUAAEZBEZHZCFUGCFZUHCFZHUFTUI
    CABIJUGUHCKUJUCUKUEACLBCLMNOSCPUBUDQR $.

  $( Theorem 19.33 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
  19.33 $p |- ( ( A. x ph \/ A. x ps ) -> A. x ( ph \/ ps ) ) $=
    ( wal wo orc alimi olc jaoi ) ACDABEZCDBCDAJCABFGBJCBAHGI $.

  $( The antecedent provides a condition implying the converse of ~ 19.33 .
     (Contributed by NM, 27-Mar-2004.)  (Proof shortened by Andrew Salmon,
     25-May-2011.)  (Proof shortened by Wolf Lammen, 5-Jul-2014.) $)
  19.33b $p |- ( -. ( E. x ph /\ E. x ps ) ->
               ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) ) $=
    ( wex wa wn wo wal wi ianor alnex pm2.53 al2imi biimtrrid olc syl6com 19.30
    orcomd ord orc jaoi sylbi 19.33 impbid1 ) ACDZBCDZEFZABGZCHZACHZBCHZGZUGUEF
    ZUFFZGUIULIZUEUFJUMUOUNUIUMUKULUMAFZCHUIUKACKUHUPBCABLMNUKUJOPUIUNUJULUIUFU
    JUIUJUFABCQRSUJUKTPUAUBABCUCUD $.

  $( Theorem 19.40 of [Margaris] p. 90.  (Contributed by NM, 26-May-1993.) $)
  19.40 $p |- ( E. x ( ph /\ ps ) -> ( E. x ph /\ E. x ps ) ) $=
    ( wa wex exsimpl exsimpr jca ) ABDCEACEBCEABCFABCGH $.

  $( Theorem *11.42 in [WhiteheadRussell] p. 163.  Theorem 19.40 of [Margaris]
     p. 90 with two quantifiers.  (Contributed by Andrew Salmon,
     24-May-2011.) $)
  19.40-2 $p |- ( E. x E. y ( ph /\ ps ) ->
                                          ( E. x E. y ph /\ E. x E. y ps ) ) $=
    ( wa wex 19.40 eximi syl ) ABEDFZCFADFZBDFZEZCFKCFLCFEJMCABDGHKLCGI $.

  $( The antecedent provides a condition implying the converse of ~ 19.40 .
     This is to ~ 19.40 what ~ 19.33b is to ~ 19.33 .  (Contributed by BJ,
     6-May-2019.)  (Proof shortened by Wolf Lammen, 13-Nov-2020.) $)
  19.40b $p |- ( ( A. x ph \/ A. x ps ) ->
                          ( ( E. x ph /\ E. x ps ) <-> E. x ( ph /\ ps ) ) ) $=
    ( wal wo wex wa wi pm3.21 aleximi pm3.2 jaoa orcoms 19.40 impbid1 ) ACDZBCD
    ZEACFZBCFZGZABGZCFZQPTUBHQRUBPSBAUACBAIJABUACABKJLMABCNO $.

  $( Split a biconditional and distribute quantifier.  (Contributed by NM,
     18-Aug-1993.) $)
  albiim $p |- ( A. x ( ph <-> ps ) <->
             ( A. x ( ph -> ps ) /\ A. x ( ps -> ph ) ) ) $=
    ( wb wal wi wa dfbi2 albii 19.26 bitri ) ABDZCEABFZBAFZGZCEMCENCEGLOCABHIMN
    CJK $.

  $( Split a biconditional and distribute two quantifiers.  (Contributed by NM,
     3-Feb-2005.) $)
  2albiim $p |- ( A. x A. y ( ph <-> ps ) <->
             ( A. x A. y ( ph -> ps ) /\ A. x A. y ( ps -> ph ) ) ) $=
    ( wb wal wi wa albiim albii 19.26 bitri ) ABEDFZCFABGDFZBAGDFZHZCFNCFOCFHMP
    CABDIJNOCKL $.

  $( Add/remove a conjunct in the scope of an existential quantifier.
     (Contributed by Raph Levien, 3-Jul-2006.) $)
  exintrbi $p |- ( A. x ( ph -> ps ) -> ( E. x ph <-> E. x ( ph /\ ps ) ) ) $=
    ( wi wa abai rbaibr alexbii ) ABDZAABEZCJAIABFGH $.

  $( Introduce a conjunct in the scope of an existential quantifier.
     (Contributed by NM, 11-Aug-1993.)  (Proof shortened by BJ,
     16-Sep-2022.) $)
  exintr $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ( ph /\ ps ) ) ) $=
    ( wi wa ancl aleximi ) ABDAABECABFG $.

  $( Universally quantified and uncurried (imported) form of syllogism.
     Theorem *10.3 in [WhiteheadRussell] p. 150.  (Contributed by Andrew
     Salmon, 8-Jun-2011.) $)
  alsyl $p |- ( ( A. x ( ph -> ps ) /\ A. x ( ps -> ch ) ) ->
        A. x ( ph -> ch ) ) $=
    ( wi pm3.33 alanimi ) ABEBCEACEDABCFG $.

  ${
    nfimd.1 $e |- ( ph -> F/ x ps ) $.
    nfimd.2 $e |- ( ph -> F/ x ch ) $.
    $( If in a context ` x ` is not free in ` ps ` and ` ch ` , then it is not
       free in ` ( ps -> ch ) ` .  Deduction form of ~ nfim .  (Contributed by
       Mario Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf Lammen,
       30-Dec-2017.) ~ df-nf changed.  (Revised by Wolf Lammen, 18-Sep-2021.)
       Eliminate curried form of ~ nfimt .  (Revised by Wolf Lammen,
       10-Jul-2022.) $)
    nfimd $p |- ( ph -> F/ x ( ps -> ch ) ) $=
      ( wi wex wal 19.35 biimpi nfrd imim12d 19.38 syl56 nfd ) ABCGZDQDHZBDIZCD
      HZGZABDHZCDIZGQDIRUABCDJKAUBSTUCABDELACDFLMBCDNOP $.
  $}

  $( Closed form of ~ nfim and ~ nfimd .  (Contributed by BJ, 20-Oct-2021.)
     Eliminate curried form, former name nfimt2.  (Revised by Wolf Lammen,
     6-Jul-2022.) $)
  nfimt $p |- ( ( F/ x ph /\ F/ x ps ) -> F/ x ( ph -> ps ) ) $=
    ( wnf wa simpl simpr nfimd ) ACDZBCDZEABCIJFIJGH $.

  ${
    nfim.1 $e |- F/ x ph $.
    nfim.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , then it is not free in
       ` ( ph -> ps ) ` .  Inference associated with ~ nfimt .  (Contributed by
       Mario Carneiro, 11-Aug-2016.)  (Proof shortened by Wolf Lammen,
       2-Jan-2018.) ~ df-nf changed.  (Revised by Wolf Lammen, 17-Sep-2021.) $)
    nfim $p |- F/ x ( ph -> ps ) $=
      ( wnf wi nfimt mp2an ) ACFBCFABGCFDEABCHI $.
  $}

  ${
    nfand.1 $e |- ( ph -> F/ x ps ) $.
    nfand.2 $e |- ( ph -> F/ x ch ) $.
    $( If in a context ` x ` is not free in ` ps ` and ` ch ` , then it is not
       free in ` ( ps /\ ch ) ` .  (Contributed by Mario Carneiro,
       7-Oct-2016.) $)
    nfand $p |- ( ph -> F/ x ( ps /\ ch ) ) $=
      ( wa wn wi df-an nfnd nfimd nfxfrd ) BCGBCHZIZHADBCJAODABNDEACDFKLKM $.

    nfand.3 $e |- ( ph -> F/ x th ) $.
    $( Deduction form of bound-variable hypothesis builder ~ nf3an .
       (Contributed by NM, 17-Feb-2013.)  (Revised by Mario Carneiro,
       16-Oct-2016.) $)
    nf3and $p |- ( ph -> F/ x ( ps /\ ch /\ th ) ) $=
      ( w3a wa df-3an nfand nfxfrd ) BCDIBCJZDJAEBCDKANDEABCEFGLHLM $.
  $}

  ${
    nfan.1 $e |- F/ x ph $.
    nfan.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , then it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.)
       (Proof shortened by Wolf Lammen, 13-Jan-2018.)  (Proof shortened by Wolf
       Lammen, 9-Oct-2021.) $)
    nfan $p |- F/ x ( ph /\ ps ) $=
      ( wa wnf wtru a1i nfand mptru ) ABFCGHABCACGHDIBCGHEIJK $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , then it is not free in
       ` ( ph -/\ ps ) ` .  (Contributed by Scott Fenton, 2-Jan-2018.) $)
    nfnan $p |- F/ x ( ph -/\ ps ) $=
      ( wnan wa wn df-nan nfan nfn nfxfr ) ABFABGZHCABIMCABCDEJKL $.

    nfan.3 $e |- F/ x ch $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , then it is not
       free in ` ( ph /\ ps /\ ch ) ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nf3an $p |- F/ x ( ph /\ ps /\ ch ) $=
      ( w3a wa df-3an nfan nfxfr ) ABCHABIZCIDABCJMCDABDEFKGKL $.
  $}

  ${
    nfbid.1 $e |- ( ph -> F/ x ps ) $.
    nfbid.2 $e |- ( ph -> F/ x ch ) $.
    $( If in a context ` x ` is not free in ` ps ` and ` ch ` , then it is not
       free in ` ( ps <-> ch ) ` .  (Contributed by Mario Carneiro,
       24-Sep-2016.)  (Proof shortened by Wolf Lammen, 29-Dec-2017.) $)
    nfbid $p |- ( ph -> F/ x ( ps <-> ch ) ) $=
      ( wb wi wa dfbi2 nfimd nfand nfxfrd ) BCGBCHZCBHZIADBCJANODABCDEFKACBDFEK
      LM $.
  $}

  ${
    nf.1 $e |- F/ x ph $.
    nf.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , then it is not free in
       ` ( ph <-> ps ) ` .  (Contributed by NM, 26-May-1993.)  (Revised by
       Mario Carneiro, 11-Aug-2016.)  (Proof shortened by Wolf Lammen,
       2-Jan-2018.) $)
    nfbi $p |- F/ x ( ph <-> ps ) $=
      ( wb wnf wtru a1i nfbid mptru ) ABFCGHABCACGHDIBCGHEIJK $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , then it is not free in
       ` ( ph \/ ps ) ` .  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario
       Carneiro, 11-Aug-2016.) $)
    nfor $p |- F/ x ( ph \/ ps ) $=
      ( wo wn wi df-or nfn nfim nfxfr ) ABFAGZBHCABIMBCACDJEKL $.

    nf.3 $e |- F/ x ch $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , then it is not
       free in ` ( ph \/ ps \/ ch ) ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nf3or $p |- F/ x ( ph \/ ps \/ ch ) $=
      ( w3o wo df-3or nfor nfxfr ) ABCHABIZCIDABCJMCDABDEFKGKL $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The empty domain of discourse
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  This database develops mathematics from first-order logic, which has only
  nonempty models.  Before stating axioms excluding the empty model
  (typically, ~ ax-6 in logic and ~ ax-nul in set theory), we state in this
  short subsection a few results relative to the empty domain, which we
  characterize by the assumption ` -. E. x T. ` .  As expected, on the empty
  domain, every universally quantified formula is true ( ~ emptyal ) and every
  existential formula is false ( ~ emptyex ), and every variable is effectively
  nonfree in any formula ( ~ emptynf ).

$)

  $( Two characterizations of the empty domain.  (Contributed by G&eacute;rard
     Lang, 5-Feb-2024.) $)
  empty $p |- ( -. E. x T. <-> A. x F. ) $=
    ( wfal wal wtru wn wex df-fal albii alnex bitr2i ) BACDEZACDAFEBKAGHDAIJ $.

  $( On the empty domain, any existentially quantified formula is false.
     (Contributed by Wolf Lammen, 21-Jan-2024.) $)
  emptyex $p |- ( -. E. x T. -> -. E. x ph ) $=
    ( wex wtru trud eximi con3i ) ABCDBCADBAEFG $.

  $( On the empty domain, any universally quantified formula is true.
     (Contributed by Wolf Lammen, 12-Mar-2023.) $)
  emptyal $p |- ( -. E. x T. -> A. x ph ) $=
    ( wtru wex wn wal emptyex alex sylibr ) CBDEAEZBDEABFJBGABHI $.

  $( On the empty domain, any variable is effectively nonfree in any formula.
     (Contributed by Wolf Lammen, 12-Mar-2023.) $)
  emptynf $p |- ( -. E. x T. -> F/ x ph ) $=
    ( wtru wex wn wal wnf emptyal nftht syl ) CBDEABFABGABHABIJ $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-5 (Distinctness) - first use of $d
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x ph $.
    $( Axiom of Distinctness.  This axiom quantifies a variable over a formula
       in which it does not occur.  Axiom C5 in [Megill] p. 444 (p. 11 of the
       preprint).  Also appears as Axiom B6 (p. 75) of system S2 of [Tarski]
       p. 77 and Axiom C5-1 of [Monk2] p. 113.

       (See comments in ~ ax5ALT about the logical redundancy of ~ ax-5 in the
       presence of our obsolete axioms.)

       This axiom essentially says that if ` x ` does not occur in ` ph ` ,
       i.e. ` ph ` does not depend on ` x ` in any way, then we can add the
       quantifier ` A. x ` to ` ph ` with no further assumptions.  By ~ sp , we
       can also remove the quantifier (unconditionally).

       For an explanation of disjoint variable conditions, see
       ~ https://us.metamath.org/mpeuni/mmset.html#distinct .  (Contributed by
       NM, 10-Jan-1993.) $)
    ax-5 $a |- ( ph -> A. x ph ) $.
  $}

  ${
    $d x ps $.
    $( Version of ~ ax-5 with antecedent.  Useful in proofs of deduction
       versions of bound-variable hypothesis builders.  (Contributed by NM,
       1-Mar-2013.) $)
    ax5d $p |- ( ph -> ( ps -> A. x ps ) ) $=
      ( wal wi ax-5 a1i ) BBCDEABCFG $.
  $}

  ${
    $d x ph $.
    $( A rephrasing of ~ ax-5 using the existential quantifier.  (Contributed
       by Wolf Lammen, 4-Dec-2017.) $)
    ax5e $p |- ( E. x ph -> ph ) $=
      ( wex wi wn wal ax-5 eximal mpbir ) ABCADAEZJBFDJBGAABHI $.
  $}

  ${
    $d x ph $.
    $( If a formula holds for some value of a variable not occurring in it,
       then it holds for all values of that variable.  (Contributed by BJ,
       28-Dec-2020.) $)
    ax5ea $p |- ( E. x ph -> A. x ph ) $=
      ( wex wal ax5e ax-5 syl ) ABCAABDABEABFG $.
  $}

  ${
    $d x ph $.
    $( If ` x ` is not present in ` ph ` , then ` x ` is not free in ` ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.)  Definition change.
       (Revised by Wolf Lammen, 12-Sep-2021.) $)
    nfv $p |- F/ x ph $=
      ( ax5ea nfi ) ABABCD $.
  $}

  ${
    $d x ps $.
    $( ~ nfv with antecedent.  Useful in proofs of deduction versions of
       bound-variable hypothesis builders such as ~ nfimd .  (Contributed by
       Mario Carneiro, 6-Oct-2016.) $)
    nfvd $p |- ( ph -> F/ x ps ) $=
      ( wnf nfv a1i ) BCDABCEF $.
  $}

  ${
    $d x ph $.
    alimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.20 of [Margaris] p. 90, see ~ alim .  See
       ~ alimdh and ~ alimd for versions without a distinct variable condition.
       (Contributed by NM, 3-Apr-1994.) $)
    alimdv $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      ( ax-5 alimdh ) ABCDADFEG $.

    $( Deduction form of Theorem 19.22 of [Margaris] p. 90, see ~ exim .  See
       ~ eximdh and ~ eximd for versions without a distinct variable condition.
       (Contributed by NM, 27-Apr-1994.) $)
    eximdv $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( ax-5 eximdh ) ABCDADFEG $.
  $}

  ${
    $d x ph $.  $d y ph $.
    2alimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.20 of [Margaris] p. 90 with two
       quantifiers, see ~ alim .  (Contributed by NM, 27-Apr-2004.) $)
    2alimdv $p |- ( ph -> ( A. x A. y ps -> A. x A. y ch ) ) $=
      ( wal alimdv ) ABEGCEGDABCEFHH $.

    $( Deduction form of Theorem 19.22 of [Margaris] p. 90 with two
       quantifiers, see ~ exim .  (Contributed by NM, 3-Aug-1995.) $)
    2eximdv $p |- ( ph -> ( E. x E. y ps -> E. x E. y ch ) ) $=
      ( wex eximdv ) ABEGCEGDABCEFHH $.
  $}

  ${
    $d x ph $.
    albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction form).  See
       also ~ albidh and ~ albid .  (Contributed by NM, 26-May-1993.) $)
    albidv $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( ax-5 albidh ) ABCDADFEG $.

    $( Formula-building rule for existential quantifier (deduction form).  See
       also ~ exbidh and ~ exbid .  (Contributed by NM, 26-May-1993.) $)
    exbidv $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( ax-5 exbidh ) ABCDADFEG $.

    $( An equality theorem for nonfreeness.  See ~ nfbidf for a version without
       disjoint variable condition but requiring more axioms.  (Contributed by
       Mario Carneiro, 4-Oct-2016.)  Remove dependency on ~ ax-6 , ~ ax-7 ,
       ~ ax-12 by adapting proof of ~ nfbidf .  (Revised by BJ,
       25-Sep-2022.) $)
    nfbidv $p |- ( ph -> ( F/ x ps <-> F/ x ch ) ) $=
      ( wex wal wi wnf exbidv albidv imbi12d df-nf 3bitr4g ) ABDFZBDGZHCDFZCDGZ
      HBDICDIAOQPRABCDEJABCDEKLBDMCDMN $.
  $}

  ${
    $d x ph $.  $d y ph $.
    2albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for two universal quantifiers (deduction form).
       (Contributed by NM, 4-Mar-1997.) $)
    2albidv $p |- ( ph -> ( A. x A. y ps <-> A. x A. y ch ) ) $=
      ( wal albidv ) ABEGCEGDABCEFHH $.

    $( Formula-building rule for two existential quantifiers (deduction form).
       (Contributed by NM, 1-May-1995.) $)
    2exbidv $p |- ( ph -> ( E. x E. y ps <-> E. x E. y ch ) ) $=
      ( wex exbidv ) ABEGCEGDABCEFHH $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.
    3exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for three existential quantifiers (deduction
       form).  (Contributed by NM, 1-May-1995.) $)
    3exbidv $p |- ( ph -> ( E. x E. y E. z ps <-> E. x E. y E. z ch ) ) $=
      ( wex exbidv 2exbidv ) ABFHCFHDEABCFGIJ $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.  $d w ph $.
    4exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for four existential quantifiers (deduction form).
       (Contributed by NM, 3-Aug-1995.) $)
    4exbidv $p |- ( ph ->
                     ( E. x E. y E. z E. w ps <-> E. x E. y E. z E. w ch ) ) $=
      ( wex 2exbidv ) ABGIFICGIFIDEABCFGHJJ $.
  $}

  ${
    $d x ph $.
    alrimiv.1 $e |- ( ph -> ps ) $.
    $( Inference form of Theorem 19.21 of [Margaris] p. 90.  See ~ 19.21 and
       ~ 19.21v .  (Contributed by NM, 21-Jun-1993.) $)
    alrimiv $p |- ( ph -> A. x ps ) $=
      ( ax-5 alrimih ) ABCACEDF $.
  $}

  ${
    $d x ph $.  $d y ph $.
    alrimivv.1 $e |- ( ph -> ps ) $.
    $( Inference form of Theorem 19.21 of [Margaris] p. 90.  See ~ 19.21 and
       ~ 19.21v .  (Contributed by NM, 31-Jul-1995.) $)
    alrimivv $p |- ( ph -> A. x A. y ps ) $=
      ( wal alrimiv ) ABDFCABDEGG $.
  $}

  ${
    $d x ph $.  $d x ps $.
    alrimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.21 of [Margaris] p. 90.  See ~ 19.21 and
       ~ 19.21v .  (Contributed by NM, 10-Feb-1997.) $)
    alrimdv $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( ax-5 alrimdh ) ABCDADFBDFEG $.
  $}

  ${
    $d x ps $.
    exlimiv.1 $e |- ( ph -> ps ) $.
    $( Inference form of Theorem 19.23 of [Margaris] p. 90, see ~ 19.23 .

       See ~ exlimi for a more general version requiring more axioms.

       This inference, along with its many variants such as ~ rexlimdv , is
       used to implement a metatheorem called "Rule C" that is given in many
       logic textbooks.  See, for example, Rule C in [Mendelson] p. 81, Rule C
       in [Margaris] p. 40, or Rule C in Hirst and Hirst's _A Primer for Logic
       and Proof_ p. 59 (PDF p. 65) at
       ~ http://www.appstate.edu/~~hirstjl/primer/hirst.pdf .  In informal
       proofs, the statement "Let ` C ` be an element such that..." almost
       always means an implicit application of Rule C.

       In essence, Rule C states that if we can prove that some element ` x `
       exists satisfying a wff, i.e. ` E. x ph ( x ) ` where ` ph ( x ) ` has
       ` x ` free, then we can use ` ph ( C ) ` as a hypothesis for the proof
       where ` C ` is a new (fictitious) constant not appearing previously in
       the proof, nor in any axioms used, nor in the theorem to be proved.  The
       purpose of Rule C is to get rid of the existential quantifier.

       We cannot do this in Metamath directly.  Instead, we use the original
       ` ph ` (containing ` x ` ) as an antecedent for the main part of the
       proof.  We eventually arrive at ` ( ph -> ps ) ` where ` ps ` is the
       theorem to be proved and does not contain ` x ` .  Then we apply
       ~ exlimiv to arrive at ` ( E. x ph -> ps ) ` .  Finally, we separately
       prove ` E. x ph ` and detach it with modus ponens ~ ax-mp to arrive at
       the final theorem ` ps ` , see ~ exlimiiv .  (Contributed by NM,
       21-Jun-1993.)  Remove dependencies on ~ ax-6 and ~ ax-8 .  (Revised by
       Wolf Lammen, 4-Dec-2017.) $)
    exlimiv $p |- ( E. x ph -> ps ) $=
      ( wex eximi ax5e syl ) ACEBCEBABCDFBCGH $.

    exlimiiv.2 $e |- E. x ph $.
    $( Inference (Rule C) associated with ~ exlimiv .  (Contributed by BJ,
       19-Dec-2020.) $)
    exlimiiv $p |- ps $=
      ( wex exlimiv ax-mp ) ACFBEABCDGH $.
  $}

  ${
    $d x ps $.  $d y ps $.
    exlimivv.1 $e |- ( ph -> ps ) $.
    $( Inference form of Theorem 19.23 of [Margaris] p. 90, see ~ 19.23 .
       (Contributed by NM, 1-Aug-1995.) $)
    exlimivv $p |- ( E. x E. y ph -> ps ) $=
      ( wex exlimiv ) ADFBCABDEGG $.
  $}

  ${
    $d x ch $.  $d x ph $.
    exlimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.23 of [Margaris] p. 90, see ~ 19.23 .
       (Contributed by NM, 27-Apr-1994.)  Remove dependencies on ~ ax-6 ,
       ~ ax-7 .  (Revised by Wolf Lammen, 4-Dec-2017.) $)
    exlimdv $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( wex eximdv ax5e syl6 ) ABDFCDFCABCDEGCDHI $.
  $}

  ${
    $d x ch $.  $d x ph $.  $d y ch $.  $d y ph $.
    exlimdvv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.23 of [Margaris] p. 90, see ~ 19.23 .
       (Contributed by NM, 31-Jul-1995.) $)
    exlimdvv $p |- ( ph -> ( E. x E. y ps -> ch ) ) $=
      ( wex exlimdv ) ABEGCDABCEFHH $.
  $}

  ${
    $d x ch $.  $d x ph $.
    exlimddv.1 $e |- ( ph -> E. x ps ) $.
    exlimddv.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Existential elimination rule of natural deduction (Rule C, explained in
       ~ exlimiv ).  (Contributed by Mario Carneiro, 15-Jun-2016.) $)
    exlimddv $p |- ( ph -> ch ) $=
      ( wex ex exlimdv mpd ) ABDGCEABCDABCFHIJ $.
  $}

  ${
    $d x ph $.
    nexdv.1 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by NM,
       5-Aug-1993.)  Reduce dependencies on axioms.  (Revised by Wolf Lammen,
       13-Jul-2020.)  (Proof shortened by Wolf Lammen, 10-Oct-2021.) $)
    nexdv $p |- ( ph -> -. E. x ps ) $=
      ( ax-5 nexdh ) ABCACEDF $.
  $}

  ${
    $d x ph $.  $d y ph $.
    $( Quantification of two variables over a formula in which they do not
       occur.  (Contributed by Alan Sare, 12-Apr-2011.) $)
    2ax5 $p |- ( ph -> A. x A. y ph ) $=
      ( id alrimivv ) AABCADE $.
  $}

  ${
    $d x ph $.
    $( Version of ~ stdpc5 with a disjoint variable condition, requiring fewer
       axioms.  (Contributed by BJ, 7-Mar-2020.)  Revised to shorten ~ 19.21v .
       (Revised by Wolf Lammen, 12-Jul-2020.) $)
    stdpc5v $p |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) $=
      ( wal wi ax-5 alim syl5 ) AACDABECDBCDACFABCGH $.

    $( Version of ~ 19.21 with a disjoint variable condition, requiring fewer
       axioms.

       _Notational convention_:  We sometimes suffix with "v" the label of a
       theorem using a distinct variable ("dv") condition instead of a
       nonfreeness hypothesis such as ` F/ x ph ` .  Conversely, we sometimes
       suffix with "f" the label of a theorem introducing such a nonfreeness
       hypothesis ("f" stands for "not free in", see ~ df-nf ) instead of a
       disjoint variable condition.  For instance, ~ 19.21v versus ~ 19.21 and
       ~ vtoclf versus ~ vtocl .  Note that "not free in" is less restrictive
       than "does not occur in".  Note that the version with a disjoint
       variable condition is easily proved from the version with the
       corresponding nonfreeness hypothesis, by using ~ nfv .  However, the dv
       version can often be proved from fewer axioms.  (Contributed by NM,
       21-Jun-1993.)  Reduce dependencies on axioms.  (Revised by Wolf Lammen,
       2-Jan-2020.)  (Proof shortened by Wolf Lammen, 12-Jul-2020.) $)
    19.21v $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( wi wal stdpc5v wex ax5e imim1i 19.38 syl impbii ) ABDCEZABCEZDZABCFOACG
      ZNDMPANACHIABCJKL $.
    $( $j usage '19.21v' avoids 'ax-6' 'ax-7' 'ax-12'; $)
  $}

  ${
    $d x ph $.
    $( Version of ~ 19.32 with a disjoint variable condition, requiring fewer
       axioms.  (Contributed by BJ, 7-Mar-2020.) $)
    19.32v $p |- ( A. x ( ph \/ ps ) <-> ( ph \/ A. x ps ) ) $=
      ( wn wi wal wo 19.21v df-or albii 3bitr4i ) ADZBEZCFLBCFZEABGZCFANGLBCHOM
      CABIJANIK $.
    $( $j usage '19.32v' avoids 'ax-6' 'ax-7' 'ax-12'; $)
  $}

  ${
    $d x ps $.
    $( Version of ~ 19.31 with a disjoint variable condition, requiring fewer
       axioms.  (Contributed by BJ, 7-Mar-2020.) $)
    19.31v $p |- ( A. x ( ph \/ ps ) <-> ( A. x ph \/ ps ) ) $=
      ( wo wal 19.32v orcom albii 3bitr4i ) BADZCEBACEZDABDZCEKBDBACFLJCABGHKBG
      I $.
    $( $j usage '19.31v' avoids 'ax-6' 'ax-7' 'ax-12'; $)
  $}

  ${
    $d x ps $.
    $( Version of ~ 19.23 with a disjoint variable condition instead of a
       nonfreeness hypothesis.  (Contributed by NM, 28-Jun-1998.)  Reduce
       dependencies on axioms.  (Revised by Wolf Lammen, 11-Jan-2020.)  Remove
       dependency on ~ ax-6 .  (Revised by Rohan Ridenour, 15-Apr-2022.) $)
    19.23v $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( wi wal wex exim ax5e syl6 ax-5 imim2i 19.38 syl impbii ) ABDCEZACFZBDZO
      PBCFBABCGBCHIQPBCEZDOBRPBCJKABCLMN $.
    $( $j usage '19.23v' avoids 'ax-6' 'ax-7' 'ax-12'; $)
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Theorem ~ 19.23v extended to two variables.  (Contributed by NM,
       10-Aug-2004.) $)
    19.23vv $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x E. y ph -> ps ) ) $=
      ( wi wal wex 19.23v albii bitri ) ABEDFZCFADGZBEZCFLCGBEKMCABDHILBCHJ $.
  $}

  ${
    $d ph y $.  $d ps x $.  $d x y $.
    $( Version of ~ pm11.53 with a disjoint variable condition, requiring fewer
       axioms.  (Contributed by BJ, 7-Mar-2020.) $)
    pm11.53v $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) $=
      ( wi wal wex 19.21v albii 19.23v bitri ) ABEDFZCFABDFZEZCFACGMELNCABDHIAM
      CJK $.
  $}

  ${
    $d x ps $.
    $( One direction of ~ 19.36v that can be proven without ~ ax-6 .
       (Contributed by Rohan Ridenour, 16-Apr-2022.)  (Proof shortened by Wolf
       Lammen, 22-Sep-2024.) $)
    19.36imv $p |- ( E. x ( ph -> ps ) -> ( A. x ph -> ps ) ) $=
      ( wal wi wex pm2.27 aleximi ax5e syl6com ) ACDABEZCFBCFBAKBCABGHBCIJ $.
  $}

  ${
    $d x ps $.
    19.36iv.1 $e |- E. x ( ph -> ps ) $.
    $( Inference associated with ~ 19.36v .  Version of ~ 19.36i with a
       disjoint variable condition.  (Contributed by NM, 5-Aug-1993.)  Reduce
       dependencies on axioms.  (Revised by Wolf Lammen, 17-Jan-2020.)  Remove
       dependency on ~ ax-6 .  (Revised by Rohan Ridenour, 15-Apr-2022.) $)
    19.36iv $p |- ( A. x ph -> ps ) $=
      ( wi wex wal 19.36imv ax-mp ) ABECFACGBEDABCHI $.
  $}

  ${
    $d x ph $.
    $( One direction of ~ 19.37v that can be proven without ~ ax-6 .
       (Contributed by Rohan Ridenour, 16-Apr-2022.) $)
    19.37imv $p |- ( E. x ( ph -> ps ) -> ( ph -> E. x ps ) ) $=
      ( wal wi wex ax-5 19.35 biimpi syl5 ) AACDZABECFZBCFZACGLKMEABCHIJ $.
  $}

  ${
    $d x ph $.
    19.37iv.1 $e |- E. x ( ph -> ps ) $.
    $( Inference associated with ~ 19.37v .  (Contributed by NM, 5-Aug-1993.)
       Remove dependency on ~ ax-6 .  (Revised by Rohan Ridenour,
       15-Apr-2022.) $)
    19.37iv $p |- ( ph -> E. x ps ) $=
      ( wi wex 19.37imv ax-mp ) ABECFABCFEDABCGH $.
  $}

  ${
    $d x ps $.
    $( Version of ~ 19.41 with a disjoint variable condition, requiring fewer
       axioms.  (Contributed by NM, 21-Jun-1993.)  Remove dependency on
       ~ ax-6 .  (Revised by Rohan Ridenour, 15-Apr-2022.) $)
    19.41v $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( wa wex 19.40 ax5e anim2i syl pm3.21 eximdv impcom impbii ) ABDZCEZACEZB
      DZOPBCEZDQABCFRBPBCGHIBPOBANCBAJKLM $.
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Version of ~ 19.41 with two quantifiers and a disjoint variable
       condition requiring fewer axioms.  (Contributed by NM, 30-Apr-1995.) $)
    19.41vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x E. y ph /\ ps ) ) $=
      ( wa wex 19.41v exbii bitri ) ABEDFZCFADFZBEZCFKCFBEJLCABDGHKBCGI $.
  $}

  ${
    $d x ps $.  $d y ps $.  $d z ps $.
    $( Version of ~ 19.41 with three quantifiers and a disjoint variable
       condition requiring fewer axioms.  (Contributed by NM, 30-Apr-1995.) $)
    19.41vvv $p |- ( E. x E. y E. z ( ph /\ ps ) <->
                     ( E. x E. y E. z ph /\ ps ) ) $=
      ( wa wex 19.41vv exbii 19.41v bitri ) ABFEGDGZCGAEGDGZBFZCGMCGBFLNCABDEHI
      MBCJK $.
  $}

  ${
    $d w ps $.  $d x ps $.  $d y ps $.  $d z ps $.
    $( Version of ~ 19.41 with four quantifiers and a disjoint variable
       condition requiring fewer axioms.  (Contributed by FL, 14-Jul-2007.) $)
    19.41vvvv $p |- ( E. w E. x E. y E. z ( ph /\ ps ) <->
                     ( E. w E. x E. y E. z ph /\ ps ) ) $=
      ( wa wex 19.41vvv exbii 19.41v bitri ) ABGEHDHCHZFHAEHDHCHZBGZFHNFHBGMOFA
      BCDEIJNBFKL $.
  $}

  ${
    $d x ph $.
    $( Version of ~ 19.42 with a disjoint variable condition requiring fewer
       axioms.  (Contributed by NM, 21-Jun-1993.) $)
    19.42v $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      ( wa wex 19.41v exancom ancom 3bitr4i ) BADCEBCEZADABDCEAJDBACFABCGAJHI
      $.
  $}

  ${
    $d y ph $.
    $( Distribution of existential quantifiers.  See also ~ exdistrv .
       (Contributed by NM, 9-Mar-1995.) $)
    exdistr $p |- ( E. x E. y ( ph /\ ps ) <-> E. x ( ph /\ E. y ps ) ) $=
      ( wa wex 19.42v exbii ) ABEDFABDFECABDGH $.
  $}

  ${
    $d y ph $.  $d x ps $.  $d x y $.
    $( Distribute a pair of existential quantifiers (over disjoint variables)
       over a conjunction.  Combination of ~ 19.41v and ~ 19.42v .  For a
       version with fewer disjoint variable conditions but requiring more
       axioms, see ~ eeanv .  (Contributed by BJ, 30-Sep-2022.) $)
    exdistrv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      ( wa wex exdistr 19.41v bitri ) ABEDFCFABDFZECFACFJEABCDGAJCHI $.
  $}

  ${
    $d w ph $.  $d z ph $.  $d y ps $.  $d x ps $.  $d w y $.  $d y z $.
    $d w x $.  $d x z $.
    $( Distribute two pairs of existential quantifiers (over disjoint
       variables) over a conjunction.  For a version with fewer disjoint
       variable conditions but requiring more axioms, see ~ ee4anv .
       (Contributed by BJ, 5-Jan-2023.) $)
    4exdistrv $p |- ( E. x E. z E. y E. w ( ph /\ ps ) <->
                                          ( E. x E. y ph /\ E. z E. w ps ) ) $=
      ( wa wex exdistrv 2exbii bitri ) ABGFHDHZEHCHADHZBFHZGZEHCHMCHNEHGLOCEABD
      FIJMNCEIK $.
  $}

  ${
    $d x ph $.  $d y ph $.
    $( Version of ~ 19.42 with two quantifiers and a disjoint variable
       condition requiring fewer axioms.  (Contributed by NM, 16-Mar-1995.) $)
    19.42vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( ph /\ E. x E. y ps ) ) $=
      ( wa wex exdistr 19.42v bitri ) ABEDFCFABDFZECFAJCFEABCDGAJCHI $.
  $}

  ${
    $d y ph $.  $d z ph $.
    $( Distribution of existential quantifiers.  (Contributed by NM,
       17-Mar-1995.) $)
    exdistr2 $p |- ( E. x E. y E. z ( ph /\ ps ) <->
                   E. x ( ph /\ E. y E. z ps ) ) $=
      ( wa wex 19.42vv exbii ) ABFEGDGABEGDGFCABDEHI $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.
    $( Version of ~ 19.42 with three quantifiers and a disjoint variable
       condition requiring fewer axioms.  (Contributed by NM, 21-Sep-2011.)
       (Proof shortened by Wolf Lammen, 27-Aug-2023.) $)
    19.42vvv $p |- ( E. x E. y E. z ( ph /\ ps )
                       <-> ( ph /\ E. x E. y E. z ps ) ) $=
      ( wa wex exdistr2 19.42v bitri ) ABFEGDGCGABEGDGZFCGAKCGFABCDEHAKCIJ $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d z ps $.
    $( Distribution of existential quantifiers in a triple conjunction.
       (Contributed by NM, 9-Mar-1995.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)
    3exdistr $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
                E. x ( ph /\ E. y ( ps /\ E. z ch ) ) ) $=
      ( w3a wex wa 3anass 2exbii 19.42vv exdistr anbi2i 3bitri exbii ) ABCGZFHE
      HZABCFHIEHZIZDRABCIZIZFHEHAUAFHEHZITQUBEFABCJKAUAEFLUCSABCEFMNOP $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d w ph $.  $d z ps $.  $d w ps $.  $d w ch $.
    $( Distribution of existential quantifiers in a quadruple conjunction.
       (Contributed by NM, 9-Mar-1995.)  (Proof shortened by Wolf Lammen,
       20-Jan-2018.) $)
    4exdistr $p |- ( E. x E. y E. z E. w ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
                E. x ( ph /\ E. y ( ps /\ E. z ( ch /\ E. w th ) ) ) ) $=
      ( wa wex w3a 19.42v anbi2i df-3an 3bitr4i 3exbii 3exdistr bitri ) ABIZCDI
      ZIHJZGJFJEJABCDHJIZKZGJFJEJABUBGJIFJIEJUAUCEFGSTHJZISUBIUAUCUDUBSCDHLMSTH
      LABUBNOPABUBEFGQR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Equality predicate (continued)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The equality predicate was introduced above in ~ wceq for use by ~ df-tru .
  See the comments in that section.  In this section, we continue with its
  first "real" use.

$)

  $( Extend wff definition to include atomic formulas using the equality
     predicate.

     (Instead of introducing ~ weq as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wceq .  This lets us avoid overloading
     the ` = ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ weq is considered to be a
     primitive syntax, even though here it is artificially "derived" from
     ~ wceq .  Note:  To see the proof steps of this syntax proof, type "MM>
     SHOW PROOF weq / ALL" in the Metamath program.)  (Contributed by NM,
     24-Jan-2006.) $)
  weq $p wff x = y $=
    ( cv wceq ) ACBCD $.

  ${
    speimfw.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, with additional weakening (compared to ~ 19.2 ) to allow
       bundling of ` x ` and ` y ` .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 23-Apr-2017.)  (Proof shortened by Wolf Lammen,
       5-Dec-2017.) $)
    speimfw $p |- ( -. A. x -. x = y -> ( A. x ph -> E. x ps ) ) $=
      ( weq wn wal wex df-ex biimpri com12 aleximi syl5com ) CDFZGCHGZOCIZACHBC
      IQPOCJKAOBCOABELMN $.

    $( Alternate proof of ~ speimfw (longer compressed proof, but fewer
       essential steps).  (Contributed by NM, 23-Apr-2017.)  (Proof shortened
       by Wolf Lammen, 5-Aug-2017.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    speimfwALT $p |- ( -. A. x -. x = y -> ( A. x ph -> E. x ps ) ) $=
      ( weq wex wi wn wal eximi df-ex 19.35 3imtr3i ) CDFZCGABHZCGOICJIACJBCGHO
      PCEKOCLABCMN $.
  $}

  ${
    spimfw.1 $e |- ( -. ps -> A. x -. ps ) $.
    spimfw.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, with additional weakening (compared to ~ sp ) to allow
       bundling of ` x ` and ` y ` .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 23-Apr-2017.)  (Proof shortened by Wolf Lammen,
       7-Aug-2017.) $)
    spimfw $p |- ( -. A. x -. x = y -> ( A. x ph -> ps ) ) $=
      ( weq wn wal wex speimfw df-ex con1i sylbi syl6 ) CDGHCIHACIBCJZBABCDFKPB
      HCIZHBBCLBQEMNO $.
  $}

  ${
    ax12i.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    ax12i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference that has ~ ax-12 (without ` A. y ` ) as its conclusion.  Uses
       only Tarski's FOL axiom schemes.  The hypotheses may be eliminable
       without using ~ ax-12 in special cases.  Proof similar to Lemma 16 of
       [Tarski] p. 70.  (Contributed by NM, 20-May-2008.) $)
    ax12i $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( weq wi wal biimprcd alrimih biimtrdi ) CDGZABMAHZCIEBNCFMABEJKL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-6 (Existence)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Existence.  One of the equality and substitution axioms of
     predicate calculus with equality.  This axiom tells us that at least one
     thing exists.  In this form (not requiring that ` x ` and ` y ` be
     distinct) it was used in an axiom system of Tarski (see Axiom B7' in
     footnote 1 of [KalishMontague] p. 81.)  It is equivalent to axiom scheme
     C10' in [Megill] p. 448 (p. 16 of the preprint); the equivalence is
     established by ~ axc10 and ~ ax6fromc10 .  A more convenient form of this
     axiom is ~ ax6e , which has additional remarks.

     Raph Levien proved the independence of this axiom from the other logical
     axioms on 12-Apr-2005.  See item 16 at
     ~ https://us.metamath.org/award2003.html .

     ~ ax-6 can be proved from the weaker version ~ ax6v requiring that the
     variables be distinct; see Theorem ~ ax6 .

     ~ ax-6 can also be proved from the Axiom of Separation (in the form that
     we use that axiom, where free variables are not universally quantified).
     See Theorem ~ ax6vsep .

     Except by ~ ax6v , this axiom should not be referenced directly.  Instead,
     use Theorem ~ ax6 .  (Contributed by NM, 10-Jan-1993.)
     (New usage is discouraged.) $)
  ax-6 $a |- -. A. x -. x = y $.

  ${
    $d x y $.
    $( Axiom B7 of [Tarski] p. 75, which requires that ` x ` and ` y ` be
       distinct.  This trivial proof is intended merely to weaken Axiom ~ ax-6
       by adding a distinct variable restriction ($d).  From here on, ~ ax-6
       should not be referenced directly by any other proof, so that Theorem
       ~ ax6 will show that we can recover ~ ax-6 from this weaker version if
       it were an axiom (as it is in the case of Tarski).

       Note:  Introducing ` x , y ` as a distinct variable group "out of the
       blue" with no apparent justification has puzzled some people, but it is
       perfectly sound.  All we are doing is adding an additional prerequisite,
       similar to adding an unnecessary logical hypothesis, that results in a
       weakening of the theorem.  This means that any _future_ theorem that
       references ~ ax6v must have a $d specified for the two variables that
       get substituted for ` x ` and ` y ` .  The $d does not propagate
       "backwards", i.e., it does not impose a requirement on ~ ax-6 .

       When possible, use of this theorem rather than ~ ax6 is preferred since
       its derivation is much shorter and requires fewer axioms.  (Contributed
       by NM, 7-Aug-2015.) $)
    ax6v $p |- -. A. x -. x = y $=
      ( ax-6 ) ABC $.
  $}

  ${
    $d x y $.
    $( At least one individual exists.  Weaker version of ~ ax6e .  When
       possible, use of this theorem rather than ~ ax6e is preferred since its
       derivation is much shorter and requires fewer axioms.  (Contributed by
       NM, 3-Aug-2017.) $)
    ax6ev $p |- E. x x = y $=
      ( weq wex wn wal ax6v df-ex mpbir ) ABCZADJEAFEABGJAHI $.
  $}

  ${
    $d x y $.
    spimw.1 $e |- ( -. ps -> A. x -. ps ) $.
    spimw.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization.  Lemma 8 of [KalishMontague] p. 87.  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 19-Apr-2017.)  (Proof shortened
       by Wolf Lammen, 7-Aug-2017.) $)
    spimw $p |- ( A. x ph -> ps ) $=
      ( weq wn wal wi ax6v spimfw ax-mp ) CDGHCIHACIBJCDKABCDEFLM $.
  $}

  ${
    $d x y $.
    spimew.1 $e |- ( ph -> A. x ph ) $.
    spimew.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Existential introduction, using implicit substitution.  Compare Lemma 14
       of [Tarski] p. 70.  (Contributed by NM, 7-Aug-1994.)  (Proof shortened
       by Wolf Lammen, 22-Oct-2023.) $)
    spimew $p |- ( ph -> E. x ps ) $=
      ( weq wn wal wex ax6v speimfw mpsyl ) CDGHCIHAACIBCJCDKEABCDFLM $.
  $}

  ${
    $d x y $.
    speiv.1 $e |- ( x = y -> ( ps -> ph ) ) $.
    speiv.2 $e |- ps $.
    $( Inference from existential specialization.  (Contributed by NM,
       19-Aug-1993.)  Use ~ spimew .  (Revised by Wolf Lammen, 22-Oct-2023.) $)
    speiv $p |- E. x ph $=
      ( wex hbth spimew ax-mp ) BACGFBACDBCFHEIJ $.
  $}

  ${
    $d x y $.
    speivw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    speivw.2 $e |- ps $.
    $( Version of ~ spei with a disjoint variable condition, which does not
       require ~ ax-13 (neither ~ ax-7 nor ~ ax-12 ).  (Contributed by BJ,
       31-May-2019.) $)
    speivw $p |- E. x ph $=
      ( weq biimprd speiv ) ABCDCDGABEHFI $.
  $}

  ${
    $d x y $.
    exgen.1 $e |- ph $.
    $( Rule of existential generalization, similar to universal generalization
       ~ ax-gen , but valid only if an individual exists.  Its proof requires
       ~ ax-6 in our axiomatization but the equality predicate does not occur
       in its statement.  Some fundamental theorems of predicate calculus can
       be proven from ~ ax-gen , ~ ax-4 and this theorem alone, not requiring
       ~ ax-7 or excessive distinct variable conditions.  (Contributed by Wolf
       Lammen, 12-Nov-2017.)  (Proof shortened by Wolf Lammen, 20-Oct-2023.) $)
    exgen $p |- E. x ph $=
      ( vy weq idd speiv ) AABDBDEAFCG $.
  $}

  $( There exists a variable such that ` T. ` holds; that is, there exists a
     variable.  This corresponds under the standard translation to one of the
     formulations of the modal axiom (D), the other being ~ 19.2 .
     (Contributed by Anthony Hart, 13-Sep-2011.)  (Proof shortened by BJ,
     12-May-2019.) $)
  extru $p |- E. x T. $=
    ( wtru tru exgen ) BACD $.

  $( Theorem 19.2 of [Margaris] p. 89.  This corresponds to the axiom (D) of
     modal logic (the other standard formulation being ~ extru ).  Note:  This
     proof is very different from Margaris' because we only have Tarski's FOL
     axiom schemes available at this point.  See the later ~ 19.2g for a more
     conventional proof of a more general result, which uses additional axioms.
     The reverse implication is the defining property of effective nonfreeness
     (see ~ df-nf ).  (Contributed by NM, 2-Aug-2017.)  Remove dependency on
     ~ ax-7 .  (Revised by Wolf Lammen, 4-Dec-2017.) $)
  19.2 $p |- ( A. x ph -> E. x ph ) $=
    ( wi id exgen 19.35i ) AABAACBADEF $.

  ${
    19.2d.1 $e |- ( ph -> A. x ps ) $.
    $( Deduction associated with ~ 19.2 .  (Contributed by BJ, 12-May-2019.) $)
    19.2d $p |- ( ph -> E. x ps ) $=
      ( wal wex 19.2 syl ) ABCEBCFDBCGH $.
  $}

  ${
    19.8w.1 $e |- ( ph -> A. x ph ) $.
    $( Weak version of ~ 19.8a and instance of ~ 19.2d .  (Contributed by NM,
       1-Aug-2017.)  (Proof shortened by Wolf Lammen, 4-Dec-2017.) $)
    19.8w $p |- ( ph -> E. x ph ) $=
      ( 19.2d ) AABCD $.
  $}

  ${
    $d x y $.  $d y ph $.
    spnfw.1 $e |- ( -. ph -> A. x -. ph ) $.
    $( Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 1-Aug-2017.)  (Proof shortened by Wolf Lammen,
       13-Aug-2017.) $)
    spnfw $p |- ( A. x ph -> ph ) $=
      ( vy weq idd spimw ) AABDCBDEAFG $.
  $}

  ${
    spfalw.1 $e |- -. ph $.
    $( Version of ~ sp when ` ph ` is false.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 23-Apr-2017.)  (Proof shortened by Wolf
       Lammen, 25-Dec-2017.) $)
    spfalw $p |- ( A. x ph -> ph ) $=
      ( wn hbth spnfw ) ABADBCEF $.
  $}

  ${
    $d x ph $.
    $( Version of ~ sp when ` x ` does not occur in ` ph ` .  Converse of
       ~ ax-5 .  Uses only Tarski's FOL axiom schemes.  (Contributed by NM,
       10-Apr-2017.)  (Proof shortened by Wolf Lammen, 4-Dec-2017.)  Shorten
       ~ 19.3v .  (Revised by Wolf Lammen, 20-Oct-2023.) $)
    spvw $p |- ( A. x ph -> ph ) $=
      ( wn ax-5 spnfw ) ABACBDE $.
    $( $j usage 'spvw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)

    $( Version of ~ 19.3 with a disjoint variable condition, requiring fewer
       axioms.  Any formula can be universally quantified using a variable
       which it does not contain.  See also ~ 19.9v .  (Contributed by Anthony
       Hart, 13-Sep-2011.)  Remove dependency on ~ ax-7 .  (Revised by Wolf
       Lammen, 4-Dec-2017.)  (Proof shortened by Wolf Lammen, 20-Oct-2023.) $)
    19.3v $p |- ( A. x ph <-> ph ) $=
      ( wal spvw ax-5 impbii ) ABCAABDABEF $.
    $( $j usage '19.3v' avoids 'ax-12'; $)

    $( Version of ~ 19.8a with a disjoint variable condition, requiring fewer
       axioms.  Converse of ~ ax5e .  (Contributed by BJ, 12-Mar-2020.) $)
    19.8v $p |- ( ph -> E. x ph ) $=
      ( ax-5 19.8w ) ABABCD $.
    $( $j usage '19.8v' avoids 'ax-12'; $)

    $( Version of ~ 19.9 with a disjoint variable condition, requiring fewer
       axioms.  Any formula can be existentially quantified using a variable
       which it does not contain.  See also ~ 19.3v .  (Contributed by NM,
       28-May-1995.)  Remove dependency on ~ ax-7 .  (Revised by Wolf Lammen,
       4-Dec-2017.) $)
    19.9v $p |- ( E. x ph <-> ph ) $=
      ( wex ax5e 19.8v impbii ) ABCAABDABEF $.
    $( $j usage '19.9v' avoids 'ax-12'; $)
  $}

  ${
    $d x y $.  $d x ph $.
    spimevw.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Existential introduction, using implicit substitution.  This is to
       ~ spimew what ~ spimvw is to ~ spimw .  Version of ~ spimev and
       ~ spimefv with an additional disjoint variable condition, using only
       Tarski's FOL axiom schemes.  (Contributed by NM, 10-Jan-1993.)  (Revised
       by BJ, 17-Mar-2020.) $)
    spimevw $p |- ( ph -> E. x ps ) $=
      ( ax-5 spimew ) ABCDACFEG $.
  $}

  ${
    $d x y $.  $d x ps $.
    spimvw.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( A weak form of specialization.  Lemma 8 of [KalishMontague] p. 87.  Uses
       only Tarski's FOL axiom schemes.  For stronger forms using more axioms,
       see ~ spimv and ~ spimfv .  (Contributed by NM, 9-Apr-2017.) $)
    spimvw $p |- ( A. x ph -> ps ) $=
      ( wn ax-5 spimw ) ABCDBFCGEH $.
  $}

  ${
    $d x y ps $.
    spsv.1 $e |- ( ph -> ps ) $.
    $( Generalization of antecedent.  A trivial weak version of ~ sps avoiding
       ~ ax-12 .  (Contributed by SN, 13-Nov-2025.)  (Proof shortened by WL,
       19-Nov-2025.) $)
    spsv $p |- ( A. x ph -> ps ) $=
      ( vy wi weq a1i spimvw ) ABCEABFCEGDHI $.
    $( $j usage 'spsv' avoids 'ax-12'; $)
  $}

  ${
    $d x y $.  $d x ps $.
    spvv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Specialization, using implicit substitution.  Version of ~ spv with a
       disjoint variable condition, which does not require ~ ax-7 , ~ ax-12 ,
       ~ ax-13 .  (Contributed by NM, 30-Aug-1993.)  (Revised by BJ,
       31-May-2019.) $)
    spvv $p |- ( A. x ph -> ps ) $=
      ( weq biimpd spimvw ) ABCDCDFABEGH $.
  $}

  ${
    $d x y $.  $d x ps $.
    chvarvv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chvarvv.2 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  Version of
       ~ chvarv with a disjoint variable condition, which does not require
       ~ ax-13 .  (Contributed by NM, 20-Apr-1994.)  (Revised by BJ,
       31-May-2019.) $)
    chvarvv $p |- ps $=
      ( spvv mpg ) ABCABCDEGFH $.
  $}

  $( Theorem 19.39 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
  19.39 $p |- ( ( E. x ph -> E. x ps ) -> E. x ( ph -> ps ) ) $=
    ( wex wi wal 19.2 imim1i 19.35 sylibr ) ACDZBCDZEACFZLEABECDMKLACGHABCIJ $.

  $( Theorem 19.24 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
  19.24 $p |- ( ( A. x ph -> A. x ps ) -> E. x ( ph -> ps ) ) $=
    ( wal wi wex 19.2 imim2i 19.35 sylibr ) ACDZBCDZEKBCFZEABECFLMKBCGHABCIJ $.

  $( Theorem 19.34 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
  19.34 $p |- ( ( A. x ph \/ E. x ps ) -> E. x ( ph \/ ps ) ) $=
    ( wal wex wo 19.2 orim1i 19.43 sylibr ) ACDZBCEZFACEZLFABFCEKMLACGHABCIJ $.

  ${
    $d x ps $.
    $( Version of ~ 19.36 with a disjoint variable condition instead of a
       nonfreeness hypothesis.  (Contributed by NM, 18-Aug-1993.)  Reduce
       dependencies on axioms.  (Revised by Wolf Lammen, 17-Jan-2020.) $)
    19.36v $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $=
      ( wi wex wal 19.35 19.9v imbi2i bitri ) ABDCEACFZBCEZDKBDABCGLBKBCHIJ $.
  $}

  ${
    $d x ps $.  $d y ph $.  $d x y $.
    $( Version of ~ 19.12vv with a disjoint variable condition, requiring fewer
       axioms.  See also ~ 19.12 .  (Contributed by BJ, 18-Mar-2020.) $)
    19.12vvv $p |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) ) $=
      ( wi wal wex 19.21v exbii 19.36v albii bitr2i 3bitri ) ABEZDFZCGABDFZEZCG
      ACFZPEZNCGZDFZOQCABDHIAPCJUARBEZDFSTUBDABCJKRBDHLM $.
  $}

  ${
    $d x ps $.
    $( Version of ~ 19.27 with a disjoint variable condition, requiring fewer
       axioms.  (Contributed by NM, 3-Jun-2004.) $)
    19.27v $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      ( wa wal 19.26 19.3v anbi2i bitri ) ABDCEACEZBCEZDJBDABCFKBJBCGHI $.
  $}

  ${
    $d x ph $.
    $( Version of ~ 19.28 with a disjoint variable condition, requiring fewer
       axioms.  (Contributed by NM, 25-Mar-2004.) $)
    19.28v $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      ( wa wal 19.26 19.3v bianbi ) ABDCEACEBCEAABCFACGH $.
  $}

  ${
    $d x ph $.
    $( Version of ~ 19.37 with a disjoint variable condition, requiring fewer
       axioms.  (Contributed by NM, 21-Jun-1993.) $)
    19.37v $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $=
      ( wi wex wal 19.35 19.3v imbi1i bitri ) ABDCEACFZBCEZDALDABCGKALACHIJ $.
  $}

  ${
    $d x ps $.
    $( Version of ~ 19.44 with a disjoint variable condition, requiring fewer
       axioms.  (Contributed by NM, 12-Mar-1993.) $)
    19.44v $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ ps ) ) $=
      ( wo wex 19.43 19.9v orbi2i bitri ) ABDCEACEZBCEZDJBDABCFKBJBCGHI $.
  $}

  ${
    $d x ph $.
    $( Version of ~ 19.45 with a disjoint variable condition, requiring fewer
       axioms.  (Contributed by NM, 12-Mar-1993.) $)
    19.45v $p |- ( E. x ( ph \/ ps ) <-> ( ph \/ E. x ps ) ) $=
      ( wo wex 19.43 19.9v orbi1i bitri ) ABDCEACEZBCEZDAKDABCFJAKACGHI $.
  $}

  ${
    $d x y $.
    $( Version of ~ equs4 with a disjoint variable condition, which requires
       fewer axioms.  (Contributed by NM, 10-May-1993.)  (Revised by BJ,
       31-May-2019.) $)
    equs4v $p |- ( A. x ( x = y -> ph ) -> E. x ( x = y /\ ph ) ) $=
      ( weq wi wal wex wa ax6ev exintr mpi ) BCDZAEBFLBGLAHBGBCILABJK $.
    $( $j usage 'equs4v' avoids 'ax-5' 'ax-7' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.
    $( Version of ~ equs4v with its consequence simplified by ~ exsimpr .
       (Contributed by BJ, 9-Nov-2021.) $)
    alequexv $p |- ( A. x ( x = y -> ph ) -> E. x ph ) $=
      ( weq wi wal wex ax6ev exim mpi ) BCDZAEBFKBGABGBCHKABIJ $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( One direction of the equivalence in ~ exsb is based on fewer axioms.
       (Contributed by Wolf Lammen, 2-Mar-2023.) $)
    exsbim $p |- ( E. y A. x ( x = y -> ph ) -> E. x ph ) $=
      ( weq wi wal wex alequexv exlimiv ) BCDAEBFABGCABCHI $.
  $}

  ${
    $d x y $.  $d x ph $.
    $( If a formula does not contain a variable ` x ` , then it is equivalent
       to the corresponding prototype of substitution with a fresh variable
       (see ~ sb6 ).  (Contributed by BJ, 23-Jul-2023.) $)
    equsv $p |- ( A. x ( x = y -> ph ) <-> ph ) $=
      ( weq wi wal wex 19.23v ax6ev a1bi bitr4i ) BCDZAEBFLBGZAEALABHMABCIJK $.
  $}

  ${
    $d x y $.  $d x ps $.
    equsalvw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Version of ~ equsalv with a disjoint variable condition, and of ~ equsal
       with two disjoint variable conditions, which requires fewer axioms.  See
       also the dual form ~ equsexvw .  (Contributed by BJ, 31-May-2019.) $)
    equsalvw $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal pm5.74i albii equsv bitri ) CDFZAGZCHMBGZCHBNOCMABEIJBCDKL
      $.
    $( $j usage 'equsalvw' avoids 'ax-7' 'ax-12' 'ax-13'; $)

    $( Version of ~ equsexv with a disjoint variable condition, and of ~ equsex
       with two disjoint variable conditions, which requires fewer axioms.  See
       also the dual form ~ equsalvw .  (Contributed by BJ, 31-May-2019.)
       (Proof shortened by Wolf Lammen, 23-Oct-2023.) $)
    equsexvw $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( weq wa wex wn wi wal alinexa notbid equsalvw bitr3i con4bii ) CDFZAGCHZ
      BRIQAIZJCKBIZQACLSTCDQABEMNOP $.
    $( $j usage 'equsexvw' avoids 'ax-7' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.
    cbvaliw.1 $e |- ( A. x ph -> A. y A. x ph ) $.
    cbvaliw.2 $e |- ( -. ps -> A. x -. ps ) $.
    cbvaliw.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.  Part of
       Lemma 7 of [KalishMontague] p. 86.  (Contributed by NM, 19-Apr-2017.) $)
    cbvaliw $p |- ( A. x ph -> A. y ps ) $=
      ( wal spimw alrimih ) ACHBDEABCDFGIJ $.
    $( $j usage 'cbvaliw' avoids 'ax-5' 'ax-7' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    cbvalivw.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.  Part of
       Lemma 7 of [KalishMontague] p. 86.  (Contributed by NM, 9-Apr-2017.) $)
    cbvalivw $p |- ( A. x ph -> A. y ps ) $=
      ( wal spimvw alrimiv ) ACFBDABCDEGH $.
    $( $j usage 'cbvalivw' avoids 'ax-7' 'ax-12' 'ax-13'; $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-7 (Equality)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Equality.  One of the equality and substitution axioms of
     predicate calculus with equality.  It states that equality is a
     right-Euclidean binary relation (this is similar, but not identical, to
     being transitive, which is proved as ~ equtr ).  This axiom scheme is a
     sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom C7 of [Monk2] p. 105 and Axiom Scheme C8' in [Megill] p. 448 (p. 16
     of the preprint).

     The equality symbol was invented in 1557 by Robert Recorde.  He chose a
     pair of parallel lines of the same length because "noe .2. thynges, can be
     moare equalle".

     We prove in ~ ax7 that this axiom can be recovered from its weakened
     version ~ ax7v where ` x ` and ` y ` are assumed to be disjoint variables.
     In particular, the only theorem referencing ~ ax-7 should be ~ ax7v .  See
     the comment of ~ ax7v for more details on these matters.  (Contributed by
     NM, 10-Jan-1993.)  (Revised by BJ, 7-Dec-2020.)  Use ~ ax7 instead.
     (New usage is discouraged.) $)
  ax-7 $a |- ( x = y -> ( x = z -> y = z ) ) $.

  ${
    $d x y $.
    $( Weakened version of ~ ax-7 , with a disjoint variable condition on
       ` x , y ` .  This should be the only proof referencing ~ ax-7 , and it
       should be referenced only by its two weakened versions ~ ax7v1 and
       ~ ax7v2 , from which ~ ax-7 is then rederived as ~ ax7 , which shows
       that either ~ ax7v or the conjunction of ~ ax7v1 and ~ ax7v2 is
       sufficient.

       In ~ ax7v , it is still allowed to substitute the same variable for
       ` x ` and ` z ` , or the same variable for ` y ` and ` z ` .  Therefore,
       ~ ax7v "bundles" (a term coined by Raph Levien) its "principal instance"
       ` ( x = y -> ( x = z -> y = z ) ) ` with ` x , y , z ` distinct, and its
       "degenerate instances" ` ( x = y -> ( x = x -> y = x ) ) ` and
       ` ( x = y -> ( x = y -> y = y ) ) ` with ` x , y ` distinct.  These
       degenerate instances are for instance used in the proofs of ~ equcomiv
       and ~ equid respectively.  (Contributed by BJ, 7-Dec-2020.)  Use ~ ax7
       instead.  (New usage is discouraged.) $)
    ax7v $p |- ( x = y -> ( x = z -> y = z ) ) $=
      ( ax-7 ) ABCD $.
  $}

  ${
    $d x y $.  $d x z $.
    $( First of two weakened versions of ~ ax7v , with an extra disjoint
       variable condition on ` x , z ` , see comments there.  (Contributed by
       BJ, 7-Dec-2020.) $)
    ax7v1 $p |- ( x = y -> ( x = z -> y = z ) ) $=
      ( ax7v ) ABCD $.
  $}

  ${
    $d x y $.  $d y z $.
    $( Second of two weakened versions of ~ ax7v , with an extra disjoint
       variable condition on ` y , z ` , see comments there.  (Contributed by
       BJ, 7-Dec-2020.) $)
    ax7v2 $p |- ( x = y -> ( x = z -> y = z ) ) $=
      ( ax7v ) ABCD $.
  $}

  ${
    $d x y $.
    $( Identity law for equality.  Lemma 2 of [KalishMontague] p. 85.  See also
       Lemma 6 of [Tarski] p. 68.  (Contributed by NM, 1-Apr-2005.)  (Revised
       by NM, 9-Apr-2017.)  (Proof shortened by Wolf Lammen, 22-Aug-2020.) $)
    equid $p |- x = x $=
      ( vy weq ax7v1 pm2.43i ax6ev exlimiiv ) BACZAACZBHIBAADEBAFG $.
  $}

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (Contributed by NM,
     13-Jan-2011.)  (Revised by NM, 21-Aug-2017.) $)
  nfequid $p |- F/ y x = x $=
    ( weq equid nfth ) AACBADE $.

  ${
    $d x y $.
    $( Weaker form of ~ equcomi with a disjoint variable condition on
       ` x , y ` .  This is an intermediate step and ~ equcomi is fully
       recovered later.  (Contributed by BJ, 7-Dec-2020.) $)
    equcomiv $p |- ( x = y -> y = x ) $=
      ( weq equid ax7v2 mpi ) ABCAACBACADABAEF $.
  $}

  ${
    $d x y $.
    $( A commuted form of ~ ax6ev .  (Contributed by BJ, 7-Dec-2020.) $)
    ax6evr $p |- E. x y = x $=
      ( weq ax6ev equcomiv eximii ) ABCBACAABDABEF $.
  $}

  ${
    $d t x $.  $d t y $.  $d t z $.
    $( Proof of ~ ax-7 from ~ ax7v1 and ~ ax7v2 (and earlier axioms), proving
       sufficiency of the conjunction of the latter two weakened versions of
       ~ ax7v , which is itself a weakened version of ~ ax-7 .

       Note that the weakened version of ~ ax-7 obtained by adding a disjoint
       variable condition on ` x , z ` (resp. on ` y , z ` ) does not permit,
       together with the other axioms, to prove reflexivity (resp. symmetry).
       (Contributed by BJ, 7-Dec-2020.) $)
    ax7 $p |- ( x = y -> ( x = z -> y = z ) ) $=
      ( vt weq wa wi ax7v2 ax7v1 imp a1i syl2and ax6evr exlimiiv ex ) ABEZACEZB
      CEZADEZPQFRGDSPDBEZQDCEZRADBHADCHTUAFRGSTUARDBCIJKLDAMNO $.
  $}

  $( Commutative law for equality.  Equality is a symmetric relation.  Lemma 3
     of [KalishMontague] p. 85.  See also Lemma 7 of [Tarski] p. 69.
     (Contributed by NM, 10-Jan-1993.)  (Revised by NM, 9-Apr-2017.) $)
  equcomi $p |- ( x = y -> y = x ) $=
    ( weq equid ax7 mpi ) ABCAACBACADABAEF $.

  $( Commutative law for equality.  Equality is a symmetric relation.
     (Contributed by NM, 20-Aug-1993.) $)
  equcom $p |- ( x = y <-> y = x ) $=
    ( weq equcomi impbii ) ABCBACABDBADE $.

  ${
    equcomd.1 $e |- ( ph -> x = y ) $.
    $( Deduction form of ~ equcom , symmetry of equality.  For the versions for
       classes, see ~ eqcom and ~ eqcomd .  (Contributed by BJ, 6-Oct-2019.) $)
    equcomd $p |- ( ph -> y = x ) $=
      ( weq equcom sylib ) ABCECBEDBCFG $.
  $}

  ${
    equcoms.1 $e |- ( x = y -> ph ) $.
    $( An inference commuting equality in antecedent.  Used to eliminate the
       need for a syllogism.  (Contributed by NM, 10-Jan-1993.) $)
    equcoms $p |- ( y = x -> ph ) $=
      ( weq equcomi syl ) CBEBCEACBFDG $.
  $}

  $( A transitive law for equality.  (Contributed by NM, 23-Aug-1993.) $)
  equtr $p |- ( x = y -> ( y = z -> x = z ) ) $=
    ( weq wi ax7 equcoms ) BCDACDEBABACFG $.

  $( A transitive law for equality.  Lemma L17 in [Megill] p. 446 (p. 14 of the
     preprint).  (Contributed by NM, 23-Aug-1993.) $)
  equtrr $p |- ( x = y -> ( z = x -> z = y ) ) $=
    ( weq equtr com12 ) CADABDCBDCABEF $.

  $( Commuted version of ~ equeucl (equality is left-Euclidean).  (Contributed
     by BJ, 12-Apr-2021.) $)
  equeuclr $p |- ( x = z -> ( y = z -> y = x ) ) $=
    ( weq wi equtrr equcoms ) BCDBADECACABFG $.

  $( Equality is a left-Euclidean binary relation.  (Right-Euclideanness is
     stated in ~ ax-7 .)  Curried (exported) form of ~ equtr2 .  (Contributed
     by BJ, 11-Apr-2021.) $)
  equeucl $p |- ( x = z -> ( y = z -> x = y ) ) $=
    ( weq equeuclr com12 ) BCDACDABDBACEF $.

  $( An equivalence law for equality.  (Contributed by NM, 1-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 10-Dec-2017.) $)
  equequ1 $p |- ( x = y -> ( x = z <-> y = z ) ) $=
    ( weq ax7 equtr impbid ) ABDACDBCDABCEABCFG $.

  $( An equivalence law for equality.  (Contributed by NM, 21-Jun-1993.)
     (Proof shortened by Wolf Lammen, 4-Aug-2017.)  (Proof shortened by BJ,
     12-Apr-2021.) $)
  equequ2 $p |- ( x = y -> ( z = x <-> z = y ) ) $=
    ( weq equtrr equeuclr impbid ) ABDCADCBDABCEACBFG $.

  $( Equality is a left-Euclidean binary relation.  Uncurried (imported) form
     of ~ equeucl .  (Contributed by NM, 12-Aug-1993.)  (Proof shortened by
     Andrew Salmon, 25-May-2011.)  (Proof shortened by BJ, 11-Apr-2021.) $)
  equtr2 $p |- ( ( x = z /\ y = z ) -> x = y ) $=
    ( weq equeucl imp ) ACDBCDABDABCEF $.

  $( One of the two equality axioms of standard predicate calculus, called
     reflexivity of equality.  (The other one is ~ stdpc7 .)  Axiom 6 of
     [Mendelson] p. 95.  Mendelson doesn't say why he prepended the redundant
     quantifier, but it was probably to be compatible with free logic (which is
     valid in the empty domain).  (Contributed by NM, 16-Feb-2005.) $)
  stdpc6 $p |- A. x x = x $=
    ( weq equid ax-gen ) AABAACD $.

  ${
    $d x z $.  $d y z $.
    $( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109.
       (Contributed by NM, 9-Jan-1993.)  Remove dependencies on ~ ax-10 ,
       ~ ax-13 .  (Revised by Wolf Lammen, 10-Jun-2019.)  Move the quantified
       variable ( ` z ` ) to the left of the equality signs.  (Revised by Wolf
       Lammen, 11-Apr-2021.)  (Proof shortened by Wolf Lammen, 12-Jul-2022.) $)
    equvinv $p |- ( x = y <-> E. z ( z = x /\ z = y ) ) $=
      ( weq wa wex equequ1 equsexvw bicomi ) CADCBDZECFABDZJKCACABGHI $.
    $( $j usage 'equvinv' avoids 'ax-10' 'ax-12' 'ax-13'; $)

    $( A modified version of the forward implication of ~ equvinv adapted to
       common usage.  (Contributed by Wolf Lammen, 8-Sep-2018.) $)
    equvinva $p |- ( x = y -> E. z ( x = z /\ y = z ) ) $=
      ( weq wex wa ax6evr equtr ancrd eximdv mpi ) ABDZBCDZCEACDZMFZCECBGLMOCLM
      NABCHIJK $.
    $( $j usage 'equvinva' avoids 'ax-10' 'ax-12' 'ax-13'; $)

    $( A biconditional form of ~ equvel with disjoint variable conditions and
       proved from Tarski's FOL axiom schemes.  (Contributed by Andrew Salmon,
       2-Jun-2011.)  Reduce axiom usage.  (Revised by Wolf Lammen,
       10-Apr-2021.)  (Proof shortened by Wolf Lammen, 12-Jul-2022.) $)
    equvelv $p |- ( A. z ( z = x -> z = y ) <-> x = y ) $=
      ( weq equequ1 equsalvw ) CBDABDCACABEF $.
    $( $j usage 'equvelv' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  $( An equivalence between two ways of expressing ~ ax-13 .  See the comment
     for ~ ax-13 .  (Contributed by NM, 2-May-2017.)  (Proof shortened by Wolf
     Lammen, 26-Feb-2018.)  (Revised by BJ, 15-Sep-2020.) $)
  ax13b $p |- ( ( -. x = y -> ( y = z -> ph ) )
                       <-> ( -. x = y -> ( -. x = z -> ( y = z -> ph ) ) ) ) $=
    ( weq wn wi ax-1 equeuclr con3rr3 imim1d pm2.43 syl6 impbid2 pm5.74i ) BCEZ
    FZCDEZAGZBDEZFZSGZQSUBSUAHQUBRSGSQRUASRTPCBDIJKRALMNO $.
  $( $j usage 'ax13b' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)

  ${
    $d x y $.
    spfw.1 $e |- ( -. ps -> A. x -. ps ) $.
    spfw.2 $e |- ( A. x ph -> A. y A. x ph ) $.
    spfw.3 $e |- ( -. ph -> A. y -. ph ) $.
    spfw.4 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.  Lemma 9
       of [KalishMontague] p. 87.  This may be the best we can do with minimal
       distinct variable conditions.  (Contributed by NM, 19-Apr-2017.)  (Proof
       shortened by Wolf Lammen, 10-Oct-2021.) $)
    spfw $p |- ( A. x ph -> ph ) $=
      ( wal weq biimpd cbvaliw wi biimprd equcoms spimw syl ) ACIBDIAABCDFECDJZ
      ABHKLBADCGBAMCDRABHNOPQ $.
    $( $j usage 'spfw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    spw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of the specialization scheme ~ sp .  Lemma 9 of
       [KalishMontague] p. 87.  While it appears that ~ sp in its general form
       does not follow from Tarski's FOL axiom schemes, from this theorem we
       can prove any _instance_ of ~ sp having mutually distinct setvar
       variables and no wff metavariables (see ~ ax12wdemo for an example of
       the procedure to eliminate the hypothesis).  Other approximations of
       ~ sp are ~ spfw (minimal distinct variable requirements), ~ spnfw (when
       ` x ` is not free in ` -. ph ` ), ~ spvw (when ` x ` does not appear in
       ` ph ` ), ~ sptruw (when ` ph ` is true), ~ spfalw (when ` ph ` is
       false), and ~ spvv (where ` ph ` is changed into ` ps ` ).  (Contributed
       by NM, 9-Apr-2017.)  (Proof shortened by Wolf Lammen, 27-Feb-2018.) $)
    spw $p |- ( A. x ph -> ph ) $=
      ( wn ax-5 wal spfw ) ABCDBFCGACHDGAFDGEI $.
    $( $j usage 'spw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.
    cbvalw.1 $e |- ( A. x ph -> A. y A. x ph ) $.
    cbvalw.2 $e |- ( -. ps -> A. x -. ps ) $.
    cbvalw.3 $e |- ( A. y ps -> A. x A. y ps ) $.
    cbvalw.4 $e |- ( -. ph -> A. y -. ph ) $.
    cbvalw.5 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)
    cbvalw $p |- ( A. x ph <-> A. y ps ) $=
      ( wal weq biimpd cbvaliw wi biimprd equcoms impbii ) ACJBDJABCDEFCDKZABIL
      MBADCGHBANCDRABIOPMQ $.
    $( $j usage 'cbvalw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    cbvalvw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.  See
       ~ cbvalv for a version with fewer disjoint variable conditions but
       requiring more axioms.  (Contributed by NM, 9-Apr-2017.)  (Proof
       shortened by Wolf Lammen, 28-Feb-2018.) $)
    cbvalvw $p |- ( A. x ph <-> A. y ps ) $=
      ( wal ax-5 wn cbvalw ) ABCDACFDGBHCGBDFCGAHDGEI $.
    $( $j usage 'cbvalvw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)

    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.  See
       ~ cbvexv for a version with fewer disjoint variable conditions but
       requiring more axioms.  (Contributed by NM, 19-Apr-2017.) $)
    cbvexvw $p |- ( E. x ph <-> E. y ps ) $=
      ( wn wal wex weq notbid cbvalvw notbii df-ex 3bitr4i ) AFZCGZFBFZDGZFACHB
      DHPROQCDCDIABEJKLACMBDMN $.
    $( $j usage 'cbvexvw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d ps y $.  $d ch x $.  $d ph x y $.
    cbvaldvaw.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Rule used to change the bound variable in a universal quantifier with
       implicit substitution.  Deduction form.  Version of ~ cbvaldva with a
       disjoint variable condition, requiring fewer axioms.  (Contributed by
       David Moews, 1-May-2017.)  Avoid ~ ax-13 .  (Revised by GG,
       10-Jan-2024.)  Reduce axiom usage, along an idea of GG. (Revised by Wolf
       Lammen, 10-Feb-2024.) $)
    cbvaldvaw $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal wi weq wb ancoms pm5.74da cbvalvw 19.21v 3bitr3i pm5.74ri ) ABDGZCE
      GZABHZDGACHZEGAQHARHSTDEDEIZABCAUABCJFKLMABDNACENOP $.

    $( Rule used to change the bound variable in an existential quantifier with
       implicit substitution.  Deduction form.  Version of ~ cbvexdva with a
       disjoint variable condition, requiring fewer axioms.  (Contributed by
       David Moews, 1-May-2017.)  Avoid ~ ax-13 .  (Revised by GG,
       10-Jan-2024.)  Reduce axiom usage.  (Revised by Wolf Lammen,
       10-Feb-2024.) $)
    cbvexdvaw $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( wex wn wal weq wa notbid cbvaldvaw alnex 3bitr3g con4bid ) ABDGZCEGZABH
      ZDICHZEIQHRHASTDEADEJKBCFLMBDNCENOP $.
  $}

  ${
    $d w z ph $.  $d x y ps $.  $d w x y z $.
    cbval2vw.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbval2vv with more disjoint variable conditions, which
       requires fewer axioms .  (Contributed by NM, 4-Feb-2005.)  Avoid
       ~ ax-13 .  (Revised by GG, 10-Jan-2024.) $)
    cbval2vw $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( wal weq cbvaldvaw cbvalvw ) ADHBFHCECEIABDFGJK $.

    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbvex2vv with more disjoint variable conditions, which
       requires fewer axioms .  (Contributed by NM, 26-Jul-1995.)  Avoid
       ~ ax-13 .  (Revised by GG, 10-Jan-2024.) $)
    cbvex2vw $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( wex weq cbvexdvaw cbvexvw ) ADHBFHCECEIABDFGJK $.
  $}

  ${
    $v f $.
    $v g $.
    $( Define temporary individual variables. $)
    cbvex4vw.vf $f setvar f $.
    cbvex4vw.vg $f setvar g $.
    $d w z ch $.  $d u v ph $.  $d x y ps $.  $d f g ps $.  $d f g w z $.
    $d u v w x y z $.
    cbvex4vw.1 $e |- ( ( x = v /\ y = u ) -> ( ph <-> ps ) ) $.
    cbvex4vw.2 $e |- ( ( z = f /\ w = g ) -> ( ps <-> ch ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbvex4v with more disjoint variable conditions, which
       requires fewer axioms.  (Contributed by NM, 26-Jul-1995.)  Avoid
       ~ ax-13 .  (Revised by GG, 10-Jan-2024.) $)
    cbvex4vw $p |- ( E. x E. y E. z E. w ph <-> E. v E. u E. f E. g ch ) $=
      ( wex weq wa 2exbidv cbvex2vw 2exbii bitri ) AGNFNZENDNBGNFNZINHNCKNJNZIN
      HNUAUBDEHIDHOEIOPABFGLQRUBUCHIBCFGJKMRST $.
  $}

  ${
    $d y z $.  $d x y $.  $d z ph $.  $d y ps $.
    alcomimw.1 $e |- ( y = z -> ( ph <-> ps ) ) $.
    $( Weak version of ~ ax-11 .  See ~ alcomw for the biconditional form.
       Uses only Tarski's FOL axiom schemes.  (Contributed by NM, 10-Apr-2017.)
       (Proof shortened by Wolf Lammen, 28-Dec-2023.) $)
    alcomimw $p |- ( A. x A. y ph -> A. y A. x ph ) $=
      ( wal cbvalvw biimpi alimi ax-5 wi weq biimprd equcoms spimvw 2alimi 3syl
      ) ADGZCGBEGZCGZUADGACGDGSTCSTABDEFHIJUADKTADCBAEDBALDEDEMABFNOPQR $.
    $( $j usage 'alcomimw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d ph z $.  $d ps x $.  $d x y $.  $d x z $.
    excomimw.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    $( Weak version of ~ excomim .  Uses only Tarski's FOL axiom schemes.
       (Contributed by BTernaryTau, 23-Jun-2025.) $)
    excomimw $p |- ( E. x E. y ph -> E. y E. x ph )
        $=
      ( wn wal wex weq notbid alcomimw con3i 2exnaln 3imtr4i ) AGZDHCHZGPCHDHZG
      ADICIACIDIRQPBGDCECEJABFKLMACDNADCNO $.
    $( $j usage 'excomimw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d ph z $.  $d ph w $.  $d ps x $.  $d ch y $.  $d x y $.  $d y z $.
    $d w x $.
    alcomw.1 $e |- ( x = w -> ( ph <-> ps ) ) $.
    alcomw.2 $e |- ( y = z -> ( ph <-> ch ) ) $.
    $( Weak version of ~ alcom and biconditional form of ~ alcomimw .  Uses
       only Tarski's FOL axiom schemes.  (Contributed by BTernaryTau,
       28-Dec-2024.) $)
    alcomw $p |- ( A. x A. y ph <-> A. y A. x ph ) $=
      ( wal alcomimw impbii ) AEJDJADJEJACDEFIKABEDGHKL $.
    $( $j usage 'alcomw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d ph z $.  $d ph w $.  $d ps x $.  $d ch y $.  $d x y $.  $d y z $.
    $d w x $.
    excomw.1 $e |- ( x = w -> ( ph <-> ps ) ) $.
    excomw.2 $e |- ( y = z -> ( ph <-> ch ) ) $.
    $( Weak version of ~ excom and biconditional form of ~ excomimw .  Uses
       only Tarski's FOL axiom schemes.  (Contributed by TM, 24-Jan-2026.) $)
    excomw $p |- ( E. x E. y ph <-> E. y E. x ph ) $=
      ( wex excomimw impbii ) AEJDJADJEJABDEGHKACEDFIKL $.
    $( $j usage 'excomw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d x y $.
    hbn1fw.1 $e |- ( A. x ph -> A. y A. x ph ) $.
    hbn1fw.2 $e |- ( -. ps -> A. x -. ps ) $.
    hbn1fw.3 $e |- ( A. y ps -> A. x A. y ps ) $.
    hbn1fw.4 $e |- ( -. ph -> A. y -. ph ) $.
    hbn1fw.5 $e |- ( -. A. y ps -> A. x -. A. y ps ) $.
    hbn1fw.6 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ ax-10 from which we can prove any ~ ax-10 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 19-Apr-2017.)  (Proof shortened by Wolf
       Lammen, 28-Feb-2018.) $)
    hbn1fw $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
      ( wal wn cbvalw notbii hbxfrbi ) ACKZLBDKZLCPQABCDEFGHJMNIO $.
    $( $j usage 'hbn1fw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d y ph $.  $d x ps $.  $d x y $.
    hbn1w.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ hbn1 .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)
    hbn1w $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
      ( wal ax-5 wn hbn1fw ) ABCDACFDGBHCGBDFZCGAHDGJHCGEI $.
    $( $j usage 'hbn1w' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)

    $( Weak version of ~ hba1 .  See comments for ~ ax10w .  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 9-Apr-2017.)  (Proof shortened
       by Wolf Lammen, 10-Oct-2021.) $)
    hba1w $p |- ( A. x ph -> A. x A. x ph ) $=
      ( wal wn wb weq cbvalvw notbii a1i spw con2i hbn1w con1i alimi 3syl ) ACF
      ZSGZCFZGZUBCFSCFUASTBDFZGZCDTUDHCDISUCABCDEJKLZMNTUDCDUEOUBSCSUAABCDEOPQR
      $.
    $( $j usage 'hba1w' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)

    $( Weak version of ~ hbe1 .  See comments for ~ ax10w .  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 19-Apr-2017.) $)
    hbe1w $p |- ( E. x ph -> A. x E. x ph ) $=
      ( wex wn wal df-ex weq notbid hbn1w hbxfrbi ) ACFAGZCHGCACINBGCDCDJABEKLM
      $.
    $( $j usage 'hbe1w' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d x z $.  $d x y $.  $d z ph $.  $d x ps $.
    hbalw.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    hbalw.2 $e |- ( ph -> A. x ph ) $.
    $( Weak version of ~ hbal .  Uses only Tarski's FOL axiom schemes.  Unlike
       ~ hbal , this theorem requires that ` x ` and ` y ` be distinct, i.e.,
       not be bundled.  (Contributed by NM, 19-Apr-2017.) $)
    hbalw $p |- ( A. y ph -> A. x A. y ph ) $=
      ( wal alimi alcomimw syl ) ADHZACHZDHLCHAMDGIABDCEFJK $.
    $( $j usage 'hbalw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d x y $.  $d ps x $.  $d ph y $.
    19.8aw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( If a formula is true, then it is true for at least one instance.  This
       is to ~ 19.8a what ~ spw is to ~ sp .  (Contributed by SN,
       26-Sep-2024.) $)
    19.8aw $p |- ( ph -> E. x ph ) $=
      ( wex wn wal alnex weq notbid spw sylbir con4i ) ACFZAOGAGZCHPACIPBGCDCDJ
      ABEKLMN $.
  $}

  ${
    $d x y $.  $d ps x $.  $d ph y $.
    exexw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Existential quantification over a given variable is idempotent.  Weak
       version of ~ bj-exexbiex , requiring fewer axioms.  (Contributed by GG,
       4-Nov-2024.) $)
    exexw $p |- ( E. x ph <-> E. x E. x ph ) $=
      ( wal wex weq notbid hba1w spw alimi impbii notbii df-ex 2exnaln 3bitr4i
      wn ) ARZCFZRTCFZRACGZUBCGTUATUASBRZCDCDHABEIZJTSCSUCCDUDKLMNACOACCPQ $.
    $( $j usage 'exexw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y z $.
    $( A special instance of ~ sp applied to an equality with a disjoint
       variable condition.  Unlike the more general ~ sp , we can prove this
       without ~ ax-12 .  Instance of ~ aeveq .

       The antecedent ` A. x x = y ` with distinct ` x ` and ` y ` is a
       characteristic of a degenerate universe, in which just one object
       exists.  Actually more than one object may still exist, but if so, we
       give up on equality as a discriminating term.

       Separating this degenerate case from a richer universe, where inequality
       is possible, is a common proof idea.  The name of this theorem follows a
       convention, where the condition ` A. x x = y ` is denoted by 'aev', a
       shorthand for 'all equal, with a distinct variable condition'.
       (Contributed by Wolf Lammen, 14-Mar-2021.) $)
    spaev $p |- ( A. x x = y -> x = y ) $=
      ( vz weq equequ1 spw ) ABDCBDACACBEF $.
    $( $j usage 'spaev' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d x y t $.  $d y z t $.
    $( Change bound variable in an equality with a disjoint variable condition.
       Instance of ~ aev .  (Contributed by NM, 22-Jul-2015.)  (Revised by BJ,
       18-Jun-2019.) $)
    cbvaev $p |- ( A. x x = y -> A. z z = y ) $=
      ( vt weq wal ax7 cbvalivw syl ) ABEZAFDBEZDFCBEZCFJKADADBGHKLDCDCBGHI $.
    $( $j usage 'cbvaev' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d x y z $.
    $( Lemma for ~ aevlem .  Instance of ~ aev .  (Contributed by NM,
       8-Jul-2016.)  (Proof shortened by Wolf Lammen, 17-Feb-2018.)  Remove
       dependency on ~ ax-12 .  (Revised by Wolf Lammen, 14-Mar-2021.)  Extract
       from proof of a former lemma for ~ axc11n and add DV condition to reduce
       axiom usage.  (Revised by BJ, 29-Mar-2021.)  (Proof shortened by Wolf
       Lammen, 30-Mar-2021.) $)
    aevlem0 $p |- ( A. x x = y -> A. z z = x ) $=
      ( weq wal spaev alrimiv cbvaev equeuclr al2imi sylc ) ABDZAEZLCECBDZCECAD
      ZCEMLCABFGABCHLNOCACBIJK $.
  $}

  ${
    $d x y u $.  $d z t u $.
    $( Lemma for ~ aev and ~ axc16g .  Change free and bound variables.
       Instance of ~ aev .  (Contributed by NM, 22-Jul-2015.)  (Proof shortened
       by Wolf Lammen, 17-Feb-2018.)  Remove dependency on ~ ax-13 , along an
       idea of BJ. (Revised by Wolf Lammen, 30-Nov-2019.)  Reduce axiom usage.
       (Revised by BJ, 29-Mar-2021.) $)
    aevlem $p |- ( A. x x = y -> A. z z = t ) $=
      ( vu weq wal cbvaev aevlem0 4syl ) ABFAGEBFEGAEFAGDEFDGCDFCGABEHEBAIAEDHD
      ECIJ $.
  $}

  ${
    $d x y $.  $d u z $.  $d u t $.
    $( The antecedent ` A. x x = y ` with a disjoint variable condition
       (typical of a one-object universe) forces equality of everything.
       (Contributed by Wolf Lammen, 19-Mar-2021.) $)
    aeveq $p |- ( A. x x = y -> z = t ) $=
      ( vu weq wal wex aevlem ax6ev ax7 aleximi mpi ax5e 3syl ) ABFAGECFZEGZCDF
      ZEHZRABECIQEDFZEHSEDJPTREECDKLMRENO $.
    $( $j usage 'aeveq' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d x y $.  $d v w z $.
    $( A "distinctor elimination" lemma with no disjoint variable conditions on
       variables in the consequent.  (Contributed by NM, 8-Nov-2006.)  Remove
       dependency on ~ ax-11 .  (Revised by Wolf Lammen, 7-Sep-2018.)  Remove
       dependency on ~ ax-13 , inspired by an idea of BJ. (Revised by Wolf
       Lammen, 30-Nov-2019.)  Remove dependency on ~ ax-12 .  (Revised by Wolf
       Lammen, 19-Mar-2021.) $)
    aev $p |- ( A. x x = y -> A. z t = u ) $=
      ( vv vw weq wal aevlem aeveq alrimiv syl ) ABHAIFGHFIZEDHZCIABFGJNOCFGEDK
      LM $.
    $( $j usage 'aev' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $v s $.  $d w s z $.
    $( Define temporary individual variable s. $)
    v.vs $f setvar s $.
    $d x y $.  $d w s $.
    $( A version of ~ aev with two universal quantifiers in the consequent.
       One can prove similar statements with arbitrary numbers of universal
       quantifiers in the consequent (the series begins with ~ aeveq , ~ aev ,
       ~ aev2 ).

       Using ~ aev and ~ alrimiv , one can actually prove (with no more axioms)
       any scheme of the form ` ( A. x x = y -> ` PHI) , DV ` ( x , y ) ` where
       PHI involves only setvar variables and the connectors ` -> ` , ` <-> ` ,
       ` /\ ` , ` \/ ` , ` T. ` , ` = ` , ` A. ` , ` E. ` , ` E* ` , ` E! ` ,
       ` F/ ` .  An example is given by ~ aevdemo .  This list cannot be
       extended to ` -. ` or ` F. ` since the scheme ` A. x x = y ` is
       consistent with ~ ax-mp , ~ ax-gen , ~ ax-1 -- ~ ax-13 (as the
       one-element universe shows), so for instance ` ( A. x x = y -> F. ) , `
       DV ` ( x , y ) ` is not provable from these axioms alone (indeed, ~ dtru
       uses non-logical axioms as well).  (Contributed by BJ, 23-Mar-2021.) $)
    aev2 $p |- ( A. x x = y -> A. z A. t u = v ) $=
      ( vw v.vs weq wal aev alrimiv syl ) ABIAJGHIGJZEDIFJZCJABGHGKNOCGHFDEKLM
      $.
    $( $j usage 'aev2' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.
    $( All variables are effectively bound in an identical variable specifier.
       Version of ~ hbae with a disjoint variable condition, requiring fewer
       axioms.  Instance of ~ aev2 .  (Contributed by NM, 13-May-1993.)  Reduce
       axiom usage.  (Revised by Wolf Lammen, 22-Mar-2021.) $)
    hbaev $p |- ( A. x x = y -> A. z A. x x = y ) $=
      ( aev2 ) ABCBAAD $.
    $( $j usage 'hbaev' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d u v $.
    $( If some set variables can assume different values, then any two distinct
       set variables cannot always be the same.  (Contributed by Wolf Lammen,
       10-Aug-2019.) $)
    naev $p |- ( -. A. x x = y -> -. A. u u = v ) $=
      ( weq wal aev con3i ) DCEDFABEAFDCABAGH $.
    $( $j usage 'naev' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d t u $.  $d v w z $.
    $( Generalization of ~ hbnaev .  (Contributed by Wolf Lammen,
       9-Apr-2021.) $)
    naev2 $p |- ( -. A. x x = y -> A. z -. A. t t = u ) $=
      ( vv vw weq wal wn naev ax-5 alimi 3syl ) ABHAIJFGHFIJZOCIEDHEIJZCIABGFKO
      CLOPCFGDEKMN $.
    $( $j usage 'naev2' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  ${
    $d x y $.
    $( Any variable is free in ` -. A. x x = y ` , if ` x ` and ` y ` are
       distinct.  This condition is dropped in ~ hbnae , at the expense of more
       axiom dependencies.  Instance of ~ naev2 .  (Contributed by NM,
       13-May-1993.)  (Revised by Wolf Lammen, 9-Apr-2021.) $)
    hbnaev $p |- ( -. A. x x = y -> A. z -. A. x x = y ) $=
      ( naev2 ) ABCBAD $.
    $( $j usage 'hbnaev' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Define proper substitution
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    justify-df.1 $e |- ph $.
    $( Metamath handles substitution uniformly.  Any expression may replace a
       variable provided that their types are compatible and that no
       substituting expression contains a set variable prohibited by a distinct
       variable condition.

       The axioms are formulated so that every such substitution is valid when
       the side conditions are satisfied.  Consequently, every theorem derived
       from the axioms inherits the same substitution property.  This agrees
       with standard mathematical practice, where substitution is unrestricted
       apart from type and freshness requirements.

       Definitions introduce abbreviations for expressions represented by their
       definiens, usually the right-hand side of a defining biconditional.
       When a definition contains dummy variables, however, the definiens is
       not uniquely determined by the definiendum, since the names of fresh
       bound variables do not appear in the definiendum.  Definitions of this
       kind are meaningful only if the particular names chosen for dummy
       variables are irrelevant.

       In ordinary logic and mathematics, renaming fresh bound variables
       (alpha-renaming) is regarded as insignificant.  Metamath's substitution
       mechanism reflects this principle, and therefore definitions must also
       respect it.  Early versions of this database relied on this convention
       implicitly.  Beginning in 2023, definitions involving dummy variables
       were accompanied by justification theorems (for example, ~ rename-sb )
       showing that alpha-renaming the definiens yields an equivalent
       expression.  Consequently, different choices of dummy variable names
       cannot produce equivalences that are not already derivable within the
       formal system.

       Metamath records not only proofs but also the list of axioms on which
       they depend.  Since definitions are intended merely as abbreviations,
       their use should not affect these dependency lists.  Unfortunately, the
       simple form of definition used before 2026 did not preserve this
       invariance.  Two instances of a definition differing only in the names
       of dummy variables could be used to reprove the corresponding
       justification theorem with unusually low axiom usage, unattainable by
       proofs using axioms alone.  Thus the recorded dependencies could depend
       on whether the definition was used or expanded away.

       Beginning in February 2026, definitions involving dummy variables were
       therefore modified to incorporate alpha-renaming explicitly.  In the
       intermediate scheme, the corresponding justification theorem was added
       as a hypothesis of the definition, ensuring that every use of the
       definition inherited the axioms needed to establish the renaming
       property.  This eliminated artificial reductions in dependency lists.

       Using the alpha-renaming property as an external hypothesis is, however,
       not ideal.  A better approach is to encode the property directly in the
       definiens itself.  This preserves the invariance of axiom dependencies
       while allowing reductions that are impossible with the hypothesis-based
       form.

       Formal justifications for this improved definition scheme are given in
       ~ just1-df , ~ just2-df , and ~ just3-df .  An implementation is
       provided by definition ~ df-sb and the theorems that follow, where the
       underlying techniques may be studied in greater detail.  (Contributed by
       Wolf Lammen, 12-Jun-2026.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    justify-df $p |- ph $=
      (  ) B $.
  $}

  ${
    just1-df.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( First justification theorem for definitions whose definiens is a
       conjunction, as in ~ df-sb .  Here ` ph ` denotes the definiendum, while
       ` ps ` and ` ch ` represent the two components of the definiens.  The
       theorem shows that the definiendum implies either component separately.
       (Contributed by Wolf Lammen, 6-Jun-2026.)
       (New usage is discouraged.) $)
    just1-df $p |- ( ph -> ps ) $=
      ( simplbi ) ABCDE $.
  $}

  ${
    just2-df.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Second justification theorem for definitions whose definiens is a
       conjunction, as in ~ df-sb .  If ` ph ` is equivalent to
       ` ( ps /\ ch ) ` , then it implies ` ( ps <-> ch ) ` .  In the case of
       ~ df-sb , this expresses the invariance of the definition under
       alpha-renaming of the bound variable.  (Contributed by Wolf Lammen,
       6-Jun-2026.) $)
    just2-df $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wb wa abab bitri simprbi ) ABBCEZABCFBJFDBCGHI $.
  $}

  ${
    just3-df.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    just3-df.2 $e |- ( ps <-> ch ) $.
    $( Third justification theorem for definitions whose definiens is a
       conjunction, as in ~ df-sb .  In addition to the defining equivalence,
       the second hypothesis requires the conjuncts of the definiens to be
       equivalent.

       When the conjuncts are quantified and differ only by a bound-variable
       renaming, this equivalence is usually obtained from an implicit
       substitution between the underlying expressions.  In some cases,
       however, it can be proved more directly and with fewer axioms.

       Under these assumptions, either conjunct implies the definiendum.
       Together with ~ just1-df , the definiendum is therefore equivalent to
       either conjunct.  (Contributed by Wolf Lammen, 6-Jun-2026.) $)
    just3-df $p |- ( ps -> ph ) $=
      ( wb wa jctr abab bitri sylibr ) BBBCFZGZABLEHABCGMDBCIJK $.
  $}

  ${
    $d x y z $.  $d t y z $.  $d ph y z $.
    $( The equivalence needed for ~ df-sb in ~ just3-df .  It is proved from
       Tarski's FOL axiom schemes.  (Contributed by BJ, 22-Jan-2023.) $)
    rename-sb $p |- ( A. y ( y = t -> A. x ( x = y -> ph ) ) <->
                   A. z ( z = t -> A. x ( x = z -> ph ) ) ) $=
      ( weq wi wal equequ1 equequ2 imbi1d albidv imbi12d cbvalvw ) CEFZBCFZAGZB
      HZGDEFZBDFZAGZBHZGCDCDFZOSRUBCDEIUCQUABUCPTACDBJKLMN $.
  $}

  $c [ $.  $( Left bracket $)
  $c / $.  $( Slash. $)
  $c ] $.  $( Right bracket $)

  $( Extend wff definition to include proper substitution.  Read:  "the wff
     that results when ` y ` is properly substituted for ` x ` in wff ` ph ` ".
     (Contributed by NM, 24-Jan-2006.) $)
  wsb $a wff [ y / x ] ph $.

  $( Indicate that the variable "y" is free in wsb even though it could
     potentially bind occurrences in "ph". $)
  $( $j free_var 'wsb' with 'y'; $)

  ${
    $d x y z $.  $d t y z $.  $d ph y z $.
    $( Define proper substitution.  We write ` [ t / x ] ph ` for "the wff
       obtained by properly substituting ` t ` for ` x ` in the wff ` ph ` ".
       Thus, ` t ` properly replaces ` x ` .  For example, ` [ t / x ] z e. x `
       is ` z e. t ` (when ` x ` and ` z ` are distinct), as shown in ~ elsb2 .

       In practice, the definiens reduces
       to " ` A. y ( y = t -> A. x ( x = y -> ph ) ) ` " (see ~ just3-df ).
       Here it is followed by the same expression with a fresh dummy variable
       ` z ` , making explicit the independence of the dummy variable's name
       (see ~ just2-df ).  This is a necessity of Metamath supporting axiom
       dependency lists.  See ~ justify-df for more information about this
       technique.

       The added conjunct will make some proofs appear duplicated.
       Alternately, one may first prove as a lemma the same theorem under a
       disjoint variable condition on the substituted and the substituting
       variables, then obtain the original theorem by applying that lemma
       twice.

       Our notation, without the alpha-renamed repetition, was introduced in
       Haskell B. Curry's _Foundations of Mathematical Logic_ (1977), p. 316
       and is frequently used in textbooks of lambda calculus and combinatory
       logic.  This notation improves the common but ambiguous
       notation, " ` ph ( t ) ` is the wff obtained by properly substituting
       ` t ` for ` x ` in ` ph ( x ) ` ".  For example, if the original
       ` ph ( x ) ` is ` x = t ` , then ` ph ( t ) ` is ` t = t ` , from which
       we obtain that ` ph ( x ) ` is ` x = x ` .  So what exactly does
       ` ph ( x ) ` mean?  Curry's notation avoids this problem.

       A closely related notation, ` ( y | x ) ph ` , was introduced in
       Bourbaki's Set Theory (Chapter 1, Description of Formal Mathematic,
       1953).

       Most textbooks define proper substitution recursively by considering
       various cases involving free and bound variables.  Instead, we use a
       single formula that is exactly equivalent and serves as a direct
       definition.  We later prove that this definition has the expected
       properties of proper substitution; see ~ sbequ , ~ sbcom2 , and
       ~ sbid2v .

       This definition remains valid when ` x ` and ` t ` are replaced with the
       same variable, as shown by ~ sbid .  This is achieved by applying
       Tarski's definition ~ sb6 twice, which is valid for disjoint variables,
       and introducing a dummy variable ` y ` that isolates ` x ` from ` t ` ,
       as in ~ dfsb7 relative to ~ sb5 .  We can also achieve this by having
       ` x ` free in the first conjunct and bound in the second, as the
       alternate definition ~ dfsb1 shows.  Another version that mixes free and
       bound variables is ~ dfsb3 .  When ` x ` and ` t ` are distinct, proper
       substitution can be expressed more simply using ~ sb5 and ~ sb6 .

       Note that each variable in the definiens is either entirely bound
       ( ` x , y ` ) or entirely free ( ` t ` ).  The definiens also uses only
       primitive symbols.

       Prefer the more general form ~ dfsb when axiom usage is unimportant.  It
       provides a simpler right hand side together with a proof of its
       alpha-renaming.  (Contributed by NM, 10-May-1993.)  Revised from the
       original definition ~ dfsb1 .  (Revised by BJ, 22-Dec-2020.)  Support
       alpha-renaming.  (Revised by Wolf Lammen, 4-Jun-2026.) $)
    df-sb $a |- ( [ t / x ] ph <-> ( A. y ( y = t -> A. x ( x = y -> ph ) )
                               /\ A. z ( z = t -> A. x ( x = z -> ph ) ) ) ) $.
  $}

  ${
    $d x y z $.  $d t y z $.  $d ph y z $.
    $( A simple consequence of ~ df-sb .  (Contributed by Wolf Lammen,
       4-Jun-2026.) $)
    dfsbimp $p |- ( [ t / x ] ph -> A. y ( y = t -> A. x ( x = y -> ph ) ) ) $=
      ( vz wsb weq wi wal df-sb simplbi ) ABDFCDGBCGAHBIHCIEDGBEGAHBIHEIABCEDJK
      $.

    $( Simplify definition ~ df-sb by proving the renaming independency.
       (Contributed by Wolf Lammen, 5-Feb-2026.) ~ df-sb changed.  (Revised by
       Wolf Lammen, 4-Jun-2026.) $)
    dfsb $p |- ( [ t / x ] ph <-> A. y ( y = t -> A. x ( x = y -> ph ) ) ) $=
      ( vz wsb weq wi wal dfsbimp df-sb rename-sb just3-df impbii ) ABDFZCDGBCG
      AHBIHCIZABCDJOPEDGBEGAHBIHEIABCEDKABCEDLMN $.
  $}

  ${
    sbtlem.1 $e |- ph $.
    $( In the case of ~ sbt , ~ rename-sb is derivable from propositional
       axioms and ~ ax-gen alone.  The essential proof step is presented in
       this lemma.  (Contributed by Wolf Lammen, 4-Feb-2026.) $)
    sbtlem $p |- A. y ( y = t -> A. x ( x = y -> ph ) ) $=
      ( weq wi wal a1i ax-gen ) CDFZBCFZAGZBHZGCNKMBALEIJIJ $.

    $d x y z $.  $d t y z $.  $d ph y z $.
    $( A substitution into a theorem yields a theorem.  See ~ sbtALT for a
       shorter proof requiring more axioms.  See ~ chvar and ~ chvarv for
       versions using implicit substitution.  (Contributed by NM, 21-Jan-2004.)
       (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof shortened by
       Wolf Lammen, 20-Jul-2018.)  Revise ~ df-sb .  (Revised by Steven Nguyen,
       6-Jul-2023.)  Revise ~ df-sb again.  (Revised by Wolf Lammen,
       4-Jun-2026.) $)
    sbt $p |- [ t / x ] ph $=
      ( vy vz wsb weq wi wal wa sbtlem pm3.2i df-sb mpbir ) ABCGECHBEHAIBJIEJZF
      CHBFHAIBJIFJZKPQABECDLABFCDLMABEFCNO $.
  $}

  $( The result of substituting in the truth constant "true" is true.
     (Contributed by BJ, 2-Sep-2023.) $)
  sbtru $p |- [ y / x ] T. $=
    ( wtru tru sbt ) CABDE $.

  ${
    $d y x $.  $d y t $.  $d y ph $.
    $( In the case of ~ stdpc4 , ~ rename-sb is derivable from fewer axioms
       than ~ dfsb .  The essential proof step is presented in this lemma.
       Based on a proof of BJ, 22-Dec-2020.  (Contributed by Wolf Lammen,
       4-Jun-2026.) $)
    stdpc4lem $p |- ( A. x ph -> A. y ( y = t -> A. x ( x = y -> ph ) ) ) $=
      ( wal weq wi ala1 a1d alrimiv ) ABEZCDFZBCFZAGBEZGCKNLAMBHIJ $.

    $d y x z $.  $d t z $.  $d z ph $.
    $( The specialization axiom of standard predicate calculus.  It states that
       if a statement ` ph ` holds for all ` x ` , then it also holds for the
       specific case of ` t ` (properly) substituted for ` x ` .  Translated to
       traditional notation, it can be read:  " ` A. x ph ( x ) -> ph ( t ) ` ,
       provided that ` t ` is free for ` x ` in ` ph ( x ) ` ".  Axiom 4 of
       [Mendelson] p. 69.  See also ~ spsbc and ~ rspsbc .  (Contributed by NM,
       14-May-1993.)  Revise ~ df-sb .  (Revised by BJ, 22-Dec-2020.)  Revise
       df-sb again.  (Revised by Wolf Lammen, 4-Jun-2026.) $)
    stdpc4 $p |- ( A. x ph -> [ t / x ] ph ) $=
      ( vy vz wal weq wi wsb stdpc4lem df-sb sylanbrc ) ABFDCGBDGAHBFHDFECGBEGA
      HBFHEFABCIABDCJABECJABDECKL $.
  $}

  ${
    $d y x $.  $d y t $.  $d y ph $.
    $( Alternate proof of ~ stdpc4 , shorter but using additional axioms.
       (Contributed by WL, 5-Jun-2026.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    stdpc4ALT $p |- ( A. x ph -> [ t / x ] ph ) $=
      ( vy wal weq wi wsb ala1 a1d alrimiv dfsb sylibr ) ABEZDCFZBDFZAGBEZGZDEA
      BCHNRDNQOAPBIJKABDCLM $.
  $}

  ${
    sbtALT.1 $e |- ph $.
    $( Alternate proof of ~ sbt , shorter but using additional axioms.
       (Contributed by NM, 21-Jan-2004.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    sbtALT $p |- [ y / x ] ph $=
      ( wsb stdpc4 mpg ) AABCEBABCFDG $.
  $}

  $( A double specialization using explicit substitution.  This is Theorem
     PM*11.1 in [WhiteheadRussell] p. 159.  See ~ stdpc4 for the analogous
     single specialization.  See ~ 2sp for another double specialization.
     (Contributed by Andrew Salmon, 24-May-2011.) $)
  2stdpc4 $p |- ( A. x A. y ph -> [ z / x ] [ w / y ] ph ) $=
    ( wal wsb stdpc4 alimi syl ) ACFZBFACEGZBFLBDGKLBACEHILBDHJ $.

  ${
    $d y t $.  $d x y $.  $d ph y $.  $d ps y $.
    $( Lemma for ~ sbi1 .  The core of the proof was extracted from a proof of
       SN. (Contributed by Wolf Lammen, 5-Jun-2026.) $)
    sbi1lem $p |- ( ( [ t / x ] ( ph -> ps ) /\ [ t / x ] ph )
                          -> A. y ( y = t -> A. x ( x = y -> ps ) ) ) $=
      ( wi wsb weq wal dfsbimp ax-2 al2imi imim3i syl2im imp ) ABFZCEGZACEGZDEH
      ZCDHZBFZCIZFZDIZQSTPFZCIZFZDIRSTAFZCIZFZDIUDPCDEJACDEJUGUJUCDUFUIUBSUEUHU
      ACTABKLMLNO $.
  $}

  ${
    $d u y z $.  $d u x z $.  $d ph u z $.  $d ps u z $.
    $( Distribute substitution over implication.  (Contributed by NM,
       14-May-1993.)  Remove dependencies on axioms.  (Revised by Steven
       Nguyen, 24-Jul-2023.)  Definition ~ df-sb changed.  (Revised by Wolf
       Lammen, 5-Jun-2026.) $)
    sbi1 $p |- ( [ y / x ] ( ph -> ps ) ->
                                          ( [ y / x ] ph -> [ y / x ] ps ) ) $=
      ( vu vz wi wsb wa weq wal sbi1lem df-sb sylanbrc ex ) ABGCDHZACDHZBCDHZPQ
      IEDJCEJBGCKGEKFDJCFJBGCKGFKRABCEDLABCFDLBCEFDMNO $.

    $( Alternate proof of ~ sbt , shorter but using additional axioms.
       (Contributed by NM, 14-May-1993.)  Remove dependencies on axioms.
       (Revised by Steven Nguyen, 24-Jul-2023.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    sbi1ALT $p |- ( [ y / x ] ( ph -> ps ) ->
                                          ( [ y / x ] ph -> [ y / x ] ps ) ) $=
      ( vz wi wsb weq wal dfsb ax-2 al2imi imim3i 3imtr4g sylbi ) ABFZCDGEDHZCE
      HZPFZCIZFZEIZACDGZBCDGZFPCEDJUBQRAFZCIZFZEIQRBFZCIZFZEIUCUDUAUGUJETUFUIQS
      UEUHCRABKLMLACEDJBCEDJNO $.
  $}

  $( Distribute substitution over implication.  Closed form of ~ sbimi .
     Specialization of implication.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.)  Revise ~ df-sb .  (Revised by
     BJ, 22-Dec-2020.)  (Proof shortened by Steven Nguyen, 24-Jul-2023.) $)
  spsbim $p |- ( A. x ( ph -> ps ) -> ( [ t / x ] ph -> [ t / x ] ps ) ) $=
    ( wi wal wsb stdpc4 sbi1 syl ) ABEZCFKCDGACDGBCDGEKCDHABCDIJ $.

  $( Biconditional property for substitution.  Closed form of ~ sbbii .
     Specialization of biconditional.  (Contributed by NM, 2-Jun-1993.)  Revise
     ~ df-sb .  (Revised by BJ, 22-Dec-2020.) $)
  spsbbi $p |- ( A. x ( ph <-> ps ) -> ( [ t / x ] ph <-> [ t / x ] ps ) ) $=
    ( wb wal wsb wi biimp alimi spsbim syl biimpr impbid ) ABEZCFZACDGZBCDGZPAB
    HZCFQRHOSCABIJABCDKLPBAHZCFRQHOTCABMJBACDKLN $.

  ${
    sbimi.1 $e |- ( ph -> ps ) $.
    $( Distribute substitution over implication.  (Contributed by NM,
       25-Jun-1998.)  Revise ~ df-sb .  (Revised by BJ, 22-Dec-2020.)  (Proof
       shortened by Steven Nguyen, 24-Jul-2023.) $)
    sbimi $p |- ( [ t / x ] ph -> [ t / x ] ps ) $=
      ( wi wsb sbt sbi1 ax-mp ) ABFZCDGACDGBCDGFKCDEHABCDIJ $.
  $}

  ${
    sb2imi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Distribute substitution over implication.  Compare ~ al2imi .
       (Contributed by Steven Nguyen, 13-Aug-2023.) $)
    sb2imi $p |- ( [ t / x ] ph -> ( [ t / x ] ps -> [ t / x ] ch ) ) $=
      ( wsb wi sbimi sbi1 syl ) ADEGBCHZDEGBDEGCDEGHALDEFIBCDEJK $.
  $}

  ${
    sbbii.1 $e |- ( ph <-> ps ) $.
    $( Infer substitution into both sides of a logical equivalence.
       (Contributed by NM, 14-May-1993.) $)
    sbbii $p |- ( [ t / x ] ph <-> [ t / x ] ps ) $=
      ( wsb biimpi sbimi biimpri impbii ) ACDFBCDFABCDABEGHBACDABEIHJ $.

    $( Infer double substitution into both sides of a logical equivalence.
       (Contributed by AV, 30-Jul-2023.) $)
    2sbbii $p |- ( [ t / x ] [ u / y ] ph <-> [ t / x ] [ u / y ] ps ) $=
      ( wsb sbbii ) ADEHBDEHCFABDEGII $.
  $}

  ${
    $d x ph $.
    sbimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction substituting both sides of an implication, with ` ph ` and
       ` x ` disjoint.  See also ~ sbimd .  (Contributed by Wolf Lammen,
       6-May-2023.)  Revise ~ df-sb .  (Revised by Steven Nguyen,
       6-Jul-2023.) $)
    sbimdv $p |- ( ph -> ( [ t / x ] ps -> [ t / x ] ch ) ) $=
      ( wi wal wsb alrimiv spsbim syl ) ABCGZDHBDEICDEIGAMDFJBCDEKL $.
  $}

  ${
    $d x ph $.
    sbbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction substituting both sides of a biconditional, with ` ph ` and
       ` x ` disjoint.  See also ~ sbbid .  (Contributed by Wolf Lammen,
       6-May-2023.)  (Proof shortened by Steven Nguyen, 6-Jul-2023.) $)
    sbbidv $p |- ( ph -> ( [ t / x ] ps <-> [ t / x ] ch ) ) $=
      ( wb wal wsb alrimiv spsbbi syl ) ABCGZDHBDEICDEIGAMDFJBCDEKL $.
  $}

  $( Conjunction inside and outside of a substitution are equivalent.  Compare
     ~ 19.26 .  (Contributed by NM, 14-May-1993.)  (Proof shortened by Steven
     Nguyen, 13-Aug-2023.) $)
  sban $p |- ( [ y / x ] ( ph /\ ps ) <-> ( [ y / x ] ph /\ [ y / x ] ps ) ) $=
    ( wa wsb simpl sbimi simpr jca pm3.2 sb2imi imp impbii ) ABEZCDFZACDFZBCDFZ
    EPQROACDABGHOBCDABIHJQRPABOCDABKLMN $.

  $( Threefold conjunction inside and outside of a substitution are equivalent.
     (Contributed by NM, 14-Dec-2006.) $)
  sb3an $p |- ( [ y / x ] ( ph /\ ps /\ ch ) <->
              ( [ y / x ] ph /\ [ y / x ] ps /\ [ y / x ] ch ) ) $=
    ( wa wsb w3a sban anbi1i df-3an sbbii bitri 3bitr4i ) ABFZDEGZCDEGZFZADEGZB
    DEGZFZQFABCHZDEGZSTQHPUAQABDEIJUCOCFZDEGRUBUDDEABCKLOCDEIMSTQKN $.

  ${
    $d y x $.  $d y t $.  $d y ph $.
    $( Existential generalization: if a proposition is true for a specific
       instance, then there exists an instance where it is true.  (Contributed
       by NM, 29-Jun-1993.)  (Proof shortened by Wolf Lammen, 3-May-2018.)
       Revise ~ df-sb .  (Revised by BJ, 22-Dec-2020.)  (Proof shortened by
       Steven Nguyen, 11-Jul-2023.)  Revise ~ df-sb .  (Revised by Wolf Lammen,
       4-Jun-2026.) $)
    spsbe $p |- ( [ t / x ] ph -> E. x ph ) $=
      ( vy wsb weq wi wal wex dfsbimp alequexv exsbim 3syl ) ABCEDCFBDFAGBHZGDH
      NDIABIABDCJNDCKABDLM $.
  $}

  ${
    $d u x $.  $d u y $.  $d u z $.  $d u ph $.
    $( Equality property for substitution, from Tarski's system.  Used in proof
       of Theorem 9.7 in [Megill] p. 449 (p. 16 of the preprint).  (Contributed
       by NM, 14-May-1993.)  Revise ~ df-sb .  (Revised by BJ, 30-Dec-2020.) $)
    sbequ $p |- ( x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
      ( vu weq wi wal wsb equequ2 imbi1d albidv dfsb 3bitr4g ) BCFZEBFZDEFAGDHZ
      GZEHECFZQGZEHADBIADCIORTEOPSQBCEJKLADEBMADECMN $.
  $}

  $( An equality theorem for substitution.  (Contributed by NM, 14-May-1993.)
     (Proof shortened by Wolf Lammen, 15-Sep-2018.)  (Proof shortened by Steven
     Nguyen, 7-Jul-2023.) $)
  sbequi $p |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) ) $=
    ( weq wsb sbequ biimpd ) BCEADBFADCFABCDGH $.

  ${
    $d y x t $.  $d y ph $.
    $( Alternate definition of substitution when variables are disjoint.
       Compare Theorem 6.2 of [Quine] p. 40.  Also proved as Lemmas 16 and 17
       of [Tarski] p. 70.  The implication "to the left" also holds without a
       disjoint variable condition ( ~ sb2 ).  Theorem ~ sb6f replaces the
       disjoint variable condition with a nonfreeness hypothesis.  Theorem
       ~ sb4b replaces it with a distinctor antecedent.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by Wolf Lammen, 21-Sep-2018.)  Revise
       ~ df-sb .  (Revised by BJ, 22-Dec-2020.)  Remove use of ~ ax-11 .
       (Revised by Steven Nguyen, 7-Jul-2023.)  (Proof shortened by Wolf
       Lammen, 16-Jul-2023.) $)
    sb6 $p |- ( [ t / x ] ph <-> A. x ( x = t -> ph ) ) $=
      ( vy wsb weq wi wal dfsb equequ2 imbi1d albidv equsalvw bitri ) ABCEDCFZB
      DFZAGZBHZGDHBCFZAGZBHZABDCIRUADCOQTBOPSADCBJKLMN $.
  $}

  ${
    $d x y z $.  $d w y $.
    $( Equivalence for double substitution.  (Contributed by NM,
       3-Feb-2005.) $)
    2sb6 $p |- ( [ z / x ] [ w / y ] ph <->
               A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wsb weq wi wal wa sb6 19.21v impexp albii imbi2i 3bitr4ri bitri ) ACEFZ
      BDFBDGZRHZBISCEGZJAHZCIZBIRBDKTUCBSUAAHZHZCISUDCIZHUCTSUDCLUBUECSUAAMNRUF
      SACEKOPNQ $.
  $}

  ${
    $d x y $.
    $( One direction of ~ sb5 , provable from fewer axioms.  Version of ~ sb1
       with a disjoint variable condition using fewer axioms.  (Contributed by
       NM, 13-May-1993.)  (Revised by Wolf Lammen, 20-Jan-2024.) $)
    sb1v $p |- ( [ y / x ] ph -> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wi wal wa wex sb6 equs4v sylbi ) ABCDBCEZAFBGMAHBIABCJABCKL $.
  $}

  ${
    $d x ph $.
    $( Substitution for a variable not occurring in a proposition.  See ~ sbf
       for a version without disjoint variable condition on ` x , ph ` .  If
       one adds a disjoint variable condition on ` x , t ` , then ~ sbv can be
       proved directly by chaining ~ equsv with ~ sb6 .  (Contributed by BJ,
       22-Dec-2020.) $)
    sbv $p |- ( [ t / x ] ph <-> ph ) $=
      ( wsb wex spsbe ax5e syl wal ax-5 stdpc4 impbii ) ABCDZAMABEAABCFABGHAABI
      MABJABCKHL $.
  $}

  ${
    $d ph x $.  $d ph z $.
    $( Commutativity law for substitution.  This theorem was incorrectly used
       as our previous version of ~ pm11.07 but may still be useful.
       (Contributed by Andrew Salmon, 17-Jun-2011.)  (Proof shortened by Jim
       Kingdon, 22-Jan-2018.) $)
    sbcom4 $p |- ( [ w / x ] [ y / z ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( wsb sbv sbbii bitri 3bitr4i ) ABEFAADCFZBEFADEFZBCFZABEGKABEADCGHMABCFA
      LABCADEGHABCGIJ $.
  $}

  ${
    pm11.07.1 $e |- ph $.
    $( Axiom *11.07 in [WhiteheadRussell] p. 159.  The original reads: *11.07
       "Whatever possible argument ` x ` may be, ` ph ( x , y ) ` is true
       whatever possible argument ` y ` may be" implies the corresponding
       statement with ` x ` and ` y ` interchanged except
       in " ` ph ( x , y ) ` ".  Under our formalism this appears to correspond
       to ~ idi and not to ~ sbcom4 as earlier thought.  See
       ~ https://groups.google.com/g/metamath/c/iS0fOvSemC8/m/M1zTH8wxCAAJ .
       (Contributed by BJ, 16-Sep-2018.)  (New usage is discouraged.) $)
    pm11.07 $p |- ph $=
      (  ) B $.
  $}

  ${
    $d x ph $.
    $( Substitution in an implication with a variable not free in the
       antecedent affects only the consequent.  Version of ~ sbrim based on
       fewer axioms, but with more disjoint variable conditions.  (Contributed
       by Wolf Lammen, 29-Jan-2024.)  Remove DV condition.  (Revised by Wolf
       Lammen, 5-Jun-2026.) $)
    sbrimvw $p |- ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) ) $=
      ( wi wsb sbv sbi1 biimtrrid wn pm2.21 sbimi sylbir ax-1 ja impbii ) ABEZC
      DFZABCDFZEAACDFRSACDGABCDHIASRAJZTCDFRTCDGTQCDABKLMBQCDBANLOP $.
  $}

  ${
    $d x y $.  $d x ph $.
    $( Obsolete version of ~ sbrimvw as of 5-Jun-2026.  (Contributed by Wolf
       Lammen, 29-Jan-2024.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    sbrimvwOLD $p |- ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) ) $=
      ( wi wsb weq wal sb6 bi2.04 albii 19.21v 3bitr2i imbi2i bitr4i ) ABEZCDFZ
      ACDGZBEZCHZEZABCDFZEQRPEZCHASEZCHUAPCDIUDUCCARBJKASCLMUBTABCDINO $.
  $}

  ${
    $d t x $.
    sbbiiev.1 $e |- ( x = t -> ( ph <-> ps ) ) $.
    $( An equivalence of substitutions (as in ~ sbbii ) allowing the additional
       information that ` x = t ` .  Version of ~ sbiev and ~ sbievw without a
       disjoint variable condition on ` ps ` , useful for substituting only
       part of ` ph ` .  (Contributed by SN, 24-Aug-2025.) $)
    sbbiiev $p |- ( [ t / x ] ph <-> [ t / x ] ps ) $=
      ( weq wi wal wsb pm5.74i albii sb6 3bitr4i ) CDFZAGZCHNBGZCHACDIBCDIOPCNA
      BEJKACDLBCDLM $.
  $}

  ${
    $d x y $.  $d x ps $.
    sbievw.is $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit substitution.  Version
       of ~ sbie and ~ sbiev with more disjoint variable conditions, requiring
       fewer axioms.  (Contributed by NM, 30-Jun-1994.)  (Revised by BJ,
       18-Jul-2023.)  (Proof shortened by SN, 24-Aug-2025.) $)
    sbievw $p |- ( [ y / x ] ph <-> ps ) $=
      ( wsb sbbiiev sbv bitri ) ACDFBCDFBABCDEGBCDHI $.

    $( Obsolete version of ~ sbievw as of 24-Aug-2025.  (Contributed by NM,
       30-Jun-1994.)  (Revised by BJ, 18-Jul-2023.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sbievwOLD $p |- ( [ y / x ] ph <-> ps ) $=
      ( wsb weq wi wal sb6 equsalvw bitri ) ACDFCDGAHCIBACDJABCDEKL $.
  $}

  ${
    $d x ph $.  $d x ch $.  $d x y $.
    sbiedvw.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbievw ).  Version of ~ sbied and ~ sbiedv with more
       disjoint variable conditions, requiring fewer axioms.  (Contributed by
       NM, 30-Jun-1994.)  (Revised by GG, 29-Jan-2024.) $)
    sbiedvw $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( wsb wi sbrimvw weq wb expcom pm5.74d sbievw bitr3i pm5.74ri ) ABDEGZCAQ
      HABHZDEGACHZABDEIRSDEDEJZABCATBCKFLMNOP $.
  $}

  ${
    $d x y ps $.  $d x y t $.  $d u y $.
    2sbievw.1 $e |- ( ( x = t /\ y = u ) -> ( ph <-> ps ) ) $.
    $( Conversion of double implicit substitution to explicit substitution.
       Version of ~ 2sbiev with more disjoint variable conditions, requiring
       fewer axioms.  (Contributed by AV, 29-Jul-2023.)  Avoid ~ ax-13 .
       (Revised by GG, 10-Jan-2024.) $)
    2sbievw $p |- ( [ t / x ] [ u / y ] ph <-> ps ) $=
      ( wsb weq sbiedvw sbievw ) ADEHBCFCFIABDEGJK $.
  $}

  ${
    $d y z $.
    $( Substituting ` y ` for ` x ` and then ` z ` for ` y ` is equivalent to
       substituting ` z ` for both ` x ` and ` y ` .  Version of ~ sbcom3 with
       a disjoint variable condition using fewer axioms.  (Contributed by NM,
       27-May-1997.)  (Revised by Giovanni Mascellani, 8-Apr-2018.)  (Revised
       by BJ, 30-Dec-2020.)  (Proof shortened by Wolf Lammen, 19-Jan-2023.) $)
    sbcom3vv $p |- ( [ z / y ] [ y / x ] ph <-> [ z / y ] [ z / x ] ph ) $=
      ( wsb sbequ sbbiiev ) ABCEABDECDACDBFG $.
  $}

  ${
    $d x w $.  $d w y $.  $d w ph $.  $d w ps $.  $d x ch $.
    sbievw2.1 $e |- ( x = w -> ( ph <-> ch ) ) $.
    sbievw2.2 $e |- ( w = y -> ( ch <-> ps ) ) $.
    $( ~ sbievw applied twice, avoiding a DV condition on ` x ` , ` y ` .
       Based on proofs by Wolf Lammen.  (Contributed by Steven Nguyen,
       29-Jul-2023.) $)
    sbievw2 $p |- ( [ y / x ] ph <-> ps ) $=
      ( wsb sbcom3vv sbievw sbbii sbv 3bitr3i bitr3i ) ADEIZCFEIZBADFIZFEIPFEIQ
      PADFEJRCFEACDFGKLPFEMNCBFEHKO $.
  $}

  ${
    $d x z w $.  $d z ph w $.  $d y w $.
    $( A composition law for substitution.  Version of ~ sbco2 with disjoint
       variable conditions and fewer axioms.  (Contributed by NM, 30-Jun-1994.)
       (Revised by BJ, 22-Dec-2020.)  (Proof shortened by Wolf Lammen,
       29-Apr-2023.) $)
    sbco2vv $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      ( vw wsb sbequ sbievw2 ) ABDFABCFABEFDCEADEBGAECBGH $.
  $}

  ${
    $d x y $.  $d ph y $.  $d ps x $.
    cbvsbv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change the bound variable (i.e. the substituted one) in wff's linked by
       implicit substitution.  The proof was extracted from a former ~ cbvabv
       version.  (Contributed by Wolf Lammen, 16-Mar-2025.) $)
    cbvsbv $p |- ( [ z / x ] ph <-> [ z / y ] ps ) $=
      ( wsb sbco2vv sbievw sbbii bitr3i ) ACEGACDGZDEGBDEGACEDHLBDEABCDFIJK $.
    $( $j usage 'cbvsbv' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d v w ph $.  $d v w x $.  $d v w y $.
    $( Lemma for ~ sbco4 .  It replaces the temporary variable ` v ` with
       another temporary variable ` w ` .  (Contributed by Jim Kingdon,
       26-Sep-2018.)  (Proof shortened by Wolf Lammen, 12-Oct-2024.)  Avoid
       ~ ax-11 .  (Revised by SN, 3-Sep-2025.) $)
    sbco4lem $p |- ( [ x / v ] [ y / x ] [ v / y ] ph <->
                     [ x / w ] [ y / x ] [ w / y ] ph ) $=
      ( wsb weq sbequ sbbidv cbvsbv ) ACEFZBCFACDFZBCFEDBEDGKLBCAEDCHIJ $.
    $( $j usage 'sbco4lem' avoids 'ax-11'; $)
  $}

  ${
    $d t u v ph $.  $d t u v x $.  $d t u v y $.  $d w ph $.  $d w x $.
    $d w y $.  $d t w $.
    $( Two ways of exchanging two variables.  Both sides of the biconditional
       exchange ` x ` and ` y ` , either via two temporary variables ` u ` and
       ` v ` , or a single temporary ` w ` .  (Contributed by Jim Kingdon,
       25-Sep-2018.)  Avoid ~ ax-11 .  (Revised by SN, 3-Sep-2025.) $)
    sbco4 $p |- ( [ y / u ] [ x / v ] [ u / x ] [ v / y ] ph <->
        [ x / w ] [ y / x ] [ w / y ] ph ) $=
      ( vt wsb weq sbequ sbbidv sbievw sbco4lem 3bitri ) ACEHZBFHZEBHZFCHOBCHZE
      BHZACGHBCHGBHACDHBCHDBHQSFCFCIPREBOFCBJKLABCGEMABCDGMN $.
    $( $j usage 'sbco4' avoids 'ax-11'; $)
  $}

  ${
    $d x w z $.  $d y w $.
    $( Substitution in an equality.  (Contributed by Raph Levien and FL,
       4-Dec-2005.)  Reduce axiom usage.  (Revised by Wolf Lammen,
       23-Jul-2023.) $)
    equsb3 $p |- ( [ y / x ] x = z <-> y = z ) $=
      ( vw weq equequ1 sbievw2 ) ACEBCEDCEABDADCFDBCFG $.

    $( Substitution applied to the atomic wff with equality.  Variant of
       ~ equsb3 .  (Contributed by AV, 29-Jul-2023.)  (Proof shortened by Wolf
       Lammen, 2-Sep-2023.) $)
    equsb3r $p |- ( [ y / x ] z = x <-> z = y ) $=
      ( vw weq equequ2 sbievw2 ) CAECBECDEABDADCFDBCFG $.
  $}

  ${
    $d x y $.
    $( Substitution applied to an atomic wff.  Version of ~ equsb1 with a
       disjoint variable condition, which neither requires ~ ax-12 nor
       ~ ax-13 .  (Contributed by NM, 10-May-1993.)  (Revised by BJ,
       11-Sep-2019.)  Remove dependencies on axioms.  (Revised by Wolf Lammen,
       30-May-2023.)  (Proof shortened by Steven Nguyen, 19-Jun-2023.)  Revise
       ~ df-sb .  (Revised by Steven Nguyen, 11-Jul-2023.)  (Proof shortened by
       Steven Nguyen, 22-Jul-2023.) $)
    equsb1v $p |- [ y / x ] x = y $=
      ( weq wsb equid equsb3 mpbir ) ABCABDBBCBEABBFG $.
  $}

  $( Any substitution in an always false formula is false.  (Contributed by
     Steven Nguyen, 3-May-2023.) $)
  nsb $p |- ( A. x -. ph -> -. [ t / x ] ph ) $=
    ( wn wal wex wsb alnex biimpi spsbe nsyl ) ADBEZABFZABCGLMDABHIABCJK $.

  $( One direction of ~ sbn , using fewer axioms.  Compare ~ 19.2 .
     (Contributed by Steven Nguyen, 18-Aug-2023.) $)
  sbn1 $p |- ( [ t / x ] -. ph -> -. [ t / x ] ph ) $=
    ( wn wsb wfal nsb fal mpg pm2.21 sb2imi mtoi ) ADZBCEABCEFBCEZFDNDBFBCGHIMA
    FBCAFJKL $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Membership predicate
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the membership predicate symbol. $)
  $c e. $.  $( Stylized lowercase Greek letter epsilon. $)


  $( Extend wff definition to include atomic formulas with the membership
     predicate.  This is read either " ` x ` is an element of ` y ` ",
     or " ` x ` is a member of ` y ` ", or " ` x ` belongs to ` y ` ",
     or " ` y ` contains ` x ` ".  Note:  The phrase " ` y ` includes
     ` x ` " means " ` x ` is a subset of ` y ` "; to use it also for
     ` x e. y ` , as some authors occasionally do, is poor form and causes
     confusion, according to George Boolos (1992 lecture at MIT).

     This syntactic construction introduces a binary non-logical predicate
     symbol ` e. ` (stylized lowercase epsilon) into our predicate calculus.
     We will eventually use it for the membership predicate of set theory, but
     that is irrelevant at this point: the predicate calculus axioms for ` e. `
     apply to any arbitrary binary predicate symbol.  "Non-logical" means that
     the predicate is presumed to have additional properties beyond the realm
     of predicate calculus, although these additional properties are not
     specified by predicate calculus itself but rather by the axioms of a
     theory (in our case set theory) added to predicate calculus.  "Binary"
     means that the predicate has two arguments.

     Instead of introducing ~ wel as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wcel .  This lets us avoid overloading
     the ` e. ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ wel is considered to be a
     primitive syntax, even though here it is artificially "derived" from
     ~ wcel .  Note:  To see the proof steps of this syntax proof, type "MM>
     SHOW PROOF wel / ALL" in the Metamath program.  (Contributed by NM,
     24-Jan-2006.) $)
  wel $p wff x e. y $=
    ( cv wcel ) ACBCD $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-8 (Left Equality for Binary Predicate)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Left Equality for Binary Predicate.  One of the equality and
     substitution axioms for a non-logical predicate in our predicate calculus
     with equality.  It substitutes equal variables into the left-hand side of
     an arbitrary binary predicate ` e. ` , which we will use for the set
     membership relation when set theory is introduced.  This axiom scheme is a
     sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom scheme C12' in [Megill] p. 448 (p. 16 of the preprint).
     "Non-logical" means that the predicate is not a primitive of predicate
     calculus proper but instead is an extension to it.  "Binary" means that
     the predicate has two arguments.  In a system of predicate calculus with
     equality, like ours, equality is not usually considered to be a
     non-logical predicate.  In systems of predicate calculus without equality,
     it typically would be.

     We prove in ~ ax8 that this axiom can be recovered from its weakened
     version ~ ax8v where ` x ` and ` y ` are assumed to be disjoint variables.
     In particular, the only theorem referencing ~ ax-8 should be ~ ax8v .  See
     the comment of ~ ax8v for more details on these matters.  (Contributed by
     NM, 30-Jun-1993.)  (Revised by BJ, 7-Dec-2020.)  Use ~ ax8 instead.
     (New usage is discouraged.) $)
  ax-8 $a |- ( x = y -> ( x e. z -> y e. z ) ) $.

  ${
    $d x y $.
    $( Weakened version of ~ ax-8 , with a disjoint variable condition on
       ` x , y ` .  This should be the only proof referencing ~ ax-8 , and it
       should be referenced only by its two weakened versions ~ ax8v1 and
       ~ ax8v2 , from which ~ ax-8 is then rederived as ~ ax8 , which shows
       that either ~ ax8v or the conjunction of ~ ax8v1 and ~ ax8v2 is
       sufficient.  (Contributed by BJ, 7-Dec-2020.)  Use ~ ax8 instead.
       (New usage is discouraged.) $)
    ax8v $p |- ( x = y -> ( x e. z -> y e. z ) ) $=
      ( ax-8 ) ABCD $.
  $}

  ${
    $d x y $.  $d x z $.
    $( First of two weakened versions of ~ ax8v , with an extra disjoint
       variable condition on ` x , z ` , see comments there.  (Contributed by
       BJ, 7-Dec-2020.) $)
    ax8v1 $p |- ( x = y -> ( x e. z -> y e. z ) ) $=
      ( ax8v ) ABCD $.
  $}

  ${
    $d x y $.  $d y z $.
    $( Second of two weakened versions of ~ ax8v , with an extra disjoint
       variable condition on ` y , z ` see comments there.  (Contributed by BJ,
       7-Dec-2020.) $)
    ax8v2 $p |- ( x = y -> ( x e. z -> y e. z ) ) $=
      ( ax8v ) ABCD $.
  $}

  ${
    $d t x $.  $d t y $.  $d t z $.
    $( Proof of ~ ax-8 from ~ ax8v1 and ~ ax8v2 , proving sufficiency of the
       conjunction of the latter two weakened versions of ~ ax8v , which is
       itself a weakened version of ~ ax-8 .  (Contributed by BJ, 7-Dec-2020.)
       (Proof shortened by Wolf Lammen, 11-Apr-2021.) $)
    ax8 $p |- ( x = y -> ( x e. z -> y e. z ) ) $=
      ( vt weq wa wex wel wi equvinv ax8v2 equcoms ax8v1 sylan9 exlimiv sylbi )
      ABEDAEZDBEZFZDGACHZBCHZIZABDJSUBDQTDCHZRUATUCIADADCKLDBCMNOP $.
  $}

  $( An identity law for the non-logical predicate.  (Contributed by NM,
     30-Jun-1993.) $)
  elequ1 $p |- ( x = y -> ( x e. z <-> y e. z ) ) $=
    ( weq wel ax8 wi equcoms impbid ) ABDACEZBCEZABCFKJGBABACFHI $.

  ${
    $d w x z $.  $d w y $.
    $( Substitution for the first argument of the non-logical predicate in an
       atomic formula.  See ~ elsb2 for substitution for the second argument.
       (Contributed by NM, 7-Nov-2006.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.)  Reduce axiom usage.  (Revised by Wolf Lammen,
       24-Jul-2023.) $)
    elsb1 $p |- ( [ y / x ] x e. z <-> y e. z ) $=
      ( vw wel elequ1 sbievw2 ) ACEBCEDCEABDADCFDBCFG $.
  $}

  ${
    $d x z $.  $d y z $.
    $( When the class variables in Definition ~ df-clel are replaced with
       setvar variables, this theorem of predicate calculus is the result.
       This theorem provides part of the justification for the consistency of
       that definition, which "overloads" the setvar variables in ~ wel with
       the class variables in ~ wcel .  (Contributed by NM, 28-Jan-2004.)
       Revised to use ~ equsexvw in order to remove dependencies on ~ ax-10 ,
       ~ ax-12 , ~ ax-13 .  Note that there is no disjoint variable condition
       on ` x , y ` , that is, on the variables of the left-hand side, as
       should be the case for definitions.  (Revised by BJ, 29-Dec-2020.) $)
    cleljust $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $=
      ( weq wel wa wex elequ1 equsexvw bicomi ) CADCBEZFCGABEZKLCACABHIJ $.
    $( $j usage 'cleljust' avoids 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-9 (Right Equality for Binary Predicate)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Right Equality for Binary Predicate.  One of the equality and
     substitution axioms for a non-logical predicate in our predicate calculus
     with equality.  It substitutes equal variables into the right-hand side of
     an arbitrary binary predicate ` e. ` , which we will use for the set
     membership relation when set theory is introduced.  This axiom scheme is a
     sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom scheme C13' in [Megill] p. 448 (p. 16 of the preprint).

     We prove in ~ ax9 that this axiom can be recovered from its weakened
     version ~ ax9v where ` x ` and ` y ` are assumed to be disjoint variables.
     In particular, the only theorem referencing ~ ax-9 should be ~ ax9v .  See
     the comment of ~ ax9v for more details on these matters.  (Contributed by
     NM, 21-Jun-1993.)  (Revised by BJ, 7-Dec-2020.)  Use ~ ax9 instead.
     (New usage is discouraged.) $)
  ax-9 $a |- ( x = y -> ( z e. x -> z e. y ) ) $.

  ${
    $d x y $.
    $( Weakened version of ~ ax-9 , with a disjoint variable condition on
       ` x , y ` .  This should be the only proof referencing ~ ax-9 , and it
       should be referenced only by its two weakened versions ~ ax9v1 and
       ~ ax9v2 , from which ~ ax-9 is then rederived as ~ ax9 , which shows
       that either ~ ax9v or the conjunction of ~ ax9v1 and ~ ax9v2 is
       sufficient.  (Contributed by BJ, 7-Dec-2020.)  Use ~ ax9 instead.
       (New usage is discouraged.) $)
    ax9v $p |- ( x = y -> ( z e. x -> z e. y ) ) $=
      ( ax-9 ) ABCD $.
  $}

  ${
    $d x y $.  $d x z $.
    $( First of two weakened versions of ~ ax9v , with an extra disjoint
       variable condition on ` x , z ` , see comments there.  (Contributed by
       BJ, 7-Dec-2020.) $)
    ax9v1 $p |- ( x = y -> ( z e. x -> z e. y ) ) $=
      ( ax9v ) ABCD $.
  $}

  ${
    $d x y $.  $d y z $.
    $( Second of two weakened versions of ~ ax9v , with an extra disjoint
       variable condition on ` y , z ` see comments there.  (Contributed by BJ,
       7-Dec-2020.) $)
    ax9v2 $p |- ( x = y -> ( z e. x -> z e. y ) ) $=
      ( ax9v ) ABCD $.
  $}

  ${
    $d t x $.  $d t y $.  $d t z $.
    $( Proof of ~ ax-9 from ~ ax9v1 and ~ ax9v2 , proving sufficiency of the
       conjunction of the latter two weakened versions of ~ ax9v , which is
       itself a weakened version of ~ ax-9 .  (Contributed by BJ, 7-Dec-2020.)
       (Proof shortened by Wolf Lammen, 11-Apr-2021.) $)
    ax9 $p |- ( x = y -> ( z e. x -> z e. y ) ) $=
      ( vt weq wa wex wel wi equvinv ax9v2 equcoms ax9v1 sylan9 exlimiv sylbi )
      ABEDAEZDBEZFZDGCAHZCBHZIZABDJSUBDQTCDHZRUATUCIADADCKLDBCMNOP $.
  $}

  $( An identity law for the non-logical predicate.  (Contributed by NM,
     21-Jun-1993.) $)
  elequ2 $p |- ( x = y -> ( z e. x <-> z e. y ) ) $=
    ( weq wel ax9 wi equcoms impbid ) ABDCAEZCBEZABCFKJGBABACFHI $.

  ${
    $d x z $.  $d y z $.
    $( A form of ~ elequ2 with a universal quantifier.  Its converse is the
       axiom of extensionality ~ ax-ext .  (Contributed by BJ, 3-Oct-2019.) $)
    elequ2g $p |- ( x = y -> A. z ( z e. x <-> z e. y ) ) $=
      ( weq wel wb elequ2 alrimiv ) ABDCAECBEFCABCGH $.
  $}

  ${
    $d w x z $.  $d w y $.
    $( Substitution for the second argument of the non-logical predicate in an
       atomic formula.  See ~ elsb1 for substitution for the first argument.
       (Contributed by Rodolfo Medina, 3-Apr-2010.)  (Proof shortened by Andrew
       Salmon, 14-Jun-2011.)  Reduce axiom usage.  (Revised by Wolf Lammen,
       24-Jul-2023.) $)
    elsb2 $p |- ( [ y / x ] z e. x <-> z e. y ) $=
      ( vw wel elequ2 sbievw2 ) CAECBECDEABDADCFDBCFG $.
  $}

  $( An identity law for the non-logical predicate, which combines ~ elequ1 and
     ~ elequ2 .  The analogous theorems for class terms are ~ eleq1 , ~ eleq2 ,
     and ~ eleq12 respectively.  (Contributed by BJ, 29-Sep-2019.) $)
  elequ12 $p |- ( ( x = y /\ z = t ) -> ( x e. z <-> y e. t ) ) $=
    ( weq wel elequ1 elequ2 sylan9bb ) ABEACFBCFCDEBDFABCGCDBHI $.

  ${
    $d x y $.
    $( The FOL statement used in the standard proof of Russell's paradox ~ ru .
       (Contributed by NM, 7-Aug-1994.)  Extract from proof of ~ ru and reduce
       axiom usage.  (Revised by BJ, 12-Oct-2019.) $)
    ru0 $p |- -. A. x ( x e. y <-> -. x e. x ) $=
      ( wel wn wb wal pm5.19 weq elequ1 elequ12 anidms notbid bibi12d spvv mto
      ) ABCZAACZDZEZAFBBCZTDZEZTGSUBABABHZPTRUAABBIUCQTUCQTEABABJKLMNO $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical redundancy of ax-10 , ax-11 , ax-12 , ax-13
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The original axiom schemes of Tarski's predicate calculus are ~ ax-4 ,
  ~ ax-5 , ~ ax6v , ~ ax-7 , ~ ax-8 , and ~ ax-9 , together with rule
  ~ ax-gen .  See ~ mmset.html#compare .  They are given as axiom schemes B4
  through B8 in [KalishMontague] p. 81.  These are shown to be logically
  complete by Theorem 1 of [KalishMontague] p. 85.

  The axiom system of set.mm includes the auxiliary axiom schemes ~ ax-10 ,
  ~ ax-11 , ~ ax-12 , and ~ ax-13 , which are not part of Tarski's axiom
  schemes.  Each object-language instance of them is provable from Tarski's
  axioms, so they are logically redundant.  However, they are conjectured not
  to be provable directly _as schemes_ from Tarski's axiom schemes using only
  Metamath's direct substitution rule.  They are used to make our system
  "scheme complete", i.e., able to prove directly all possible schemes
  with wff and setvar variables, bundled or not, whose object-language
  instances are valid.  ( ~ ax-12 has been proved to be required; see
  ~ https://us.metamath.org/award2003.html#9a .  Metalogical independence of
  the other three are open problems.)

  (There are additional predicate calculus axiom schemes included in set.mm
  such as ~ ax-c5 , but they can all be proved as theorems from the above.)

  Terminology:  Two setvar (individual) metavariables are "bundled" in an axiom
  or theorem scheme when there is no distinct variable constraint ($d) imposed
  on them.  (The term "bundled" is due to Raph Levien.)  For example, the ` x `
  and ` y ` in ~ ax-6 are bundled, but they are not in ~ ax6v . We also say
  that a scheme is bundled when it has at least one pair of bundled setvar
  variables.  If distinct variable conditions are added to all setvar variable
  pairs in a bundled scheme, we call that the "principal" instance
  of the bundled scheme.  For example, ~ ax6v is the principal instance of
  ~ ax-6 . Whenever a common variable is substituted for two or more bundled
  variables in an axiom or theorem scheme, we call the substitution instance
  "degenerate".  For example, the instance ` -. A. x -. x = x ` of ~ ax-6 is
  degenerate.  An advantage of bundling is ease of use since there are fewer
  distinct variable restrictions ($d) to be concerned with, and theorems
  are more general.  There may be some
  economy in being able to prove facts about principal and degenerate instances
  simultaneously.  A disadvantage is that bundling may present difficulties in
  translations to other proof languages, which typically lack the concept (in
  part because their variables often represent the variables of the
  object language rather than metavariables ranging over them).

  Because Tarski's axiom schemes are logically complete, they can be used to
  prove any object-language instance of ~ ax-10 , ~ ax-11 , ~ ax-12 , and
  ~ ax-13 .  "Translating" this to Metamath, it means that Tarski's axioms can
  prove any substitution instance of ~ ax-10 , ~ ax-11 , ~ ax-12 , or ~ ax-13
  in which (1) there are no wff metavariables and (2) all setvar variables
  are mutually distinct i.e. are not bundled.  In effect this is mimicking the
  object language by pretending that each setvar variable is an
  object-language variable.  (There may also be specific instances with wff
  metavariables and/or bundling that are directly provable from Tarski's axiom
  schemes, but it isn't guaranteed.  Whether all of them are possible is part
  of the still open metalogical independence problem for our additional axiom
  schemes.)

  It can be useful to see how this can be done, both to show that our
  additional schemes are valid metatheorems of Tarski's system and to be able
  to translate object-language instances of our proofs into proofs that would
  work with a system using only Tarski's original schemes.  In addition, it may
  (or may not) provide insight into the conjectured metalogical independence of
  our additional schemes.

  The theorem schemes ~ ax10w , ~ ax11w , ~ ax12w , and ~ ax13w are derived
  using only Tarski's axiom schemes, showing that Tarski's schemes can be used
  to derive all substitution instances of ~ ax-10 , ~ ax-11 , ~ ax-12 , and
  ~ ax-13 meeting Conditions (1) and (2).  (The "w" suffix stands for "weak
  version".)  Each hypothesis of ~ ax10w , ~ ax11w , and ~ ax12w is of the form
  ` ( x = y -> ( ph <-> ps ) ) ` where ` ps ` is an auxiliary or "dummy" wff
  metavariable in which ` x ` doesn't occur.  We can show by induction on
  formula length that the hypotheses can be eliminated in all cases meeting
  Conditions (1) and (2).  The example ~ ax12wdemo illustrates the techniques
  (equality theorems and bound variable renaming) used to achieve this.

  We also show the degenerate instances for axioms with bundled variables in
  ~ ax11dgen , ~ ax12dgen , ~ ax13dgen1 , ~ ax13dgen2 , ~ ax13dgen3 , and
  ~ ax13dgen4 . (Their proofs are trivial, but we include them to be thorough.)
  Combining the principal and degenerate cases _outside_ of Metamath, we show
  that the bundled schemes ~ ax-10 , ~ ax-11 , ~ ax-12 , and ~ ax-13 are
  schemes of Tarski's system, meaning that all object-language instances they
  generate are theorems of Tarski's system.

  It is interesting that Tarski used the bundled scheme ~ ax-6 in an older
  system, so it seems the main purpose of his later ~ ax6v was just to show
  that the weaker unbundled form is sufficient rather than an aesthetic
  objection to bundled free and bound variables.  Since we adopt the
  bundled ~ ax-6 as our official axiom, we show that the degenerate
  instance holds in ~ ax6dgen .  (Recall that in set.mm, the only statement
  referencing ~ ax-6 is ~ ax6v .)

  The case of ~ sp is curious:  originally an axiom scheme of Tarski's system,
  it was proved logically redundant by Lemma 9 of [KalishMontague] p. 86.
  However, the proof is by induction on formula length, and the scheme form
  ` A. x ph -> ph ` apparently cannot be proved directly from Tarski's other
  axiom schemes.  The best we can do seems to be ~ spw , again requiring
  substitution instances of ` ph ` that meet Conditions (1) and (2) above.
  Note that our direct proof ~ sp requires ~ ax-12 , which is not part of
  Tarski's system.

$)

  $( Tarski's system uses the weaker ~ ax6v instead of the bundled ~ ax-6 , so
     here we show that the degenerate case of ~ ax-6 can be derived.  Even
     though ~ ax-6 is in the list of axioms used, recall that in set.mm, the
     only statement referencing ~ ax-6 is ~ ax6v .  We later rederive from
     ~ ax6v the bundled form as ~ ax6 with the help of the auxiliary axiom
     schemes.  (Contributed by NM, 23-Apr-2017.) $)
  ax6dgen $p |- -. A. x -. x = x $=
    ( weq wn wal equid notnoti spfalw mt2 ) AABZCZADIAEZJAIKFGH $.

  ${
    $d y ph $.  $d x ps $.  $d x y $.
    ax10w.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ ax-10 from which we can prove any ~ ax-10 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  It is an alias of ~ hbn1w introduced for labeling consistency.
       (Contributed by NM, 9-Apr-2017.)  Use ~ hbn1w instead.
       (New usage is discouraged.) $)
    ax10w $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
      ( hbn1w ) ABCDEF $.
  $}

  ${
    $d y z $.  $d x y $.  $d z ph $.  $d y ps $.
    ax11w.1 $e |- ( y = z -> ( ph <-> ps ) ) $.
    $( Weak version of ~ ax-11 from which we can prove any ~ ax-11 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  Unlike ~ ax-11 , this theorem requires that ` x ` and ` y ` be
       distinct i.e. are not bundled.  It is an alias of ~ alcomimw introduced
       for labeling consistency.  (Contributed by NM, 10-Apr-2017.)  Use
       ~ alcomimw instead.  (New usage is discouraged.) $)
    ax11w $p |- ( A. x A. y ph -> A. y A. x ph ) $=
      ( alcomimw ) ABCDEFG $.
    $( $j usage 'ax11w' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  $( Degenerate instance of ~ ax-11 where bundled variables ` x ` and ` y `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax11dgen $p |- ( A. x A. x ph -> A. x A. x ph ) $=
    ( wal id ) ABCBCD $.
  $( $j usage 'ax11dgen' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)

  ${
    $d x ps $.
    ax12wlemw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Lemma for weak version of ~ ax-12 .  Uses only Tarski's FOL axiom
       schemes.  In some cases, this lemma may lead to shorter proofs than
       ~ ax12w .  (Contributed by NM, 10-Apr-2017.) $)
    ax12wlem $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( ax-5 ax12i ) ABCDEBCFG $.
  $}

  ${
    $d y z $.  $d x ps $.  $d z ph $.  $d y ch $.
    ax12w.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    ax12w.2 $e |- ( y = z -> ( ph <-> ch ) ) $.
    $( Weak version of ~ ax-12 from which we can prove any ~ ax-12 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  An instance of the first hypothesis will normally require that
       ` x ` and ` y ` be distinct (unless ` x ` does not occur in ` ph ` ).
       For an example of how the hypotheses can be eliminated when we
       substitute an expression without wff variables for ` ph ` , see
       ~ ax12wdemo .  (Contributed by NM, 10-Apr-2017.) $)
    ax12w $p |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $=
      ( wal weq wi spw ax12wlem syl5 ) AEIADEJZOAKDIACEFHLABDEGMN $.
    $( $j usage 'ax12w' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  $( Degenerate instance of ~ ax-12 where bundled variables ` x ` and ` y `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax12dgen $p |- ( x = x -> ( A. x ph -> A. x ( x = x -> ph ) ) ) $=
    ( wal weq wi ala1 a1i ) ABCBBDZAEBCEHAHBFG $.
  $( $j usage 'ax12dgen' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)

  ${
    $d x y z w v $.
    $( Example of an application of ~ ax12w that results in an instance of
       ~ ax-12 for a contrived formula with mixed free and bound variables,
       ` ( x e. y /\ A. x z e. x /\ A. y A. z y e. x ) ` , in place of ` ph ` .
       The proof illustrates bound variable renaming with ~ cbvalvw to obtain
       fresh variables to avoid distinct variable clashes.  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 14-Apr-2017.) $)
    ax12wdemo $p |- ( x = y
              -> ( A. y ( x e. y /\ A. x z e. x /\ A. y A. z y e. x )
     -> A. x ( x = y -> ( x e. y /\ A. x z e. x /\ A. y A. z y e. x ) ) ) ) $=
      ( vw vv wel wal w3a weq elequ1 elequ2 cbvalvw a1i albidv bitrid 3anbi123d
      wb 3anbi13d ax12w ) ABFZCAFZAGZBAFZCGZBGZHBBFZCDFZDGZEBFZCGZEGZHAEFZUBEAF
      ZCGZEGZHABEABIZTUFUBUHUEUKABBJUBUHQUPUAUGADADCKLMUEUOUPUKUDUNBEBEIZUCUMCB
      EAJNLZUPUNUJEUPUMUICABEKNNOPUQTULUEUOUBBEAKUEUOQUQURMRS $.
    $( $j usage 'ax12wdemo' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d x z $.
    $( Weak version (principal instance) of ~ ax-13 .  (Because ` y ` and ` z `
       don't need to be distinct, this actually bundles the principal instance
       and the degenerate instance
       ` ( -. x = y -> ( y = y -> A. x y = y ) ) ` .)  Uses only Tarski's FOL
       axiom schemes.  The proof is trivial but is included to complete the set
       ~ ax10w , ~ ax11w , and ~ ax12w .  (Contributed by NM, 10-Apr-2017.) $)
    ax13w $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
      ( weq wn ax5d ) ABDEBCDAF $.
    $( $j usage 'ax13w' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13'; $)
  $}

  $( Degenerate instance of ~ ax-13 where bundled variables ` x ` and ` y `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax13dgen1 $p |- ( -. x = x -> ( x = z -> A. x x = z ) ) $=
    ( weq wal wi equid pm2.24i ) AACABCZHADEAFG $.
  $( $j usage 'ax13dgen1' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
     'ax-13'; $)

  $( Degenerate instance of ~ ax-13 where bundled variables ` x ` and ` z `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax13dgen2 $p |- ( -. x = y -> ( y = x -> A. x y = x ) ) $=
    ( weq wn wal equcomi pm2.21 syl5 ) BACZABCZJDIAEZBAFJKGH $.
  $( $j usage 'ax13dgen2' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
     'ax-13'; $)

  $( Degenerate instance of ~ ax-13 where bundled variables ` y ` and ` z `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax13dgen3 $p |- ( -. x = y -> ( y = y -> A. x y = y ) ) $=
    ( weq wal wn equid ax-gen 2a1i ) BBCZADABCEIIABFGH $.
  $( $j usage 'ax13dgen3' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
     'ax-13'; $)

  $( Degenerate instance of ~ ax-13 where bundled variables ` x ` , ` y ` , and
     ` z ` have a common substitution.  Therefore, also a degenerate instance
     of ~ ax13dgen1 , ~ ax13dgen2 , and ~ ax13dgen3 .  Also an instance of the
     intuitionistic tautology ~ pm2.21 .  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.)  Reduce axiom usage.  (Revised by Wolf
     Lammen, 10-Oct-2021.) $)
  ax13dgen4 $p |- ( -. x = x -> ( x = x -> A. x x = x ) ) $=
    ( weq wal pm2.21 ) AABZEACD $.
  $( $j usage 'ax13dgen4' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
     'ax-13'; $)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Predicate calculus with equality:  Auxiliary axiom schemes (4 schemes)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  In this section we introduce four additional schemes ~ ax-10 , ~ ax-11 ,
  ~ ax-12 , and ~ ax-13 that are not part of Tarski's system but can be proved
  (outside of Metamath) as theorem schemes of Tarski's system.  These are
  needed to give our system the property of "scheme completeness", which
  means that we can prove (with Metamath) all possible theorem schemes
  expressible in our language of wff metavariables ranging over object-language
  wffs, and setvar variables ranging over object-language individual variables.

  To show that these schemes are valid metatheorems of Tarski's system S2,
  above we proved from Tarski's system theorems ~ ax10w , ~ ax11w , ~ ax12w ,
  and ~ ax13w , which show that any object-language instance of these schemes
  (emulated by having no wff metavariables and requiring all setvar variables
  to be mutually distinct) can be proved using only the schemes in Tarski's
  system S2.

  An open problem is to show that these four additional schemes are mutually
  _metalogically_ independent and metalogically independent from Tarski's.  So
  far, independence of ~ ax-12 from all others has been shown, and
  independence of Tarski's ~ ax-6 from all others has been shown; see
  items 9a and 11 on ~ https://us.metamath.org/award2003.html .

$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-10 (Quantified Negation)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Negation.  Axiom C5-2 of [Monk2] p. 113.  This axiom
     scheme is logically redundant (see ~ ax10w ) but is used as an auxiliary
     axiom scheme to achieve scheme completeness.  It means that ` x ` is not
     free in ` -. A. x ph ` .  (Contributed by NM, 21-May-2008.)  Use its alias
     ~ hbn1 instead if you must use it.  Any theorem in first-order logic (FOL)
     that contains only set variables that are all mutually distinct, and has
     no wff variables, can be proved *without* using ~ ax-10 through ~ ax-13 ,
     by invoking ~ ax10w through ~ ax13w .  We encourage proving theorems
     *without* ~ ax-10 through ~ ax-13 and moving them up to the ~ ax-4 through
     ~ ax-9 section.  (New usage is discouraged.) $)
  ax-10 $a |- ( -. A. x ph -> A. x -. A. x ph ) $.

  $( Alias for ~ ax-10 to be used instead of it.  (Contributed by NM,
     24-Jan-1993.)  (Proof shortened by Wolf Lammen, 18-Aug-2014.) $)
  hbn1 $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    ( ax-10 ) ABC $.

  $( The setvar ` x ` is not free in ` E. x ph ` .  Corresponds to the axiom
     (5) of modal logic (see also ~ modal5 ).  (Contributed by NM,
     24-Jan-1993.) $)
  hbe1 $p |- ( E. x ph -> A. x E. x ph ) $=
    ( wex wn wal df-ex hbn1 hbxfrbi ) ABCADZBEDBABFIBGH $.

  $( Dual statement of ~ hbe1 .  Modified version of ~ axc7e with a universally
     quantified consequent.  (Contributed by Wolf Lammen, 15-Sep-2021.) $)
  hbe1a $p |- ( E. x A. x ph -> A. x ph ) $=
    ( wal wex wn df-ex hbn1 con1i sylbi ) ABCZBDJEBCZEJJBFJKABGHI $.

  $( One direction of ~ nf5 can be proved with a smaller footprint on axiom
     usage.  (Contributed by Wolf Lammen, 16-Sep-2021.) $)
  nf5-1 $p |- ( A. x ( ph -> A. x ph ) -> F/ x ph ) $=
    ( wal wi wex exim hbe1a syl6 nfd ) AABCZDBCZABKABEJBEJAJBFABGHI $.

  ${
    nf5i.1 $e |- ( ph -> A. x ph ) $.
    $( Deduce that ` x ` is not free in ` ph ` from the definition.
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nf5i $p |- F/ x ph $=
      ( wal wi wnf nf5-1 mpg ) AABDEABFBABGCH $.
  $}

  ${
    nf5dh.1 $e |- ( ph -> A. x ph ) $.
    nf5dh.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduce that ` x ` is not free in ` ps ` in a context.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) ~ df-nf changed.  (Revised by Wolf Lammen,
       11-Oct-2021.) $)
    nf5dh $p |- ( ph -> F/ x ps ) $=
      ( wal wi wnf alrimih nf5-1 syl ) ABBCFGZCFBCHALCDEIBCJK $.
  $}

  ${
    $d x ph $.
    nf5dv.1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Apply the definition of not-free in a context.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) ~ df-nf changed.  (Revised by Wolf Lammen,
       18-Sep-2021.)  (Proof shortened by Wolf Lammen, 13-Jul-2022.) $)
    nf5dv $p |- ( ph -> F/ x ps ) $=
      ( ax-5 nf5dh ) ABCACEDF $.
  $}

  ${
    $d x y $.
    $( All variables are effectively bound in a distinct variable specifier.
       Version of ~ nfnae with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by Mario Carneiro, 11-Aug-2016.)  Avoid
       ~ ax-13 .  (Revised by GG, 10-Jan-2024.)  (Proof shortened by Wolf
       Lammen, 25-Sep-2024.) $)
    nfnaew $p |- F/ z -. A. x x = y $=
      ( weq wal wn hbnaev nf5i ) ABDAEFCABCGH $.
  $}

  $( The setvar ` x ` is not free in ` E. x ph ` .  (Contributed by Mario
     Carneiro, 11-Aug-2016.) $)
  nfe1 $p |- F/ x E. x ph $=
    ( wex hbe1 nf5i ) ABCBABDE $.

  $( The setvar ` x ` is not free in ` A. x ph ` .  (Contributed by Mario
     Carneiro, 11-Aug-2016.) ~ df-nf changed.  (Revised by Wolf Lammen,
     11-Sep-2021.)  Remove dependency on ~ ax-12 .  (Revised by Wolf Lammen,
     12-Oct-2021.) $)
  nfa1 $p |- F/ x A. x ph $=
    ( wal wn wex alex nfe1 nfn nfxfr ) ABCADZBEZDBABFKBJBGHI $.

  $( A convenience theorem particularly designed to remove dependencies on
     ~ ax-11 in conjunction with distinctors.  (Contributed by Wolf Lammen,
     2-Sep-2018.) $)
  nfna1 $p |- F/ x -. A. x ph $=
    ( wal nfa1 nfn ) ABCBABDE $.

  $( Lemma 23 of [Monk2] p. 114.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nfia1 $p |- F/ x ( A. x ph -> A. x ps ) $=
    ( wal nfa1 nfim ) ACDBCDCACEBCEF $.

  $( The setvar ` x ` is not free in ` F/ x ph ` .  (Contributed by Mario
     Carneiro, 11-Aug-2016.)  Remove dependency on ~ ax-12 .  (Revised by Wolf
     Lammen, 12-Oct-2021.) $)
  nfnf1 $p |- F/ x F/ x ph $=
    ( wnf wex wal wi df-nf nfe1 nfa1 nfim nfxfr ) ABCABDZABEZFBABGLMBABHABIJK
    $.

  $( The analogue in our predicate calculus of axiom (5) of modal logic S5.
     See also ~ hbe1 .  (Contributed by NM, 5-Oct-2005.) $)
  modal5 $p |- ( -. A. x -. ph -> A. x -. A. x -. ph ) $=
    ( wn hbn1 ) ACBD $.

  ${
    $d x y $.
    $( The setvar ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y `
       are distinct.  (Contributed by Mario Carneiro, 11-Aug-2016.)  Shorten
       ~ nfs1v and ~ hbs1 combined.  (Revised by Wolf Lammen, 28-Jul-2022.) $)
    nfs1v $p |- F/ x [ y / x ] ph $=
      ( wsb weq wi wal sb6 nfa1 nfxfr ) ABCDBCEAFZBGBABCHKBIJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-11 (Quantifier Commutation)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantifier Commutation.  This axiom says universal quantifiers
     can be swapped.  Axiom scheme C6' in [Megill] p. 448 (p. 16 of the
     preprint).  Also appears as Lemma 12 of [Monk2] p. 109 and Axiom C5-3 of
     [Monk2] p. 113.  This axiom scheme is logically redundant (see ~ ax11w )
     but is used as an auxiliary axiom scheme to achieve metalogical
     completeness.  Use its weak version ~ alcomimw when it allows to avoid
     dependence on ~ ax-11 .  (Contributed by NM, 12-Mar-1993.) $)
  ax-11 $a |- ( A. x A. y ph -> A. y A. x ph ) $.

  ${
    alcoms.1 $e |- ( A. x A. y ph -> ps ) $.
    $( Swap quantifiers in an antecedent.  (Contributed by NM, 11-May-1993.) $)
    alcoms $p |- ( A. y A. x ph -> ps ) $=
      ( wal ax-11 syl ) ACFDFADFCFBADCGEH $.
  $}

  $( Theorem 19.5 of [Margaris] p. 89.  Use its weak version ~ alcomw when it
     allows to avoid dependence on ~ ax-11 .  (Contributed by NM,
     30-Jun-1993.) $)
  alcom $p |- ( A. x A. y ph <-> A. y A. x ph ) $=
    ( wal ax-11 impbii ) ACDBDABDCDABCEACBEF $.

  $( Theorem *11.21 in [WhiteheadRussell] p. 160.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  alrot3 $p |- ( A. x A. y A. z ph <-> A. y A. z A. x ph ) $=
    ( wal alcom albii bitri ) ADEZCEBEIBEZCEABEDEZCEIBCFJKCABDFGH $.

  $( Rotate four universal quantifiers twice.  (Contributed by NM, 2-Feb-2005.)
     (Proof shortened by Fan Zheng, 6-Jun-2016.) $)
  alrot4 $p |- ( A. x A. y A. z A. w ph <-> A. z A. w A. x A. y ph ) $=
    ( wal alrot3 albii bitri ) AEFDFCFZBFACFZEFDFZBFKBFEFDFJLBACDEGHKBDEGI $.

  $( Theorem 19.11 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.)
     Remove dependencies on ~ ax-5 , ~ ax-6 , ~ ax-7 , ~ ax-10 , ~ ax-12 .
     (Revised by Wolf Lammen, 8-Jan-2018.)  (Proof shortened by Wolf Lammen,
     22-Aug-2020.) $)
  excom $p |- ( E. x E. y ph <-> E. y E. x ph ) $=
    ( wn wal wex alcom notbii 2exnaln 3bitr4i ) ADZCEBEZDKBECEZDACFBFABFCFLMKBC
    GHABCIACBIJ $.
  $( $j usage 'excom' avoids 'ax-5' 'ax-6' 'ax-7' 'ax-10' 'ax-12' 'ax-13'; $)

  $( One direction of Theorem 19.11 of [Margaris] p. 89.  (Contributed by NM,
     5-Aug-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.)  Remove
     dependencies on ~ ax-5 , ~ ax-6 , ~ ax-7 , ~ ax-10 , ~ ax-12 .  (Revised
     by Wolf Lammen, 8-Jan-2018.) $)
  excomim $p |- ( E. x E. y ph -> E. y E. x ph ) $=
    ( wex excom biimpi ) ACDBDABDCDABCEF $.
  $( $j usage 'excomim' avoids 'ax-5' 'ax-6' 'ax-7' 'ax-10' 'ax-12' 'ax-13'; $)

  $( Swap 1st and 3rd existential quantifiers.  (Contributed by NM,
     9-Mar-1995.) $)
  excom13 $p |- ( E. x E. y E. z ph <-> E. z E. y E. x ph ) $=
    ( wex excom exbii 3bitri ) ADEZCEBEIBEZCEABEZDEZCEKCEDEIBCFJLCABDFGKCDFH $.

  $( Rotate existential quantifiers.  (Contributed by NM, 17-Mar-1995.) $)
  exrot3 $p |- ( E. x E. y E. z ph <-> E. y E. z E. x ph ) $=
    ( wex excom13 excom bitri ) ADECEBEABEZCEDEIDECEABCDFIDCGH $.

  $( Rotate existential quantifiers twice.  (Contributed by NM, 9-Mar-1995.) $)
  exrot4 $p |- ( E. x E. y E. z E. w ph <-> E. z E. w E. x E. y ph ) $=
    ( wex excom13 exbii bitri ) AEFDFCFZBFACFZDFEFZBFKBFEFDFJLBACDEGHKBEDGI $.

  ${
    hbal.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by NM, 12-Mar-1993.) $)
    hbal $p |- ( A. y ph -> A. x A. y ph ) $=
      ( wal alimi ax-11 syl ) ACEZABEZCEIBEAJCDFACBGH $.
  $}

  ${
    hbald.1 $e |- ( ph -> A. y ph ) $.
    hbald.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbal .
       (Contributed by NM, 2-Jan-2002.) $)
    hbald $p |- ( ph -> ( A. y ps -> A. x A. y ps ) ) $=
      ( wal alimdh ax-11 syl6 ) ABDGZBCGZDGKCGABLDEFHBDCIJ $.
  $}

  ${
    $d w x y $.  $d w x z $.  $d w ph $.
    $( Move universal quantifier in and out of substitution.  (Contributed by
       NM, 16-May-1993.)  (Proof shortened by Wolf Lammen, 29-Sep-2018.)
       Reduce dependencies on axioms.  (Revised by Steven Nguyen,
       13-Aug-2023.) $)
    sbal $p |- ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) $=
      ( vw weq wi wal wsb alcom 19.21v albii bitr3i imbi2i dfsb 3bitr4i ) EDFZC
      EFZAGZCHZGZBHZEHZUAEHZBHABHZCDIZACDIZBHUAEBJQRUEGZCHZGZEHQTBHZGZEHUFUCUJU
      LEUIUKQUISBHZCHUKUMUHCRABKLSCBJMNLUECEDOUBULEQTBKLPUGUDBACEDOLP $.
  $}

  ${
    $d x z $.  $d y z $.
    sbalv.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Quantify with new variable inside substitution.  (Contributed by NM,
       18-Aug-1993.) $)
    sbalv $p |- ( [ y / x ] A. z ph <-> A. z ps ) $=
      ( wal wsb sbal albii bitri ) AEGCDHACDHZEGBEGAECDILBEFJK $.
  $}

  ${
    $d x z w $.  $d y z w $.  $d ph w $.
    hbsbw.1 $e |- ( ph -> A. z ph ) $.
    $( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct.  Version of ~ hbsb with a disjoint
       variable condition, which requires fewer axioms.  (Contributed by NM,
       12-Aug-1993.)  Remove dependencies on axioms.  (Revised by GG,
       23-May-2024.)  (Proof shortened by Wolf Lammen, 14-May-2025.) $)
    hbsbw $p |- ( [ y / x ] ph -> A. z [ y / x ] ph ) $=
      ( wsb wal sbimi sbal sylib ) ABCFZADGZBCFKDGALBCEHADBCIJ $.
    $( $j usage 'hbsbw' avoids 'ax-10' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x z $.  $d u v x w $.  $d u v y z $.  $d u v ph $.
    $( Commutativity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
       27-May-1997.)  (Proof shortened by Wolf Lammen, 23-Dec-2022.) $)
    sbcom2 $p |- ( [ w / z ] [ y / x ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( vv vu weq wsb wb wi wal 2sb6 alcom ancomst sbequ sbbidv ax6ev exlimiiv
      wa 2albii 3bitri bitr4i bitr3id sylan9bb sylan9bbr bitr3d ex ) FEHZABCIZD
      EIZADEIZBCIZJZFGCHZUIUNKGUOUIUNUOUITADFIZBGIZUKUMUOUQUJDFIZUIUKUQABGIZDFI
      ZUOURUTBGHZDFHZTAKZDLBLZUQUTVBVATAKZBLDLVEDLBLVDADBFGMVEDBNVEVCBDVBVAAOUA
      UBABDGFMUCUOUSUJDFAGCBPQUDUJFEDPUEUIUQULBGIUOUMUIUPULBGAFEDPQULGCBPUFUGUH
      GCRSFERS $.
  $}

  ${
    $d v w ph $.  $d v w x $.  $d v w y $.
    $( Obsolete version of ~ sbco4lem as of 3-Sep-2025.  (Contributed by Jim
       Kingdon, 26-Sep-2018.)  (Proof shortened by Wolf Lammen, 12-Oct-2024.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sbco4lemOLD $p |- ( [ x / v ] [ y / x ] [ v / y ] ph <->
        [ x / w ] [ y / x ] [ w / y ] ph ) $=
      ( wsb sbcom2 sbbii sbco2vv 2sbbii 3bitr3i ) ACDFZDEFZBCFZEBFLBCFZDEFZEBFA
      CEFZBCFEBFODBFNPEBLDEBCGHMQEBCBACEDIJODBEIK $.
  $}

  ${
    $d t u v ph $.  $d t u v x $.  $d t u v y $.  $d w ph $.  $d w x $.
    $d w y $.  $d t w $.
    $( Obsolete version of ~ sbco4 as of 3-Sep-2025.  (Contributed by Jim
       Kingdon, 25-Sep-2018.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    sbco4OLD $p |- ( [ y / u ] [ x / v ] [ u / x ] [ v / y ] ph <->
        [ x / w ] [ y / x ] [ w / y ] ph ) $=
      ( vt wsb sbcom2 sbco2vv sbbii bitr3i sbco4lem 3bitri ) ACEHZBFHZEBHFCHZOB
      CHZEBHZACGHBCHGBHACDHBCHDBHQPFCHZEBHSPFCEBITREBOBCFJKLABCGEMABCDGMN $.
  $}

  $( Lemma 24 of [Monk2] p. 114.  (Contributed by Mario Carneiro, 24-Sep-2016.)
     Remove dependency on ~ ax-12 .  (Revised by Wolf Lammen, 18-Oct-2021.) $)
  nfa2 $p |- F/ x A. y A. x ph $=
    ( wal alcom nfa1 nfxfr ) ABDCDACDZBDBACBEHBFG $.

  ${
    nfexhe.1 $e |- ( E. x ph -> ph ) $.
    $( Version of ~ nfex with the existential dual to the 'h' hypothesis,
       avoiding ~ ax-12 .  (Contributed by SN, 11-Feb-2026.) $)
    nfexhe $p |- F/ x E. y ph $=
      ( wex hbe1 excomim eximi syl alrimih nfi ) ACEZBLBEZLBLBFMABEZCELABCGNACD
      HIJK $.
    $( $j usage 'nfexhe' avoids 'ax-12'; $)
  $}

  $( An inner universal quantifier's variable is bound.  (Contributed by SN,
     11-Feb-2026.) $)
  nfexa2 $p |- F/ x E. y A. x ph $=
    ( wal hbe1a nfexhe ) ABDBCABEF $.
  $( $j usage 'nfexa2' avoids 'ax-12'; $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-12 (Substitution)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Substitution.  One of the 5 equality axioms of predicate
     calculus.  The final consequent ` A. x ( x = y -> ph ) ` is a way of
     expressing " ` y ` substituted for ` x ` in wff ` ph ` " (cf. ~ sb6 ).  It
     is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of [Monk2] p. 105,
     from which it can be proved by cases.

     The original version of this axiom was ~ ax-c15 and was replaced with this
     shorter ~ ax-12 in Jan. 2007.  The old axiom is proved from this one as
     Theorem ~ axc15 .  Conversely, this axiom is proved from ~ ax-c15 as
     Theorem ~ ax12 .

     Juha Arpiainen proved the metalogical independence of this axiom (in the
     form of the older axiom ~ ax-c15 ) from the others on 19-Jan-2006.  See
     item 9a at ~ https://us.metamath.org/award2003.html .

     See ~ ax12v and ~ ax12v2 for other equivalents of this axiom that (unlike
     this axiom) have distinct variable restrictions.

     This axiom scheme is logically redundant (see ~ ax12w ) but is used as an
     auxiliary axiom scheme to achieve scheme completeness.  (Contributed by
     NM, 22-Jan-2007.)  (New usage is discouraged.) $)
  ax-12 $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.

  ${
    $d x y $.  $d y ph $.
    $( This is essentially Axiom ~ ax-12 weakened by additional restrictions on
       variables.  Besides ~ axc11r , this theorem should be the only one
       referencing ~ ax-12 directly.

       Both restrictions on variables have their own value.  If for a moment we
       assume ` x ` could be set to ` y ` , then, after elimination of the
       tautology ` y = y ` , immediately we have ` ph -> A. y ph ` for all
       ` ph ` and ` y ` , that is ~ ax-5 , a degenerate result.

       The second restriction is not necessary, but a simplification that makes
       the following interpretation easier to see.  Since ` ph ` textually at
       most depends on ` x ` , we can look at it at some given 'fixed' ` y ` .
       This theorem now states that the truth value of ` ph ` will stay
       constant, as long as we 'vary ` x ` around ` y ` ' only such that
       ` x = y ` still holds.  Or in other words, equality is the finest
       grained logical expression.  If you cannot differ two sets by ` = ` ,
       you won't find a whatever sophisticated expression that does.  One might
       wonder how the described variation of ` x ` is possible at all.  Note
       that Metamath is a text processor that easily sees a difference between
       text chunks ` { x | -. x = x } ` and ` { y | -. y = y } ` .  Our usual
       interpretation is to abstract from textual variations of the same set,
       but we are free to interpret Metamath's formalism differently, and in
       fact let ` x ` run through all textual representations of sets.

       Had we allowed ` ph ` to depend also on ` y ` , this idea is both harder
       to see, and it is less clear that this extra freedom introduces effects
       not covered by other axioms.  (Contributed by Wolf Lammen,
       8-Aug-2020.) $)
    ax12v $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( wal weq wi ax-5 ax-12 syl5 ) AACDBCEZJAFBDACGABCHI $.
  $}

  ${
    $d x y z $.  $d z ph $.
    $( It is possible to remove any restriction on ` ph ` in ~ ax12v .  Same as
       Axiom C8 of [Monk2] p. 105.  Use ~ ax12v instead when sufficient.
       (Contributed by NM, 5-Aug-1993.)  Remove dependencies on ~ ax-10 and
       ~ ax-13 .  (Revised by Jim Kingdon, 15-Dec-2017.)  (Proof shortened by
       Wolf Lammen, 8-Dec-2019.) $)
    ax12v2 $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( vz weq wi wal equtrr ax12v imim1d alimdv syl9r syld ax6evr exlimiiv ) C
      DEZBCEZAQAFZBGZFZFDPQBDEZTCDBHZUAAUAAFZBGPSABDIPUCRBPQUAAUBJKLMDCNO $.
    $( $j usage 'ax12v2' avoids 'ax-10' 'ax-11' 'ax-13'; $)
  $}

  ${
    $d x y $.
    $( Version of ~ ax12v2 rewritten to use an existential quantifier.  One
       direction of ~ sbalex without the universal quantifier, avoiding
       ~ ax-10 .  (Contributed by SN, 14-Aug-2025.) $)
    ax12ev2 $p |- ( E. x ( x = y /\ ph ) -> ( x = y -> ph ) ) $=
      ( weq wa wex wn wi wal exnalimn ax12v2 con1d biimtrid com12 ) BCDZOAEBFZA
      POAGZHBIZGOAOABJOARQBCKLMN $.
    $( $j usage 'ax12ev2' avoids 'ax-10' 'ax-11' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d y ph $.
    $( If a wff is true, it is true for at least one instance.  Special case of
       Theorem 19.8 of [Margaris] p. 89.  See ~ 19.8v for a version with a
       disjoint variable condition requiring fewer axioms.  (Contributed by NM,
       9-Jan-1993.)  Allow a shortening of ~ sp .  (Revised by Wolf Lammen,
       13-Jan-2018.)  (Proof shortened by Wolf Lammen, 8-Dec-2019.) $)
    19.8a $p |- ( ph -> E. x ph ) $=
      ( vy weq wex wi wal ax12v alequexv syl6 ax6evr exlimiiv ) BCDZAABEZFCMAMA
      FBGNABCHABCIJCBKL $.
  $}

  ${
    19.8ad.1 $e |- ( ph -> ps ) $.
    $( If a wff is true, it is true for at least one instance.  Deduction form
       of ~ 19.8a .  (Contributed by DAW, 13-Feb-2017.) $)
    19.8ad $p |- ( ph -> E. x ps ) $=
      ( wex 19.8a syl ) ABBCEDBCFG $.
  $}

  $( Specialization.  A universally quantified wff implies the wff without a
     quantifier.  Axiom scheme B5 of [Tarski] p. 67 (under his system S2,
     defined in the last paragraph on p. 77).  Also appears as Axiom scheme C5'
     in [Megill] p. 448 (p. 16 of the preprint).  This corresponds to the axiom
     (T) of modal logic.

     For the axiom of specialization presented in many logic textbooks, see
     Theorem ~ stdpc4 .

     This theorem shows that our obsolete axiom ~ ax-c5 can be derived from the
     others.  The proof uses ideas from the proof of Lemma 21 of [Monk2]
     p. 114.

     It appears that this scheme cannot be derived directly from Tarski's
     axioms without auxiliary axiom scheme ~ ax-12 .  It is thought the best we
     can do using only Tarski's axioms is ~ spw .  Also see ~ spvw where ` x `
     and ` ph ` are disjoint, using fewer axioms.  (Contributed by NM,
     21-May-2008.)  (Proof shortened by Scott Fenton, 24-Jan-2011.)  (Proof
     shortened by Wolf Lammen, 13-Jan-2018.) $)
  sp $p |- ( A. x ph -> ph ) $=
    ( wal wn wex alex 19.8a con1i sylbi ) ABCADZBEZDAABFAKJBGHI $.

  ${
    spi.1 $e |- A. x ph $.
    $( Inference rule of universal instantiation, or universal specialization.
       Converse of the inference rule of (universal) generalization ~ ax-gen .
       Contrary to the rule of generalization, its closed form is valid, see
       ~ sp .  (Contributed by NM, 5-Aug-1993.) $)
    spi $p |- ph $=
      ( wal sp ax-mp ) ABDACABEF $.
  $}

  ${
    sps.1 $e |- ( ph -> ps ) $.
    $( Generalization of antecedent.  (Contributed by NM, 5-Jan-1993.) $)
    sps $p |- ( A. x ph -> ps ) $=
      ( wal sp syl ) ACEABACFDG $.
  $}

  $( A double specialization (see ~ sp ).  Another double specialization,
     closer to PM*11.1, is ~ 2stdpc4 .  (Contributed by BJ, 15-Sep-2018.) $)
  2sp $p |- ( A. x A. y ph -> ph ) $=
    ( wal sp sps ) ACDABACEF $.

  ${
    spsd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction generalizing antecedent.  (Contributed by NM, 17-Aug-1994.) $)
    spsd $p |- ( ph -> ( A. x ps -> ch ) ) $=
      ( wal sp syl5 ) BDFBACBDGEH $.
  $}

  $( Theorem 19.2 of [Margaris] p. 89, generalized to use two setvar variables.
     Use ~ 19.2 when sufficient.  (Contributed by Mel L. O'Cat,
     31-Mar-2008.) $)
  19.2g $p |- ( A. x ph -> E. y ph ) $=
    ( wex 19.8a sps ) AACDBACEF $.

  ${
    19.21bi.1 $e |- ( ph -> A. x ps ) $.
    $( Inference form of ~ 19.21 and also deduction form of ~ sp .
       (Contributed by NM, 26-May-1993.) $)
    19.21bi $p |- ( ph -> ps ) $=
      ( wal sp syl ) ABCEBDBCFG $.
  $}

  ${
    19.21bbi.1 $e |- ( ph -> A. x A. y ps ) $.
    $( Inference removing two universal quantifiers.  Version of ~ 19.21bi with
       two quantifiers.  (Contributed by NM, 20-Apr-1994.) $)
    19.21bbi $p |- ( ph -> ps ) $=
      ( wal 19.21bi ) ABDABDFCEGG $.
  $}

  ${
    19.23bi.1 $e |- ( E. x ph -> ps ) $.
    $( Inference form of Theorem 19.23 of [Margaris] p. 90, see ~ 19.23 .
       (Contributed by NM, 12-Mar-1993.) $)
    19.23bi $p |- ( ph -> ps ) $=
      ( wex 19.8a syl ) AACEBACFDG $.
  $}

  ${
    nexr.1 $e |- -. E. x ph $.
    $( Inference associated with the contrapositive of ~ 19.8a .  (Contributed
       by Jeff Hankins, 26-Jul-2009.) $)
    nexr $p |- -. ph $=
      ( wex 19.8a mto ) AABDCABEF $.
  $}

  $( Quantified excluded middle (see ~ exmid ).  Also known as the drinker
     paradox (if ` ph ( x ) ` is interpreted as " ` x ` drinks", then this
     theorem tells that there exists a person such that, if this person drinks,
     then everyone drinks).  Exercise 9.2a of Boolos, p. 111, _Computability
     and Logic_.  (Contributed by NM, 10-Dec-2000.) $)
  qexmid $p |- E. x ( ph -> A. x ph ) $=
    ( wal 19.8a 19.35ri ) AABCZBFBDE $.

  $( Consequence of the definition of not-free.  (Contributed by Mario
     Carneiro, 26-Sep-2016.) ~ df-nf changed.  (Revised by Wolf Lammen,
     11-Sep-2021.)  (Proof shortened by Wolf Lammen, 23-Nov-2023.) $)
  nf5r $p |- ( F/ x ph -> ( ph -> A. x ph ) ) $=
    ( wex wnf wal 19.8a id nfrd syl5 ) AABCABDZABEABFJABJGHI $.

  ${
    nf5ri.1 $e |- F/ x ph $.
    $( Consequence of the definition of not-free.  (Contributed by Mario
       Carneiro, 11-Aug-2016.)  (Proof shortened by Wolf Lammen,
       15-Mar-2023.) $)
    nf5ri $p |- ( ph -> A. x ph ) $=
      ( wal nfri 19.23bi ) AABDBABCEF $.
  $}

  ${
    nf5rd.1 $e |- ( ph -> F/ x ps ) $.
    $( Consequence of the definition of not-free in a context.  (Contributed by
       Mario Carneiro, 11-Aug-2016.) $)
    nf5rd $p |- ( ph -> ( ps -> A. x ps ) ) $=
      ( wnf wal wi nf5r syl ) ABCEBBCFGDBCHI $.
  $}

  ${
    $d x y $.
    spimedv.1 $e |- ( ch -> F/ x ph ) $.
    spimedv.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Deduction version of ~ spimev .  Version of ~ spimed with a disjoint
       variable condition, which does not require ~ ax-13 .  See ~ spime for a
       non-deduction version.  (Contributed by NM, 14-May-1993.)  (Revised by
       BJ, 31-May-2019.) $)
    spimedv $p |- ( ch -> ( ph -> E. x ps ) ) $=
      ( wal wex nf5rd weq wi ax6ev eximii 19.35i syl6 ) CAADHBDICADFJABDDEKABLD
      DEMGNOP $.
  $}

  ${
    $d x y $.
    spimefv.1 $e |- F/ x ph $.
    spimefv.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Version of ~ spime with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 31-May-2019.) $)
    spimefv $p |- ( ph -> E. x ps ) $=
      ( wex wi wtru wnf a1i spimedv mptru ) ABCGHABICDACJIEKFLM $.
  $}

  ${
    nfim1.1 $e |- F/ x ph $.
    nfim1.2 $e |- ( ph -> F/ x ps ) $.
    $( A closed form of ~ nfim .  (Contributed by NM, 2-Jun-1993.)  (Revised by
       Mario Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf Lammen,
       2-Jan-2018.) ~ df-nf changed.  (Revised by Wolf Lammen, 18-Sep-2021.) $)
    nfim1 $p |- F/ x ( ph -> ps ) $=
      ( wal wn wo wi wnf nf3 mpbi nftht sps nfimd pm2.21 alimi syl jaoi ax-mp )
      ACFZAGZCFZHZABIZCJZACJUDDACKLUAUFUCUAABCACMABCJCENOUCUECFUFUBUECABPQUECMR
      ST $.

    $( A closed form of ~ nfan .  (Contributed by Mario Carneiro, 3-Oct-2016.)
       ~ df-nf changed.  (Revised by Wolf Lammen, 18-Sep-2021.)  (Proof
       shortened by Wolf Lammen, 7-Jul-2022.) $)
    nfan1 $p |- F/ x ( ph /\ ps ) $=
      ( wa wn wi df-an nfnd nfim1 nfn nfxfr ) ABFABGZHZGCABIOCANCDABCEJKLM $.
  $}

  $( Closed form of ~ 19.3 and version of ~ 19.9t with a universal quantifier.
     (Contributed by NM, 9-Nov-2020.)  (Proof shortened by BJ, 9-Oct-2022.) $)
  19.3t $p |- ( F/ x ph -> ( A. x ph <-> ph ) ) $=
    ( wnf wal sp nf5r impbid2 ) ABCABDAABEABFG $.

  ${
    19.3.1 $e |- F/ x ph $.
    $( A wff may be quantified with a variable not free in it.  Version of
       ~ 19.9 with a universal quantifier.  Theorem 19.3 of [Margaris] p. 89.
       See ~ 19.3v for a version requiring fewer axioms.  (Contributed by NM,
       12-Mar-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.3 $p |- ( A. x ph <-> ph ) $=
      ( wal sp nf5ri impbii ) ABDAABEABCFG $.
  $}

  ${
    19.9d.1 $e |- ( ps -> F/ x ph ) $.
    $( A deduction version of one direction of ~ 19.9 .  (Contributed by NM,
       14-May-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.)  Revised to
       shorten other proofs.  (Revised by Wolf Lammen, 14-Jul-2020.) ~ df-nf
       changed.  (Revised by Wolf Lammen, 11-Sep-2021.)  (Proof shortened by
       Wolf Lammen, 8-Jul-2022.) $)
    19.9d $p |- ( ps -> ( E. x ph -> ph ) ) $=
      ( wex wal nfrd sp syl6 ) BACEACFABACDGACHI $.
  $}

  $( Closed form of ~ 19.9 and version of ~ 19.3t with an existential
     quantifier.  (Contributed by NM, 13-May-1993.)  (Revised by Mario
     Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf Lammen, 14-Jul-2020.) $)
  19.9t $p |- ( F/ x ph -> ( E. x ph <-> ph ) ) $=
    ( wnf wex id 19.9d 19.8a impbid1 ) ABCZABDAAIBIEFABGH $.

  ${
    19.9.1 $e |- F/ x ph $.
    $( A wff may be existentially quantified with a variable not free in it.
       Version of ~ 19.3 with an existential quantifier.  Theorem 19.9 of
       [Margaris] p. 89.  See ~ 19.9v for a version requiring fewer axioms.
       (Contributed by FL, 24-Mar-2007.)  (Revised by Mario Carneiro,
       24-Sep-2016.)  (Proof shortened by Wolf Lammen, 30-Dec-2017.)  Revised
       to shorten other proofs.  (Revised by Wolf Lammen, 14-Jul-2020.) $)
    19.9 $p |- ( E. x ph <-> ph ) $=
      ( wnf wex wb 19.9t ax-mp ) ABDABEAFCABGH $.
  $}

  $( Closed form of Theorem 19.21 of [Margaris] p. 90, see ~ 19.21 .
     (Contributed by NM, 27-May-1997.)  (Revised by Mario Carneiro,
     24-Sep-2016.)  (Proof shortened by Wolf Lammen, 3-Jan-2018.) ~ df-nf
     changed.  (Revised by Wolf Lammen, 11-Sep-2021.)  (Proof shortened by BJ,
     3-Nov-2021.) $)
  19.21t $p |- ( F/ x ph -> ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) ) $=
    ( wnf wex wal wi 19.38a 19.9t imbi1d bitr3d ) ACDZACEZBCFZGABGCFANGABCHLMAN
    ACIJK $.

  ${
    19.21.1 $e |- F/ x ph $.
    $( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ".  See ~ 19.21v for a version
       requiring fewer axioms.  See also ~ 19.21h .  (Contributed by NM,
       14-May-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.) ~ df-nf
       changed.  (Revised by Wolf Lammen, 18-Sep-2021.) $)
    19.21 $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( wnf wi wal wb 19.21t ax-mp ) ACEABFCGABCGFHDABCIJ $.
  $}

  ${
    stdpc5.1 $e |- F/ x ph $.
    $( An axiom scheme of standard predicate calculus that emulates Axiom 5 of
       [Mendelson] p. 69.  The hypothesis ` F/ x ph ` can be thought of as
       emulating " ` x ` is not free in ` ph ` ".  With this definition, the
       meaning of "not free" is less restrictive than the usual textbook
       definition; for example ` x ` would not (for us) be free in ` x = x ` by
       ~ nfequid .  This theorem scheme can be proved as a metatheorem of
       Mendelson's axiom system, even though it is slightly stronger than his
       Axiom 5.  See ~ stdpc5v for a version requiring fewer axioms.
       (Contributed by NM, 22-Sep-1993.)  (Revised by Mario Carneiro,
       12-Oct-2016.)  (Proof shortened by Wolf Lammen, 1-Jan-2018.)  Remove
       dependency on ~ ax-10 .  (Revised by Wolf Lammen, 4-Jul-2021.)  (Proof
       shortened by Wolf Lammen, 11-Oct-2021.) $)
    stdpc5 $p |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) $=
      ( wi wal 19.21 biimpi ) ABECFABCFEABCDGH $.
  $}

  ${
    19.21-2.1 $e |- F/ x ph $.
    19.21-2.2 $e |- F/ y ph $.
    $( Version of ~ 19.21 with two quantifiers.  (Contributed by NM,
       4-Feb-2005.) $)
    19.21-2 $p |- ( A. x A. y ( ph -> ps ) <-> ( ph -> A. x A. y ps ) ) $=
      ( wi wal 19.21 albii bitri ) ABGDHZCHABDHZGZCHAMCHGLNCABDFIJAMCEIK $.
  $}

  $( Closed form of Theorem 19.23 of [Margaris] p. 90.  See ~ 19.23 .
     (Contributed by NM, 7-Nov-2005.)  (Proof shortened by Wolf Lammen,
     13-Aug-2020.) ~ df-nf changed.  (Revised by Wolf Lammen, 11-Sep-2021.)
     (Proof shortened by BJ, 8-Oct-2022.) $)
  19.23t $p |- ( F/ x ps -> ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $=
    ( wnf wex wal wi 19.38b 19.3t imbi2d bitr3d ) BCDZACEZBCFZGABGCFMBGABCHLNBM
    BCIJK $.

  ${
    19.23.1 $e |- F/ x ps $.
    $( Theorem 19.23 of [Margaris] p. 90.  See ~ 19.23v for a version requiring
       fewer axioms.  (Contributed by NM, 24-Jan-1993.)  (Revised by Mario
       Carneiro, 24-Sep-2016.) $)
    19.23 $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( wnf wi wal wex wb 19.23t ax-mp ) BCEABFCGACHBFIDABCJK $.
  $}

  ${
    alimd.1 $e |- F/ x ph $.
    alimd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.20 of [Margaris] p. 90, see ~ alim .  See
       ~ alimdh , ~ alimdv for variants requiring fewer axioms.  (Contributed
       by Mario Carneiro, 24-Sep-2016.) $)
    alimd $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      ( nf5ri alimdh ) ABCDADEGFH $.
  $}

  ${
    alrimi.1 $e |- F/ x ph $.
    alrimi.2 $e |- ( ph -> ps ) $.
    $( Inference form of Theorem 19.21 of [Margaris] p. 90, see ~ 19.21 .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    alrimi $p |- ( ph -> A. x ps ) $=
      ( nf5ri alrimih ) ABCACDFEG $.
  $}

  ${
    alrimdd.1 $e |- F/ x ph $.
    alrimdd.2 $e |- ( ph -> F/ x ps ) $.
    alrimdd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.21 of [Margaris] p. 90, see ~ 19.21 .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    alrimdd $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( wal nf5rd alimd syld ) ABBDHCDHABDFIABCDEGJK $.
  $}

  ${
    alrimd.1 $e |- F/ x ph $.
    alrimd.2 $e |- F/ x ps $.
    alrimd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.21 of [Margaris] p. 90, see ~ 19.21 .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    alrimd $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( wnf a1i alrimdd ) ABCDEBDHAFIGJ $.
  $}

  ${
    eximd.1 $e |- F/ x ph $.
    eximd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.22 of [Margaris] p. 90, see ~ exim .
       (Contributed by NM, 29-Jun-1993.)  (Revised by Mario Carneiro,
       24-Sep-2016.) $)
    eximd $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( nf5ri eximdh ) ABCDADEGFH $.
  $}

  ${
    exlimi.1 $e |- F/ x ps $.
    exlimi.2 $e |- ( ph -> ps ) $.
    $( Inference associated with ~ 19.23 .  See ~ exlimiv for a version with a
       disjoint variable condition requiring fewer axioms.  (Contributed by NM,
       10-Jan-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)
    exlimi $p |- ( E. x ph -> ps ) $=
      ( wi wex 19.23 mpgbi ) ABFACGBFCABCDHEI $.
  $}

  ${
    exlimd.1 $e |- F/ x ph $.
    exlimd.2 $e |- F/ x ch $.
    exlimd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.9 of [Margaris] p. 89.  (Contributed by NM,
       23-Jan-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.)  (Proof
       shortened by Wolf Lammen, 12-Jan-2018.) $)
    exlimd $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( wex eximd 19.9 imbitrdi ) ABDHCDHCABCDEGICDFJK $.
  $}

  ${
    exlimdd.1 $e |- F/ x ph $.
    exlimdd.2 $e |- F/ x ch $.
    exlimdd.3 $e |- ( ph -> E. x ps ) $.
    ${
      exlimimdd.4 $e |- ( ph -> ( ps -> ch ) ) $.
      $( Existential elimination rule of natural deduction.  (Contributed by
         ML, 17-Jul-2020.)  Shorten ~ exlimdd .  (Revised by Wolf Lammen,
         3-Sep-2023.) $)
      exlimimdd $p |- ( ph -> ch ) $=
        ( wex exlimd mpd ) ABDICGABCDEFHJK $.
    $}

    ${
      exlimdd.4 $e |- ( ( ph /\ ps ) -> ch ) $.
      $( Existential elimination rule of natural deduction.  (Contributed by
         Mario Carneiro, 9-Feb-2017.)  (Proof shortened by Wolf Lammen,
         3-Sep-2023.) $)
      exlimdd $p |- ( ph -> ch ) $=
        ( ex exlimimdd ) ABCDEFGABCHIJ $.
    $}
  $}

  ${
    nexd.1 $e |- F/ x ph $.
    nexd.2 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
    nexd $p |- ( ph -> -. E. x ps ) $=
      ( nf5ri nexdh ) ABCACDFEG $.
  $}

  ${
    albid.1 $e |- F/ x ph $.
    albid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction form).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    albid $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( nf5ri albidh ) ABCDADEGFH $.

    $( Formula-building rule for existential quantifier (deduction form).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    exbid $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( nf5ri exbidh ) ABCDADEGFH $.

    $( An equality theorem for effectively not free.  (Contributed by Mario
       Carneiro, 4-Oct-2016.) ~ df-nf changed.  (Revised by Wolf Lammen,
       18-Sep-2021.) $)
    nfbidf $p |- ( ph -> ( F/ x ps <-> F/ x ch ) ) $=
      ( wex wal wi wnf exbid albid imbi12d df-nf 3bitr4g ) ABDGZBDHZICDGZCDHZIB
      DJCDJAPRQSABCDEFKABCDEFLMBDNCDNO $.
  $}

  ${
    19.16.1 $e |- F/ x ph $.
    $( Theorem 19.16 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
    19.16 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> A. x ps ) ) $=
      ( wal wb 19.3 albi bitr3id ) AACEABFCEBCEACDGABCHI $.
  $}

  ${
    19.17.1 $e |- F/ x ps $.
    $( Theorem 19.17 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
    19.17 $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> ps ) ) $=
      ( wb wal albi 19.3 bitrdi ) ABECFACFBCFBABCGBCDHI $.
  $}

  ${
    19.27.1 $e |- F/ x ps $.
    $( Theorem 19.27 of [Margaris] p. 90.  See ~ 19.27v for a version requiring
       fewer axioms.  (Contributed by NM, 21-Jun-1993.) $)
    19.27 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      ( wa wal 19.26 19.3 anbi2i bitri ) ABECFACFZBCFZEKBEABCGLBKBCDHIJ $.
  $}

  ${
    19.28.1 $e |- F/ x ph $.
    $( Theorem 19.28 of [Margaris] p. 90.  See ~ 19.28v for a version requiring
       fewer axioms.  (Contributed by NM, 1-Aug-1993.)  (Proof shortened by
       Wolf Lammen, 7-May-2025.) $)
    19.28 $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      ( wa wal 19.26 19.3 bianbi ) ABECFACFBCFAABCGACDHI $.
  $}

  ${
    19.19.1 $e |- F/ x ph $.
    $( Theorem 19.19 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
    19.19 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> E. x ps ) ) $=
      ( wex wb wal 19.9 exbi bitr3id ) AACEABFCGBCEACDHABCIJ $.
  $}

  ${
    19.36.1 $e |- F/ x ps $.
    $( Theorem 19.36 of [Margaris] p. 90.  See ~ 19.36v for a version requiring
       fewer axioms.  (Contributed by NM, 24-Jun-1993.) $)
    19.36 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $=
      ( wi wex wal 19.35 19.9 imbi2i bitri ) ABECFACGZBCFZELBEABCHMBLBCDIJK $.

    19.36i.2 $e |- E. x ( ph -> ps ) $.
    $( Inference associated with ~ 19.36 .  See ~ 19.36iv for a version
       requiring fewer axioms.  (Contributed by NM, 24-Jun-1993.) $)
    19.36i $p |- ( A. x ph -> ps ) $=
      ( wi wex wal 19.36 mpbi ) ABFCGACHBFEABCDIJ $.
  $}

  ${
    19.37.1 $e |- F/ x ph $.
    $( Theorem 19.37 of [Margaris] p. 90.  See ~ 19.37v for a version requiring
       fewer axioms.  (Contributed by NM, 21-Jun-1993.) $)
    19.37 $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $=
      ( wi wex wal 19.35 19.3 imbi1i bitri ) ABECFACGZBCFZEAMEABCHLAMACDIJK $.
  $}

  ${
    19.32.1 $e |- F/ x ph $.
    $( Theorem 19.32 of [Margaris] p. 90.  See ~ 19.32v for a version requiring
       fewer axioms.  (Contributed by NM, 14-May-1993.)  (Revised by Mario
       Carneiro, 24-Sep-2016.) $)
    19.32 $p |- ( A. x ( ph \/ ps ) <-> ( ph \/ A. x ps ) ) $=
      ( wn wi wal wo nfn 19.21 df-or albii 3bitr4i ) AEZBFZCGNBCGZFABHZCGAPHNBC
      ACDIJQOCABKLAPKM $.
  $}

  ${
    19.31.1 $e |- F/ x ps $.
    $( Theorem 19.31 of [Margaris] p. 90.  See ~ 19.31v for a version requiring
       fewer axioms.  (Contributed by NM, 14-May-1993.) $)
    19.31 $p |- ( A. x ( ph \/ ps ) <-> ( A. x ph \/ ps ) ) $=
      ( wo wal 19.32 orcom albii 3bitr4i ) BAEZCFBACFZEABEZCFLBEBACDGMKCABHILBH
      J $.
  $}

  ${
    19.41.1 $e |- F/ x ps $.
    $( Theorem 19.41 of [Margaris] p. 90.  See ~ 19.41v for a version requiring
       fewer axioms.  (Contributed by NM, 14-May-1993.)  (Proof shortened by
       Andrew Salmon, 25-May-2011.)  (Proof shortened by Wolf Lammen,
       12-Jan-2018.) $)
    19.41 $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( wa wex 19.40 19.9 anbi2i sylib pm3.21 eximd impcom impbii ) ABEZCFZACFZ
      BEZPQBCFZERABCGSBQBCDHIJBQPBAOCDBAKLMN $.
  $}

  ${
    19.42.1 $e |- F/ x ph $.
    $( Theorem 19.42 of [Margaris] p. 90.  See ~ 19.42v for a version requiring
       fewer axioms.  See ~ exan for an immediate version.  (Contributed by NM,
       18-Aug-1993.) $)
    19.42 $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      ( wa wex 19.41 exancom ancom 3bitr4i ) BAECFBCFZAEABECFAKEBACDGABCHAKIJ
      $.
  $}

  ${
    19.44.1 $e |- F/ x ps $.
    $( Theorem 19.44 of [Margaris] p. 90.  See ~ 19.44v for a version requiring
       fewer axioms.  (Contributed by NM, 12-Mar-1993.) $)
    19.44 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ ps ) ) $=
      ( wo wex 19.43 19.9 orbi2i bitri ) ABECFACFZBCFZEKBEABCGLBKBCDHIJ $.
  $}

  ${
    19.45.1 $e |- F/ x ph $.
    $( Theorem 19.45 of [Margaris] p. 90.  See ~ 19.45v for a version requiring
       fewer axioms.  (Contributed by NM, 12-Mar-1993.) $)
    19.45 $p |- ( E. x ( ph \/ ps ) <-> ( ph \/ E. x ps ) ) $=
      ( wo wex 19.43 19.9 orbi1i bitri ) ABECFACFZBCFZEALEABCGKALACDHIJ $.
  $}

  ${
    $d x y $.
    spimfv.nf $e |- F/ x ps $.
    spimfv.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, using implicit substitution.  Version of ~ spim with a
       disjoint variable condition, which does not require ~ ax-13 .  See
       ~ spimvw for a version with two disjoint variable conditions, requiring
       fewer axioms, and ~ spimv for another variant.  (Contributed by NM,
       10-Jan-1993.)  (Revised by BJ, 31-May-2019.) $)
    spimfv $p |- ( A. x ph -> ps ) $=
      ( weq wi ax6ev eximii 19.36i ) ABCECDGABHCCDIFJK $.
  $}

  ${
    $d x y $.
    chvarfv.nf $e |- F/ x ps $.
    chvarfv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chvarfv.2 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  Version of
       ~ chvar with a disjoint variable condition, which does not require
       ~ ax-13 .  (Contributed by Raph Levien, 9-Jul-2003.)  (Revised by BJ,
       31-May-2019.) $)
    chvarfv $p |- ps $=
      ( weq biimpd spimfv mpg ) ABCABCDECDHABFIJGK $.
  $}

  ${
    $d x y $.  $d y ph $.
    cbv3v2.nf $e |- F/ x ps $.
    cbv3v2.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Version of ~ cbv3 with two disjoint variable conditions, which does not
       require ~ ax-11 nor ~ ax-13 .  (Contributed by BJ, 24-Jun-2019.)  (Proof
       shortened by Wolf Lammen, 30-Aug-2021.) $)
    cbv3v2 $p |- ( A. x ph -> A. y ps ) $=
      ( wal spimfv alrimiv ) ACGBDABCDEFHI $.
  $}

  ${
    $d x t $.
    $( Equivalence of two ways to express proper substitution of a setvar for
       another setvar disjoint from it in a formula.  This proof of their
       equivalence does not use ~ df-sb .

       That both sides of the biconditional express proper substitution is
       proved by ~ sb5 and ~ sb6 .  The implication "to the left" is ~ equs4v
       and does not require ~ ax-10 nor ~ ax-12 .  It also holds without
       disjoint variable condition if we allow more axioms (see ~ equs4 ).
       Theorem 6.2 of [Quine] p. 40.  Theorem ~ equs5 replaces the disjoint
       variable condition with a distinctor antecedent.  Theorem ~ equs45f
       replaces the disjoint variable condition on ` x , t ` with the
       nonfreeness hypothesis of ` t ` in ` ph ` .  (Contributed by NM,
       14-Apr-2008.)  Revised to use ~ equsexv in place of ~ equsex in order to
       remove dependency on ~ ax-13 .  (Revised by BJ, 20-Dec-2020.)  Revise to
       remove dependency on ~ df-sb .  (Revised by BJ, 21-Sep-2024.)  (Proof
       shortened by SN, 14-Aug-2025.) $)
    sbalex $p |- ( E. x ( x = t /\ ph ) <-> A. x ( x = t -> ph ) ) $=
      ( weq wa wex wi wal nfe1 ax12ev2 alrimi equs4v impbii ) BCDZAEZBFZNAGZBHP
      QBOBIABCJKABCLM $.
    $( $j usage 'sbalex' avoids 'ax-11' 'df-sb' 'ax-13'; $)

    $( Obsolete version of ~ sbalex as of 14-Aug-2025.  (Contributed by NM,
       14-Apr-2008.)  (Revised by BJ, 20-Dec-2020.)  (Revised by BJ,
       21-Sep-2024.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    sbalexOLD $p |- ( E. x ( x = t /\ ph ) <-> A. x ( x = t -> ph ) ) $=
      ( weq wa wex wi wal nfa1 ax12v2 imp exlimi equs4v impbii ) BCDZAEZBFOAGZB
      HZPRBQBIOARABCJKLABCMN $.
  $}

  ${
    $d x t $.
    $( Version of ~ sb4a with a disjoint variable condition, which does not
       require ~ ax-13 .  The distinctor antecedent from ~ sb4b is replaced by
       a disjoint variable condition in this theorem.  (Contributed by NM,
       2-Feb-2007.)  (Revised by BJ, 15-Dec-2023.) $)
    sb4av $p |- ( [ t / x ] A. t ph -> A. x ( x = t -> ph ) ) $=
      ( wal wsb weq wi sp sbimi sb6 sylib ) ACDZBCEABCEBCFAGBDLABCACHIABCJK $.
  $}

  ${
    sbimd.1 $e |- F/ x ph $.
    sbimd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction substituting both sides of an implication.  (Contributed by
       Wolf Lammen, 24-Nov-2022.)  Revise ~ df-sb .  (Revised by Steven Nguyen,
       9-Jul-2023.) $)
    sbimd $p |- ( ph -> ( [ y / x ] ps -> [ y / x ] ch ) ) $=
      ( wi wal wsb alrimi spsbim syl ) ABCHZDIBDEJCDEJHANDFGKBCDELM $.
  $}

  ${
    sbbid.1 $e |- F/ x ph $.
    sbbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction substituting both sides of a biconditional.  (Contributed by
       NM, 30-Jun-1993.)  Remove dependency on ~ ax-10 and ~ ax-13 .  (Revised
       by Wolf Lammen, 24-Nov-2022.)  Revise ~ df-sb .  (Revised by Steven
       Nguyen, 11-Jul-2023.) $)
    sbbid $p |- ( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) ) $=
      ( wb wal wsb alrimi spsbbi syl ) ABCHZDIBDEJCDEJHANDFGKBCDELM $.

    2sbbid.1 $e |- F/ y ph $.
    $( Deduction doubly substituting both sides of a biconditional.
       (Contributed by AV, 30-Jul-2023.) $)
    2sbbid $p |- ( ph -> ( [ t / x ] [ u / y ] ps
                       <-> [ t / x ] [ u / y ] ch ) ) $=
      ( wsb sbbid ) ABEFKCEFKDGHABCEFJILL $.
  $}

  ${
    $d y x $.  $d y t $.  $d y ph $.
    $( An equality theorem for substitution.  (Contributed by NM, 16-May-1993.)
       Revise ~ df-sb .  (Revised by BJ, 22-Dec-2020.) $)
    sbequ1 $p |- ( x = t -> ( ph -> [ t / x ] ph ) ) $=
      ( vy weq wi wal wsb equeucl ax12v syl6 com23 alrimdv dfsb imbitrrdi ) BCE
      ZADCEZBDEZAFBGZFZDGABCHPATDPQASPQRASFBDCIABDJKLMABDCNO $.
  $}

  ${
    $d y x $.  $d y t $.  $d y ph $.
    $( An equality theorem for substitution.  (Contributed by NM, 16-May-1993.)
       Revise ~ df-sb .  (Revised by BJ, 22-Dec-2020.)  (Proof shortened by
       Wolf Lammen, 3-Feb-2024.) $)
    sbequ2 $p |- ( x = t -> ( [ t / x ] ph -> ph ) ) $=
      ( vy wsb weq wex wi wa dfsbimp equvinva equcomi sp imim12i impcomd syl2im
      wal aleximi ax5e syl6com ) ABCEZBCFZADGZAUADCFZBDFZAHZBQZHZDQUBUECDFZIZDG
      UCABDCJBCDKUHUJADUHUIUEAUIUDUGUFCDLUFBMNORPADST $.
  $}

  $( One of the two equality axioms of standard predicate calculus, called
     substitutivity of equality.  (The other one is ~ stdpc6 .)  Translated to
     traditional notation, it can be read:
      " ` x = y -> ( ph ( x , x ) -> ph ( x , y ) ) ` , provided that ` y ` is
     free for ` x ` in ` ph ( x , x ) ` ".  Axiom 7 of [Mendelson] p. 95.
     (Contributed by NM, 15-Feb-2005.) $)
  stdpc7 $p |- ( x = y -> ( [ x / y ] ph -> ph ) ) $=
    ( wsb wi sbequ2 equcoms ) ACBDAECBACBFG $.

  $( An equality theorem for substitution.  (Contributed by NM,
     14-May-1993.) $)
  sbequ12 $p |- ( x = y -> ( ph <-> [ y / x ] ph ) ) $=
    ( weq wsb sbequ1 sbequ2 impbid ) BCDAABCEABCFABCGH $.

  $( An equality theorem for substitution.  (Contributed by NM, 6-Oct-2004.)
     (Proof shortened by Andrew Salmon, 21-Jun-2011.) $)
  sbequ12r $p |- ( x = y -> ( [ x / y ] ph <-> ph ) ) $=
    ( wsb wb weq sbequ12 bicomd equcoms ) ACBDZAECBCBFAJACBGHI $.

  ${
    $d x y $.  $d x ph $.
    $( Elimination of substitution.  Also see ~ sbel2x .  (Contributed by NM,
       5-Aug-1993.)  Avoid ~ ax-13 .  (Revised by Wolf Lammen, 6-Aug-2023.)
       Avoid ~ ax-10 .  (Revised by GG, 20-Aug-2023.) $)
    sbelx $p |- ( ph <-> E. x ( x = y /\ [ x / y ] ph ) ) $=
      ( weq wsb wa wex sbequ12r equsexvw bicomi ) BCDACBEZFBGAKABCABCHIJ $.
    $( $j usage 'sbelx' avoids 'ax-10' 'ax-11' 'ax-13'; $)
  $}

  $( An equality theorem for substitution.  (Contributed by NM, 2-Jun-1993.)
     (Proof shortened by Wolf Lammen, 23-Jun-2019.) $)
  sbequ12a $p |- ( x = y -> ( [ y / x ] ph <-> [ x / y ] ph ) ) $=
    ( weq wsb sbequ12r sbequ12 bitr2d ) BCDACBEAABCEABCFABCGH $.

  $( An identity theorem for substitution.  Remark 9.1 in [Megill] p. 447 (p.
     15 of the preprint).  (Contributed by NM, 26-May-1993.)  (Proof shortened
     by Wolf Lammen, 30-Sep-2018.) $)
  sbid $p |- ( [ x / x ] ph <-> ph ) $=
    ( weq wsb wb equid sbequ12r ax-mp ) BBCABBDAEBFABBGH $.

  ${
    $d x y $.
    $( A composition law for substitution.  Version of ~ sbco with a disjoint
       variable condition using fewer axioms.  (Contributed by NM,
       14-May-1993.)  (Revised by GG, 7-Aug-2023.)  (Proof shortened by SN,
       26-Aug-2025.) $)
    sbcov $p |- ( [ y / x ] [ x / y ] ph <-> [ y / x ] ph ) $=
      ( wsb sbequ12r sbbiiev ) ACBDABCABCEF $.
    $( $j usage 'sbcov' avoids 'ax-10' 'ax-11' 'ax-13'; $)

    $( Obsolete version of ~ sbcov as of 26-Aug-2025.  (Contributed by NM,
       14-May-1993.)  (Revised by GG, 7-Aug-2023.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sbcovOLD $p |- ( [ y / x ] [ x / y ] ph <-> [ y / x ] ph ) $=
      ( wsb sbcom3vv sbid sbbii bitri ) ACBDBCDACCDZBCDABCDACBCEIABCACFGH $.
    $( $j usage 'sbcov' avoids 'ax-10' 'ax-11' 'ax-13'; $)
  $}

  ${
    $d x y $.
    $( Equivalence for substitution.  (Contributed by NM, 2-Jun-1993.)  (Proof
       shortened by Wolf Lammen, 23-Sep-2018.) $)
    sb6a $p |- ( [ y / x ] ph <-> A. x ( x = y -> [ x / y ] ph ) ) $=
      ( wsb weq wi wal sbcov sb6 bitr3i ) ABCDACBDZBCDBCEKFBGABCHKBCIJ $.
  $}

  ${
    $d t x $.  $d x ph $.
    $( Reverting substitution yields the original expression.  Based on fewer
       axioms than ~ sbid2v , at the expense of an extra distinct variable
       condition.  (Contributed by NM, 14-May-1993.)  (Revised by Wolf Lammen,
       5-Aug-2023.) $)
    sbid2vw $p |- ( [ t / x ] [ x / t ] ph <-> ph ) $=
      ( wsb sbequ12r sbievw ) ACBDABCABCEF $.
  $}

  ${
    $d w x y $.  $d w z $.  $d w ph $.
    $( Generalization of ~ axc16 .  Use the latter when sufficient.  This proof
       only requires, on top of { ~ ax-1 -- ~ ax-7 }, Theorem ~ ax12v .
       (Contributed by NM, 15-May-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof shortened by Wolf Lammen, 18-Feb-2018.)  Remove
       dependency on ~ ax-13 , along an idea of BJ. (Revised by Wolf Lammen,
       30-Nov-2019.)  (Revised by BJ, 7-Jul-2021.)  Shorten ~ axc11rv .
       (Revised by Wolf Lammen, 11-Oct-2021.) $)
    axc16g $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( vw weq wal wi aevlem ax12v sps pm2.27 al2imi syld syl ) BCFBGDEFZDGZAAD
      GZHBCDEIQAPAHZDGZRPATHDADEJKPSADPALMNO $.
  $}

  ${
    $d x y $.
    $( Proof of older axiom ~ ax-c16 .  (Contributed by NM, 8-Nov-2006.)
       (Revised by NM, 22-Sep-2017.) $)
    axc16 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( axc16g ) ABCBD $.
  $}

  ${
    $d x y $.
    $( Biconditional strengthening of ~ axc16g .  (Contributed by NM,
       15-May-1993.) $)
    axc16gb $p |- ( A. x x = y -> ( ph <-> A. z ph ) ) $=
      ( weq wal axc16g sp impbid1 ) BCEBFAADFABCDGADHI $.
  $}

  ${
    $d x y $.
    $( If ~ dtru is false, then there is only one element in the universe, so
       everything satisfies ` F/ ` .  (Contributed by Mario Carneiro,
       7-Oct-2016.)  Remove dependency on ~ ax-11 .  (Revised by Wolf Lammen,
       9-Sep-2018.)  (Proof shortened by BJ, 14-Jun-2019.)  Remove dependency
       on ~ ax-10 .  (Revised by Wolf Lammen, 12-Oct-2021.) $)
    axc16nf $p |- ( A. x x = y -> F/ z ph ) $=
      ( weq wal wex wn wi axc16g eximal sylibr syld nfd ) BCEBFZADOADGZAADFOAHZ
      QDFIPAIQBCDJAADKLABCDJMN $.
  $}

  ${
    $d x y $.
    $( Version of ~ axc11 with a disjoint variable condition on ` x ` and
       ` y ` , which is provable, on top of { ~ ax-1 -- ~ ax-7 }, from ~ ax12v
       (contrary to ~ axc11 which seems to require the full ~ ax-12 and
       ~ ax-13 ).  (Contributed by NM, 16-May-2008.)  (Revised by BJ,
       6-Jul-2021.)  (Proof shortened by Wolf Lammen, 11-Oct-2021.) $)
    axc11v $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $=
      ( weq wal axc16g spsd ) BCDBEAACEBABCCFG $.

    $( Version of ~ axc11r with a disjoint variable condition on ` x ` and
       ` y ` , which is provable, on top of { ~ ax-1 -- ~ ax-7 }, from ~ ax12v
       (contrary to ~ axc11 which seems to require the full ~ ax-12 and
       ~ ax-13 , and to ~ axc11r which seems to require the full ~ ax-12 ).
       (Contributed by BJ, 6-Jul-2021.)  (Proof shortened by Wolf Lammen,
       11-Oct-2021.) $)
    axc11rv $p |- ( A. x x = y -> ( A. y ph -> A. x ph ) ) $=
      ( weq wal axc16 spsd ) BCDBEAABECABCFG $.
  $}

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  (Contributed
     by NM, 27-Feb-2005.) $)
  drsb2 $p |- ( A. x x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
    ( weq wsb wb sbequ sps ) BCEADBFADCFGBABCDHI $.

  ${
    $d x y $.
    equsalv.nf $e |- F/ x ps $.
    equsalv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( An equivalence related to implicit substitution.  Version of ~ equsal
       with a disjoint variable condition, which does not require ~ ax-13 .
       See ~ equsalvw for a version with two disjoint variable conditions
       requiring fewer axioms.  See also the dual form ~ equsexv .
       (Contributed by NM, 2-Jun-1993.)  (Revised by BJ, 31-May-2019.) $)
    equsalv $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal wex 19.23 pm5.74i albii ax6ev a1bi 3bitr4i ) CDGZBHZCIQCJZBH
      QAHZCIBQBCEKTRCQABFLMSBCDNOP $.

    $( An equivalence related to implicit substitution.  Version of ~ equsex
       with a disjoint variable condition, which does not require ~ ax-13 .
       See ~ equsexvw for a version with two disjoint variable conditions
       requiring fewer axioms.  See also the dual form ~ equsalv .
       (Contributed by NM, 5-Aug-1993.)  (Revised by BJ, 31-May-2019.)  Avoid
       ~ ax-10 .  (Revised by GG, 18-Nov-2024.) $)
    equsexv $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( weq wa wex biimpa exlimi wi wal equsalv equs4v sylbir impbii ) CDGZAHZC
      IZBSBCERABFJKBRALCMTABCDEFNACDOPQ $.
    $( $j usage 'equsexv' avoids 'ax-10'; $)
  $}

  $( Substitution has no effect on a nonfree variable.  (Contributed by NM,
     30-May-2009.)  (Revised by Mario Carneiro, 12-Oct-2016.)  (Proof shortened
     by Wolf Lammen, 3-May-2018.) $)
  sbft $p |- ( F/ x ph -> ( [ y / x ] ph <-> ph ) ) $=
    ( wnf wsb wex spsbe 19.9t imbitrid wal nf5r stdpc4 syl6 impbid ) ABDZABCEZA
    PABFOAABCGABHIOAABJPABKABCLMN $.

  ${
    sbf.1 $e |- F/ x ph $.
    $( Substitution for a variable not free in a wff does not affect it.  For a
       version requiring disjoint variables but fewer axioms, see ~ sbv .
       (Contributed by NM, 14-May-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    sbf $p |- ( [ y / x ] ph <-> ph ) $=
      ( wnf wsb wb sbft ax-mp ) ABEABCFAGDABCHI $.
  $}

  $( Substitution has no effect on a bound variable.  (Contributed by NM,
     1-Jul-2005.) $)
  sbf2 $p |- ( [ y / x ] A. x ph <-> A. x ph ) $=
    ( wal nfa1 sbf ) ABDBCABEF $.

  ${
    sbh.1 $e |- ( ph -> A. x ph ) $.
    $( Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 14-May-1993.) $)
    sbh $p |- ( [ y / x ] ph <-> ph ) $=
      ( nf5i sbf ) ABCABDEF $.
  $}

  ${
    $d x y $.
    $( The setvar ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y `
       are distinct.  (Contributed by NM, 26-May-1993.) $)
    hbs1 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wsb nfs1v nf5ri ) ABCDBABCEF $.
  $}

  ${
    nfs1f.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfs1f $p |- F/ x [ y / x ] ph $=
      ( wsb sbf nfxfr ) ABCEABABCDFDG $.
  $}

  ${
    $d x y $.
    $( Alternate definition of substitution when variables are disjoint.
       Similar to Theorem 6.1 of [Quine] p. 40.  The implication "to the right"
       is ~ sb1v and even needs no disjoint variable condition, see ~ sb1 .
       Theorem ~ sb5f replaces the disjoint variable condition with a
       nonfreeness hypothesis.  (Contributed by NM, 18-Aug-1993.)  (Revised by
       Wolf Lammen, 4-Sep-2023.) $)
    sb5 $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wi wal wa wex sb6 sbalex bitr4i ) ABCDBCEZAFBGMAHBIABCJABCKL $.

    $( A property related to substitution that replaces the distinctor from
       ~ equs5 to a disjoint variable condition.  Version of ~ equs5a with a
       disjoint variable condition, which does not require ~ ax-13 .  See also
       ~ sbalex .  (Contributed by NM, 2-Feb-2007.)  (Revised by GG,
       15-Dec-2023.) $)
    equs5av $p |- ( E. x ( x = y /\ A. y ph ) -> A. x ( x = y -> ph ) ) $=
      ( weq wal wa wi nfa1 ax12v2 spsd imp exlimi ) BCDZACEZFMAGZBEZBOBHMNPMAPC
      ABCIJKL $.
  $}

  ${
    $d x y z $.  $d w y $.
    $( Equivalence for double substitution.  (Contributed by NM,
       3-Feb-2005.) $)
    2sb5 $p |- ( [ z / x ] [ w / y ] ph <->
               E. x E. y ( ( x = z /\ y = w ) /\ ph ) ) $=
      ( wsb weq wa wex sb5 19.42v anass exbii anbi2i 3bitr4ri bitri ) ACEFZBDFB
      DGZQHZBIRCEGZHAHZCIZBIQBDJSUBBRTAHZHZCIRUCCIZHUBSRUCCKUAUDCRTALMQUERACEJN
      OMP $.
  $}

  ${
    $d y t $.  $d y x $.  $d y ph $.
    $( An alternate definition of proper substitution ~ df-sb .  By introducing
       a dummy variable ` y ` in the definiens, we are able to eliminate any
       distinct variable restrictions among the variables ` t ` , ` x ` , and
       ` ph ` of the definiendum.  No distinct variable conflicts arise because
       ` y ` effectively insulates ` t ` from ` x ` .  To achieve this, we use
       a chain of two substitutions in the form of ~ sb5 , first ` y ` for
       ` x ` then ` t ` for ` y ` .  Compare Definition 2.1'' of [Quine] p. 17,
       which is obtained from this theorem by applying ~ df-clab .  Theorem
       ~ sb7h provides a version where ` ph ` and ` y ` don't have to be
       distinct.  (Contributed by NM, 28-Jan-2004.)  Revise ~ df-sb .  (Revised
       by BJ, 25-Dec-2020.)  (Proof shortened by Wolf Lammen, 3-Sep-2023.) $)
    dfsb7 $p |- ( [ t / x ] ph <-> E. y ( y = t /\ E. x ( x = y /\ ph ) ) ) $=
      ( weq wi wal wa wex wsb sbalex anbi2i exbii dfsb 3bitr4ri ) CDEZBCEZAFBGZ
      HZCIPRFCGPQAHBIZHZCIABDJRCDKUASCTRPABCKLMABCDNO $.
  $}

  ${
    $d y t $.  $d y x $.  $d y ph $.
    $( Negation inside and outside of substitution are equivalent.
       (Contributed by NM, 14-May-1993.)  (Proof shortened by Wolf Lammen,
       30-Apr-2018.)  Revise ~ df-sb .  (Revised by BJ, 25-Dec-2020.) $)
    sbn $p |- ( [ t / x ] -. ph <-> -. [ t / x ] ph ) $=
      ( vy wn wsb weq wi wal wa dfsb alinexa imbi2i albii dfsb7 xchbinxr 3bitri
      wex ) AEZBCFDCGZBDGZSHBIZHZDITUAAJBRZEZHZDIZABCFZESBDCKUCUFDUBUETUAABLMNU
      GTUDJDRUHTUDDLABDCOPQ $.
  $}

  ${
    $d x y $.  $d x z $.
    $( Move existential quantifier in and out of substitution.  (Contributed by
       NM, 27-Sep-2003.) $)
    sbex $p |- ( [ z / y ] E. x ph <-> E. x [ z / y ] ph ) $=
      ( wn wal wsb wex sbn sbalv xchbinx df-ex sbbii 3bitr4i ) AEZBFZEZCDGZACDG
      ZEZBFZEABHZCDGSBHRPCDGUAPCDIOTCDBACDIJKUBQCDABLMSBLN $.
  $}

  $( Alternate definition of ~ df-nf .  (Contributed by Mario Carneiro,
     11-Aug-2016.) ~ df-nf changed.  (Revised by Wolf Lammen, 11-Sep-2021.) $)
  nf5 $p |- ( F/ x ph <-> A. x ( ph -> A. x ph ) ) $=
    ( wnf wex wal wi df-nf nfa1 19.23 bitr4i ) ABCABDABEZFAKFBEABGAKBABHIJ $.

  $( An alternate definition of ~ df-nf .  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nf6 $p |- ( F/ x ph <-> A. x ( E. x ph -> ph ) ) $=
    ( wnf wex wal wi df-nf nfe1 19.21 bitr4i ) ABCABDZABEFKAFBEABGKABABHIJ $.

  ${
    nf5d.1 $e |- F/ x ph $.
    nf5d.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduce that ` x ` is not free in ` ps ` in a context.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
    nf5d $p |- ( ph -> F/ x ps ) $=
      ( wal wi wnf alrimi nf5-1 syl ) ABBCFGZCFBCHALCDEIBCJK $.
  $}

  ${
    nf5di.1 $e |- ( ph -> F/ x ph ) $.
    $( Since the converse holds by ~ a1i , this inference shows that we can
       represent a not-free hypothesis with either ` F/ x ph ` (inference form)
       or ` ( ph -> F/ x ph ) ` (deduction form).  (Contributed by NM,
       17-Aug-2018.)  (Proof shortened by Wolf Lammen, 10-Jul-2019.) $)
    nf5di $p |- F/ x ph $=
      ( wal nf5rd pm2.43i nf5i ) ABAABDAABCEFG $.
  $}

  ${
    19.9h.1 $e |- ( ph -> A. x ph ) $.
    $( A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.)
       (Proof shortened by Wolf Lammen, 5-Jan-2018.)  (Proof shortened by Wolf
       Lammen, 14-Jul-2020.) $)
    19.9h $p |- ( E. x ph <-> ph ) $=
      ( nf5i 19.9 ) ABABCDE $.
  $}

  ${
    19.21h.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ".  See also ~ 19.21 and ~ 19.21v .
       (Contributed by NM, 1-Aug-2017.)  (Proof shortened by Wolf Lammen,
       1-Jan-2018.) $)
    19.21h $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( nf5i 19.21 ) ABCACDEF $.
  $}

  ${
    19.23h.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.23 of [Margaris] p. 90.  See ~ 19.23 .  (Contributed by NM,
       24-Jan-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.)  (Proof
       shortened by Wolf Lammen, 1-Jan-2018.) $)
    19.23h $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( nf5i 19.23 ) ABCBCDEF $.
  $}

  ${
    exlimih.1 $e |- ( ps -> A. x ps ) $.
    exlimih.2 $e |- ( ph -> ps ) $.
    $( Inference associated with ~ 19.23 .  See ~ exlimiv for a version with a
       disjoint variable condition requiring fewer axioms.  (Contributed by NM,
       10-Jan-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.)  (Proof
       shortened by Wolf Lammen, 1-Jan-2018.) $)
    exlimih $p |- ( E. x ph -> ps ) $=
      ( nf5i exlimi ) ABCBCDFEG $.
  $}

  ${
    exlimdh.1 $e |- ( ph -> A. x ph ) $.
    exlimdh.2 $e |- ( ch -> A. x ch ) $.
    exlimdh.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.9 of [Margaris] p. 89.  (Contributed by NM,
       28-Jan-1997.) $)
    exlimdh $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( nf5i exlimd ) ABCDADEHCDFHGI $.
  $}

  ${
    $d x y $.
    equsalhw.1 $e |- ( ps -> A. x ps ) $.
    equsalhw.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Version of ~ equsalh with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by NM, 29-Nov-2015.)  (Proof shortened
       by Wolf Lammen, 8-Jul-2022.) $)
    equsalhw $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( nf5i equsalv ) ABCDBCEGFH $.

    $( An equivalence related to implicit substitution.  Version of ~ equsexh
       with a disjoint variable condition, which does not require ~ ax-13 .
       (Contributed by NM, 5-Aug-1993.)  (Revised by BJ, 31-May-2019.) $)
    equsexhv $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( nf5i equsexv ) ABCDBCEGFH $.
  $}

  $( The setvar ` x ` is not free in ` A. x ph ` .  This corresponds to the
     axiom (4) of modal logic.  Example in Appendix in [Megill] p. 450 (p. 19
     of the preprint).  Also Lemma 22 of [Monk2] p. 114.  (Contributed by NM,
     24-Jan-1993.)  (Proof shortened by Wolf Lammen, 12-Oct-2021.) $)
  hba1 $p |- ( A. x ph -> A. x A. x ph ) $=
    ( wal nfa1 nf5ri ) ABCBABDE $.

  $( Closed theorem version of bound-variable hypothesis builder ~ hbn .
     (Contributed by NM, 10-May-1993.)  (Proof shortened by Wolf Lammen,
     14-Oct-2021.) $)
  hbnt $p |- ( A. x ( ph -> A. x ph ) -> ( -. ph -> A. x -. ph ) ) $=
    ( wal wi wn nf5-1 nfnd nf5rd ) AABCDBCZAEBIABABFGH $.

  ${
    hbn.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` .
       (Contributed by NM, 10-Jan-1993.)  (Proof shortened by Wolf Lammen,
       17-Dec-2017.) $)
    hbn $p |- ( -. ph -> A. x -. ph ) $=
      ( wal wi wn hbnt mpg ) AABDEAFZIBDEBABGCH $.
  $}

  ${
    hbnd.1 $e |- ( ph -> A. x ph ) $.
    hbnd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbn .
       (Contributed by NM, 3-Jan-2002.) $)
    hbnd $p |- ( ph -> ( -. ps -> A. x -. ps ) ) $=
      ( wal wi wn alrimih hbnt syl ) ABBCFGZCFBHZMCFGALCDEIBCJK $.
  $}

  ${
    hbim1.1 $e |- ( ph -> A. x ph ) $.
    hbim1.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( A closed form of ~ hbim .  (Contributed by NM, 2-Jun-1993.) $)
    hbim1 $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
      ( wi wal a2i 19.21h sylibr ) ABFZABCGZFKCGABLEHABCDIJ $.
  $}

  ${
    hbimd.1 $e |- ( ph -> A. x ph ) $.
    hbimd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hbimd.3 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbim .
       (Contributed by NM, 14-May-1993.)  (Proof shortened by Wolf Lammen,
       3-Jan-2018.) $)
    hbimd $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $=
      ( wi nf5dh nfimd nf5rd ) ABCHDABCDABDEFIACDEGIJK $.
  $}

  ${
    hbim.1 $e |- ( ph -> A. x ph ) $.
    hbim.2 $e |- ( ps -> A. x ps ) $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by NM, 24-Jan-1993.)  (Proof shortened
       by Mel L. O'Cat, 3-Mar-2008.)  (Proof shortened by Wolf Lammen,
       1-Jan-2018.) $)
    hbim $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
      ( wal wi a1i hbim1 ) ABCDBBCFGAEHI $.
  $}

  ${
    hb.1 $e |- ( ph -> A. x ph ) $.
    hb.2 $e |- ( ps -> A. x ps ) $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by NM, 14-May-1993.)  (Proof shortened
       by Wolf Lammen, 2-Jan-2018.) $)
    hban $p |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) ) $=
      ( wa nf5i nfan nf5ri ) ABFCABCACDGBCEGHI $.
    hb.3 $e |- ( ch -> A. x ch ) $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph /\ ps /\ ch ) ` .  (Contributed by NM, 14-Sep-2003.)  (Proof
       shortened by Wolf Lammen, 2-Jan-2018.) $)
    hb3an $p |- ( ( ph /\ ps /\ ch ) -> A. x ( ph /\ ps /\ ch ) ) $=
      ( w3a nf5i nf3an nf5ri ) ABCHDABCDADEIBDFICDGIJK $.
  $}

  $( Introduction of implication into substitution.  (Contributed by NM,
     14-May-1993.) $)
  sbi2 $p |- ( ( [ y / x ] ph -> [ y / x ] ps ) -> [ y / x ] ( ph -> ps ) ) $=
    ( wsb wi wn sbn pm2.21 sbimi sylbir ax-1 ja ) ACDEZBCDEABFZCDEZNGAGZCDEPACD
    HQOCDABIJKBOCDBALJM $.

  $( Implication inside and outside of a substitution are equivalent.
     (Contributed by NM, 14-May-1993.) $)
  sbim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( wi wsb sbi1 sbi2 impbii ) ABECDFACDFBCDFEABCDGABCDHI $.

  ${
    $d t x $.  $d t y $.  $d ps t $.  $d ph t $.
    sbrim.1 $e |- F/ x ph $.
    $( Substitution in an implication with a variable not free in the
       antecedent affects only the consequent.  (Contributed by NM,
       2-Jun-1993.)  (Revised by Mario Carneiro, 4-Oct-2016.)  Avoid ~ ax-10 .
       (Revised by GG, 20-Nov-2024.) $)
    sbrim $p |- ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) ) $=
      ( vt weq wi wal wsb bi2.04 albii 19.21 bitri imbi2i 19.21v bitr4i 3bitr4i
      dfsb ) FDGZCFGZABHZHZCIZHZFIATUABHZCIZHZHZFIZUBCDJABCDJZHZUEUIFUETAUGHZHU
      IUDUMTUDAUFHZCIUMUCUNCUAABKLAUFCEMNOTAUGKNLUBCFDSULAUHFIZHUJUKUOABCFDSOAU
      HFPQR $.
    $( $j usage 'sbrim' avoids 'ax-10'; $)
  $}

  ${
    sblim.1 $e |- F/ x ps $.
    $( Substitution in an implication with a variable not free in the
       consequent affects only the antecedent.  (Contributed by NM,
       14-Nov-2013.)  (Revised by Mario Carneiro, 4-Oct-2016.) $)
    sblim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> ps ) ) $=
      ( wi wsb sbim sbf imbi2i bitri ) ABFCDGACDGZBCDGZFLBFABCDHMBLBCDEIJK $.
  $}

  $( Disjunction inside and outside of a substitution are equivalent.
     (Contributed by NM, 29-Sep-2002.) $)
  sbor $p |- ( [ y / x ] ( ph \/ ps ) <-> ( [ y / x ] ph \/ [ y / x ] ps ) ) $=
    ( wn wi wsb wo sbim sbn imbi1i bitri df-or sbbii 3bitr4i ) AEZBFZCDGZACDGZE
    ZBCDGZFZABHZCDGSUAHRPCDGZUAFUBPBCDIUDTUAACDJKLUCQCDABMNSUAMO $.

  $( Equivalence inside and outside of a substitution are equivalent.
     (Contributed by NM, 14-May-1993.) $)
  sbbi $p |- ( [ y / x ] ( ph <-> ps )
     <-> ( [ y / x ] ph <-> [ y / x ] ps ) ) $=
    ( wb wsb wi wa dfbi2 sbbii sbim anbi12i sban 3bitr4i bitri ) ABEZCDFABGZBAG
    ZHZCDFZACDFZBCDFZEZPSCDABIJQCDFZRCDFZHUAUBGZUBUAGZHTUCUDUFUEUGABCDKBACDKLQR
    CDMUAUBINO $.

  ${
    sblbis.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce left biconditional inside of a substitution.  (Contributed by
       NM, 19-Aug-1993.) $)
    sblbis $p |- ( [ y / x ] ( ch <-> ph ) <-> ( [ y / x ] ch <-> ps ) ) $=
      ( wb wsb sbbi bibi2i bitri ) CAGDEHCDEHZADEHZGLBGCADEIMBLFJK $.
  $}

  ${
    sbrbis.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce right biconditional inside of a substitution.  (Contributed by
       NM, 18-Aug-1993.) $)
    sbrbis $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> [ y / x ] ch ) ) $=
      ( wb wsb sbbi bibi1i bitri ) ACGDEHADEHZCDEHZGBMGACDEILBMFJK $.
  $}

  ${
    sbrbif.1 $e |- F/ x ch $.
    sbrbif.2 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce right biconditional inside of a substitution.  (Contributed by
       NM, 18-Aug-1993.)  (Revised by Mario Carneiro, 4-Oct-2016.) $)
    sbrbif $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      ( wb wsb sbrbis sbf bibi2i bitri ) ACHDEIBCDEIZHBCHABCDEGJNCBCDEFKLM $.
  $}

  ${
    $d x y $.  $d x z $.
    $( Move nonfree predicate in and out of substitution; see ~ sbal and
       ~ sbex .  (Contributed by BJ, 2-May-2019.)  (Proof shortened by Wolf
       Lammen, 2-May-2025.) $)
    sbnf $p |- ( [ z / y ] F/ x ph <-> F/ x [ z / y ] ph ) $=
      ( wnf wsb wex wal wi df-nf sbbii sbim sbex sbal imbi12i bitr4i 3bitri ) A
      BEZCDFABGZABHZIZCDFSCDFZTCDFZIZACDFZBEZRUACDABJKSTCDLUDUEBGZUEBHZIUFUBUGU
      CUHABCDMABCDNOUEBJPQ $.
  $}

  ${
    $d x y $.
    sbiev.1 $e |- F/ x ps $.
    sbiev.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit substitution.  Version
       of ~ sbie with a disjoint variable condition, not requiring ~ ax-13 .
       See ~ sbievw for a version with a disjoint variable condition requiring
       fewer axioms.  (Contributed by NM, 30-Jun-1994.)  (Revised by Wolf
       Lammen, 18-Jan-2023.)  Remove dependence on ~ ax-10 and shorten proof.
       (Revised by BJ, 18-Jul-2023.)  (Proof shortened by SN, 24-Jul-2025.) $)
    sbiev $p |- ( [ y / x ] ph <-> ps ) $=
      ( wsb sbbiiev sbf bitri ) ACDGBCDGBABCDFHBCDEIJ $.
    $( $j usage 'sbiev' avoids 'ax-10' 'ax-13'; $)

    $( Obsolete version of ~ sbiev as of 24-Aug-2025.  (Contributed by NM,
       30-Jun-1994.)  (Revised by Wolf Lammen, 18-Jan-2023.)  Remove dependence
       on ~ ax-10 and shorten proof.  (Revised by BJ, 18-Jul-2023.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sbievOLD $p |- ( [ y / x ] ph <-> ps ) $=
      ( wsb weq wi wal sb6 equsalv bitri ) ACDGCDHAICJBACDKABCDEFLM $.
  $}

  ${
    $d x y $.
    sbiedw.1 $e |- F/ x ph $.
    sbiedw.2 $e |- ( ph -> F/ x ch ) $.
    sbiedw.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbiev ).  Version of ~ sbied with a disjoint variable
       condition, requiring fewer axioms.  (Contributed by NM, 30-Jun-1994.)
       Avoid ~ ax-13 .  (Revised by GG, 10-Jan-2024.) $)
    sbiedw $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( wsb wi sbrim nfim1 weq wb com12 pm5.74d sbiev bitr3i pm5.74ri ) ABDEIZC
      ATJABJZDEIACJZABDEFKUAUBDEACDFGLDEMZABCAUCBCNHOPQRS $.
    $( $j usage 'sbiedw' avoids 'ax-10' 'ax-11' 'ax-13'; $)
  $}

  $( Show that the original axiom ~ ax-c7 can be derived from ~ ax-10
     ( ~ hbn1 ), ~ sp and propositional calculus.  See ~ ax10fromc7 for the
     rederivation of ~ ax-10 from ~ ax-c7 .

     Normally, ~ axc7 should be used rather than ~ ax-c7 , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     21-May-2008.) $)
  axc7 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn sp hbn1 nsyl4 ) ABCZAHDBCABEABFG $.

  $( Abbreviated version of ~ axc7 using the existential quantifier.
     Corresponds to the dual of Axiom (B) of modal logic.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Wolf Lammen, 8-Jul-2022.) $)
  axc7e $p |- ( E. x A. x ph -> ph ) $=
    ( wal wex hbe1a 19.21bi ) ABCBDABABEF $.

  $( The analogue in our predicate calculus of the Brouwer axiom (B) of modal
     logic S5.  (Contributed by NM, 5-Oct-2005.) $)
  modal-b $p |- ( ph -> A. x -. A. x -. ph ) $=
    ( wn wal axc7 con4i ) ACZBDCBDAGBEF $.

  $( A closed version of ~ 19.9h .  (Contributed by NM, 13-May-1993.)  (Proof
     shortened by Wolf Lammen, 3-Mar-2018.) $)
  19.9ht $p |- ( A. x ( ph -> A. x ph ) -> ( E. x ph -> ph ) ) $=
    ( wal wi nf5-1 19.9d ) AAABCDBCBABEF $.

  $( Show that the original axiom ~ ax-c4 can be derived from ~ ax-4
     ( ~ alim ), ~ ax-10 ( ~ hbn1 ), ~ sp and propositional calculus.  See
     ~ ax4fromc4 for the rederivation of ~ ax-4 from ~ ax-c4 .

     Part of the proof is based on the proof of Lemma 22 of [Monk2] p. 114.
     (Contributed by NM, 21-May-2008.)  (Proof modification is discouraged.) $)
  axc4 $p |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( wal wi wn sp con2i hbn1 con1i alimi 3syl alim syl5 ) ACDZOCDZOBECDBCDOOFZ
    CDZFZSCDPROQCGHQCISOCORACIJKLOBCMN $.

  ${
    axc4i.1 $e |- ( A. x ph -> ps ) $.
    $( Inference version of ~ axc4 .  (Contributed by NM, 3-Jan-1993.) $)
    axc4i $p |- ( A. x ph -> A. x ps ) $=
      ( wal nfa1 alrimi ) ACEBCACFDG $.
  $}

  ${
    nfal.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , then it is not free in ` A. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfal $p |- F/ x A. y ph $=
      ( wal nf5ri hbal nf5i ) ACEBABCABDFGH $.
  $}

  ${
    nfex.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , then it is not free in ` E. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.)  (Proof shortened by Wolf
       Lammen, 30-Dec-2017.)  Reduce symbol count in ~ nfex , ~ hbex .
       (Revised by Wolf Lammen, 16-Oct-2021.) $)
    nfex $p |- F/ x E. y ph $=
      ( wex wn wal df-ex nfn nfal nfxfr ) ACEAFZCGZFBACHMBLBCABDIJIK $.
  $}

  ${
    hbex.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , then it is not free in ` E. y ph ` .
       (Contributed by NM, 12-Mar-1993.)  Reduce symbol count in ~ nfex ,
       ~ hbex .  (Revised by Wolf Lammen, 16-Oct-2021.) $)
    hbex $p |- ( E. y ph -> A. x E. y ph ) $=
      ( wex nf5i nfex nf5ri ) ACEBABCABDFGH $.
  $}

  ${
    nfnf.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , then it is not free in ` F/ y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.)  (Proof shortened by Wolf
       Lammen, 30-Dec-2017.) $)
    nfnf $p |- F/ x F/ y ph $=
      ( wnf wex wal wi df-nf nfex nfal nfim nfxfr ) ACEACFZACGZHBACINOBABCDJABC
      DKLM $.
  $}

  $( Theorem 19.12 of [Margaris] p. 89.  Assuming the converse is a mistake
     sometimes made by beginners!  But sometimes the converse does hold, as in
     ~ 19.12vv and ~ r19.12sn .  (Contributed by NM, 12-Mar-1993.)  (Proof
     shortened by Wolf Lammen, 3-Jan-2018.) $)
  19.12 $p |- ( E. x A. y ph -> A. y E. x ph ) $=
    ( wal wex nfa1 nfex sp eximi alrimi ) ACDZBEABECKCBACFGKABACHIJ $.

  ${
    nfald.1 $e |- F/ y ph $.
    nfald.2 $e |- ( ph -> F/ x ps ) $.
    $( Deduction form of ~ nfal .  (Contributed by Mario Carneiro,
       24-Sep-2016.)  (Proof shortened by Wolf Lammen, 16-Oct-2021.) $)
    nfald $p |- ( ph -> F/ x A. y ps ) $=
      ( wal wex 19.12 nfrd alimd ax-11 syl56 nfd ) ABDGZCOCHBCHZDGABCGZDGOCGBCD
      IAPQDEABCFJKBDCLMN $.

    $( If ` x ` is not free in ` ps ` , then it is not free in ` E. y ps ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    nfexd $p |- ( ph -> F/ x E. y ps ) $=
      ( wex wn wal df-ex nfnd nfald nfxfrd ) BDGBHZDIZHACBDJAOCANCDEABCFKLKM $.
  $}

  ${
    $d w x z $.  $d w y z $.  $d w ph $.
    nfsbv.nf $e |- F/ z ph $.
    $( If ` z ` is not free in ` ph ` , then it is not free in ` [ y / x ] ph `
       when ` z ` is disjoint from both ` x ` and ` y ` .  Version of ~ nfsb
       with an additional disjoint variable condition on ` x , z ` but not
       requiring ~ ax-13 .  (Contributed by Mario Carneiro, 11-Aug-2016.)
       (Revised by Wolf Lammen, 7-Feb-2023.)  Remove disjoint variable
       condition on ` x , y ` .  (Revised by Steven Nguyen, 13-Aug-2023.)
       (Proof shortened by Wolf Lammen, 25-Oct-2024.) $)
    nfsbv $p |- F/ z [ y / x ] ph $=
      ( wsb nf5ri hbsbw nf5i ) ABCFDABCDADEGHI $.
  $}

  ${
    $d x z $.  $d y z $.
    sbco2v.1 $e |- F/ z ph $.
    $( A composition law for substitution.  Version of ~ sbco2 with disjoint
       variable conditions but not requiring ~ ax-13 .  (Contributed by NM,
       30-Jun-1994.)  (Revised by Wolf Lammen, 29-Apr-2023.) $)
    sbco2v $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      ( wsb nfsbv sbequ sbiev ) ABDFABCFDCABCDEGADCBHI $.
  $}

  ${
    aaan.1 $e |- F/ y ph $.
    aaan.2 $e |- F/ x ps $.
    $( Distribute universal quantifiers.  (Contributed by NM, 12-Aug-1993.)
       Avoid ~ ax-10 .  (Revised by GG, 21-Nov-2024.) $)
    aaan $p |- ( A. x A. y ( ph /\ ps ) <-> ( A. x ph /\ A. y ps ) ) $=
      ( wa wal 19.26-2 19.3 albii alcom bitri anbi12i ) ABGDHCHADHZCHZBDHZCHZGA
      CHZQGABCDIPSRQOACADEJKRBCHZDHQBCDLTBDBCFJKMNM $.
    $( $j usage 'aaan' avoids 'ax-10'; $)
  $}

  ${
    eeor.1 $e |- F/ y ph $.
    eeor.2 $e |- F/ x ps $.
    $( Distribute existential quantifiers.  (Contributed by NM, 8-Aug-1994.)
       Avoid ~ ax-10 .  (Revised by GG, 21-Nov-2024.) $)
    eeor $p |- ( E. x E. y ( ph \/ ps ) <-> ( E. x ph \/ E. y ps ) ) $=
      ( wo wex 19.43 exbii 19.9 excom bitri orbi12i ) ABGDHZCHADHZBDHZGZCHZACHZ
      QGZORCABDIJSPCHZQCHZGUAPQCIUBTUCQPACADEKJUCBCHZDHQBCDLUDBDBCFKJMNMM $.
    $( $j usage 'eeor' avoids 'ax-10'; $)
  $}

  ${
    $d x y $.
    cbv3v.nf1 $e |- F/ y ph $.
    cbv3v.nf2 $e |- F/ x ps $.
    cbv3v.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbv3 with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by NM, 5-Aug-1993.)  (Revised by BJ,
       31-May-2019.) $)
    cbv3v $p |- ( A. x ph -> A. y ps ) $=
      ( wal nf5ri hbal spimfv alrimih ) ACHBDADCADEIJABCDFGKL $.
  $}

  ${
    $d x y $.
    cbv1v.1 $e |- F/ x ph $.
    cbv1v.2 $e |- F/ y ph $.
    cbv1v.3 $e |- ( ph -> F/ y ps ) $.
    cbv1v.4 $e |- ( ph -> F/ x ch ) $.
    cbv1v.5 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbv1 with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by NM, 5-Aug-1993.)  (Revised by BJ,
       16-Jun-2019.) $)
    cbv1v $p |- ( ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal wi nfim1 weq com12 a2d cbv3v 19.21 3imtr3i pm2.86i ) ABDKZCEKZABLZD
      KACLZEKAUALAUBLUCUDDEABEGHMACDFIMDENZABCAUEBCLJOPQABDFRACEGRST $.
  $}

  ${
    $d x y $.
    cbv2w.1 $e |- F/ x ph $.
    cbv2w.2 $e |- F/ y ph $.
    cbv2w.3 $e |- ( ph -> F/ y ps ) $.
    cbv2w.4 $e |- ( ph -> F/ x ch ) $.
    cbv2w.5 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbv2 with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by NM, 5-Aug-1993.)  Avoid ~ ax-13 .
       (Revised by GG, 10-Jan-2024.) $)
    cbv2w $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal weq wb wi biimp syl6 cbv1v equcomi biimpr syl56 impbid ) ABDKCEKABC
      DEFGHIADELZBCMZBCNJBCOPQACBEDGFIHEDLUBAUCCBNEDRJBCSTQUA $.
  $}

  ${
    $d x ph $.  $d x ch $.  $d x y $.
    cbvaldw.1 $e |- F/ y ph $.
    cbvaldw.2 $e |- ( ph -> F/ y ps ) $.
    cbvaldw.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Deduction used to change bound variables, using implicit substitution.
       Version of ~ cbvald with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by NM, 2-Jan-2002.)  Avoid ~ ax-13 .
       (Revised by GG, 10-Jan-2024.) $)
    cbvaldw $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( nfv nfvd cbv2w ) ABCDEADIFGACDJHK $.

    $( Deduction used to change bound variables, using implicit substitution.
       Version of ~ cbvexd with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by NM, 2-Jan-2002.)  Avoid ~ ax-13 .
       (Revised by GG, 10-Jan-2024.) $)
    cbvexdw $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( wex wn wal nfnd weq wb notbi imbitrdi cbvaldw alnex 3bitr3g con4bid ) A
      BDIZCEIZABJZDKCJZEKUAJUBJAUCUDDEFABEGLADEMBCNUCUDNHBCOPQBDRCERST $.
  $}

  ${
    $d x y $.
    cbv3hv.nf1 $e |- ( ph -> A. y ph ) $.
    cbv3hv.nf2 $e |- ( ps -> A. x ps ) $.
    cbv3hv.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbv3h with a disjoint variable condition on ` x , y ` ,
       which does not require ~ ax-13 .  Was used in a proof of ~ axc11n (but
       of independent interest).  (Contributed by NM, 25-Jul-2015.)  (Proof
       shortened by Wolf Lammen, 29-Nov-2020.)  (Proof shortened by BJ,
       30-Nov-2020.) $)
    cbv3hv $p |- ( A. x ph -> A. y ps ) $=
      ( nf5i cbv3v ) ABCDADEHBCFHGI $.
  $}

  ${
    $d x y $.
    cbvalv1.nf1 $e |- F/ y ph $.
    cbvalv1.nf2 $e |- F/ x ps $.
    cbvalv1.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbval with a disjoint variable condition, which does not
       require ~ ax-13 .  See ~ cbvalvw for a version with two more disjoint
       variable conditions, requiring fewer axioms, and ~ cbvalv for another
       variant.  (Contributed by NM, 13-May-1993.)  (Revised by BJ,
       31-May-2019.) $)
    cbvalv1 $p |- ( A. x ph <-> A. y ps ) $=
      ( wal weq biimpd cbv3v wi biimprd equcoms impbii ) ACHBDHABCDEFCDIZABGJKB
      ADCFEBALCDPABGMNKO $.

    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbvex with a disjoint variable condition, which does not
       require ~ ax-13 .  See ~ cbvexvw for a version with two disjoint
       variable conditions, requiring fewer axioms, and ~ cbvexv for another
       variant.  (Contributed by NM, 21-Jun-1993.)  (Revised by BJ,
       31-May-2019.) $)
    cbvexv1 $p |- ( E. x ph <-> E. y ps ) $=
      ( wex wn wal nfn weq notbid cbvalv1 alnex 3bitr3i con4bii ) ACHZBDHZAIZCJ
      BIZDJRISITUACDADEKBCFKCDLABGMNACOBDOPQ $.
  $}

  ${
    $d x y z w $.
    cbval2v.1 $e |- F/ z ph $.
    cbval2v.2 $e |- F/ w ph $.
    cbval2v.3 $e |- F/ x ps $.
    cbval2v.4 $e |- F/ y ps $.
    cbval2v.5 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbval2 with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by NM, 22-Dec-2003.)  (Revised by BJ,
       16-Jun-2019.)  (Proof shortened by GG, 10-Jan-2024.) $)
    cbval2v $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( wal nfal weq nfv wnf a1i wb ex cbv2w cbvalv1 ) ADLBFLCEAEDGMBCFIMCENZAB
      DFUBDOUBFOAFPUBHQBDPUBJQUBDFNABRKSTUA $.

    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbvex2 with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by NM, 14-Sep-2003.)  (Revised by BJ,
       16-Jun-2019.) $)
    cbvex2v $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( wex wn wal nfn weq wa notbid cbval2v 2nexaln 3bitr4i con4bii ) ADLCLZBF
      LELZAMZDNCNBMZFNENUCMUDMUEUFCDEFAEGOAFHOBCIOBDJOCEPDFPQABKRSACDTBEFTUAUB
      $.
  $}

  ${
    $d x z $.  $d y z $.
    dvelimhw.1 $e |- ( ph -> A. x ph ) $.
    dvelimhw.2 $e |- ( ps -> A. z ps ) $.
    dvelimhw.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    dvelimhw.4 $e |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $.
    $( Proof of ~ dvelimh without using ~ ax-13 but with additional distinct
       variable conditions.  (Contributed by NM, 1-Oct-2002.)  (Revised by
       Andrew Salmon, 21-Jul-2011.)  (Revised by NM, 1-Aug-2017.)  (Proof
       shortened by Wolf Lammen, 23-Dec-2018.) $)
    dvelimhw $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi wnf nfv equcom nfna1 nf5d nfxfrd nf5i a1i nfimd equsalhw
      nfald nfbii sylib nf5rd ) CDJZCKLZBCUIEDJZAMZEKZCNBCNUIUKCEUIEOUIUJACUJDE
      JZUICEDPUIUMCUHCQIRSACNUIACFTUAUBUDULBCABEDGHUCUEUFUG $.
  $}

  ${
    $d ph y $.  $d ps x $.
    $( Theorem *11.53 in [WhiteheadRussell] p. 164.  See ~ pm11.53v for a
       version requiring fewer axioms.  (Contributed by Andrew Salmon,
       24-May-2011.) $)
    pm11.53 $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) $=
      ( wi wal wex 19.21v albii nfv nfal 19.23 bitri ) ABEDFZCFABDFZEZCFACGOENP
      CABDHIAOCBCDBCJKLM $.
  $}

  ${
    $d x ps $.  $d y ph $.
    $( Special case of ~ 19.12 where its converse holds.  See ~ 19.12vvv for a
       version with a disjoint variable condition requiring fewer axioms.
       (Contributed by NM, 18-Jul-2001.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)
    19.12vv $p |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) ) $=
      ( wi wal wex 19.21v exbii nfv nfal 19.36 19.36v albii 19.21 bitr2i 3bitri
      ) ABEZDFZCGABDFZEZCGACFZTEZRCGZDFZSUACABDHIATCBCDBCJKLUEUBBEZDFUCUDUFDABC
      MNUBBDADCADJKOPQ $.
  $}

  ${
    eean.1 $e |- F/ y ph $.
    eean.2 $e |- F/ x ps $.
    $( Distribute existential quantifiers.  (Contributed by NM, 27-Oct-2010.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    eean $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      ( wa wex 19.42 exbii nfex 19.41 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
  $}

  ${
    $d y ph $.  $d x ps $.
    $( Distribute a pair of existential quantifiers over a conjunction.
       Combination of ~ 19.41v and ~ 19.42v .  For a version requiring fewer
       axioms but with additional disjoint variable conditions, see
       ~ exdistrv .  (Contributed by NM, 26-Jul-1995.) $)
    eeanv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      ( nfv eean ) ABCDADEBCEF $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d x ps $.  $d z ps $.  $d x ch $.  $d y ch $.
    $( Distribute three existential quantifiers over a conjunction.
       (Contributed by NM, 26-Jul-1995.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  Reduce distinct variable restrictions.  (Revised by Wolf
       Lammen, 20-Jan-2018.) $)
    eeeanv $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
                                         ( E. x ph /\ E. y ps /\ E. z ch ) ) $=
      ( wa wex w3a eeanv anbi1i df-3an exbii 19.42v bitri 2exbii nfv nfex 19.41
      3bitri 3bitr4i ) ABGZEHZDHZCFHZGZADHZBEHZGZUEGABCIZFHZEHDHZUGUHUEIUDUIUEA
      BDEJKULUBUEGZEHZDHUCUEGZDHUFUKUMDEUKUBCGZFHUMUJUPFABCLMUBCFNOPUNUODUBUEEC
      EFCEQRSMUCUEDCDFCDQRSTUGUHUELUA $.
  $}

  ${
    $d z ph $.  $d w ph $.  $d x ps $.  $d y ps $.
    $( Distribute two pairs of existential quantifiers over a conjunction.  For
       a version requiring fewer axioms but with additional disjoint variable
       conditions, see ~ 4exdistrv .  (Contributed by NM, 31-Jul-1995.)  Remove
       disjoint variable conditions on ` y , z ` and ` x , w ` .  (Revised by
       Eric Schmidt, 26-Oct-2025.) $)
    ee4anv $p |- ( E. x E. y E. z E. w ( ph /\ ps ) <->
                                          ( E. x E. y ph /\ E. z E. w ps ) ) $=
      ( wa wex excom exbii eeanv 2exbii nfv nfex eean 3bitri ) ABGFHZEHDHZCHQDH
      ZEHZCHADHZBFHZGZEHCHUACHUBEHGRTCQDEIJSUCCEABDFKLUAUBCEAEDAEMNBCFBCMNOP $.

    ${
      $d y z $.  $d w x $.
      $( Obsolete version of ~ ee4anv as of 26-Oct-2025.  (Contributed by NM,
         31-Jul-1995.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
      ee4anvOLD $p |- ( E. x E. y E. z E. w ( ph /\ ps ) <->
                                          ( E. x E. y ph /\ E. z E. w ps ) ) $=
        ( wa wex excom exbii eeanv 2exbii 3bitri ) ABGFHZEHDHZCHNDHZEHZCHADHZBF
        HZGZEHCHRCHSEHGOQCNDEIJPTCEABDFKLRSCEKM $.
    $}
  $}

  ${
    $d ph y $.  $d x y $.
    $( Substitution of variable in universal quantifier.  Version of ~ sb8f
       with a disjoint variable condition replacing the nonfree hypothesis
       ` F/ y ph ` , not requiring ~ ax-12 .  (Contributed by SN,
       5-Dec-2024.) $)
    sb8v $p |- ( A. x ph <-> A. y [ y / x ] ph ) $=
      ( wsb wal weq wi sb6 albii alcom equcom imbi1i equsv bitri 3bitrri ) ABCD
      ZCEBCFZAGZBEZCERCEZBEABEPSCABCHIRCBJTABTCBFZAGZCEARUBCQUAABCKLIACBMNIO $.
    $( $j usage 'sb8v' avoids 'ax-10' 'ax-12'; $)
  $}

  ${
    $d x y $.
    sb8f.nf $e |- F/ y ph $.
    $( Substitution of variable in universal quantifier.  Version of ~ sb8 with
       a disjoint variable condition, not requiring ~ ax-10 or ~ ax-13 .
       (Contributed by NM, 16-May-1993.)  (Revised by Wolf Lammen,
       19-Jan-2023.)  Avoid ~ ax-10 .  (Revised by SN, 5-Dec-2024.) $)
    sb8f $p |- ( A. x ph <-> A. y [ y / x ] ph ) $=
      ( wsb wal weq wi sb6 albii alcom sbf equcom imbi1i 3bitr3ri 3bitrri ) ABC
      EZCFBCGZAHZBFZCFSCFZBFABFQTCABCIJSCBKUAABACBECBGZAHZCFAUAACBIACBDLUCSCUBR
      ACBMNJOJP $.
    $( $j usage 'sb8f' avoids 'ax-10' 'ax-13'; $)

    $( Substitution of variable in existential quantifier.  Version of ~ sb8e
       with a disjoint variable condition, not requiring ~ ax-13 .
       (Contributed by NM, 12-Aug-1993.)  (Revised by Wolf Lammen,
       19-Jan-2023.) $)
    sb8ef $p |- ( E. x ph <-> E. y [ y / x ] ph ) $=
      ( wsb nfs1v sbequ12 cbvexv1 ) AABCEBCDABCFABCGH $.
  $}

  ${
    $d z x $.  $d z w y $.
    2sb8ef.1 $e |- F/ w ph $.
    2sb8ef.2 $e |- F/ z ph $.
    $( An equivalent expression for double existence.  Version of ~ 2sb8e with
       more disjoint variable conditions, not requiring ~ ax-13 .  (Contributed
       by Wolf Lammen, 28-Jan-2023.) $)
    2sb8ef $p |- ( E. x E. y ph <->
                  E. z E. w [ z / x ] [ w / y ] ph ) $=
      ( wex wsb sb8ef exbii excom bitri nfsbv 3bitri ) ACHZBHZACEIZBHZEHZRBDIZD
      HZEHUAEHDHQREHZBHTPUCBACEFJKRBELMSUBERBDACEDGNJKUAEDLO $.
  $}

  ${
    $d x y $.
    sb6rfv.nf $e |- F/ y ph $.
    $( Reversed substitution.  Version of ~ sb6rf requiring disjoint variables,
       but fewer axioms.  (Contributed by NM, 1-Aug-1993.)  (Revised by Wolf
       Lammen, 7-Feb-2023.) $)
    sb6rfv $p |- ( ph <-> A. y ( y = x -> [ y / x ] ph ) ) $=
      ( weq wsb wi wal sbequ12r equsalv bicomi ) CBEABCFZGCHALACBDACBIJK $.
  $}

  ${
    $d x y z $.  $d y z ph $.
    $( Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ".
       (Contributed by G&eacute;rard Lang, 14-Nov-2013.)  (Revised by Mario
       Carneiro, 6-Oct-2016.)  (Proof shortened by Wolf Lammen, 22-Sep-2018.)
       Avoid ~ ax-13 .  (Revised by Wolf Lammen, 30-Jan-2023.) $)
    sbnf2 $p |- ( F/ x ph
       <-> A. y A. z ( [ y / x ] ph <-> [ z / x ] ph ) ) $=
      ( wnf wa wsb wi wal wb wex nfv sb8ef imbi12i df-nf pm11.53v 3bitr4i alcom
      sb8v bitri anbi12i pm4.24 2albiim ) ABEZUDFABCGZABDGZHDICIZUFUEHZDICIZFUD
      UEUFJDICIUDUGUDUIABKZABIZHZUECKZUFDIZHUDUGUJUMUKUNABCACLMABDSNABOZUEUFCDP
      QUDUHCIDIZUIULUFDKZUECIZHUDUPUJUQUKURABDADLMABCSNUOUFUEDCPQUHDCRTUAUDUBUE
      UFCDUCQ $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( An equivalent expression for existence.  One direction ( ~ exsbim )
       needs fewer axioms.  (Contributed by NM, 2-Feb-2005.)  Avoid ~ ax-13 .
       (Revised by Wolf Lammen, 16-Oct-2022.) $)
    exsb $p |- ( E. x ph <-> E. y A. x ( x = y -> ph ) ) $=
      ( weq wi wal nfv nfa1 ax12v sp com12 impbid cbvexv1 ) ABCDZAEZBFZBCACGOBH
      NAPABCIPNAOBJKLM $.
  $}

  ${
    $d x y z $.  $d y w $.  $d z w ph $.
    $( An equivalent expression for double existence.  (Contributed by NM,
       2-Feb-2005.)  (Proof shortened by Wolf Lammen, 30-Sep-2018.) $)
    2exsb $p |- ( E. x E. y ph <->
                  E. z E. w A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wex wsb weq wa wi wal nfv 2sb8ef 2sb6 2exbii bitri ) ACFBFACEGBDGZEFDFB
      DHCEHIAJCKBKZEFDFABCDEAELADLMQRDEABCDENOP $.
  $}

  ${
    $d y x $.
    sbbib.y $e |- F/ y ph $.
    sbbib.x $e |- F/ x ps $.
    $( Reversal of substitution.  (Contributed by AV, 6-Aug-2023.)  (Proof
       shortened by Wolf Lammen, 4-Sep-2023.) $)
    sbbib $p |- ( A. y ( [ y / x ] ph <-> ps )
              <-> A. x ( ph <-> [ x / y ] ps ) ) $=
      ( wsb wb nfs1v nfbi weq sbequ12r sbequ12 bibi12d cbvalv1 ) ACDGZBHABDCGZH
      DCPBCACDIFJAQDEBDCIJDCKPABQADCLBDCMNO $.
  $}

  ${
    $d x ps $.  $d y ph $.  $d x y $.
    $( Reversal of substitution.  (Contributed by AV, 6-Aug-2023.) $)
    sbbibvv $p |- ( A. y ( [ y / x ] ph <-> ps )
              <-> A. x ( ph <-> [ x / y ] ps ) ) $=
      ( nfv sbbib ) ABCDADEBCEF $.
  $}

  ${
    $d x y w $.  $d ph w $.  $d ps w $.  $d w z $.
    cbvsbvf.1 $e |- F/ y ph $.
    cbvsbvf.2 $e |- F/ x ps $.
    cbvsbvf.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change the bound variable (i.e. the substituted one) in wff's linked by
       implicit substitution.  The proof was part of a former ~ cbvabw version.
       (Contributed by GG and WL, 26-Oct-2024.) $)
    cbvsbvf $p |- ( [ z / x ] ph <-> [ z / y ] ps ) $=
      ( vw weq wi wal wsb nfv nfim equequ1 imbi12d cbvalv1 imbi2i dfsb 3bitr4i
      albii ) IEJZCIJZAKZCLZKZILUCDIJZBKZDLZKZILACEMBDEMUGUKIUFUJUCUEUICDUDADUD
      DNFOUHBCUHCNGOCDJUDUHABCDIPHQRSUBACIETBDIETUA $.
    $( $j usage 'cbvsbvf' avoids 'ax-10' 'ax-13'; $)
  $}

  ${
    $d x z $.  $d y z $.
    $( Alternate proof of ~ cleljust .  It is kept here and should not be
       modified because it is referenced on the Metamath Proof Explorer Home
       Page (mmset.html) as an example of how disjoint variable conditions are
       inherited by substitutions.  (Contributed by NM, 28-Jan-2004.)  (Revised
       by BJ, 29-Dec-2020.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    cleljustALT $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $=
      ( weq wel wa wex ax-5 elequ1 equsexhv bicomi ) CADCBEZFCGABEZLMCAMCHCABIJ
      K $.

    $( Alternate proof of ~ cleljust .  Compared with ~ cleljustALT , it uses
       ~ nfv followed by ~ equsexv instead of ~ ax-5 followed by ~ equsexhv ,
       so it uses the idiom ` F/ x ph ` instead of ` ph -> A. x ph ` to express
       nonfreeness.  This style is generally preferred for later theorems.
       (Contributed by NM, 28-Jan-2004.)  (Revised by Mario Carneiro,
       21-Dec-2016.)  (Revised by BJ, 29-Dec-2020.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    cleljustALT2 $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $=
      ( weq wel wa wex nfv elequ1 equsexv bicomi ) CADCBEZFCGABEZLMCAMCHCABIJK
      $.
  $}

  $( Alternate proof of ~ equs5a .  Uses ~ ax-12 but not ~ ax-13 .
     (Contributed by NM, 2-Feb-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  equs5aALT $p |- ( E. x ( x = y /\ A. y ph ) -> A. x ( x = y -> ph ) ) $=
    ( weq wal wa wi nfa1 ax-12 imp exlimi ) BCDZACEZFLAGZBEZBNBHLMOABCIJK $.

  $( Alternate proof of ~ equs5e .  Uses ~ ax-12 but not ~ ax-13 .
     (Contributed by NM, 2-Feb-2007.)  (Proof shortened by Wolf Lammen,
     15-Jan-2018.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  equs5eALT $p |- ( E. x ( x = y /\ ph ) -> A. x ( x = y -> E. y ph ) ) $=
    ( weq wa wex wi wal nfa1 hbe1 19.23bi ax-12 syl5 imp exlimi ) BCDZAEPACFZGZ
    BHZBRBIPASAQCHZPSATCACJKQBCLMNO $.

  $( Same as ~ axc11 but with reversed antecedent.  Note the use of ~ ax-12
     (and not merely ~ ax12v as in ~ axc11rv ).

     This theorem is mostly used to eliminate conditions requiring set
     variables be distinct (cf. ~ cbvaev and ~ aecom , for example) in proofs.
     In practice, theorems beyond elementary set theory do not really benefit
     from such eliminations.  As of 2024, it is used in conjunction with
     ~ ax-13 only, and like that, it should be applied only in niches where
     indispensable.  (Contributed by NM, 25-Jul-2015.) $)
  axc11r $p |- ( A. y y = x -> ( A. x ph -> A. y ph ) ) $=
    ( weq wal wi ax-12 sps pm2.27 al2imi syld ) CBDZCEABEZLAFZCEZACELMOFCACBGHL
    NACLAIJK $.

  ${
    $d x y $.
    dral1v.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Version of ~ dral1 with a disjoint variable condition, which does not
       require ~ ax-13 .  Remark: the corresponding versions for ~ dral2 and
       ~ drex2 are instances of ~ albidv and ~ exbidv respectively.
       (Contributed by NM, 24-Nov-1994.)  (Revised by BJ, 17-Jun-2019.)  Base
       the proof on ~ ax12v .  (Revised by Wolf Lammen, 30-Mar-2024.)  Avoid
       ~ ax-10 .  (Revised by GG, 18-Nov-2024.) $)
    dral1v $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      ( weq wal hbaev albidh axc11v axc11rv impbid bitrd ) CDFCGZACGBCGZBDGZNAB
      CCDCHEINOPBCDJBCDKLM $.
    $( $j usage 'dral1v' avoids 'ax-10'; $)

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Version of ~ drex1 with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by NM, 27-Feb-2005.)  (Revised by BJ,
       17-Jun-2019.) $)
    drex1v $p |- ( A. x x = y -> ( E. x ph <-> E. y ps ) ) $=
      ( weq wal wn wex notbid dral1v df-ex 3bitr4g ) CDFCGZAHZCGZHBHZDGZHACIBDI
      NPROQCDNABEJKJACLBDLM $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Version of ~ drnf1 with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by Mario Carneiro, 4-Oct-2016.)
       (Revised by BJ, 17-Jun-2019.)  Avoid ~ ax-10 .  (Revised by GG,
       18-Nov-2024.) $)
    drnf1v $p |- ( A. x x = y -> ( F/ x ph <-> F/ y ps ) ) $=
      ( weq wal wex wi wnf drex1v dral1v imbi12d df-nf 3bitr4g ) CDFCGZACHZACGZ
      IBDHZBDGZIACJBDJPQSRTABCDEKABCDELMACNBDNO $.
    $( $j usage 'drnf1v' avoids 'ax-10'; $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-13 (Quantified Equality)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Equality.  One of the equality and substitution axioms
     of predicate calculus with equality.

     An equivalent way to express this axiom that may be easier to understand
     is ` ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ` (see
     ~ ax13b ).  Recall that in the intended interpretation, our variables are
     metavariables ranging over the variables of predicate calculus (the object
     language).  In order for the first antecedent ` -. x = y ` to hold, ` x `
     and ` y ` must have different values and thus cannot be the same
     object-language variable (so they are effectively "distinct variables"
     even though no $d is present).  Similarly, ` x ` and ` z ` cannot be the
     same object-language variable.  Therefore, ` x ` will not occur in the wff
     ` y = z ` when the first two antecedents hold, so analogous to ~ ax-5 ,
     the conclusion ` ( y = z -> A. x y = z ) ` follows.  Note that ~ ax-5
     cannot prove this because its distinct variable ($d) requirement is not
     satisfied directly but only indirectly (outside of Metamath) by the
     argument above.

     The original version of this axiom was ~ ax-c9 and was replaced with this
     shorter ~ ax-13 in December 2015.  The old axiom is proved from this one
     as Theorem ~ axc9 .

     The primary purpose of this axiom is to provide a way to introduce the
     quantifier ` A. x ` on ` y = z ` even when ` x ` and ` y ` are substituted
     with the same variable.  In this case, the first antecedent becomes
     ` -. x = x ` and the axiom still holds.

     This axiom is mostly used to eliminate conditions requiring set variables
     be distinct (cf. ~ ax6ev and ~ ax6e , for example) in proofs.  In
     practice, theorems beyond elementary set theory do not really benefit from
     such eliminations, so direct or indirect application of this axiom is
     discouraged now.  You need to explicitly confirm its use in case you see a
     sensible application in a niche.

     After some assisting contributions by others over the years, it was in
     particular the extensive work of Gino Giotto in 2024 that helped reducing
     dependencies on this axiom on a large scale.

     Although this version is shorter, the original version ~ axc9 may be more
     practical to work with because of the "distinctor" form of its
     antecedents.  A typical application of ~ axc9 is in ~ dvelimh which
     converts a distinct variable pair to the distinctor antecedent
     ` -. A. x x = y ` .  In particular, it is conjectured that it is not
     possible to prove ~ ax6 from ~ ax6v without this axiom.

     This axiom can be weakened if desired by adding distinct variable
     restrictions on pairs ` x , z ` and ` y , z ` .  To show that, we add
     these restrictions to Theorem ~ ax13v and use only ~ ax13v for further
     derivations.  Thus, ~ ax13v should be the only theorem referencing this
     axiom.  Other theorems can reference either ~ ax13v (preferred) or ~ ax13
     (if the stronger form is needed).

     This axiom scheme is logically redundant (see ~ ax13w ) but is used as an
     auxiliary axiom scheme to achieve scheme completeness (i.e. so that all
     possible cases of bundling can be proved; see text linked at
     ~ mmtheorems.html#ax6dgen ).  It is not known whether this axiom can be
     derived from the others.  (Contributed by NM, 21-Dec-2015.)
     (New usage is discouraged.) $)
  ax-13 $a |- ( -. x = y -> ( y = z -> A. x y = z ) ) $.

  ${
    $d x z $.  $d y z $.
    $( A weaker version of ~ ax-13 with distinct variable restrictions on pairs
       ` x , z ` and ` y , z ` .  In order to show (with ~ ax13 ) that this
       weakening is still adequate, this should be the only theorem referencing
       ~ ax-13 directly.

       Had we additionally required ` x ` and ` y ` be distinct, too, this
       theorem would have been a direct consequence of ~ ax-5 .  So essentially
       this theorem states, that a distinct variable condition can be replaced
       with an inequality between set variables.  Preferably, use the version
       ~ ax13w to avoid the propagation of ~ ax-13 .  (Contributed by NM,
       30-Jun-2016.)  (New usage is discouraged.) $)
    ax13v $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
      ( ax-13 ) ABCD $.
  $}

  ${
    $d x z w $.  $d y w $.
    $( A version of ~ ax13v with one distinct variable restriction dropped.
       For convenience, ` y ` is kept on the right side of equations.  The
       proof of ~ ax13 bases on ideas from NM, 24-Dec-2015.  (Contributed by
       Wolf Lammen, 8-Sep-2018.)  (New usage is discouraged.) $)
    ax13lem1 $p |- ( -. x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq wa wex wal equvinva ax13v equeucl alimdv syl9 impd exlimdv syl5
      wn ) CBEZCDEZBDEZFZDGABEQZRAHZCBDIUBUAUCDUBSTUCUBTTAHSUCABDJSTRACBDKLMNOP
      $.
  $}

  ${
    $d x w $.  $d z w $.  $d y w $.
    $( Derive ~ ax-13 from ~ ax13v and Tarski's FOL. This shows that the
       weakening in ~ ax13v is still sufficient for a complete system.
       Preferably, use the weaker ~ ax13w to avoid the propagation of ~ ax-13 .
       (Contributed by NM, 21-Dec-2015.)  (Proof shortened by Wolf Lammen,
       31-Jan-2018.)  Reduce axiom usage.  (Revised by Wolf Lammen,
       2-Jun-2021.)  (New usage is discouraged.) $)
    ax13 $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
      ( vw weq wn wal wi wa wex equvinv ax13lem1 imp ax7v1 alanimi an4s exlimdv
      syl2an ex biimtrid ax13b mpbir ) ABEFZBCEZUDAGZHZHUCACEFZUFHHUCUGUFUDDBEZ
      DCEZIZDJUCUGIZUEBCDKUKUJUEDUKUJUEUCUHUGUIUEUCUHIUHAGZUIAGZUEUGUIIUCUHULAB
      DLMUGUIUMACDLMUHUIUDAUHUIUDDBCNMORPSQTSUEABCUAUB $.
  $}

  ${
    $d w x z $.  $d w y $.
    $( Lemma for ~ nfeqf2 .  This lemma is equivalent to ~ ax13v with one
       distinct variable constraint removed.  (Contributed by Wolf Lammen,
       8-Sep-2018.)  Reduce axiom usage.  (Revised by Wolf Lammen,
       18-Oct-2020.)  (New usage is discouraged.) $)
    ax13lem2 $p |- ( -. x = y -> ( E. x z = y -> z = y ) ) $=
      ( vw weq wn wex wi wal ax13lem1 equeucl eximi 19.36v syl9 alrimdv equequ2
      sylib equsalvw imbitrdi ) ABEFZCBEZAGZDBEZCDEZHZDIUATUBUEDTUCUCAIZUBUDABD
      JUBUEAGUFUDHUAUEACDBKLUCUDAMQNOUDUADBDBCPRS $.
  $}

  ${
    $d x z $.
    $( An equation between setvar is free of any other setvar.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
       Wolf Lammen, 9-Jun-2019.)  Remove dependency on ~ ax-12 .  (Revised by
       Wolf Lammen, 16-Dec-2022.)  (New usage is discouraged.) $)
    nfeqf2 $p |- ( -. A. x x = y -> F/ x z = y ) $=
      ( weq wal wex wnf exnal hbe1 ax13lem2 ax13lem1 syldc eximdh hbe1a syl6com
      wn nfd sylbir ) ABDZAEPSPZAFZCBDZAGSAHUAUBAUBAFZUAUBAEZAFUDUCTUDAUBAITUCU
      BUDABCJABCKLMUBANOQR $.
  $}

  ${
    $d x z $.
    $( Quantifier introduction when one pair of variables is distinct.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 2-Jan-2002.)  (Revised by NM, 20-Jul-2015.)  Remove
       dependency on ~ ax-11 .  (Revised by Wolf Lammen, 8-Sep-2018.)
       (New usage is discouraged.) $)
    dveeq2 $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( weq wal wn nfeqf2 nf5rd ) ABDAEFCBDAABCGH $.
  $}

  ${
    $d x z $.
    $( An equation between setvar is free of any other setvar.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
       Wolf Lammen, 10-Jun-2019.)  (New usage is discouraged.) $)
    nfeqf1 $p |- ( -. A. x x = y -> F/ x y = z ) $=
      ( weq wal wn wnf nfeqf2 equcom nfbii sylib ) ABDAEFCBDZAGBCDZAGABCHLMACBI
      JK $.
  $}

  ${
    $d x z $.
    $( Quantifier introduction when one pair of variables is distinct.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 2-Jan-2002.)  Remove dependency on ~ ax-11 .
       (Revised by Wolf Lammen, 8-Sep-2018.)  (New usage is discouraged.) $)
    dveeq1 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( weq wal wn nfeqf1 nf5rd ) ABDAEFBCDAABCGH $.
  $}

  ${
    $d x w $.  $d y w $.  $d z w $.
    $( A variable is effectively not free in an equality if it is not either of
       the involved variables. ` F/ ` version of ~ ax-c9 .  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
       Mario Carneiro, 6-Oct-2016.)  Remove dependency on ~ ax-11 .  (Revised
       by Wolf Lammen, 6-Sep-2018.)  (New usage is discouraged.) $)
    nfeqf $p |- ( ( -. A. z z = x /\ -. A. z z = y ) -> F/ z x = y ) $=
      ( vw weq wal wn wa nfna1 nfan wex equvinva dveeq1 imp equtr2 alanimi an4s
      syl2an ex exlimdv syl5 nf5d ) CAEZCFGZCBEZCFGZHZABEZCUDUFCUCCIUECIJUHADEZ
      BDEZHZDKUGUHCFZABDLUGUKULDUGUKULUDUIUFUJULUDUIHUICFZUJCFZULUFUJHUDUIUMCAD
      MNUFUJUNCBDMNUIUJUHCABDOPRQSTUAUB $.
  $}

  $( Derive set.mm's original ~ ax-c9 from the shorter ~ ax-13 .  Usage is
     discouraged to avoid uninformed ~ ax-13 propagation.  (Contributed by NM,
     29-Nov-2015.)  (Revised by NM, 24-Dec-2015.)  (Proof shortened by Wolf
     Lammen, 29-Apr-2018.)  (New usage is discouraged.) $)
  axc9 $p |- ( -. A. z z = x -> ( -. A. z z = y
              -> ( x = y -> A. z x = y ) ) ) $=
    ( weq wal wn wi wa nfeqf nf5rd ex ) CADCEFZCBDCEFZABDZNCEGLMHNCABCIJK $.

  ${
    $d y w $.  $d x w $.
    $( At least one individual exists.  This is not a theorem of free logic,
       which is sound in empty domains.  For such a logic, we would add this
       theorem as an axiom of set theory (Axiom 0 of [Kunen] p. 10).  In the
       system consisting of ~ ax-4 through ~ ax-9 , all axioms other than
       ~ ax-6 are believed to be theorems of free logic, although the system
       without ~ ax-6 is not complete in free logic.

       Usage of this theorem is discouraged because it depends on ~ ax-13 .  It
       is preferred to use ~ ax6ev when it is sufficient.  (Contributed by NM,
       14-May-1993.)  Shortened after ~ ax13lem1 became available.  (Revised by
       Wolf Lammen, 8-Sep-2018.)  (New usage is discouraged.) $)
    ax6e $p |- E. x x = y $=
      ( vw weq wex 19.8a wn wi wal ax13lem1 ax6ev equtr eximii syl6com exlimiiv
      19.35i pm2.61i ) ABDZRAEZRAFCBDZRGZSHCUATTAISABCJTRAACDTRHAACKACBLMPNCBKO
      Q $.
  $}

  $( Theorem showing that ~ ax-6 follows from the weaker version ~ ax6v .
     (Even though this theorem depends on ~ ax-6 , all references of ~ ax-6 are
     made via ~ ax6v .  An earlier version stated ~ ax6v as a separate axiom,
     but having two axioms caused some confusion.)

     This theorem should be referenced in place of ~ ax-6 so that all proofs
     can be traced back to ~ ax6v .  When possible, use the weaker ~ ax6v
     rather than ~ ax6 since the ~ ax6v derivation is much shorter and requires
     fewer axioms.  (Contributed by NM, 12-Nov-2013.)  (Revised by NM,
     25-Jul-2015.)  (Proof shortened by Wolf Lammen, 4-Feb-2018.)  Usage of
     this theorem is discouraged because it depends on ~ ax-13 .  Use ~ ax6v
     instead.  (New usage is discouraged.) $)
  ax6 $p |- -. A. x -. x = y $=
    ( weq wex wn wal ax6e df-ex mpbi ) ABCZADJEAFEABGJAHI $.

  $( Show that the original axiom ~ ax-c10 can be derived from ~ ax6 and ~ axc7
     (on top of propositional calculus, ~ ax-gen , and ~ ax-4 ).  See
     ~ ax6fromc10 for the rederivation of ~ ax6 from ~ ax-c10 .

     Normally, ~ axc10 should be used rather than ~ ax-c10 , except by theorems
     specifically studying the latter's properties.  See ~ bj-axc10v for a
     weaker version requiring fewer axioms.  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  Usage of this theorem is discouraged
     because it depends on ~ ax-13 .  (New usage is discouraged.) $)
  axc10 $p |- ( A. x ( x = y -> A. x ph ) -> ph ) $=
    ( weq wal wi wn ax6 con3 al2imi mtoi axc7 syl ) BCDZABEZFZBEZOGZBEZGAQSNGZB
    EBCHPRTBNOIJKABLM $.

  $( Closed theorem form of ~ spim .  (Contributed by NM, 15-Jan-2008.)
     (Revised by Mario Carneiro, 17-Oct-2016.)  (Proof shortened by Wolf
     Lammen, 21-Mar-2023.)  Usage of this theorem is discouraged because it
     depends on ~ ax-13 .  (New usage is discouraged.) $)
  spimt $p |- ( ( F/ x ps /\ A. x ( x = y -> ( ph -> ps ) ) ) ->
                                                         ( A. x ph -> ps ) ) $=
    ( weq wi wal wex wnf ax6e exim mpi 19.35 sylib id 19.9d sylan9r ) CDEZABFZF
    CGZACGZBCHZBCIZBTSCHZUAUBFTRCHUDCDJRSCKLABCMNBUCCUCOPQ $.

  ${
    spim.1 $e |- F/ x ps $.
    spim.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, using implicit substitution.  Compare Lemma 14 of
       [Tarski] p. 70.  The ~ spim series of theorems requires that only one
       direction of the substitution hypothesis hold.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  See ~ spimw for a version
       requiring fewer axioms.  (Contributed by NM, 10-Jan-1993.)  (Revised by
       Mario Carneiro, 3-Oct-2016.)  (Proof shortened by Wolf Lammen,
       18-Feb-2018.)  (New usage is discouraged.) $)
    spim $p |- ( A. x ph -> ps ) $=
      ( weq wi ax6e eximii 19.36i ) ABCECDGABHCCDIFJK $.
  $}

  ${
    spimed.1 $e |- ( ch -> F/ x ph ) $.
    spimed.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Deduction version of ~ spime .  (Contributed by NM, 14-May-1993.)
       (Revised by Mario Carneiro, 3-Oct-2016.)  (Proof shortened by Wolf
       Lammen, 19-Feb-2018.)  Usage of this theorem is discouraged because it
       depends on ~ ax-13 .  Use ~ spimedv instead.
       (New usage is discouraged.) $)
    spimed $p |- ( ch -> ( ph -> E. x ps ) ) $=
      ( wal wex nf5rd weq wi ax6e eximii 19.35i syl6 ) CAADHBDICADFJABDDEKABLDD
      EMGNOP $.
  $}

  ${
    spime.1 $e |- F/ x ph $.
    spime.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Existential introduction, using implicit substitution.  Compare Lemma 14
       of [Tarski] p. 70.  See ~ spimew and ~ spimevw for weaker versions
       requiring fewer axioms.  (Contributed by NM, 7-Aug-1994.)  (Revised by
       Mario Carneiro, 3-Oct-2016.)  (Proof shortened by Wolf Lammen,
       6-Mar-2018.)  Usage of this theorem is discouraged because it depends on
       ~ ax-13 .  Use ~ spimefv instead.  (New usage is discouraged.) $)
    spime $p |- ( ph -> E. x ps ) $=
      ( wex wi wtru wnf a1i spimed mptru ) ABCGHABICDACJIEKFLM $.
  $}

  ${
    $d x ps $.
    spimv.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( A version of ~ spim with a distinct variable requirement instead of a
       bound-variable hypothesis.  See ~ spimfv and ~ spimvw for versions
       requiring fewer axioms.  (Contributed by NM, 31-Jul-1993.)  Usage of
       this theorem is discouraged because it depends on ~ ax-13 .  Use
       ~ spimvw instead.  (New usage is discouraged.) $)
    spimv $p |- ( A. x ph -> ps ) $=
      ( nfv spim ) ABCDBCFEG $.

    $( Alternate proof of ~ spimv .  Note that it requires only ~ ax-1 through
       ~ ax-5 together with ~ ax6e .  Currently, proofs derive from ~ ax6v ,
       but if ~ ax-6 could be used instead, this proof would reduce axiom
       usage.  (Contributed by NM, 31-Jul-1993.)  Remove dependency on
       ~ ax-10 .  (Revised by BJ, 29-Nov-2020.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    spimvALT $p |- ( A. x ph -> ps ) $=
      ( weq wi ax6e eximii 19.36iv ) ABCCDFABGCCDHEIJ $.
  $}

  ${
    $d x ph $.
    spimev.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Distinct-variable version of ~ spime .  (Contributed by NM,
       10-Jan-1993.)  Usage of this theorem is discouraged because it depends
       on ~ ax-13 .  Use ~ spimevw instead.  (New usage is discouraged.) $)
    spimev $p |- ( ph -> E. x ps ) $=
      ( nfv spime ) ABCDACFEG $.
  $}

  ${
    $d x ps $.
    spv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Specialization, using implicit substitution.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  Use the weaker ~ spvv if
       possible.  (Contributed by NM, 30-Aug-1993.)
       (New usage is discouraged.) $)
    spv $p |- ( A. x ph -> ps ) $=
      ( weq biimpd spimv ) ABCDCDFABEGH $.
  $}

  ${
    spei.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    spei.2 $e |- ps $.
    $( Inference from existential specialization, using implicit substitution.
       Remove a distinct variable constraint.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  Use the weaker ~ speiv if
       possible.  (Contributed by NM, 19-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 12-May-2018.)  (New usage is discouraged.) $)
    spei $p |- E. x ph $=
      ( weq ax6e mpbiri eximii ) CDGZACCDHKABFEIJ $.
  $}

  ${
    chvar.1 $e |- F/ x ps $.
    chvar.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chvar.3 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  Use the weaker
       ~ chvarfv if possible.  (Contributed by Raph Levien, 9-Jul-2003.)
       (Revised by Mario Carneiro, 3-Oct-2016.)  (New usage is discouraged.) $)
    chvar $p |- ps $=
      ( weq biimpd spim mpg ) ABCABCDECDHABFIJGK $.
  $}

  ${
    $d x ps $.
    chvarv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chvarv.2 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  Use the weaker
       ~ chvarvv if possible.  (Contributed by NM, 20-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 22-Apr-2018.)  (New usage is discouraged.) $)
    chvarv $p |- ps $=
      ( nfv chvar ) ABCDBCGEFH $.
  $}

  ${
    cbv3.1 $e |- F/ y ph $.
    cbv3.2 $e |- F/ x ps $.
    cbv3.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution, that
       does not use ~ ax-c9 .  Usage of this theorem is discouraged because it
       depends on ~ ax-13 .  Use the weaker ~ cbv3v if possible.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-May-2018.)
       (New usage is discouraged.) $)
    cbv3 $p |- ( A. x ph -> A. y ps ) $=
      ( wal nf5ri hbal spim alrimih ) ACHBDADCADEIJABCDFGKL $.
  $}

  ${
    cbval.1 $e |- F/ y ph $.
    cbval.2 $e |- F/ x ps $.
    cbval.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  Check
       out ~ cbvalw , ~ cbvalvw , ~ cbvalv1 for versions requiring fewer
       axioms.  (Contributed by NM, 13-May-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.)  (New usage is discouraged.) $)
    cbval $p |- ( A. x ph <-> A. y ps ) $=
      ( wal weq biimpd cbv3 wi biimprd equcoms impbii ) ACHBDHABCDEFCDIZABGJKBA
      DCFEBALCDPABGMNKO $.

    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  Check
       out ~ cbvexvw , ~ cbvexv1 for weaker versions requiring fewer axioms.
       (Contributed by NM, 21-Jun-1993.)  (New usage is discouraged.) $)
    cbvex $p |- ( E. x ph <-> E. y ps ) $=
      ( wex wn wal nfn weq notbid cbval alnex 3bitr3i con4bii ) ACHZBDHZAIZCJBI
      ZDJRISITUACDADEKBCFKCDLABGMNACOBDOPQ $.
  $}

  ${
    $d y ph $.  $d x ps $.
    cbvalv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  See
       ~ cbvalvw for a version requiring fewer axioms, to be preferred when
       sufficient.  (Contributed by NM, 5-Aug-1993.)  Remove dependency on
       ~ ax-10 and shorten proof.  (Revised by Wolf Lammen, 11-Sep-2023.)
       (New usage is discouraged.) $)
    cbvalv $p |- ( A. x ph <-> A. y ps ) $=
      ( nfv cbval ) ABCDADFBCFEG $.

    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  See
       ~ cbvexvw for a version requiring fewer axioms, to be preferred when
       sufficient.  (Contributed by NM, 21-Jun-1993.)  Remove dependency on
       ~ ax-10 and shorten proof.  (Revised by Wolf Lammen, 11-Sep-2023.)
       (New usage is discouraged.) $)
    cbvexv $p |- ( E. x ph <-> E. y ps ) $=
      ( nfv cbvex ) ABCDADFBCFEG $.
  $}

  ${
    cbv1.1 $e |- F/ x ph $.
    cbv1.2 $e |- F/ y ph $.
    cbv1.3 $e |- ( ph -> F/ y ps ) $.
    cbv1.4 $e |- ( ph -> F/ x ch ) $.
    cbv1.5 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  See
       ~ cbv1v with disjoint variable conditions, not depending on ~ ax-13 .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.)  Format hypotheses to common style.  (Revised by Wolf
       Lammen, 13-May-2018.)  (New usage is discouraged.) $)
    cbv1 $p |- ( ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal wi nfim1 weq com12 a2d cbv3 19.21 3imtr3i pm2.86i ) ABDKZCEKZABLZDK
      ACLZEKAUALAUBLUCUDDEABEGHMACDFIMDENZABCAUEBCLJOPQABDFRACEGRST $.
  $}

  ${
    cbv2.1 $e |- F/ x ph $.
    cbv2.2 $e |- F/ y ph $.
    cbv2.3 $e |- ( ph -> F/ y ps ) $.
    cbv2.4 $e |- ( ph -> F/ x ch ) $.
    cbv2.5 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  See
       ~ cbv2w with disjoint variable conditions, not depending on ~ ax-13 .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.)  Format hypotheses to common style, avoid ~ ax-10 .
       (Revised by Wolf Lammen, 10-Sep-2023.)  (New usage is discouraged.) $)
    cbv2 $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal weq wb wi biimp syl6 cbv1 equcomi biimpr syl56 impbid ) ABDKCEKABCD
      EFGHIADELZBCMZBCNJBCOPQACBEDGFIHEDLUBAUCCBNEDRJBCSTQUA $.
    $( $j usage 'cbv2' avoids 'ax-10'; $)
  $}

  ${
    cbv3h.1 $e |- ( ph -> A. y ph ) $.
    cbv3h.2 $e |- ( ps -> A. x ps ) $.
    cbv3h.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  Use the
       weaker ~ cbv3hv if possible.  (Contributed by NM, 8-Jun-1993.)  (Proof
       shortened by Andrew Salmon, 25-May-2011.)  (Proof shortened by Wolf
       Lammen, 12-May-2018.)  (New usage is discouraged.) $)
    cbv3h $p |- ( A. x ph -> A. y ps ) $=
      ( nf5i cbv3 ) ABCDADEHBCFHGI $.
  $}

  ${
    cbv1h.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbv1h.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    cbv1h.3 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 11-May-1993.)  (Proof shortened by Wolf Lammen,
       13-May-2018.)  (New usage is discouraged.) $)
    cbv1h $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal nfa1 nfa2 wi 2sp syl nf5d weq cbv1 ) AEIZDIZBCDERDJZAEDKZSBEUASABBE
      ILADEMZFNOSCDTSACCDILUBGNOSADEPBCLLUBHNQ $.
  $}

  ${
    cbv2h.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbv2h.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    cbv2h.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 11-May-1993.)  (New usage is discouraged.) $)
    cbv2h $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal weq wb wi biimp syl6 cbv1h equcomi biimpr syl56 alcoms impbid ) AEI
      DIBDIZCEIZABCDEFGADEJZBCKZBCLHBCMNOAUBUALEDACBEDGFEDJUCAUDCBLEDPHBCQROST
      $.
  $}

  ${
    $d x ph $.  $d x ch $.
    cbvald.1 $e |- F/ y ph $.
    cbvald.2 $e |- ( ph -> F/ y ps ) $.
    cbvald.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Deduction used to change bound variables, using implicit substitution,
       particularly useful in conjunction with ~ dvelim .  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  See ~ cbvaldw
       for a version with ` x , y ` disjoint, not depending on ~ ax-13 .
       (Contributed by NM, 2-Jan-2002.)  (Revised by Mario Carneiro,
       6-Oct-2016.)  (Revised by Wolf Lammen, 13-May-2018.)
       (New usage is discouraged.) $)
    cbvald $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( nfv nfvd cbv2 ) ABCDEADIFGACDJHK $.

    $( Deduction used to change bound variables, using implicit substitution,
       particularly useful in conjunction with ~ dvelim .  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  Use the weaker
       ~ cbvexdw if possible.  (Contributed by NM, 2-Jan-2002.)  (Revised by
       Mario Carneiro, 6-Oct-2016.)  (New usage is discouraged.) $)
    cbvexd $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( wex wn wal nfnd weq wb notbi imbitrdi cbvald alnex 3bitr3g con4bid ) AB
      DIZCEIZABJZDKCJZEKUAJUBJAUCUDDEFABEGLADEMBCNUCUDNHBCOPQBDRCERST $.
  $}

  ${
    $d ps y $.  $d ch x $.  $d ph x $.  $d ph y $.
    cbvaldva.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Rule used to change the bound variable in a universal quantifier with
       implicit substitution.  Deduction form.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  Use the weaker ~ cbvaldvaw
       if possible.  (Contributed by David Moews, 1-May-2017.)
       (New usage is discouraged.) $)
    cbvaldva $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( nfv nfvd weq wb ex cbvald ) ABCDEAEGABEHADEIBCJFKL $.

    $( Rule used to change the bound variable in an existential quantifier with
       implicit substitution.  Deduction form.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  Use the weaker ~ cbvexdvaw
       if possible.  (Contributed by David Moews, 1-May-2017.)
       (New usage is discouraged.) $)
    cbvexdva $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( nfv nfvd weq wb ex cbvexd ) ABCDEAEGABEHADEIBCJFKL $.
  $}

  ${
    $d y x $.  $d y z $.  $d w x $.  $d w z $.
    cbval2.1 $e |- F/ z ph $.
    cbval2.2 $e |- F/ w ph $.
    cbval2.3 $e |- F/ x ps $.
    cbval2.4 $e |- F/ y ps $.
    cbval2.5 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  Use the
       weaker ~ cbval2v if possible.  (Contributed by NM, 22-Dec-2003.)
       (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof shortened by Wolf
       Lammen, 11-Sep-2023.)  (New usage is discouraged.) $)
    cbval2 $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( wal nfal weq nfv wnf a1i wb ex cbv2 cbval ) ADLBFLCEAEDGMBCFIMCENZABDFU
      BDOUBFOAFPUBHQBDPUBJQUBDFNABRKSTUA $.

    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  Use the
       weaker ~ cbvex2v if possible.  (Contributed by NM, 14-Sep-2003.)
       (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof shortened by Wolf
       Lammen, 16-Jun-2019.)  (New usage is discouraged.) $)
    cbvex2 $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( wex wn wal nfn weq wa notbid cbval2 2nexaln 3bitr4i con4bii ) ADLCLZBFL
      ELZAMZDNCNBMZFNENUCMUDMUEUFCDEFAEGOAFHOBCIOBDJOCEPDFPQABKRSACDTBEFTUAUB
      $.
  $}

  ${
    $d z w ph $.  $d x y ps $.  $d x w $.  $d z y $.
    cbval2vv.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  Use the
       weaker ~ cbval2vw if possible.  (Contributed by NM, 4-Feb-2005.)  Remove
       dependency on ~ ax-10 .  (Revised by Wolf Lammen, 18-Jul-2021.)
       (New usage is discouraged.) $)
    cbval2vv $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( wal weq cbvaldva cbvalv ) ADHBFHCECEIABDFGJK $.

    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  Use the
       weaker ~ cbvex2vw if possible.  (Contributed by NM, 26-Jul-1995.)
       Remove dependency on ~ ax-10 .  (Revised by Wolf Lammen, 18-Jul-2021.)
       (New usage is discouraged.) $)
    cbvex2vv $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( wex weq cbvexdva cbvexv ) ADHBFHCECEIABDFGJK $.
  $}

  ${
    $v f $.
    $v g $.
    $( Define temporary individual variables. $)
    cbvex4v.vf $f setvar f $.
    cbvex4v.vg $f setvar g $.
    $d w z ch $.  $d u v ph $.  $d x y ps $.  $d f g ps $.  $d f w $.
    $d g z $.  $d u v w z $.  $d u w x z $.  $d v w y z $.  $d w x y z $.
    cbvex4v.1 $e |- ( ( x = v /\ y = u ) -> ( ph <-> ps ) ) $.
    cbvex4v.2 $e |- ( ( z = f /\ w = g ) -> ( ps <-> ch ) ) $.
    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  Use the
       weaker ~ cbvex4vw if possible.  (Contributed by NM, 26-Jul-1995.)
       (New usage is discouraged.) $)
    cbvex4v $p |- ( E. x E. y E. z E. w ph <-> E. v E. u E. f E. g ch ) $=
      ( wex weq wa 2exbidv cbvex2vv 2exbii bitri ) AGNFNZENDNBGNFNZINHNCKNJNZIN
      HNUAUBDEHIDHOEIOPABFGLQRUBUCHIBCFGJKMRST $.
  $}

  $( Lemma used in proofs of implicit substitution properties.  The converse
     requires either a disjoint variable condition ( ~ sbalex ) or a
     nonfreeness hypothesis ( ~ equs45f ).  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  See ~ equs4v for a weaker
     version requiring fewer axioms.  (Contributed by NM, 10-May-1993.)  (Proof
     shortened by Mario Carneiro, 20-May-2014.)  (Proof shortened by Wolf
     Lammen, 5-Feb-2018.)  (New usage is discouraged.) $)
  equs4 $p |- ( A. x ( x = y -> ph ) -> E. x ( x = y /\ ph ) ) $=
    ( weq wi wal wex wa ax6e exintr mpi ) BCDZAEBFLBGLAHBGBCILABJK $.

  ${
    equsal.1 $e |- F/ x ps $.
    equsal.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( An equivalence related to implicit substitution.  Usage of this theorem
       is discouraged because it depends on ~ ax-13 .  See ~ equsalvw and
       ~ equsalv for versions with disjoint variable conditions proved from
       fewer axioms.  See also the dual form ~ equsex .  (Contributed by NM,
       2-Jun-1993.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.)  (Revised
       by Mario Carneiro, 3-Oct-2016.)  (Proof shortened by Wolf Lammen,
       5-Feb-2018.)  (New usage is discouraged.) $)
    equsal $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal wex 19.23 pm5.74i albii ax6e a1bi 3bitr4i ) CDGZBHZCIQCJZBHQ
      AHZCIBQBCEKTRCQABFLMSBCDNOP $.

    $( An equivalence related to implicit substitution.  Usage of this theorem
       is discouraged because it depends on ~ ax-13 .  See ~ equsexvw and
       ~ equsexv for versions with disjoint variable conditions proved from
       fewer axioms.  See also the dual form ~ equsal .  See ~ equsexALT for an
       alternate proof.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario
       Carneiro, 3-Oct-2016.)  (Proof shortened by Wolf Lammen, 6-Feb-2018.)
       (New usage is discouraged.) $)
    equsex $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( weq wa wex biimpa exlimi wi wal equsal equs4 sylbir impbii ) CDGZAHZCIZ
      BSBCERABFJKBRALCMTABCDEFNACDOPQ $.

    $( Alternate proof of ~ equsex .  This proves the result directly, instead
       of as a corollary of ~ equsal via ~ equs4 .  Note in particular that
       only existential quantifiers appear in the proof and that the only step
       requiring ~ ax-13 is ~ ax6e .  This proof mimics that of ~ equsal (in
       particular, note that ~ pm5.32i , ~ exbii , ~ 19.41 , ~ mpbiran
       correspond respectively to ~ pm5.74i , ~ albii , ~ 19.23 , ~ a1bi ).
       (Contributed by BJ, 20-Aug-2020.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    equsexALT $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( weq wa wex pm5.32i exbii ax6e 19.41 mpbiran bitri ) CDGZAHZCIPBHZCIZBQR
      CPABFJKSPCIBCDLPBCEMNO $.
  $}

  ${
    equsalh.1 $e |- ( ps -> A. x ps ) $.
    equsalh.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( An equivalence related to implicit substitution.  Usage of this theorem
       is discouraged because it depends on ~ ax-13 .  See ~ equsalhw for a
       version with a disjoint variable condition requiring fewer axioms.
       (Contributed by NM, 2-Jun-1993.)  (New usage is discouraged.) $)
    equsalh $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( nf5i equsal ) ABCDBCEGFH $.

    $( An equivalence related to implicit substitution.  Usage of this theorem
       is discouraged because it depends on ~ ax-13 .  See ~ equsexhv for a
       version with a disjoint variable condition which does not require
       ~ ax-13 .  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)
    equsexh $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( nf5i equsex ) ABCDBCEGFH $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( Derivation of set.mm's original ~ ax-c15 from ~ ax-c11n and the shorter
       ~ ax-12 that has replaced it.

       Theorem ~ ax12 shows the reverse derivation of ~ ax-12 from ~ ax-c15 .

       Normally, ~ axc15 should be used rather than ~ ax-c15 , except by
       theorems specifically studying the latter's properties.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
       NM, 2-Feb-2007.)  (Proof shortened by Wolf Lammen, 26-Mar-2023.)
       (New usage is discouraged.) $)
    axc15 $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( vz weq wal wn wex ax6ev dveeq2 ax12v equeuclr sps imim1d al2imi imim12d
      wi imim2d syl6mpi exlimdv mpi ) BCEZBFGZDCEZDHUBAUBAQZBFZQZQZDCIUCUDUHDUC
      UDUDBFZBDEZAUJAQZBFZQZQUHBCDJABDKUIUBUJUMUGUDUBUJQBDBCLZMUIULUFAUDUKUEBUD
      UBUJAUNNORPSTUA $.
  $}

  $( Rederivation of Axiom ~ ax-12 from ~ ax12v (used only via ~ sp ),
     ~ axc11r , and ~ axc15 (on top of Tarski's FOL).  Since this version
     depends on ~ ax-13 , usage of the weaker ~ ax12v , ~ ax12w , ~ ax12i are
     preferred.  (Contributed by NM, 22-Jan-2007.)  Proof uses contemporary
     axioms.  (Revised by Wolf Lammen, 8-Aug-2020.)  (Proof shortened by BJ,
     4-Jul-2021.)  (New usage is discouraged.) $)
  ax12 $p |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wi axc11r ala1 syl6 a1d wn sp axc15 syl7 pm2.61i ) BCDZBEZPACEZPA
    FBEZFZFQTPQRABESACBGAPBHIJRAQKPSACLABCMNO $.

  $( A bidirectional version of ~ axc15 .  Usage of this theorem is discouraged
     because it depends on ~ ax-13 .  (Contributed by NM, 30-Jun-2006.)
     (New usage is discouraged.) $)
  ax12b $p |- ( ( -. A. x x = y /\ x = y ) ->
              ( ph <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wa wi axc15 imp sp com12 adantl impbid ) BCDZBEFZOGAOAHZBEZPOA
    RHABCIJORAHPROAQBKLMN $.

  $( Alternate proof of ~ ax13 from FOL, ~ sp , and ~ axc9 .  (Contributed by
     NM, 21-Dec-2015.)  (Proof shortened by Wolf Lammen, 31-Jan-2018.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax13ALT $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
    ( weq wn wal wi sp con3i axc9 syl2im ax13b mpbir ) ABDZEZBCDZPAFZGZGOACDZEZ
    RGGONAFZETSAFZERUANNAHIUBSSAHIBCAJKQABCLM $.

  ${
    $d x z $.  $d y z $.
    $( Derive set.mm's original ~ ax-c11n from others.  Commutation law for
       identical variable specifiers.  The antecedent and consequent are true
       when ` x ` and ` y ` are substituted with the same variable.  Lemma L12
       in [Megill] p. 445 (p. 12 of the preprint).  If a disjoint variable
       condition is added on ` x ` and ` y ` , then this becomes an instance of
       ~ aevlem .  Use ~ aecom instead when this does not lengthen the proof.
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 10-May-1993.)  (Revised by NM, 7-Nov-2015.)  (Proof
       shortened by Wolf Lammen, 6-Mar-2018.)  (Revised by Wolf Lammen,
       30-Nov-2019.)  (Proof shortened by BJ, 29-Mar-2021.)  (Proof shortened
       by Wolf Lammen, 2-Jul-2021.)  (New usage is discouraged.) $)
    axc11n $p |- ( A. x x = y -> A. y y = x ) $=
      ( vz weq wal wn dveeq1 com12 axc11r aev syl6 syl9 ax6evr exlimiiv pm2.18d
      wi ) ABDAEZBADBEZACDZQRFZRPPCSTSBEZQRTSUABACGHQUASAERSBAIACBABJKLCAMNO $.
  $}

  $( Commutation law for identical variable specifiers.  Both sides of the
     biconditional are true when ` x ` and ` y ` are substituted with the same
     variable.  Usage of this theorem is discouraged because it depends on
     ~ ax-13 .  (Contributed by NM, 10-May-1993.)  Change to a biconditional.
     (Revised by BJ, 26-Sep-2019.)  (New usage is discouraged.) $)
  aecom $p |- ( A. x x = y <-> A. y y = x ) $=
    ( weq wal axc11n impbii ) ABCADBACBDABEBAEF $.

  ${
    aecoms.1 $e |- ( A. x x = y -> ph ) $.
    $( A commutation rule for identical variable specifiers.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
       NM, 10-May-1993.)  (New usage is discouraged.) $)
    aecoms $p |- ( A. y y = x -> ph ) $=
      ( weq wal aecom sylbi ) CBECFBCEBFACBGDH $.
  $}

  ${
    naecoms.1 $e |- ( -. A. x x = y -> ph ) $.
    $( A commutation rule for distinct variable specifiers.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
       NM, 2-Jan-2002.)  (New usage is discouraged.) $)
    naecoms $p |- ( -. A. y y = x -> ph ) $=
      ( weq wal aecom sylnbir ) CBECFBCEBFABCGDH $.
  $}

  $( Show that ~ ax-c11 can be derived from ~ ax-c11n in the form of ~ axc11n .
     Normally, ~ axc11 should be used rather than ~ ax-c11 , except by theorems
     specifically studying the latter's properties.  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  Use the weaker ~ axc11v when
     possible.  (Contributed by NM, 16-May-2008.)  (Proof shortened by Wolf
     Lammen, 21-Apr-2018.)  (New usage is discouraged.) $)
  axc11 $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $=
    ( wal wi axc11r aecoms ) ABDACDECBABCFG $.

  $( All variables are effectively bound in an identical variable specifier.
     Usage of this theorem is discouraged because it depends on ~ ax-13 .  Use
     the weaker ~ hbaev when possible.  (Contributed by NM, 13-May-1993.)
     (Proof shortened by Wolf Lammen, 21-Apr-2018.)
     (New usage is discouraged.) $)
  hbae $p |- ( A. x x = y -> A. z A. x x = y ) $=
    ( weq wal wi wn sp axc9 syl7 axc11r axc11 pm2.43i syl5 pm2.61ii axc4i ax-11
    syl ) ABDZAEZSCEZAETCESUAACADCEZCBDCEZTUAFTSUBGUCGUASAHABCIJSACKTSBEZUCUATU
    DSABLMSBCKNOPSACQR $.

  $( All variables are effectively bound in a distinct variable specifier.
     Lemma L19 in [Megill] p. 446 (p. 14 of the preprint).  Usage of this
     theorem is discouraged because it depends on ~ ax-13 .  Use the weaker
     ~ hbnaev when possible.  (Contributed by NM, 13-May-1993.)
     (New usage is discouraged.) $)
  hbnae $p |- ( -. A. x x = y -> A. z -. A. x x = y ) $=
    ( weq wal hbae hbn ) ABDAECABCFG $.

  $( All variables are effectively bound in an identical variable specifier.
     Usage of this theorem is discouraged because it depends on ~ ax-13 .
     (Contributed by Mario Carneiro, 11-Aug-2016.)
     (New usage is discouraged.) $)
  nfae $p |- F/ z A. x x = y $=
    ( weq wal hbae nf5i ) ABDAECABCFG $.

  $( All variables are effectively bound in a distinct variable specifier.
     Usage of this theorem is discouraged because it depends on ~ ax-13 .  Use
     the weaker ~ nfnaew when possible.  (Contributed by Mario Carneiro,
     11-Aug-2016.)  (New usage is discouraged.) $)
  nfnae $p |- F/ z -. A. x x = y $=
    ( weq wal nfae nfn ) ABDAECABCFG $.

  ${
    hbnaes.1 $e |- ( A. z -. A. x x = y -> ph ) $.
    $( Rule that applies ~ hbnae to antecedent.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  (Contributed by NM,
       15-May-1993.)  (New usage is discouraged.) $)
    hbnaes $p |- ( -. A. x x = y -> ph ) $=
      ( weq wal wn hbnae syl ) BCFBGHZKDGABCDIEJ $.
  $}

  ${
    $d x y z $.  $d z ph $.
    axc16i.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    axc16i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference with ~ axc16 as its conclusion.  (Contributed by NM,
       20-May-2008.)  (Proof modification is discouraged.)  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  Use ~ axc16
       instead.  (New usage is discouraged.) $)
    axc16i $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( weq wal wi nfv ax7 cbv3 spimvw equcomi syl syl5com alimdv mpcom alimi
      biimpcd nf5i biimprd syl6com 3syl ) CDHZCIEDHZEIZCEHZEIZAACIZJUFUGCEUFEKU
      GCKCEDLMUHECHZEIZUJUFUHUMUGUFECECDLNUFUGULEUFDCHZUGULCDOUGDEHUNULJEDODECL
      PQRSULUIEECOZTPAUJBEIUKAUIBEUIABFUARBAECBCGUBAEKULUIBAJUOUIABFUCPMUDUE $.
  $}

  ${
    $d x y $.
    $( Alternate proof of ~ axc16nf , shorter but requiring ~ ax-11 and
       ~ ax-13 .  (Contributed by Mario Carneiro, 7-Oct-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    axc16nfALT $p |- ( A. x x = y -> F/ z ph ) $=
      ( weq wal nfae axc16g nf5d ) BCEBFADBCDGABCDHI $.
  $}

  ${
    dral1.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Usage of
       this theorem is discouraged because it depends on ~ ax-13 .  Usage of
       ~ albidv is preferred, which requires fewer axioms.  (Contributed by NM,
       27-Feb-2005.)  Allow a shortening of ~ dral1 .  (Revised by Wolf Lammen,
       4-Mar-2018.)  (New usage is discouraged.) $)
    dral2 $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $=
      ( weq wal nfae albid ) CDGCHABECDEIFJ $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Usage of
       this theorem is discouraged because it depends on ~ ax-13 .  Use the
       weaker ~ dral1v if possible.  (Contributed by NM, 24-Nov-1994.)  Remove
       dependency on ~ ax-11 .  (Revised by Wolf Lammen, 6-Sep-2018.)
       (New usage is discouraged.) $)
    dral1 $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      ( weq wal nfa1 albid axc11 axc11r impbid bitrd ) CDFZCGZACGBCGZBDGZOABCNC
      HEIOPQBCDJBDCKLM $.

    $( Alternate proof of ~ dral1 , shorter but requiring ~ ax-11 .
       (Contributed by NM, 24-Nov-1994.)  (Proof shortened by Wolf Lammen,
       22-Apr-2018.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    dral1ALT $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      ( weq wal dral2 axc11 axc11r impbid bitrd ) CDFCGZACGBCGZBDGZABCDCEHMNOBC
      DIBDCJKL $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Usage of
       this theorem is discouraged because it depends on ~ ax-13 .  Use the
       weaker ~ drex1v if possible.  (Contributed by NM, 27-Feb-2005.)
       (New usage is discouraged.) $)
    drex1 $p |- ( A. x x = y -> ( E. x ph <-> E. y ps ) ) $=
      ( weq wal wn wex notbid dral1 df-ex 3bitr4g ) CDFCGZAHZCGZHBHZDGZHACIBDIN
      PROQCDNABEJKJACLBDLM $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Usage of
       this theorem is discouraged because it depends on ~ ax-13 .  Usage of
       ~ exbidv is preferred, which requires fewer axioms.  (Contributed by NM,
       27-Feb-2005.)  (New usage is discouraged.) $)
    drex2 $p |- ( A. x x = y -> ( E. z ph <-> E. z ps ) ) $=
      ( weq wal nfae exbid ) CDGCHABECDEIFJ $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 4-Oct-2016.)  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  Use ~ drnf1v instead.
       (New usage is discouraged.) $)
    drnf1 $p |- ( A. x x = y -> ( F/ x ph <-> F/ y ps ) ) $=
      ( weq wal wi wnf dral1 imbi12d nf5 3bitr4g ) CDFCGZAACGZHZCGBBDGZHZDGACIB
      DIPRCDNABOQEABCDEJKJACLBDLM $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 4-Oct-2016.)  (Proof shortened by Wolf
       Lammen, 5-May-2018.)  Usage of this theorem is discouraged because it
       depends on ~ ax-13 .  Use ~ nfbidv instead.
       (New usage is discouraged.) $)
    drnf2 $p |- ( A. x x = y -> ( F/ z ph <-> F/ z ps ) ) $=
      ( weq wal nfae nfbidf ) CDGCHABECDEIFJ $.
  $}

  ${
    nfald2.1 $e |- F/ y ph $.
    nfald2.2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
    $( Variation on ~ nfald which adds the hypothesis that ` x ` and ` y ` are
       distinct in the inner subproof.  (Contributed by Mario Carneiro,
       8-Oct-2016.)  Usage of this theorem is discouraged because it depends on
       ~ ax-13 .  Use ~ nfald instead.  (New usage is discouraged.) $)
    nfald2 $p |- ( ph -> F/ x A. y ps ) $=
      ( weq wal wnf wn wa nfnae nfan nfald ex nfa1 biidd drnf1 mpbiri pm2.61d2
      ) ACDGCHZBDHZCIZAUAJZUCAUDKBCDAUDDECDDLMFNOUAUCUBDIBDPUBUBCDUAUBQRST $.

    $( Variation on ~ nfexd which adds the hypothesis that ` x ` and ` y ` are
       distinct in the inner subproof.  (Contributed by Mario Carneiro,
       8-Oct-2016.)  Usage of this theorem is discouraged because it depends on
       ~ ax-13 .  Use ~ nfexd instead.  (New usage is discouraged.) $)
    nfexd2 $p |- ( ph -> F/ x E. y ps ) $=
      ( wex wn wal df-ex weq wa nfnd nfald2 nfxfrd ) BDGBHZDIZHACBDJAQCAPCDEACD
      KCIHLBCFMNMO $.
  $}

  ${
    exdistrf.1 $e |- ( -. A. x x = y -> F/ y ph ) $.
    $( Distribution of existential quantifiers, with a bound-variable
       hypothesis saying that ` y ` is not free in ` ph ` , but ` x ` can be
       free in ` ph ` (and there is no distinct variable condition on ` x ` and
       ` y ` ).  (Contributed by Mario Carneiro, 20-Mar-2013.)  (Proof
       shortened by Wolf Lammen, 14-May-2018.)  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  Use ~ exdistr instead.
       (New usage is discouraged.) $)
    exdistrf $p |- ( E. x E. y ( ph /\ ps ) -> E. x ( ph /\ E. y ps ) ) $=
      ( wa wex nfe1 weq wi 19.8a anim2i eximi biidd drex1 imbitrrid 19.40 19.9d
      wal wn anim1d syl56 pm2.61i exlimi ) ABFZDGZABDGZFZCGZCUHCHCDICSZUFUIJUFU
      IUJUHDGUEUHDBUGABDKLMUHUHCDUJUHNOPUFADGZUGFUJTZUHUIABDQULUKAUGAULDERUAUHC
      KUBUCUD $.
  $}

  ${
    dvelimf.1 $e |- F/ x ph $.
    dvelimf.2 $e |- F/ z ps $.
    dvelimf.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelimv without any variable restrictions.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
       NM, 1-Oct-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof
       shortened by Wolf Lammen, 11-May-2018.)  (New usage is discouraged.) $)
    dvelimf $p |- ( -. A. x x = y -> F/ x ps ) $=
      ( weq wi wal wn equsal bicomi nfnae wa wnf nfeqf ancoms a1i nfald2 nfxfrd
      nfimd ) BEDIZAJZEKZCDICKLZCUFBABEDGHMNUGUECECDEOUGCEICKLZPZUDACUHUGUDCQED
      CRSACQUIFTUCUAUB $.
  $}

  ${
    dvelimdf.1 $e |- F/ x ph $.
    dvelimdf.2 $e |- F/ z ph $.
    dvelimdf.3 $e |- ( ph -> F/ x ps ) $.
    dvelimdf.4 $e |- ( ph -> F/ z ch ) $.
    dvelimdf.5 $e |- ( ph -> ( z = y -> ( ps <-> ch ) ) ) $.
    $( Deduction form of ~ dvelimf .  Usage of this theorem is discouraged
       because it depends on ~ ax-13 .  (Contributed by NM, 7-Apr-2004.)
       (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof shortened by Wolf
       Lammen, 11-May-2018.)  (New usage is discouraged.) $)
    dvelimdf $p |- ( ph -> ( -. A. x x = y -> F/ x ch ) ) $=
      ( weq wal wn wi wnf nfim1 wb com12 pm5.74d dvelimf pm5.5 nfbidf imbitrid
      ) DELDMNACOZDPACDPABOUEDEFABDGIQACFHJQFELZABCAUFBCRKSTUAAUECDGACUBUCUD $.
  $}

  ${
    dvelimh.1 $e |- ( ph -> A. x ph ) $.
    dvelimh.2 $e |- ( ps -> A. z ps ) $.
    dvelimh.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim without any variable restrictions.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  Check out
       ~ dvelimhw for a version requiring fewer axioms.  (Contributed by NM,
       1-Oct-2002.)  (Proof shortened by Wolf Lammen, 11-May-2018.)
       (New usage is discouraged.) $)
    dvelimh $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn nf5i dvelimf nf5rd ) CDICJKBCABCDEACFLBEGLHMN $.
  $}

  ${
    $d z ps $.
    dvelim.1 $e |- ( ph -> A. x ph ) $.
    dvelim.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( This theorem can be used to eliminate a distinct variable restriction on
       ` x ` and ` z ` and replace it with the "distinctor" ` -. A. x x = y `
       as an antecedent. ` ph ` normally has ` z ` free and can be read
       ` ph ( z ) ` , and ` ps ` substitutes ` y ` for ` z ` and can be read
       ` ph ( y ) ` .  We do not require that ` x ` and ` y ` be distinct: if
       they are not, the distinctor will become false (in multiple-element
       domains of discourse) and "protect" the consequent.

       To obtain a closed-theorem form of this inference, prefix the hypotheses
       with ` A. x A. z ` , conjoin them, and apply ~ dvelimdf .

       Other variants of this theorem are ~ dvelimh (with no distinct variable
       restrictions) and ~ dvelimhw (that avoids ~ ax-13 ).  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  Check out
       ~ dvelimhw for a version requiring fewer axioms.  (Contributed by NM,
       23-Nov-1994.)  (New usage is discouraged.) $)
    dvelim $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( ax-5 dvelimh ) ABCDEFBEHGI $.
  $}

  ${
    $d x ph $.  $d z ps $.
    dvelimv.1 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Similar to ~ dvelim with first hypothesis replaced by a distinct
       variable condition.  Usage of this theorem is discouraged because it
       depends on ~ ax-13 .  Check out ~ dvelimhw for a version requiring fewer
       axioms.  (Contributed by NM, 25-Jul-2015.)  (Proof shortened by Wolf
       Lammen, 30-Apr-2018.)  (New usage is discouraged.) $)
    dvelimv $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( ax-5 dvelim ) ABCDEACGFH $.
  $}

  ${
    $d z ps $.
    dvelimnf.1 $e |- F/ x ph $.
    dvelimnf.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim using "not free" notation.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  (Contributed by Mario
       Carneiro, 9-Oct-2016.)  (New usage is discouraged.) $)
    dvelimnf $p |- ( -. A. x x = y -> F/ x ps ) $=
      ( nfv dvelimf ) ABCDEFBEHGI $.
  $}

  ${
    $d w x z $.  $d w y $.
    $( Alternate proof of ~ dveeq2 , shorter but requiring ~ ax-11 .
       (Contributed by NM, 2-Jan-2002.)  (Revised by NM, 20-Jul-2015.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    dveeq2ALT $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq equequ2 dvelimv ) CDECBEABDDBCFG $.
  $}

  $( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109,
     however we do not require ` z ` to be distinct from ` x ` and ` y ` .
     Usage of this theorem is discouraged because it depends on ~ ax-13 .  See
     ~ equvinv for a shorter proof requiring fewer axioms when ` z ` is
     required to be distinct from ` x ` and ` y ` .  (Contributed by NM,
     10-Jan-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
     shortened by Wolf Lammen, 16-Sep-2023.)  (New usage is discouraged.) $)
  equvini $p |- ( x = y -> E. z ( x = z /\ z = y ) ) $=
    ( weq wa wex wi equtr equcomi jctild 19.8a syl6 wal ax13 ax6e eximii 19.35i
    wn pm2.61i ) CADZABDZACDZCBDZEZCFZGTUAUDUETUAUCUBCABHCAIJZUDCKLTRUAUACMUECA
    BNUAUDCTUAUDGCCAOUFPQLS $.

  $( A variable elimination law for equality with no distinct variable
     requirements.  Compare ~ equvini .  Usage of this theorem is discouraged
     because it depends on ~ ax-13 .  Use ~ equvelv when possible.
     (Contributed by NM, 1-Mar-2013.)  (Proof shortened by Mario Carneiro,
     17-Oct-2016.)  (Proof shortened by Wolf Lammen, 15-Jun-2019.)
     (New usage is discouraged.) $)
  equvel $p |- ( A. z ( z = x <-> z = y ) -> x = y ) $=
    ( weq wb wal wex albi wi ax6e biimpr ax7 syli com12 eximii 19.35i spsd a1dd
    sps wn wa nfeqf 19.9d ex bija sylc ) CADZCBDZEZCFUGCFZUHCFZEABDZCGZULUGUHCH
    UIULCUHUIULICCBJUIUHULUHUIUGULUGUHKCABLZMNOPUJUKUMULIZUJUKULUMUGUKULICUGUHU
    LCUNQSRUJTZUKTZUOULUPUQUACABCUBUCUDUEUF $.

  $( A property related to substitution that unlike ~ equs5 does not require a
     distinctor antecedent.  Usage of this theorem is discouraged because it
     depends on ~ ax-13 .  This proof uses ~ ax12 , see ~ equs5aALT for an
     alternative one using ~ ax-12 but not ~ ax13 .  Usage of the weaker
     ~ equs5av is preferred, which uses ~ ax12v2 , but not ~ ax-13 .
     (Contributed by NM, 2-Feb-2007.)  (New usage is discouraged.) $)
  equs5a $p |- ( E. x ( x = y /\ A. y ph ) -> A. x ( x = y -> ph ) ) $=
    ( weq wal wa wi nfa1 ax12 imp exlimi ) BCDZACEZFLAGZBEZBNBHLMOABCIJK $.

  $( A property related to substitution that unlike ~ equs5 does not require a
     distinctor antecedent.  This proof uses ~ ax12 , see ~ equs5eALT for an
     alternative one using ~ ax-12 but not ~ ax13 .  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  (Contributed by NM,
     2-Feb-2007.)  (Proof shortened by Wolf Lammen, 15-Jan-2018.)
     (New usage is discouraged.) $)
  equs5e $p |- ( E. x ( x = y /\ ph ) -> A. x ( x = y -> E. y ph ) ) $=
    ( weq wa wex wi wal nfa1 ax12 hbe1 19.23bi impel exlimi ) BCDZAEOACFZGZBHZB
    QBIOPCHZRAPBCJASCACKLMN $.

  ${
    equs45f.1 $e |- F/ y ph $.
    $( Two ways of expressing substitution when ` y ` is not free in ` ph ` .
       The implication "to the left" is ~ equs4 and does not require the
       nonfreeness hypothesis.  Theorem ~ sbalex replaces the nonfreeness
       hypothesis with a disjoint variable condition and ~ equs5 replaces it
       with a distinctor antecedent.  (Contributed by NM, 25-Apr-2008.)
       (Revised by Mario Carneiro, 4-Oct-2016.)  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  Use ~ sbalex instead.
       (New usage is discouraged.) $)
    equs45f $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      ( weq wa wex wi wal nf5ri anim2i eximi equs5a syl equs4 impbii ) BCEZAFZB
      GZQAHBIZSQACIZFZBGTRUBBAUAQACDJKLABCMNABCOP $.
  $}

  $( Lemma used in proofs of substitution properties.  If there is a disjoint
     variable condition on ` x , y ` , then ~ sbalex can be used instead; if
     ` y ` is not free in ` ph ` , then ~ equs45f can be used.  Usage of this
     theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
     NM, 14-May-1993.)  (Revised by BJ, 1-Oct-2018.)
     (New usage is discouraged.) $)
  equs5 $p |- ( -. A. x x = y ->
             ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wa wex wi nfna1 nfa1 axc15 impd exlimd equs4 impbid1 ) BCDZBEF
    ZQAGZBHQAIZBEZRSUABQBJTBKRQAUAABCLMNABCOP $.

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is disjoint.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 2-Jan-2002.)  (New usage is discouraged.) $)
    dveel1 $p |- ( -. A. x x = y -> ( y e. z -> A. x y e. z ) ) $=
      ( vw wel elequ1 dvelimv ) DCEBCEABDDBCFG $.

    $( Quantifier introduction when one pair of variables is disjoint.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 2-Jan-2002.)  (New usage is discouraged.) $)
    dveel2 $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $=
      ( vw wel elequ2 dvelimv ) CDECBEABDDBCFG $.
  $}

  ${
    $d w y $.  $d w z $.  $d w x $.
    $( Axiom ~ ax-c14 is redundant if we assume ~ ax-5 .  Remark 9.6 in
       [Megill] p. 448 (p. 16 of the preprint), regarding axiom scheme C14'.

       Note that ` w ` is a dummy variable introduced in the proof.  Its
       purpose is to satisfy the distinct variable requirements of ~ dveel2 and
       ~ ax-5 .  By the end of the proof it has vanished, and the final theorem
       has no distinct variable requirements.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  (Contributed by NM,
       29-Jun-1995.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    axc14 $p |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x e. y -> A. z x e. y ) ) ) $=
      ( vw weq wal wn wel hbn1 dveel2 hbim1 elequ1 imbi2d dvelim nfa1 nfn 19.21
      wi imbitrdi pm2.86d ) CAECFGZCBEZCFZGZABHZUECFZUAUDUERZUGCFUDUFRUDDBHZRUG
      CADUDUHCUBCICBDJKDAEUHUEUDDABLMNUDUECUCCUBCOPQST $.
  $}

  ${
    sb6x.1 $e |- F/ x ph $.
    $( Equivalence involving substitution for a variable not free.  Usage of
       this theorem is discouraged because it depends on ~ ax-13 .  Usage of
       ~ sb6 is preferred, which requires fewer axioms.  (Contributed by NM,
       2-Jun-1993.)  (Revised by Mario Carneiro, 4-Oct-2016.)
       (New usage is discouraged.) $)
    sb6x $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( wsb weq wi wal sbf biidd equsal bitr4i ) ABCEABCFZAGBHABCDIAABCDMAJKL
      $.
  $}

  $( Substitution does not change an identical variable specifier.  Usage of
     this theorem is discouraged because it depends on ~ ax-13 .  (Contributed
     by NM, 15-May-1993.)  (New usage is discouraged.) $)
  sbequ5 $p |- ( [ w / z ] A. x x = y <-> A. x x = y ) $=
    ( weq wal nfae sbf ) ABEAFCDABCGH $.

  $( Substitution does not change a distinctor.  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  (Contributed by NM,
     5-Aug-1993.)  (New usage is discouraged.) $)
  sbequ6 $p |- ( [ w / z ] -. A. x x = y <-> -. A. x x = y ) $=
    ( weq wal wn nfnae sbf ) ABEAFGCDABCHI $.

  ${
    sb5rf.1 $e |- F/ y ph $.
    $( Reversed substitution.  Usage of this theorem is discouraged because it
       depends on ~ ax-13 .  (Contributed by NM, 3-Feb-2005.)  (Revised by
       Mario Carneiro, 6-Oct-2016.)  (Proof shortened by Wolf Lammen,
       20-Sep-2018.)  (New usage is discouraged.) $)
    sb5rf $p |- ( ph <-> E. y ( y = x /\ [ y / x ] ph ) ) $=
      ( weq wsb wa wex sbequ12r equsex bicomi ) CBEABCFZGCHALACBDACBIJK $.

    $( Reversed substitution.  For a version requiring disjoint variables, but
       fewer axioms, see ~ sb6rfv .  Usage of this theorem is discouraged
       because it depends on ~ ax-13 .  Use the weaker ~ sb6rfv if possible.
       (Contributed by NM, 1-Aug-1993.)  (Revised by Mario Carneiro,
       6-Oct-2016.)  (Proof shortened by Wolf Lammen, 21-Sep-2018.)
       (New usage is discouraged.) $)
    sb6rf $p |- ( ph <-> A. y ( y = x -> [ y / x ] ph ) ) $=
      ( weq wsb wi wal sbequ12r equsal bicomi ) CBEABCFZGCHALACBDACBIJK $.
  $}

  ${
    $d x y $.
    $( Alternate proof of ~ ax12v2 , shorter, but depending on more axioms.
       (Contributed by NM, 5-Aug-1993.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ax12vALT $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( weq wal wi ax-1 axc16 syl5 a1d axc15 pm2.61i ) BCDZBEZMAMAFZBEZFZFNQMAO
      NPAMGOBCHIJABCKL $.
  $}

  $( We can always find values matching ` x ` and ` y ` , as long as they are
     represented by distinct variables.  This theorem merges two ~ ax6e
     instances ` E. z z = x ` and ` E. w w = y ` into a common expression.
     Alan Sare contributed a variant of this theorem with distinct variable
     conditions before, see ~ ax6e2nd .  Usage of this theorem is discouraged
     because it depends on ~ ax-13 .  (Contributed by Wolf Lammen,
     27-Sep-2018.)  (New usage is discouraged.) $)
  2ax6elem $p |- ( -. A. w w = z -> E. z E. w ( z = x /\ w = y ) ) $=
    ( weq wal wn wex ax6e nfnae nfan nfeqf pm3.21 spimed eximd mpi nfae equvini
    wa ex equtrr anim1d aleximi syl5 pm2.61d2 ) DCEDFGZDAEZDFZCAEZDBEZSZDHZCHZU
    FUHGZUMUFUNSZUICHUMCAIUOUIULCUFUNCDCCJDACJKUIUKUODBCADLUJUIMNOPTUHCBEZCHUMC
    BIUHUPULCDACQUPCDEZUJSZDHUHULCBDRUGURUKDUGUQUIUJDACUAUBUCUDOPUE $.

  ${
    $d w z $.
    $( We can always find values matching ` x ` and ` y ` , as long as they are
       represented by distinct variables.  Version of ~ 2ax6elem with a
       distinct variable constraint.  Usage of this theorem is discouraged
       because it depends on ~ ax-13 .  (Contributed by Wolf Lammen,
       28-Sep-2018.)  (Proof shortened by Wolf Lammen, 3-Oct-2023.)
       (New usage is discouraged.) $)
    2ax6e $p |- E. z E. w ( z = x /\ w = y ) $=
      ( weq wal wa wex aeveq jca 19.8ad 2ax6elem pm2.61i ) DCEDFZCAEZDBEZGZDHZC
      HNRCNQDNOPDCCAIDCDBIJKKABCDLM $.
  $}

  ${
    $d w z $.
    2sb5rf.1 $e |- F/ z ph $.
    2sb5rf.2 $e |- F/ w ph $.
    $( Reversed double substitution.  Usage of this theorem is discouraged
       because it depends on ~ ax-13 .  (Contributed by NM, 3-Feb-2005.)
       (Revised by Mario Carneiro, 6-Oct-2016.)  Remove distinct variable
       constraints.  (Revised by Wolf Lammen, 28-Sep-2018.)
       (New usage is discouraged.) $)
    2sb5rf $p |- ( ph <->
                E. z E. w ( ( z = x /\ w = y ) /\ [ z / x ] [ w / y ] ph ) ) $=
      ( weq wa wex 19.41 exbii 2ax6e biantrur 3bitr4ri sbequ12r sylan9bb 2exbii
      wsb pm5.32i bitr4i ) ADBHZECHZIZAIZEJZDJZUDACESZBDSZIZEJDJUDEJZAIZDJUKDJZ
      AIUGAUKADFKUFULDUDAEGKLUMABCDEMNOUJUEDEUDUIAUBUIUHUCAUHDBPAECPQTRUA $.

    $( Reversed double substitution.  Usage of this theorem is discouraged
       because it depends on ~ ax-13 .  (Contributed by NM, 3-Feb-2005.)
       (Revised by Mario Carneiro, 6-Oct-2016.)  Remove variable constraints.
       (Revised by Wolf Lammen, 28-Sep-2018.)  (Proof shortened by Wolf Lammen,
       13-Apr-2023.)  (New usage is discouraged.) $)
    2sb6rf $p |- ( ph <->
                A. z A. w ( ( z = x /\ w = y ) -> [ z / x ] [ w / y ] ph ) ) $=
      ( weq wa wi wal wsb wex 19.23 albii 2ax6e a1bi 3bitr4ri sbequ12r sylan9bb
      pm5.74i 2albii bitr4i ) ADBHZECHZIZAJZEKZDKZUFACELZBDLZJZEKDKUFEMZAJZDKUM
      DMZAJUIAUMADFNUHUNDUFAEGNOUOABCDEPQRULUGDEUFUKAUDUKUJUEAUJDBSAECSTUAUBUC
      $.
  $}

  ${
    $d x y ph $.
    $( Elimination of double substitution.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 29-Sep-2018.)
       (New usage is discouraged.) $)
    sbel2x $p |- ( ph <-> E. x E. y ( ( x = z /\ y = w ) /\
                     [ y / w ] [ x / z ] ph ) ) $=
      ( weq wa wsb wex nfv 2sb5rf ancom anbi1i 2exbii excom 3bitri ) ACEFZBDFZG
      ZADBHECHZGZBICIRQGZTGZBICIUCCIBIAEDCBACJABJKUAUCCBSUBTQRLMNUCCBOP $.
  $}

  ${
    $d y x $.  $d y t $.  $d y ph $.
    $( Simplified definition of substitution when variables are distinct.
       Version of ~ sb6 with a distinctor antecedent.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  (Contributed by NM,
       27-May-1997.)  Revise ~ df-sb .  (Revised by Wolf Lammen, 21-Feb-2024.)
       (New usage is discouraged.) $)
    sb4b $p |- ( -. A. x x = t -> ( [ t / x ] ph
                                              <-> A. x ( x = t -> ph ) ) ) $=
      ( vy weq wal wn wi wa nfna1 nfeqf2 nfan1 wb equequ2 imbi1d albid pm5.74da
      wsb adantl albidv dfsb wex ax6ev a1bi 19.23v bitr4i 3bitr4g ) BCEZBFGZDCE
      ZBDEZAHZBFZHZDFUJUHAHZBFZHZDFZABCRUPUIUNUQDUIUJUMUPUIUJIULUOBUIUJBUHBJBCD
      KLUJULUOMUIUJUKUHADCBNOSPQTABDCUAUPUJDUBZUPHURUSUPDCUCUDUJUPDUEUFUG $.
  $}

  $( Simplified definition of substitution when variables are distinct.  This
     is the biconditional strengthening of ~ sb3 .  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  (Contributed by BJ,
     6-Oct-2018.)  Shorten ~ sb3 .  (Revised by Wolf Lammen, 21-Feb-2021.)
     (New usage is discouraged.) $)
  sb3b $p |- ( -. A. x x = y -> ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) ) $=
    ( weq wal wn wsb wi wa wex sb4b equs5 bitr4d ) BCDZBEFABCGNAHBENAIBJABCKABC
    LM $.

  $( One direction of a simplified definition of substitution when variables
     are distinct.  Usage of this theorem is discouraged because it depends on
     ~ ax-13 .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 21-Feb-2024.)  (New usage is discouraged.) $)
  sb3 $p |- ( -. A. x x = y -> ( E. x ( x = y /\ ph ) -> [ y / x ] ph ) ) $=
    ( weq wal wn wsb wa wex sb3b biimprd ) BCDZBEFABCGLAHBIABCJK $.

  $( One direction of a simplified definition of substitution.  The converse
     requires either a disjoint variable condition ( ~ sb5 ) or a nonfreeness
     hypothesis ( ~ sb5f ).  Usage of this theorem is discouraged because it
     depends on ~ ax-13 .  Use the weaker ~ sb1v when possible.  (Contributed
     by NM, 13-May-1993.)  Revise ~ df-sb .  (Revised by Wolf Lammen,
     21-Feb-2024.)  (New usage is discouraged.) $)
  sb1 $p |- ( [ y / x ] ph -> E. x ( x = y /\ ph ) ) $=
    ( weq wal wsb wa wex wi spsbe pm3.2 aleximi syl5 wn sb3b biimpd pm2.61i ) B
    CDZBEZABCFZRAGZBHZITABHSUBABCJRAUABRAKLMSNTUBABCOPQ $.

  $( One direction of a simplified definition of substitution.  The converse
     requires either a disjoint variable condition ( ~ sb6 ) or a nonfreeness
     hypothesis ( ~ sb6f ).  Usage of this theorem is discouraged because it
     depends on ~ ax-13 .  (Contributed by NM, 13-May-1993.)  Revise ~ df-sb .
     (Revised by Wolf Lammen, 26-Jul-2023.)  (New usage is discouraged.) $)
  sb2 $p |- ( A. x ( x = y -> ph ) -> [ y / x ] ph ) $=
    ( weq wal wi wsb pm2.27 al2imi stdpc4 syl6 wn sb4b biimprd pm2.61i ) BCDZBE
    ZPAFZBEZABCGZFQSABETPRABPAHIABCJKQLTSABCMNO $.

  $( A version of one implication of ~ sb4b that does not require a distinctor
     antecedent.  Usage of this theorem is discouraged because it depends on
     ~ ax-13 .  Use the weaker ~ sb4av when possible.  (Contributed by NM,
     2-Feb-2007.)  Revise ~ df-sb .  (Revised by Wolf Lammen, 28-Jul-2023.)
     (New usage is discouraged.) $)
  sb4a $p |- ( [ t / x ] A. t ph -> A. x ( x = t -> ph ) ) $=
    ( weq wal wsb wi sbequ2 sps axc11r ala1 syl6 syld wn sb4b sp alimi biimtrdi
    imim2i pm2.61i ) BCDZBEZACEZBCFZUAAGZBEZGUBUDUCUFUAUDUCGBUCBCHIUBUCABEUFACB
    JAUABKLMUBNUDUAUCGZBEUFUCBCOUGUEBUCAUAACPSQRT $.

  $( Alternate definition of substitution.  Remark 9.1 in [Megill] p. 447 (p.
     15 of the preprint).  This was the original definition before ~ df-sb .
     Note that it does not require dummy variables in its definiens; this is
     done by having ` x ` free in the first conjunct and bound in the second.
     Usage of this theorem is discouraged because it depends on ~ ax-13 .
     (Contributed by BJ, 9-Jul-2023.)  Revise ~ df-sb .  (Revised by Wolf
     Lammen, 29-Jul-2023.)  (New usage is discouraged.) $)
  dfsb1 $p |- ( [ y / x ] ph <->
                ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) ) $=
    ( wsb weq wi wa wex sbequ2 com12 sb1 jca wal sbequ1 embantd sps adantrd sb3
    id wn adantld pm2.61i impbii ) ABCDZBCEZAFZUEAGBHZGZUDUFUGUEUDAABCIJABCKLUE
    BMZUHUDFUIUFUDUGUEUFUDFBUEUEAUDUESABCNOPQUITUGUDUFABCRUAUBUC $.

  $( Bound-variable hypothesis builder for substitution.  Usage of this theorem
     is discouraged because it depends on ~ ax-13 .  (Contributed by NM,
     14-May-1993.)  (New usage is discouraged.) $)
  hbsb2 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x [ y / x ] ph ) ) $=
    ( weq wal wn wsb wi sb4b sb2 axc4i biimtrdi ) BCDZBEFABCGZMAHZBENBEABCIONBA
    BCJKL $.

  $( Bound-variable hypothesis builder for substitution.  Usage of this theorem
     is discouraged because it depends on ~ ax-13 .  (Contributed by Mario
     Carneiro, 4-Oct-2016.)  (New usage is discouraged.) $)
  nfsb2 $p |- ( -. A. x x = y -> F/ x [ y / x ] ph ) $=
    ( weq wal wn wsb nfna1 hbsb2 nf5d ) BCDZBEFABCGBKBHABCIJ $.

  $( Special case of a bound-variable hypothesis builder for substitution.
     Usage of this theorem is discouraged because it depends on ~ ax-13 .
     (Contributed by NM, 2-Feb-2007.)  (New usage is discouraged.) $)
  hbsb2a $p |- ( [ y / x ] A. y ph -> A. x [ y / x ] ph ) $=
    ( wal wsb weq wi sb4a sb2 axc4i syl ) ACDBCEBCFAGZBDABCEZBDABCHLMBABCIJK $.

  $( One direction of a simplified definition of substitution that unlike
     ~ sb4b does not require a distinctor antecedent.  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  (Contributed by NM,
     2-Feb-2007.)  (New usage is discouraged.) $)
  sb4e $p |- ( [ y / x ] ph -> A. x ( x = y -> E. y ph ) ) $=
    ( wsb weq wa wex wi wal sb1 equs5e syl ) ABCDBCEZAFBGMACGHBIABCJABCKL $.

  $( Special case of a bound-variable hypothesis builder for substitution.
     Usage of this theorem is discouraged because it depends on ~ ax-13 .
     (Contributed by NM, 2-Feb-2007.)  (New usage is discouraged.) $)
  hbsb2e $p |- ( [ y / x ] ph -> A. x [ y / x ] E. y ph ) $=
    ( wsb weq wex wi wal sb4e sb2 axc4i syl ) ABCDBCEACFZGZBHMBCDZBHABCINOBMBCJ
    KL $.

  ${
    hbsb3.1 $e |- ( ph -> A. y ph ) $.
    $( If ` y ` is not free in ` ph ` , ` x ` is not free in ` [ y / x ] ph ` .
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       Check out ~ bj-hbsb3v for a weaker version requiring fewer axioms.
       (Contributed by NM, 14-May-1993.)  (New usage is discouraged.) $)
    hbsb3 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wsb wal sbimi hbsb2a syl ) ABCEZACFZBCEJBFAKBCDGABCHI $.
  $}

  ${
    nfs1.1 $e |- F/ y ph $.
    $( If ` y ` is not free in ` ph ` , ` x ` is not free in ` [ y / x ] ph ` .
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       Check out ~ nfs1v for a version requiring fewer axioms.  (Contributed by
       Mario Carneiro, 11-Aug-2016.)  (New usage is discouraged.) $)
    nfs1 $p |- F/ x [ y / x ] ph $=
      ( wsb nf5ri hbsb3 nf5i ) ABCEBABCACDFGH $.
  $}

  ${
    $d x y z $.  $d z ph $.
    $( Alternate proof of ~ axc16 , shorter but requiring ~ ax-10 , ~ ax-11 ,
       ~ ax-13 and using ~ df-nf and ~ df-sb .  (Contributed by NM,
       17-May-2008.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    axc16ALT $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( vz wsb sbequ12 ax-5 hbsb3 axc16i ) AABDEBCDABDFABDADGHI $.
  $}

  ${
    $d x y $.
    $( Alternate proof of ~ axc16g that uses ~ df-sb and requires ~ ax-10 ,
       ~ ax-11 , ~ ax-13 .  (Contributed by NM, 15-May-1993.)  (Proof shortened
       by Andrew Salmon, 25-May-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    axc16gALT $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( weq wal aev axc16ALT biidd dral1 biimprd sylsyld ) BCEBFDBEDFZAABFZADFZ
      BCDBDGABCHMONAADBMAIJKL $.
  $}

  $( Substitution applied to an atomic wff.  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  Use the weaker ~ equsb1v if
     possible.  (Contributed by NM, 10-May-1993.)
     (New usage is discouraged.) $)
  equsb1 $p |- [ y / x ] x = y $=
    ( weq wi wsb sb2 id mpg ) ABCZIDIABEAIABFIGH $.

  $( Substitution applied to an atomic wff.  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  Check out ~ equsb1v for a
     version requiring fewer axioms.  (Contributed by NM, 10-May-1993.)
     (New usage is discouraged.) $)
  equsb2 $p |- [ y / x ] y = x $=
    ( weq wi wsb sb2 equcomi mpg ) ABCBACZDIABEAIABFABGH $.

  $( An alternate definition of proper substitution that, like ~ dfsb1 , mixes
     free and bound variables to avoid distinct variable requirements.  Usage
     of this theorem is discouraged because it depends on ~ ax-13 .
     (Contributed by NM, 17-Feb-2005.)  (New usage is discouraged.) $)
  dfsb2 $p |- ( [ y / x ] ph <->
              ( ( x = y /\ ph ) \/ A. x ( x = y -> ph ) ) ) $=
    ( wsb weq wa wi wal wo sp sbequ2 sps orc syl6an wn sb4b olc biimtrdi sbequ1
    pm2.61i imp sb2 jaoi impbii ) ABCDZBCEZAFZUFAGBHZIZUFBHZUEUIGUJUFUEAUIUFBJU
    FUEAGBABCKLUGUHMNUJOUEUHUIABCPUHUGQRTUGUEUHUFAUEABCSUAABCUBUCUD $.

  $( An alternate definition of proper substitution ~ df-sb that uses only
     primitive connectives (no defined terms) on the right-hand side.  Usage of
     this theorem is discouraged because it depends on ~ ax-13 .  (Contributed
     by NM, 6-Mar-2007.)  (New usage is discouraged.) $)
  dfsb3 $p |- ( [ y / x ] ph <->
              ( ( x = y -> -. ph ) -> A. x ( x = y -> ph ) ) ) $=
    ( weq wa wi wal wo wn wsb df-or dfsb2 imnan imbi1i 3bitr4i ) BCDZAEZPAFBGZH
    QIZRFABCJPAIFZRFQRKABCLTSRPAMNO $.

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Usage of this
     theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
     NM, 2-Jun-1993.)  (New usage is discouraged.) $)
  drsb1 $p |- ( A. x x = y -> ( [ z / x ] ph <-> [ z / y ] ph ) ) $=
    ( weq wal wi wa wex wsb wb equequ1 sps imbi1d anbi1d drex1 anbi12d 3bitr4g
    dfsb1 ) BCEZBFZBDEZAGZUBAHZBIZHCDEZAGZUFAHZCIZHABDJACDJUAUCUGUEUIUAUBUFATUB
    UFKBBCDLMZNUDUHBCUAUBUFAUJOPQABDSACDSR $.

  ${
    $d v y $.
    $( In the case of two successive substitutions for two always equal
       variables, the second substitution has no effect.  Usage of this theorem
       is discouraged because it depends on ~ ax-13 .  (Contributed by BJ and
       WL, 9-Aug-2023.)  (New usage is discouraged.) $)
    sb2ae $p |-
               ( A. x x = y -> ( [ u / x ] [ v / y ] ph <-> [ v / y ] ph ) ) $=
      ( weq wal wsb drsb1 nfs1v sbf bitrdi ) BCFBGACDHZBEHMCEHMMBCEIMCEACDJKL
      $.
  $}

  ${
    sb6f.1 $e |- F/ y ph $.
    $( Equivalence for substitution when ` y ` is not free in ` ph ` .  The
       implication "to the left" is ~ sb2 and does not require the nonfreeness
       hypothesis.  Theorem ~ sb6 replaces the nonfreeness hypothesis with a
       disjoint variable condition on ` x , y ` and requires fewer axioms.
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 2-Jun-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.)  (New usage is discouraged.) $)
    sb6f $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( wsb weq wi wal nf5ri sbimi sb4a syl sb2 impbii ) ABCEZBCFAGBHZOACHZBCEP
      AQBCACDIJABCKLABCMN $.

    $( Equivalence for substitution when ` y ` is not free in ` ph ` .  The
       implication "to the right" is ~ sb1 and does not require the nonfreeness
       hypothesis.  Theorem ~ sb5 replaces the nonfreeness hypothesis with a
       disjoint variable condition on ` x , y ` and requires fewer axioms.
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.)  (New usage is discouraged.) $)
    sb5f $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wi wal wa wex sb6f equs45f bitr4i ) ABCEBCFZAGBHNAIBJABCDKABCDL
      M $.
  $}

  $( A variable not free in a proposition remains so after substitution in that
     proposition with a distinct variable (closed form of ~ nfsb4 ).  Usage of
     this theorem is discouraged because it depends on ~ ax-13 .  (Contributed
     by NM, 7-Apr-2004.)  (Revised by Mario Carneiro, 4-Oct-2016.)  (Proof
     shortened by Wolf Lammen, 11-May-2018.)  (New usage is discouraged.) $)
  nfsb4t $p |- ( A. x F/ z ph ->
                 ( -. A. z z = y -> F/ z [ y / x ] ph ) ) $=
    ( wnf wal weq wn wsb wi wa sbequ12 sps drnf2 biimpd spsd impcom nfnae nfan
    wb a1d nfnf1 nfal nfa1 sp adantr nfsb2 adantl a1i dvelimdf pm2.61dan ) ADEZ
    BFZBCGZBFZDCGDFHZABCIZDEZJUMUOKURUPUOUMURUOULURBUOULURAUQBCDUNAUQTZBABCLZMN
    OPQUAUMUOHZKZAUQDCBUMVADULDBADUBUCBCDRSUMVABULBUDBCBRSUMULVAULBUEUFVAUQBEUM
    ABCUGUHUNUSJVBUTUIUJUK $.

  ${
    nfsb4.1 $e |- F/ z ph $.
    $( A variable not free in a proposition remains so after substitution in
       that proposition with a distinct variable (inference associated with
       ~ nfsb4t ).  Theorem ~ nfsb replaces the distinctor antecedent with a
       disjoint variable condition.  See ~ nfsbv for a weaker version of ~ nfsb
       not requiring ~ ax-13 .  (Contributed by NM, 14-May-1993.)  (Revised by
       Mario Carneiro, 4-Oct-2016.)  Usage of this theorem is discouraged
       because it depends on ~ ax-13 .  Use ~ nfsbv instead.
       (New usage is discouraged.) $)
    nfsb4 $p |- ( -. A. z z = y -> F/ z [ y / x ] ph ) $=
      ( wnf weq wal wn wsb wi nfsb4t mpg ) ADFDCGDHIABCJDFKBABCDLEM $.
  $}

  $( Elimination of equality from antecedent after substitution.  Usage of this
     theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
     NM, 5-Aug-1993.)  Reduce dependencies on axioms.  (Revised by Wolf Lammen,
     28-Jul-2018.)  Revise ~ df-sb .  (Revised by Wolf Lammen, 28-Jul-2023.)
     (New usage is discouraged.) $)
  sbequ8 $p |- ( [ y / x ] ph <-> [ y / x ] ( x = y -> ph ) ) $=
    ( wsb weq wi equsb1 a1bi sbim bitr4i ) ABCDZBCEZBCDZKFLAFBCDMKBCGHLABCIJ $.

  ${
    sbie.1 $e |- F/ x ps $.
    sbie.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit substitution.  For
       versions requiring disjoint variables, but fewer axioms, see ~ sbiev and
       ~ sbievw .  Usage of this theorem is discouraged because it depends on
       ~ ax-13 .  (Contributed by NM, 30-Jun-1994.)  (Revised by Mario
       Carneiro, 4-Oct-2016.)  (Proof shortened by Wolf Lammen, 13-Jul-2019.)
       (New usage is discouraged.) $)
    sbie $p |- ( [ y / x ] ph <-> ps ) $=
      ( wb wsb weq equsb1 sbimi ax-mp sbf sblbis mpbi ) ABGZCDHZACDHBGCDIZCDHQC
      DJRPCDFKLBBACDBCDEMNO $.
  $}

  ${
    sbied.1 $e |- F/ x ph $.
    sbied.2 $e |- ( ph -> F/ x ch ) $.
    sbied.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ) Usage of this theorem is discouraged because it
       depends on ~ ax-13 .  See ~ sbiedw , ~ sbiedvw for variants using
       disjoint variables, but requiring fewer axioms.  (Contributed by NM,
       30-Jun-1994.)  (Revised by Mario Carneiro, 4-Oct-2016.)  (Proof
       shortened by Wolf Lammen, 24-Jun-2018.)  (New usage is discouraged.) $)
    sbied $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( wsb wi sbrim nfim1 weq wb com12 pm5.74d sbie bitr3i pm5.74ri ) ABDEIZCA
      TJABJZDEIACJZABDEFKUAUBDEACDFGLDEMZABCAUCBCNHOPQRS $.
  $}

  ${
    $d x ph $.  $d x ch $.
    sbiedv.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  Usage of this theorem is discouraged because it
       depends on ~ ax-13 .  Use the weaker ~ sbiedvw when possible.
       (Contributed by NM, 7-Jan-2017.)  (New usage is discouraged.) $)
    sbiedv $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( nfv nfvd weq wb ex sbied ) ABCDEADGACDHADEIBCJFKL $.
  $}

  ${
    $d x y ps $.  $d t y $.
    2sbiev.1 $e |- ( ( x = t /\ y = u ) -> ( ph <-> ps ) ) $.
    $( Conversion of double implicit substitution to explicit substitution.
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       See ~ 2sbievw for a version with extra disjoint variables, but based on
       fewer axioms.  (Contributed by AV, 29-Jul-2023.)
       (New usage is discouraged.) $)
    2sbiev $p |- ( [ t / x ] [ u / y ] ph <-> ps ) $=
      ( wsb nfv weq sbiedv sbie ) ADEHBCFBCICFJABDEGKL $.
  $}

  $( Substituting ` y ` for ` x ` and then ` z ` for ` y ` is equivalent to
     substituting ` z ` for both ` x ` and ` y ` .  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  For a version requiring a
     disjoint variable, but fewer axioms, see ~ sbcom3vv .  (Contributed by
     Giovanni Mascellani, 8-Apr-2018.)  Remove dependency on ~ ax-11 .
     (Revised by Wolf Lammen, 16-Sep-2018.)  (Proof shortened by Wolf Lammen,
     16-Sep-2018.)  (New usage is discouraged.) $)
  sbcom3 $p |- ( [ z / y ] [ y / x ] ph <-> [ z / y ] [ z / x ] ph ) $=
    ( weq wal wsb wb nfa1 drsb2 sbbid wn sb4b sbequ pm5.74i albii bitrdi bitr4d
    wi pm2.61i ) CDEZCFZABCGZCDGZABDGZCDGZHUBUCUECDUACIACDBJKUBLZUDUAUESZCFZUFU
    GUDUAUCSZCFUIUCCDMUJUHCUAUCUEACDBNOPQUECDMRT $.

  $( A composition law for substitution.  Usage of this theorem is discouraged
     because it depends on ~ ax-13 .  See ~ sbcov for a version with a disjoint
     variable condition requiring fewer axioms.  (Contributed by NM,
     14-May-1993.)  (Proof shortened by Wolf Lammen, 21-Sep-2018.)
     (New usage is discouraged.) $)
  sbco $p |- ( [ y / x ] [ x / y ] ph <-> [ y / x ] ph ) $=
    ( wsb sbcom3 sbid sbbii bitri ) ACBDBCDACCDZBCDABCDACBCEIABCACFGH $.

  ${
    sbid2.1 $e |- F/ x ph $.
    $( An identity law for substitution.  Usage of this theorem is discouraged
       because it depends on ~ ax-13 .  Check out ~ sbid2vw for a weaker
       version requiring fewer axioms.  (Contributed by NM, 14-May-1993.)
       (Revised by Mario Carneiro, 6-Oct-2016.)  (New usage is discouraged.) $)
    sbid2 $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      ( wsb sbco sbf bitri ) ACBEBCEABCEAABCFABCDGH $.
  $}

  ${
    $d x ph $.
    $( An identity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  See ~ sbid2vw for a version
       with an extra disjoint variable condition requiring fewer axioms.
       (Contributed by NM, 5-Aug-1993.)  (New usage is discouraged.) $)
    sbid2v $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      ( nfv sbid2 ) ABCABDE $.
  $}

  $( An idempotent law for substitution.  Usage of this theorem is discouraged
     because it depends on ~ ax-13 .  (Contributed by NM, 30-Jun-1994.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.)  (Proof shortened by Wolf
     Lammen, 13-Jul-2019.)  (New usage is discouraged.) $)
  sbidm $p |- ( [ y / x ] [ y / x ] ph <-> [ y / x ] ph ) $=
    ( wsb sbcom3 sbid sbbii bitr3i ) ABCDZBCDABBDZBCDIABBCEJABCABFGH $.

  ${
    sbco2.1 $e |- F/ z ph $.
    $( A composition law for substitution.  For versions requiring fewer
       axioms, but more disjoint variable conditions, see ~ sbco2v and
       ~ sbco2vv .  Usage of this theorem is discouraged because it depends on
       ~ ax-13 .  (Contributed by NM, 30-Jun-1994.)  (Revised by Mario
       Carneiro, 6-Oct-2016.)  (Proof shortened by Wolf Lammen, 17-Sep-2018.)
       (New usage is discouraged.) $)
    sbco2 $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      ( weq wal wsb wb sbequ12 sbequ bitr3d sps wn nfnae nfsb4 wi sbied pm2.61i
      a1i ) DCFZDGZABDHZDCHZABCHZIZUAUFDUAUCUDUEUCDCJADCBKZLMUBNZUCUEDCDCDOABCD
      EPUAUCUEIQUHUGTRS $.
  $}

  ${
    sbco2d.1 $e |- F/ x ph $.
    sbco2d.2 $e |- F/ z ph $.
    sbco2d.3 $e |- ( ph -> F/ z ps ) $.
    $( A composition law for substitution.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  (Contributed by NM,
       2-Jun-1993.)  (Revised by Mario Carneiro, 6-Oct-2016.)
       (New usage is discouraged.) $)
    sbco2d $p |- ( ph -> ( [ y / z ] [ z / x ] ps <-> [ y / x ] ps ) ) $=
      ( wsb wi nfim1 sbco2 sbrim sbbii bitri 3bitr3i pm5.74ri ) ABCEIZEDIZBCDIZ
      ABJZCEIZEDIZUACDIASJZATJUACDEABEGHKLUCARJZEDIUDUBUEEDABCEFMNAREDGMOABCDFM
      PQ $.
  $}

  $( A composition law for substitution.  Usage of this theorem is discouraged
     because it depends on ~ ax-13 .  (Contributed by NM, 2-Jun-1993.)  (Proof
     shortened by Wolf Lammen, 18-Sep-2018.)  (New usage is discouraged.) $)
  sbco3 $p |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ x / y ] ph ) $=
    ( weq wal wsb wb drsb1 nfae sbequ12a sps sbbid bitr3d wn nfnae nfsb2 sbco2d
    sbco sbbii bitr3di pm2.61i ) BCEZBFZABCGZCDGZACBGZBDGZHUDUEBDGUFUHUEBCDIUDU
    EUGBDBCBJUCUEUGHBABCKLMNUDOZUECBGZBDGUFUHUIUECDBBCCPBCBPABCQRUJUGBDACBSTUAU
    B $.

  $( A commutativity law for substitution.  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  Check out ~ sbcom3vv for a
     version requiring fewer axioms.  (Contributed by NM, 27-May-1997.)  (Proof
     shortened by Wolf Lammen, 20-Sep-2018.)  (New usage is discouraged.) $)
  sbcom $p |- ( [ y / z ] [ y / x ] ph <-> [ y / x ] [ y / z ] ph ) $=
    ( wsb sbco3 sbcom3 3bitr3i ) ABDEDCEADBEBCEABCEDCEADCEBCEABDCFABDCGADBCGH
    $.

  ${
    sbtrt.nf $e |- F/ y ph $.
    $( Partially closed form of ~ sbtr .  Usage of this theorem is discouraged
       because it depends on ~ ax-13 .  (Contributed by BJ, 4-Jun-2019.)
       (New usage is discouraged.) $)
    sbtrt $p |- ( A. y [ y / x ] ph -> ph ) $=
      ( wsb wal stdpc4 sbid2 sylib ) ABCEZCFJCBEAJCBGACBDHI $.
  $}

  ${
    sbtr.nf $e |- F/ y ph $.
    sbtr.1 $e |- [ y / x ] ph $.
    $( A partial converse to ~ sbt .  If the substitution of a variable for a
       nonfree one in a wff gives a theorem, then the original wff is a
       theorem.  Usage of this theorem is discouraged because it depends on
       ~ ax-13 .  (Contributed by BJ, 15-Sep-2018.)
       (New usage is discouraged.) $)
    sbtr $p |- ph $=
      ( wsb sbtrt mpg ) ABCFACABCDGEH $.
  $}

  ${
    sb8.1 $e |- F/ y ph $.
    $( Substitution of variable in universal quantifier.  Usage of this theorem
       is discouraged because it depends on ~ ax-13 .  For a version requiring
       disjoint variables, but fewer axioms, see ~ sb8f .  (Contributed by NM,
       16-May-1993.)  (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof
       shortened by Jim Kingdon, 15-Jan-2018.)  (New usage is discouraged.) $)
    sb8 $p |- ( A. x ph <-> A. y [ y / x ] ph ) $=
      ( wsb nfs1 sbequ12 cbval ) AABCEBCDABCDFABCGH $.

    $( Substitution of variable in existential quantifier.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  For a version
       requiring disjoint variables, but fewer axioms, see ~ sb8ef .
       (Contributed by NM, 12-Aug-1993.)  (Revised by Mario Carneiro,
       6-Oct-2016.)  (Proof shortened by Jim Kingdon, 15-Jan-2018.)
       (New usage is discouraged.) $)
    sb8e $p |- ( E. x ph <-> E. y [ y / x ] ph ) $=
      ( wsb nfs1 sbequ12 cbvex ) AABCEBCDABCDFABCGH $.
  $}

  $( Commutation of quantification and substitution variables.  Usage of this
     theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
     NM, 5-Aug-1993.)  Allow a shortening of ~ sb9i .  (Revised by Wolf Lammen,
     15-Jun-2019.)  (New usage is discouraged.) $)
  sb9 $p |- ( A. x [ x / y ] ph <-> A. y [ y / x ] ph ) $=
    ( weq wal wsb wb sbequ12a equcoms sps dral1 wn nfnae wnf nfsb2 naecoms cbv2
    wi a1i pm2.61i ) BCDZBEZACBFZBEABCFZCEGUCUDBCUAUCUDGZBUECBACBHIZJKUBLZUCUDB
    CBCBMBCCMUCCNCBACBOPABCOUAUERUGUFSQT $.

  $( Commutation of quantification and substitution variables.  Usage of this
     theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
     NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 15-Jun-2019.)
     (New usage is discouraged.) $)
  sb9i $p |- ( A. x [ x / y ] ph -> A. y [ y / x ] ph ) $=
    ( wsb wal sb9 biimpi ) ACBDBEABCDCEABCFG $.

  ${
    $d y ph $.
    $( Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ".
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 29-May-2009.)  (New usage is discouraged.) $)
    sbhb $p |- ( ( ph -> A. x ph ) <-> A. y ( ph -> [ y / x ] ph ) ) $=
      ( wal wi wsb nfv sb8 imbi2i 19.21v bitr4i ) AABDZEAABCFZCDZEAMECDLNAABCAC
      GHIAMCJK $.
  $}

  ${
    $d y z $.
    nfsbd.1 $e |- F/ x ph $.
    nfsbd.2 $e |- ( ph -> F/ z ps ) $.
    $( Deduction version of ~ nfsb .  (Contributed by NM, 15-Feb-2013.)  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  Use
       ~ nfsbv instead.  (New usage is discouraged.) $)
    nfsbd $p |- ( ph -> F/ z [ y / x ] ps ) $=
      ( weq wal wsb wnf wn wi alrimi nfsb4t syl axc16nf pm2.61d2 ) AEDHEIZBCDJZ
      EKZABEKZCISLUAMAUBCFGNBCDEOPTEDEQR $.
  $}

  ${
    $d y z $.
    nfsb.1 $e |- F/ z ph $.
    $( If ` z ` is not free in ` ph ` , then it is not free in ` [ y / x ] ph `
       when ` y ` and ` z ` are distinct.  See ~ nfsbv for a version with an
       additional disjoint variable condition on ` x , z ` but not requiring
       ~ ax-13 .  (Contributed by Mario Carneiro, 11-Aug-2016.)  (Proof
       shortened by Wolf Lammen, 25-Feb-2024.)  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  Use ~ nfsbv instead.
       (New usage is discouraged.) $)
    nfsb $p |- F/ z [ y / x ] ph $=
      ( wsb wnf wtru nftru a1i nfsbd mptru ) ABCFDGHABCDBIADGHEJKL $.
  $}

  ${
    $d y z $.
    hbsb.1 $e |- ( ph -> A. z ph ) $.
    $( If ` z ` is not free in ` ph ` , then it is not free in ` [ y / x ] ph `
       when ` y ` and ` z ` are distinct.  (Contributed by NM, 12-Aug-1993.)
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       Use ~ hbsbw instead.  (New usage is discouraged.) $)
    hbsb $p |- ( [ y / x ] ph -> A. z [ y / x ] ph ) $=
      ( wsb nf5i nfsb nf5ri ) ABCFDABCDADEGHI $.
  $}

  ${
    $d y z $.
    sb7f.1 $e |- F/ z ph $.
    $( This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       disjoint.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-5 ,
       i.e., that does not have the concept of a variable not occurring in a
       formula.  (Definition ~ dfsb1 is also suitable, but its mixing of free
       and bound variables is distasteful to some logicians.)  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
       NM, 26-Jul-2006.)  (Revised by Mario Carneiro, 6-Oct-2016.)
       (New usage is discouraged.) $)
    sb7f $p |- ( [ y / x ] ph <->
               E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( wsb weq wa wex sb5f sbbii sbco2 sb5 3bitr3i ) ABDFZDCFBDGAHBIZDCFABCFDC
      GPHDIOPDCABDEJKABCDELPDCMN $.
  $}

  ${
    $d y z $.
    sb7h.1 $e |- ( ph -> A. z ph ) $.
    $( This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       disjoint.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-5 ,
       i.e., that does not have the concept of a variable not occurring in a
       formula.  (Definition ~ dfsb1 is also suitable, but its mixing of free
       and bound variables is distasteful to some logicians.)  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
       NM, 26-Jul-2006.)  (Proof shortened by Andrew Salmon, 25-May-2011.)
       (New usage is discouraged.) $)
    sb7h $p |- ( [ y / x ] ph <->
               E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( nf5i sb7f ) ABCDADEFG $.
  $}

  ${
    $d x y $.
    sb10f.1 $e |- F/ x ph $.
    $( Hao Wang's identity axiom P6 in Irving Copi, _Symbolic Logic_ (5th ed.,
       1979), p. 328.  In traditional predicate calculus, this is a sole axiom
       for identity from which the usual ones can be derived.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
       NM, 9-May-2005.)  (Revised by Mario Carneiro, 6-Oct-2016.)
       (New usage is discouraged.) $)
    sb10f $p |- ( [ y / z ] ph <-> E. x ( x = y /\ [ x / z ] ph ) ) $=
      ( weq wsb wa wex nfsb sbequ equsexv bicomi ) BCFADBGZHBIADCGZNOBCADCBEJAB
      CDKLM $.
  $}

  ${
    $d x y $.
    $( Check out ~ sbal for a version not dependent on ~ ax-13 .  A theorem
       used in elimination of disjoint variable restriction on ` x ` and ` z `
       by replacing it with a distinctor ` -. A. x x = z ` .  (Contributed by
       NM, 15-May-1993.)  (Proof shortened by Wolf Lammen, 3-Oct-2018.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    sbal1 $p |- ( -. A. x x = z ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wsb wb wa wi sb4b nfnae wnf nfeqf2 19.21t bicomd sbequ12 sps
      albid syl sylan9bbr alcom bitrdi adantl bitr4d ex dral2 bitr3d pm2.61d2 )
      BDEBFGZCDEZCFZABFZCDHZACDHZBFZIZUKUMGZURUKUSJUOULAKZBFZCFZUQUSUOULUNKZCFU
      KVBUNCDLUKVCVACBDCMUKULBNZVCVAIBDCOVDVAVCULABPQUATUBUSUQVBIUKUSUQUTCFZBFV
      BUSUPVEBCDBMACDLTUTBCUCUDUEUFUGUMUNUOUQULUNUOICUNCDRSAUPCDBULAUPICACDRSUH
      UIUJ $.
  $}

  ${
    $d z x $.
    $( Move quantifier in and out of substitution.  (Contributed by NM,
       2-Jan-2002.)  Remove a distinct variable constraint.  (Revised by Wolf
       Lammen, 24-Dec-2022.)  (Proof shortened by Wolf Lammen, 23-Sep-2023.)
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       Use ~ sbal instead.  (New usage is discouraged.) $)
    sbal2 $p |- ( -. A. x x = y ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wsb wb sbequ12 dral2 bitr3d adantl wa sb4b nfnae albid alcom
      sps wi bitrdi wnf nfeqf1 19.21t syl sylan9bbr bitr4d pm2.61dan ) BCEBFGZC
      DEZCFZABFZCDHZACDHZBFZIZUKUPUIUKULUMUOUJULUMICULCDJSAUNCDBUJAUNICACDJSKLM
      UIUKGZNUMUJULTZCFZUOUQUMUSIUIULCDOMUQUOUJATZBFZCFZUIUSUQUOUTCFZBFVBUQUNVC
      BCDBPACDOQUTBCRUAUIVAURCBCCPUIUJBUBVAURIBCDUCUJABUDUEQUFUGUH $.
  $}

  ${
    $d z w ph $.
    $( An equivalent expression for double existence.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  For a version requiring
       more disjoint variables, but fewer axioms, see ~ 2sb8ef .  (Contributed
       by Wolf Lammen, 2-Nov-2019.)  (New usage is discouraged.) $)
    2sb8e $p |- ( E. x E. y ph <->
                  E. z E. w [ z / x ] [ w / y ] ph ) $=
      ( wex wsb nfv sb8e exbii excom bitri nfsb 3bitri ) ACFZBFZACEGZBFZEFZQBDG
      ZDFZEFTEFDFPQEFZBFSOUBBACEAEHIJQBEKLRUAEQBDACEDADHMIJTEDKN $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Uniqueness and unique existence
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  ${
    $d x y $.  $d y ph $.
    $( An elementary proof of ~ moeu in disguise, connecting an expression
       characterizing uniqueness ( ~ df-mo ) to that of existential uniqueness
       ( ~ eu6 ).  No particular order of definition is required, as one can be
       derived from the other.  This is shown here and in ~ dfeumo .
       (Contributed by Wolf Lammen, 27-May-2019.) $)
    dfmoeu $p |- ( ( E. x ph -> E. y A. x ( ph <-> x = y ) ) <->
                      E. y A. x ( ph -> x = y ) ) $=
      ( wex weq wb wal wi wn alnex pm2.21 alimi sylbir 19.8ad biimp eximi nfia1
      ja wa com12 id ax12v embantd ancld albiim imbitrrdi exlimi eximdv impbii
      spsd ) ABDZABCEZFZBGZCDZHAULHZBGZCDZUKUOURUKIZUQCUSAIZBGUQABJUTUPBAULKLMN
      UNUQCUMUPBAULOLPRUKURUOUKUQUNCAUQUNHBUPUMBQAUQUQULAHBGZSUNAUQVAAUPVABAAUL
      VAAUAULAVAABCUBTUCUJUDAULBUEUFUGUHTUI $.

    $( An elementary proof showing the reverse direction of ~ dfmoeu .  Here
       the characterizing expression of existential uniqueness ( ~ eu6 ) is
       derived from that of uniqueness ( ~ df-mo ).  (Contributed by Wolf
       Lammen, 3-Oct-2023.) $)
    dfeumo $p |- ( ( E. x ph /\ E. y A. x ( ph -> x = y ) ) <->
                      E. y A. x ( ph <-> x = y ) ) $=
      ( weq wb wal wex wa ax6ev biimpr aleximi mpi exlimiv pm4.71ri abai dfmoeu
      wi anbi2i 3bitrri ) ABCDZEZBFZCGZABGZUCHUDUDUCQZHUDATQBFCGZHUCUDUBUDCUBTB
      GUDBCIUATABATJKLMNUDUCOUEUFUDABCPRS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Uniqueness: the at-most-one quantifier
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Token for the at-most-one quantifier. $)
  $c E* $.

  $( Extend wff definition to include the at-most-one quantifier ("there exists
     at most one ` x ` such that ` ph ` "). $)
  wmo $a wff E* x ph $.

  ${
    $d x y z $.  $d ph y z $.
    $( Soundness justification theorem for ~ df-mo .  (Contributed by NM,
       11-Mar-2010.)  Added this theorem by adapting the proof of ~ eujust .
       (Revised by BJ, 30-Sep-2022.) $)
    mojust $p |- ( E. y A. x ( ph -> x = y ) <-> E. z A. x ( ph -> x = z ) ) $=
      ( weq wi wal equequ2 imbi2d albidv cbvexvw ) ABCEZFZBGABDEZFZBGCDCDEZMOBP
      LNACDBHIJK $.
  $}

  ${
    $d x y z $.  $d ph y z $.
    mojust.1 $e |- ( E. y A. x ( ph -> x = y ) <->
                     E. z A. x ( ph -> x = z ) ) $.
    $( Define the at-most-one quantifier.  The expression ` E* x ph ` is read
       "there exists at most one ` x ` such that ` ph ` ".  This is also called
       the "uniqueness quantifier" but that expression is also used for the
       unique existential quantifier ~ df-eu , therefore we avoid that
       ambiguous name.

       Notation of [BellMachover] p. 460, whose definition we show as ~ mo3 .
       For other possible definitions see ~ moeu and ~ mo4 .

       Note that the definiens does not express "at-most-one" in the empty
       domain.  Since the hypothesis relies on ~ ax-6 , this case is excluded
       anyway.  Nevertheless, it was suggested to begin with the definition of
       uniqueness ( ~ eu6 ) and then define the at-most-one quantifier via
       ~ moeu .  Both ~ eu6 and ~ moeu remain valid in the empty domain.

       The hypothesis asserts that the definition is independent of the
       particular choice of the dummy variable ` y ` .  Without this
       hypothesis, ~ mojust would be derivable from propositional axioms alone:
       one could apply the definiens for ` E* x ph ` twice, using different
       dummy variables ` y ` and ` z ` , and then invoke ~ bitr3i to establish
       their equivalence.  This would jeopardize the independence of axioms, as
       demonstrated in an analoguous situation involving ~ df-ss to prove
       ~ ax-8 (see ~ in-ax8 ).

       Prefer ~ dfmo unless you can prove the hypothesis from fewer axioms in
       special cases.  (Contributed by Wolf Lammen, 27-May-2019.)  Make this
       the definition (which used to be ~ moeu , while this definition was then
       proved as ~ dfmo ).  (Revised by BJ, 30-Sep-2022.) $)
    df-mo $a |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $.
  $}

  ${
    $d x y z $.  $d ph y z $.
    $( Simplify definition ~ df-mo by removing its provable hypothesis.
       (Contributed by Wolf Lammen, 15-Feb-2026.) $)
    dfmo $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $=
      ( vz mojust df-mo ) ABCDABCDEF $.
  $}

  ${
    $d x y $.  $d ph y $.
    $( Nonexistence implies uniqueness.  (Contributed by BJ, 30-Sep-2022.)
       Avoid ~ ax-11 .  (Revised by Wolf Lammen, 16-Oct-2022.) $)
    nexmo $p |- ( -. E. x ph -> E* x ph ) $=
      ( vy wn wal weq wi wex wmo pm2.21 alimi alrimiv 19.2d bicomi dfmo 3imtr4i
      alnex ) ADZBEZABCFZGZBEZCHABHDZABISUBCSUBCRUABATJKLMSUCABQNABCOP $.
    $( $j usage 'nexmo' avoids 'ax-11'; $)
  $}

  $( Any proposition holds for some ` x ` or holds for at most one ` x ` .
     (Contributed by NM, 8-Mar-1995.)  Shorten proof and avoid ~ df-eu .
     (Revised by BJ, 14-Oct-2022.) $)
  exmo $p |- ( E. x ph \/ E* x ph ) $=
    ( wex wmo nexmo orri ) ABCABDABEF $.

  $( Absorption of existence condition by uniqueness.  (Contributed by NM,
     4-Nov-2002.)  Shorten proof and avoid ~ df-eu .  (Revised by BJ,
     14-Oct-2022.) $)
  moabs $p |- ( E* x ph <-> ( E. x ph -> E* x ph ) ) $=
    ( wmo wex wi ax-1 nexmo id ja impbii ) ABCZABDZKEKLFLKKABGKHIJ $.

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( The at-most-one quantifier reverses implication.  (Contributed by NM,
       22-Apr-1995.) $)
    moim $p |- ( A. x ( ph -> ps ) -> ( E* x ps -> E* x ph ) ) $=
      ( vy wi wal weq wex wmo imim1 al2imi eximdv dfmo 3imtr4g ) ABEZCFZBCDGZEZ
      CFZDHAQEZCFZDHBCIACIPSUADORTCABQJKLBCDMACDMN $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    moimi.1 $e |- ( ph -> ps ) $.
    $( The at-most-one quantifier reverses implication.  (Contributed by NM,
       15-Feb-2006.) $)
    moimi $p |- ( E* x ps -> E* x ph ) $=
      ( wi wmo moim mpg ) ABEBCFACFECABCGDH $.
  $}

  ${
    $d x ph $.
    moimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( The at-most-one quantifier reverses implication, deduction form.
       (Contributed by Thierry Arnoux, 25-Feb-2017.) $)
    moimdv $p |- ( ph -> ( E* x ch -> E* x ps ) ) $=
      ( wi wal wmo alrimiv moim syl ) ABCFZDGCDHBDHFALDEIBCDJK $.
  $}

  $( Equivalence theorem for the at-most-one quantifier.  (Contributed by BJ,
     7-Oct-2022.)  (Proof shortened by Wolf Lammen, 18-Feb-2023.) $)
  mobi $p |- ( A. x ( ph <-> ps ) -> ( E* x ph <-> E* x ps ) ) $=
    ( wb wal wi wa wmo albiim moim impbid21d imp sylbi ) ABDCEABFCEZBAFCEZGACHZ
    BCHZDZABCINORNOPQBACJABCJKLM $.

  ${
    mobii.1 $e |- ( ps <-> ch ) $.
    $( Formula-building rule for the at-most-one quantifier (inference form).
       (Contributed by NM, 9-Mar-1995.)  (Revised by Mario Carneiro,
       17-Oct-2016.) $)
    mobii $p |- ( E* x ps <-> E* x ch ) $=
      ( wb wmo mobi mpg ) ABEACFBCFECABCGDH $.
  $}

  ${
    $d x ph $.
    mobidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for the at-most-one quantifier (deduction form).
       (Contributed by Mario Carneiro, 7-Oct-2016.)  Reduce axiom dependencies
       and shorten proof.  (Revised by BJ, 7-Oct-2022.) $)
    mobidv $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      ( wb wal wmo alrimiv mobi syl ) ABCFZDGBDHCDHFALDEIBCDJK $.
  $}

  ${
    mobid.1 $e |- F/ x ph $.
    mobid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for the at-most-one quantifier (deduction form).
       (Contributed by NM, 8-Mar-1995.)  Remove dependency on ~ ax-10 ,
       ~ ax-11 , ~ ax-13 .  (Revised by BJ, 14-Oct-2022.)  (Proof shortened by
       Wolf Lammen, 18-Feb-2023.) $)
    mobid $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      ( wb wal wmo alrimi mobi syl ) ABCGZDHBDICDIGAMDEFJBCDKL $.
  $}

  $( If an implication holds for at most one value, then its consequent holds
     for at most one value.  See also ~ ala1 and ~ exa1 .  (Contributed by NM,
     28-Jul-1995.)  (Proof shortened by Wolf Lammen, 22-Dec-2018.) $)
  moa1 $p |- ( E* x ( ph -> ps ) -> E* x ps ) $=
    ( wi ax-1 moimi ) BABDCBAEF $.

  $( "At most one" is still the case when a conjunct is added.  (Contributed by
     NM, 22-Apr-1995.) $)
  moan $p |- ( E* x ph -> E* x ( ps /\ ph ) ) $=
    ( wa simpr moimi ) BADACBAEF $.

  ${
    moani.1 $e |- E* x ph $.
    $( "At most one" is still true when a conjunct is added, inference form.
       (Contributed by NM, 9-Mar-1995.) $)
    moani $p |- E* x ( ps /\ ph ) $=
      ( wmo wa moan ax-mp ) ACEBAFCEDABCGH $.
  $}

  $( "At most one" is still the case when a disjunct is removed.  (Contributed
     by NM, 5-Apr-2004.) $)
  moor $p |- ( E* x ( ph \/ ps ) -> E* x ph ) $=
    ( wo orc moimi ) AABDCABEF $.

  $( "At most one" imports disjunction to conjunction.  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  mooran1 $p |- ( ( E* x ph \/ E* x ps ) -> E* x ( ph /\ ps ) ) $=
    ( wmo wa simpl moimi moan jaoi ) ACDABEZCDBCDJACABFGBACHI $.

  $( "At most one" exports disjunction to conjunction.  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  mooran2 $p |- ( E* x ( ph \/ ps ) -> ( E* x ph /\ E* x ps ) ) $=
    ( wo wmo moor olc moimi jca ) ABDZCEACEBCEABCFBJCBAGHI $.

  ${
    $d x y $.  $d ph y $.
    $( Bound-variable hypothesis builder for the at-most-one quantifier.
       (Contributed by NM, 8-Mar-1995.)  (Revised by Mario Carneiro,
       7-Oct-2016.)  Adapt to new definition.  (Revised by BJ, 1-Oct-2022.) $)
    nfmo1 $p |- F/ x E* x ph $=
      ( vy wmo weq wi wal wex dfmo nfexa2 nfxfr ) ABDABCEFZBGCHBABCILBCJK $.
    $( $j usage 'nfmo1' avoids 'ax-12'; $)
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.  $d z ps $.
    nfmod2.1 $e |- F/ y ph $.
    nfmod2.2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
    $( Bound-variable hypothesis builder for the at-most-one quantifier.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  See
       ~ nfmodv for a version replacing the distinctor with a disjoint variable
       condition, not requiring ~ ax-13 .  (Contributed by Mario Carneiro,
       14-Nov-2016.)  Avoid ~ df-eu .  (Revised by BJ, 14-Oct-2022.)
       (New usage is discouraged.) $)
    nfmod2 $p |- ( ph -> F/ x E* y ps ) $=
      ( vz wmo weq wi wal wex dfmo nfv wn wa wnf nfeqf1 adantl nfimd nfald2
      nfexd nfxfrd ) BDHBDGIZJZDKZGLACBDGMAUFCGAGNAUECDEACDICKOZPBUDCFUGUDCQACD
      GRSTUAUBUC $.
  $}

  ${
    $d x y z $.  $d ph z $.  $d ps z $.
    nfmodv.1 $e |- F/ y ph $.
    nfmodv.2 $e |- ( ph -> F/ x ps ) $.
    $( Bound-variable hypothesis builder for the at-most-one quantifier.  See
       ~ nfmod for a version without disjoint variable conditions but requiring
       ~ ax-13 .  (Contributed by Mario Carneiro, 14-Nov-2016.)  (Revised by
       BJ, 28-Jan-2023.) $)
    nfmodv $p |- ( ph -> F/ x E* y ps ) $=
      ( vz wmo weq wi wal wex dfmo nfv nfvd nfimd nfald nfexd nfxfrd ) BDHBDGIZ
      JZDKZGLACBDGMAUBCGAGNAUACDEABTCFATCOPQRS $.
    $( $j usage 'nfmodv' avoids 'ax-13'; $)
  $}

  ${
    $d x y $.
    nfmov.1 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for the at-most-one quantifier.  See
       ~ nfmo for a version without disjoint variable conditions but requiring
       ~ ax-13 .  (Contributed by NM, 9-Mar-1995.)  (Revised by Wolf Lammen,
       2-Oct-2023.) $)
    nfmov $p |- F/ x E* y ph $=
      ( wmo wnf wtru nftru a1i nfmodv mptru ) ACEBFGABCCHABFGDIJK $.
    $( $j usage 'nfmov' avoids 'ax-13'; $)
  $}

  ${
    nfmod.1 $e |- F/ y ph $.
    nfmod.2 $e |- ( ph -> F/ x ps ) $.
    $( Bound-variable hypothesis builder for the at-most-one quantifier.
       Deduction version of ~ nfmo .  Usage of this theorem is discouraged
       because it depends on ~ ax-13 .  Use the weaker ~ nfmodv when possible.
       (Contributed by Mario Carneiro, 14-Nov-2016.)
       (New usage is discouraged.) $)
    nfmod $p |- ( ph -> F/ x E* y ps ) $=
      ( wnf weq wal wn adantr nfmod2 ) ABCDEABCGCDHCIJFKL $.
  $}

  ${
    nfmo.1 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for the at-most-one quantifier.  Note
       that ` x ` and ` y ` need not be disjoint.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  Use the weaker ~ nfmov when
       possible.  (Contributed by NM, 9-Mar-1995.)
       (New usage is discouraged.) $)
    nfmo $p |- F/ x E* y ph $=
      ( wmo wnf wtru nftru a1i nfmod mptru ) ACEBFGABCCHABFGDIJK $.
  $}

  ${
    $d x y z $.  $d ph z $.
    mof.1 $e |- F/ y ph $.
    $( Version of ~ df-mo with disjoint variable condition replaced by
       nonfreeness hypothesis.  (Contributed by NM, 8-Mar-1995.)  Extract
       ~ dfmo from this proof, and prove ~ mof from it (as of 30-Sep-2022,
       directly from ~ df-mo ).  (Revised by Wolf Lammen, 28-May-2019.)  Avoid
       ~ ax-13 .  (Revised by Wolf Lammen, 16-Oct-2022.) $)
    mof $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $=
      ( vz wmo weq wi wal wex dfmo nfv nfim equequ2 imbi2d albidv cbvexv1 bitri
      nfal ) ABFABEGZHZBIZEJABCGZHZBIZCJABEKUBUEECUACBATCDTCLMSUEELECGZUAUDBUFT
      UCAECBNOPQR $.
  $}

  ${
    $d x y z $.  $d ph z $.
    mo3.nf $e |- F/ y ph $.
    $( Alternate definition of the at-most-one quantifier.  Definition of
       [BellMachover] p. 460, except that definition has the side condition
       that ` y ` not occur in ` ph ` in place of our hypothesis.  (Contributed
       by NM, 8-Mar-1995.)  (Proof shortened by Wolf Lammen, 18-Aug-2019.)
       Remove dependency on ~ ax-13 .  (Revised by BJ and WL, 29-Jan-2023.) $)
    mo3 $p |- ( E* x ph <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( vz wmo wsb wa weq wi wal nfmo1 nfmov wex dfmo sp spsbim equsb3 imbitrdi
      alrimi anim12d equtr2 syl6 exlimiv sylbi nfs1v pm3.21 alimd com12 aleximi
      imim1d sb8ef mof 3imtr4g moabs sylibr alcoms impbii ) ABFZAABCGZHZBCIZJZC
      KZBKUSVDBABLUSVCCACBDMUSABEIZJZBKZENVCABEOVGVCEVGVAVECEIZHVBVGAVEUTVHVFBP
      VGUTVEBCGVHAVEBCQBCERSUABCEUBUCUDUETTVCUSCBVCBKZCKZABNZUSJUSVJUTCNAVBJZBK
      ZCNVKUSVIUTVMCUTVIVMUTVCVLBABCUFUTAVAVBUTAUGUKUHUIUJABCDULABCDUMUNABUOUPU
      QUR $.
  $}

  ${
    $d x y $.
    mo.nf $e |- F/ y ph $.
    $( Equivalent definitions of "there exists at most one".  (Contributed by
       NM, 7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.)  (Proof
       shortened by Wolf Lammen, 2-Dec-2018.) $)
    mo $p |- ( E. y A. x ( ph -> x = y ) <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( weq wi wal wex wmo wsb wa mof mo3 bitr3i ) ABCEZFBGCHABIAABCJKOFCGBGABC
      DLABCDMN $.
  $}

  ${
    $d x y $.  $d y z ph $.  $d x z ps $.
    mo4.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( At-most-one quantifier expressed using implicit substitution.  This
       theorem is also a direct consequence of ~ mo4f , but this proof is based
       on fewer axioms.

       By the way, swapping ` x ` , ` y ` and ` ph ` , ` ps ` leads to an
       expression for ` E* y ps ` , which is equivalent to ` E* x ph ` (is a
       proof line), so the right hand side is a rare instance of an expression
       where swapping the quantifiers can be done without ~ ax-11 .
       (Contributed by NM, 26-Jul-1995.)  Reduce axiom usage.  (Revised by Wolf
       Lammen, 18-Oct-2023.) $)
    mo4 $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $=
      ( vz wmo wa weq wal wex dfmo equequ1 imbi12d cbvalvw biimpi pm2.27 alimdv
      wi sylibr im2anan9 equtr2 syl6com ex com12 exlimiv cbvexvw biimpri ax6evr
      mpcom sylbi pm3.2 imim1d ax7 syl8 com4r impcom impancom eximdv mpi expcom
      aleximi ax5e syl56 exbii 3bitr4i moabs bitri impbii ) ACGZABHZCDIZSZDJZCJ
      ZVJACFIZSZCJZFKZVOACFLZVRVOFBDFIZSZDJZVRVOVRWCVQWBCDVLABVPWAECDFMNOZPWCVQ
      VNCVQWCVNVQWBVMDVQWBVMVKVQWBHVPWAHVLAVQVPBWBWAAVPQBWAQUACDFUBUCUDRUERUJUF
      UKVOBDKZBDGZSZVJWEACKZVOWFCKWFWHWEABCDEUGUHVNAWFCAVNWFAVNHZWCFKZWFWIVPFKW
      JFCUIWIVPWCFAVPVNWCAVPHVMWBDVPAVMWBSAVMBVPWAAVMBVLVPWASABVKVLABULUMCDFUNU
      OUPUQRURUSUTBDFLZTVAVBWFCVCVDVJWFWGVSWJVJWFVRWCFWDVEVTWKVFBDVGVHTVI $.
  $}

  ${
    $d x y $.  $d y ph $.
    mo4f.1 $e |- F/ x ps $.
    mo4f.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( At-most-one quantifier expressed using implicit substitution.  Note that
       the disjoint variable condition on ` y , ph ` can be replaced by the
       nonfreeness hypothesis ` |- F/ y ph ` with essentially the same proof.
       (Contributed by NM, 10-Apr-2004.)  Remove dependency on ~ ax-13 .
       (Revised by Wolf Lammen, 19-Jan-2023.) $)
    mo4f $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $=
      ( wmo wsb wa weq wi wal nfv mo3 sbiev anbi2i imbi1i 2albii bitri ) ACGAAC
      DHZIZCDJZKZDLCLABIZUBKZDLCLACDADMNUCUECDUAUDUBTBAABCDEFOPQRS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Unique existence: the unique existential quantifier
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Token for the unique existential quantifier. $)
  $c E! $.

  $( Extend wff definition to include the unique existential quantifier ("there
     exists a unique ` x ` such that ` ph ` "). $)
  weu $a wff E! x ph $.

  $( Define the existential uniqueness quantifier.  This expresses unique
     existence, or existential uniqueness, which is the conjunction of
     existence ( ~ df-ex ) and uniqueness ( ~ df-mo ).  The expression
     ` E! x ph ` is read "there exists exactly one ` x ` such that ` ph ` " or
     "there exists a unique ` x ` such that ` ph ` ".  This is also called the
     "uniqueness quantifier" but that expression is also used for the
     at-most-one quantifier ~ df-mo , therefore we avoid that ambiguous name.

     Definition 10.1 of [BellMachover] p. 97; also Definition *14.02 of
     [WhiteheadRussell] p. 175.  Other possible definitions are given by
     ~ eu1 , ~ eu2 , ~ eu3v , and ~ eu6 .  As for double unique existence,
     beware that the expression ` E! x E! y ph ` means "there exists a unique
     ` x ` such that there exists a unique ` y ` such that ` ph ` " which is a
     weaker property than "there exists exactly one ` x ` and one ` y ` such
     that ` ph ` " (see ~ 2eu4 ).  (Contributed by NM, 12-Aug-1993.)  Make this
     the definition (which used to be ~ eu6 , while this definition was then
     proved as ~ dfeu ).  (Revised by BJ, 30-Sep-2022.) $)
  df-eu $a |- ( E! x ph <-> ( E. x ph /\ E* x ph ) ) $.

  ${
    $d x y $.  $d ph y $.
    $( An alternate way to express existential uniqueness.  (Contributed by NM,
       8-Jul-1994.)  Replace a nonfreeness hypothesis with a disjoint variable
       condition on ` ph ` , ` y ` to reduce axiom usage.  (Revised by Wolf
       Lammen, 29-May-2019.) $)
    eu3v $p |- ( E! x ph <-> ( E. x ph /\ E. y A. x ( ph -> x = y ) ) ) $=
      ( weu wex wmo wa weq wi wal df-eu dfmo anbi2i bitri ) ABDABEZABFZGOABCHIB
      JCEZGABKPQOABCLMN $.
  $}

  ${
    $d w x y $.  $d x z $.  $d y ph $.  $d w z ph $.
    $( Soundness justification theorem for ~ eu6 when this was the definition
       of the unique existential quantifier (note that ` y ` and ` z ` need not
       be disjoint, although the weaker theorem with that disjoint variable
       condition added would be enough to justify the soundness of the
       definition).  See ~ eujustALT for a proof that provides an example of
       how it can be achieved through the use of ~ dvelim .  (Contributed by
       NM, 11-Mar-2010.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    eujust $p |- ( E. y A. x ( ph <-> x = y )
               <-> E. z A. x ( ph <-> x = z ) ) $=
      ( vw weq wb wal wex equequ2 bibi2d albidv cbvexvw bitri ) ABCFZGZBHZCIABE
      FZGZBHZEIABDFZGZBHZDIQTCECEFZPSBUDORACEBJKLMTUCEDEDFZSUBBUERUAAEDBJKLMN
      $.

    $( Alternate proof of ~ eujust illustrating the use of ~ dvelim .
       (Contributed by NM, 11-Mar-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eujustALT $p |- ( E. y A. x ( ph <-> x = y )
                  <-> E. z A. x ( ph <-> x = z ) ) $=
      ( vw weq wal wb wex equequ2 bibi2d albidv sps wn hbnae ax-5 notbid dvelim
      wi df-ex drex1 alrimih naecoms a1i cbv2h syl 3bitr4g pm2.61i ) CDFZCGZABC
      FZHZBGZCIZABDFZHZBGZDIZHUMUQCDUIUMUQHCUIULUPBUIUKUOACDBJKLZMUAUJNZUMNZCGZ
      NUQNZDGZNUNURUTVBVDUTUTDGZCGVBVDHUTVECCDCOCDDOUBUTVAVCCDVAVADGSDCABEFZHZB
      GZNZVADCEVIDPECFZVHUMVJVGULBVJVFUKAECBJKLQRUCVIVCCDEVICPEDFZVHUQVKVGUPBVK
      VFUOAEDBJKLQRUIVAVCHSUTUIUMUQUSQUDUEUFQUMCTUQDTUGUH $.
  $}

  ${
    $d x y z $.  $d y z ph $.
    $( Lemma of ~ eu6im .  A dissection of an idiom characterizing existential
       uniqueness.  (Contributed by NM, 12-Aug-1993.)  This used to be the
       definition of the unique existential quantifier, while ~ df-eu was then
       proved as ~ dfeu .  (Revised by BJ, 30-Sep-2022.)  (Proof shortened by
       Wolf Lammen, 3-Jan-2023.)  Extract common proof lines.  (Revised by Wolf
       Lammen, 3-Mar-2023.) $)
    eu6lem $p |- ( E. y A. x ( ph <-> x = y ) <->
          ( E. y A. x ( x = y -> ph ) /\ E. z A. x ( ph -> x = z ) ) ) $=
      ( weq wb wal wex wi wa 19.42v alsyl equvelv sylib pm4.71i albiim biancomi
      equequ2 imbi2d exbii albidv anbi2d bitrid pm5.32ri bitr4i ax6evr 3bitr4ri
      biantru exdistrv bitri ) ABCEZFBGZCHUKAIBGZABDEZIZBGZJZDHZCHUMCHUPDHJULUR
      CULCDEZJZDHULUSDHZJURULULUSDKUQUTDUQUQUSJUTUQUSUQUKUNIBGUSUKAUNBLCDBMNOUS
      ULUQULUMAUKIZBGZJUSUQULUMVCAUKBPQUSVCUPUMUSVBUOBUSUKUNACDBRSUAUBUCUDUETVA
      ULDCUFUHUGTUMUPCDUIUJ $.

    $( Alternate definition of the unique existential quantifier ~ df-eu not
       using the at-most-one quantifier.  (Contributed by NM, 12-Aug-1993.)
       This used to be the definition of the unique existential quantifier,
       while ~ df-eu was then proved as ~ dfeu .  (Revised by BJ, 30-Sep-2022.)
       (Proof shortened by Wolf Lammen, 3-Jan-2023.)  Remove use of ~ ax-11 .
       (Revised by SN, 21-Sep-2023.) $)
    eu6 $p |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $=
      ( weu wex weq wb wal wa wi dfmoeu anbi2i abai 3bitr4ri ancom biimpr alimi
      eu3v eximi exsbim syl biantru 3bitr4i bitri ) ABDZABEZABCFZGZBHZCEZIZUJUF
      UFUJJZIUFAUGJBHCEZIUKUEULUMUFABCKLUFUJMABCRNUJUFIUJUJUFJZIUKUJUJUFMUFUJOU
      NUJUJUGAJZBHZCEUFUIUPCUHUOBAUGPQSABCTUAUBUCUD $.

    $( One direction of ~ eu6 needs fewer axioms.  (Contributed by Wolf Lammen,
       2-Mar-2023.) $)
    eu6im $p |- ( E. y A. x ( ph <-> x = y ) -> E! x ph ) $=
      ( vz weq wi wal wex wa wb weu exsbim anim1i eu6lem eu3v 3imtr4i ) BCEZAFB
      GCHZABDEFBGDHZIABHZSIAQJBGCHABKRTSABCLMABCDNABDOP $.
  $}

  ${
    $d x y z $.  $d ph z $.
    euf.1 $e |- F/ y ph $.
    $( Version of ~ eu6 with disjoint variable condition replaced by
       nonfreeness hypothesis.  (Contributed by NM, 12-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 30-Oct-2018.)  Avoid ~ ax-13 .  (Revised by
       Wolf Lammen, 16-Oct-2022.) $)
    euf $p |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $=
      ( vz weu weq wb wal wex eu6 nfbi nfal equequ2 bibi2d albidv cbvexv1 bitri
      nfv ) ABFABEGZHZBIZEJABCGZHZBIZCJABEKUBUEECUACBATCDTCSLMUEESECGZUAUDBUFTU
      CAECBNOPQR $.
  $}

  $( Existential uniqueness implies existence.  (Contributed by NM,
     15-Sep-1993.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.)  (Proof
     shortened by Wolf Lammen, 4-Dec-2018.)  (Proof shortened by BJ,
     7-Oct-2022.) $)
  euex $p |- ( E! x ph -> E. x ph ) $=
    ( weu wex wmo df-eu simplbi ) ABCABDABEABFG $.

  $( Existential uniqueness implies uniqueness.  (Contributed by NM,
     23-Mar-1995.) $)
  eumo $p |- ( E! x ph -> E* x ph ) $=
    ( weu wex wmo df-eu simprbi ) ABCABDABEABFG $.

  ${
    eumoi.1 $e |- E! x ph $.
    $( Uniqueness inferred from existential uniqueness.  (Contributed by NM,
       5-Apr-1995.) $)
    eumoi $p |- E* x ph $=
      ( weu wmo eumo ax-mp ) ABDABECABFG $.
  $}

  $( Existence implies that uniqueness is equivalent to unique existence.
     (Contributed by NM, 5-Apr-2004.) $)
  exmoeub $p |- ( E. x ph -> ( E* x ph <-> E! x ph ) ) $=
    ( weu wex wmo df-eu baibr ) ABCABDABEABFG $.

  $( Existence is equivalent to uniqueness implying existential uniqueness.
     (Contributed by NM, 5-Apr-2004.)  (Proof shortened by Wolf Lammen,
     5-Dec-2018.)  (Proof shortened by BJ, 7-Oct-2022.) $)
  exmoeu $p |- ( E. x ph <-> ( E* x ph -> E! x ph ) ) $=
    ( wex wmo weu wi exmoeub biimpd nexmo con1i euex ja impbii ) ABCZABDZABEZFN
    OPABGHOPNNOABIJABKLM $.

  $( Uniqueness implies that existence is equivalent to unique existence.
     (Contributed by BJ, 7-Oct-2022.) $)
  moeuex $p |- ( E* x ph -> ( E. x ph <-> E! x ph ) ) $=
    ( weu wex wmo df-eu rbaibr ) ABCABDABEABFG $.

  $( Uniqueness is equivalent to existence implying unique existence.
     Alternate definition of the at-most-one quantifier, in terms of the
     existential quantifier and the unique existential quantifier.
     (Contributed by NM, 8-Mar-1995.)  This used to be the definition of the
     at-most-one quantifier, while ~ df-mo was then proved as ~ dfmo2 .
     (Revised by BJ, 30-Sep-2022.) $)
  moeu $p |- ( E* x ph <-> ( E. x ph -> E! x ph ) ) $=
    ( wmo wex wi weu moabs exmoeub pm5.74i bitri ) ABCZABDZKELABFZEABGLKMABHIJ
    $.

  $( Equivalence theorem for the unique existential quantifier.  Theorem
     *14.271 in [WhiteheadRussell] p. 192.  (Contributed by Andrew Salmon,
     11-Jul-2011.)  Reduce dependencies on axioms.  (Revised by BJ,
     7-Oct-2022.) $)
  eubi $p |- ( A. x ( ph <-> ps ) -> ( E! x ph <-> E! x ps ) ) $=
    ( wb wal wex wmo wa weu exbi mobi anbi12d df-eu 3bitr4g ) ABDCEZACFZACGZHBC
    FZBCGZHACIBCIOPRQSABCJABCKLACMBCMN $.

  ${
    eubii.1 $e |- ( ph <-> ps ) $.
    $( Introduce unique existential quantifier to both sides of an equivalence.
       (Contributed by NM, 9-Jul-1994.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)
    eubii $p |- ( E! x ph <-> E! x ps ) $=
      ( wb weu eubi mpg ) ABEACFBCFECABCGDH $.
  $}

  ${
    $d x ph $.
    eubidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for unique existential quantifier (deduction
       form).  (Contributed by NM, 9-Jul-1994.)  Reduce axiom dependencies and
       shorten proof.  (Revised by BJ, 7-Oct-2022.) $)
    eubidv $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      ( wb wal weu alrimiv eubi syl ) ABCFZDGBDHCDHFALDEIBCDJK $.
  $}

  ${
    eubid.1 $e |- F/ x ph $.
    eubid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for the unique existential quantifier (deduction
       form).  (Contributed by NM, 9-Jul-1994.)  (Proof shortened by Wolf
       Lammen, 19-Feb-2023.) $)
    eubid $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      ( wb wal weu alrimi eubi syl ) ABCGZDHBDICDIGAMDEFJBCDKL $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Alternate version of ~ nfeu1 with a shorter proof but using ~ ax-12 .
       Bound-variable hypothesis builder for uniqueness.  See also ~ nfeu1 .
       (Contributed by NM, 9-Jul-1994.)  (Revised by Mario Carneiro,
       7-Oct-2016.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nfeu1ALT $p |- F/ x E! x ph $=
      ( vy weu weq wb wal wex eu6 nfexa2 nfxfr ) ABDABCEFZBGCHBABCILBCJK $.
  $}

  $( Bound-variable hypothesis builder for uniqueness.  See ~ nfeu1ALT for a
     shorter proof using ~ ax-12 .  This proof illustrates the systematic way
     of proving nonfreeness in a defined expression: consider the definiens as
     a tree whose nodes are its subformulas, and prove by tree-induction the
     nonfreeness of each node, starting from the leaves (generally using ~ nfv
     or nf* theorems for previously defined expressions) and up to the root.
     Here, the definiens is a conjunction of two previously defined
     expressions, which automatically yields the present proof.  (Contributed
     by NM, 9-Jul-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.)  (Revised by
     BJ, 2-Oct-2022.)  (Proof modification is discouraged.) $)
  nfeu1 $p |- F/ x E! x ph $=
    ( weu wex wmo wa df-eu nfe1 nfmo1 nfan nfxfr ) ABCABDZABEZFBABGLMBABHABIJK
    $.
  $( $j usage 'nfeu1' avoids 'ax-12'; $)

  ${
    nfeud2.1 $e |- F/ y ph $.
    nfeud2.2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
    $( Bound-variable hypothesis builder for uniqueness.  (Contributed by Mario
       Carneiro, 14-Nov-2016.)  (Proof shortened by Wolf Lammen, 4-Oct-2018.)
       (Proof shortened by BJ, 14-Oct-2022.)  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  Use ~ nfeudw instead.
       (New usage is discouraged.) $)
    nfeud2 $p |- ( ph -> F/ x E! y ps ) $=
      ( weu wex wmo wa df-eu nfexd2 nfmod2 nfand nfxfrd ) BDGBDHZBDIZJACBDKAPQC
      ABCDEFLABCDEFMNO $.
  $}

  ${
    $d x y $.
    nfeudw.1 $e |- F/ y ph $.
    nfeudw.2 $e |- ( ph -> F/ x ps ) $.
    $( Bound-variable hypothesis builder for the unique existential quantifier.
       Deduction version of ~ nfeu .  Version of ~ nfeud with a disjoint
       variable condition, which does not require ~ ax-13 .  (Contributed by
       NM, 15-Feb-2013.)  Avoid ~ ax-13 .  (Revised by GG, 10-Jan-2024.) $)
    nfeudw $p |- ( ph -> F/ x E! y ps ) $=
      ( weu wex wmo wa df-eu nfexd nfmodv nfand nfxfrd ) BDGBDHZBDIZJACBDKAPQCA
      BCDEFLABCDEFMNO $.
    $( $j usage 'nfeudw' avoids 'ax-13'; $)
  $}

  ${
    nfeud.1 $e |- F/ y ph $.
    nfeud.2 $e |- ( ph -> F/ x ps ) $.
    $( Bound-variable hypothesis builder for the unique existential quantifier.
       Deduction version of ~ nfeu .  Usage of this theorem is discouraged
       because it depends on ~ ax-13 .  Use the weaker ~ nfeudw when possible.
       (Contributed by NM, 15-Feb-2013.)  (Revised by Mario Carneiro,
       7-Oct-2016.)  (New usage is discouraged.) $)
    nfeud $p |- ( ph -> F/ x E! y ps ) $=
      ( wnf weq wal wn adantr nfeud2 ) ABCDEABCGCDHCIJFKL $.
  $}

  ${
    $d x y $.
    nfeuw.1 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for the unique existential quantifier.
       Version of ~ nfeu with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by NM, 8-Mar-1995.)  Avoid ~ ax-13 .
       (Revised by GG, 10-Jan-2024.) $)
    nfeuw $p |- F/ x E! y ph $=
      ( weu wnf wtru nftru a1i nfeudw mptru ) ACEBFGABCCHABFGDIJK $.
    $( $j usage 'nfeuw' avoids 'ax-13'; $)
  $}

  ${
    nfeu.1 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for the unique existential quantifier.
       Note that ` x ` and ` y ` need not be disjoint.  Usage of this theorem
       is discouraged because it depends on ~ ax-13 .  Use the weaker ~ nfeuw
       when possible.  (Contributed by NM, 8-Mar-1995.)  (Revised by Mario
       Carneiro, 7-Oct-2016.)  (New usage is discouraged.) $)
    nfeu $p |- F/ x E! y ph $=
      ( weu wnf wtru nftru a1i nfeud mptru ) ACEBFGABCCHABFGDIJK $.
  $}

  $( Rederive ~ df-eu from the old definition ~ eu6 .  (Contributed by NM,
     23-Mar-1995.)  (Proof shortened by Wolf Lammen, 25-May-2019.)  (Proof
     shortened by BJ, 7-Oct-2022.)  (Proof modification is discouraged.)  Use
     ~ df-eu instead.  (New usage is discouraged.) $)
  dfeu $p |- ( E! x ph <-> ( E. x ph /\ E* x ph ) ) $=
    ( wex weu wa wi wmo abai euex pm4.71ri moeu anbi2i 3bitr4i ) ABCZABDZENNOFZ
    EONABGZENOHONABIJQPNABKLM $.

  ${
    $d x y $.  $d y ph $.
    $( Rederive ~ df-mo from the old definition ~ moeu .  (Contributed by Wolf
       Lammen, 27-May-2019.)  (Proof modification is discouraged.)  Use ~ dfmo
       instead.  (New usage is discouraged.) $)
    dfmo2 $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $=
      ( wmo wex weu wi weq wb wal moeu eu6 imbi2i dfmoeu 3bitri ) ABDABEZABFZGP
      ABCHZIBJCEZGARGBJCEABKQSPABCLMABCNO $.
  $}

  ${
    $d x y z $.
    $( There exists a unique set equal to a given set.  Special case of ~ eueqi
       proved using only predicate calculus.  The proof needs ` y = z ` be free
       of ` x ` .  This is ensured by having ` x ` and ` y ` be distinct.
       Alternately, a distinctor ` -. A. x x = y ` could have been used
       instead.  See ~ eueq and ~ eueqi for classes.  (Contributed by Stefan
       Allan, 4-Dec-2008.)  (Proof shortened by Wolf Lammen, 8-Sep-2019.)
       Reduce axiom usage.  (Revised by Wolf Lammen, 1-Mar-2023.) $)
    euequ $p |- E! x x = y $=
      ( vz weq weu wex wi wal ax6ev equeuclr alrimiv eximii eu3v mpbir2an ) ABD
      ZAEOAFOACDGZAHZCFABICBDZQCCBIRPACABJKLOACMN $.
  $}

  $( substitution $)

  ${
    $d w y z $.  $d ph z w $.  $d w x z $.
    sb8eulem.nfsb $e |- F/ y [ w / x ] ph $.
    $( Lemma.  Factor out the common proof skeleton of ~ sb8euv and ~ sb8eu .
       Variable substitution in unique existential quantifier.  (Contributed by
       NM, 7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.)  (Proof
       shortened by Wolf Lammen, 24-Aug-2019.)  Factor out common proof lines.
       (Revised by Wolf Lammen, 9-Feb-2023.) $)
    sb8eulem $p |- ( E! x ph <-> E! y [ y / x ] ph ) $=
      ( vz weq wb wal wex wsb weu sb8v equsb3 sblbis albii nfv nfbi sbequ eu6
      equequ1 bibi12d cbvalv1 3bitri exbii 3bitr4i ) ABFGZHZBIZFJABCKZCFGZHZCIZ
      FJABLUJCLUIUMFUIUHBDKZDIABDKZDFGZHZDIUMUHBDMUNUQDUGUPABDBDFNOPUQULDCUOUPC
      EUPCQRULDQDCGUOUJUPUKADCBSDCFUAUBUCUDUEABFTUJCFTUF $.
  $}

  ${
    $d w x y $.  $d ph w $.
    sb8euv.nf $e |- F/ y ph $.
    $( Variable substitution in unique existential quantifier.  Version of
       ~ sb8eu requiring more disjoint variables, but fewer axioms.
       (Contributed by NM, 7-Aug-1994.)  (Revised by Wolf Lammen,
       7-Feb-2023.) $)
    sb8euv $p |- ( E! x ph <-> E! y [ y / x ] ph ) $=
      ( vw nfsbv sb8eulem ) ABCEABECDFG $.
    $( $j usage 'sb8euv' avoids 'ax-13'; $)
  $}

  ${
    $d w y $.  $d ph w $.  $d w x $.
    sb8eu.1 $e |- F/ y ph $.
    $( Variable substitution in unique existential quantifier.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  For a version
       requiring more disjoint variables, but fewer axioms, see ~ sb8euv .
       (Contributed by NM, 7-Aug-1994.)  (Revised by Mario Carneiro,
       7-Oct-2016.)  (Proof shortened by Wolf Lammen, 24-Aug-2019.)
       (New usage is discouraged.) $)
    sb8eu $p |- ( E! x ph <-> E! y [ y / x ] ph ) $=
      ( vw nfsb sb8eulem ) ABCEABECDFG $.

    $( Variable substitution for the at-most-one quantifier.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 .  (Contributed by
       Alexander van der Vekens, 17-Jun-2017.)  (New usage is discouraged.) $)
    sb8mo $p |- ( E* x ph <-> E* y [ y / x ] ph ) $=
      ( wex weu wi wsb wmo sb8e sb8eu imbi12i moeu 3bitr4i ) ABEZABFZGABCHZCEZQ
      CFZGABIQCIORPSABCDJABCDKLABMQCMN $.
  $}

  ${
    $d x y $.  $d x z ps $.  $d y z ph $.
    cbvmovw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.  See
       ~ cbvmo and ~ cbvmow for versions with fewer disjoint variable
       conditions but requiring more axioms.  (Contributed by NM, 9-Mar-1995.)
       (Revised by GG, 30-Sep-2024.) $)
    cbvmovw $p |- ( E* x ph <-> E* y ps ) $=
      ( vz weq wi wal wex wmo equequ1 imbi12d cbvalvw exbii dfmo 3bitr4i ) ACFG
      ZHZCIZFJBDFGZHZDIZFJACKBDKTUCFSUBCDCDGABRUAECDFLMNOACFPBDFPQ $.
    $( $j usage 'cbvmovw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y z $.  $d ph z $.  $d ps z $.
    cbvmow.1 $e |- F/ y ph $.
    cbvmow.2 $e |- F/ x ps $.
    cbvmow.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbvmo with a disjoint variable condition, which does not
       require ~ ax-10 , ~ ax-13 .  (Contributed by NM, 9-Mar-1995.)  (Revised
       by GG, 23-May-2024.) $)
    cbvmow $p |- ( E* x ph <-> E* y ps ) $=
      ( vz weq wi wal wex wmo nfv nfim equequ1 imbi12d cbvalv1 exbii dfmo
      3bitr4i ) ACHIZJZCKZHLBDHIZJZDKZHLACMBDMUDUGHUCUFCDAUBDEUBDNOBUECFUECNOCD
      IABUBUEGCDHPQRSACHTBDHTUA $.
    $( $j usage 'cbvmow' avoids 'ax-10' 'ax-13'; $)
  $}

  ${
    cbvmo.1 $e |- F/ y ph $.
    cbvmo.2 $e |- F/ x ps $.
    cbvmo.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  Use the
       weaker ~ cbvmow , ~ cbvmovw when possible.  (Contributed by NM,
       9-Mar-1995.)  (Revised by Andrew Salmon, 8-Jun-2011.)  (Proof shortened
       by Wolf Lammen, 4-Jan-2023.)  (New usage is discouraged.) $)
    cbvmo $p |- ( E* x ph <-> E* y ps ) $=
      ( wmo wsb sb8mo sbie mobii bitri ) ACHACDIZDHBDHACDEJNBDABCDFGKLM $.
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    cbveuvw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.  See
       ~ cbveu for a version with fewer disjoint variable conditions but
       requiring more axioms.  (Contributed by NM, 25-Nov-1994.)  (Revised by
       GG, 30-Sep-2024.) $)
    cbveuvw $p |- ( E! x ph <-> E! y ps ) $=
      ( wex wmo wa weu cbvexvw cbvmovw anbi12i df-eu 3bitr4i ) ACFZACGZHBDFZBDG
      ZHACIBDIOQPRABCDEJABCDEKLACMBDMN $.
    $( $j usage 'cbveuvw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.
    cbveuw.1 $e |- F/ y ph $.
    cbveuw.2 $e |- F/ x ps $.
    cbveuw.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Version of ~ cbveu with a disjoint variable condition, which does not
       require ~ ax-10 , ~ ax-13 .  (Contributed by NM, 25-Nov-1994.)  (Revised
       by GG, 23-May-2024.) $)
    cbveuw $p |- ( E! x ph <-> E! y ps ) $=
      ( wex wmo wa weu cbvexv1 cbvmow anbi12i df-eu 3bitr4i ) ACHZACIZJBDHZBDIZ
      JACKBDKQSRTABCDEFGLABCDEFGMNACOBDOP $.
    $( $j usage 'cbveuw' avoids 'ax-10' 'ax-13'; $)
  $}

  ${
    cbveu.1 $e |- F/ y ph $.
    cbveu.2 $e |- F/ x ps $.
    cbveu.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .  Use the
       weaker ~ cbveuw , ~ cbveuvw when possible.  (Contributed by NM,
       25-Nov-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.)
       (New usage is discouraged.) $)
    cbveu $p |- ( E! x ph <-> E! y ps ) $=
      ( weu wsb sb8eu sbie eubii bitri ) ACHACDIZDHBDHACDEJNBDABCDFGKLM $.

    $( Alternative proof of ~ cbveu .  Since ~ df-eu combines two other
       quantifiers, one can base this theorem on their associated 'change
       bounded variable' kind of theorems as well.  (Contributed by Wolf
       Lammen, 5-Jan-2023.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    cbveuALT $p |- ( E! x ph <-> E! y ps ) $=
      ( wex wmo wa weu cbvex cbvmo anbi12i df-eu 3bitr4i ) ACHZACIZJBDHZBDIZJAC
      KBDKQSRTABCDEFGLABCDEFGMNACOBDOP $.
  $}

  ${
    $d x y $.
    eu2.nf $e |- F/ y ph $.
    $( An alternate way of defining existential uniqueness.  Definition 6.10 of
       [TakeutiZaring] p. 26.  (Contributed by NM, 8-Jul-1994.)  (Proof
       shortened by Wolf Lammen, 2-Dec-2018.) $)
    eu2 $p |- ( E! x ph <->
    ( E. x ph /\ A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $=
      ( weu wex wmo wa wsb weq wi wal df-eu mo3 anbi2i bitri ) ABEABFZABGZHQAAB
      CIHBCJKCLBLZHABMRSQABCDNOP $.
  $}

  ${
    $d x y $.
    eu1.nf $e |- F/ y ph $.
    $( An alternate way to express uniqueness used by some authors.  Exercise
       2(b) of [Margaris] p. 110.  (Contributed by NM, 20-Aug-1993.)  (Revised
       by Mario Carneiro, 7-Oct-2016.)  (Proof shortened by Wolf Lammen,
       29-Oct-2018.)  Avoid ~ ax-13 .  (Revised by Wolf Lammen, 7-Feb-2023.) $)
    eu1 $p |- ( E! x ph <->
                E. x ( ph /\ A. y ( [ y / x ] ph -> x = y ) ) ) $=
      ( wsb weu weq wb wal wex wi wa nfs1v sb8euv sb6rfv equcom imbi2i anbi12ci
      euf albii albiim bitr4i exbii 3bitr4i ) ABCEZCFUECBGZHCIZBJABFAUEBCGZKZCI
      ZLZBJUECBABCMSABCDNUKUGBUKUEUFKZCIZUFUEKCIZLUGAUNUJUMABCDOUIULCUHUFUEBCPQ
      TRUEUFCUAUBUCUD $.
    $( $j usage 'eu1' avoids 'ax-13'; $)
  $}

  ${
    euor.nf $e |- F/ x ph $.
    $( Introduce a disjunct into a unique existential quantifier.  For a
       version requiring disjoint variables, but fewer axioms, see ~ euorv .
       (Contributed by NM, 21-Oct-2005.) $)
    euor $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      ( wn weu wo nfn biorf eubid biimpa ) AEZBCFABGZCFLBMCACDHABIJK $.
  $}

  ${
    $d x ph $.
    $( Introduce a disjunct into a unique existential quantifier.  Version of
       ~ euor requiring disjoint variables, but fewer axioms.  (Contributed by
       NM, 23-Mar-1995.)  Reduce dependencies on axioms.  (Revised by Wolf
       Lammen, 14-Jan-2023.) $)
    euorv $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      ( wn weu wo biorf eubidv biimpa ) ADZBCEABFZCEJBKCABGHI $.
  $}

  $( Introduce or eliminate a disjunct in a unique existential quantifier.
     (Contributed by NM, 21-Oct-2005.)  (Proof shortened by Andrew Salmon,
     9-Jul-2011.)  (Proof shortened by Wolf Lammen, 27-Dec-2018.) $)
  euor2 $p |- ( -. E. x ph -> ( E! x ( ph \/ ps ) <-> E! x ps ) ) $=
    ( wex wn wo nfe1 nfn wb 19.8a biorf bicomd nsyl5 eubid ) ACDZEABFZBCOCACGHA
    OPBIACJAEBPABKLMN $.

  ${
    $d w x z $.  $d w y z $.  $d w ph $.
    $( Substitution into an at-most-one quantifier.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    sbmo $p |- ( [ y / x ] E* z ph <-> E* z [ y / x ] ph ) $=
      ( vw weq wi wal wex wsb wmo sbex nfv sblim sbalv exbii bitri dfmo 3bitr4i
      sbbii ) ADEFZGZDHZEIZBCJZABCJZUAGZDHZEIZADKZBCJUFDKUEUCBCJZEIUIUCEBCLUKUH
      EUBUGBCDAUABCUABMNOPQUJUDBCADERTUFDERS $.
  $}

  ${
    $d x y $.  $d y ph $.  $d x ps $.
    eu4.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Uniqueness using implicit substitution.  (Contributed by NM,
       26-Jul-1995.) $)
    eu4 $p |- ( E! x ph <-> ( E. x ph /\
             A. x A. y ( ( ph /\ ps ) -> x = y ) ) ) $=
      ( weu wex wmo wa weq wi wal df-eu mo4 anbi2i bitri ) ACFACGZACHZIQABICDJK
      DLCLZIACMRSQABCDENOP $.
  $}

  $( Existential uniqueness implies uniqueness through reverse implication.
     (Contributed by NM, 22-Apr-1995.) $)
  euimmo $p |- ( A. x ( ph -> ps ) -> ( E! x ps -> E* x ph ) ) $=
    ( weu wmo wi wal eumo moim syl5 ) BCDBCEABFCGACEBCHABCIJ $.

  $( Add unique existential quantifiers to an implication.  Note the reversed
     implication in the antecedent.  (Contributed by NM, 19-Oct-2005.)  (Proof
     shortened by Andrew Salmon, 14-Jun-2011.)  (Proof shortened by Wolf
     Lammen, 1-Oct-2023.) $)
  euim $p |- ( ( E. x ph /\ A. x ( ph -> ps ) ) -> ( E! x ps -> E! x ph ) ) $=
    ( wi wal weu wmo wex euimmo exmoeub biimpd sylan9r ) ABDCEBCFACGZACHZACFZAB
    CINMOACJKL $.

  ${
    moanimlem.1 $e |- ( ph -> ( E* x ps <-> E* x ( ph /\ ps ) ) ) $.
    moanimlem.2 $e |- ( E. x ( ph /\ ps ) -> ph ) $.
    $( Factor out the common proof skeleton of ~ moanimv and ~ moanim .
       (Contributed by NM, 3-Dec-2001.)  (Proof shortened by Wolf Lammen,
       24-Dec-2018.)  Factor out common proof lines.  (Revised by Wolf Lammen,
       8-Feb-2023.) $)
    moanimlem $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      ( wa wmo wi biimprcd wex nexmo nsyl5 moan ja impbii ) ABFZCGZABCGZHARQDIA
      RQPCJAQEPCKLBACMNO $.
  $}

  ${
    $d x ph $.
    $( Introduction of a conjunct into an at-most-one quantifier.  Version of
       ~ moanim requiring disjoint variables, but fewer axioms.  (Contributed
       by NM, 23-Mar-1995.)  Reduce axiom usage .  (Revised by Wolf Lammen,
       8-Feb-2023.) $)
    moanimv $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      ( wa ibar mobidv simpl exlimiv moanimlem ) ABCABABDZCABEFJACABGHI $.
  $}

  ${
    moanim.1 $e |- F/ x ph $.
    $( Introduction of a conjunct into "at most one" quantifier.  For a version
       requiring disjoint variables, but fewer axioms, see ~ moanimv .
       (Contributed by NM, 3-Dec-2001.)  (Proof shortened by Wolf Lammen,
       24-Dec-2018.) $)
    moanim $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      ( wa ibar mobid simpl exlimi moanimlem ) ABCABABEZCDABFGKACDABHIJ $.

    $( Introduction of a conjunct into unique existential quantifier.
       (Contributed by NM, 19-Feb-2005.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.)  (Proof shortened by Wolf Lammen, 24-Dec-2018.) $)
    euan $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      ( wa weu wex euex simpl exlimi syl ibar eubid biimprcd jcai biimpa impbii
      ) ABEZCFZABCFZESATSRCGARCHRACDABIJKATSABRCDABLMZNOATSUAPQ $.
  $}

  $( Nested at-most-one quantifiers.  (Contributed by NM, 25-Jan-2006.) $)
  moanmo $p |- E* x ( ph /\ E* x ph ) $=
    ( wmo wa wi id nfmo1 moanim mpbir ancom mobii ) AABCZDZBCLADZBCZOLLELFLABAB
    GHIMNBALJKI $.

  $( Nested at-most-one and unique existential quantifiers.  (Contributed by
     NM, 25-Jan-2006.)  (Proof shortened by Wolf Lammen, 27-Dec-2018.) $)
  moaneu $p |- E* x ( ph /\ E! x ph ) $=
    ( wmo wa weu moanmo eumo anim2i moimi ax-mp ) AABCZDZBCAABEZDZBCABFNLBMKAAB
    GHIJ $.

  ${
    $d x ph $.
    $( Introduction of a conjunct into unique existential quantifier.
       (Contributed by NM, 23-Mar-1995.)  Reduce dependencies on axioms.
       (Revised by Wolf Lammen, 14-Jan-2023.) $)
    euanv $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      ( weu wex euex simpl exlimiv syl ibar eubidv biimprcd jcai biimpa impbii
      wa ) ABPZCDZABCDZPRASRQCEAQCFQACABGHIASRABQCABJKZLMASRTNO $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( "At most one" picks a variable value, eliminating an existential
       quantifier.  (Contributed by NM, 27-Jan-1997.)  (Proof shortened by Wolf
       Lammen, 17-Sep-2019.) $)
    mopick $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
      ( vy wmo wa wex wi weq wal dfmo pm3.45 aleximi ax12ev2 syl6 syl5d exlimiv
      sp sylbi imp ) ACEZABFZCGZABHZUAACDIZHZCJZDGUCUDHZACDKUGUHDUGAUEUCBUFCRUG
      UCUEBFZCGUEBHUFUBUICAUEBLMBCDNOPQST $.
    $( $j usage 'mopick' avoids 'ax-10'; $)
  $}

  ${
    moexexlem.1 $e |- F/ y ph $.
    moexexlem.2 $e |- F/ y E* x ph $.
    moexexlem.3 $e |- F/ x E* y E. x ( ph /\ ps ) $.
    $( Factor out the proof skeleton of ~ moexex and ~ moexexvw .  (Contributed
       by Wolf Lammen, 2-Oct-2023.) $)
    moexexlem $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) )
      $=
      ( wmo wal wa wex wi nfmo1 nfa1 nfim mopick ex com23 alrimd moim spsd syl6
      exlimd wn nfex exsimpl exlimi nexmo nsyl5 a1d pm2.61d1 imp ) ACHZBDHZCIZA
      BJCKZDHZUMACKZUOUQLZUMAUSCACMUOUQCUNCNGOUMAUPBLZDIZUSUMAUTDFEUMUPABUMUPAB
      LABCPQRSVAUNUQCUPBDTUAUBUCURUDUQUOUPDKURUQUPURDADCEUEABCUFUGUPDUHUIUJUKUL
      $.
  $}

  ${
    $d x y $.
    $( Double quantification with "at most one".  (Contributed by NM,
       3-Dec-2001.) $)
    2moexv $p |- ( E* x E. y ph -> A. y E* x ph ) $=
      ( wex wmo nfe1 nfmov 19.8a moimi alrimi ) ACDZBEABECKCBACFGAKBACHIJ $.
    $( $j usage '2moexv' avoids 'ax-13'; $)

    $d y ph $.
    $( "At most one" double quantification.  Version of ~ moexexv with an
       additional disjoint variable condition, which does not require ~ ax-13 .
       (Contributed by NM, 26-Jan-1997.)  (Revised by GG, 22-Aug-2023.)  Factor
       out common proof lines with ~ moexex .  (Revised by Wolf Lammen,
       2-Oct-2023.) $)
    moexexvw $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      ( nfv wmo wa wex nfe1 nfmov moexexlem ) ABCDADEACFDEABGZCHCDLCIJK $.
    $( $j usage 'moexexvw' avoids 'ax-13'; $)
  $}

  ${
    $d x y $.
    $( A condition allowing to swap an existential quantifier and at
       at-most-one quantifier.  Version of ~ 2moswap with a disjoint variable
       condition, which does not require ~ ax-13 .  (Contributed by NM,
       10-Apr-2004.)  (Revised by GG, 22-Aug-2023.)  Factor out common proof
       lines with ~ moexexvw .  (Revised by Wolf Lammen, 2-Oct-2023.) $)
    2moswapv $p |- ( A. x E* y ph -> ( E* x E. y ph -> E* y E. x ph ) ) $=
      ( wmo wal wex nfmov moexexlem expcom 19.8a pm4.71ri exbii mobii imbitrrdi
      wa nfe1 ) ACDBEZACFZBDZRAOZBFZCDZABFZCDSQUBRABCACPZRCBUDGUABCTBPGHIUCUACA
      TBARACJKLMN $.
    $( $j usage '2moswapv' avoids 'ax-13'; $)
  $}

  ${
    $d x y $.
    $( A condition allowing to swap an existential quantifier and a unique
       existential quantifier.  Version of ~ 2euswap with a disjoint variable
       condition, which does not require ~ ax-13 .  (Contributed by NM,
       10-Apr-2004.)  (Revised by GG, 22-Aug-2023.) $)
    2euswapv $p |- ( A. x E* y ph -> ( E! x E. y ph -> E! y E. x ph ) ) $=
      ( wmo wal wex wa weu wi excomim a1i 2moswapv anim12d df-eu 3imtr4g ) ACDB
      EZACFZBFZQBDZGABFZCFZTCDZGQBHTCHPRUASUBRUAIPABCJKABCLMQBNTCNO $.
    $( $j usage '2euswapv' avoids 'ax-13'; $)

    $( Double quantification with existential uniqueness.  Version of ~ 2euex
       with ` x ` and ` y ` distinct, but not requiring ~ ax-13 .  (Contributed
       by NM, 3-Dec-2001.)  (Revised by Wolf Lammen, 2-Oct-2023.) $)
    2euexv $p |- ( E! x E. y ph -> E. y E! x ph ) $=
      ( wex weu wa df-eu excom nfe1 nfmov 19.8a moimi moeu sylib eximd biimtrid
      wmo wi impcom sylbi ) ACDZBEUABDZUABQZFABEZCDZUABGUCUBUEUBABDZCDUCUEABCHU
      CUFUDCUACBACIJUCABQUFUDRAUABACKLABMNOPST $.
    $( $j usage '2euexv' avoids 'ax-13'; $)

    $( Double existential uniqueness implies double unique existential
       quantification.  Version of ~ 2exeu with ` x ` and ` y ` distinct, but
       not requiring ~ ax-13 .  (Contributed by NM, 3-Dec-2001.)  (Revised by
       Wolf Lammen, 2-Oct-2023.) $)
    2exeuv $p |- ( ( E! x E. y ph /\ E! y E. x ph ) -> E! x E! y ph ) $=
      ( wex weu wa wmo eumo euex moimi syl 2euexv anim12ci df-eu sylibr ) ACDZB
      EZABDCEZFACEZBDZSBGZFSBEQUARTQPBGUAPBHSPBACIJKACBLMSBNO $.
    $( $j usage '2exeuv' avoids 'ax-13'; $)
  $}

  $( Existential uniqueness "picks" a variable value for which another wff is
     true.  If there is only one thing ` x ` such that ` ph ` is true, and
     there is also an ` x ` (actually the same one) such that ` ph ` and ` ps `
     are both true, then ` ph ` implies ` ps ` regardless of ` x ` .  This
     theorem can be useful for eliminating existential quantifiers in a
     hypothesis.  Compare Theorem *14.26 in [WhiteheadRussell] p. 192.
     (Contributed by NM, 10-Jul-1994.) $)
  eupick $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
    ( weu wmo wa wex wi eumo mopick sylan ) ACDACEABFCGABHACIABCJK $.

  $( Version of ~ eupick with closed formulas.  (Contributed by NM,
     6-Sep-2008.) $)
  eupicka $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> A. x ( ph -> ps ) ) $=
    ( weu wa wex wi nfeu1 nfe1 nfan eupick alrimi ) ACDZABEZCFZEABGCMOCACHNCIJA
    BCKL $.

  $( Existential uniqueness "pick" showing wff equivalence.  (Contributed by
     NM, 25-Nov-1994.)  (Proof shortened by Wolf Lammen, 27-Dec-2018.) $)
  eupickb $p |- ( ( E! x ph /\ E! x ps /\ E. x ( ph /\ ps ) ) ->
               ( ph <-> ps ) ) $=
    ( weu wa wex w3a wi eupick 3adant2 exancom sylan2b 3adant1 impbid ) ACDZBCD
    ZABECFZGABOQABHPABCIJPQBAHZOQPBAECFRABCKBACILMN $.

  $( Theorem *14.26 in [WhiteheadRussell] p. 192.  (Contributed by Andrew
     Salmon, 11-Jul-2011.)  (Proof shortened by Wolf Lammen, 27-Dec-2018.) $)
  eupickbi $p |- ( E! x ph -> ( E. x ( ph /\ ps ) <-> A. x ( ph -> ps ) ) ) $=
    ( weu wa wex wi wal eupicka ex euex exintr syl5com impbid ) ACDZABECFZABGCH
    ZOPQABCIJOACFQPACKABCLMN $.

  $( "At most one" can show the existence of a common value.  In this case we
     can infer existence of conjunction from a conjunction of existence, and it
     is one way to achieve the converse of ~ 19.40 .  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  mopick2 $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) /\ E. x ( ph /\ ch ) ) ->
                E. x ( ph /\ ps /\ ch ) ) $=
    ( wmo wa wex w3a nfmo1 nfe1 nfan mopick ancld anim1d df-3an imbitrrdi eximd
    3impia ) ADEZABFZDGZACFZDGABCHZDGSUAFZUBUCDSUADADITDJKUDUBTCFUCUDATCUDABABD
    LMNABCOPQR $.

  ${
    moexex.1 $e |- F/ y ph $.
    $( "At most one" double quantification.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  Use the version ~ moexexvw
       when possible.  (Contributed by NM, 3-Dec-2001.)  (Proof shortened by
       Wolf Lammen, 28-Dec-2018.)  Factor out common proof lines with
       ~ moexexvw .  (Revised by Wolf Lammen, 2-Oct-2023.)
       (New usage is discouraged.) $)
    moexex $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      ( nfmo wa wex nfe1 moexexlem ) ABCDEADCEFABGZCHCDKCIFJ $.
  $}

  ${
    $d y ph $.
    $( "At most one" double quantification.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  Use the weaker ~ moexexvw
       when possible.  (Contributed by NM, 26-Jan-1997.)
       (New usage is discouraged.) $)
    moexexv $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      ( nfv moexex ) ABCDADEF $.
  $}

  $( Double quantification with "at most one".  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  Use the weaker ~ 2moexv when
     possible.  (Contributed by NM, 3-Dec-2001.)
     (New usage is discouraged.) $)
  2moex $p |- ( E* x E. y ph -> A. y E* x ph ) $=
    ( wex wmo nfe1 nfmo 19.8a moimi alrimi ) ACDZBEABECKCBACFGAKBACHIJ $.

  $( Double quantification with existential uniqueness.  Usage of this theorem
     is discouraged because it depends on ~ ax-13 .  Use the weaker ~ 2euexv
     when possible.  (Contributed by NM, 3-Dec-2001.)  (Proof shortened by
     Andrew Salmon, 9-Jul-2011.)  (New usage is discouraged.) $)
  2euex $p |- ( E! x E. y ph -> E. y E! x ph ) $=
    ( wex weu wa df-eu excom nfe1 nfmo wi 19.8a moimi moeu sylib eximd biimtrid
    wmo impcom sylbi ) ACDZBEUABDZUABRZFABEZCDZUABGUCUBUEUBABDZCDUCUEABCHUCUFUD
    CUACBACIJUCABRUFUDKAUABACLMABNOPQST $.

  $( Nested unique existential quantifier and at-most-one quantifier.
     (Contributed by NM, 3-Dec-2001.) $)
  2eumo $p |- ( E! x E* y ph -> E* x E! y ph ) $=
    ( weu wmo wi euimmo eumo mpg ) ACDZACEZFKBDJBEFBJKBGACHI $.

  $( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
  2eu2ex $p |- ( E! x E! y ph -> E. x E. y ph ) $=
    ( weu wex euex eximi syl ) ACDZBDIBEACEZBEIBFIJBACFGH $.

  $( A condition allowing to swap an existential quantifier and at at-most-one
     quantifier.  Usage of this theorem is discouraged because it depends on
     ~ ax-13 .  Use the weaker ~ 2moswapv when possible.  (Contributed by NM,
     10-Apr-2004.)  (New usage is discouraged.) $)
  2moswap $p |- ( A. x E* y ph -> ( E* x E. y ph -> E* y E. x ph ) ) $=
    ( wmo wal wex wa nfe1 moexex expcom 19.8a pm4.71ri exbii mobii imbitrrdi )
    ACDBEZACFZBDZQAGZBFZCDZABFZCDRPUAQABCACHIJUBTCASBAQACKLMNO $.

  $( A condition allowing to swap an existential quantifier and a unique
     existential quantifier.  Usage of this theorem is discouraged because it
     depends on ~ ax-13 .  Use the weaker ~ 2euswapv when possible.
     (Contributed by NM, 10-Apr-2004.)  (New usage is discouraged.) $)
  2euswap $p |- ( A. x E* y ph -> ( E! x E. y ph -> E! y E. x ph ) ) $=
    ( wmo wal wex wa weu wi excomim a1i 2moswap anim12d df-eu 3imtr4g ) ACDBEZA
    CFZBFZQBDZGABFZCFZTCDZGQBHTCHPRUASUBRUAIPABCJKABCLMQBNTCNO $.

  $( Double existential uniqueness implies double unique existential
     quantification.  The converse does not hold.  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  Use the weaker ~ 2exeuv when
     possible.  (Contributed by NM, 3-Dec-2001.)  (Proof shortened by Mario
     Carneiro, 22-Dec-2016.)  (New usage is discouraged.) $)
  2exeu $p |- ( ( E! x E. y ph /\ E! y E. x ph ) -> E! x E! y ph ) $=
    ( wex weu wa wmo eumo euex moimi syl 2euex anim12ci df-eu sylibr ) ACDZBEZA
    BDCEZFACEZBDZSBGZFSBEQUARTQPBGUAPBHSPBACIJKACBLMSBNO $.

  ${
    $d x y z w $.  $d z w ph $.
    $( Two ways of expressing "there exists at most one ordered pair
       ` <. x , y >. ` such that ` ph ( x , y ) ` holds.  Note that this is not
       equivalent to ` E* x E* y ph ` .  See also ~ 2mo .  This is the analogue
       of ~ 2eu4 for existential uniqueness.  (Contributed by Wolf Lammen,
       26-Oct-2019.)  Reduce dependencies on axioms.  (Revised by Wolf Lammen,
       3-Jan-2023.) $)
    2mo2 $p |- ( ( E* x E. y ph /\ E* y E. x ph ) <->
                          E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) $=
      ( wex weq wi wal wa wmo exdistrv jcab 2albii 19.26-2 19.23v albii anbi12i
      alcom dfmo bitri 3bitri 2exbii 3bitr4ri ) ACFZBDGZHZBIZABFZCEGZHZCIZJZEFD
      FUHDFZULEFZJAUFUJJHZCIBIZEFDFUEBKZUICKZJUHULDELUQUMDEUQAUFHZAUJHZJZCIBIUT
      CIZBIZVACIBIZJUMUPVBBCAUFUJMNUTVABCOVDUHVEULVCUGBAUFCPQVEVABIZCIULVABCSVF
      UKCAUJBPQUARUBUCURUNUSUOUEBDTUICETRUD $.
  $}

  ${
    $d x y z w $.  $d z w ph $.
    $( Two ways of expressing "there exists at most one ordered pair
       ` <. x , y >. ` such that ` ph ( x , y ) ` holds.  See also ~ 2mo2 .
       (Contributed by NM, 2-Feb-2005.)  (Revised by Mario Carneiro,
       17-Oct-2016.)  (Proof shortened by Wolf Lammen, 2-Nov-2019.) $)
    2mo $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <->
              A. x A. y A. z A. w ( ( ph /\ [ z / x ] [ w / y ] ph ) ->
                                                      ( x = z /\ y = w ) ) ) $=
      ( weq wa wi wal wex wsb wmo nfmo1 nfe1 nfmov nfan 19.8a spsbe sbimi nfv
      2mo2 biimpi 19.21bbi syl2ani sbcom2 sylbi anim12ii alrimi alrimivv sylbir
      mo3 nfs1v nfsbv pm3.21 imim1d alimd aleximi 2nexaln 2sb8ef xchnxbi pm2.21
      com12 wn 2alimi 2eximi 19.23bi pm2.61d1 impbii alrot4 bitri ) ABDFZCEFZGZ
      HZCIZBIZEJZDJZAACEKZBDKZGZVMHZCIZBIZEIZDIZWBEIDICIBIVRWFVRACJZBLZABJZCLZG
      ZWFABCDEUAWKWDDEWKWCBWHWJBWGBMWIBCABNOPWKWBCWHWJCWGCBACNOWICMPWHWAVKWJVLA
      WHWGWGBDKZVKVTACQVSWGBDACERSWHWGWLGVKHZBDWHWMDIBIWGBDWGDTUKUBUCUDAWJWIWIC
      EKZVLVTABQVTABDKZCEKWNACEBDUEWOWICEABDRSUFWJWIWNGVLHZCEWJWPEICIWICEWIETUK
      UBUCUDUGUHUHUIUJWFVTEJZDJZVRWEWQVQDWDVTVPEVTWDVPVTWCVOBVSBDULVTWBVNCVSBDC
      ACEULUMVTAWAVMVTAUNUOUPUPVBUQUQWRVCAVCZCIBIZVRWGBJWTWRABCURABCDEAETADTUSU
      TWTVREWTEJVRDWTVPDEWSVNBCAVMVAVDVEVFVFUFVGVHWBDEBCVIVJ $.
  $}

  ${
    $d z w ph $.  $d x y ps $.  $d x y z w $.
    2mos.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Double "there exists at most one", using implicit substitution.
       (Contributed by NM, 10-Feb-2005.)  (Proof shortened by Wolf Lammen,
       21-May-2025.) $)
    2mos $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <->
             A. x A. y A. z A. w ( ( ph /\ ps ) -> ( x = z /\ y = w ) ) ) $=
      ( weq wa wi wal wex wsb 2mo 2sbievw anbi2i imbi1i 2albii bitri ) ACEHDFHI
      ZJDKCKFLELAADFMCEMZIZTJZFKEKZDKCKABIZTJZFKEKZDKCKACDEFNUDUGCDUCUFEFUBUETU
      ABAABCDFEGOPQRRS $.
  $}

  $( Double existential uniqueness.  This theorem shows a condition under which
     a "naive" definition matches the correct one.  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  Use the weaker ~ 2eu1v when
     possible.  (Contributed by NM, 3-Dec-2001.)  (Proof shortened by Wolf
     Lammen, 23-Apr-2023.)  (New usage is discouraged.) $)
  2eu1 $p |- ( A. x E* y ph ->
        ( E! x E! y ph <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
    ( wmo wal weu wex wa wi 2eu2ex moeu albii euim sylan2b pm2.43b 2euswap syld
    ex syl jcad 2exeu impbid1 ) ACDZBEZACFZBFZACGZBFZABGCFZHUDUFUHUIUDUFUHUFUGB
    GZUDUFUHIZIABCJUJUDUKUDUJUGUEIZBEUKUCULBACKLUGUEBMNRSOZUDUFUHUIUMABCPQTABCU
    AUB $.

  ${
    $d x y $.
    $( Double existential uniqueness.  This theorem shows a condition under
       which a "naive" definition matches the correct one.  Version of ~ 2eu1
       with ` x ` and ` y ` distinct, but not requiring ~ ax-13 .  (Contributed
       by NM, 3-Dec-2001.)  (Revised by Wolf Lammen, 2-Oct-2023.) $)
    2eu1v $p |- ( A. x E* y ph ->
          ( E! x E! y ph <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
      ( wmo wal weu wex wa wi 2eu2ex moeu albii sylan2b ex syl pm2.43b 2euswapv
      euim syld jcad 2exeuv impbid1 ) ACDZBEZACFZBFZACGZBFZABGCFZHUDUFUHUIUDUFU
      HUFUGBGZUDUFUHIZIABCJUJUDUKUDUJUGUEIZBEUKUCULBACKLUGUEBRMNOPZUDUFUHUIUMAB
      CQSTABCUAUB $.
    $( $j usage '2eu1v' avoids 'ax-13'; $)
  $}

  $( Double existential uniqueness.  Usage of this theorem is discouraged
     because it depends on ~ ax-13 .  (Contributed by NM, 3-Dec-2001.)
     (New usage is discouraged.) $)
  2eu2 $p |- ( E! y E. x ph -> ( E! x E! y ph <-> E! x E. y ph ) ) $=
    ( wex weu wmo wi eumo 2moex wa 2eu1 simpl biimtrdi 3syl 2exeu expcom impbid
    wal ) ABDZCEZACEBEZACDBEZTSCFACFBRZUAUBGSCHACBIUCUAUBTJUBABCKUBTLMNUBTUAABC
    OPQ $.

  $( Double existential uniqueness.  Usage of this theorem is discouraged
     because it depends on ~ ax-13 .  (Contributed by NM, 3-Dec-2001.)  (Proof
     shortened by Wolf Lammen, 23-Apr-2023.)  (New usage is discouraged.) $)
  2eu3 $p |- ( A. x A. y ( E* x ph \/ E* y ph ) ->
 ( ( E! x E! y ph /\ E! y E! x ph ) <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
    ( wmo wo wal weu wa wb nfmo1 19.31 albii nfal 19.32 bitri 2eu1 biimpd ancom
    wex 2exeu imbitrdi jaoa ancomsd ancoms jca impbid1 sylbi ) ABDZACDZECFZBFZU
    HCFZUIBFZEZACGBGZABGCGZHZACSBGZABSCGZHZIUKULUIEZBFUNUJVABUHUICACJKLULUIBUHB
    CABJMNOUNUQUTUNUPUOUTULUPUTUMUOULUPUSURHZUTULUPVBACBPQUSURRUAUMUOUTABCPQUBU
    CUTUOUPABCTUSURUPACBTUDUEUFUG $.

  ${
    $d x y z w $.  $d z w ph $.
    $( This theorem provides us with a definition of double existential
       uniqueness ("exactly one ` x ` and exactly one ` y ` ").  Naively one
       might think (incorrectly) that it could be defined by ` E! x E! y ph ` .
       See ~ 2eu1 for a condition under which the naive definition holds and
       ~ 2exeu for a one-way implication.  See ~ 2eu5 and ~ 2eu8 for alternate
       definitions.  (Contributed by NM, 3-Dec-2001.)  (Proof shortened by Wolf
       Lammen, 14-Sep-2019.) $)
    2eu4 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      ( wex weu wa wmo weq wi wal df-eu excom bianbi anbi12i anandi 2mo2 anbi2i
      3bitr2i ) ACFZBGZABFZCGZHUABFZUABIZHZUEUCCIZHZHUEUFUHHZHUEABDJCEJHKCLBLEF
      DFZHUBUGUDUIUABMUDUCCFUHUEUCCMACBNOPUEUFUHQUJUKUEABCDERST $.
    $( An alternate definition of double existential uniqueness (see ~ 2eu4 ).
       A mistake sometimes made in the literature is to use ` E! x E! y ` to
       mean "exactly one ` x ` and exactly one ` y ` ".  (For example, see
       Proposition 7.53 of [TakeutiZaring] p. 53.)  It turns out that this is
       actually a weaker assertion, as can be seen by expanding out the formal
       definitions.  This theorem shows that the erroneous definition can be
       repaired by conjoining ` A. x E* y ph ` as an additional condition.  The
       correct definition apparently has never been published.  ( ` E* ` means
       "there exists at most one".)  (Contributed by NM, 26-Oct-2003.)  Avoid
       ~ ax-13 .  (Revised by Wolf Lammen, 2-Oct-2023.) $)
    2eu5 $p |- ( ( E! x E! y ph /\ A. x E* y ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      ( weu wmo wal wa wex weq wi 2eu1v pm5.32ri eumo 2moexv syl adantl pm4.71i
      2eu4 3bitr2i ) ACFBFZACGBHZIACJZBFZABJZCFZIZUCIUHUDBJABDKCEKILCHBHEJDJIUC
      UBUHABCMNUHUCUGUCUEUGUFCGUCUFCOACBPQRSABCDETUA $.
  $}

  ${
    $d x y z w $.  $d z w ph $.
    $( Two equivalent expressions for double existential uniqueness.
       (Contributed by NM, 2-Feb-2005.)  (Revised by Mario Carneiro,
       17-Oct-2016.)  (Proof shortened by Wolf Lammen, 2-Oct-2019.) $)
    2eu6 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
               E. z E. w A. x A. y ( ph <-> ( x = z /\ y = w ) ) ) $=
      ( wex weu wa weq wi wal wb 2eu4 imim2i sps exlimd syli wsb 2alimi 2eximi
      nfia1 nfa1 nfv simpl ax12v com12 spsd nfs1v sbequ1 imim2d al2imi sb6 2sb6
      simpr bitr3i imbitrdi sylcom ancld 2albiim imbitrrdi exlimi 2eximdv 2exsb
      imp biimpr sylibr biimp jca impbii bitri ) ACFZBGABFCGHVKBFZABDIZCEIZHZJZ
      CKZBKZEFDFZHZAVOLZCKZBKZEFDFZABCDEMVTWDVLVSWDVLVRWCDEVKVRWCJBVQWBBUAVKVRV
      RVOAJZCKBKZHWCVKVRWFVKVRVMVKJZBKZWFVKVQWHBVQVKWHVKVQVMWHVQAVMCVPCUBZVMCUC
      VPAVMJCVOVMAVMVNUDNOPVKBDUEQUFUGVRWHVMACERZJZBKZWFVQWGWKBVQVKWJVMVQAWJCWI
      ACEUHVPAWJJCAVPVNWJVOVNAVMVNUNNACEUIQOPUJUKWLWJBDRWFWJBDULABCDEUMUOUPUQUR
      AVOBCUSUTVAVBVDWDVLVSWDWFEFDFVLWCWFDEWAWEBCAVOVESTABCDEVCVFWCVRDEWAVPBCAV
      OVGSTVHVIVJ $.
  $}

  $( Two equivalent expressions for double existential uniqueness.  Usage of
     this theorem is discouraged because it depends on ~ ax-13 .  (Contributed
     by NM, 19-Feb-2005.)  (New usage is discouraged.) $)
  2eu7 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
             E! x E! y ( E. x ph /\ E. y ph ) ) $=
    ( wex weu wa nfe1 nfeu euan ancom eubii 3bitri 3bitr4ri ) ABDZCEZACDZFZBEOP
    BEZFNPFZCEZBEROFOPBNBCABGHITQBTPNFZCEPOFQSUACNPJKPNCACGIPOJLKROJM $.

  $( Two equivalent expressions for double existential uniqueness.  Curiously,
     we can put ` E! ` on either of the internal conjuncts but not both.  We
     can also commute ` E! x E! y ` using ~ 2eu7 .  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  (Contributed by NM,
     20-Feb-2005.)  (New usage is discouraged.) $)
  2eu8 $p |- ( E! x E! y ( E. x ph /\ E. y ph ) <->
                E! x E! y ( E! x ph /\ E. y ph ) ) $=
    ( wex wa 2eu2 pm5.32i nfeu1 nfeu euan ancom eubii nfe1 3bitri 3bitr4ri 2eu7
    weu 3bitr3ri ) ACDZBQZABQZCQZEZTABDZCQZEUASEZCQZBQZUDSECQBQTUBUEACBFGUBSEZB
    QUBTEUHUCUBSBUABCABHIJUGUIBUGSUAEZCQSUBEUIUFUJCUASKLSUACACMJSUBKNLTUBKOABCP
    R $.

  ${
    $d x y $.
    $( Two ways to express "exactly one thing exists".  To paraphrase the
       statement and explain the label: there Exists a Unique thing if and only
       if for All ` x ` , ` x ` Equals some given (and disjoint) ` y ` .  Both
       sides are false in set theory, see Theorems ~ neutru and ~ dtru .
       (Contributed by NM, 5-Apr-2004.)  State the theorem using truth constant
       ` T. ` .  (Revised by BJ, 7-Oct-2022.)  Reduce axiom dependencies.
       (Revised by Wolf Lammen, 2-Mar-2023.) $)
    euae $p |- ( E! x T. <-> A. x x = y ) $=
      ( wtru weq wi wal wex wa extru biantrur hbaev 19.8w wn hbnaev alnex sylib
      weu con4i impbii trut albii exbii bitri eu3v 3bitr4ri ) CABDZEZAFZBGZCAGZ
      UIHUFAFZCAQUJUIAIJUKUKBGZUIUKULUKBABBKLUKULUKMZUMBFULMABBNUKBOPRSUKUHBUFU
      GAUFTUAUBUCCABUDUE $.

    $( Two ways to express "exactly one thing exists".  The left-hand side
       requires only one variable to express this.  Both sides are false in set
       theory, see Theorem ~ dtru .  (Contributed by NM, 5-Apr-2004.)  (Proof
       shortened by BJ, 7-Oct-2022.) $)
    exists1 $p |- ( E! x x = x <-> A. x x = y ) $=
      ( weq weu wtru wal equid bitru eubii euae bitri ) AACZADEADABCAFLEALAGHIA
      BJK $.

    $( A condition implying that at least two things exist.  (Contributed by
       NM, 10-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.)
       Reduce axiom usage.  (Revised by Wolf Lammen, 4-Mar-2023.) $)
    exists2 $p |- ( ( E. x ph /\ E. x -. ph ) -> -. E! x x = x ) $=
      ( vy wex weq weu wal axc16nf nfrd com12 exists1 alex bicomi 3imtr4g con2d
      wn imp ) ABDZAPBDZBBEBFZPRTSRBCEBGZABGZTSPZUARUBUAABABCBHIJBCKUBUCABLMNOQ
      $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Other axiomatizations related to classical predicate calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Aristotelian logic: Assertic syllogisms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Model the Aristotelian assertic syllogisms using modern notation.  This
  section shows that the Aristotelian assertic syllogisms can be proven with
  our axioms of logic, and also provides generally useful theorems.

  In antiquity Aristotelian logic and Stoic logic (see ~ mptnan ) were the
  leading logical systems.  Aristotelian logic became the leading system in
  medieval Europe.  This section models this system (including later
  refinements).  Aristotle defined syllogisms very generally ("a discourse in
  which certain (specific) things having been supposed, something different
  from the things supposed results of necessity because these things are so")
  Aristotle, _Prior Analytics_ 24b18-20.  However, in _Prior Analytics_ he
  limits himself to categorical syllogisms that consist of three categorical
  propositions with specific structures.  The syllogisms are the valid subset
  of the possible combinations of these structures.  The medieval schools used
  vowels to identify the types of terms (a=all, e=none, i=some, and o=some are
  not), and named the different syllogisms with Latin words that had the vowels
  in the intended order.

  "There is a surprising amount of scholarly debate about how best to formalize
  Aristotle's syllogisms..." according to _Aristotle's Modal Proofs: Prior
  Analytics A8-22 in Predicate Logic_, Adriane Rini, Springer, 2011,
  ISBN 978-94-007-0049-9, page 28.  For example, Lukasiewicz believes it is
  important to note that "Aristotle does not introduce singular terms or
  premisses into his system".  Lukasiewicz also believes that Aristotelian
  syllogisms are predicates (having a true/false value), not inference rules:
  "The characteristic sign of an inference is the word 'therefore'... no
  syllogism is formulated by Aristotle primarily as an inference, but they are
  all implications."  Jan Lukasiewicz, _Aristotle's Syllogistic from the
  Standpoint of Modern Formal Logic_, Second edition, Oxford, 1957, page 1-2.
  Lukasiewicz devised a specialized prefix notation for representing
  Aristotelian syllogisms instead of using standard predicate logic notation.

  We instead translate each Aristotelian syllogism into an inference rule, and
  each rule is defined using standard predicate logic notation and predicates.
  The predicates are represented by wff variables that may depend on the
  quantified variable ` x ` .  Our translation is essentially identical to the
  one used in Rini page 18, Table 2 "Non-Modal Syllogisms in Lower Predicate
  Calculus (LPC)", which uses standard predicate logic with predicates.  Rini
  states, "the crucial point is that we capture the meaning Aristotle intends,
  and the method by which we represent that meaning is less important".  There
  are two differences: we make the existence criteria explicit, and we use
  ` ph ` , ` ps ` , and ` ch ` in the order they appear (a common Metamath
  convention).  Patzig also uses standard predicate logic notation and
  predicates (though he interprets them as conditional propositions, not as
  inference rules); see Gunther Patzig, _Aristotle's Theory of the Syllogism_
  second edition, 1963, English translation by Jonathan Barnes, 1968, page 38.
  Terms such as "all" and "some" are translated into predicate logic using the
  approach devised by Frege and Russell.  "Frege (and Russell) devised an
  ingenious procedure for regimenting binary quantifiers like "every" and
  "some" in terms of unary quantifiers like "everything" and "something": they
  formalized sentences of the form "Some A is B" and "Every A is B" as
  exists x (Ax and Bx) and all x (Ax implies Bx), respectively."
  "Quantifiers and Quantification", _Stanford Encyclopedia of Philosophy_,
  ~ http://plato.stanford.edu/entries/quantification/ .
  See _Principia Mathematica_ page 22 and *10 for more information
  (especially *10.3 and *10.26).

  Expressions of the form "no ` ph ` is ` ps ` " are consistently translated as
  ` A. x ( ph -> -. ps ) ` .  These can also be expressed as
  ` -. E. x ( ph /\ ps ) ` , per ~ alinexa .
  We translate "all ` ph ` is ` ps ` " to ` A. x ( ph -> ps ) ` ,
  "some ` ph ` is ` ps ` " to ` E. x ( ph /\ ps ) ` , and
  "some ` ph ` is not ` ps ` " to ` E. x ( ph /\ -. ps ) ` .
  It is traditional to use the singular form "is", not the plural form "are",
  in the generic expressions.  By convention the major premise is listed first.

  In traditional Aristotelian syllogisms the predicates have a restricted form
  ("x is a ..."); those predicates could be modeled in modern notation by more
  specific constructs such as ` x = A ` , ` x e. A ` , or ` x C_ A ` .  Here we
  use wff variables instead of specialized restricted forms.  This
  generalization makes the syllogisms more useful in more circumstances.  In
  addition, these expressions make it clearer that the syllogisms of
  Aristotelian logic are the forerunners of predicate calculus.  If we used
  restricted forms like ` x e. A ` instead, we would not only unnecessarily
  limit their use, but we would also need to use set and class axioms, making
  their relationship to predicate calculus less clear.  Using such specific
  constructs would also be anti-historical; Aristotle and others who directly
  followed his work focused on relating wholes to their parts, an approach now
  called part-whole theory.  The work of Cantor and Peano (over 2,000 years
  later) led to a sharper distinction between inclusion ( ` C_ ` ) and
  membership ( ` e. ` ); this distinction was not directly made in Aristotle's
  work.

  There are some widespread misconceptions about the existential assumptions
  made by Aristotle (aka "existential import").  Aristotle was not trying to
  develop something exactly corresponding to modern logic.  Aristotle devised
  "a companion-logic for science.  He relegates fictions like fairy godmothers
  and mermaids and unicorns to the realms of poetry and literature.  In his
  mind, they exist outside the ambit of science.  This is why he leaves no room
  for such nonexistent entities in his logic.  This is a thoughtful choice,
  not an inadvertent omission.  Technically, Aristotelian science is a search
  for definitions, where a definition is "a phrase signifying a thing's
  essence."  (Topics, I.5.102a37, Pickard-Cambridge.)...  Because non-existent
  entities cannot be anything, they do not, in Aristotle's mind, possess an
  essence...  This is why he leaves no place for fictional entities like
  goat-stags (or unicorns)."  Source: Louis F. Groarke, "Aristotle: Logic",
  section 7. (Existential Assumptions),
  _Internet Encyclopedia of Philosophy_ (A Peer-Reviewed Academic Resource),
  ~ http://www.iep.utm.edu/aris-log/ .
  Thus, some syllogisms have "extra" existence hypotheses that do not directly
  appear in Aristotle's original materials (since they were always assumed);
  they are added where they are needed.  This affects ~ barbari , ~ celaront ,
  ~ cesaro , ~ camestros , ~ felapton , ~ darapti , ~ calemos , ~ fesapo , and
  ~ bamalip .

  These are only the _assertic_ syllogisms.  Aristotle also defined modal
  syllogisms that deal with modal qualifiers such as "necessarily" and
  "possibly".  Historically, Aristotelian modal syllogisms were not as widely
  used.  For more about modal syllogisms in a modern context, see Rini as well
  as _Aristotle's Modal Syllogistic_ by Marko Malink, Harvard University Press,
  November 2013.  We do not treat them further here.

  Aristotelian logic is essentially the forerunner of predicate calculus (as
  well as set theory since it discusses membership in groups), while Stoic
  logic is essentially the forerunner of propositional calculus.

  The following twenty-four syllogisms (from ~ barbara to ~ bamalip ) are all
  proven from { ~ ax-mp , ~ ax-1 , ~ ax-2 , ~ ax-3 , ~ ax-gen , ~ ax-4 },
  which corresponds in the usual translation to modal logic (a universal (resp.
  existential) quantifier maps to necessity (resp. possibility)) to the weakest
  normal modal logic (K).  Some proofs could be shortened by using additionally
  ~ spi (inference form of ~ sp , which corresponds to the axiom (T) of modal
  logic), as demonstrated by ~ dariiALT , ~ barbariALT , ~ festinoALT ,
  ~ barocoALT , ~ daraptiALT .

$)

  $( Figure 1.  Aristotelian syllogisms are grouped by "figures", which does
     not matter for our purposes but is a reasonable way to order them. $)

  ${
    $( Major premise for the Aristotelian syllogism "Barbara", e.g., "All men
       are mortal".  By convention, the major premise is first. $)
    barbara.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Barbara, e.g., "Socrates is a man". $)
    barbara.min $e |- A. x ( ch -> ph ) $.
    $( "Barbara", one of the fundamental syllogisms of Aristotelian logic.  All
       ` ph ` is ` ps ` , and all ` ch ` is ` ph ` , therefore all ` ch ` is
       ` ps ` .  In Aristotelian notation, AAA-1:  MaP and SaM therefore SaP.
       For example, given "All men are mortal" and "Socrates is a man", we can
       prove "Socrates is mortal".  If H is the set of men, M is the set of
       mortal beings, and S is Socrates, these word phrases can be represented
       as ` A. x ( x e. H -> x e. M ) ` (all men are mortal) and
       ` A. x ( x = S -> x e. H ) ` (Socrates is a man) therefore
       ` A. x ( x = S -> x e. M ) ` (Socrates is mortal).  Russell and
       Whitehead note that "the syllogism in Barbara [[ ~ barbara ] is derived
       from [[ ~ syl ]" (quote after Theorem *2.06 of [WhiteheadRussell]
       p. 101).  Most of the proof is in ~ alsyl .  There are a legion of
       sources for Barbara, including ~ http://www.friesian.com/aristotl.htm ,
       ~ http://plato.stanford.edu/entries/aristotle-logic/ , and
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.) $)
    barbara $p |- A. x ( ch -> ps ) $=
      ( wi wal alsyl mp2an ) CAGDHABGDHCBGDHFECABDIJ $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Celarent", e.g., "No
       reptiles have fur". $)
    celarent.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Celarent, e.g., "All snakes are reptiles". $)
    celarent.min $e |- A. x ( ch -> ph ) $.
    $( "Celarent", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and all ` ch ` is ` ph ` , therefore no ` ch ` is ` ps ` .
       Instance of ~ barbara .  In Aristotelian notation, EAE-1:  MeP and SaM
       therefore SeP. For example, given the "No reptiles have fur" and "All
       snakes are reptiles", therefore "No snakes have fur".  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.) $)
    celarent $p |- A. x ( ch -> -. ps ) $=
      ( wn barbara ) ABGCDEFH $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Darii", e.g., "All rabbits
       have fur". $)
    darii.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Darii, e.g., "Some pets are rabbits". $)
    darii.min $e |- E. x ( ch /\ ph ) $.
    $( "Darii", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ch ` is ` ph ` , therefore some ` ch ` is ` ps ` .
       In Aristotelian notation, AII-1:  MaP and SiM therefore SiP. For
       example, given "All rabbits have fur" and "Some pets are rabbits",
       therefore "Some pets have fur".  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  See ~ dariiALT for a
       shorter proof requiring more axioms.  (Contributed by David A. Wheeler,
       24-Aug-2016.)  Reduce dependencies on axioms.  (Revised by BJ,
       16-Sep-2022.) $)
    darii $p |- E. x ( ch /\ ps ) $=
      ( wa wi wal wex id anim2d alimi ax-mp exim mp2 ) CAGZCBGZHZDIZQDJRDJABHZD
      ITEUASDUAABCUAKLMNFQRDOP $.

    $( Alternate proof of ~ darii , shorter but using more axioms.  This shows
       how the use of ~ spi may shorten some proofs of the Aristotelian
       syllogisms, even though this adds axiom dependencies.  Note that ~ spi
       is the inference associated with ~ sp , which corresponds to the axiom
       (T) of modal logic.  (Contributed by David A. Wheeler, 27-Aug-2016.)
       Added precisions on axiom usage.  (Revised by BJ, 27-Sep-2022.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dariiALT $p |- E. x ( ch /\ ps ) $=
      ( wa wi spi anim2i eximii ) CAGCBGDFABCABHDEIJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Ferio" ("Ferioque"), e.g.,
       "No homework is fun". $)
    ferio.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Ferio, e.g., "Some reading is homework". $)
    ferio.min $e |- E. x ( ch /\ ph ) $.
    $( "Ferio" ("Ferioque"), one of the syllogisms of Aristotelian logic.  No
       ` ph ` is ` ps ` , and some ` ch ` is ` ph ` , therefore some ` ch ` is
       not ` ps ` .  Instance of ~ darii .  In Aristotelian notation, EIO-1:
       MeP and SiM therefore SoP. For example, given "No homework is fun" and
       "Some reading is homework", therefore "Some reading is not fun".  This
       is essentially a logical axiom in Aristotelian logic.  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.) $)
    ferio $p |- E. x ( ch /\ -. ps ) $=
      ( wn darii ) ABGCDEFH $.
  $}

  ${
    barbarilem.min $e |- E. x ph $.
    barbarilem.maj $e |- A. x ( ph -> ps ) $.
    $( Lemma for ~ barbari and the other Aristotelian syllogisms with
       existential assumption.  (Contributed by BJ, 16-Sep-2022.) $)
    barbarilem $p |- E. x ( ph /\ ps ) $=
      ( wi wal wex wa exintr mp2 ) ABFCGACHABICHEDABCJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Barbari", e.g., "All men
       are mortal". $)
    barbari.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Barbari, e.g., "All Greeks are men". $)
    barbari.min $e |- A. x ( ch -> ph ) $.
    $( Existence premise for Barbari, e.g., "Greeks exist". $)
    barbari.e $e |- E. x ch $.
    $( "Barbari", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ch ` is ` ph ` , and some ` ch ` exist, therefore some
       ` ch ` is ` ps ` .  In Aristotelian notation, AAI-1:  MaP and SaM
       therefore SiP. For example, given "All men are mortal", "All Greeks are
       men", and "Greeks exist", therefore "Some Greeks are mortal".  Note the
       existence hypothesis (to prove the "some" in the conclusion).  Example
       from ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David
       A. Wheeler, 27-Aug-2016.)  Reduce dependencies on axioms.  (Revised by
       BJ, 16-Sep-2022.) $)
    barbari $p |- E. x ( ch /\ ps ) $=
      ( barbara barbarilem ) CBDGABCDEFHI $.

    $( Alternate proof of ~ barbari , shorter but using more axioms.  See
       comment of ~ dariiALT .  (Contributed by David A. Wheeler, 27-Aug-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    barbariALT $p |- E. x ( ch /\ ps ) $=
      ( wa wi barbara spi ancli eximii ) CCBHDGCBCBIDABCDEFJKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Celaront", e.g., "No
       reptiles have fur". $)
    celaront.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Celaront, e.g., "All Snakes are reptiles". $)
    celaront.min $e |- A. x ( ch -> ph ) $.
    $( Existence premise for Celaront, e.g., "Snakes exist". $)
    celaront.e $e |- E. x ch $.
    $( "Celaront", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ch ` is ` ph ` , and some ` ch ` exist, therefore some
       ` ch ` is not ` ps ` .  Instance of ~ barbari .  In Aristotelian
       notation, EAO-1:  MeP and SaM therefore SoP. For example, given "No
       reptiles have fur", "All snakes are reptiles", and "Snakes exist", prove
       "Some snakes have no fur".  Note the existence hypothesis.  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 27-Aug-2016.) $)
    celaront $p |- E. x ( ch /\ -. ps ) $=
      ( wn barbari ) ABHCDEFGI $.
  $}

  $( Figure 2 $)

  ${
    $( Major premise for the Aristotelian syllogism "Cesare" $)
    cesare.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Cesare $)
    cesare.min $e |- A. x ( ch -> ps ) $.
    $( "Cesare", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and all ` ch ` is ` ps ` , therefore no ` ch ` is ` ph ` .  In
       Aristotelian notation, EAE-2:  PeM and SaM therefore SeP. Related to
       ~ celarent .  (Contributed by David A. Wheeler, 27-Aug-2016.)  Reduce
       dependencies on axioms.  (Revised by BJ, 16-Sep-2022.) $)
    cesare $p |- A. x ( ch -> -. ph ) $=
      ( wn wi wal con2 alimi ax-mp celarent ) BACDABGHZDIBAGHZDIENODABJKLFM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Camestres" $)
    camestres.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Camestres $)
    camestres.min $e |- A. x ( ch -> -. ps ) $.
    $( "Camestres", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and no ` ch ` is ` ps ` , therefore no ` ch ` is ` ph ` .  In
       Aristotelian notation, AEE-2:  PaM and SeM therefore SeP. (Contributed
       by David A. Wheeler, 28-Aug-2016.)  Reduce dependencies on axioms.
       (Revised by BJ, 16-Sep-2022.) $)
    camestres $p |- A. x ( ch -> -. ph ) $=
      ( wn wi wal con3 alimi ax-mp celarent ) BGZACDABHZDINAGHZDIEOPDABJKLFM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Festino" $)
    festino.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Festino $)
    festino.min $e |- E. x ( ch /\ ps ) $.
    $( "Festino", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and some ` ch ` is ` ps ` , therefore some ` ch ` is not
       ` ph ` .  In Aristotelian notation, EIO-2:  PeM and SiM therefore SoP.
       (Contributed by David A. Wheeler, 25-Nov-2016.)  Reduce dependencies on
       axioms.  (Revised by BJ, 16-Sep-2022.) $)
    festino $p |- E. x ( ch /\ -. ph ) $=
      ( wa wn wi wal wex con2 anim2d alimi ax-mp exim mp2 ) CBGZCAHZGZIZDJZRDKT
      DKABHIZDJUBEUCUADUCBSCABLMNOFRTDPQ $.

    $( Alternate proof of ~ festino , shorter but using more axioms.  See
       comment of ~ dariiALT .  (Contributed by David A. Wheeler, 27-Aug-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    festinoALT $p |- E. x ( ch /\ -. ph ) $=
      ( wa wn wi spi con2i anim2i eximii ) CBGCAHZGDFBNCABABHIDEJKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Baroco" $)
    baroco.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Baroco $)
    baroco.min $e |- E. x ( ch /\ -. ps ) $.
    $( "Baroco", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ch ` is not ` ps ` , therefore some ` ch ` is not
       ` ph ` .  In Aristotelian notation, AOO-2:  PaM and SoM therefore SoP.
       For example, "All informative things are useful", "Some websites are not
       useful", therefore "Some websites are not informative".  (Contributed by
       David A. Wheeler, 28-Aug-2016.)  Reduce dependencies on axioms.
       (Revised by BJ, 16-Sep-2022.) $)
    baroco $p |- E. x ( ch /\ -. ph ) $=
      ( wn wa wi wal wex con3 anim2d alimi ax-mp exim mp2 ) CBGZHZCAGZHZIZDJZSD
      KUADKABIZDJUCEUDUBDUDRTCABLMNOFSUADPQ $.

    $( Alternate proof of ~ festino , shorter but using more axioms.  See
       comment of ~ dariiALT .  (Contributed by David A. Wheeler, 27-Aug-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    barocoALT $p |- E. x ( ch /\ -. ph ) $=
      ( wn wa wi spi con3i anim2i eximii ) CBGZHCAGZHDFNOCABABIDEJKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Cesaro" $)
    cesaro.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Cesaro $)
    cesaro.min $e |- A. x ( ch -> ps ) $.
    $( Existence premise for Cesaro $)
    cesaro.e $e |- E. x ch $.
    $( "Cesaro", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ch ` is ` ps ` , and ` ch ` exist, therefore some ` ch `
       is not ` ph ` .  In Aristotelian notation, EAO-2:  PeM and SaM therefore
       SoP. (Contributed by David A. Wheeler, 28-Aug-2016.)  Reduce
       dependencies on axioms.  (Revised by BJ, 16-Sep-2022.) $)
    cesaro $p |- E. x ( ch /\ -. ph ) $=
      ( wn cesare barbarilem ) CAHDGABCDEFIJ $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Camestros" $)
    camestros.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Camestros $)
    camestros.min $e |- A. x ( ch -> -. ps ) $.
    $( Existence premise for Camestros $)
    camestros.e $e |- E. x ch $.
    $( "Camestros", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , no ` ch ` is ` ps ` , and ` ch ` exist, therefore some ` ch `
       is not ` ph ` .  In Aristotelian notation, AEO-2:  PaM and SeM therefore
       SoP. For example, "All horses have hooves", "No humans have hooves", and
       humans exist, therefore "Some humans are not horses".  (Contributed by
       David A. Wheeler, 28-Aug-2016.)  Reduce dependencies on axioms.
       (Revised by BJ, 16-Sep-2022.) $)
    camestros $p |- E. x ( ch /\ -. ph ) $=
      ( wn camestres barbarilem ) CAHDGABCDEFIJ $.
  $}

  $( Figure 3 $)

  ${
    $( Major premise for the Aristotelian syllogism "Datisi" $)
    datisi.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Datisi $)
    datisi.min $e |- E. x ( ph /\ ch ) $.
    $( "Datisi", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ph ` is ` ch ` , therefore some ` ch ` is ` ps ` .
       In Aristotelian notation, AII-3:  MaP and MiS therefore SiP.
       (Contributed by David A. Wheeler, 28-Aug-2016.)  Shorten and reduce
       dependencies on axioms.  (Revised by BJ, 16-Sep-2022.) $)
    datisi $p |- E. x ( ch /\ ps ) $=
      ( wa wex exancom mpbi darii ) ABCDEACGDHCAGDHFACDIJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Disamis" $)
    disamis.maj $e |- E. x ( ph /\ ps ) $.
    $( Minor premise for Disamis $)
    disamis.min $e |- A. x ( ph -> ch ) $.
    $( "Disamis", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       ` ps ` , and all ` ph ` is ` ch ` , therefore some ` ch ` is ` ps ` .
       In Aristotelian notation, IAI-3:  MiP and MaS therefore SiP.
       (Contributed by David A. Wheeler, 28-Aug-2016.)  Reduce dependencies on
       axioms.  (Revised by BJ, 16-Sep-2022.) $)
    disamis $p |- E. x ( ch /\ ps ) $=
      ( wa wex datisi exancom mpbi ) BCGDHCBGDHACBDFEIBCDJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Ferison" $)
    ferison.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Ferison $)
    ferison.min $e |- E. x ( ph /\ ch ) $.
    $( "Ferison", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and some ` ph ` is ` ch ` , therefore some ` ch ` is not
       ` ps ` .  Instance of ~ datisi .  In Aristotelian notation, EIO-3:  MeP
       and MiS therefore SoP. (Contributed by David A. Wheeler,
       28-Aug-2016.) $)
    ferison $p |- E. x ( ch /\ -. ps ) $=
      ( wn datisi ) ABGCDEFH $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Bocardo" $)
    bocardo.maj $e |- E. x ( ph /\ -. ps ) $.
    $( Minor premise for Bocardo $)
    bocardo.min $e |- A. x ( ph -> ch ) $.
    $( "Bocardo", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       not ` ps ` , and all ` ph ` is ` ch ` , therefore some ` ch ` is not
       ` ps ` .  Instance of ~ disamis .  In Aristotelian notation, OAO-3:  MoP
       and MaS therefore SoP. For example, "Some cats have no tails", "All cats
       are mammals", therefore "Some mammals have no tails".  (Contributed by
       David A. Wheeler, 28-Aug-2016.) $)
    bocardo $p |- E. x ( ch /\ -. ps ) $=
      ( wn disamis ) ABGCDEFH $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Darapti" $)
    darapti.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Darapti $)
    darapti.min $e |- A. x ( ph -> ch ) $.
    $( Existence premise for Darapti $)
    darapti.e $e |- E. x ph $.
    $( "Darapti", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ph ` is ` ch ` , and some ` ph ` exist, therefore some
       ` ch ` is ` ps ` .  In Aristotelian notation, AAI-3:  MaP and MaS
       therefore SiP. For example, "All squares are rectangles" and "All
       squares are rhombuses", therefore "Some rhombuses are rectangles".
       (Contributed by David A. Wheeler, 28-Aug-2016.)  Reduce dependencies on
       axioms.  (Revised by BJ, 16-Sep-2022.) $)
    darapti $p |- E. x ( ch /\ ps ) $=
      ( wa wi wal wex id alanimi mp2an pm3.43 alimi ax-mp exim mp2 ) ACBHZIZDJZ
      ADKTDKACIZABIZHZDJZUBUCDJUDDJUFFEUCUDUEDUELMNUEUADACBOPQGATDRS $.

    $( Alternate proof of ~ darapti , shorter but using more axioms.  See
       comment of ~ dariiALT .  (Contributed by David A. Wheeler, 27-Aug-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    daraptiALT $p |- E. x ( ch /\ ps ) $=
      ( wa wi spi jca eximii ) ACBHDGACBACIDFJABIDEJKL $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Felapton" $)
    felapton.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Felapton $)
    felapton.min $e |- A. x ( ph -> ch ) $.
    $( Existence premise for Felapton $)
    felapton.e $e |- E. x ph $.
    $( "Felapton", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ph ` is ` ch ` , and some ` ph ` exist, therefore some
       ` ch ` is not ` ps ` .  Instance of ~ darapti .  In Aristotelian
       notation, EAO-3:  MeP and MaS therefore SoP. For example, "No flowers
       are animals" and "All flowers are plants", therefore "Some plants are
       not animals".  (Contributed by David A. Wheeler, 28-Aug-2016.) $)
    felapton $p |- E. x ( ch /\ -. ps ) $=
      ( wn darapti ) ABHCDEFGI $.
  $}

  $( Figure 4 $)

  ${
    $( Major premise for the Aristotelian syllogism "Calemes" $)
    calemes.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Calemes $)
    calemes.min $e |- A. x ( ps -> -. ch ) $.
    $( "Calemes", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and no ` ps ` is ` ch ` , therefore no ` ch ` is ` ph ` .  In
       Aristotelian notation, AEE-4:  PaM and MeS therefore SeP. (Contributed
       by David A. Wheeler, 28-Aug-2016.)  Reduce dependencies on axioms.
       (Revised by BJ, 16-Sep-2022.) $)
    calemes $p |- A. x ( ch -> -. ph ) $=
      ( wn wi wal con2 alimi ax-mp camestres ) ABCDEBCGHZDICBGHZDIFNODBCJKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Dimatis" $)
    dimatis.maj $e |- E. x ( ph /\ ps ) $.
    $( Minor premise for Dimatis $)
    dimatis.min $e |- A. x ( ps -> ch ) $.
    $( "Dimatis", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       ` ps ` , and all ` ps ` is ` ch ` , therefore some ` ch ` is ` ph ` .
       In Aristotelian notation, IAI-4:  PiM and MaS therefore SiP. For
       example, "Some pets are rabbits", "All rabbits have fur", therefore
       "Some fur bearing animals are pets".  Like ~ darii with positions
       interchanged.  (Contributed by David A. Wheeler, 28-Aug-2016.)  Shorten
       and reduce dependencies on axioms.  (Revised by BJ, 16-Sep-2022.) $)
    dimatis $p |- E. x ( ch /\ ph ) $=
      ( wa wex darii exancom mpbi ) ACGDHCAGDHBCADFEIACDJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Fresison" $)
    fresison.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Fresison $)
    fresison.min $e |- E. x ( ps /\ ch ) $.
    $( "Fresison", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` (PeM), and some ` ps ` is ` ch ` (MiS), therefore some ` ch ` is
       not ` ph ` (SoP).  In Aristotelian notation, EIO-4:  PeM and MiS
       therefore SoP. (Contributed by David A. Wheeler, 28-Aug-2016.)  Shorten
       and reduce dependencies on axioms.  (Revised by BJ, 16-Sep-2022.) $)
    fresison $p |- E. x ( ch /\ -. ph ) $=
      ( wa wex exancom mpbi festino ) ABCDEBCGDHCBGDHFBCDIJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Calemos" $)
    calemos.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Calemos $)
    calemos.min $e |- A. x ( ps -> -. ch ) $.
    $( Existence premise for Calemos $)
    calemos.e $e |- E. x ch $.
    $( "Calemos", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` (PaM), no ` ps ` is ` ch ` (MeS), and ` ch ` exist, therefore
       some ` ch ` is not ` ph ` (SoP).  In Aristotelian notation, AEO-4:  PaM
       and MeS therefore SoP. (Contributed by David A. Wheeler, 28-Aug-2016.)
       Shorten and reduce dependencies on axioms.  (Revised by BJ,
       16-Sep-2022.) $)
    calemos $p |- E. x ( ch /\ -. ph ) $=
      ( wn calemes barbarilem ) CAHDGABCDEFIJ $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Fesapo" $)
    fesapo.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Fesapo $)
    fesapo.min $e |- A. x ( ps -> ch ) $.
    $( Existence premise for Fesapo $)
    fesapo.e $e |- E. x ps $.
    $( "Fesapo", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ps ` is ` ch ` , and ` ps ` exist, therefore some ` ch `
       is not ` ph ` .  In Aristotelian notation, EAO-4:  PeM and MaS therefore
       SoP. (Contributed by David A. Wheeler, 28-Aug-2016.)  Reduce
       dependencies on axioms.  (Revised by BJ, 16-Sep-2022.) $)
    fesapo $p |- E. x ( ch /\ -. ph ) $=
      ( wn wi wal con2 alimi ax-mp felapton ) BACDABHIZDJBAHIZDJEOPDABKLMFGN $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Bamalip" $)
    bamalip.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Bamalip $)
    bamalip.min $e |- A. x ( ps -> ch ) $.
    $( Existence premise for Bamalip $)
    bamalip.e $e |- E. x ph $.
    $( "Bamalip", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ps ` is ` ch ` , and ` ph ` exist, therefore some ` ch `
       is ` ph ` .  In Aristotelian notation, AAI-4:  PaM and MaS therefore
       SiP. Very similar to ~ barbari .  (Contributed by David A. Wheeler,
       28-Aug-2016.)  Shorten and reduce dependencies on axioms.  (Revised by
       BJ, 16-Sep-2022.) $)
    bamalip $p |- E. x ( ch /\ ph ) $=
      ( wa wex barbari exancom mpbi ) ACHDICAHDIBCADFEGJACDKL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Intuitionistic logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Intuitionistic (constructive) logic is similar to classical logic with the
  notable omission of ~ ax-3 and theorems such as ~ exmid or ~ peirce .  We
  mostly treat intuitionistic logic in a separate file, iset.mm, which is known
  as the Intuitionistic Logic Explorer on the web site.  However, iset.mm has a
  number of additional axioms (mainly to replace definitions like ~ df-or and
  ~ df-ex which are not valid in intuitionistic logic) and we want to prove
  those axioms here to demonstrate that adding those axioms in iset.mm does not
  make iset.mm any less consistent than set.mm.

  The following axioms are unchanged between set.mm and iset.mm: ~ ax-1 ,
  ~ ax-2 , ~ ax-mp , ~ ax-4 , ~ ax-11 , ~ ax-gen , ~ ax-7 , ~ ax-12 , ~ ax-8 ,
  ~ ax-9 , and ~ ax-5 .

  In this list of axioms, the ones that repeat earlier theorems are marked
  "(New usage is discouraged.)" so that the earlier theorems will be used
  consistently in other proofs.

$)

  $( Left 'and' elimination (intuitionistic logic axiom ax-ia1).  (Contributed
     by Jim Kingdon, 21-May-2018.)  (New usage is discouraged.) $)
  axia1 $p |- ( ( ph /\ ps ) -> ph ) $=
    ( simpl ) ABC $.

  $( Right 'and' elimination (intuitionistic logic axiom ax-ia2).  (Contributed
     by Jim Kingdon, 21-May-2018.)  (New usage is discouraged.) $)
  axia2 $p |- ( ( ph /\ ps ) -> ps ) $=
    ( simpr ) ABC $.

  $( 'And' introduction (intuitionistic logic axiom ax-ia3).  (Contributed by
     Jim Kingdon, 21-May-2018.)  (New usage is discouraged.) $)
  axia3 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $=
    ( pm3.2 ) ABC $.

  $( 'Not' introduction (intuitionistic logic axiom ax-in1).  (Contributed by
     Jim Kingdon, 21-May-2018.)  (New usage is discouraged.) $)
  axin1 $p |- ( ( ph -> -. ph ) -> -. ph ) $=
    ( pm2.01 ) AB $.

  $( 'Not' elimination (intuitionistic logic axiom ax-in2).  (Contributed by
     Jim Kingdon, 21-May-2018.)  (New usage is discouraged.) $)
  axin2 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( pm2.21 ) ABC $.

  $( Definition of 'or' (intuitionistic logic axiom ax-io).  (Contributed by
     Jim Kingdon, 21-May-2018.)  (New usage is discouraged.) $)
  axio $p |- ( ( ( ph \/ ch ) -> ps ) <->
      ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $=
    ( jaob ) ABCD $.

  $( Specialization (intuitionistic logic axiom ax-4).  This is just ~ sp by
     another name.  (Contributed by Jim Kingdon, 31-Dec-2017.)
     (New usage is discouraged.) $)
  axi4 $p |- ( A. x ph -> ph ) $=
    ( sp ) ABC $.

  $( Converse of ~ axc4 (intuitionistic logic axiom ax-i5r).  (Contributed by
     Jim Kingdon, 31-Dec-2017.) $)
  axi5r $p |- ( ( A. x ph -> A. x ps ) -> A. x ( A. x ph -> ps ) ) $=
    ( wal wi hba1 hbim sp imim2i alrimih ) ACDZBCDZEKBECKLCACFBCFGLBKBCHIJ $.

  $( The setvar ` x ` is not free in ` A. x ph ` (intuitionistic logic axiom
     ax-ial).  (Contributed by Jim Kingdon, 31-Dec-2017.)
     (New usage is discouraged.) $)
  axial $p |- ( A. x ph -> A. x A. x ph ) $=
    ( hba1 ) ABC $.

  $( The setvar ` x ` is not free in ` E. x ph ` (intuitionistic logic axiom
     ax-ie1).  (Contributed by Jim Kingdon, 31-Dec-2017.)
     (New usage is discouraged.) $)
  axie1 $p |- ( E. x ph -> A. x E. x ph ) $=
    ( hbe1 ) ABC $.

  $( A key property of existential quantification (intuitionistic logic axiom
     ax-ie2).  (Contributed by Jim Kingdon, 31-Dec-2017.) $)
  axie2 $p |- ( A. x ( ps -> A. x ps ) ->
              ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $=
    ( wal wi wnf wex wb nf5 19.23t sylbir ) BBCDECDBCFABECDACGBEHBCIABCJK $.

  $( Axiom of existence (intuitionistic logic axiom ax-i9).  In classical
     logic, this is equivalent to ~ ax-6 but in intuitionistic logic it needs
     to be stated using the existential quantifier.  (Contributed by Jim
     Kingdon, 31-Dec-2017.)  (New usage is discouraged.) $)
  axi9 $p |- E. x x = y $=
    ( ax6e ) ABC $.

  $( Axiom of Quantifier Substitution (intuitionistic logic axiom ax-10).  This
     is just ~ axc11n by another name.  (Contributed by Jim Kingdon,
     31-Dec-2017.)  (New usage is discouraged.) $)
  axi10 $p |- ( A. x x = y -> A. y y = x ) $=
    ( axc11n ) ABC $.

  $( Axiom of Quantifier Introduction (intuitionistic logic axiom ax-i12).  In
     classical logic, this is mostly a restatement of ~ axc9 (with one
     additional quantifier).  But in intuitionistic logic, changing the
     negations and implications to disjunctions makes it stronger.  Usage of
     this theorem is discouraged because it depends on ~ ax-13 .  (Contributed
     by Jim Kingdon, 31-Dec-2017.)  Avoid ~ ax-11 .  (Revised by Wolf Lammen,
     24-Apr-2023.)  (New usage is discouraged.) $)
  axi12 $p |- ( A. z z = x \/ ( A. z z = y \/
                A. z ( x = y -> A. z x = y ) ) ) $=
    ( weq wal wo wi nfa1 nfor 19.32 wn axc9 orrd orri orass mpbir mpgbi mpbi )
    CADZCEZCBDZCEZFZABDZUDCEGZCEZFZTUBUFFFUCUEFZUGCUCUECTUBCSCHUACHIJUHTUBUEFZF
    TUITKUBUEABCLMNTUBUEOPQTUBUFOR $.

  $( Axiom of Bundling (intuitionistic logic axiom ax-bnd).  In classical
     logic, this and ~ axi12 are fairly straightforward consequences of
     ~ axc9 .  But in intuitionistic logic, it is not easy to add the extra
     ` A. x ` to ~ axi12 and so we treat the two as separate axioms.  Usage of
     this theorem is discouraged because it depends on ~ ax-13 .  (Contributed
     by Jim Kingdon, 22-Mar-2018.)  (Proof shortened by Wolf Lammen,
     24-Apr-2023.)  (New usage is discouraged.) $)
  axbnd $p |- ( A. z z = x \/ ( A. z z = y \/
                 A. x A. z ( x = y -> A. z x = y ) ) ) $=
    ( weq wal wo wi nfae nfor 19.32 orass bitri axi12 mpbir mpgbi ) CADCEZCBDCE
    ZFZABDZSCEGCEZFZPQTAEZFFZAUAAERUBFUCRTAPQACAAHCBAHIJPQUBKLUAPQTFFABCMPQTKNO
    $.
