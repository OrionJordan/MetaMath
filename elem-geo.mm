$(
###############################################################################
  ELEMENTARY GEOMETRY
###############################################################################
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Misc. Logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Additional logical theorems to streamline proofs. $)

${
    $( Rearrangement of conjuncts. Used in cong-seg-divL1. $)
    2an13
        $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ( ph /\ ch ) )
        $= ( wa an3 ancom2s ) ABEDCACEABDCFG $.
$}

${
    pm1.5syl.1 $e |- ( ph -> ( ps \/ ( ch \/ th ) ) ) $.
    $( Saves steps in Col perm $)
    pm1.5syl
        $p |- ( ph -> ( ch \/ ( ps \/ th ) ) )
        $= ( wo pm1.5 syl ) ABCDFFCBDFFEBCDGH $.
$}

${
    pm2.3syl.1 $e |- ( ph -> ( ps \/ ( ch \/ th ) ) ) $.
    $( Rearrangement of disjuncts in the antecedent $)
    pm2.3syl
        $p |- ( ph -> ( ps \/ ( th \/ ch ) ) )
        $= ( wo pm2.3 syl ) ABCDFFBDCFFEBCDGH $.
$}

${
    disimp2intro.1 $e |- ( ( ph /\ ps ) -> th ) $.
    disimp2intro.2 $e |- ( ( ch /\ ps ) -> ta ) $.
    disimp2intro
        $p |- ( ( ( ph \/ ch ) /\ ps ) -> ( th \/ ta ) )
        $= ( wo wa orcd olcd jaoian ) ABDEHCABIDEFJCBIEDGKL $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Primitive notions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Declare constants and variables. The constant C is for congruence and B for betweenness. $)

$c B C $.
$v a b c d e f g h i j k m n o p q r s a' b' c' d' $.

$( Assign each variable as a setvar (analougous to point). $)

pointa $f setvar a $.
pointb $f setvar b $.
pointc $f setvar c $.
pointd $f setvar d $.
pointe $f setvar e $.
pointf $f setvar f $.
pointg $f setvar g $.
pointh $f setvar h $.
pointi $f setvar i $.
pointj $f setvar j $.
pointk $f setvar k $.
pointm $f setvar m $.
pointn $f setvar n $.
pointo $f setvar o $.
pointp $f setvar p $.
pointq $f setvar q $.
pointr $f setvar r $.
points $f setvar s $.
pointa' $f setvar a' $.
pointb' $f setvar b' $.
pointc' $f setvar c' $.
pointd' $f setvar d' $.

$( Assign syntax to predicates. $)

wffcong $a wff ( a b C c d ) $.
wffbetw $a wff ( B a b c ) $.

$( Logical axioms of predicates. $)

ax-predC1 $a |- ( x = y -> ( ( x b C c d ) -> ( y b C c d ) ) ) $.
ax-predC2 $a |- ( x = y -> ( ( a x C c d ) -> ( a y C c d ) ) ) $.
ax-predC3 $a |- ( x = y -> ( ( a b C x d ) -> ( a b C y d ) ) ) $.
ax-predC4 $a |- ( x = y -> ( ( a b C c x ) -> ( a b C c y ) ) ) $.

ax-predB1 $a |- ( x = y -> ( ( B x b c ) -> ( B y b c ) ) ) $.
ax-predB2 $a |- ( x = y -> ( ( B a x c ) -> ( B a y c ) ) ) $.
ax-predB3 $a |- ( x = y -> ( ( B a b x ) -> ( B a b y ) ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

ax-A1 $a |- ( a b C b a ) $.
ax-A2 $a |- ( ( ( a b C p q ) /\ ( a b C r s ) ) -> ( p q C r s ) ) $.
ax-A3 $a |- ( ( a b C c c ) -> a = b ) $.

${
$d q x $.
$d a x $.
$d b x $.
$d c x $.
ax-A4 $a |- E. x ( ( B q a x ) /\ ( a x C b c ) ) $.
$}

ax-A5 $a |- ( ( ( ( ( ( ( ( B a b c ) /\ ( B e f g ) ) /\ ( a b C e f ) ) /\ ( b c C f g ) ) /\ ( a d C e h ) ) /\ ( b d C f h ) ) /\ -. a = b ) -> ( c d C g h ) ) $.
ax-A6 $a |- ( ( B a b a ) -> a = b ) $.
ax-A7 $a |- ( ( ( B a p c ) /\ ( B b q c ) ) -> E. x ( ( B p x b ) /\ ( B q x a ) ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Dimensions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$( In order to analyze a dimensionless geometry, references to dimensions will be definitions instead of axioms, and used in the hypothesis of certain theorems depending on some dimension. $)

$( Declare Upper dimension symbols $)
$c U0 U1 U2 $.

$( Extend wff notation to include Upper dimension 0. $)
wffU0 $a wff U0 $.

$( Extend wff notation to include Upper dimension 1. $)
wffU1 $a wff U0 $.

$( Extend wff notation to include Upper dimension 2. $)
wffU2 $a wff U0 $.

df-U0 $a |- ( U0 <-> A. a A. b a = b ) $.

df-U1 $a |- ( U1 <-> ( ( ( B a b c ) \/ ( B b c a ) ) \/ ( B c a b ) ) ) $.

df-U2 $a |- ( U2 <-> ( ( ( ( ( a p C a q ) /\ ( b p C b q ) ) /\ ( c p C c q ) ) /\ -. p = q ) -> ( ( ( B a b c ) \/ ( B b c a ) ) \/ ( B c a b ) ) ) $.

$( Declare Lower dimension symbols $)
$c L1 L2 $.

$( Extend wff notation to include Lower dimension 1. $)
wffL1 $a wff L1 $.

$( Extend wff notation to include Lower dimension 2. $)
wffL2 $a wff L2 $.

df-L1 $a |- ( L1 <-> E. a E. b -. a = b ) $.

df-L2 $a |- ( L2 <-> E. a E. b E. c ( ( -. ( B a b c ) \/ -. ( B b c a ) ) \/ -. ( B c a b ) ) $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Dimension properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

U0imp
    $p |- ( U0 -> a = b )
    $= ( wffU0 weq wal df-U0 biimpi 19.21bbi ) CZABDZABIJBEAEABFGH $.

${
    $( Our space is either 0D, or at least 1D. Useful for many proofs. $)
    U0orL1
        $p |- ( U0 \/ L1 )
        $= ( wffU0 wffL1 wn pointa pointb weq wex wal df-U0 exnal biimpri sylnbi eximi syl df-L1 sylibr orri ) AZBZRCZDEFZCEGZDGZSTUAEHZCZDGZUCRUDDHZUFDEIUFUGCUD DJKLUEUBDUBUEUAEJKMNDEOPQ $.
$}

${
    $( In zero dimensions, all congruence holds $)
    U0impcong
        $p |- ( U0 -> ( a b C c d ) )
        $= ( wffU0 weq wffcong U0imp cong-nullseg ax-predC2 mpisyl ax-predC4 sylc ) EZCDFABCCGZABCDGCDHNABFAACCGOABHACIABACCJKCDABCLM $.
$}

${
    $( In zero dimensions, all betweenness holds $)
    U0impbetw
        $p |- ( U0 -> ( B a b c ) )
        $= ( wffU0 weq wffbetw U0imp betw-id ax-predB3 mpisyl ) DBCEABBFABCFBCGABHBCABIJ $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Congruence properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

${
    $( Theorem 2.1 of [SST]. $)
    cong-ref
        $p |- ( a b C a b )
        $= ( wffcong ax-A1 ax-A2 mp2an ) BAABCZGABABCBADZHBAABABEF $.
$}

${
    $( Theorem 2.2 of [SST]. $)
    cong-sym
        $p |- ( ( a b C c d ) -> ( c d C a b ) )
        $= ( wffcong cong-ref ax-A2 mpan2 ) ABCDEABABECDABEABFABCDABGH $.
$}

${
    cong-sym-d.1 $e |- ( ph -> ( a b C c d ) ) $.
    $( Deductive form of cong-sym. $)
    cong-sym-d
        $p |- ( ph -> ( c d C a b ) )
        $= ( wffcong wa cong-ref jctir ax-A2 syl ) ABCDEGZBCBCGZHDEBCGAMNFBCIJBCDEBCKL $.
$}

${
    $( Theorem 2.3 of [SST]. $)
    cong-trans
        $p |- ( ( ( a b C c d ) /\ ( c d C e f ) ) -> ( a b C e f ) )
        $= ( wffcong cong-sym ax-A2 sylan ) ABCDGCDABGCDEFGABEFGABCDHCDABEFIJ $.
$}

${
    cong-trans-d.1 $e |- ( ph -> ( a b C c d ) ) $.
    cong-trans-d.2 $e |- ( ph -> ( c d C e f ) ) $.
    cong-trans-d
        $p |- ( ph -> ( a b C e f ) )
        $= ( wffcong wa jca cong-trans syl ) ABCDEJZDEFGJZKBCFGJAOPHILBCDEFGMN $.
$}

${
    cong-trans-d2.1 $e |- ( ph -> ( ( a b C c d ) /\ ( c d C e f ) ) ) $.
    cong-trans-d2
        $p |- ( ph -> ( a b C e f ) )
        $= ( wffcong simpld simprd cong-trans-d ) ABCDEFGABCDEIZDEFGIZHJAMNHKL $.
$}

${
    $( Theorem 2.4 of [SST]. $)
    cong-lhs
        $p |- ( ( a b C c d ) -> ( b a C c d ) )
        $= ( wffcong ax-A1 ax-A2 mpan ) ABBAEABCDEBACDEABFABBACDGH $.
$}

${
    cong-lhs-d.1 $e |- ( ph -> ( a b C c d ) ) $.
    cong-lhs-d
        $p |- ( ph -> ( b a C c d ) )
        $= ( wffcong cong-lhs syl ) ABCDEGCBDEGFBCDEHI $.
$}

${
    $( Theorem 2.5 of [SST]. $)
    cong-rhs
        $p |- ( ( a b C c d ) -> ( a b C d c ) )
        $= ( wffcong ax-A1 cong-trans mpan2 ) ABCDECDDCEABDCECDFABCDDCGH $.
$}

${
    cong-rhs-d.1 $e |- ( ph -> ( a b C c d ) ) $.
    $( Deductive form of cong-rhs. $)
    cong-rhs-d
        $p |- ( ph -> ( a b C d c ) )
        $= ( wffcong congrhs syl ) ABCDEGBCEDGFBCDEHI $.
$}

${
    $( A congruence identity combining left hand symmetry and right hand symmetry. $)
    cong-2143
        $p |- ( ( a b C c d ) -> ( b a C d c ) )
        $= ( wffcong cong-lhs congrhs syl ) ABCDEBACDEBADCEABCDFBACDGH $.
$}

${
    cong-2143-d.1 $e |- ( ph -> ( a b C c d ) ) $.
    $( Deductive form of cong-2143. $)
    cong-2143-d
        $p |- ( ph -> ( b a C d c ) )
        $= ( wffcong cong-2143 syl ) ABCDEGCBEDGFBCDEHI $.
$}

cong-3421
    $p |- ( ( a b C c d ) -> ( c d C b a ) )
    $= ( wffcong cong-sym cong-rhs syl ) ABCDECDABECDBAEABCDFCDABGH $.

cong-4312
    $p |- ( ( a b C c d ) -> ( d c C a b ) )
    $= ( wffcong cong-sym cong-lhs syl ) ABCDECDABEDCABEABCDFCDABGH $.

${
    cong-4312-d.1 $e |- ( ph -> ( a b C c d ) ) $.
    cong-4312-d
        $p |- ( ph -> ( d c C a b ) )
        $= ( wffcong cong-4312 syl ) ABCDEGEDBCGFBCDEHI $.
$}

cong-4321
    $p |- ( ( a b C c d ) -> ( d c C b a ) )
    $= ( wffcong cong-sym cong-lhs cong-rhs 3syl ) ABCDECDABEDCABEDCBAEABCDFCDABGDCABHI $.

${
    $d a x $.
    $d b x $.
    cong-nullseg
        $p |- ( a a C b b )
        $= ( vx wffcong weq wi ax-A3 equcomi ax-predC2 3syl pm2.43i wffbetw wa wex ax-A4 exsimpr ax-mp exlimiiv ) ACBBDZAABBDZCSTSACECAESTFACBGACHCAABBIJKBACLZSMCNS CNCABBBOUASCPQR $.
$}

cong-nullseg-sym
    $p |- ( ( c c C a b ) -> a = b )
    $= ( wffcong weq cong-sym ax-A3 syl ) CCABDABCCDABECCABFABCGH $.

$( Declare OFSC symbol $)
$c OFSC $.

$( Extend wff notation to include outer five-segment configuration $)
wffofsc $a wff OFSC ( a b c d e f g h ) $.

df-ofsc $a |- ( OFSC ( a b c d e f g h ) <-> ( ( ( ( ( ( B a b c ) /\ ( B e f g ) ) /\ ( a b C e f )  ) /\ ( b c C f g ) ) /\ ( a d C e h ) ) /\ ( b d C f h ) ) ) $.

${
    $( Introduces OFSC from its definition. $)
    ofsc-intro
        $p |- ( ( ( ( ( ( ( B a b c ) /\ ( B e f g ) ) /\ ( a b C e f ) ) /\ ( b c C f g ) ) /\ ( a d C e h ) ) /\ ( b d C f h ) ) -> OFSC ( a b c d e f g h ) )
        $= ( wffofsc wffbetw wa wffcong df-ofsc biimpri ) ABCDEFGHIABCJEFGJKABEFLKBCFGLKADEHLKBDFHLKABCDEFGH MN $.
$}

${
    $( Exchanges OFSC with its definition. $)
    ofsc-outro
        $p |- ( OFSC ( a b c d e f g h ) -> ( ( ( ( ( ( B a b c ) /\ ( B e f g ) ) /\ ( a b C e f ) ) /\ ( b c C f g ) ) /\ ( a d C e h ) ) /\ ( b d C f h ) ) )
        $= ( wffofsc wffbetw wa wffcong df-ofsc biimpi ) ABCDEFGHIABCJEFGJKABEFLKBCFGLKADEHLKBDFHLKABCDEFGH MN $.
$}

${
    ofsc-intro-d.1 $e |- ( ph -> ( B a b c ) ) $.
    ofsc-intro-d.2 $e |- ( ph -> ( B e f g ) ) $.
    ofsc-intro-d.3 $e |- ( ph -> ( a b C e f ) ) $.
    ofsc-intro-d.4 $e |- ( ph -> ( b c C f g ) ) $.
    ofsc-intro-d.5 $e |- ( ph -> ( a d C e h ) ) $.
    ofsc-intro-d.6 $e |- ( ph -> ( b d C f h ) ) $.
    $( Deductive form of ofsc-intro. $)
    ofsc-intro-d
        $p |- ( ph -> OFSC ( a b c d e f g h ) )
        $= ( wffbetw wa wffcong wffofsc jca df-ofsc sylibr ) ABCDPZFGHPZQZBCFGRZQZCDGHRZQZBEFIRZQZCEGIRZQBCDEFG HISAUKULAUIUJAUGUHAUEUFAUCUDJKTLTMTNTOTBCDEFGHIUAU B $.
$}
${
    $( Alternative form of Five-Segment-Configuration-Axiom (ax-A5) using OFSC. $)
    ax-A5-alt
        $p |- ( ( OFSC ( a b c d e f g h ) /\ -. a = b ) -> ( c d C g h ) )
        $= ( wffofsc wffbetw wa wffcong weq wn df-ofsc ax-A5 sylanb ) ABCDEFGHIABCJEFGJKABEFLKBCFGLKADEHLKBDFHLKABMNCDGH LABCDEFGHOABCDEFGHPQ $.
$}

${
    $( Segment Addition. Theorem 2.11 of [SST]. $)
    segment-addition
        $p |- ( ( ( ( ( B a b c ) /\ ( B e f g ) ) /\ ( a b C e f ) ) /\ ( b c C f g ) ) -> ( a c C e g ) )
        $= ( weq wffbetw wa wffcong wi equcomi ax-predC2 equcoms cong-sym syl6 ax-A3 ax-predC3 imim12i mpsylsyld ax-predC1 syl6d adantld impd wn cong-2143 ad3antlr cong-nullseg ax-A5 an42ds mpan2 mpdan syl expcom pm2.61i ) ABGZABCHDEFHIZABDEJZIZBCEFJZIZACDFJZKUPUSUTVBUPURU TVBKUQUPURUTBCDFJZVBDEGZEDGZKUPURDEAAJZUTVCKZDELUP URAADEJZVFURVHKBABAADEMNAADEOPVFVDVEVGDEAQEDBCFRST VCVBKBABACDFUANUBUCUDVAUPUEZVBVAVIIZCAFDJZVBVJBAED JZVKURVLUQUTVIABDEUFUGVJVLIAADDJZVKADUHVAVMVLVIVKA BCADEFDUIUJUKULCAFDUFUMUNUO $.
$}

${
    segment-addition-d.1 $e |- ( ph -> ( B a b c ) ) $.
    segment-addition-d.2 $e |- ( ph -> ( B e f g ) ) $.
    segment-addition-d.3 $e |- ( ph -> ( a b C e f ) ) $.
    segment-addition-d.4 $e |- ( ph -> ( b c C f g ) ) $.
    segment-addition-d
        $p |- ( ph -> ( a c C e g ) )
        $= ( wffbetw wffcong segment-addition syl1111anc ) ABCDLEFGLBCEFMCDFGMBDEGMHIJKBCDEFGNO $.
$}

${
    $( If two points satisfy the segment construction axiom, they are the same point. Theorem 2.12 of [SST].$)
    unique-segcon
        $p |- ( -. q = a -> ( ( ( ( B q a x ) /\ ( a x C b c ) ) /\ ( ( B q a z ) /\ ( a z C b c ) ) ) -> x = z ) )
        $= ( wffcong wi weq wn wffbetw wa cong-sym simpll jca cong-ref jctir jctr ad2ant2r an3 ancom1s anim12i ax-A2 3syl segment-addition syl ax-A5 expcom syl5 ax-A3 imim2i mpsylsyld ) AAABGZABAAGZHFCIJZFCAKZCADEGZLFCBKZCBDEGZLZLZUMABI ZAAABMVAUPUPLZFCFCGZLZCACAGZLZFAFBGZLZCACBGZLZUOUM VAVIVJVAVGVHVAVEVFVAVCVDVAUPUPUPUQUTNZVLOFCPZQCAPQ VAUPURLZVDLZVJLVHVAVOVJUPURVOUQUSVNVDVMRSVAUQUSLZD ECAGZDECBGZLVJUQUPUTVPUQUPURUSTUAUQVQUSVRCADEMCBDE MUBDECACBUCUDZOFCAFCBUEUFOVSOVKUOUMFCAAFCABUGUHUIU NVBUMABAUJUKUL $.
$}

${
    unique-segcond.1 $e |- ( ph -> -. q = a ) $.
    unique-segcond.2 $e |- ( ph -> ( B q a x ) ) $.
    unique-segcond.3 $e |- ( ph -> ( a x C b c ) ) $.
    unique-segcond.4 $e |- ( ph -> ( B q a z ) ) $.
    unique-segcond.5 $e |- ( ph -> ( a z C b c ) ) $.
    unique-segcond
        $p |- ( ph -> x = z )
        $= ( weq wn wffbetw wffcong wa jca jca32 unique-segcon sylc ) AGDMNGDBOZDBEFPZQZGDCOZDCEFPZQQBCMHAUDUEUFAUBUCIJR KLSBCDEFGTUA $.
$}

cong-diff
    $p |- ( ( a b C c d ) -> ( -. a = b -> -. c = d ) )
    $= ( wffcong weq wn ax-predC4 ax-A3 syl6 com12 con3d wi equcomi a1i nsyld ) ABCDEZABFZGDCFZCDFZQSRSQRSQABCCERDCABCHABCIJKLTSMQ CDNOP $.

cong-diff2
    $p |- ( ( a b C c d ) -> ( -. c = d -> -. a = b ) )
    $= ( wffcong weq wn wi cong-sym cong-diff syl ) ABCDECDABECDFGABFGHABCDICDABJK $.

ax-a2-sym
    $p |- ( ( ( p q C a b ) /\ ( r s C a b ) ) -> ( p q C r s ) )
    $= ( wffcong cong-sym ax-A2 syl2an ) CDABGABCDGABEFGCDEFGEFABGCDABHEFABHABCDEFIJ $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Betweenness properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


${
    $d a x $.
    $d b x $.
    betw-id
        $p |- ( B a b b )
        $= ( vx wffbetw wffcong wa weq wi ax-A3 adantl ax-predB3 equcoms syl adantrd pm2.43i ax-A4 exlimiiv ) ABCDZBCBBEZFZABBDZCTUATRUASTBCGZRUAHZSUBRBCBIJUCCB CBABKLMNOCBBBAPQ $.
$}

${
    $d a x $.
    $d b x $.
    $d c x $.
    betw-sym
        $p |- ( ( B a b c ) -> ( B c b a ) )
        $= ( wffbetw betw-id wa vx wex ax-A7 weq wi ax-A6 adantr equcomi ax-predB2 adantld 3syl pm2.43i exlimiv syl mpan2 ) ABCDZBCCDZCBADZBCEUBUCFBGBDZCGADZFZGHUDGABCBCIUGUD GUGUDUGBGJZGBJZUGUDKUEUHUFBGLMBGNUIUFUDUEGBCAOPQRS TUA $.
$}

${
    betw-sym-d.1 $e |- ( ph -> ( B a b c ) ) $.
    betw-sym-d
        $p |- ( ph -> ( B c b a ) )
        $= ( wffbetw betw-sym syl ) ABCDFDCBFEBCDGH $.
$}

betw-id2
    $p |- ( B a a b )
    $= ( wffbetw betw-id betw-sym ax-mp ) BAACAABCBADBAAEF $.

${
    $d a x $.
    $d b x $.
    betw-swap
        $p |- ( ( ( B a b c ) /\ ( B b a c ) ) -> a = b )
        $= ( wffbetw wa vx wex weq ax-A7 ax-A6 anim12i equtr2 syl exlimiv equcomd ) ABCDBACDEZBAPBFBDZAFADZEZFGBAHZFABCBAISTFSBFHZAFHZ ETQUARUBBFJAFJKBAFLMNMO $.
$}

${
    $d a x $.
    $d b x $.
    $d c x $.
    betw-134
        $p |- ( ( ( B a b d ) /\ ( B b c d ) ) -> ( B a b c ) )
        $= ( wffbetw wa vx wex ax-A7 weq wi ax-A6 adantr equcomi ax-predB2 adantld 3syl pm2.43i exlimiv betw-sym ) ABDEBCDEFBGBEZCGAEZFZGHCBAEZABCEGABDBCIUCUDGUCUDUC BGJZGBJZUCUDKUAUEUBBGLMBGNUFUBUDUAGBCAOPQRSCBATQ $.
$}

${
    betw-134.1 $e |- ( ph -> ( B a b d ) ) $.
    betw-134.2 $e |- ( ph -> ( B b c d ) ) $.
    betw-134-d
        $p |- ( ph -> ( B a b c ) )
        $= ( wffbetw betw-134 syl2anc ) ABCEHCDEHBCDHFGBCDEIJ $.
$}

betw-241
    $p |- ( ( ( B a b c ) /\ ( B a c d ) ) -> ( B b c d ) )
    $= ( wffbetw wa betw-sym anim12ci betw-134 3syl ) ABCEZACDEZFDCAEZCBAEZFDCBEBCDEKNLMABCGACDGHDCBAIDC BGJ $.

${
    betw-241-d.1 $e |- ( ph -> ( B a b c ) ) $.
    betw-241-d.2 $e |- ( ph -> ( B a c d ) ) $.
    betw-241-d
        $p |- ( ph -> ( B b c d ) )
        $= ( wffbetw betw-241 syl2anc ) ABCDHBDEHCDEHFGBCDEIJ $.
$}

betw-241-sym
    $p |- ( ( ( B a b c ) /\ ( B a c d ) ) -> ( B d c b ) )
    $= ( wffbetw wa betw-241 betw-sym syl ) ABCEACDEFBCDEDCBEABCDGBCDHI $.

${
    betw-241-d.1 $e |- ( ph -> ( B a b c ) ) $.
    betw-241-d.2 $e |- ( ph -> ( B a c d ) ) $.
    betw-241-sym-d
        $p |- ( ph -> ( B d c b ) )
        $= ( wffbetw betw-241-sym syl2anc ) ABCDHBDEHEDCHFGBCDEIJ $.
$}

${
    $d ph x $.
    $d a x $.
    $d c x $.
    $d d x $.
    betw-142-d.1 $e |- ( ph -> ( B a b c ) ) $.
    betw-142-d.2 $e |- ( ph -> ( B b c d ) ) $.
    betw-142-d.3 $e |- ( ph -> -. b = c ) $.
    betw-142-d
        $p |- ( ph -> ( B a c d ) )
        $= ( vx wffbetw wffcong wa wex ax-A4 a1i weq wi betw-241 ex anim1d syl cong-ref jctir jctird wn unique-segcon syld ax-predB3 adantrd syl6 pm2.43d exlimdv mpd ) ABDIJZDIDEKZLZIMZBDEJZUQAIDDEBNOAUPURIAUPURAUPIEPZ UPURQAUPCDIJZUOLZCDEJZDEDEKZLZLZUSAUPVAVDABCDJZUPV AQFVFUNUTUOVFUNUTBCDIRSTUAAVBVCGDEUBUCUDACDPUEVEUS QHIEDDECUFUAUGUSUNURUOIEBDUHUIUJUKULUM $.
$}

${
    $( Theorem 3.7(1) of [SST]. $)
    betw-142
        $p |- ( ( ( ( B a b c ) /\ ( B b c d ) ) /\ -. b = c ) -> ( B a c d ) )
        $= ( wffbetw wa weq wn simpll simplr simpr betw-142-d ) ABCEZBCDEZFZBCGHZFABCDMNPIMNPJOPKL $.
$}

${
    $( Theorem 3.5(2) of [SST] $)
    betw-132
        $p |- ( ( ( B a b d ) /\ ( B b c d ) ) -> ( B a c d ) )
        $= ( weq wffbetw wa wi ax-predB2 adantrd wn betw-134 anim1i anabss3 betw-142 sylan expcom pm2.61i ) BCEZABDFZBCDFZGZACDFZHSTUCUABCADIJUBSKZUCUBABCFZUA GZUDUCTUAUFUBUEUAABCDLMNABCDOPQR $.
$}

${
    betw-132-d.1 $e |- ( ph -> ( B b c d ) ) $.
    betw-132-d.2 $e |- ( ph -> ( B a b d ) ) $.
    betw-132-d
        $p |- ( ph -> ( B a c d ) )
        $= ( wffbetw betw-132 syl2anc ) ABCEHCDEHBDEHGFBCDEIJ $.
$}

${
    $( Theorem 3.6(2) of [SST] $)
    betw-243
        $p |- ( ( ( B a b c ) /\ ( B a c d ) ) -> ( B a b d ) )
        $= ( wffbetw wa betw-sym anim12ci betw-132 3syl ) ABCEZACDEZFDCAEZCBAEZFDBAEABDEKNLMABCGACDGHDCBAIDB AGJ $.
$}

${
    betw-243-d.1 $e |- ( ph -> ( B a c d ) ) $.
    betw-243-d.2 $e |- ( ph -> ( B a b c ) ) $.
    betw-243-d
        $p |- ( ph -> ( B a b d ) )
        $= ( wffbetw betw-243 syl2anc ) ABCDHBDEHBCEHGFBCDEIJ $.
$}

${
    $( Theorem 3.7(2) of [SST] $)
    betw-143
        $p |- ( ( ( ( B a b c ) /\ ( B b c d ) ) /\ -. b = c ) -> ( B a b d ) )
        $= ( wffbetw wa weq wn betw-sym anim12ci equcomi con3i anim12i betw-142 3syl ) ABCEZBCDEZFZBCGZHZFDCBEZCBAEZFZCBGZHZFDBAEABDERUCT UEPUBQUAABCIBCDIJUDSCBKLMDCBANDBAIO $.
$}

${
    betw-143-d.1 $e |- ( ph -> ( B a b c ) ) $.
    betw-143-d.2 $e |- ( ph -> ( B b c d ) ) $.
    betw-143-d.3 $e |- ( ph -> -. b = c ) $.
    betw-143-d
        $p |- ( ph -> ( B a b d ) )
        $= ( wffbetw weq wn betw-143 syl21anc ) ABCDICDEICDJKBCEIFGHBCDELM $.
$}

betw-equality
    $p |- ( ( ( B a b c ) /\ ( B a c b ) ) -> b = c )
    $= ( wffbetw wa weq betw-241 ax-A6 syl ) ABCDACBDEBCBDBCFABCBGBCHI $.

${
    betw-inequality.1 $e |- ( ph -> -. a = b ) $.
    betw-inequality.2 $e |- ( ph -> ( B a b c ) ) $.
    betw-inequality
        $p |- ( ph -> -. a = c )
        $= ( weq wffbetw ax-predB1 ax-A6 syl6 equtr syld mpan9 mtand ) ABDGZBCGZEABCDHZPQFPRDCGZQPRDCDHSBDCDIDCJKBDCLMNO $.
$}

${
    $d c v $.
    $d c u $.
    $( Two distinct points u,v imply the existence of a third distinct point. Theorem 3.14 of [SST] $)
    2pimp3p
        $p |- ( -. u = v -> E. c ( ( B a b c ) /\ -. b = c ) )
        $= ( weq wn wffbetw wffcong wa wex ax-A4 a1i wi cong-diff2 adantl com12 pm5.3 sylib eximdv mpd ) BAFGZCDEHZDEBAIZJZEKZUCDEFGZJZEKUFUBEDBACLMUBUEUHE UBUEUGNUEUHNUEUBUGUDUBUGNUCDEBAOPQUCUDUGRSTUA $.
$}

${
    $d a v $.
    $d a u $.
    $d b v $.
    $d b u $.
    $d c v $.
    $d c u $.
    $( When working in at least one dimension, there always exist a third point. $)
    uniq3p
        $p |- ( L1 -> E. c ( ( B a b c ) /\ -. b = c ) )
        $= ( wffL1 vu vv weq wn wex wffbetw wa df-L1 biimpi 2pimp3p exlimivv syl ) DZEFGHZFIEIZABCJBCGHKCIZQSEFLMRTEFFEABCNOP $.
$}

${
    $d a q $.
    $d b x $.
    $d ph q x $.
    $d c q x $.
    $d e q x $.
    $d p q x $.
    svintssd.1 $e |- ( ph -> ( B a b c ) ) $.
    svintssd.2 $e |- ( ph -> ( B d e c ) ) $.
    svintssd.3 $e |- ( ph -> ( B a p d ) ) $.
    $( Deduction associated with svintss. $)
    svintssd
        $p |- ( ph -> E. q ( ( B p q c ) /\ ( B b q e ) ) )
        $= ( vx wffbetw wa wex betw-sym syl ax-A7 syl2anc wi adantll expcom imp betw-132 ex ad2antrl anim1d eximdv mpd exlimddv ) AGLDMZFLBMZNZGHDMZCHFMZNZHOZLABGEMDFEMZUMLOKAEFDMU RJEFDPQLBDEGFRSAUMNZLHDMZUONZHOZUQAUMVBADCBMZUMVBT ABCDMVCIBCDPQUMVCVBULVCVBUKHFDBLCRUAUBQUCUSVAUPHUS UTUNUOUKUTUNTAULUKUTUNGLHDUDUEUFUGUHUIUJ $.
$}

${
    $d a q $.
    $d b q $.
    $d c q $.
    $d d q $.
    $d e q $.
    $d p q $.
    $( A line segment between one side of a triangle to the opposite vertex intersects with a segment from the remaining two sides. Theorem 3.17 of [SST] $)
    svintss
        $p |- ( ( ( ( B a b c ) /\ ( B d e c ) ) /\ ( B a p d ) ) -> E. q ( ( B p q c ) /\ ( B b q e ) ) )
        $= ( wffbetw wa simpll simplr simpr svintssd ) ABCHZDECHZIZAFDHZIABCDEFGNOQJNOQKPQLM $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Congruence and Betweenness properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Declare IFSC symbol $)
$c IFSC $.

$( Extend wff notation to include inner five-track configuration $)
wffifsc $a wff IFSC ( a b c d e f g h ) $.

df-ifsc $a |- ( IFSC ( a b c d e f g h ) <-> ( ( ( ( ( ( B a b c ) /\ ( B e f g ) ) /\ ( a c C e g )  ) /\ ( b c C f g ) ) /\ ( a d C e h ) ) /\ ( c d C g h ) ) ) $.

${
    ifsc-intro.1 $e |- ( ph -> ( B a b c ) ) $.
    ifsc-intro.2 $e |- ( ph -> ( B e f g ) ) $.
    ifsc-intro.3 $e |- ( ph -> ( a c C e g ) ) $.
    ifsc-intro.4 $e |- ( ph -> ( b c C f g ) ) $.
    ifsc-intro.5 $e |- ( ph -> ( a d C e h ) ) $.
    ifsc-intro.6 $e |- ( ph -> ( c d C g h ) ) $.
    $( Introduce the Inner-Five-Segment-Congruence predicate $)
    ifsc-intro
        $p |- ( ph -> IFSC ( a b c d e f g h ) )
        $= ( wffbetw wa wffcong wffifsc jca df-ifsc sylibr ) ABCDPZFGHPZQZBDFHRZQZCDGHRZQZBEFIRZQZDEHIRZQBCDEFG HISAUKULAUIUJAUGUHAUEUFAUCUDJKTLTMTNTOTBCDEFGHIUAU B $.
$}

${
    $( The Inner-Five-Segment-Congruence predicate implies its first conjunct. $)
    ifsc1
        $p |- ( IFSC ( a b c d e f g h ) -> ( B a b c ) )
        $= ( wffifsc wffbetw wa wffcong df-ifsc simp-5l sylbi ) ABCDEFGHIABCJZEFGJZKACEGLZKBCFGLZKADEHLZKCDGHLZKPA BCDEFGHMPQRSTUANO $.
$}

${
    $( The Inner-Five-Segment-Congruence predicate implies its second conjunct. $)
    ifsc2
        $p |- ( IFSC ( a b c d e f g h ) -> ( B e f g ) )
        $= ( wffifsc wffbetw wa wffcong df-ifsc simp-5r sylbi ) ABCDEFGHIABCJZEFGJZKACEGLZKBCFGLZKADEHLZKCDGHLZKQA BCDEFGHMPQRSTUANO $.
$}

${
    $( The Inner-Five-Segment-Congruence predicate implies its third conjunct. $)
    ifsc3
        $p |- ( IFSC ( a b c d e f g h ) -> ( a c C e g ) )
        $= ( wffifsc wffbetw wa wffcong df-ifsc simp-4r sylbi ) ABCDEFGHIABCJEFGJKZACEGLZKBCFGLZKADEHLZKCDGHLZKQAB CDEFGHMPQRSTNO $.
$}

${
    $( The Inner-Five-Segment-Congruence predicate implies its fourth conjunct. $)
    ifsc4
        $p |- ( IFSC ( a b c d e f g h ) -> ( b c C f g ) )
        $= ( wffifsc wffbetw wa wffcong df-ifsc simpllr sylbi ) ABCDEFGHIABCJEFGJKACEGLKZBCFGLZKADEHLZKCDGHLZKQABC DEFGHMPQRSNO $.
$}

${
    $( The Inner-Five-Segment-Congruence predicate implies its fifth conjunct. $)
    ifsc5
        $p |- ( IFSC ( a b c d e f g h ) -> ( a d C e h ) )
        $= ( wffifsc wffbetw wa wffcong df-ifsc simplr sylbi ) ABCDEFGHIABCJEFGJKACEGLKBCFGLKZADEHLZKCDGHLZKQABCD EFGHMPQRNO $.
$}

${
    $( The Inner-Five-Segment-Congruence predicate implies its sixth conjunct. $)
    ifsc6
        $p |- ( IFSC ( a b c d e f g h ) -> ( c d C g h ) )
        $= ( wffifsc wffbetw wa wffcong df-ifsc simprbi )( a c C d f ) ABCDEFGHIABCJEFGJKACEGLKBCFGLKADEHLKCDGHLABCDEFGHM N $.
$}

${
    $( Lemma for Theorem 4.2. Shows 4.2 holds when a = c. $)
    ifsccongeq
        $p |- ( a = c -> ( IFSC ( a b c d e f g h ) -> ( b d C f h ) ) )
        $= ( weq wffifsc wffcong ifsc6 wa wi wffbetw ifsc1 ax-predB1 ax-A6 syl6 syl5 ifsc4 ax-predC2 cong-nullseg-sym syli equcomi jcad ax-predC3 ax-predC1 sylan9 mpdi ) ACIZABCDEFGHJZCDGHKZBDFHKZABCDEFGHLUKULGFIZCBIZMUM UNNUKULUOUPUKULFGIZUOULUKUPUQULABCOZUKUPABCDEFGHPU KURCBCOUPACBCQCBRSTZULBCFGKZUPUQABCDEFGHUAUPUTBBFG KUQCBBFGUBFGBUCSTUDFGUESUSUFUOUMCDFHKUPUNGFCDHUGCB DFHUHUISUJ $.
$}

${
    $d a x y $.
    $d b x y $.
    $d c x y $.
    $d d x y $.
    $d e x y $.
    $d f x y $.
    $d g x y $.
    $d h x y $.
    ifsccongneq
        $p |- ( -. a = c -> ( IFSC ( a b c d e f g h ) -> ( b d C f h ) ) )
        $= ( wffifsc weq wn wffcong vx wffbetw wa wi vy simprrr ifsc4 cong-2143 syl adantr jca pm2.21 a1i ax-predC2 cong-nullseg-sym syl6 impd a1dd jcad equcomi ifsc6 ax-predC1 ax-predC3 sylan9 syl5 ancoms sylan2 a1ddd imp4a jad mpi expcomd expd pm3.41 syl8 pm3.21 anim1d wffofsc ifsc1 ad2antrr simprrl betw-241-sym ifsc2 simprll ax-a2-sym cong-sym-d ad2ant2l adantl ifsc3 ifsc5 ofsc-intro-d ax-A5-alt sylan expcom syl9 ex com3r pm2.61i ax-A4 exlimiiv ) ABCDEFGHIZACJKZBDFHLZACMNZCMBCLZOZWMWNOZWOPZMEGQNZ GQBCLZOZWRWTPZQMCJZXCXDPXEXCWRWMWOPZWTXEXCWRXFXEWM XCWROZWOXEWMXGOZWQCBGFLZOZPXHWOPZXHWQXIWMXCWPWQRWM XIXGWMBCFGLXIABCDEFGHSBCFGTUAZUBUCXEXHXJXKXHKXKPXE XHWOUDUEXEXJWMXGWOXEXJWMXGWOXEXJGFJZBCJZOXFXEXJXMX NXEWQXIXMXEWQXNXIXMPXEWQCCBCLXNMCCBCUFBCCUGUHZXNXI CCGFLXMBCCGFUFGFCUGUHUHUIXEWQXIXNXEWQXNXIXOUJUIUKX NXMCBJZXFBCULXPXMXFWMCDGHLZXPXMOWOABCDEFGHUMZXPXQB DGHLXMWOCBDGHUNGFBDHUOUPUQURUSUHUTVAVBVCVDVEWMWNWO VFVGXCWRXEKZWTXCWRXSWTPXGWSXHWNOZXSWOXGWMXHWNXGWMV HVIXTMCBDQGFHVJZXSWOXTMCBDQGFHXTABCNZWPOMCBNXTYBWP WMYBXGWNABCDEFGHVKVLXHWPWNWMXCWPWQVMZUBUCABCMVNUAX TEFGNZXAOQGFNXTYDXAWMYDXGWNABCDEFGHVOVLXHXAWNWMXAX BWRVPZUBUCEFGQVNUAXTCMGQLZMCQGLXHYFWNXGYFWMXBWQYFX AWPXBWQOGQCMBCGQCMVQVRVSVTZUBCMGQTUAWMXIXGWNXLVLXH ACMDEGQHVJWNMDQHLXHACMDEGQHYCYEWMACEGLXGABCDEFGHWA UBYGWMADEHLXGABCDEFGHWBUBWMXQXGXRUBZWCACMDEGQHWDWE XHXQWNYHUBWCYAXSWOMCBDQGFHWDWFUQWGWHWIWJQGBCEWKWLM CBCAWKWLWF $.
$}

ifsc-cong
    $p |- ( IFSC ( a b c d e f g h ) -> ( b d C f h ) )
    $= ( weq wffifsc wffcong wi ifsccongeq ifsccongneq pm2.61i ) ACIABCDEFGHJBDFHKLABCDEFGHMABCDEFGHNO $.

${
    $( Let two line segments be congruent, with a point placed on each segment some set distance from an endpoint. Then the distance from that point to the other endpoint of the segment it lies on is the same for both segments. Theorem 4.3 of [SST] $)
    segment-subtraction
        $p |- ( ( ( ( ( B a b c ) /\ ( B e f g ) ) /\ ( a c C e g ) ) /\ ( b c C f g ) ) -> ( a b C e f ) )
        $= ( wffbetw wa wffcong wffifsc cong-2143 cong-nullseg jctir ad2antlr ancli pm3.22 an12s df-ifsc biimpri 3syl ifsc-cong ) ABCGDEFGHZACDFIZHBCEFIZHZABCADEFDJZBAEDIABDEIUEUEC AFDIZAADDIZHZHUEUHHZUGHZUFUEUIUCUIUBUDUCUGUHACDFKA DLMNOUGUEUHUKUGUJPQUFUKABCADEFDRSTABCADEFDUABAEDKT $.
$}

${
    betw-cong-equivalence.1 $e |- ( ph -> ( B a b c ) ) $.
    betw-cong-equivalence.2 $e |- ( ph -> ( a b C a c ) ) $.
    betw-cong-equivalence
        $p |- ( ph -> b = c )
        $= ( wffcong weq wffbetw wa betw-sym-d betw-id2 a1i cong-4321 syl jca31 cong-ref jca wi segment-subtraction mpd ax-A3 equcomd ) ADCADCCCGZDCHADCBIZCCBIZJDBCBGZJZCBCBGZJZUDAUHUIAU EUFUGABCDEKUFACBLMABCBDGUGFBCBDNOPUIACBQMRUJUDSADC BCCBTMUADCCUBOUC $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Congruence on a series of points
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Declare C3 symbol $)
$c C3 $.

$( Extend wff notation to include three-way congruence $)
wffcong3 $a wff ( a b c C3 d e f ) $.

df-cong3 $a |- ( ( a b c C3 d e f ) <-> ( ( ( a b C d e ) /\ ( b c C e f ) ) /\ ( a c C d f ) ) ) $.

${
    cong3-intro.1 $e |- ( ph -> ( a b C d e ) ) $.
    cong3-intro.2 $e |- ( ph -> ( b c C e f ) ) $.
    cong3-intro.3 $e |- ( ph -> ( a c C d f ) ) $.
    $( Introduces three-way congruence $)
    cong3-intro
        $p |- ( ph -> ( a b c C3 d e f ) )
        $= ( wffcong wa wffcong3 jca df-cong3 sylibr ) ABCEFKZCDFGKZLZBDEGKZLBCDEFGMASTAQRHINJNBCDEFGOP $.
$}

${
    $( Three-way congruence implies its first conjunct. $)
    cong3-elim1
        $p |- ( ( a b c C3 d e f ) -> ( a b C d e ) )
        $= ( wffcong3 wffcong wa df-cong3 biimpi simplld ) ABCDEFGZABDEHZBCEFHZACDFHZMNOIPIABCDEFJKL $.
$}

${
    $( Three-way congruence implies its second conjunct. $)
    cong3-elim2
        $p |- ( ( a b c C3 d e f ) -> ( b c C e f ) )
        $= ( wffcong3 wffcong wa df-cong3 biimpi simplrd ) ABCDEFGZABDEHZBCEFHZACDFHZMNOIPIABCDEFJKL $.
$}

${
    $( Three-way congruence implies its third conjunct. $)
    cong3-elim3
        $p |- ( ( a b c C3 d e f ) -> ( a c C d f ) )
        $= ( wffcong3 wffcong wa df-cong3 biimpi simprd ) ABCDEFGZABDEHBCEFHIZACDFHZMNOIABCDEFJKL $.
$}

cong3-reflexivity
    $p |- ( a b c C3 a b c )
    $= ( wffcong3 wffcong wa cong-ref pm3.2i df-cong3 mpbir ) ABCABCDABABEZBCBCEZFZACACEZFMNKLABGBCGHACGHABCABCI J $.

cong3-sym
    $p |- ( ( a b c C3 d e f ) -> ( d e f C3 a b c ) )
    $= ( wffcong3 cong3-elim1 cong-sym-d cong3-elim2 cong3-elim3 cong3-intro ) ABCDEFGZDEFABCMABDEABCDEFHIMBCEFABCDEFJIMACDFABCDE FKIL $.

${
    cong3-sym-d.1 $e |- ( ph -> ( a b c C3 d e f ) ) $.
    cong3-sym-d
        $p |- ( ph -> ( d e f C3 a b c ) )
        $= ( wffcong3 cong3-sym syl ) ABCDEFGIEFGBCDIHBCDEFGJK $.
$}

cong3-trans
    $p |- ( ( ( a b c C3 d e f ) /\ ( d e f C3 g h i ) ) -> ( a b c C3 g h i ) )
    $= ( wffcong3 wa wffcong cong3-elim1 anim12i cong-trans-d2 cong3-elim2 cong3-elim3 cong3-intro ) ABCDEFJZDEFGHIJZKZABCGHIUAABDEGHSABDELTDEGHLABCDEF MDEFGHIMNOUABCEFHISBCEFLTEFHILABCDEFPDEFGHIPNOUAAC DFGISACDFLTDFGILABCDEFQDEFGHIQNOR $.

${
    cong3-trans-d.1 $e |- ( ph -> ( a b c C3 d e f ) ) $.
    cong3-trans-d.2 $e |- ( ph -> ( d e f C3 g h i ) ) $.
    cong3-trans-d
        $p |- ( ph -> ( a b c C3 g h i ) )
        $= ( wffcong3 cong3-trans syl2anc ) ABCDEFGMEFGHIJMBCDHIJMKLBCDEFGHIJNO $.
$}

cong3-213
    $p |- ( ( a b c C3 d e f ) -> ( b a c C3 e d f ) )
    $= ( wffcong3 wffcong cong3-elim1 cong-2143 syl cong3-elim3 cong3-elim2 cong3-intro ) ABCDEFGZBACEDFOABDEHBAEDHABCDEFIABDEJKABCDEFLABCDE FMN $.

cong3-312
    $p |- ( ( a b c C3 d e f ) -> ( c a b C3 f d e ) )
    $= ( wffcong3 wffcong cong3-elim3 cong-2143 syl cong3-elim1 cong3-elim2 cong3-intro ) ABCDEFGZCABFDEOACDFHCAFDHABCDEFIACDFJKABCDEFLOBCEF HCBFEHABCDEFMBCEFJKN $.

cong3-321
    $p |- ( ( a b c C3 d e f ) -> ( c b a C3 f e d ) )
    $= ( wffcong3 cong3-213 cong3-312 syl ) ABCDEFGBACEDFGCBAFEDGABCDEFHBACEDFIJ $.

cong3-231
    $p |- ( ( a b c C3 d e f ) -> ( b c a C3 e f d ) )
    $= ( wffcong3 cong3-321 cong3-213 syl ) ABCDEFGCBAFEDGBCAEFDGABCDEFHCBAFEDIJ $.

cong3-132
    $p |- ( ( a b c C3 d e f ) -> ( a c b C3 d f e ) )
    $= ( wffcong3 cong3-231 cong3-321 syl ) ABCDEFGBCAEFDGACBDFEGABCDEFHBCAEFDIJ $.

U0imp3cong
    $p |- ( U0 -> ( a b c C3 d e f ) )
    $= ( wffU0 U0impcong cong3-intro ) GABCDEFABDEHBCEFHACDFHI $.

${
    $( Congruent segment division holds in zero dimensions $)
    cong-seg-divU0
        $p |- ( U0 -> E. e ( ( B d e f ) /\ ( a b c C3 d e f ) ) )
        $= ( wffU0 wffbetw wffcong3 wa U0impbetw U0imp3cong jca 19.8ad ) GZDEFHZABCDEFIZJEOPQDEFKABCDEFLMN $.
$}

${
    $d a p q $.
    $d b p q $.
    $d c p q $.
    $d ph e p q $.
    $d d e p q $.
    $d e f p q $.
    cong-seg-divL1-d.1 $e |- ( ph -> ( a c C d f ) ) $.
    cong-seg-divL1-d.2 $e |- ( ph -> ( B a b c ) ) $.
    cong-seg-divL1-d.3 $e |- ( ph -> L1 ) $.
    cong-seg-divL1-d
        $p |- ( ph -> E. e ( ( B d e f ) /\ ( a b c C3 d e f ) ) )
        $= ( pointp wffbetw weq wn wa wex wffcong3 wffL1 uniq3p syl wffcong ax-A4 19.42v pm3.21 wi simprl simprr simpl pointq equcomi con3i adantl ad2antll simprrl betw-sym-d ad2antrl cong-sym-d betw-243 ad2ant2r adantr betw-241 cong-sym ad2antlr segment-addition-d unique-segcond equcomd ax-predB3 sylc ax-predC4 cong3-intro jca anasss an12s ex exlimiiv syl12anc a1i syl5d impd eximdv biimtrrid mpan2i exlimdv mpd ) AGEKLZEKMZNZOZKPZEFGLZBCDEFGQZOZFPZARWIJGEKSTAWHWM KAWHKEFLZEFBCUAZOZFPZWMFEBCKUBWHWQOWHWPOZFPAWMWHWP FUCAWRWLFAWHWPWLAWPWPAOZWHWLAWPUDWHWSWLUEUEAWHWSWL WHWSOWPAWHWLWHWPAUFWHWPAUGWHWSUHKFUILZFUICDUAZOZWP AWHOZOZWLUEUIXBXDWLWPXBXCWLWPXBXCWLWPXBOZXCOZWJWKX FUIGMZEFUILZWJXFGUIXFGUIEBDKWHKEMZNZXEAWGXJWEXIWFK EUJUKULUMXFGEKXEAWEWGUNUOXFBDEGABDEGUAXEWHHUPZUQXE KEUILZXCWNWTXLWOXAKEFUIURUSUTXFBDEUIXFBCDEFUIABCDL XEWHIUPXEXHXCWNWTXHWOXAKEFUIVAUSUTZXEBCEFUAZXCWOXN WNXBEFBCVBVCUTZXECDFUIUAZXCXAXPWPWTFUICDVBUMUTZVDU QVEVFZXMUIGEFVGVHXFBCDEFGXOXFXGXPCDFGUAXRXQUIGCDFV IVHXKVJVKVLVMVNUIFCDKUBVOVPVNVQVRVSVTWAWBWCWD $.
$}

${
    $d a e $.
    $d b e $.
    $d c e $.
    $d d e $.
    $d e f $.
    cong-seg-divL1
        $p |- ( ( L1 /\ ( ( a c C d f ) /\ ( B a b c ) ) ) -> E. e ( ( B d e f ) /\ ( a b c C3 d e f ) ) )
        $= ( wffL1 wffcong wffbetw wa simprl simprr simpl cong-seg-divL1-d ) GZACDFHZABCIZJZJABCDEFOPQKOPQLORMN $.
$}

${
    $d a e $.
    $d b e $.
    $d c e $.
    $d d e $.
    $d e f $.
    cong-seg-div
        $p |- ( ( ( a c C d f ) /\ ( B a b c ) ) -> E. e ( ( B d e f ) /\ ( a b c C3 d e f ) ) )
        $= ( wffU0 wffL1 wo wffcong wffbetw wa wffcong3 wex U0orL1 cong-seg-divU0 adantr cong-seg-divL1 jaoian mpan ) GZHZIACDFJABCKLZDEFKABCDEFMLENZOUAUCUDUBUAUDUCABCD EFPQABCDEFRST $.
$}

${
    $d a e $.
    $d b e $.
    $d c e $.
    $d d e $.
    $d e f $.
    cong-seg-div-d.1 $e |- ( ph -> ( a c C d f ) ) $.
    cong-seg-div-d.2 $e |- ( ph -> ( B a b c ) ) $.
    cong-seg-div-d
        $p |- ( ph -> E. e ( ( B d e f ) /\ ( a b c C3 d e f ) ) )
        $= ( wffcong wffbetw wffcong3 wa wex cong-seg-div syl2anc ) ABDEGJBCDKEFGKBCDEFGLMFNHIBCDEFGOP $.
$}

${
    betw-preserved-Ed.2 $e |- ( ph -> ( a b c C3 d e f ) ) $.
    betw-preserved-Ed.3 $e |- ( ph -> ( ( B d x f ) /\ ( a b c C3 d x f ) ) ) $.
    $( Betweenness is preserved across congruence of series of points. Theorem 4.6 of [SST]. ( Implied Existential / Deductive form ) $)
    betw-preserved-Ed
        $p |- ( ph -> ( B d e f ) )
        $= ( weq wffbetw wffifsc wffcong wffcong3 simpld cong-ref a1i cong3-sym-d simprd cong3-trans-d cong3-elim1 syl cong3-elim2 cong-2143 ifsc-intro ifsc-cong cong-nullseg-sym 3syl ax-predB2 sylc ) ABGKZFBHLZFGHLAFBHBFBHGMBBBGNULAFBHBFBHGAUMCDEFBHO ZJPZUOFHFHNAFHQRBHBHNABHQRAFBHFGHOZFBFGNAFGHFBHAFG HCDEFBHACDEFGHISAUMUNJTUASZFBHFGHUBUCABHGHNZHBHGNA UPURUQFBHFGHUDUCBHGHUEUCUFFBHBFBHGUGBGBUHUIUOBGFHU JUK $.
$}

${
    $d ph x $.
    $d a x $.
    $d b x $.
    $d c x $.
    $d d x $.
    $d e x $.
    $d f x $.
    betw-preserved-d.2 $e |- ( ph -> ( B a b c ) ) $.
    betw-preserved-d.1 $e |- ( ph -> ( a b c C3 d e f ) ) $.
    $( Betweenness is preserved across congruence of series of points. Theorem 4.6 of [SST]. ( Deductive form ) $)
    betw-preserved-d
        $p |- ( ph -> ( B d e f ) )
        $= ( vx wffbetw wffcong3 wa wffcong cong3-elim3 syl cong-seg-div-d adantr simpr betw-preserved-Ed exlimddv ) AEJGKBCDEJGLMZEFGKJABCDEJGABCDEFGLZBDEGNIBCDEFGOPH QAUBMJBCDEFGAUCUBIRAUBSTUA $.
$}

betw-preserved
    $p |- ( ( ( B a b c ) /\ ( a b c C3 d e f ) ) -> ( B d e f ) )
    $= ( wffbetw wffcong3 wa simpl simpr betw-preserved-d ) ABCGZABCDEFHZIABCDEFMNJMNKL $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Colinearity
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Declare Col symbol $)
$c Col $.

$( Extend wff notation to include Colinearity $)
wffcol $a wff Col ( a b c ) $.

df-col $a |- ( Col ( a b c ) <-> ( ( B a b c ) \/ ( ( B b c a ) \/ ( B c a b ) ) ) ) $.

col-elim
    $p |- ( Col ( a b c ) -> ( ( B a b c ) \/ ( ( B b c a ) \/ ( B c a b ) ) ) )
    $= ( wffcol wffbetw wo df-col biimpi ) ABCDABCEBCAECABEFFABCGH $.

col-intro
    $p |- ( ( ( B a b c ) \/ ( ( B b c a ) \/ ( B c a b ) ) ) -> Col ( a b c ) )
    $= ( wffcol wffbetw wo df-col biimpri ) ABCDABCEBCAECABEFFABCGH $.

${
    col-intro-1-d.1 $e |- ( ph -> ( B a b c ) ) $.
    col-intro-1-d
        $p |- ( ph -> Col ( a b c ) )
        $= ( wffbetw wo wffcol orcd col-intro syl ) ABCDFZCDBFDBCFGZGBCDHALMEIBCDJK $.
$}

${
    col-intro-2-d.1 $e |- ( ph -> ( B b c a ) ) $.
    col-intro-2-d
        $p |- ( ph -> Col ( a b c ) )
        $= ( wffbetw wo wffcol orcd olcd col-intro syl ) ABCDFZCDBFZDBCFZGZGBCDHAPMANOEIJBCDKL $.
$}

${
    col-intro-3-d.1 $e |- ( ph -> ( B c a b ) ) $.
    col-intro-3-d
        $p |- ( ph -> Col ( a b c ) )
        $= ( wffbetw wo wffcol olcd col-intro syl ) ABCDFZCDBFZDBCFZGZGBCDHAOLANMEIIBCDJK $.
$}

${
    $( Permutation of colinearity $)
    col-231
        $p |- ( Col ( a b c ) -> Col ( b c a ) )
        $= ( wffcol wffbetw wo df-col biimpi pm1.5syl pm2.3syl biimpri syl ) ABCDZBCAEZCABEZABCEZFFZBCADZMNPOMPNOMPNOFFABCGHIJR QBCAGKL $.
$}

${
    $( Permutation of colinearity $)
    col-312
        $p |- ( Col ( a b c ) -> Col ( c a b ) )
        $= ( wffcol col-231 syl ) ABCDBCADCABDABCEBCAEF $.
$}

${
    $( Permutation of colinearity $)
    col-321
        $p |- ( Col ( a b c ) -> Col ( c b a ) )
        $= ( wffcol wffbetw wo df-col biimpi betw-sym orim1i syl pm2.3syl orim12i orim2i sylibr ) ABCDZCBAEZBACEZACBEZFZFZCBADPQCABEZBCAEZFZFUAPQUCU BPABCEZUCUBFZFZQUFFPUGABCGHUEQUFABCIJKLUDTQUBRUCSC ABIBCAIMNKCBAGO $.
$}

${
    $( Permutation of colinearity $)
    col-213
        $p |- ( Col ( a b c ) -> Col ( b a c ) )
        $= ( wffcol col-312 col-321 syl ) ABCDCABDBACDABCECABFG $.
$}

${
    $( Permutation of colinearity $)
    col-132
        $p |- ( Col ( a b c ) -> Col ( a c b ) )
        $= ( wffcol col-231 col-321 syl ) ABCDBCADACBDABCEBCAFG $.
$}

${
    $( Theorem 4.12 of [SST] $)
    col-id
        $p |- Col ( a a b )
        $= ( wffbetw wo wffcol betw-id2 orci col-intro ax-mp ) AABCZABACBAACDZDAABEJKABFGAABHI $.
$}

${
    $( Colinearity is preserved across congruence of series of points. Theorem 4.13 of [SST]. $)
    col-preserved
        $p |- ( ( Col ( a b c ) /\ ( a b c C3 d e f ) ) -> Col ( d e f ) )
        $= ( wffbetw wo wffcong3 wa wffcol betw-preserved cong3-231 sylan2 cong3-312 disimp2intro df-col anbi1i 3imtr4i ) ABCGZBCAGZCABGZHZHZABCDEFIZJDEFGZEFDGZFDEGZHZHABCK ZUEJDEFKTUEUCUFUIABCDEFLUAUEUBUGUHUEUABCAEFDIUGABC DEFMBCAEFDLNUEUBCABFDEIUHABCDEFOCABFDELNPPUJUDUEAB CQRDEFQS $.
$}

${
    $d a f $.
    $d b f $.
    $d c f $.
    $d d f $.
    $d e f $.
    $( Lemma for col-seg-div in the case Babc $)
    l1-col-seg-div
        $p |- ( ( ( B a b c ) /\ ( a b C d e ) ) -> E. f ( a b c C3 d e f ) )
        $= ( wffbetw wffcong wa wffcong3 wi ax-A4 cong-sym anim2i eximii simplr simprr segment-addition anasss an4s jca31 df-cong3 sylibr expcom 19.37iv ) ABCGZABDEHZIZABCDEFJZFDEFGZBCEFHZIZUHUIKFUJEFBCHZI ULFFEBCDLUMUKUJEFBCMNOUHULUIUHULIZUGUKIACDFHZIUIUN UGUKUOUFUGULPUHUJUKQUFUJUGUKUOUFUJIUGUKUOABCDEFRST UAABCDEFUBUCUDOUE $.
$}

${
    $d a f $.
    $d b f $.
    $d c f $.
    $d d f $.
    $d e f $.
    $( Lemma for col-seg-div in the case Bbac $)
    l2-col-seg-div
        $p |- ( ( ( B b a c ) /\ ( a b C d e ) ) -> E. f ( a b c C3 d e f ) )
        $= ( wffbetw wffcong wa wffcong3 wex cong-2143 l1-col-seg-div sylan2 cong3-213 eximi syl ) BACGZABDEHZIBACEDFJZFKZABCDEFJZFKSRBAEDHUAABDELBAC EDFMNTUBFBACEDFOPQ $.
$}

${
    $d a f $.
    $d b f $.
    $d c f $.
    $d d f $.
    $d e f $.
    $( Lemma for col-seg-div in the case Bacb $)
    l3-col-seg-div
        $p |- ( ( ( B a c b ) /\ ( a b C d e ) ) -> E. f ( a b c C3 d e f ) )
        $= ( wffbetw wffcong wa wffcong3 wex cong-seg-div ancoms exsimpr syl cong3-132 eximi ) ACBGZABDEHZIZACBDFEJZFKZABCDEFJZFKTDFEGZUAIFKZUBSR UEACBDFELMUDUAFNOUAUCFACBDFEPQO $.
$}

${
    $d a f $.
    $d b f $.
    $d c f $.
    $d d f $.
    $d e f $.
    $( Similar to segment division, including outpoints. Theorem 4.14 of [SST] $)
    col-seg-div
        $p |- ( ( Col ( a b c ) /\ ( a b C d e ) ) -> E. f ( a b c C3 d e f ) )
        $= ( wffcol wffbetw wo wffcong wffcong3 wex col-elim l1-col-seg-div betw-sym l3-col-seg-div sylan l2-col-seg-div jaoian ) ABCGABCHZBCAHZCABHZIZIABDEJZABCDEFKFLZABCMTUDUEUCA BCDEFNUAUDUEUBUAACBHUDUEBCAOABCDEFPQUBBACHUDUECABO ABCDEFRQSSQ $.
$}

$( Declare Five-Segment configuration symbol $)
$c FSC $.

$( Extend wff notation to include five-segment configuration $)
wfffsc $a wff FSC ( a b c d e f g h ) $.

df-fsc $a |- ( C ( a b c d e f g h ) <-> ( ( ( Col ( a b c ) /\ ( a b c C3 e f g ) ) /\ ( a d C e h ) ) /\ ( b d C f h ) ) ) $.

${
    fs-intro.1 $e |- ( ph -> Col ( a b c ) ) $.
    fs-intro.2 $e |- ( ph -> ( a b c C3 e f g ) ) $.
    fs-intro.3 $e |- ( ph -> ( a d C e h ) ) $.
    fs-intro.4 $e |- ( ph -> ( b d C f h ) ) $.
    fs-intro
        $p |- ( ph -> FSC ( a b c d e f g h ) )
        $= ( wffcol wffcong3 wa wffcong wfffsc jca df-fsc syl21anbrc ) ABCDNZBCDFGHOZPBEFIQCEGIQBCDEFGHIRAUBUCJKSLMBCDEFG HITUA $.
$}

${
    fs-cong-d.3 $e |- ( ph -> ( B a c b ) ) $.
    fs-cong-d.1 $e |- ( ph -> ( a b c C3 e f g ) ) $.
    fs-cong-d.4 $e |- ( ph -> ( a d C e h ) ) $.
    fs-cong-d.5 $e |- ( ph -> ( b d C f h ) ) $.
    $( Lemma for fs-cong in the case Bacb $)
    l1-fs-cong-d
        $p |- ( ph -> ( c d C g h ) )
        $= ( wffifsc wffcong wffbetw wffcong3 wa cong3-132 syl jca betw-preserved cong3-elim1 cong3-elim2 cong-2143 ifsc-intro ifsc-cong ) ABDCEFHGINDEHIOABDCEFHGIJABDCPZBDCFHGQZRFHGPAUHUIJ ABCDFGHQZUIKBCDFGHSTUABDCFHGUBTAUJBCFGOKBCDFGHUCTA CDGHOZDCHGOAUJUKKBCDFGHUDTCDGHUETLMUFBDCEFHGIUGT $.
$}

${
    fs-cong-d.3 $e |- ( ph -> ( B a b c ) ) $.
    fs-cong-d.1 $e |- ( ph -> ( a b c C3 e f g ) ) $.
    fs-cong-d.4 $e |- ( ph -> ( a d C e h ) ) $.
    fs-cong-d.5 $e |- ( ph -> ( b d C f h ) ) $.
    fs-cong-d.2 $e |- ( ph -> -. a = b ) $.
    $( Lemma for fs-cong in the case Babc $)
    l2-fs-cong-d
        $p |- ( ph -> ( c d C g h ) )
        $= ( wffofsc weq wn wffcong betw-preserved-d wffcong3 cong3-elim1 syl cong3-elim2 ofsc-intro-d ax-A5-alt syl2anc ) ABCDEFGHIOBCPQDEHIRABCDEFGHIJABCDFGHJKSABCDFGHTZBC FGRKBCDFGHUAUBAUGCDGHRKBCDFGHUCUBLMUDNBCDEFGHIUEUF $.
$}

${
    fs-cong-d.3 $e |- ( ph -> ( B c a b ) ) $.
    fs-cong-d.1 $e |- ( ph -> ( a b c C3 e f g ) ) $.
    fs-cong-d.4 $e |- ( ph -> ( a d C e h ) ) $.
    fs-cong-d.5 $e |- ( ph -> ( b d C f h ) ) $.
    fs-cong-d.2 $e |- ( ph -> -. a = b ) $.
    $( Lemma for fs-cong in the case Bcab $)
    l3-fs-cong-d
        $p |- ( ph -> ( c d C g h ) )
        $= ( wffofsc weq wn wffcong betw-sym-d wffcong3 cong3-312 syl betw-preserved-d cong3-elim1 cong-2143 cong3-elim3 ofsc-intro-d equcomi nsyl ax-A5-alt syl2anc ) ACBDEGFHIOCBPZQDEHIRACBDEGFHIADBCJSAHFGADBCHFGJABC DFGHTZDBCHFGTKBCDFGHUAUBUCSABCFGRZCBGFRAUMUNKBCDFG HUDUBBCFGUEUBAUMBDFHRKBCDFGHUFUBMLUGABCPULNCBUHUIC BDEGFHIUJUK $.
$}

${
    fs-cong-d.3 $e |- ( ph -> Col ( a b c ) ) $.
    fs-cong-d.1 $e |- ( ph -> ( a b c C3 e f g ) ) $.
    fs-cong-d.4 $e |- ( ph -> ( a d C e h ) ) $.
    fs-cong-d.5 $e |- ( ph -> ( b d C f h ) ) $.
    fs-cong-d.2 $e |- ( ph -> -. a = b ) $.
    fs-cong-d
        $p |- ( ph -> ( c d C g h ) )
        $= ( wffcol wffcong wffbetw wo wi col-elim wa simpr wffcong3 adantr l1-fs-cong-d expcom weq wn l2-fs-cong-d a1i betw-sym imim1i l3-fs-cong-d jaod ax-mp syl mpcom ) BCDOZADEHIPZJURBCDQZCDBQZDBCQZRZRZAUSSZBCDTBDCQZVE SZVDVESAVFUSAVFUABCDEFGHIAVFUBABCDFGHUCZVFKUDABEFI PZVFLUDACEGIPZVFMUDUEUFVGUTVEVCUTVESVGAUTUSAUTUABC DEFGHIAUTUBAVHUTKUDAVIUTLUDAVJUTMUDABCUGUHZUTNUDUI UFUJVGVAVEVBVAVFVECDBUKULVBVESVGAVBUSAVBUABCDEFGHI AVBUBAVHVBKUDAVIVBLUDAVJVBMUDAVKVBNUDUMUFUJUNUNUOU PUQ $.
$}

${
    $( Five-segment configuration implies congruence. Theorem 4.16 of [SST] $)
    fs-cong
        $p |- ( ( FSC ( a b c d e f g h ) /\ -. a = b ) -> ( c d C g h ) )
        $= ( wfffsc weq wn wa wffcol wffcong3 wffcong df-fsc simp-4l sylanb birani simpllr syl simplrd simprd simpr fs-cong-d ) ABCDEFGHIZABJKZLZABCDEFGHUFABCMZABCEFGNZLZADEHOZLZ BDFHOZLZUGUIABCDEFGHPZUIUJULUNUGQRUHUOUJUFUOUGUPSZ UIUJULUNTUAUHUKULUNUQUBUHUMUNUQUCUFUGUDUE $.
$}

${
    $( If a is equidistant from p and q, and b is equidistant from p and q, all points on the line ab are equidistant from p and q. Theorem 4.17 of [SST]. $)
    line-cong
        $p |- ( ( ( ( -. a = b /\ Col ( a b c ) ) /\ ( a p C a q ) ) /\ ( b p C b q ) ) -> ( c p C c q ) )
        $= ( weq wn wffcol wa wffcong simpllr wffcong3 cong3-reflexivity a1i simplr simpr simplll fs-cong-d ) ABFGZABCHZIZADAEJZIZBDBEJZIZABCDABCESTUBUDKABCABCL UEABCMNUAUBUDOUCUDPSTUBUDQR $.
$}

${
    line-cong-d.1 $e |- ( ph -> -. a = b ) $.
    line-cong-d.2 $e |- ( ph -> Col ( a b c ) ) $.
    line-cong-d.3 $e |- ( ph -> ( a p C a q ) ) $.
    line-cong-d.4 $e |- ( ph -> ( b p C b q ) ) $.
    line-cong-d
        $p |- ( ph -> ( c p C c q ) )
        $= ( weq wn wffcol wa wffcong jca31 jca line-cong syl ) ABCKLZBCDMZNBEBFOZNZCECFOZNDEDFOAUCUDATUAUBGHIPJQB CDEFRS $.
$}

${
    $( A point colinear with distinct points a,b is uniquely determined by its distances from these points. Theorem 4.18 of [SST] $)
    line-distance-uniq
        $p |- ( ( ( ( -. a = b /\ Col ( a b c ) ) /\ ( a c C a d ) ) /\ ( b c C b d ) ) -> c = d )
        $= ( weq wn wffcol wa wffcong line-cong cong-nullseg-sym syl ) ABEFABCGHACADIHBCBDIHCCCDICDEABCCDJCDCKL $.
$}

${
    $( Corollary of line-distance-uniq without the restriction that a and b must be distinct. Theorem 4.19 of [SST] $)
    distance-uniq-corollary
        $p |- ( ( ( ( B b c a ) /\ ( a c C a d ) ) /\ ( b c C b d ) ) -> c = d )
        $= ( weq wffbetw wffcong wa wi pm3.2 anim1d ax-predB1 equcoms imp ax-A6 equcomd syl ax-predC2 cong-nullseg-sym syl6 adantr ad2antrr equtrr sylc wn wo orc olcd anim2i wffcol df-col anbi2i anbi1i line-distance-uniq sylanbr sylanl1 pm2.61i ) ABEZBCAFZACADGZHZBCBDGZHZCDEZIURVCURUSHZUTHZVBHZVD URVAVFVBURUSVEUTURUSJKKVGADEZCAEZVDVFVHVBVEUTVHVEU TAAADGZVHVEVIUTVJIVEACAFZVIURUSVKUSVKIBABACALMNVKA CACOPQZCAAADRQADASTNUAVEVIUTVBVLUBADCUCUDTURUEZVCV MUSHZUTHZVBHVDVMVAVOVBVMUSVNUTVMUSJKKVNVMABCFZUSCA BFZUFZUFZHZUTVBVDUSVSVMUSVRVPUSVQUGUHUIVTUTHVMABCU JZHZUTHVBVDWBVTUTWAVSVMABCUKULUMABCDUNUOUPTUQ $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Connectivity of betweenness
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

${
    l1-connectivity-between.1 $e |- ( ph -> ( B a b c ) ) $.
    l1-connectivity-between.2 $e |- ( ph -> ( B a b d ) ) $.
    l1-connectivity-between.3 $e |- ( ph -> ( B a d e ) ) $.
    l1-connectivity-between.4 $e |- ( ph -> ( B a c f ) ) $.
    l1-connectivity-between.5 $e |- ( ph -> ( B a e h ) ) $.
    l1-connectivity-between.6 $e |- ( ph -> ( B a f j ) ) $.
    l1-connectivity-between.7 $e |- ( ph -> ( e d C c d ) ) $.
    l1-connectivity-between.8 $e |- ( ph -> ( c f C c d ) ) $.
    l1-connectivity-between.9 $e |- ( ph -> ( e h C b c ) ) $.
    l1-connectivity-between.10 $e |- ( ph -> ( f j C b d ) ) $.
    l1-connectivity-between.11 $e |- ( ph -> -. a = b ) $.
    $( The first lemma for connectivity of betweenness. $)
    l1-connectivity-between
        $p |- ( ph -> h = j )
        $= ( betw-243-d betw-241-d betw-sym-d cong-lhs-d cong-sym-d cong-trans-d cong-4312-d segment-addition-d wffcong cong-ref a1i unique-segcond ) AHICCIBTABCFHNABCEFLKUAZUAAHCCIAHFCCDIACFHABCFHUMN UBUCABCDIJABDGIOMUAZUBAFHCDRUDAFECDGIACEFABCEFKLUB UCABDGIMOUBAFEDEDGPADGDEQUEUFAGICESUGUHUHUDABCDIUN JUACICIUIACIUJUKUL $.
$}

${
    l2-connectivity-between.1 $e |- ( ph -> ( B a b c ) ) $.
    l2-connectivity-between.2 $e |- ( ph -> ( B a b d ) ) $.
    l2-connectivity-between.3 $e |- ( ph -> ( B a d e ) ) $.
    l2-connectivity-between.4 $e |- ( ph -> ( B a c f ) ) $.
    l2-connectivity-between.5 $e |- ( ph -> ( B a e h ) ) $.
    l2-connectivity-between.6 $e |- ( ph -> ( B a f j ) ) $.
    l2-connectivity-between.7 $e |- ( ph -> ( e d C c d ) ) $.
    l2-connectivity-between.8 $e |- ( ph -> ( c f C c d ) ) $.
    l2-connectivity-between.9 $e |- ( ph -> ( e h C b c ) ) $.
    l2-connectivity-between.10 $e |- ( ph -> ( f j C b d ) ) $.
    l2-connectivity-between.11 $e |- ( ph -> -. a = b ) $.
    $( The second lemma for connectivity of betweenness. Establish OFSC, then cases for point decidability of B and C. $)
    l2-connectivity-between
        $p |- ( ph -> ( f e C c d ) )
        $= ( weq wffcong wa ax-predC3 mpan9 ax-A3 syl betw-243-d betw-241-d betw-sym-d cong-lhs-d cong-sym-d cong-trans-d cong-4312-d segment-addition-d cong-ref a1i unique-segcond adantr equtr sylc equcomd ax-predC2 wn wffofsc betw-241-sym-d wi pm2.21 equcomi cong-2143-d imim1i imim12i jad mp2 ax-A1 ofsc-intro-d ax-A5-alt sylan cong-rhs pm2.61dan ) ACDUAZGFDEUBZAWAUCZIFUAGIDEUBZWBWCFIWCFHUAZHIUAZFI UAWCFHDDUBZWEAFHCDUBWAWGRCDFHDUDUEFHDUFUGAWFWAAHIC CIBTABCFHNABCEFLKUHZUHAHCCIAHFCCDIACFHABCFHWHNUIUJ ABCDIJABDGIOMUHZUIAFHCDRUKZAFECDGIACEFABCEFKLUIUJA BDGIMOUIAFEDEDGPADGDEQULUMZAGICESUNUOZUOUKABCDIWIJ UHCICIUBACIUPUQURZUSFHIUTVAVBAGICEUBWAWDSCDGIEUDUE IFGDEVCVAAWAVDZUCGFEDUBZWBACDGFHFEDVEWNWOACDGFHFED ABCDGJMUIABEFHLNVFAHFCDWJULAFEDGWKULIHUAZCFIDUBZCF HDUBZVGZVGZAWFVGAWRVGZIHCFDUDWMWTAWFXAAVDXAVGWTAWR VHUQWFWPWSXAHIVIAWQWRAFCDIWLVJVKVLVMVNDFFDUBADFVOU QVPCDGFHFEDVQVRGFEDVSUGVT $.
$}

${
    l3-connectivity-between.7 $e |- ( ph -> ( e d C c d ) ) $.
    l3-connectivity-between.1 $e |- ( ph -> ( B a b c ) ) $.
    l3-connectivity-between.2 $e |- ( ph -> ( B a b d ) ) $.
    l3-connectivity-between.3 $e |- ( ph -> ( B a d e ) ) $.
    l3-connectivity-between.4 $e |- ( ph -> ( B a c f ) ) $.
    l3-connectivity-between.5 $e |- ( ph -> ( B a e h ) ) $.
    l3-connectivity-between.6 $e |- ( ph -> ( B a f j ) ) $.
    l3-connectivity-between.12 $e |- ( ph -> ( B c x e ) ) $.
    l3-connectivity-between.13 $e |- ( ph -> ( B d x f ) ) $.
    l3-connectivity-between.8 $e |- ( ph -> ( c f C c d ) ) $.
    l3-connectivity-between.9 $e |- ( ph -> ( e h C b c ) ) $.
    l3-connectivity-between.10 $e |- ( ph -> ( f j C b d ) ) $.
    l3-connectivity-between.11 $e |- ( ph -> -. a = b ) $.
    l3-connectivity-between.14 $e |- ( ph -> ( B e c p ) ) $.
    l3-connectivity-between.15 $e |- ( ph -> ( B f c r ) ) $.
    l3-connectivity-between.16 $e |- ( ph -> ( B p r q ) ) $.
    l3-connectivity-between.17 $e |- ( ph -> ( c p C c f ) ) $.
    l3-connectivity-between.18 $e |- ( ph -> ( c r C c x ) ) $.
    l3-connectivity-between.19 $e |- ( ph -> ( r q C r p ) ) $.
    l3-connectivity-between.20 $e |- ( ph -> -. c = e ) $.
    $( The third lemma for connectivity of betweenness. $)
    l3-connectivity-between
        $p |- ( ph -> f = d )
        $= ( wffcong weq betw-sym-d col-intro-3-d cong-trans-d wa wi ax-predC3 equcomi adantl wffifsc cong-ref a1i cong-sym-d l2-connectivity-between cong-lhs-d ax-a2-sym syl2anc ifsc-intro ifsc-cong syl adantr ax-A3 embantd mpi equtr mpd wffofsc wn wffbetw betw-134 cong-4321 ax-A1 ofsc-intro-d ax-predC2 mpan9 cong-nullseg-sym mtand nsyl ax-A5-alt ax-predC1 ax-predC4 sylc cong-sym 3syl sylan pm2.61dan betw-241-d l1-connectivity-between equcomd ax-predB3 betw-142-d ax-predB1 ax-A6 wffcol betw-243-d col-intro-1-d col-132 line-cong-d segment-addition-d ) ALLHFUNHFUOZAHFLLAKLUOZHFKLUNHFLLUNAKKKLUNXOAEGKKL UMAEGKAGEKUGUPZUQAEKEFUNELEFUNZEKELUNAEKEHEFUJUCUR AFELEUNZXQAHBUOZXRAXSUSZXQXRXTXNELEHUNZXQXTBFUOZXN XTBHUOZBFBHUNZBFHHUNZUTZUTYBBHBFHVAXTYCYFYBXSYCAHB VBVCXTYDYEYBAYDXSAEBGFEBGHVDYDAEBGFEBGHUAUAEGEGUNA EGVEVFBGBGUNABGVEVFAEHEFUCVGAGFEFUNZGHEFUNGFGHUNNA HGEFACDEFGHIJOPQRSTNUCUDUEUFVHZVIEFGFGHVJVKVLEBGFE BGHVMVNZVOYEYBUTXTBFHVPVFVQVQVRXSYBXNUTAHBFVSVCVTX TXOEKEHUNZYAXTKMUOZMLUOZXOXTBBKMUNZYKAHBKMUNZXSYMA MKBHUNZYNAHEMKKEBHWAHEUOZWBYOAHEMKKEBHUHAKEGWCEBGW CKEBWCXPUAKEBGWDVKAYJHEKEUNUJEKEHWEVNZUKHKKHUNAHKW FVFUJWGAEHUOZYPAYREGUOZUMAYRUSZHGUOZYSYTHHHGUNZUUA AHEHGUNZYRUUBAHEEFUNHGEFUNUUCAEHEFUCVIYHEFHEHGVJVK ZEHHHGWHWIHGHWJVNYRUUAYSUTAEHGVSVCVTWKZHEVBWLZHEMK KEBHWMVKZMKBHWEVNZHBBKMWNWIKMBWJVNZXTMLMMUNZMMMLUN YLXTYKMLMKUNZUUJUUIAUUKXSULVOKMMLMWOWPMLMMWQMLMWJW RKMLVSWPAYJXSUJVOKLEEHWHWPHFELEWOWPELEFWEVNAHBFEKM LEWAXSWBXRAHBFEKMLEAFBHUBUPZUIUUHABFBHMLYIABHMKUNU UKBHMLUNAMKBHUUGVGULMKBHMLVJVKURZYQAEMEBUNZBEMEUNU KEMEBWEVNWGHBFEKMLEWMWSWTFELEWEVNEFEKELVJVKZADIGKL ADIUOZYPUUFAUUPUSZHEHWCZYPUUQDHUOZDEHWCZUURUUQIHUO ZUUSUUQIHIWCZUVAADHIWCUUPUVBADEHIACDEHORXAZAJIUOEH JWCEHIWCAIJACDEFGHIJOPQRSTNUCUDUEUFXBXCACEHJRTXAJI EHXDWPZUUEXEDIHIXFWIIHXGVNUUPUVAUUSUTADIHVSVCVTAUU TUUPUVCVODHEHXFWPHEXGVNWKADGIXHDIGXHADGIACDGIACDFG QPXISXAXJDGIXKVNAEHDKLUUEAEHDUVCUQUUOAEMHKLAEMUOZY SUMAUVEUSZEBUOZBGUOZYSUVFMMEBUNZUVGAUUNUVEUVIUKEMM EBWNWIEBMWJVNZUVFBBBGUNZUVHUVFUVGBEBGUNZUVKUVJAUVL UVEAFBHEFBHGVDUVLAFBHEFBHGUBUBFHFHUNAFHVEVFBHBHUNA BHVEVFAYGFEFGUNNGFEFWEVNUUDVLFBHEFBHGVMVNVOEBBBGWH WPBGBWJVNEBGVSWPWKAEMHUHUQUUOAMLMKULVGXLZXLAEHIKLU UEAEHIUVDXJUUOUVMXLXLXLKLKWJVNAHBFKMLUULUIUUHUUMXM KLHFLVAWPVGHFLWJVN $.
$}

${
    1 $e |- ( ph -> ( e d C c d ) ) $.
    2 $e |- ( ph -> ( B a b c ) ) $.
    3 $e |- ( ph -> ( B a b d ) ) $.
    4 $e |- ( ph -> ( B a d e ) ) $.
    5 $e |- ( ph -> ( B a c f ) ) $.
    6 $e |- ( ph -> ( B a e h ) ) $.
    7 $e |- ( ph -> ( B a f j ) ) $.
    8 $e |- ( ph -> ( B c x e ) ) $.
    9 $e |- ( ph -> ( B d x f ) ) $.
    10 $e |- ( ph -> ( c f C c d ) ) $.
    11 $e |- ( ph -> ( e h C b c ) ) $.
    12 $e |- ( ph -> ( f j C b d ) ) $.
    13 $e |- ( ph -> -. a = b ) $.
    14 $e |- ( ph -> ( B e c p ) ) $.
    15 $e |- ( ph -> ( B f c r ) ) $.
    16 $e |- ( ph -> ( B p r q ) ) $.
    17 $e |- ( ph -> ( c p C c f ) ) $.
    18 $e |- ( ph -> ( c r C c x ) ) $.
    19 $e |- ( ph -> ( r q C r p ) ) $.
    l4-connectivity-between
        $p |- ( ph -> ( ( B a c d ) \/ ( B a d c ) ) )
        $= ( weq wn wffbetw wa wffcong adantr simpr l3-connectivity-between ax-predB3 sylc equcomi adantl wo pm2.1 a1i orim12da ) AEGUMZUNZVICEFUOZCFEUOZAVJUPZHFUMCEHUOZVKVMBCDEFGH IJKLMAGFEFUQVJNURACDEUOVJOURACDFUOVJPURACFGUOZVJQU RAVNVJRURZACGIUOVJSURACHJUOVJTURAEBGUOVJUAURAFBHUO VJUBURAEHEFUQVJUCURAGIDEUQVJUDURAHJDFUQVJUEURACDUM UNVJUFURAGEKUOVJUGURAHEMUOVJUHURAKMLUOVJUIURAEKEHU QVJUJURAEMEBUQVJUKURAMLMKUQVJULURAVJUSUTVPHFCEVAVB AVIUPGEUMZVOVLVIVQAEGVCVDAVOVIQURGECFVAVBVJVIVEAVI VFVGVH $.
$}

${
    $d q x $.
    $d e q r $.
    $d f q r $.
    $d ph p q r $.
    $d a p q r $.
    $d c p q r $.
    $d d p q r $.
    1 $e |- ( ph -> ( e d C c d ) ) $.
    2 $e |- ( ph -> ( B a b c ) ) $.
    3 $e |- ( ph -> ( B a b d ) ) $.
    4 $e |- ( ph -> ( B a d e ) ) $.
    5 $e |- ( ph -> ( B a c f ) ) $.
    6 $e |- ( ph -> ( B a e h ) ) $.
    7 $e |- ( ph -> ( B a f j ) ) $.
    8 $e |- ( ph -> ( B c x e ) ) $.
    9 $e |- ( ph -> ( B d x f ) ) $.
    10 $e |- ( ph -> ( c f C c d ) ) $.
    11 $e |- ( ph -> ( e h C b c ) ) $.
    12 $e |- ( ph -> ( f j C b d ) ) $.
    13 $e |- ( ph -> -. a = b ) $.
    l5-connectivity-between
        $p |- ( ph -> ( ( B a c d ) \/ ( B a d c ) ) )
        $= ( pointp wffbetw wffcong wa wo wi pointr pointq pm3.2 anim1d anim2d adantr weq wn simp-4l ancoms simplrl adantl simprrl simp-4r simplrr simprrr l4-connectivity-between syl6 imim1d com12 syl pm3.3 com23 com13 ax-A4 exlimiiv ) GEUDUEZEUDEHUFZUGZACEFUECFEUEUHZUIZUDHEUJUEZEUJEBU FZUGZVRVTUIZUJUDUJUKUEZUJUKUJUDUFZUGZWCWDUIUKVRWCW GVTVRWCAWGUGZVSUIZWGVTUIVRAWCWGUGZUGZVSUIZWCWIUIVR WKAVRWCUGZWGUGZUGZVSVRWJWNAVRWCWMWGVRWCULUMUNWOBCD EFGHIJUDUKUJAGFEFUFWNKUOACDEUEWNLUOACDFUEWNMUOACFG UEWNNUOACEHUEWNOUOACGIUEWNPUOACHJUEWNQUOAEBGUEWNRU OAFBHUEWNSUOAEHEFUFWNTUOAGIDEUFWNUAUOAHJDFUFWNUBUO ACDUPUQWNUCUOWNAVPVPVQWCWGAURUSWNWAAVRWAWBWGUTVAAW MWEWFVBWNAVQVPVQWCWGAVCUSWNWBAVRWAWBWGVDVAAWMWEWFV EVFVGWCWLWIWCWHWKVSWCWGWJAWCWGULUNVHVIVJWIAWGVSAWG VSVKVLVGVMUKUJUJUDUDVNVOUJEEBHVNVOUDEEHGVNVO $.
$}

${
    $d ph x $.
    $d a x $.
    $d c x $.
    $d d x $.
    1 $e |- ( ph -> ( e d C c d ) ) $.
    2 $e |- ( ph -> ( B a b c ) ) $.
    3 $e |- ( ph -> ( B a b d ) ) $.
    4 $e |- ( ph -> ( B a d e ) ) $.
    5 $e |- ( ph -> ( B a c f ) ) $.
    6 $e |- ( ph -> ( B a e h ) ) $.
    7 $e |- ( ph -> ( B a f j ) ) $.
    10 $e |- ( ph -> ( c f C c d ) ) $.
    11 $e |- ( ph -> ( e h C b c ) ) $.
    12 $e |- ( ph -> ( f j C b d ) ) $.
    13 $e |- ( ph -> -. a = b ) $.
    l6-connectivity-between
        $p |- ( ph -> ( ( B a c d ) \/ ( B a d c ) ) )
        $= ( vx wffbetw wa wo wex betw-sym-d ax-A7 syl2anc wffcong adantr simprl simprr weq wn l5-connectivity-between exlimddv ) ADUAFUBZEUAGUBZUCZBDEUBBEDUBUDUAAGDBUBFEBUBUSUAUEA BDGNUFABEFMUFUAGFBDEUGUHAUSUCUABCDEFGHIAFEDEUIUSJU JABCDUBUSKUJABCEUBUSLUJABEFUBUSMUJABDGUBUSNUJABFHU BUSOUJABGIUBUSPUJAUQURUKAUQURULADGDEUIUSQUJAFHCDUI USRUJAGICEUIUSSUJABCUMUNUSTUJUOUP $.
$}

${
    $d b h $.
    $d f h $.
    $d ph h j $.
    $d a h j $.
    $d c h j $.
    $d d h j $.
    1 $e |- ( ph -> ( e d C c d ) ) $.
    2 $e |- ( ph -> ( B a b c ) ) $.
    3 $e |- ( ph -> ( B a b d ) ) $.
    4 $e |- ( ph -> ( B a d e ) ) $.
    5 $e |- ( ph -> ( B a c f ) ) $.
    10 $e |- ( ph -> ( c f C c d ) ) $.
    13 $e |- ( ph -> -. a = b ) $.
    l7-connectivity-between
        $p |- ( ph -> ( ( B a c d ) \/ ( B a d c ) ) )
        $= ( pointj wffbetw wffcong wa wo wi pointh pm3.2 anim2d adantr simprll simprrl simprlr simprrr weq wn l6-connectivity-between syl6 ax-A4 exlimiiv expcom ) BGOPZGOCEQZRZABDEPBEDPSZTOAURUSBFUAPZFUACDQZRZAURR ZUSTUAVBVCAVBURRZRZUSVBURVDAVBURUBUCVEBCDEFGUAOAFE DEQVDHUDABCDPVDIUDABCEPVDJUDABEFPVDKUDABDGPVDLUDAU TVAURUEAVBUPUQUFADGDEQVDMUDAUTVAURUGAVBUPUQUHABCUI UJVDNUDUKULUAFCDBUMUNUOOGCEBUMUN $.
$}

${
    $d ph e f $.
    $d a e f $.
    $d c e f $.
    $d d e f $.
    2 $e |- ( ph -> ( B a b c ) ) $.
    3 $e |- ( ph -> ( B a b d ) ) $.
    13 $e |- ( ph -> -. a = b ) $.
    l8-connectivity-between
        $p |- ( ph -> ( ( B a c d ) \/ ( B a d c ) ) )
        $= ( pointf wffbetw wffcong wa wo wi pointe pm3.2 anim2d simprlr adantr simprll simprrl simprrr weq wn l7-connectivity-between syl6 cong-lhs ax-gen ax-A4 darii exlimiiv expcom ) BDIJZDIDEKZLZABDEJBEDJMZNIAUOUPBEOJZOEDEKZLZAUOLZU PNOUSUTAUSUOLZLZUPUSUOVAAUSUOPQVBBCDEOIAUQURUORABC DJVAFSABCEJVAGSAUQURUOTAUSUMUNUAAUSUMUNUBABCUCUDVA HSUEUFEODEKZURUQOVCURNOEODEUGUHOEDEBUIUJUKULIDDEBU IUK $.
$}

connectivity-between
    $p |- ( ( ( -. a = b /\ ( B a b c ) ) /\ ( B a b d ) ) -> ( ( B a c d ) \/ ( B a d c ) ) )
    $= ( weq wn wffbetw wa simplr simpr simpll l8-connectivity-between ) ABEFZABCGZHZABDGZHABCDMNPIOPJMNPKL $.

connectivity-between-2
    $p |- ( ( ( -. a = b /\ ( B a b c ) ) /\ ( B a b d ) ) -> ( ( B b c d ) \/ ( B b d c ) ) )
    $= ( weq wn wffbetw wa wo simplr anim1i simpr connectivity-between orim12da betw-241 orim12i syl ) ABEFZABCGZHZABDGZHZSACDGZHZUAADCGZHZIBCDGZBDCGZIUB UCUEUDUFUBSUCRSUAJKUBUAUETUALKABCDMNUDUGUFUHABCDOA BDCOPQ $.

${
    connectivity-between-2-d.1 $e |- ( ph -> -. a = b ) $.
    connectivity-between-2-d.2 $e |- ( ph -> ( B a b c ) ) $.
    connectivity-between-2-d.3 $e |- ( ph -> ( B a b d ) ) $.
    connectivity-between-2-d
        $p |- ( ph -> ( ( B b c d ) \/ ( B b d c ) ) )
        $= ( weq wn wffbetw wa wo jca31 connectivity-between-2 syl ) ABCIJZBCDKZLBCEKZLCDEKCEDKMAQRSFGHNBCDEOP $.
$}

${
    $d ph p $.
    $d a p $.
    $d b p $.
    $d c p $.
    $d d p $.
    connectivity-between-3.1 $e |- ( ph -> ( B a b d ) ) $.
    connectivity-between-3.2 $e |- ( ph -> ( B a c d ) ) $.
    connectivity-between-3-d
        $p |- ( ph -> ( ( B a b c ) \/ ( B a c b ) ) )
        $= ( weq wffbetw wo wa ax-predB3 mpan9 olcd wn pointp wex 2pimp3p adantl equcomi con3i ad2antll betw-sym ad2antrl adantr betw-134 syl2anc jca31 connectivity-between-2 syl adantlr exlimddv pm2.61dan ) AECHZBCDIZBDCIZJZAUNKUPUOABDEIZUNUPGECBDLMNAUNOZKE BPIZBPHZOZKZUQPUSVCPQACEEBPRSAVCUQUSAVCKZPBHZOZPBC IZKPBDIZKUQVDVFVGVHVBVFAUTVEVAPBTUAUBVDPBEIZBCEIZV GUTVIAVBEBPUCUDZAVJVCFUEPBCEUFUGVDVIURVHVKAURVCGUE PBDEUFUGUHPBCDUIUJUKULUM $.
$}

connectivity-between-3
    $p |- ( ( ( B a b d ) /\ ( B a c d ) ) -> ( ( B a b c ) \/ ( B a c b ) ) )
    $= ( wffbetw wa simpl simpr connectivity-between-3-d ) ABDEZACDEZFABCDJKGJKHI $.

${
    $d a q $.
    segment-construction-2.1 $e |- ( ph -> ( ( B b a q ) /\ ( a q C a b ) ) ) $.
    segment-construction-2.2 $e |- ( ph -> ( ( B q a x ) /\ ( a x C c d ) ) ) $.
    segment-construction-2.3 $e |- ( ph -> -. a = b ) $.
    l1-segment-construction-connectivity
        $p |- ( ph -> ( ( ( B a b x ) \/ ( B a x b ) ) /\ ( a x C c d ) ) )
        $= ( wffbetw wo wffcong wa weq wn wi cong-diff2 adantl sylc equcomiv nsyl 2an13 syl2anc betw-sym anim1i syl simpld connectivity-between-2-d an3 syl21anc ) ACDBKCBDKLZGCBKZCBEFMZNZUOULUNNAGCDBACGOZGCOADCGKZ CGCDMZNZCDOPZUPPZHJURUTVAQUQCGCDRSTGCUAUBAGCDKZUMA UQUMNZVBUMNAUSUOVCHIUQURUMUNUCUDUQVBUMDCGUEUFUGUHA UMUNIUHUIIIULUOUMUNUJUK $.
$}

${
    $d a q x $.
    $d b q x $.
    $d c q x $.
    $d d q x $.
    segment-construction-connectivity
        $p |- ( -. a = b -> E. x ( ( ( B a b x ) \/ ( B a x b ) ) /\ ( a x C c d ) ) )
        $= ( pointq wffbetw wffcong wa weq wn wo wex wi ax-A4 pm3.21 anim1d simpr simplr simpll l1-segment-construction-connectivity syl6 eximii 19.37iv expcom exlimiiv ) CBFGBFBCHIZBCJKZBCAGBACGLBADEHZIZAMZNFUHUGUKUHUGIZ UJAFBAGUIIZULUJNAABDEFOUMULUHUMIZUGIZUJUMUHUNUGUMU HPQUOABCDEFUNUGRUHUMUGSUHUMUGTUAUBUCUDUEFBBCCOUF $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Segment Comparison
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Declare Le Lt Ge Gt symbol $)
$c Le Ge Lt Gt $.

$( Extend wff notation to include Less Than $)
wfflt $a wff ( a b Lt c d ) $.

$( Extend wff notation to include Less Than or Equal $)
wffle $a wff ( a b Le c d ) $.

$( Extend wff notation to include Greater Than $)
wffgt $a wff ( a b Gt c d ) $.

$( Extend wff notation to include Greater Than or Equal $)
wffge $a wff ( a b Ge c d ) $.

${
$d a y $.
$d b y $.
$d c y $.
$d d y $.
df-le $a |- ( ( a b Le c d ) <-> E. y ( ( B c y d ) /\ ( a b C c y ) ) ) $.
$}

df-ge $a |- ( ( a b Ge c d ) <-> ( c d Le a b ) ) $.

df-lt $a |- ( ( a b Lt c d ) <-> ( ( a b Le c d ) /\ -. ( a b C c d ) ) ) $.

df-gt $a |- ( ( a b Gt c d ) <-> ( c d Lt a b ) ) $.

${
    $d x y $.
    $d a y $.
    $d b y $.
    $d c y $.
    $d d y $.
    $( If a wff is true, it is true for at least one instance. For use with 'Less Than or Equal' predicate. $)
    exist-lemma-le
        $p |- ( ( ( B c x d ) /\ ( a b C c x ) ) -> E. y ( ( B c y d ) /\ ( a b C c y ) ) )
        $= ( wffbetw wffcong wa weq wi ax6evr ax-predB2 ax-predC4 anim12d eximii 19.37iv ) EAFGZCDEAHZIZEBFGZCDEBHZIZBABJZTUCKBBALUDRUASUBABE FMABCDENOPQ $.
$}

${
    $d x y $.
    $d a y $.
    $d b y $.
    $d c y $.
    $d d y $.
    $( If a wff is true, it is true for at least one instance. For use with 'Less Than or Equal' predicate alt definition. $)
    exist-lemma-le2
        $p |- ( ( ( B a b x ) /\ ( a x C c d ) ) -> E. y ( ( B a b y ) /\ ( a y C c d ) ) )
        $= ( wffbetw wffcong wa weq wi ax6evr ax-predB3 ax-predC2 anim12d eximii 19.37iv ) CDAGZCAEFHZIZCDBGZCBEFHZIZBABJZTUCKBBALUDRUASUBABC DMABCEFNOPQ $.
$}

${
    $d a x y $.
    $d b x y $.
    $d c x y $.
    $d d x y $.
    l1-le-def2
        $p |- ( ( a b Le c d ) -> E. x ( ( B a b x ) /\ ( a x C c d ) ) )
        $= ( wffle vy wffbetw wffcong wa wex df-le biimpi wffcong3 wffcol id col-intro-1-d cong-sym anim12i col-seg-div syl simpl biantrurd exbidv mpbid betw-preserved cong3-elim3 adantl cong-sym-d jca eximi exlimiv ) BCDEFZDGEHZBCDGIZJZGKZBCAHZBADEIZJZAKZUMUQGBCDELMU PVAGUPUNDGEBCANZJZAKZVAUPVBAKZVDUPDGEOZDGBCIZJVEUN VFUOVGUNDGEUNPQBCDGRSDGEBCATUAUPVBVCAUPUNVBUNUOUBU CUDUEVCUTAVCURUSDGEBCAUFVCDEBAVBDEBAIUNDGEBCAUGUHU IUJUKUAULUA $.
$}

${
    $d a x y $.
    $d b x y $.
    $d c x y $.
    $d d x y $.
    $( An alternate definition for the 'Less than or Equal to' predicate. Theorem 5.5 of [SST] $)
    le-def2
        $p |- ( ( a b Le c d ) <-> E. x ( ( B a b x ) /\ ( a x C c d ) ) )
        $= ( wffle wffbetw wffcong wa wex l1-le-def2 vy wffcong3 cong-seg-div ancoms cong3-elim1 anim2i eximi syl df-le sylibr exlimiv impbii ) BCDEFZBCAGZBADEHZIZAJABCDEKUGUDAUGDLEGZBCDLHZIZLJZ UDUGUHBCADLEMZIZLJZUKUFUEUNBCADLENOUMUJLULUIUHBCAD LEPQRSLBCDETUAUBUC $.
$}

${
    $d x y $.
    $d a y $.
    $d b y $.
    $d c y $.
    $d d y $.
    le-intro.1 $e |- ( ph -> ( B c x d ) ) $.
    le-intro.2 $e |- ( ph -> ( a b C c x ) ) $.
    $( Introduces the 'Less Than or Equal to' predicate. $)
    le-intro
        $p |- ( ph -> ( a b Le c d ) )
        $= ( vy wffbetw wffcong wa wex wffle jca exist-lemma-le syl df-le sylibr ) AEIFJCDEIKLIMZCDEFNAEBFJZCDEBKZLTAUAUBGHOBICDEFPQI CDEFRS $.
$}

${
    $d x y $.
    $d a y $.
    $d b y $.
    $d c y $.
    $d d y $.
    le-intro.1 $e |- ( ph -> ( B a b x ) ) $.
    le-intro.2 $e |- ( ph -> ( a x C c d ) ) $.
    $( Introduces the 'Less Than or Equal to' predicate from alt definition. $)
    le-intro2
        $p |- ( ph -> ( a b Le c d ) )
        $= ( vy wffbetw wffcong wa wex wffle jca exist-lemma-le2 syl le-def2 sylibr ) ACDIJCIEFKLIMZCDEFNACDBJZCBEFKZLTAUAUBGHOBICDEFPQI CDEFRS $.
$}

${
    $( The Left Hand Side of the 'Less Than or Equal to' predicate commutes. $)
    le-LHS
        $p |- ( ( a b Le c d ) -> ( b a Le c d ) )
        $= ( vy wffbetw wffcong wa wex wffle cong-lhs anim2i eximi df-le 3imtr4i ) CEDFZABCEGZHZEIPBACEGZHZEIABCDJBACDJRTEQSPABCEKLME ABCDNEBACDNO $.
$}

${
    $d a x $.
    $d b x $.
    $d c x $.
    $d d x $.
    $( The Right Hand Side of the 'Less Than or Equal to' predicate commutes. $)
    le-RHS
        $p |- ( ( a b Le c d ) -> ( a b Le d c ) )
        $= ( vx wffbetw wffcong wa wex wffle cong-rhs anim2i eximi le-def2 3imtr4i ) ABEFZAECDGZHZEIPAEDCGZHZEIABCDJABDCJRTEQSPAECDKLME ABCDNEABDCNO $.
$}

${
    $d a x $.
    $d b x $.
    $d c x $.
    $d d x $.
    $d e y $.
    $d f y $.
    $d ph x y $.
    $d g x y $.
    $d h x y $.
    cong-preserves-le.1 $e |- ( ph -> ( a b Le c d ) ) $.
    cong-preserves-le.2 $e |- ( ph -> ( a b C e f ) ) $.
    cong-preserves-le.3 $e |- ( ph -> ( c d C g h ) ) $.
    $( Congruence of two segments preserves the 'Less than or Equal to' predicate. Theorem 5.6 of [SST] $)
    cong-preserves-le-d
        $p |- ( ph -> ( e f Le g h ) )
        $= ( vx wffbetw wffcong wa wex wffle vy df-le biimpi syl nfv nfe1 wffcong3 adantr simprl cong-seg-div-d wi cong3-elim1 anim2i a1i eximdv mpd ad2antrr simplrr simprr jca cong-trans-d2 ax-A2 syl2anc 19.8ad exlimdd exlimddv sylibr ) AHMINZFGHMOZPZMQZFGHIRADSENZBCDSOZPZVISABCDERZVLSQ ZJVMVNSBCDETUAUBAVLPZVFDSHMOZPZVIMVOMUCVHMUDVOVFDS EHMIUEZPZMQVQMQVODSEHMIADEHIOVLLUFAVJVKUGUHVOVSVQM VSVQUIVOVRVPVFDSEHMIUJUKULUMUNVOVQPZVHMVTVFVGVOVFV PUGVTBCFGOZBCHMOVGAWAVLVQKUOVTBCDSHMVTVKVPAVJVKVQU PVOVFVPUQURUSBCFGHMUTVAURVBVCVDMFGHITVE $.
$}

${
    $d b y $.
    $( The 'Less than or Equal to' predicate is reflexive. Theorem 5.7 of [SST] $)
    le-reflexivity
        $p |- ( a b Le a b )
        $= ( vy wffbetw wffcong wa wex wffle weq ax6evr betw-id ax-predB2 mpi cong-ref ax-predC4 jca eximii df-le biimpri ax-mp ) ACBDZABACEZFZCGZABABHZBCIZUCCCBJUFUAUBUFABBDUAABKB CABLMUFABABEUBABNBCABAOMPQUEUDCABABRST $.
$}

${
    $d c y z $.
    $d d y z $.
    $d ph x y z $.
    $d a x y z $.
    $d b x y z $.
    $d e x y z $.
    $d f x y z $.
    le-transitivity.1 $e |- ( ph -> ( a b Le c d ) ) $.
    le-transitivity.2 $e |- ( ph -> ( c d Le e f ) ) $.
    $( The 'Less than or Equal to' predicate is transitive. Theorem 5.8 of [SST] $)
    le-transitivity
        $p |- ( ph -> ( a b Le e f ) )
        $= ( vz wffbetw wffcong wa wex wffle vx df-le biimpi syl vy adantr nfv nfe1 wffcong3 simprr simplrl cong-seg-div-d cong3-elim1 anim2i eximi simprl jca betw-243 simplrr anassrs cong-trans-d 19.8ad exlimdd exlimddv sylibr ) AFJGKZBCFJLZMZJNZBCFGOADPEKZBCDPLZMZVDPABCDEOZVGPN ZHVHVIPBCDEQRSAVGMZFTGKZDEFTLZMZVDTVJDEFGOZVMTNZAV NVGIUAVNVOTDEFGQRSVJVMMZFJTKZDPFJLZMZVDJVPJUBVCJUC VPVQDPEFJTUDZMZJNVSJNVPDPEFJTVJVKVLUEAVEVFVMUFUGWA VSJVTVRVQDPEFJTUHUIUJSVPVSMZVCJWBVAVBWBVQVKMVAWBVQ VKVPVQVRUKVJVKVLVSUFULFJTGUMSWBBCDPFJVJVMVSVFAVEVF VMVSMUNUOVPVQVRUEUPULUQURUSUSJBCFGQUT $.
$}

${
    $d ph z $.
    $d x z $.
    $d y z $.
    $d a z $.
    $d b z $.
    $d c z $.
    $d d z $.
    le-antisymmetry.3 $e |- ( ph -> ( ( B c y d ) /\ ( a b C c y ) ) ) $.
    le-antisymmetry.4 $e |- ( ph -> ( ( B a x b ) /\ ( c d C a x ) ) ) $.
    l1-le-antisymmetry
        $p |- ( ph -> ( a b C c d ) )
        $= ( vz wffbetw wffcong wa wffcong3 wex simprd simpld cong-seg-div-d cong3-elim1 anim2i eximi syl weq simpll sylan simprl betw-243-d cong-sym ad2antll simplr cong-sym-d cong-trans-d betw-cong-equivalence ax-predB2 sylc jca betw-equality equcomd adantr ax-predC4 exlimddv ) AFJCKZDBFJLZMZDEFGLZJAVBDBEFJCNZMZJOVDJOADBEFJCAFC GKZDEFCLZHPZADBEKZFGDBLZIQRVGVDJVFVCVBDBEFJCSTUAUB AVDMZCGUCVIVEVMGCVMFGCKZVHMGCUCVMVNVHVMJGUCVBVNVMF JGVMFJCGAVHVIMVDVHHVHVIVDUDUEZAVBVCUFZUGVMFJDBFGVC FJDBLAVBDBFJUHUIVMFGDBAVKVLMVDVLIVKVLVDUJUEUKULUMV PJGFCUNUOVOUPFGCUQUBURAVIVDVJUSCGDEFUTUOVA $.
$}

${
    $d ph x y $.
    $d a x y $.
    $d b x y $.
    $d c x y $.
    $d d x y $.
    le-antisymmetry.1 $e |- ( ph -> ( a b Le c d ) ) $.
    le-antisymmetry.2 $e |- ( ph -> ( c d Le a b ) ) $.
    $( The 'Less than or Equal to' predicate is anti-symmetric. Theorem 5.9 of [SST] $)
    le-antisymmetry
        $p |- ( ph -> ( a b C c d ) )
        $= ( vy wffbetw wffcong wa wffle wex df-le biimpi syl vx adantr simplr simpr l1-le-antisymmetry exlimddv ) ADHEIBCDHJKZBCDEJZHABCDELZUCHMZFUEUFHBCDENOPAUCKZB QCIDEBQJKZUDQUGDEBCLZUHQMZAUIUCGRUIUJQDEBCNOPUGUHK QHBCDEAUCUHSUGUHTUAUBUB $.
$}

${
    $d c y $.
    $( The null segment is Less than or Equal to every segment. Theorem 5.11 of [SST]. $)
    le-nullsegment
        $p |- ( a a Le c d )
        $= ( wffle vy wffbetw wffcong wa wex weq ax6evr betw-id2 cong-nullseg pm3.2i ax-predB2 ax-predC4 anim12d mpi eximii df-le mpbir ) AABCDBECFZAABEGZHZEIBEJZUDEEBKUEBBCFZAABBGZHUDUFUG BCLABMNUEUFUBUGUCBEBCOBEAABPQRSEAABCTUA $.
$}

${
    $d a x $.
    $d a y $.
    $d b x $.
    $d b y $.
    $d c x $.
    $d d x $.
    $( The Trichotomy law for 'Less than or Equal to' predicate . Theorem 5.10 of [SST]. $)
    le-cases
        $p |- ( ( a b Le c d ) \/ ( c d Le a b ) )
        $= ( weq wffle wo vy wffbetw wffcong wa wex le-nullsegment df-le biimpi ax-mp ax-predC2 anim2d eximdv mpi biimpri syl orcd wn vx segment-construction-connectivity andir exbii sylib 19.43 le-def2 cong-sym anim2i eximi orim12i pm2.61i ) ABEZABCDFZCDABFZGZUQURUSUQCHDIZABCHJZKZHLZURUQVAAA CHJZKZHLZVDAACDFZVGACDMVHVGHAACDNOPUQVFVCHUQVEVBVA ABACHQRSTURVDHABCDNUAUBUCUQUDZABUEIZAUECDJZKZUELZA UEBIZVKKZUELZGZUTVIVLVOGZUELZVQVIVJVNGVKKZUELVSUEA BCDUFVTVRUEVJVNVKUGUHUIVLVOUEUJUIVMURVPUSURVMUEABC DUKUAVPVNCDAUEJZKZUELZUSVOWBUEVKWAVNAUECDULUMUNUSW CUECDABNUAUBUOUBUP $.
$}

${
    l1-le-betw.2 $e |- ( ph -> ( B a b c ) ) $.
    l1-le-betw
        $p |- ( ph -> ( ( a b Le a c ) /\ ( b c Le a c ) ) )
        $= ( wffle wffcong cong-ref a1i le-intro betw-sym-d le-intro2 le-LHS syl le-RHS jca ) ABCBDFCDBDFZACBCBDEBCBCGABCHIJACDDBFZQADCDBFRABDCD BABCDEKDBDBGADBHILDCDBMNCDDBONP $.
$}

${
    l1-le-betw.1 $e |- ( ph -> Col ( a b c ) ) $.
    l1-le-betw.2 $e |- ( ph -> ( a b Le a c ) ) $.
    l1-le-betw.3 $e |- ( ph -> ( b c Le a c ) ) $.
    l2-le-betw
        $p |- ( ph -> ( B a b c ) )
        $= ( wffbetw wo simpr wa weq betw-sym-d wffcong wffle adantr le-LHS syl le-RHS id l1-le-betw adantl simprd le-antisymmetry cong-4321 betw-cong-equivalence betw-id ax-predB2 mpisyl simpld cong-sym-d cong-2143-d jaodan wffcol col-elim mpjaodan ) ABCDHZUQCDBHZDBCHZIZAUQJAURUQUSAURKZDCLBDDHUQVABDC VACDBAURJMVACBDBNBDBCNVACBDBVACBBDOZCBDBOVABCBDOZV BAVCURFPBCBDQRCBBDSRVACDCBOZDBCBOZURVDVEKAURCDBURT UAUBUCUDCBDBUERUFBDUGDCBDUHUIAUSKZDCBVFBCLDBBHDCBH VFDBCAUSJVFBDCDVFCDBDVFCDBDACDBDOUSGPVFBDDCOZBDCDO VFDBDCOZVGVFVHBCDCOZUSVHVIKAUSDBCUSTUAUBUJDBDCQRBD DCSRUDUKULUFDBUGBCDBUHUIMUMABCDUNUQUTIEBCDUORUP $.
$}

${
    le-betw.1 $e |- ( ph -> Col ( a b c ) ) $.
    le-betw-d
        $p |- ( ph -> ( ( B a b c ) <-> ( ( a b Le a c ) /\ ( b c Le a c ) ) ) )
        $= ( wffbetw wffle wa id l1-le-betw wffcol adantr simprl simprr l2-le-betw ex impbid2 ) ABCDFZBCBDGZCDBDGZHZRBCDRIJAUARAUAHBCDABCDKUAELAST MASTNOPQ $.
$}

le-betw
    $p |- ( Col ( a b c ) -> ( ( B a b c ) <-> ( ( a b Le a c ) /\ ( b c Le a c ) ) ) )
    $= ( wffcol id le-betw-d ) ABCDZABCGEF $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Rays
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Declare Ray symbol $)
$c Ray $.

$( Extend wff notation to include Ray $)
wffray $a wff Ray ( p a b ) $.

$( Definition of a Ray $)

df-ray $a |- ( Ray ( p a b ) <-> ( ( -. a = p /\ -. b = p ) /\ ( ( B p a b ) \/ ( B p b a ) ) ) ) $.

df-ray-outro
    $p |- ( Ray ( p a b ) -> ( ( -. a = p /\ -. b = p ) /\ ( ( B p a b ) \/ ( B p b a ) ) ) )
    $= ( wffray weq wn wa wffbetw wo df-ray biimpi ) ABCDACEFBCEFGCABHCBAHIGABCJK $.

df-ray-outro1
    $p |- ( Ray ( p a b ) -> -. a = p )
    $= ( wffray weq wn wffbetw wo df-ray-outro simplld ) ABCDACEFBCEFCABGCBAGHABCIJ $.

df-ray-outro2
    $p |- ( Ray ( p a b ) -> -. b = p )
    $= ( wffray weq wn wffbetw wo df-ray-outro simplrd ) ABCDACEFBCEFCABGCBAGHABCIJ $.

df-ray-outro3
    $p |- ( Ray ( p a b ) -> ( ( B p a b ) \/ ( B p b a ) ) )
    $= ( wffray weq wn wa wffbetw wo df-ray-outro simprd ) ABCDACEFBCEFGCABHCBAHIABCJK $.

df-ray-intro
    $p |- ( ( ( -. a = p /\ -. b = p ) /\ ( ( B p a b ) \/ ( B p b a ) ) ) -> Ray ( p a b ) )
    $= ( wffray weq wn wa wffbetw wo df-ray biimpri ) ABCDACEFBCEFGCABHCBAHIGABCJK $.

${
    df-ray-intro-d.1 $e |- ( ph -> -. a = p ) $.
    df-ray-intro-d.2 $e |- ( ph -> -. b = p ) $.
    df-ray-intro-d.3 $e |- ( ph -> ( ( B p a b ) \/ ( B p b a ) ) ) $.
    df-ray-intro-d
        $p |- ( ph -> Ray ( p a b ) )
        $= ( weq wn wffbetw wo wffray df-ray-intro syl21anc ) ABDHICDHIDBCJDCBJKBCDLEFGBCDMN $.
$}

$( Belonging to the same ray is an equivalence relation  $)

ray-reflexivity
    $p |- ( -. a = p -> Ray ( p a a ) )
    $= ( weq wn id wffbetw betw-id a1i orcd df-ray-intro-d ) ABCDZAABKEZLKBAAFZMMKBAGHIJ $.

ray-symmetric
    $p |- ( Ray ( p a b ) -> Ray ( p b a ) )
    $= ( wffray df-ray-outro2 df-ray-outro1 wffbetw df-ray-outro3 orcomd df-ray-intro-d ) ABCDZBACABCEABCFKCABGCBAGABCHIJ $.

ray-transitivity
    $p |- ( ( Ray ( p a b ) /\ Ray ( p b c ) ) -> Ray ( p a c ) )
    $= ( wffray wa weq wn df-ray-outro1 adantr df-ray-outro2 adantl wffbetw wo df-ray-outro3 anim12i wi betw-243 orcd a1i equcomi nsyl biantrurd connectivity-between anasss biimtrdi connectivity-between-3 ancoms olcd ccased mpd df-ray-intro-d ) ABDEZBCDEZFZACDUMADGHUNABDIJUNCDGHUMBCDKLUODABMZDB AMZNZDBCMZDCBMZNZFZDACMZDCAMZNZUMURUNVAABDOBCDOPUN VBVEQUMUNUPUSUQUTVEUPUSFZVEQUNVFVCVDDABCRSTUNUQUSF ZDBGZHZVGFVEUNVIVGUNBDGVHBCDIDBUAUBUCVIUQUSVEDBACU DUEUFUPUTFVEQUNDACBUGTUQUTFZVEQUNVJVDVCUTUQVDDCBAR UHUITUJLUKUL $.

${
    betw-implies-ray-d.1 $e |- ( ph -> -. a = b ) $.
    betw-implies-ray-d.2 $e |- ( ph -> ( B a b c ) ) $.
    $( Betweenness implies the latter two points are a Ray with an origin at the preceding point. $)
    betw-implies-ray-d
        $p |- ( ph -> Ray ( a b c ) )
        $= ( weq wn wffbetw wo wffray equcomi nsyl ax-predB3 syl5com ax-A6 syl6 mtod orcd df-ray-intro syl21anc ) ACBGZHDBGZHBCDIZBDCIZJCDBKABCGZUBECBLMAUCUFEAUCBCB IZUFAUDUCUGFDBBCNOBCPQRAUDUEFSCDBTUA $.
$}

betw-implies-ray
    $p |- ( ( -. a = b /\ ( B a b c ) ) -> Ray ( a b c ) )
    $= ( weq wn wffbetw wa simpl simpr betw-implies-ray-d ) ABDEZABCFZGABCKLHKLIJ $.

${
    ray-col-d.1 $e |- ( ph -> Ray ( a b c ) ) $.
    ray-col-d
        $p |- ( ph -> Col ( a b c ) )
        $= ( wffbetw wo wffcol wffray df-ray-outro3 syl betw-sym orcd orim2i col-intro ) ABCDFZCDBFZDBCFZGZGZBCDHAPBDCFZGZTACDBIUBECDBJKUAS PUAQRBDCLMNKBCDOK $.
$}

${
    betw-implies-betw-ray-d.1 $e |- ( ph -> -. a = p ) $.
    betw-implies-betw-ray-d.2 $e |- ( ph -> -. b = p ) $.
    betw-implies-betw-ray-d.3 $e |- ( ph -> -. c = p ) $.
    betw-implies-betw-ray-d.4 $e |- ( ph -> ( B a p c ) ) $.
    betw-implies-betw-ray-d
        $p |- ( ph -> ( ( B b p c ) <-> Ray ( p a b ) ) )
        $= ( wffbetw wffray betw-sym wa weq wn adantr wo wi betw-sym-d connectivity-between-2 expl syl expd mpd imp df-ray-intro-d ex syl5 df-ray-outro3 adantl equcomi nsyl betw-143 expcom syl6 betw-241 a1i jaod impbid ) ACEDJZBCEKZUTDECJZAVACEDLAVBVAAVBMBCEABENZOZVBFPAC ENOVBGPAVBEBCJZECBJZQZADEBJZVBVGRABEDISZAVHVBVGADE NOZVHVBMVGRHVJVHVBVGDEBCTUAUBUCUDUEUFUGUHAVAUTAVAM ZVGUTVAVGABCEUIUJVKVEUTVFVKVEVBUTVKVHVEVBRAVHVAVIP VKVHVEVBVKEBNZOZVHVEMZVBRVKVCVLAVDVAFPEBUKULVNVMVB DEBCUMUNUBUCUDDECLUOVFBCEJZVKUTECBLVKBEDJZVOUTRZAV PVAIPVPVQRVKVOVPUTBCEDUPUNUQUDUHURUDUGUS $.
$}

${
    $( Theorem 6.2 of [SST]. $)
    betw-implies-betw-ray
        $p |- ( ( ( ( -. a = p /\ -. b = p ) /\ -. c = p ) /\ ( B a p c ) ) -> ( ( B b p c ) <-> Ray ( p a b ) ) )
        $= ( weq wn wa wffbetw simplll simpllr simplr simpr betw-implies-betw-ray-d ) ADEFZBDEFZGZCDEFZGZADCHZGABCDNOQSINOQSJPQSKRSLM $.
$}

${
    $d a c $.
    $d b c $.
    $d c p $.
    l1-ray-definition-point.1 $e |- ( ph -> -. a = p ) $.
    l1-ray-definition-point.2 $e |- ( ph -> -. b = p ) $.
    l1-ray-definition-point.3 $e |- ( ph -> E. c ( ( -. c = p /\ ( B a p c ) ) /\ ( B b p c ) ) ) $.
    $( A lemma for ray-definition-point. Shows the reverse direction of the bi-implication. $)
    l1-ray-definition-point
        $p |- ( ph -> Ray ( p a b ) )
        $= ( wffbetw wo wex weq wn wa betw-sym anim2i anim1i eximi syl connectivity-between-2 ax5e df-ray-intro-d ) ABCEFGAEBCIECBIJZDKZUCADELMZDEBIZNZDECIZNZDKZUDAUG CEDIZNZDKZUJAUEBEDIZNZUKNZDKUMHUPULDUOUGUKUNUFUEBE DOPQRSULUIDUKUHUGCEDOPRSUIUCDDEBCTRSUCDUASUB $.
$}

${
    $d ph c $.
    $d a c $.
    $d c p $.
    l2-ray-definition-point.1 $e |- ( ph -> Ray ( p a b ) ) $.
    $( A lemma for ray-definition-point. Shows the forward direction of the bi-implication. $)
    l2-ray-definition-point
        $p |- ( ph -> ( ( -. a = p /\ -. b = p ) /\ E. c ( ( -. c = p /\ ( B a p c ) ) /\ ( B b p c ) ) ) )
        $= ( weq wn wffbetw wa wex wffray df-ray-outro1 syl df-ray-outro2 nfv nfe1 wi 2pimp3p a1i mpd equcomi con3i anim2i eximi simprr simprl jca wo betw-sym-d df-ray-outro3 adantr nsyl jca31 betw-143 3adant2 3expib betw-134 a1d jaodan anabsi5 19.8ad exlimdd ) ABEGZHZCEGHZDEGZHZBEDIZJZCEDIZJZDKZABCELZVEFBCEMNZ AVNVFFBCEONAVIVHJZVMDADPVLDQAVIEDGZHZJZDKZVPDKAVEV TVOVEVTRAEBBEDSTUAVSVPDVRVHVIVGVQDEUBUCUDUENAVPJZV LDWAVJVKWAVHVIAVIVHUFAVIVHUGZUHWADECWADEBIZEBCIZEC BIZUIZJZEBGZHZJZDECIZWAWCWFWIWABEDWBUJAWFVPAVNWFFB CEUKNULWAVDWHAVEVPVOULEBUBUMUNWGWIWKWCWDWJWKRWEWCW DJZWGWIWKWLWIWKWGDEBCUOUPUQWCWEJWKWJDECBURUSUTVANU JUHVBVCUN $.
$}

${
    $d a c $.
    $d b c $.
    $d c p $.
    $( Alternative definition of the 'Ray' predicate obtained by asserting the existence of a point. Theorem 6.3 of [SST]. $)
    ray-definition-point
        $p |- ( Ray ( p a b ) <-> ( ( -. a = p /\ -. b = p ) /\ E. c ( ( -. c = p /\ ( B a p c ) ) /\ ( B b p c ) ) ) )
        $= ( wffray weq wn wa wffbetw wex id l2-ray-definition-point simpll simplr simpr l1-ray-definition-point impbii ) ABDEZADFGZBDFGZHZCDFGADCIHBDCIHCJZHZRABCDRKLUCABCD STUBMSTUBNUAUBOPQ $.
$}

$( Declare IntersectAt symbol $)
$c IntersectAt $.

$( Extend wff notation to include IntersectAt $)
wffintersectat $a wff IntersectAt ( a b c d x ) $.

$( Two lines 'ab' and 'cd' intersect at 'x'. $)
df-intersectat $a |- ( IntersectAt ( a b c d x ) <-> ( ( E. p ( Col ( p a b ) /\ Col ( p c d ) ) /\ Col ( x a b ) ) /\ Col ( x c d ) ) )  $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Midpoint
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Declare Midpoint symbol $)
$c Mid $.

$( Extend wff notation to include Mid $)
wffmid $a wff Mid ( a m b ) $.

$( Definition of a Midpoint $)

df-mid $a |- ( Mid ( a m b ) <-> ( ( B a m b ) /\ ( m a C m b ) ) ) $.

predM1
    $p |- ( x = y -> ( Mid ( x m b ) -> Mid ( y m b ) ) )
    $= ( weq wffbetw wffcong wa wffmid ax-predB1 ax-predC2 anim12d df-mid 3imtr4g ) ABEZADCFZDADCGZHBDCFZDBDCGZHACDIBCDIOPRQSABDCJABDD CKLACDMBCDMN $.

predM2
    $p |- ( x = y -> ( Mid ( a x b ) -> Mid ( a y b ) ) )
    $= ( weq wffbetw wffcong wa wffmid ax-predB2 ax-predC1 ax-predC3 syld anim12d df-mid 3imtr4g ) ABEZCADFZACADGZHCBDFZBCBDGZHCDAICDBIQRTSUAABCDJQSB CADGUAABCADKABBCDLMNCDAOCDBOP $.

predM3
    $p |- ( x = y -> ( Mid ( a m x ) -> Mid ( a m y ) ) )
    $= ( weq wffbetw wffcong wa wffmid ax-predB3 ax-predC4 anim12d df-mid 3imtr4g ) ABEZCDAFZDCDAGZHCDBFZDCDBGZHCADICBDIOPRQSABCDJABDC DKLCADMCBDMN $.

df-mid-outro
    $p |- ( Mid ( a m b ) -> ( ( B a m b ) /\ ( m a C m b ) ) )
    $= ( wffmid wffbetw wffcong wa df-mid biimpi ) ABCDACBECACBFGABCHI $.

df-mid-outro-cong-sym
    $p |- ( Mid ( a m b ) -> ( ( B a m b ) /\ ( m b C m a ) ) )
    $= ( wffmid wffbetw wffcong wa df-mid-outro cong-sym anim2i syl ) ABCDACBEZCACBFZGLCBCAFZGABCHMNLCACBIJK $.

df-mid-outro1
    $p |- ( Mid ( a m b ) -> ( B a m b ) )
    $= ( wffmid wffbetw wffcong df-mid simplbi ) ABCDACBECACBFABCGH $.

df-mid-outro2
    $p |- ( Mid ( a m b ) -> ( m a C m b ) )
    $= ( wffmid wffbetw wffcong df-mid simprbi ) ABCDACBECACBFABCGH $.

df-mid-intro
    $p |- ( ( ( B a m b ) /\ ( m a C m b ) ) -> Mid ( a m b ) )
    $= ( wffmid wffbetw wffcong wa df-mid biimpri ) ABCDACBECACBFGABCHI $.

${
    df-mid-intro-d.1 $e |- ( ph -> ( B a m b ) ) $.
    df-mid-intro-d.2 $e |- ( ph -> ( m a C m b ) ) $.
    df-mid-intro-d
        $p |- ( ph -> Mid ( a m b ) )
        $= ( wffbetw wffcong wffmid df-mid sylanbrc ) ABDCGDBDCHBCDIEFBCDJK $.
$}

${
    $( The Midpoint predicate is symmetric. Theorem 7.2 in [SST]. $)
    mid-symmetry
        $p |- ( Mid ( a m b ) -> Mid ( b m a ) )
        $= ( wffmid wffbetw wffcong wa df-mid-outro betw-sym cong-sym anim12i syl df-mid-intro ) ABCDZBCAEZCBCAFZGZBACDNACBEZCACBFZGQABCHROSPACBICA CBJKLBACML $.
$}


${
    $( A Midpoint identity. Theorem 7.3 in [SST]. $)
    mid-identity
        $p |- ( Mid ( a m a ) -> m = a )
        $= ( wffmid wffbetw weq df-mid-outro1 ax-A6 equcomi 3syl ) AABCABADABEBAEAABFABGABHI $.
$}

mid-identity2
    $p |- ( Mid ( a a b ) -> a = b )
    $= ( wffmid wffcong weq df-mid-outro2 cong-nullseg-sym syl ) ABACAAABDABEABAFABAGH $.

mid-identity3
    $p |- ( Mid ( a b b ) -> a = b )
    $= ( wffmid wffcong weq df-mid-outro2 ax-A3 equcomi 3syl ) ABBCBABBDBAEABEABBFBABGBAHI $.

mid-identity4
    $p |- Mid ( a a a )
    $= ( wffbetw wffcong wa wffmid betw-id ax-A1 pm3.2i df-mid-intro ax-mp ) AAABZAAAACZDAAAEKLAAFAAGHAAAIJ $.

mid-identity2-converse
    $p |- ( a = b -> Mid ( a a b ) )
    $= ( weq wffmid mid-identity4 predM3 mpi ) ABCAAADABADAEABAAFG $.

mid-identity3-converse
    $p |- ( a = b -> Mid ( a b b ) )
    $= ( weq wffmid equcomi mid-identity4 predM1 mpisyl ) ABCBACBBBDABBDABEBFBABBGH $.

${
    $d m q $.
    $d p q $.
    $( The point 'p' can always be reflected across the point 'm'. Existence portion of Theorem 7.4 of [SST]. $)
    mid-outpoint-exists
        $p |- E. q Mid ( p m q )
        $= ( wffbetw wffcong wa wffmid ax-A4 cong-sym anim2i eximii df-mid-intro ) BACDZABACEZFZBCAGCMACABEZFOCCAABBHPNMACABIJKBCALK $.
$}

mid-outpoint-unique
    $p |- ( ( Mid ( a m p ) /\ Mid ( a m q ) ) -> p = q )
    $= ( weq wffmid wa wi predM1 anim12d mid-identity2 anim12i syl6 ax7 imp wn wffbetw wffcong df-mid-outro-cong-sym unique-segcon syl2ani pm2.61i ) ABEZACBFZADBFZGZCDEZHUCUFBCEZBDEZGZUGUCUFBCBFZBDBF ZGUJUCUDUKUEULABCBIABDBIJUKUHULUIBCKBDKLMUHUIUGBCD NOMUDUCPABCQBCBARGABDQBDBARGUGUEACBSADBSCDBBAATUAU B $.

${
    $( The point 'b' reflected across the point 'm' gives a unique point. Theorem 7.9 of [SST]. $)
    mid-outpoint-unique2
        $p |- ( ( Mid ( p m a ) /\ Mid ( q m a ) ) -> p = q )
        $= ( wffmid wa weq mid-symmetry anim12i mid-outpoint-unique syl ) CABEZDABEZFACBEZADBEZFCDGLNMOCABHDABHIABCDJK $.
$}

mid-outpoint-unique3
    $p |- ( ( Mid ( a m p ) /\ Mid ( q m a ) ) -> p = q )
    $= ( wffmid wa weq mid-symmetry anim1i mid-outpoint-unique2 syl ) ACBEZDABEZFCABEZMFCDGLNMACBHIABCDJK $.

${
    mid-congruence-preserved.1 $e |- ( ph -> ( ( B r p a ) /\ ( p a C q m ) ) ) $.
    mid-congruence-preserved.2 $e |- ( ph -> ( ( B s q b ) /\ ( q b C p m ) ) ) $.
    mid-congruence-preserved.3 $e |- ( ph -> ( ( B a r c ) /\ ( r c C q m ) ) ) $.
    mid-congruence-preserved.4 $e |- ( ph -> ( ( B b s d ) /\ ( s d C p m ) ) ) $.
    mid-congruence-preserved.5 $e |- ( ph -> Mid ( p m r ) ) $.
    mid-congruence-preserved.6 $e |- ( ph -> Mid ( q m s ) ) $.
    mid-congruence-preserved.7 $e |- ( ph -> -. p = m ) $.
    l1-mid-congruence-preserved
        $p |- ( ph -> ( p q C r s ) )
        $= ( wffifsc wffcong wffbetw wa betw-sym adantr syl wffmid df-mid-outro1 betw-134 syl2anc betw-132-d simpld betw-241-d betw-sym-d df-mid-outro2 cong-lhs simpl2im cong-3421 simprd cong-sym-d ax-A2 segment-addition-d cong-2143-d cong-lhs-d ax-a2-sym wffofsc weq wn betw-243-d cong-rhs cong-trans-d ax-A1 a1i ofsc-intro-d ax-predB3 syl5com a1d jcad betw-equality syl6 pm2.65d jca ax-A5-alt ifsc-intro wi ifsc-cong mpd ) ABGFHDIFJRZGHIJSZABGFHDIFJABGITZGFITZBGFTAIGBTZGBH FSZUAWHKWJWHWKIGBUBUCUDZAGIFUEZWIOGIFUFUDZBGFIUGUH ZAFIDABFIDABGFIWNWLUIZABIDTZIDHFSZMUJZUKZULAFBFDAF GBFIDABGFWOULWTAWMFGFISOGIFUMUDZAHFGBSZHFIDSGBIDSA BGHFSZXBAWJWKXCKGBHFUNUOZBGHFUPUDAIDHFAWQWRMUQZURH FGBIDUSUHUTZVAAFGFIXAVAAHBJDACHFBEJFDRZHBJDSZACHFB EJFDACHJTZHFJTZCHFTAJHCTZHCGFSZUAXILXKXIXLJHCUBUCU DZAHJFUEZXJPHJFUFUDZCHFJUGUHZAFJEAHFJEXOACHJEXMACJ ETZJEGFSZNUJZUKUKZULZACHFEJFXPYAACHGFSEJGFSCHEJSAG FCHAXKXLGFCHSZLHCGFUPUOZURAJEGFAXQXRNUQZVBGFCHEJVC UHAFHFJAXNFHFJSPHJFUMUDZVAZUTYFADECBSZCBEDSABFDEEF CBVDZBFVEZVFZUAYGAYHYJABFDEEFCBABFIDWSWPVGACFEACFJ EXSACHFJXOXMUIVGULABFFESZBFEFSABGFFJEWOXTABGFHFJAX CBGFHSXDBGHFVHUDYEVIAJEGFYDURUTZBFFEVHUDAFDCFSFDFC SAFIDCHFWTXPAFIFGCHAFGFIXAURACHFGAYBCHFGSYCGFCHUPU DURVIXEUTFDCFVHUDBEEBSABEVJVKAYKFEFBSYLBFFEUPUDVLA YIGFVEZAYIIGFTZIFGTZUAYMAYIYNYOAWJYIYNAWJWKKUJBFIG VMVNAYOYIAGFIWNULVOVPIGFVQVRAYMVFYIQVOVSVTBFDEEFCB WAUDDECBUPUDXFWBXGXHWCACHFBEJFDWDVKWEVAYEWBWFWGWCA BGFHDIFJWDVKWE $.
$}

${
    $d ph a b c d $.
    $d a b c d m $.
    $d a b c d p $.
    $d a b c d q $.
    $d a b c d r $.
    $d a b c d s $.
    mid-congruence-preserved.2 $e |- ( ph -> Mid ( p m r ) ) $.
    mid-congruence-preserved.4 $e |- ( ph -> Mid ( q m s ) ) $.
    mid-congruence-preserved-d
        $p |- ( ph -> ( p q C r s ) )
        $= ( weq wffcong wffmid wa jca predM1 mid-identity2 syl6 imp adantrr simpl equcomd df-mid-outro2 ad2antll ax-predC1 sylc ax-predC3 sylan2 ancoms pointa wffbetw wn wi pointb pm3.21 anim1d pointc pointd wex id simplll anim12ci simpllr adantl simprlr simprr simpr simplr simp-4r ad5antr simp-5r l1-mid-congruence-preserved syl1111anc ax-A4 nfth nfv pm3.3 exlimd mp2 exlimiiv expcom pm2.61dan ) ACBIZCDEFJZWAAWBAWACEBKZDFBKZLZWBAWCWDGHMWAWELZBEI ZCDBFJZWBWAWCWGWDWAWCWGWAWCBEBKWGCBEBNBEOPQRWFBCIB DBFJZWHWFCBWAWESTWDWIWAWCDFBUAUBBCDBFUCUDBECDFUEUD UFUGECUHUICUHDBJLZAWAUJZLZWBUKUHWLWJWBFDULUIDULCBJ LZWLWJLZWBUKULWMWNWLWMLZWJLZWBWMWLWOWJWMWLUMUNUHEU OUIEUODBJLZWPWBUKUOWQWPWLWQLZWMLZWJLZWBWQWOWSWJWQW LWRWMWQWLUMUNUNULFUPUIFUPCBJLZWTLZWBUKZXAUPUQWTWBU KZXBWLXALZWQWMWJWBXAXAWTWLXAURWLWQWMWJUSUTWTWQXAWL WQWMWJVAVBXAWRWMWJVCXAWSWJVDXEWQLZWMLZWJLUHULUOUPB CDEFXGWJVEXFWMWJVFXEWQWMWJVAWLXAWQWMWJVGAWCWKXAWQW MWJGVHAWDWKXAWQWMWJHVHAWKXAWQWMWJVIVJVKZUPFCBULVLX CXAXDUPXCUPXHVMXDUPVNXAWTWBVOVPVQPUOEDBUHVLVRPULDC BFVLVRVSUHCDBEVLVRVT $.
$}

${
    $( Theorem 7.13 of [SST]. $)
    mid-congruence-preserved
        $p |- ( ( Mid ( p m r ) /\ Mid ( q m s ) ) -> ( p q C r s ) )
        $= ( wffmid wa simpl simpr mid-congruence-preserved-d ) BDAFZCEAFZGABCDEKLHKLIJ $.
$}

mid-col
    $p |- ( Mid ( a b c ) -> Col ( a b c ) )
    $= ( wffmid df-mid-outro1 col-intro-1-d ) ACBDABCACBEF $.

${
    mid-col-d.1 $e |- ( ph -> Mid ( a b c ) ) $.
    mid-col-d
        $p |- ( ph -> Col ( a b c ) )
        $= ( wffmid wffcol mid-col syl ) ABDCFBCDGEBCDHI $.
$}

${
    congruence-preserves-mid-d.1 $e |- ( ph -> Mid ( a b c ) ) $.
    congruence-preserves-mid-d.2 $e |- ( ph -> ( a b c C3 a' b' c' ) ) $.
    congruence-preserves-mid-d
        $p |- ( ph -> Mid ( a' b' c' ) )
        $= ( wffmid wffbetw df-mid-outro1 syl betw-preserved-d wffcong wffcong3 cong3-elim1 cong-2143-d df-mid-outro2 cong3-elim2 cong-trans-d ax-A2 syl2anc df-mid-intro-d ) AEGFABCDEFGABDCJZBCDKHBDCLMINACBFEOCBFGOFEFGOABCEF ABCDEFGPZBCEFOIBCDEFGQMRACBCDFGAUECBCDOHBDCSMAUFCD FGOIBCDEFGTMUACBFEFGUBUCUD $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Orthogonality
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Declare RightAng symbol $)
$c RightAng $.

$( Extend wff notation to include RightAng $)
wffrightang $a wff RightAng ( a b c ) $.

$( Definition of a RightAng $)

${
$d a d $.
$d b d $.
$d c d $.
df-rightang $a |- ( RightAng ( a b c ) <-> E. d ( Mid ( c b d ) /\ ( a c C a d ) ) ) $.
$}

${
    $d a d $.
    $d b d $.
    $d c d $.
    df-rightang-outro
        $p |- ( RightAng ( a b c ) -> E. d ( Mid ( c b d ) /\ ( a c C a d ) ) )
        $= ( wffrightang wffmid wffcong wa wex df-rightang biimpi ) ABCECDBFACADGHDIABCDJK $.
$}

${
    $d a d $.
    $d b d $.
    $d c d $.
    df-rightang-intro
        $p |- ( E. d ( Mid ( c b d ) /\ ( a c C a d ) ) -> RightAng ( a b c ) )
        $= ( wffrightang wffmid wffcong wa wex df-rightang biimpri ) ABCECDBFACADGHDIABCDJK $.
$}

${
    $d b d $.
    $d c d $.
    $d d x $.
    $d d y $.
    predRightAng1
        $p |- ( x = y -> ( RightAng ( x b c ) -> RightAng ( y b c ) ) )
        $= ( weq wffrightang wa pointd wffmid wffcong wex df-rightang-outro adantl simprl simprr wi ax-predC1 ax-predC3 syld ad2antrr mpd jca 19.8ad df-rightang-intro syl exlimddv ex ) ABEZACDFZBCDFZUHUIGZDHCIZADAHJZGZUJHUIUNHKUHACDHLM UKUNGZULBDBHJZGZHKUJUOUQHUOULUPUKULUMNUOUMUPUKULUM OUHUMUPPUIUNUHUMBDAHJUPABDAHQABBDHRSTUAUBUCBCDHUDU EUFUG $.
$}

${
    $d a d $.
    $d c d $.
    $d d x $.
    $d d y $.
    $( Equality substitution axiom for the second term of the 'RightAng' predicate. $)
    predRightAng2
        $p |- ( x = y -> ( RightAng ( a x c ) -> RightAng ( a y c ) ) )
        $= ( weq wffrightang wa pointd wffmid wffcong wex df-rightang-outro adantl simpll simprl predM2 sylc simprr jca 19.8ad df-rightang-intro syl exlimddv ex ) ABEZCADFZCBDFZUEUFGZDHAIZCDCHJZGZUGHUFUKHKUECADHLM UHUKGZDHBIZUJGZHKUGULUNHULUMUJULUEUIUMUEUFUKNUHUIU JOABDHPQUHUIUJRSTCBDHUAUBUCUD $.
$}

${
    $d a d $.
    $d b d $.
    $d d x $.
    $d d y $.
    $( Equality substitution axiom for the third term of the 'RightAng' predicate. $)
    predRightAng3
        $p |- ( x = y -> ( RightAng ( a b x ) -> RightAng ( a b y ) ) )
        $= ( weq wffrightang wa pointd wffmid wffcong wex df-rightang-outro adantl simpll simprl predM1 sylc simprr ax-predC2 jca 19.8ad df-rightang-intro syl exlimddv ex ) ABEZCDAFZCDBFZUFUGGZAHDIZCACHJZGZUHHUGULHKUFCDAHLM UIULGZBHDIZCBCHJZGZHKUHUMUPHUMUNUOUMUFUJUNUFUGULNZ UIUJUKOABHDPQUMUFUKUOUQUIUJUKRABCCHSQTUACDBHUBUCUD UE $.
$}

${
    predRightAng1-d.1 $e |- ( ph -> RightAng ( x b c ) ) $.
    predRightAng1-d.2 $e |- ( ph -> x = y ) $.
    $( Deductive form of predRightAng1. $)
    predRightAng1-d
        $p |- ( ph -> RightAng ( y b c ) )
        $= ( weq wffrightang predRightAng1 sylc ) ABCHBDEICDEIGFBCDEJK $.
$}

${
    predRightAng2-d.1 $e |- ( ph -> RightAng ( a x c ) ) $.
    predRightAng2-d.2 $e |- ( ph -> x = y ) $.
    $( Deductive form of predRightAng1. $)
    predRightAng2-d
        $p |- ( ph -> RightAng ( a y c ) )
        $= ( weq wffrightang predRightAng2 sylc ) ABCHDBEIDCEIGFBCDEJK $.
$}

${
    predRightAng3-d.1 $e |- ( ph -> RightAng ( a b x ) ) $.
    predRightAng3-d.2 $e |- ( ph -> x = y ) $.
    $( Deductive form of predRightAng1. $)
    predRightAng3-d
        $p |- ( ph -> RightAng ( a b y ) )
        $= ( weq wffrightang predRightAng3 sylc ) ABCHDEBIDECIGFBCDEJK $.
$}

${
    $d a e $.
    $d b e $.
    $d c e $.
    $d d e $.
    rightang-symmetry.1 $e |- ( ph -> Mid ( c b d ) ) $.
    rightang-symmetry.2 $e |- ( ph -> ( a c C a d ) ) $.
    l1-rightang-symmetry-d
        $p |- ( ph -> RightAng ( c b a ) )
        $= ( pointe wffmid wffcong wa wex wffrightang mid-symmetry syl mid-outpoint-exists a1i 19.42v sylanbrc mid-congruence-preserved anim1i anabss3 eximi 19.41v an32 exbii sylib cong-4321 anim2i ancomd ax-A2 exancom df-rightang-intro ) ABHCIZDBDHJZKHLZDCBMAUOUNKZHLZUPAEBDBJZEBDHJZKZUNK ZHLZURAUTBDBEJZKZUNKZHLZVCAUTUNKZVDKZHLZVGAVHHLZVD VJAEDCIZUNKZHLZVKAVLUNHLZVNADECIVLFDECNOVOACBHPQVL UNHRSVMVHHVLUNVHVMUTUNCEBDHTUAUBUCOGVHVDHUDSVIVFHU TUNVDUEUFUGVFVBHVEVAUNVEUTUSVDUSUTBDBEUHUIUJUAUCOV BUQHVAUOUNEBDBDHUKUAUCOUOUNHULUGDCBHUMO $.
$}

l1-rightang-symmetry
    $p |- ( ( Mid ( c b d ) /\ ( a c C a d ) ) -> RightAng ( c b a ) )
    $= ( wffmid wffcong wa simpl simpr l1-rightang-symmetry-d ) CDBEZACADFZGABCDKLHKLIJ $.

${
    $d a d $.
    $d b d $.
    $d c d $.
    $( Theorem 8.2 of [SST] $)
    rightang-symmetry
        $p |- ( RightAng ( a b c ) -> RightAng ( c b a ) )
        $= ( wffrightang pointd wffmid wffcong wa wex df-rightang-outro l1-rightang-symmetry exlimiv syl ) ABCDCEBFACAEGHZEICBADZABCEJNOEABCEKLM $.
$}

${
    rightang-symmetry-d.1 $e |- ( ph -> RightAng ( a b c ) ) $.
    rightang-symmetry-d
        $p |- ( ph -> RightAng ( c b a ) )
        $= ( wffrightang rightang-symmetry syl ) ABCDFDCBFEBCDGH $.
$}

${
    $d a d $.
    $d b d $.
    $( Theorem 8.5 of [SST] $)
    rightang-identity
        $p |- RightAng ( a b b )
        $= ( pointd wffmid wffcong wa wex wffrightang weq ax6evr mid-identity2-converse cong-ref ax-predC4 mpi jca eximii df-rightang-intro ax-mp ) BCBDZABACEZFZCGABBHBCIZUACCBJUBSTBCKUBABABETABLBCA BAMNOPABBCQR $.
$}

${
    $d b e $.
    $d c e $.
    $d d e $.
    rightang-line.1 $e |- ( ph -> ( a c C a e ) ) $.
    rightang-line.4 $e |- ( ph -> Mid ( c b e ) ) $.
    rightang-line.2 $e |- ( ph -> -. a = b ) $.
    rightang-line.3 $e |- ( ph -> Col ( b a d ) ) $.
    l1-rightang-line-d
        $p |- ( ph -> RightAng ( d b c ) )
        $= ( wffmid wffcong wa wex wffrightang wffcol col-213 syl df-mid-outro2 line-cong-d jca 19.8ad df-rightang-intro ) ADFCKZEDEFLZMZFNECDOAUFFAUDUEHABCEDFIACBEPBCEPJCBE QRGAUDCDCFLHDFCSRTUAUBECDFUCR $.
$}

${
    $d ph e $.
    $d a e $.
    $d b e $.
    $d c e $.
    $d d e $.
    rightang-line-d.1 $e |- ( ph -> RightAng ( a b c ) ) $.
    rightang-line-d.2 $e |- ( ph -> -. a = b ) $.
    rightang-line-d.3 $e |- ( ph -> Col ( b a d ) ) $.
    $( If ABC is a right angle, all points on the line AB produce a right angle with respect to C. Theorem 8.3 of [SST]. $)
    rightang-line-d
        $p |- ( ph -> RightAng ( d b c ) )
        $= ( pointe wffmid wffcong wa wffrightang wex df-rightang-outro syl simprr simprl weq wn adantr wffcol l1-rightang-line-d exlimddv ) ADICJZBDBIKZLZECDMIABCDMUGINFBCDIOPAUGLBCDEIAUEUFQ AUEUFRABCSTUGGUAACBEUBUGHUAUCUD $.
$}

${
    $( Theorem 8.3 of [SST] $)
    rightang-line
        $p |- ( ( ( RightAng ( a b c ) /\ -. a = b ) /\ Col ( b a d ) ) -> RightAng ( d b c ) )
        $= ( wffrightang weq wn wa wffcol simpll simplr simpr rightang-line-d ) ABCEZABFGZHZBADIZHABCDNOQJNOQKPQLM $.
$}

${
    $d ph d $.
    $d a c d $.
    $d b c d $.
    $d c d e $.
    rightang-reflect-d.1 $e |- ( ph -> RightAng ( a b c ) ) $.
    rightang-reflect-d.2 $e |- ( ph -> Mid ( e b c ) ) $.
    $( Theorem 8.4 of [SST]. $)
    rightang-reflect-d
        $p |- ( ph -> RightAng ( a b e ) )
        $= ( pointd wffmid wffcong wa wffrightang wex df-rightang-outro syl adantr weq mid-symmetry simprl mid-outpoint-unique syl2anc equcomd simprr ax-predC4 sylc cong-sym-d jca 19.8ad df-rightang-intro exlimddv ) ADHCIZBDBHJZKZBCELZHABCDLUMHMFBCDHNOAUMKZEDCIZBEBD JZKZDMUNUOURDUOUPUQAUPUMGPZUOBDBEUOHEQULBDBEJUOEHU ODECIZUKEHQUOUPUTUSEDCROAUKULSDCEHTUAUBAUKULUCHEBD BUDUEUFUGUHBCEDUIOUJ $.
$}

${
    $d a c $.
    $d b c $.
    $d c e $.
    $( Theorem 8.4 of [SST]. $)
    rightang-reflect
        $p |- ( ( RightAng ( a b c ) /\ Mid ( e b c ) ) -> RightAng ( a b e ) )
        $= ( wffrightang wffmid wa simpl simpr rightang-reflect-d ) ABCEZDCBFZGABCDKLHKLIJ $.
$}

${
    l1-rightang-between-d.1 $e |- ( ph -> Mid ( c b p ) ) $.
    l1-rightang-between-d.3 $e |- ( ph -> Mid ( c b q ) ) $.
    l1-rightang-between-d.2 $e |- ( ph -> ( a c C a p ) ) $.
    l1-rightang-between-d.4 $e |- ( ph -> ( d c C d q ) ) $.
    l1-rightang-between-d.5 $e |- ( ph -> ( B a c d ) ) $.
    l1-rightang-between-d
        $p |- ( ph -> b = c )
        $= ( weq wffbetw wffcong wffmid mid-outpoint-unique syl2anc equcomd ax-predC4 sylc distance-uniq-corollary syl21anc predM1 mid-identity syl equeuclr ) ADFMZCFMZCDMABDENEDEFOZBDBFOUHLAGFMEDEGOUJAFGADFCP ZDGCPFGMHIDCFGQRSKGFEDETUAJEBDFUBUCZAFFCPZUIAUHUKU MULHDFFCUDUAFCUEUFDCFUGUA $.
$}

${
    $d d q $.
    $d ph p q $.
    $d a p q $.
    $d b p q $.
    $d c p q $.
    rightang-between-d.2 $e |- ( ph -> RightAng ( a b c ) ) $.
    rightang-between-d.3 $e |- ( ph -> RightAng ( d b c ) ) $.
    rightang-between-d.1 $e |- ( ph -> ( B a c d ) ) $.
    $( Deductive form of rightang-between. $)
    rightang-between-d
        $p |- ( ph -> b = c )
        $= ( pointp wffmid wffcong wa weq wffrightang wex df-rightang-outro syl pointq adantr simprll simprrl simprlr simprrr wffbetw l1-rightang-between-d anassrs exlimddv ) ADICJZBDBIKZLZCDMZIABCDNUJIOFBCDIPQAUJLDRCJZEDERKZ LZUKRAUNROZUJAECDNUOGECDRPQSAUJUNUKAUJUNLZLBCDEIRA UHUIUNTAUJULUMUAAUHUIUNUBAUJULUMUCABDEUDUPHSUEUFUG UG $.
$}

${
    $( Theorem 8.6 of [SST]. $)
    rightang-between
        $p |- ( ( ( RightAng ( a b c ) /\ RightAng ( d b c ) ) /\ ( B a c d ) ) -> b = c )
        $= ( wffrightang wa wffbetw simpll simplr simpr rightang-between-d ) ABCEZDBCEZFZACDGZFABCDLMOHLMOINOJK $.
$}

${
    $d ph p $.
    $d a p $.
    $d b c' p $.
    $d c c' p $.
    $d a' c' p $.
    l1-rightang-equality-d.5 $e |- ( ph -> Mid ( a c a' ) ) $.
    l1-rightang-equality-d.6 $e |- ( ph -> Mid ( c b c' ) ) $.
    l1-rightang-equality-d.1 $e |- ( ph -> RightAng ( a b c ) ) $.
    l1-rightang-equality-d.2 $e |- ( ph -> RightAng ( a c b ) ) $.
    $( Lemma for rightang-equality. $)
    l1-rightang-equality-d
        $p |- ( ph -> b = c )
        $= ( weq wn wa wffrightang adantr wffmid wffcong wex simpl df-mid-outro2 3syl cong-2143-d pointp df-rightang-outro syl simprl mid-outpoint-unique syl2anc simprr ax-predC4 sylc exlimddv rightang-symmetry-d simpr mid-col-d rightang-line-d ad2antrr cong-trans-d ax-A2 jca 19.8ad df-rightang-intro wffbetw df-mid-outro1 rightang-between-d pm2.18da ) ACDKZAVGLZMZBCDEABCDNZVHIOZVIDFCPZEDEFQZMZFRECDNVI VNFVIVLVMAVLVHHOZVIBDEDQBDEFQVMVIDBDEVIABEDPZDBDEQ AVHSGBEDTUAUBVIBDBFEFVIDUCCPZBDBUCQZMZBDBFQZUCVIVJ VSUCRVKBCDUCUDUEVIVSMZUCFKZVRVTWAVQVLWBVIVQVRUFVIV LVSVOODCUCFUGUHVIVQVRUIUCFBDBUJUKULVIFBFEVIBUCDPZF BFUCQZMZFBFEQZUCVIFDBNWEUCRVICDBFVIBDCABDCNVHJOUMA VHUNVIDCFVOUOUPFDBUCUDUEVIWEMZUCEKZWDWFWGWCVPWHVIW CWDUFAVPVHWEGUQBDUCEUGUHVIWCWDUIUCEFBFUJUKULUBURBD EDEFUSUHUTVAECDFVBUEVIVPBDEVCAVPVHGOBEDVDUEVEVF $.
$}

${
    $d a a' $.
    $d ph a' c' $.
    $d a' b c' $.
    $d a' c c' $.
    rightang-equality-d.1 $e |- ( ph -> RightAng ( a b c ) ) $.
    rightang-equality-d.2 $e |- ( ph -> RightAng ( a c b ) ) $.
    $( Deductive form of rightang-equality. $)
    rightang-equality-d
        $p |- ( ph -> b = c )
        $= ( pointc' wffmid weq wex mid-outpoint-exists a1i wa pointa' wi simpl simpr simplr wffrightang ad2antrr l1-rightang-equality-d ex exlimdv embantd mpi exlimddv ) ADGCHZCDIZGUGGJACDGKLAUGMZABNDHZNJZOUHUKADBNKLUIAU KUHAUGPUIUJUHNUIUJUHUIUJMBCDNGUIUJQAUGUJRABCDSUGUJ ETABDCSUGUJFTUAUBUCUDUEUF $.
$}

${
    $( Theorem 8.7 of [SST]. $)
    rightang-equality
        $p |- ( ( RightAng ( a b c ) /\ RightAng ( a c b ) ) -> b = c )
        $= ( wffrightang wa simpl simpr rightang-equality-d ) ABCDZACBDZEABCIJFIJGH $.
$}

${
    rightang-identity2-d.1 $e |- ( ph -> RightAng ( a b a ) ) $.
    $( Deductive form of rightang-identity2 $)
    rightang-identity2-d
        $p |- ( ph -> a = b )
        $= ( wffrightang rightang-identity a1i rightang-symmetry-d rightang-equality-d ) ABBCACBBCBBEACBFGHDI $.
$}

${
    $( Theorem 8.8 of [SST]. $)
    rightang-identity2
        $p |- ( RightAng ( a b a ) -> a = b )
        $= ( wffrightang id rightang-identity2-d ) ABACZABFDE $.
$}

${
    rightang-colinear-equality-d.1 $e |- ( ph -> RightAng ( a b c ) ) $.
    rightang-colinear-equality-d.2 $e |- ( ph -> Col ( a b c ) ) $.
    $( Deductive form of rightang-colinear-equality. $)
    rightang-colinear-equality-d
        $p |- ( ph -> ( a = b \/ b = c ) )
        $= ( weq wo animorrl wn wa wffrightang adantr simpr wffcol col-213 syl rightang-line-d wffbetw betw-id a1i rightang-between-d olcd pm2.61dan ) ABCGZUECDGZHAUEUFIAUEJZKZUFUEUHDCDDUHBCDDABCDLUGEM AUGNUHBCDOZCBDOAUIUGFMBCDPQRZUJDDDSUHDDTUAUBUCUD $.
$}

${
    $( Theorem 8.9 of [SST]. $)
    rightang-colinear-equality
        $p |- ( ( RightAng ( a b c ) /\ Col ( a b c ) ) -> ( a = b \/ b = c ) )
        $= ( wffrightang wffcol wa simpl simpr rightang-colinear-equality-d ) ABCDZABCEZFABCJKGJKHI $.
$}

${
    $d a p $.
    $d a' d d' $.
    $d ph d d' p $.
    $d b d d' p $.
    $d c d d' p $.
    $d b' d d' p $.
    $d c' d d' p $.
    congruence-preserves-rightang-d.1 $e |- ( ph -> RightAng ( a b c ) ) $.
    congruence-preserves-rightang-d.2 $e |- ( ph -> ( a b c C3 a' b' c' ) ) $.
    $( Deductive form of congruence-preserves-rightang. $)
    congruence-preserves-rightang-d
        $p |- ( ph -> RightAng ( a' b' c' ) )
        $= ( weq wffrightang wa rightang-identity a1i wffcong simpr equcomd wffcong3 adantr cong3-elim2 syl ax-predC2 sylc cong-nullseg-sym predRightAng3-d wn pointd wffmid wex mid-outpoint-exists pointd' wffofsc wffbetw df-mid-outro1 ad2antlr adantl ad2antrr cong-2143-d df-mid-outro2 ax-A2 syl2anc cong3-elim3 cong3-elim1 ofsc-intro-d simpllr equcomi nsyl ax-A5-alt pointp df-rightang-outro simprl mid-outpoint-unique simprr ax-predC4 exlimddv cong-sym-d jca 19.8ad df-rightang-intro pm2.61dan ) ACDJZEFGKZAWALZFGEFEFFKWCEFMNWCCCFGOZFGJWCDCJZCDFG OZWDWCCDAWAPQWCBCDEFGRZWFAWGWAISBCDEFGTZUADCCFGUBU CFGCUDUAUEAWAUFZLZDUGCUHZWBUGWKUGUIWJCDUGUJNWJWKLZ GUKFUHZWBUKWMUKUIWLFGUKUJNWLWMLZWMEGEUKOZLZUKUIWBW NWPUKWNWMWOWLWMPWNEUKEGWNBUGEUKOBUGEGOZEUKEGOWNUGB UKEWNDCUGBGFUKEULWEUFUGBUKEOWNDCUGBGFUKEWKDCUGUMWJ WMDUGCUNUOWMGFUKUMWLGUKFUNUPWNCDFGWJWFWKWMWJWGWFAW GWIISZWHUAUQZURWNFGCUGOZFGFUKOZCUGFUKOWNWFCDCUGOZW TWSWKXBWJWMDUGCUSUOCDFGCUGUTVAWMXAWLGUKFUSUPFGCUGF UKUTVAWNBDEGWNWGBDEGOZWJWGWKWMWRUQZBCDEFGVBUAZURWN BCEFWNWGBCEFOXDBCDEFGVCUAURVDWNWAWEAWIWKWMVEDCVFVG DCUGBGFUKEVHVAURWNBDBUGOZXCWQWNDVICUHZBDBVIOZLZXFV IWNBCDKZXIVIUIWJXJWKWMAXJWIHSUQBCDVIVJUAWNXILZVIUG JZXHXFXKXGWKXLWNXGXHVKWJWKWMXIVEDCVIUGVLVAWNXGXHVM VIUGBDBVNUCVOXEBDBUGEGUTVABUGEUKEGUTVAVPVQVREFGUKV SUAVOVOVT $.
$}

${
    $( Theorem 8.10 of [SST]. $)
    congruence-preserves-rightang
        $p |- ( ( RightAng ( a b c ) /\ ( a b c C3 a' b' c' ) ) -> RightAng ( a' b' c' ) )
        $= ( wffrightang wffcong3 wa simpl simpr congruence-preserves-rightang-d ) ABCGZABCDEFHZIABCDEFMNJMNKL $.
$}

$( Declare PerpAt symbol $)
$c PerpAt $.

$( Extend wff notation to include PerpAt $)
wffperpat $a wff PerpAt ( a b c d x ) $.

$( Two lines 'ab' and 'cd' are perpendicular and intersect at 'x' $)
df-perpat $a |- ( PerpAt ( a b c d x ) <-> ( ( ( ( -. a = b /\ -. c = d ) /\ Col ( a b x ) ) /\ Col ( c d x ) ) /\ ( ( Col ( u a b ) /\ Col ( v c d ) ) -> RightAng ( u x v ) ) ) ) $.

perpat-outro
    $p |- ( PerpAt ( a b c d x ) -> ( ( ( ( -. a = b /\ -. c = d ) /\ Col ( a b x ) ) /\ Col ( c d x ) ) /\ ( ( Col ( u a b ) /\ Col ( v c d ) ) -> RightAng ( u x v ) ) ) )
    $= ( wffperpat weq wn wa wffcol wffrightang wi df-perpat biimpi ) ADEFGHDEIJFGIJKDEALKFGALKCDELBFGLKCABMNKABCDEFGOP $.

${
    perpat-outro.1 $e |- ( ph -> PerpAt ( a b c d x ) ) $.
    perpat-outro1
        $p |- ( ph -> -. a = b )
        $= ( wffperpat weq wn wa wffcol vu vv wffrightang wi perpat-outro simp-4l syl ) ABCDEFHZCDIJZGTUAEFIJZKCDBLZKEFBLZKMCDLNEFLKMBNOPZ KUABNMCDEFQUAUBUCUDUERSS $.
$}

${
    perpat-outro.1 $e |- ( ph -> PerpAt ( a b c d x ) ) $.
    perpat-outro2
        $p |- ( ph -> -. c = d )
        $= ( wffperpat weq wn wa wffcol vu vv wffrightang wi perpat-outro simp-4r syl ) ABCDEFHZEFIJZGTCDIJZUAKCDBLZKEFBLZKMCDLNEFLKMBNOPZ KUABNMCDEFQUBUAUCUDUERSS $.
$}

${
    perpat-outro.1 $e |- ( ph -> PerpAt ( a b c d x ) ) $.
    perpat-outro3
        $p |- ( ph -> Col ( a b x ) )
        $= ( wffperpat wffcol weq wn wa vu vv wffrightang wi perpat-outro simpllr syl ) ABCDEFHZCDBIZGTCDJKEFJKLZUALEFBIZLMCDINEFILMBNOPZL UABNMCDEFQUBUAUCUDRSS $.
$}

${
    perpat-outro.1 $e |- ( ph -> PerpAt ( a b c d x ) ) $.
    perpat-outro4
        $p |- ( ph -> Col ( c d x ) )
        $= ( wffperpat wffcol weq wn wa vu vv wffrightang wi perpat-outro simplrd syl ) ABCDEFHZEFBIZGTCDJKEFJKLCDBILUAMCDINEFILMBNOPBNMCD EFQRS $.
$}

${
    perpat-outro.1 $e |- ( ph -> PerpAt ( a b c d x ) ) $.
    perpat-outro5
        $p |- ( ph -> ( ( Col ( u a b ) /\ Col ( v c d ) ) -> RightAng ( u x v ) ) )
        $= ( wffperpat wffcol wa wffrightang wi weq wn perpat-outro simprd syl ) ABEFGHJZDEFKCGHKLDBCMNZITEFOPGHOPLEFBKLGHBKLUABCDE FGHQRS $.
$}

perpat-intro
    $p |- ( ( ( ( ( -. a = b /\ -. c = d ) /\ Col ( a b x ) ) /\ Col ( c d x ) ) /\ ( ( Col ( u a b ) /\ Col ( v c d ) ) -> RightAng ( u x v ) ) ) -> PerpAt ( a b c d x ) )
    $= ( wffperpat weq wn wa wffcol wffrightang wi df-perpat biimpri ) ADEFGHDEIJFGIJKDEALKFGALKCDELBFGLKCABMNKABCDEFGOP $.

${
    perpat-intro-d.5 $e |- ( ph -> -. a = b ) $.
    perpat-intro-d.1 $e |- ( ph -> -. c = d ) $.
    perpat-intro-d.2 $e |- ( ph -> Col ( a b x ) ) $.
    perpat-intro-d.3 $e |- ( ph -> Col ( c d x ) ) $.
    perpat-intro-d.4 $e |- ( ph -> ( ( Col ( u a b ) /\ Col ( v c d ) ) -> RightAng ( u x v ) ) ) $.
    perpat-intro-d
        $p |- ( ph -> PerpAt ( a b c d x ) )
        $= ( weq wn wa wffcol wffrightang wi wffperpat jca df-perpat syl21anbrc ) AEFNOZGHNOZPZEFBQZPGHBQDEFQCGHQPDBCRSBEFGHTAUFUGAU DUEIJUAKUALMBCDEFGHUBUC $.
$}

${
    perpat-symmetry.1 $e |- ( ph -> PerpAt ( a b c d x ) ) $.
    perpat-symmetry-d
        $p |- ( ph -> PerpAt ( c d a b x ) )
        $= ( vu vv perpat-outro2 perpat-outro1 perpat-outro4 perpat-outro3 wffcol wa wffrightang perpat-outro5 ancomsd rightang-symmetry syl6 perpat-intro-d ) ABHIEFCDABCDEFGJABCDEFGKABCDEFGLABCDEFGMAIEFNZHCDN ZOHBIPZIBHPAUCUBUDABIHCDEFGQRHBISTUA $.
$}

${
    $( Theorem 8.12 of [SST] $)
    perpat-symmetry
        $p |- ( PerpAt ( a b c d x ) -> PerpAt ( c d a b x ) )
        $= ( wffperpat id perpat-symmetry-d ) ABCDEFZABCDEIGH $.
$}

$( Declare Perp symbol $)
$c Perp $.

$( Extend wff notation to include Perp $)
wffperp $a wff Perp ( a b c d ) $.

$( Two lines 'ab' and 'cd' are perpendicular. $)
df-perp $a |- ( Perp ( a b c d ) <-> E. x PerpAt ( a b c d x ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Circles
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Declare OnCircle symbol $)
$c OnCircle $.

$( Extend wff notation to include Mid $)
wffonc $a wff OnCircle ( p o r ) $.

$( A point 'p' is on the circle with center 'o' and radius 'r'. $)
df-oncirc $a |- ( OnCircle ( p o r ) <-> ( o p C o r ) ) $.

df-oncircle-intro
    $p |- ( ( a p C a b ) -> OnCircle ( p a b ) )
    $= ( wffonc wffcong df-oncirc biimpri ) ABCDACABEABCFG $.

df-oncircle-outro
    $p |- ( OnCircle ( p a b ) -> ( a p C a b ) )
    $= ( wffonc wffcong df-oncirc biimpi ) ABCDACABEABCFG $.

oncircle-identity
    $p |- OnCircle ( b a b )
    $= ( wffonc wffcong cong-ref df-oncirc mpbir ) ABBCABABDABEABBFG $.

oncircle-symmetry
    $p |- ( OnCircle ( p a b ) -> OnCircle ( b a p ) )
    $= ( wffcong wffonc cong-sym df-oncirc 3imtr4i ) ACABDABACDABCEACBEACABFABCGACBGH $.

$( Declare IsChord symbol $)
$c IsChord $.

$( Extend wff notation to include Mid $)
wffischord $a wff IsChord ( a b o r ) $.

$( A segment 'ab' is a chord of circle with center 'o' and radius 'r' if both 'a' and 'b' are on the circle. $)
df-ischord $a |- ( IsChord ( a b o r ) <-> ( OnCircle ( a o r ) /\ OnCircle ( b o r ) ) ) $.
