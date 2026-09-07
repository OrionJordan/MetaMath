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
$v a b c d e f g h i j k p q r s $.

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
pointp $f setvar p $.
pointq $f setvar q $.
pointr $f setvar r $.
points $f setvar s $.

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
        $= ( wffU0 weq wffcong U0imp congnullseg ax-predC2 mpisyl ax-predC4 sylc ) EZCDFABCCGZABCDGCDHNABFAACCGOABHACIABACCJKCDABCLM $.
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

congref $p |- ( a b C a b )
    $= ( wffcong ax-A1 ax-A2 mp2an ) BAABCZGABABCBADZHBAABABEF $.

${
    congsymi.1 $e |- ( a b C c d ) $.
    congsymi $p |- ( c d C a b )
        $= ( wffcong congref ax-A2 mp2an ) ABCDFABABFCDABFEABGABCDABHI $.
$}

${
    congsymd.1 $e |- ( ph -> ( a b C c d ) ) $.
    congsymd
        $p |- ( ph -> ( c d C a b ) )
        $= ( wffcong wa congref jctir ax-A2 syl ) ABCDEGZBCBCGZHDEBCGAMNFBCIJBCDEBCKL $.
$}

congsym $p |- ( ( a b C c d ) -> ( c d C a b ) )
    $= ( wffcong congref ax-A2 mpan2 ) ABCDEABABECDABEABFABCDABGH $.

congtrans $p |- ( ( ( a b C c d ) /\ ( c d C e f ) ) -> ( a b C e f ) )
    $= ( wffcong congsym ax-A2 sylan ) ABCDGCDABGCDEFGABEFGABCDHCDABEFIJ $.

${
    cong-trans-d.1 $e |- ( ph -> ( a b C c d ) ) $.
    cong-trans-d.2 $e |- ( ph -> ( c d C e f ) ) $.
    cong-trans-d
        $p |- ( ph -> ( a b C e f ) )
        $= ( wffcong wa jca congtrans syl ) ABCDEJZDEFGJZKBCFGJAOPHILBCDEFGMN $.
$}

${
    cong-trans-d2.1 $e |- ( ph -> ( ( a b C c d ) /\ ( c d C e f ) ) ) $.
    cong-trans-d2
        $p |- ( ph -> ( a b C e f ) )
        $= ( wffcong simpld simprd cong-trans-d ) ABCDEFGABCDEIZDEFGIZHJAMNHKL $.
$}

conglhs $p |- ( ( a b C c d ) -> ( b a C c d ) )
    $= ( wffcong ax-A1 ax-A2 mpan ) ABBAEABCDEBACDEABFABBACDGH $.

${
    conglhs-d.1 $e |- ( ph -> ( a b C c d ) ) $.
    conglhs-d
        $p |- ( ph -> ( b a C c d ) )
        $= ( wffcong conglhs syl ) ABCDEGCBDEGFBCDEHI $.
$}

congrhs $p |- ( ( a b C c d ) -> ( a b C d c ) )
    $= ( wffcong ax-A1 congtrans mpan2 ) ABCDECDDCEABDCECDFABCDDCGH $.

cong_2143
    $p |- ( ( a b C c d ) -> ( b a C d c ) )
    $= ( wffcong conglhs congrhs syl ) ABCDEBACDEBADCEABCDFBACDGH $.

${
    cong-2143-d.1 $e |- ( ph -> ( a b C c d ) ) $.
    cong-2143-d
        $p |- ( ph -> ( b a C d c ) )
        $= ( wffcong cong_2143 syl ) ABCDEGCBEDGFBCDEHI $.
$}

cong_3421
    $p |- ( ( a b C c d ) -> ( c d C b a ) )
    $= ( wffcong congsym congrhs syl ) ABCDECDABECDBAEABCDFCDABGH $.

cong_4312
    $p |- ( ( a b C c d ) -> ( d c C a b ) )
    $= ( wffcong congsym conglhs syl ) ABCDECDABEDCABEABCDFCDABGH $.

${
    cong-4312-d.1 $e |- ( ph -> ( a b C c d ) ) $.
    cong-4312-d
        $p |- ( ph -> ( d c C a b ) )
        $= ( wffcong cong_4312 syl ) ABCDEGEDBCGFBCDEHI $.
$}

cong_4321
    $p |- ( ( a b C c d ) -> ( d c C b a ) )
    $= ( wffcong congsym conglhs congrhs 3syl ) ABCDECDABEDCABEDCBAEABCDFCDABGDCABHI $.

${
    $d a x $.
    $d b x $.
    congnullseg
        $p |- ( a a C b b )
        $= ( vx wffcong weq wi ax-A3 equcomi ax-predC2 3syl pm2.43i wffbetw wa wex ax-A4 exsimpr ax-mp exlimiiv ) ACBBDZAABBDZCSTSACECAESTFACBGACHCAABBIJKBACLZSMCNS CNCABBBOUASCPQR $.
$}

congnullsegsym
    $p |- ( ( c c C a b ) -> a = b )
    $= ( wffcong weq congsym ax-A3 syl ) CCABDABCCDABECCABFABCGH $.

$( Declare OFSC symbol $)
$c OFSC $.


$( Extend wff notation to include outer five-segment configuration $)
wffafs $a wff OFSC ( a b c d e f g h ) $.

df-afs $a |- ( OFSC ( a b c d e f g h ) <-> ( ( ( ( ( ( B a b c ) /\ ( B e f g ) ) /\ ( a b C e f )  ) /\ ( b c C f g ) ) /\ ( a d C e h ) ) /\ ( b d C f h ) ) ) $.

${
    ofsc-intro.1 $e |- ( ph -> ( B a b c ) ) $.
    ofsc-intro.2 $e |- ( ph -> ( B e f g ) ) $.
    ofsc-intro.3 $e |- ( ph -> ( a b C e f ) ) $.
    ofsc-intro.4 $e |- ( ph -> ( b c C f g ) ) $.
    ofsc-intro.5 $e |- ( ph -> ( a d C e h ) ) $.
    ofsc-intro.6 $e |- ( ph -> ( b d C f h ) ) $.
    $( Introduce the Outer-Five-Segment-Congruence predicate $)
    ofsc-intro
        $p |- ( ph -> OFSC ( a b c d e f g h ) )
        $= ( wffbetw wa wffcong wffafs jca df-afs sylibr ) ABCDPZFGHPZQZBCFGRZQZCDGHRZQZBEFIRZQZCEGIRZQBCDEFG HISAUKULAUIUJAUGUHAUEUFAUCUDJKTLTMTNTOTBCDEFGHIUAU B $.
$}

ax5alt
    $p |- ( ( OFSC ( a b c d e f g h ) /\ -. a = b ) -> ( c d C g h ) )
    $= ( wffafs wffbetw wa wffcong weq wn df-afs ax-A5 sylanb ) ABCDEFGHIABCJEFGJKABEFLKBCFGLKADEHLKBDFHLKABMNCDGH LABCDEFGHOABCDEFGHPQ $.

${
    $( Segment Addition. Theorem 2.11 of [SST] First 14 lines rearrange conjuncts and deduce that not a=b proves the theorem. Next fiftenn lines build the theorem from a = b. $)
    segment_addition
        $p |- ( ( ( ( ( B a b c ) /\ ( B e f g ) ) /\ ( a b C e f ) ) /\ ( b c C f g ) ) -> ( a c C e g ) )
        $= ( weq wffbetw wa wffcong wi equcomi ax-predC2 equcoms congsym syl6 ax-A3 ax-predC3 imim12i mpsylsyld ax-predC1 syl6d adantld impd wn cong_2143 ad3antlr congnullseg ax-A5 an42ds mpan2 mpdan syl expcom pm2.61i ) ABGZABCHDEFHIZABDEJZIZBCEFJZIZACDFJZKUPUSUTVBUPURU TVBKUQUPURUTBCDFJZVBDEGZEDGZKUPURDEAAJZUTVCKZDELUP URAADEJZVFURVHKBABAADEMNAADEOPVFVDVEVGDEAQEDBCFRST VCVBKBABACDFUANUBUCUDVAUPUEZVBVAVIIZCAFDJZVBVJBAED JZVKURVLUQUTVIABDEUFUGVJVLIAADDJZVKADUHVAVMVLVIVKA BCADEFDUIUJUKULCAFDUFUMUNUO $.
$}

${
    segment_additiond.1 $e |- ( ph -> ( B a b c ) ) $.
    segment_additiond.2 $e |- ( ph -> ( B e f g ) ) $.
    segment_additiond.3 $e |- ( ph -> ( a b C e f ) ) $.
    segment_additiond.4 $e |- ( ph -> ( b c C f g ) ) $.
    segment_additiond
        $p |- ( ph -> ( a c C e g ) )
        $= ( wffbetw wffcong segment_addition syl1111anc ) ABCDLEFGLBCEFMCDFGMBDEGMHIJKBCDEFGNO $.
$}

${
    $( Segment Uniqueness. First 10 steps prove ax = az. Next four prove qx=qz. Steps 17 below show x = z implies A5 $)
    unique-segcon
        $p |- ( -. q = a -> ( ( ( ( B q a x ) /\ ( a x C b c ) ) /\ ( ( B q a z ) /\ ( a z C b c ) ) ) -> x = z ) )
        $= ( wffcong wi weq wn wffbetw wa congsym simpll jca congref jctir jctr ad2ant2r an3 ancom1s anim12i ax-A2 3syl segment_addition syl ax-A5 expcom syl5 ax-A3 imim2i mpsylsyld ) AAABGZABAAGZHFCIJZFCAKZCADEGZLFCBKZCBDEGZLZLZUMABI ZAAABMVAUPUPLZFCFCGZLZCACAGZLZFAFBGZLZCACBGZLZUOUM VAVIVJVAVGVHVAVEVFVAVCVDVAUPUPUPUQUTNZVLOFCPZQCAPQ VAUPURLZVDLZVJLVHVAVOVJUPURVOUQUSVNVDVMRSVAUQUSLZD ECAGZDECBGZLVJUQUPUTVPUQUPURUSTUAUQVQUSVRCADEMCBDE MUBDECACBUCUDZOFCAFCBUEUFOVSOVKUOUMFCAAFCABUGUHUIU NVBUMABAUJUKUL $.
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
    $= ( wffcong weq wn wi congsym cong-diff syl ) ABCDECDABECDFGABFGHABCDICDABJK $.

cong-a2sym
    $p |- ( ( ( p q C a b ) /\ ( r s C a b ) ) -> ( p q C r s ) )
    $= ( wffcong congsym ax-A2 syl2an ) CDABGABCDGABEFGCDEFGEFABGCDABHEFABHABCDEFIJ $.

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
    betw-symd.1 $e |- ( ph -> ( B a b c ) ) $.
    betw-symd
        $p |- ( ph -> ( B c b a ) )
        $= ( wffbetw betw-sym syl ) ABCDFDCBFEBCDGH $.
$}

betw-id2
    $p |- ( B a a b )
    $= ( wffbetw betw-id betw-sym ax-mp ) BAACAABCBADBAAEF $.

${
    $d a x $.
    $d b x $.
    btwn-swap
        $p |- ( ( ( B a b c ) /\ ( B b a c ) ) -> a = b )
        $= ( wffbetw wa vx wex weq ax-A7 ax-A6 anim12i equtr2 syl exlimiv equcomd ) ABCDBACDEZBAPBFBDZAFADZEZFGBAHZFABCBAISTFSBFHZAFHZ ETQUARUBBFJAFJKBAFLMNMO $.
$}

${
    $d a x $.
    $d b x $.
    $d c x $.
    betw-intr1
        $p |- ( ( ( B a b d ) /\ ( B b c d ) ) -> ( B a b c ) )
        $= ( wffbetw wa vx wex ax-A7 weq wi ax-A6 adantr equcomi ax-predB2 adantld 3syl pm2.43i exlimiv betw-sym ) ABDEBCDEFBGBEZCGAEZFZGHCBAEZABCEGABDBCIUCUDGUCUDUC BGJZGBJZUCUDKUAUEUBBGLMBGNUFUBUDUAGBCAOPQRSCBATQ $.
$}

betw-exch1
    $p |- ( ( ( B a b c ) /\ ( B a c d ) ) -> ( B b c d ) )
    $= ( wffbetw wa betw-sym anim12ci betw-intr1 3syl ) ABCEZACDEZFDCAEZCBAEZFDCBEBCDEKNLMABCGACDGHDCBAIDC BGJ $.

${
    betw-241-d.1 $e |- ( ph -> ( B a b c ) ) $.
    betw-241-d.2 $e |- ( ph -> ( B a c d ) ) $.
    betw-241-d
        $p |- ( ph -> ( B b c d ) )
        $= ( wffbetw betw-exch1 syl2anc ) ABCDHBDEHCDEHFGBCDEIJ $.
$}

betw-exch1sym
    $p |- ( ( ( B a b c ) /\ ( B a c d ) ) -> ( B d c b ) )
    $= ( wffbetw wa betw-exch1 betw-sym syl ) ABCEACDEFBCDEDCBEABCDGBCDHI $.

${
    betw-241-d.1 $e |- ( ph -> ( B a b c ) ) $.
    betw-241-d.2 $e |- ( ph -> ( B a c d ) ) $.
    betw-241-sym-d
        $p |- ( ph -> ( B d c b ) )
        $= ( wffbetw betw-exch1sym syl2anc ) ABCDHBDEHEDCHFGBCDEIJ $.
$}

${
    $d ph x $.
    $d a x $.
    $d c x $.
    $d d x $.
    betw-outd.1 $e |- ( ph -> ( B a b c ) ) $.
    betw-outd.2 $e |- ( ph -> ( B b c d ) ) $.
    betw-outd.3 $e |- ( ph -> -. b = c ) $.
    betw-outd
        $p |- ( ph -> ( B a c d ) )
        $= ( vx wffbetw wffcong wa wex ax-A4 a1i weq wi betw-exch1 ex anim1d syl congref jctir jctird wn unique-segcon syld ax-predB3 adantrd syl6 pm2.43d exlimdv mpd ) ABDIJZDIDEKZLZIMZBDEJZUQAIDDEBNOAUPURIAUPURAUPIEPZ UPURQAUPCDIJZUOLZCDEJZDEDEKZLZLZUSAUPVAVDABCDJZUPV AQFVFUNUTUOVFUNUTBCDIRSTUAAVBVCGDEUBUCUDACDPUEVEUS QHIEDDECUFUAUGUSUNURUOIEBDUHUIUJUKULUM $.
$}

${
    $( Theorem 3.7(1) of [SST]. $)
    betw-out
        $p |- ( ( ( ( B a b c ) /\ ( B b c d ) ) /\ -. b = c ) -> ( B a c d ) )
        $= ( wffbetw wa weq wn simpll simplr simpr betw-outd ) ABCEZBCDEZFZBCGHZFABCDMNPIMNPJOPKL $.
$}

${
    $( Theorem 3.5(2) of [SST] $)
    betw-exch2
        $p |- ( ( ( B a b d ) /\ ( B b c d ) ) -> ( B a c d ) )
        $= ( weq wffbetw wa wi ax-predB2 adantrd wn betw-intr1 anim1i anabss3 betw-out sylan expcom pm2.61i ) BCEZABDFZBCDFZGZACDFZHSTUCUABCADIJUBSKZUCUBABCFZUA GZUDUCTUAUFUBUEUAABCDLMNABCDOPQR $.
$}

${
    betw-132-d.1 $e |- ( ph -> ( B b c d ) ) $.
    betw-132-d.2 $e |- ( ph -> ( B a b d ) ) $.
    betw-132-d
        $p |- ( ph -> ( B a c d ) )
        $= ( wffbetw betw-exch2 syl2anc ) ABCEHCDEHBDEHGFBCDEIJ $.
$}

${
    $( Theorem 3.6(2) of [SST] $)
    betw-ep2
        $p |- ( ( ( B a b c ) /\ ( B a c d ) ) -> ( B a b d ) )
        $= ( wffbetw wa betw-sym anim12ci betw-exch2 3syl ) ABCEZACDEZFDCAEZCBAEZFDBAEABDEKNLMABCGACDGHDCBAIDB AGJ $.
$}

${
    betw-243-d.1 $e |- ( ph -> ( B a c d ) ) $.
    betw-243-d.2 $e |- ( ph -> ( B a b c ) ) $.
    betw-243-d
        $p |- ( ph -> ( B a b d ) )
        $= ( wffbetw betw-ep2 syl2anc ) ABCDHBDEHBCEHGFBCDEIJ $.
$}

${
    $( Theorem 3.7(2) of [SST] $)
    betw-outtr
        $p |- ( ( ( ( B a b c ) /\ ( B b c d ) ) /\ -. b = c ) -> ( B a b d ) )
        $= ( wffbetw wa weq wn betw-sym anim12ci equcomi con3i anim12i betw-out 3syl ) ABCEZBCDEZFZBCGZHZFDCBEZCBAEZFZCBGZHZFDBAEABDERUCT UEPUBQUAABCIBCDIJUDSCBKLMDCBANDBAIO $.
$}

betw-equality
    $p |- ( ( ( B a b c ) /\ ( B a c b ) ) -> b = c )
    $= ( wffbetw wa weq betw-exch1 ax-A6 syl ) ABCDACBDEBCBDBCFABCBGBCHI $.

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
        $= ( vx wffbetw wa wex betw-sym syl ax-A7 syl2anc wi adantll expcom imp betw-exch2 ex ad2antrl anim1d eximdv mpd exlimddv ) AGLDMZFLBMZNZGHDMZCHFMZNZHOZLABGEMDFEMZUMLOKAEFDMU RJEFDPQLBDEGFRSAUMNZLHDMZUONZHOZUQAUMVBADCBMZUMVBT ABCDMVCIBCDPQUMVCVBULVCVBUKHFDBLCRUAUBQUCUSVAUPHUS UTUNUOUKUTUNTAULUKUTUNGLHDUDUEUFUGUHUIUJ $.
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
        $= ( weq wffifsc wffcong ifsc6 wa wi wffbetw ifsc1 ax-predB1 ax-A6 syl6 syl5 ifsc4 ax-predC2 congnullsegsym syli equcomi jcad ax-predC3 ax-predC1 sylan9 mpdi ) ACIZABCDEFGHJZCDGHKZBDFHKZABCDEFGHLUKULGFIZCBIZMUM UNNUKULUOUPUKULFGIZUOULUKUPUQULABCOZUKUPABCDEFGHPU KURCBCOUPACBCQCBRSTZULBCFGKZUPUQABCDEFGHUAUPUTBBFG KUQCBBFGUBFGBUCSTUDFGUESUSUFUOUMCDFHKUPUNGFCDHUGCB DFHUHUISUJ $.
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
        $= ( wffifsc weq wn wffcong vx wffbetw wa wi vy simprrr ifsc4 cong_2143 syl adantr jca pm2.21 a1i ax-predC2 congnullsegsym syl6 impd a1dd jcad equcomi ifsc6 ax-predC1 ax-predC3 sylan9 syl5 ancoms sylan2 a1ddd imp4a jad mpi expcomd expd pm3.41 syl8 pm3.21 anim1d wffafs ifsc1 ad2antrr simprrl betw-exch1sym ifsc2 simprll cong-a2sym congsymd ad2ant2l adantl ifsc3 ifsc5 ofsc-intro ax5alt sylan expcom syl9 ex com3r pm2.61i ax-A4 exlimiiv ) ABCDEFGHIZACJKZBDFHLZACMNZCMBCLZOZWMWNOZWOPZMEGQNZ GQBCLZOZWRWTPZQMCJZXCXDPXEXCWRWMWOPZWTXEXCWRXFXEWM XCWROZWOXEWMXGOZWQCBGFLZOZPXHWOPZXHWQXIWMXCWPWQRWM XIXGWMBCFGLXIABCDEFGHSBCFGTUAZUBUCXEXHXJXKXHKXKPXE XHWOUDUEXEXJWMXGWOXEXJWMXGWOXEXJGFJZBCJZOXFXEXJXMX NXEWQXIXMXEWQXNXIXMPXEWQCCBCLXNMCCBCUFBCCUGUHZXNXI CCGFLXMBCCGFUFGFCUGUHUHUIXEWQXIXNXEWQXNXIXOUJUIUKX NXMCBJZXFBCULXPXMXFWMCDGHLZXPXMOWOABCDEFGHUMZXPXQB DGHLXMWOCBDGHUNGFBDHUOUPUQURUSUHUTVAVBVCVDVEWMWNWO VFVGXCWRXEKZWTXCWRXSWTPXGWSXHWNOZXSWOXGWMXHWNXGWMV HVIXTMCBDQGFHVJZXSWOXTMCBDQGFHXTABCNZWPOMCBNXTYBWP WMYBXGWNABCDEFGHVKVLXHWPWNWMXCWPWQVMZUBUCABCMVNUAX TEFGNZXAOQGFNXTYDXAWMYDXGWNABCDEFGHVOVLXHXAWNWMXAX BWRVPZUBUCEFGQVNUAXTCMGQLZMCQGLXHYFWNXGYFWMXBWQYFX AWPXBWQOGQCMBCGQCMVQVRVSVTZUBCMGQTUAWMXIXGWNXLVLXH ACMDEGQHVJWNMDQHLXHACMDEGQHYCYEWMACEGLXGABCDEFGHWA UBYGWMADEHLXGABCDEFGHWBUBWMXQXGXRUBZWCACMDEGQHWDWE XHXQWNYHUBWCYAXSWOMCBDQGFHWDWFUQWGWHWIWJQGBCEWKWLM CBCAWKWLWF $.
$}

ifsc-cong
    $p |- ( IFSC ( a b c d e f g h ) -> ( b d C f h ) )
    $= ( weq wffifsc wffcong wi ifsccongeq ifsccongneq pm2.61i ) ACIABCDEFGHJBDFHKLABCDEFGHMABCDEFGHNO $.

${
    $( Let two line segments be congruent, with a point placed on each segment some set distance from an endpoint. Then the distance from that point to the other endpoint of the segment it lies on is the same for both segments. Theorem 4.3 of [SST] $)
    segment-subtraction
        $p |- ( ( ( ( ( B a b c ) /\ ( B e f g ) ) /\ ( a c C e g ) ) /\ ( b c C f g ) ) -> ( a b C e f ) )
        $= ( wffbetw wa wffcong wffifsc cong_2143 congnullseg jctir ad2antlr ancli pm3.22 an12s df-ifsc biimpri 3syl ifsc-cong ) ABCGDEFGHZACDFIZHBCEFIZHZABCADEFDJZBAEDIABDEIUEUEC AFDIZAADDIZHZHUEUHHZUGHZUFUEUIUCUIUBUDUCUGUHACDFKA DLMNOUGUEUHUKUGUJPQUFUKABCADEFDRSTABCADEFDUABAEDKT $.
$}

${
    betw-cong-equivalence.1 $e |- ( ph -> ( B a b c ) ) $.
    betw-cong-equivalence.2 $e |- ( ph -> ( a b C a c ) ) $.
    betw-cong-equivalence
        $p |- ( ph -> b = c )
        $= ( wffcong weq wffbetw wa betw-symd betw-id2 a1i cong_4321 syl jca31 congref jca wi segment-subtraction mpd ax-A3 equcomd ) ADCADCCCGZDCHADCBIZCCBIZJDBCBGZJZCBCBGZJZUDAUHUIAU EUFUGABCDEKUFACBLMABCBDGUGFBCBDNOPUIACBQMRUJUDSADC BCCBTMUADCCUBOUC $.
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
    $= ( wffcong3 wffcong wa congref pm3.2i df-cong3 mpbir ) ABCABCDABABEZBCBCEZFZACACEZFMNKLABGBCGHACGHABCABCI J $.

cong3-sym
    $p |- ( ( a b c C3 d e f ) -> ( d e f C3 a b c ) )
    $= ( wffcong3 cong3-elim1 congsymd cong3-elim2 cong3-elim3 cong3-intro ) ABCDEFGZDEFABCMABDEABCDEFHIMBCEFABCDEFJIMACDFABCDE FKIL $.

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
    $= ( wffcong3 wffcong cong3-elim1 cong_2143 syl cong3-elim3 cong3-elim2 cong3-intro ) ABCDEFGZBACEDFOABDEHBAEDHABCDEFIABDEJKABCDEFLABCDE FMN $.

cong3-312
    $p |- ( ( a b c C3 d e f ) -> ( c a b C3 f d e ) )
    $= ( wffcong3 wffcong cong3-elim3 cong_2143 syl cong3-elim1 cong3-elim2 cong3-intro ) ABCDEFGZCABFDEOACDFHCAFDHABCDEFIACDFJKABCDEFLOBCEF HCBFEHABCDEFMBCEFJKN $.

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
        $= ( pointp wffbetw weq wn wa wex wffcong3 wffL1 uniq3p syl wffcong ax-A4 19.42v pm3.21 wi simprl simprr simpl pointq equcomi con3i adantl ad2antll simprrl betw-symd ad2antrl congsymd betw-ep2 ad2ant2r adantr betw-exch1 congsym ad2antlr segment_additiond unique-segcond equcomd ax-predB3 sylc ax-predC4 cong3-intro jca anasss an12s ex exlimiiv syl12anc a1i syl5d impd eximdv biimtrrid mpan2i exlimdv mpd ) AGEKLZEKMZNZOZKPZEFGLZBCDEFGQZOZFPZARWIJGEKSTAWHWM KAWHKEFLZEFBCUAZOZFPZWMFEBCKUBWHWQOWHWPOZFPAWMWHWP FUCAWRWLFAWHWPWLAWPWPAOZWHWLAWPUDWHWSWLUEUEAWHWSWL WHWSOWPAWHWLWHWPAUFWHWPAUGWHWSUHKFUILZFUICDUAZOZWP AWHOZOZWLUEUIXBXDWLWPXBXCWLWPXBXCWLWPXBOZXCOZWJWKX FUIGMZEFUILZWJXFGUIXFGUIEBDKWHKEMZNZXEAWGXJWEXIWFK EUJUKULUMXFGEKXEAWEWGUNUOXFBDEGABDEGUAXEWHHUPZUQXE KEUILZXCWNWTXLWOXAKEFUIURUSUTXFBDEUIXFBCDEFUIABCDL XEWHIUPXEXHXCWNWTXHWOXAKEFUIVAUSUTZXEBCEFUAZXCWOXN WNXBEFBCVBVCUTZXECDFUIUAZXCXAXPWPWTFUICDVBUMUTZVDU QVEVFZXMUIGEFVGVHXFBCDEFGXOXFXGXPCDFGUAXRXQUIGCDFV IVHXKVJVKVLVMVNUIFCDKUBVOVPVNVQVRVSVTWAWBWCWD $.
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
    btwn-preserved-Ed.2 $e |- ( ph -> ( a b c C3 d e f ) ) $.
    btwn-preserved-Ed.3 $e |- ( ph -> ( ( B d x f ) /\ ( a b c C3 d x f ) ) ) $.
    $( Betweenness is preserved across congruence of series of points. Theorem 4.6 of [SST]. ( Implied Existential / Deductive form ) $)
    btwn-preserved-Ed
        $p |- ( ph -> ( B d e f ) )
        $= ( weq wffbetw wffifsc wffcong wffcong3 simpld congref a1i cong3-sym-d simprd cong3-trans-d cong3-elim1 syl cong3-elim2 cong_2143 ifsc-intro ifsc-cong congnullsegsym 3syl ax-predB2 sylc ) ABGKZFBHLZFGHLAFBHBFBHGMBBBGNULAFBHBFBHGAUMCDEFBHO ZJPZUOFHFHNAFHQRBHBHNABHQRAFBHFGHOZFBFGNAFGHFBHAFG HCDEFBHACDEFGHISAUMUNJTUASZFBHFGHUBUCABHGHNZHBHGNA UPURUQFBHFGHUDUCBHGHUEUCUFFBHBFBHGUGBGBUHUIUOBGFHU JUK $.
$}

${
    $d ph x $.
    $d a x $.
    $d b x $.
    $d c x $.
    $d d x $.
    $d e x $.
    $d f x $.
    btwn-preserved-d.2 $e |- ( ph -> ( B a b c ) ) $.
    btwn-preserved-d.1 $e |- ( ph -> ( a b c C3 d e f ) ) $.
    $( Betweenness is preserved across congruence of series of points. Theorem 4.6 of [SST]. ( Deductive form ) $)
    btwn-preserved-d
        $p |- ( ph -> ( B d e f ) )
        $= ( vx wffbetw wffcong3 wa wffcong cong3-elim3 syl cong-seg-div-d adantr simpr btwn-preserved-Ed exlimddv ) AEJGKBCDEJGLMZEFGKJABCDEJGABCDEFGLZBDEGNIBCDEFGOPH QAUBMJBCDEFGAUCUBIRAUBSTUA $.
$}

btwn-preserved
    $p |- ( ( ( B a b c ) /\ ( a b c C3 d e f ) ) -> ( B d e f ) )
    $= ( wffbetw wffcong3 wa simpl simpr btwn-preserved-d ) ABCGZABCDEFHZIABCDEFMNJMNKL $.

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
        $= ( wffbetw wo wffcong3 wa wffcol btwn-preserved cong3-231 sylan2 cong3-312 disimp2intro df-col anbi1i 3imtr4i ) ABCGZBCAGZCABGZHZHZABCDEFIZJDEFGZEFDGZFDEGZHZHABCK ZUEJDEFKTUEUCUFUIABCDEFLUAUEUBUGUHUEUABCAEFDIUGABC DEFMBCAEFDLNUEUBCABFDEIUHABCDEFOCABFDELNPPUJUDUEAB CQRDEFQS $.
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
        $= ( wffbetw wffcong wa wffcong3 wi ax-A4 congsym anim2i eximii simplr simprr segment_addition anasss an4s jca31 df-cong3 sylibr expcom 19.37iv ) ABCGZABDEHZIZABCDEFJZFDEFGZBCEFHZIZUHUIKFUJEFBCHZI ULFFEBCDLUMUKUJEFBCMNOUHULUIUHULIZUGUKIACDFHZIUIUN UGUKUOUFUGULPUHUJUKQUFUJUGUKUOUFUJIUGUKUOABCDEFRST UAABCDEFUBUCUDOUE $.
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
        $= ( wffbetw wffcong wa wffcong3 wex cong_2143 l1-col-seg-div sylan2 cong3-213 eximi syl ) BACGZABDEHZIBACEDFJZFKZABCDEFJZFKSRBAEDHUAABDELBAC EDFMNTUBFBACEDFOPQ $.
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

df-fsc $a |- ( FSC ( a b c d e f g h ) <-> ( ( ( Col ( a b c ) /\ ( a b c C3 e f g ) ) /\ ( a d C e h ) ) /\ ( b d C f h ) ) ) $.

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
        $= ( wffifsc wffcong wffbetw wffcong3 wa cong3-132 syl jca btwn-preserved cong3-elim1 cong3-elim2 cong_2143 ifsc-intro ifsc-cong ) ABDCEFHGINDEHIOABDCEFHGIJABDCPZBDCFHGQZRFHGPAUHUIJ ABCDFGHQZUIKBCDFGHSTUABDCFHGUBTAUJBCFGOKBCDFGHUCTA CDGHOZDCHGOAUJUKKBCDFGHUDTCDGHUETLMUFBDCEFHGIUGT $.
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
        $= ( wffafs weq wn wffcong btwn-preserved-d wffcong3 cong3-elim1 syl cong3-elim2 ofsc-intro ax5alt syl2anc ) ABCDEFGHIOBCPQDEHIRABCDEFGHIJABCDFGHJKSABCDFGHTZBC FGRKBCDFGHUAUBAUGCDGHRKBCDFGHUCUBLMUDNBCDEFGHIUEUF $.
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
        $= ( wffafs weq wn wffcong betw-symd wffcong3 cong3-312 syl btwn-preserved-d cong3-elim1 cong_2143 cong3-elim3 ofsc-intro equcomi nsyl ax5alt syl2anc ) ACBDEGFHIOCBPZQDEHIRACBDEGFHIADBCJSAHFGADBCHFGJABC DFGHTZDBCHFGTKBCDFGHUAUBUCSABCFGRZCBGFRAUMUNKBCDFG HUDUBBCFGUEUBAUMBDFHRKBCDFGHUFUBMLUGABCPULNCBUHUIC BDEGFHIUJUK $.
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
        $= ( weq wn wffcol wa wffcong line-cong congnullsegsym syl ) ABEFABCGHACADIHBCBDIHCCCDICDEABCCDJCDCKL $.
$}

${
    $( Corollary of line-distance-uniq without the restriction that a and b must be distinct. Theorem 4.19 of [SST] $)
    distance-uniq-corollary
        $p |- ( ( ( ( B b c a ) /\ ( a c C a d ) ) /\ ( b c C b d ) ) -> c = d )
        $= ( weq wffbetw wffcong wa wi pm3.2 anim1d ax-predB1 equcoms imp ax-A6 equcomd syl ax-predC2 congnullsegsym syl6 adantr ad2antrr equtrr sylc wn wo orc olcd anim2i wffcol df-col anbi2i anbi1i line-distance-uniq sylanbr sylanl1 pm2.61i ) ABEZBCAFZACADGZHZBCBDGZHZCDEZIURVCURUSHZUTHZVBHZVD URVAVFVBURUSVEUTURUSJKKVGADEZCAEZVDVFVHVBVEUTVHVEU TAAADGZVHVEVIUTVJIVEACAFZVIURUSVKUSVKIBABACALMNVKA CACOPQZCAAADRQADASTNUAVEVIUTVBVLUBADCUCUDTURUEZVCV MUSHZUTHZVBHVDVMVAVOVBVMUSVNUTVMUSJKKVNVMABCFZUSCA BFZUFZUFZHZUTVBVDUSVSVMUSVRVPUSVQUGUHUIVTUTHVMABCU JZHZUTHVBVDWBVTUTWAVSVMABCUKULUMABCDUNUOUPTUQ $.
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
        $= ( betw-243-d betw-241-d betw-symd conglhs-d congsymd cong-trans-d cong-4312-d segment_additiond wffcong congref a1i unique-segcond ) AHICCIBTABCFHNABCEFLKUAZUAAHCCIAHFCCDIACFHABCFHUMN UBUCABCDIJABDGIOMUAZUBAFHCDRUDAFECDGIACEFABCEFKLUB UCABDGIMOUBAFEDEDGPADGDEQUEUFAGICESUGUHUHUDABCDIUN JUACICIUIACIUJUKUL $.
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
        $= ( weq wffcong wa ax-predC3 mpan9 ax-A3 syl betw-243-d betw-241-d betw-symd conglhs-d congsymd cong-trans-d cong-4312-d segment_additiond congref a1i unique-segcond adantr equtr sylc equcomd ax-predC2 wn wffafs betw-241-sym-d wi pm2.21 equcomi cong-2143-d imim1i imim12i jad mp2 ax-A1 ofsc-intro ax5alt sylan congrhs pm2.61dan ) ACDUAZGFDEUBZAWAUCZIFUAGIDEUBZWBWCFIWCFHUAZHIUAZFI UAWCFHDDUBZWEAFHCDUBWAWGRCDFHDUDUEFHDUFUGAWFWAAHIC CIBTABCFHNABCEFLKUHZUHAHCCIAHFCCDIACFHABCFHWHNUIUJ ABCDIJABDGIOMUHZUIAFHCDRUKZAFECDGIACEFABCEFKLUIUJA BDGIMOUIAFEDEDGPADGDEQULUMZAGICESUNUOZUOUKABCDIWIJ UHCICIUBACIUPUQURZUSFHIUTVAVBAGICEUBWAWDSCDGIEUDUE IFGDEVCVAAWAVDZUCGFEDUBZWBACDGFHFEDVEWNWOACDGFHFED ABCDGJMUIABEFHLNVFAHFCDWJULAFEDGWKULIHUAZCFIDUBZCF HDUBZVGZVGZAWFVGAWRVGZIHCFDUDWMWTAWFXAAVDXAVGWTAWR VHUQWFWPWSXAHIVIAWQWRAFCDIWLVJVKVLVMVNDFFDUBADFVOU QVPCDGFHFEDVQVRGFEDVSUGVT $.
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
        $= ( wffcong weq betw-symd col-intro-3-d cong-trans-d wa wi ax-predC3 equcomi adantl wffifsc congref a1i congsymd l2-connectivity-between conglhs-d cong-a2sym syl2anc ifsc-intro ifsc-cong syl adantr ax-A3 embantd mpi equtr mpd wffafs wn wffbetw betw-intr1 cong_4321 ax-A1 ofsc-intro ax-predC2 mpan9 congnullsegsym mtand nsyl ax5alt ax-predC1 ax-predC4 sylc congsym 3syl sylan pm2.61dan betw-241-d l1-connectivity-between equcomd ax-predB3 betw-outd ax-predB1 ax-A6 wffcol betw-243-d col-intro-1-d col-132 line-cong-d segment_additiond ) ALLHFUNHFUOZAHFLLAKLUOZHFKLUNHFLLUNAKKKLUNXOAEGKKL UMAEGKAGEKUGUPZUQAEKEFUNELEFUNZEKELUNAEKEHEFUJUCUR AFELEUNZXQAHBUOZXRAXSUSZXQXRXTXNELEHUNZXQXTBFUOZXN XTBHUOZBFBHUNZBFHHUNZUTZUTYBBHBFHVAXTYCYFYBXSYCAHB VBVCXTYDYEYBAYDXSAEBGFEBGHVDYDAEBGFEBGHUAUAEGEGUNA EGVEVFBGBGUNABGVEVFAEHEFUCVGAGFEFUNZGHEFUNGFGHUNNA HGEFACDEFGHIJOPQRSTNUCUDUEUFVHZVIEFGFGHVJVKVLEBGFE BGHVMVNZVOYEYBUTXTBFHVPVFVQVQVRXSYBXNUTAHBFVSVCVTX TXOEKEHUNZYAXTKMUOZMLUOZXOXTBBKMUNZYKAHBKMUNZXSYMA MKBHUNZYNAHEMKKEBHWAHEUOZWBYOAHEMKKEBHUHAKEGWCEBGW CKEBWCXPUAKEBGWDVKAYJHEKEUNUJEKEHWEVNZUKHKKHUNAHKW FVFUJWGAEHUOZYPAYREGUOZUMAYRUSZHGUOZYSYTHHHGUNZUUA AHEHGUNZYRUUBAHEEFUNHGEFUNUUCAEHEFUCVIYHEFHEHGVJVK ZEHHHGWHWIHGHWJVNYRUUAYSUTAEHGVSVCVTWKZHEVBWLZHEMK KEBHWMVKZMKBHWEVNZHBBKMWNWIKMBWJVNZXTMLMMUNZMMMLUN YLXTYKMLMKUNZUUJUUIAUUKXSULVOKMMLMWOWPMLMMWQMLMWJW RKMLVSWPAYJXSUJVOKLEEHWHWPHFELEWOWPELEFWEVNAHBFEKM LEWAXSWBXRAHBFEKMLEAFBHUBUPZUIUUHABFBHMLYIABHMKUNU UKBHMLUNAMKBHUUGVGULMKBHMLVJVKURZYQAEMEBUNZBEMEUNU KEMEBWEVNWGHBFEKMLEWMWSWTFELEWEVNEFEKELVJVKZADIGKL ADIUOZYPUUFAUUPUSZHEHWCZYPUUQDHUOZDEHWCZUURUUQIHUO ZUUSUUQIHIWCZUVAADHIWCUUPUVBADEHIACDEHORXAZAJIUOEH JWCEHIWCAIJACDEFGHIJOPQRSTNUCUDUEUFXBXCACEHJRTXAJI EHXDWPZUUEXEDIHIXFWIIHXGVNUUPUVAUUSUTADIHVSVCVTAUU TUUPUVCVODHEHXFWPHEXGVNWKADGIXHDIGXHADGIACDGIACDFG QPXISXAXJDGIXKVNAEHDKLUUEAEHDUVCUQUUOAEMHKLAEMUOZY SUMAUVEUSZEBUOZBGUOZYSUVFMMEBUNZUVGAUUNUVEUVIUKEMM EBWNWIEBMWJVNZUVFBBBGUNZUVHUVFUVGBEBGUNZUVKUVJAUVL UVEAFBHEFBHGVDUVLAFBHEFBHGUBUBFHFHUNAFHVEVFBHBHUNA BHVEVFAYGFEFGUNNGFEFWEVNUUDVLFBHEFBHGVMVNVOEBBBGWH WPBGBWJVNEBGVSWPWKAEMHUHUQUUOAMLMKULVGXLZXLAEHIKLU UEAEHIUVDXJUUOUVMXLXLXLKLKWJVNAHBFKMLUULUIUUHUUMXM KLHFLVAWPVGHFLWJVN $.
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
        $= ( vx wffbetw wa wo wex betw-symd ax-A7 syl2anc wffcong adantr simprl simprr weq wn l5-connectivity-between exlimddv ) ADUAFUBZEUAGUBZUCZBDEUBBEDUBUDUAAGDBUBFEBUBUSUAUEA BDGNUFABEFMUFUAGFBDEUGUHAUSUCUABCDEFGHIAFEDEUIUSJU JABCDUBUSKUJABCEUBUSLUJABEFUBUSMUJABDGUBUSNUJABFHU BUSOUJABGIUBUSPUJAUQURUKAUQURULADGDEUIUSQUJAFHCDUI USRUJAGICEUIUSSUJABCUMUNUSTUJUOUP $.
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
        $= ( pointf wffbetw wffcong wa wo wi pointe pm3.2 anim2d simprlr adantr simprll simprrl simprrr weq wn l7-connectivity-between syl6 conglhs ax-gen ax-A4 darii exlimiiv expcom ) BDIJZDIDEKZLZABDEJBEDJMZNIAUOUPBEOJZOEDEKZLZAUOLZU PNOUSUTAUSUOLZLZUPUSUOVAAUSUOPQVBBCDEOIAUQURUORABC DJVAFSABCEJVAGSAUQURUOTAUSUMUNUAAUSUMUNUBABCUCUDVA HSUEUFEODEKZURUQOVCURNOEODEUGUHOEDEBUIUJUKULIDDEBU IUK $.
$}

connectivity-between
    $p |- ( ( ( -. a = b /\ ( B a b c ) ) /\ ( B a b d ) ) -> ( ( B a c d ) \/ ( B a d c ) ) )
    $= ( weq wn wffbetw wa simplr simpr simpll l8-connectivity-between ) ABEFZABCGZHZABDGZHABCDMNPIOPJMNPKL $.

connectivity-between-2
    $p |- ( ( ( -. a = b /\ ( B a b c ) ) /\ ( B a b d ) ) -> ( ( B b c d ) \/ ( B b d c ) ) )
    $= ( weq wn wffbetw wa wo simplr anim1i simpr connectivity-between orim12da betw-exch1 orim12i syl ) ABEFZABCGZHZABDGZHZSACDGZHZUAADCGZHZIBCDGZBDCGZIUB UCUEUDUFUBSUCRSUAJKUBUAUETUALKABCDMNUDUGUFUHABCDOA BDCOPQ $.

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
        $= ( weq wffbetw wo wa ax-predB3 mpan9 olcd wn pointp wex 2pimp3p adantl equcomi con3i ad2antll betw-sym ad2antrl adantr betw-intr1 syl2anc jca31 connectivity-between-2 syl adantlr exlimddv pm2.61dan ) AECHZBCDIZBDCIZJZAUNKUPUOABDEIZUNUPGECBDLMNAUNOZKE BPIZBPHZOZKZUQPUSVCPQACEEBPRSAVCUQUSAVCKZPBHZOZPBC IZKPBDIZKUQVDVFVGVHVBVFAUTVEVAPBTUAUBVDPBEIZBCEIZV GUTVIAVBEBPUCUDZAVJVCFUEPBCEUFUGVDVIURVHVKAURVCGUE PBDEUFUGUHPBCDUIUJUKULUM $.
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
        $= ( wffle vy wffbetw wffcong wa wex df-le biimpi wffcong3 wffcol id col-intro-1-d congsym anim12i col-seg-div syl simpl biantrurd exbidv mpbid btwn-preserved cong3-elim3 adantl congsymd jca eximi exlimiv ) BCDEFZDGEHZBCDGIZJZGKZBCAHZBADEIZJZAKZUMUQGBCDELMU PVAGUPUNDGEBCANZJZAKZVAUPVBAKZVDUPDGEOZDGBCIZJVEUN VFUOVGUNDGEUNPQBCDGRSDGEBCATUAUPVBVCAUPUNVBUNUOUBU CUDUEVCUTAVCURUSDGEBCAUFVCDEBAVBDEBAIUNDGEBCAUGUHU IUJUKUAULUA $.
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
        $= ( vy wffbetw wffcong wa wex wffle conglhs anim2i eximi df-le 3imtr4i ) CEDFZABCEGZHZEIPBACEGZHZEIABCDJBACDJRTEQSPABCEKLME ABCDNEBACDNO $.
$}

${
    $d a x $.
    $d b x $.
    $d c x $.
    $d d x $.
    $( The Right Hand Side of the 'Less Than or Equal to' predicate commutes. $)
    le-RHS
        $p |- ( ( a b Le c d ) -> ( a b Le d c ) )
        $= ( vx wffbetw wffcong wa wex wffle congrhs anim2i eximi le-def2 3imtr4i ) ABEFZAECDGZHZEIPAEDCGZHZEIABCDJABDCJRTEQSPAECDKLME ABCDNEABDCNO $.
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
        $= ( vy wffbetw wffcong wa wex wffle weq ax6evr betw-id ax-predB2 mpi congref ax-predC4 jca eximii df-le biimpri ax-mp ) ACBDZABACEZFZCGZABABHZBCIZUCCCBJUFUAUBUFABBDUAABKB CABLMUFABABEUBABNBCABAOMPQUEUDCABABRST $.
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
        $= ( vz wffbetw wffcong wa wex wffle vx df-le biimpi syl vy adantr nfv nfe1 wffcong3 simprr simplrl cong-seg-div-d cong3-elim1 anim2i eximi simprl jca betw-ep2 simplrr anassrs cong-trans-d 19.8ad exlimdd exlimddv sylibr ) AFJGKZBCFJLZMZJNZBCFGOADPEKZBCDPLZMZVDPABCDEOZVGPN ZHVHVIPBCDEQRSAVGMZFTGKZDEFTLZMZVDTVJDEFGOZVMTNZAV NVGIUAVNVOTDEFGQRSVJVMMZFJTKZDPFJLZMZVDJVPJUBVCJUC VPVQDPEFJTUDZMZJNVSJNVPDPEFJTVJVKVLUEAVEVFVMUFUGWA VSJVTVRVQDPEFJTUHUIUJSVPVSMZVCJWBVAVBWBVQVKMVAWBVQ VKVPVQVRUKVJVKVLVSUFULFJTGUMSWBBCDPFJVJVMVSVFAVEVF VMVSMUNUOVPVQVRUEUPULUQURUSUSJBCFGQUT $.
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
        $= ( vz wffbetw wffcong wa wffcong3 wex simprd simpld cong-seg-div-d cong3-elim1 anim2i eximi syl weq simpll sylan simprl betw-243-d congsym ad2antll simplr congsymd cong-trans-d betw-cong-equivalence ax-predB2 sylc jca betw-equality equcomd adantr ax-predC4 exlimddv ) AFJCKZDBFJLZMZDEFGLZJAVBDBEFJCNZMZJOVDJOADBEFJCAFC GKZDEFCLZHPZADBEKZFGDBLZIQRVGVDJVFVCVBDBEFJCSTUAUB AVDMZCGUCVIVEVMGCVMFGCKZVHMGCUCVMVNVHVMJGUCVBVNVMF JGVMFJCGAVHVIMVDVHHVHVIVDUDUEZAVBVCUFZUGVMFJDBFGVC FJDBLAVBDBFJUHUIVMFGDBAVKVLMVDVLIVKVLVDUJUEUKULUMV PJGFCUNUOVOUPFGCUQUBURAVIVDVJUSCGDEFUTUOVA $.
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
        $= ( wffle vy wffbetw wffcong wa wex weq ax6evr betw-id2 congnullseg pm3.2i ax-predB2 ax-predC4 anim12d mpi eximii df-le mpbir ) AABCDBECFZAABEGZHZEIBEJZUDEEBKUEBBCFZAABBGZHUDUFUG BCLABMNUEUFUBUGUCBEBCOBEAABPQRSEAABCTUA $.
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
        $= ( weq wffle wo vy wffbetw wffcong wa wex le-nullsegment df-le biimpi ax-mp ax-predC2 anim2d eximdv mpi biimpri syl orcd wn vx segment-construction-connectivity andir exbii sylib 19.43 le-def2 congsym anim2i eximi orim12i pm2.61i ) ABEZABCDFZCDABFZGZUQURUSUQCHDIZABCHJZKZHLZURUQVAAA CHJZKZHLZVDAACDFZVGACDMVHVGHAACDNOPUQVFVCHUQVEVBVA ABACHQRSTURVDHABCDNUAUBUCUQUDZABUEIZAUECDJZKZUELZA UEBIZVKKZUELZGZUTVIVLVOGZUELZVQVIVJVNGVKKZUELVSUEA BCDUFVTVRUEVJVNVKUGUHUIVLVOUEUJUIVMURVPUSURVMUEABC DUKUAVPVNCDAUEJZKZUELZUSVOWBUEVKWAVNAUECDULUMUNUSW CUECDABNUAUBUOUBUP $.
$}

${
    l1-le-betw.2 $e |- ( ph -> ( B a b c ) ) $.
    l1-le-betw
        $p |- ( ph -> ( ( a b Le a c ) /\ ( b c Le a c ) ) )
        $= ( wffle wffcong congref a1i le-intro betw-symd le-intro2 le-LHS syl le-RHS jca ) ABCBDFCDBDFZACBCBDEBCBCGABCHIJACDDBFZQADCDBFRABDCD BABCDEKDBDBGADBHILDCDBMNCDDBONP $.
$}

${
    l1-le-betw.1 $e |- ( ph -> Col ( a b c ) ) $.
    l1-le-betw.2 $e |- ( ph -> ( a b Le a c ) ) $.
    l1-le-betw.3 $e |- ( ph -> ( b c Le a c ) ) $.
    l2-le-betw
        $p |- ( ph -> ( B a b c ) )
        $= ( wffbetw wo simpr wa weq betw-symd wffcong wffle adantr le-LHS syl le-RHS id l1-le-betw adantl simprd le-antisymmetry cong_4321 betw-cong-equivalence betw-id ax-predB2 mpisyl simpld congsymd cong-2143-d jaodan wffcol col-elim mpjaodan ) ABCDHZUQCDBHZDBCHZIZAUQJAURUQUSAURKZDCLBDDHUQVABDC VACDBAURJMVACBDBNBDBCNVACBDBVACBBDOZCBDBOVABCBDOZV BAVCURFPBCBDQRCBBDSRVACDCBOZDBCBOZURVDVEKAURCDBURT UAUBUCUDCBDBUERUFBDUGDCBDUHUIAUSKZDCBVFBCLDBBHDCBH VFDBCAUSJVFBDCDVFCDBDVFCDBDACDBDOUSGPVFBDDCOZBDCDO VFDBDCOZVGVFVHBCDCOZUSVHVIKAUSDBCUSTUAUBUJDBDCQRBD DCSRUDUKULUFDBUGBCDBUHUIMUMABCDUNUQUTIEBCDUORUP $.
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
