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

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Primitive notions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Declare constants and variables. The constant C is for congruence and B for betweenness. $)

$c B C $.
$v a b c d e f g h p q r s $.

$( Assign each variable as a setvar (analougous to point). $)

pointa $f setvar a $.
pointb $f setvar b $.
pointc $f setvar c $.
pointd $f setvar d $.
pointe $f setvar e $.
pointf $f setvar f $.
pointg $f setvar g $.
pointh $f setvar h $.
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
ax-A4 $a |- E. x ( ( B q a x ) /\ ( a x C b c ) ) $.
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

df-U0 $a |- ( U0 <-> a = b ) $.

df-U1 $a |- ( U1 <-> ( ( ( B a b c ) \/ ( B b c a ) ) \/ ( B c a b ) ) ) $.

df-U0 $a |- ( U0 <-> a = b ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Dimension properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


U0imp
    $p |- ( U0 -> a = b )
    $= ( wffU0 weq df-U0 biimpi ) CABDABEF $.

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

conglhs $p |- ( ( a b C c d ) -> ( b a C c d ) )
    $= ( wffcong ax-A1 ax-A2 mpan ) ABBAEABCDEBACDEABFABBACDGH $.

congrhs $p |- ( ( a b C c d ) -> ( a b C d c ) )
    $= ( wffcong ax-A1 congtrans mpan2 ) ABCDECDDCEABDCECDFABCDDCGH $.

cong_2143
    $p |- ( ( a b C c d ) -> ( b a C d c ) )
    $= ( wffcong conglhs congrhs syl ) ABCDEBACDEBADCEABCDFBACDGH $.

cong_3421
    $p |- ( ( a b C c d ) -> ( c d C b a ) )
    $= ( wffcong congsym congrhs syl ) ABCDECDABECDBAEABCDFCDABGH $.

cong_4312
    $p |- ( ( a b C c d ) -> ( d c C a b ) )
    $= ( wffcong congsym conglhs syl ) ABCDECDABEDCABEABCDFCDABGH $.

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
    $( Segment Uniqueness. First 10 steps prove ax = az. Next four prove qx=qz. Steps 17 below show x = z implies A5 $)
    unique-segcon
        $p |- ( -. q = a -> ( ( ( ( B q a x ) /\ ( a x C b c ) ) /\ ( ( B q a z ) /\ ( a z C b c ) ) ) -> x = z ) )
        $= ( wffcong wi weq wn wffbetw wa congsym simpll jca congref jctir jctr ad2ant2r an3 ancom1s anim12i ax-A2 3syl segment_addition syl ax-A5 expcom syl5 ax-A3 imim2i mpsylsyld ) AAABGZABAAGZHFCIJZFCAKZCADEGZLFCBKZCBDEGZLZLZUMABI ZAAABMVAUPUPLZFCFCGZLZCACAGZLZFAFBGZLZCACBGZLZUOUM VAVIVJVAVGVHVAVEVFVAVCVDVAUPUPUPUQUTNZVLOFCPZQCAPQ VAUPURLZVDLZVJLVHVAVOVJUPURVOUQUSVNVDVMRSVAUQUSLZD ECAGZDECBGZLVJUQUPUTVPUQUPURUSTUAUQVQUSVRCADEMCBDE MUBDECACBUCUDZOFCAFCBUEUFOVSOVKUOUMFCAAFCABUGUHUIU NVBUMABAUJUKUL $.
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

betw-exch1sym
    $p |- ( ( ( B a b c ) /\ ( B a c d ) ) -> ( B d c b ) )
    $= ( wffbetw wa betw-exch1 betw-sym syl ) ABCEACDEFBCDEDCBEABCDGBCDHI $.

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
    $( Theorem 3.6(2) of [SST] $)
    betw-ep2
        $p |- ( ( ( B a b c ) /\ ( B a c d ) ) -> ( B a b d ) )
        $= ( wffbetw wa betw-sym anim12ci betw-exch2 3syl ) ABCEZACDEZFDCAEZCBAEZFDBAEABDEKNLMABCGACDGHDCBAIDB AGJ $.
$}

${
    $( Theorem 3.7(2) of [SST] $)
    betw-outtr
        $p |- ( ( ( ( B a b c ) /\ ( B b c d ) ) /\ -. b = c ) -> ( B a b d ) )
        $= ( wffbetw wa weq wn betw-sym anim12ci equcomi con3i anim12i betw-out 3syl ) ABCEZBCDEZFZBCGZHZFDCBEZCBAEZFZCBGZHZFDBAEABDERUCT UEPUBQUAABCIBCDIJUDSCBKLMDCBANDBAIO $.
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
        $= ( wffifsc wffbetw wa wffcong df-ifsc simprbi ) ABCDEFGHIABCJEFGJKACEGLKBCFGLKADEHLKCDGHLABCDEFGHM N $.
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
    $d a c $.
    $d b c $.
    0D-or-1DL
        $p |- ( a = b \/ E. c ( ( B d e c ) /\ -. e = c ) )
        $= ( weq wffbetw wn wa wex 2pimp3p orri ) ABFDECGECFHICJBADECKL $.
$}

$( Declare C3 symbol $)
$c C3 $.

$( Extend wff notation to include inner five-track configuration $)
wffcong3 $a wff ( a b c C3 d e f ) $.

df-cong3 $a |- ( ( a b c C3 d e f ) <-> ( ( a b C d e ) /\ ( b c C e f ) /\ ( a c C d f ) ) ) $.
