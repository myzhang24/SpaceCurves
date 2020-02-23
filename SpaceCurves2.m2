newPackage(
        "SpaceCurves2",
        Version => "2.0", 
        Date => "Dec 2018",
        Authors => {{Name => "Mengyuan Zhang", 
                  Email => "myzhang@berkeley.edu", 
                  HomePage => "https://math.berkeley.edu/~myzhang/"}
	      },
        Headline => "Curves in P3",
        DebuggingMode => true
        )

export {
--Surface	
	"IntersectionPairing",	      
	"CanonicalClass",
	"HyperplaneClass",
	"LinearSystem",
	"Points",
	"BlowupPlane",
	"Chi",
	"blowupPlane",
	"Scroll",
	"scroll",
--Divisors
	"Divisor",
	"Coordinate",
	"Surface",
	"divisor",
	"hyperplaneClass",
	"canonicalClass",
	"curve",
	"divisors",
--ACM Curves
    	"makeCastelnuovo",
	"UPP",
	"castelnuovo",
	"isACMBetti",
	"Smooth",
	"specialize",
	"allBetti",
	"degreeMatrix",
	"randomDeterminantalIdeal",
--Minimal curves
    	"minimalCurve",
	"raoModule",
	"minimalCurveBetti",
--Invariants
    	"sectionRing",
	"planarSection",
	"spectrum",
	"postulation",
	"tangentDimension",
	"hilbertDimension",
--Plotting
	"dgTable"	
}


--I. Surfaces
Surface = new Type of HashTable

BlowupPlane = new Type of Surface
net BlowupPlane := X -> net concatenate {
    "Plane blown up at ", toString (# X.Points), 
    " general points \n mapped by the linear system ",
    toString X.HyperplaneClass
    }   
blowupPlane = method()
blowupPlane(ZZ,List,Ring) := (n,L,kk) -> (
    assert(n>= 1 and #L == n+1);
    y := getSymbol "y";
    S := kk(monoid[y_0..y_2]);
    M := random(S^3,S^n); --matrix of coordinates of n points in P2
    points := apply(numcols M, i-> minors(2,matrix{gens S,entries M_(i)}));    
    B := super basis(L#0,intersect apply(n, i -> points_i^(L#(i+1)))); --linear system
    assert(numcols B >= 4);    --it needs to map to at least P3
    new BlowupPlane from {
    	symbol IntersectionPairing => diagonalMatrix splice{1,n:-1},
	symbol CanonicalClass => -splice{3,n:1},
	symbol HyperplaneClass => L,
	symbol Points => points,
	symbol LinearSystem => B,
	symbol Chi => 1	
    }
) 
blowupPlane(ZZ,List) := (n,L) -> blowupPlane(n,L,ZZ/101)	--default coeff ZZ/101
blowupPlane ZZ := n -> blowupPlane(n,{3} | splice{n:1})    --default linear system anti-canonical

Scroll = new Type of Surface
net Scroll := X -> net concatenate {
    "P(O_P(", toString first X.Type,
    ")+O_P(", toString last X.Type, ")) embedded by O(1)."
    }
scroll = method()
scroll (List, Ring) := (L,kk) -> (
    assert(#L == 2 and isField kk);
    (a,b) := toSequence sort L;
    X := getSymbol "X";
    R := kk(monoid[X_0..X_3,Degrees=>{{0,1},{0,1},{1,-a},{1,-b}}]);
    B := basis({1,0},R);    --basis sections
    new Scroll from {
    	symbol Type => {a,b},
	symbol LinearSystem => B,
	symbol HyperplaneClass => {1,b},
	symbol CanonicalClass => {-2,-(b-a+2)},
	symbol IntersectionPairing => matrix{{-(b-a),1},{1,0}},    --basis -e curve C_0 and fiber f
	symbol Chi => 1
    }        
)
scroll List := L -> scroll(L,ZZ/101)
scroll(ZZ,ZZ) := (a,b) -> scroll {a,b}

ideal Surface := X -> (
    B := X.LinearSystem;
    R := ring source B;
    kk := coefficientRing R;
    x := getSymbol "x";
    S := kk(monoid[x_0..x_(numcols B-1)]);
    kernel map(R,S,B)
)

--II.Divisors

Divisor = new Type of HashTable
net Divisor := X -> net X.Coordinate

divisor = method()
divisor(List, Surface) := (C, X) -> (
    new Divisor from {
        symbol Coordinate => C,
        symbol Surface => X
        }
    )

hyperplaneClass = method()
hyperplaneClass Surface := X -> divisor(X.HyperplaneClass,X) 
canonicalClass  = method()
canonicalClass Surface := X -> divisor(X.CanonicalClass,X)

QQ * Divisor := Divisor => (k,D) -> divisor(k * D.Coordinate, D.Surface)
ZZ * Divisor := Divisor => (n,D) -> divisor(n * D.Coordinate, D.Surface)
Divisor + Divisor := Divisor => (C,D) -> (
    assert(C.Surface === D.Surface);
    divisor(C.Coordinate + D.Coordinate, D.Surface)
    )
Divisor - Divisor := Divisor => (C,D) -> (
    assert(C.Surface === D.Surface);
    divisor(C.Coordinate - D.Coordinate, D.Surface)
    )
Divisor * Divisor := QQ => (C,D) -> (
    X := C.Surface;
    assert(X === D.Surface);
    assert(X.IntersectionPairing =!= null);
    (matrix{C.Coordinate} * X.IntersectionPairing * 
	transpose matrix{D.Coordinate})_(0,0)
    )

degree Divisor := C -> C * hyperplaneClass(C.Surface)
genus Divisor := C -> 1/2*((canonicalClass(C.Surface)+C)*C)+1
chi Divisor := C -> 1/2*C*(C-canonicalClass(C.Surface))+C.Surface.Chi

ideal Divisor := Ideal => D -> (
    X := D.Surface;
    L := D.Coordinate;
    B := X.LinearSystem;
    S := ring B;
    kk := coefficientRing S;
    f := 0_S;
    
    if class X === BlowupPlane then (
    	n := #L-1;
	C := super basis(L#0,intersect apply(n, i -> ((X.Points)#i)^(L#(i+1))));
	f = (C*random(S^(numcols C),S^1))_(0,0);    --random plane model
    );
    if class X === Scroll then (
	(a,b) := toSequence X.Type;
    	f = random({L#0,L#1-b*L#0},S);	  --random P1*P1 model
    );
    x := getSymbol "x";
    kernel map(S/ideal f,kk(monoid[x_0..x_3]),B*random(S^(numcols B),S^4))
    --here we project randomly into P3
)

divisors = method()
divisors(ZZ,BlowupPlane) := List => (d,X) -> (
    --generates effective divisors of a given degree on a surface
    n := #X.HyperplaneClass-1;
    flatten for a from ceiling(d/3) to d list (
	   degs := apply(select(partitions(3*a-d, ceiling(a/3)),p->#p<=n),q ->
		{a} | toList q | splice{(n-#q):0}); 
	   degs = select(degs, L -> L#0 >= L#1 + L#2 + L#3);
	   apply(degs, L-> divisor(L,X))
    )     
)
divisors(ZZ,Scroll) := List => (d,X) -> (
    (p,q) := toSequence X.Type;
    n := p-1;
    e := q-p;
    t := getSymbol "t";
    R := (ZZ/2)(monoid[t_0,t_1,Degrees => {n+1,1}]);
    select(apply(flatten entries basis(d,R), m -> flatten exponents m), 
	P -> first P != 0 and last P != 0 and last P >= e*first P) / (cord -> divisor(cord,X))
)

--III.Minimal Curves

raoModule = method()
raoModule Ideal := I -> (
    n := numgens ring I-1;
    coker (dual res Ext^n(comodule I,ring I)).dd_(-n)
)
minimalCurve = method(Options => {Ideal => false})
alphaBeta = M -> (    
    --compute rank and rank 1 codim 1 via random evaluation
    kk := coefficientRing ring M;
    t := getSymbol "t";
    S := kk(monoid[t]);
    L := apply(4,i->random(1,S)+random(0,S));
    (A,B,C) := smithNormalForm sub(M,matrix{L});
    D := apply(min(numrows A,numcols A), i-> A_(i,i));
    (numcols M,#select(D,d->d!=0),#select(D,d->d==1))    
)
selectColumns = (d,M) -> (
    --selects the columns of a matrix of degree <= d
    L := select(flatten last degrees M,D->D<= d);
    M_(splice{0..#L-1})
)
minimalCurve Module := opts -> M -> (
    --Take a finite length module
    --returns a minimal curve
    R := ring M;
    if M == 0 then return ideal(R_0,R_1);
    assert(dim M == 0);
    Q := res M;
    r := rank Q_2 - rank Q_3 + rank Q_4 - 1;
    degs := flatten last degrees Q.dd_2;
    ok := 1;
    L := {};
    degloop := unique degs;
    deg := first degloop;
    while #L < r do (
	--This algorithm computes the correct columns to select
    	(s,a,b) := alphaBeta selectColumns(deg,Q.dd_2);
	if (s != a or s != b) then (
	    L = L | splice{(min(a-1,b)-#L):deg};
	    ok = 0;
	) else (
	    if ok == 1 then L = L | select(degs,d -> d == deg);
	);
    	degloop = drop(degloop,1);
	if degloop != {} then deg = first degloop;
    ); 
    cols := for i from 0 to #degs-1 list (	
    	j := position(L, l -> l == degs#i);
	if j === null then (
	    i   
	) else (    	    
	    L = drop(L,{j,j});
	    continue    
	)    		
    );
    if opts.Ideal then (
        ideal gens kernel transpose (random(Q_2,Q_2)*(Q.dd_3))^cols
    ) else (
        h := sum L - sum flatten degrees Q_2 + sum flatten degrees Q_3 - sum flatten degrees Q_4;
        betti chainComplex {random(R^1,(target (Q.dd_3)^cols)**R^{-h}),(Q.dd_3)^cols**R^{-h},
	    Q.dd_4**R^{-h}, Q.dd_5**R^{-h}}
    )
)
minimalCurve Ideal := opts-> I -> minimalCurve(raoModule I,Ideal => opts.Ideal)

--ACM curves
makeCastelnuovo = method(Options => {UPP => true})
makeCastelnuovo(ZZ,List) := opts -> (d,bin) -> (
    --generates a list of continuation of castelnuovo functions
    L := flatten apply(bin, C -> (
	m := max C;
    	if opts.UPP and C#-1 < C#-2 then (
	    m = min(d-sum C,C#-1-1);
	) else m = min(d-sum C,C#-1);     
    	apply(splice{1..m}, i -> C |{i})		    
    )
    );
    (select(L, C -> sum C == d), select(L, C -> sum C < d))   
)
castelnuovo = method(Options => {UPP => true})
castelnuovo ZZ := opts -> d -> (
    --generates all castelnuovo functions of d points in P2 
    --by default in uniform position
    flatten apply(splice{2..floor (sqrt (2*d+1/4-1/2))}, s -> (
	finished := {};
	bin := {};
	unfinished := {splice{1..s}};
    	while (
	    (finished, unfinished) = makeCastelnuovo(d,unfinished,UPP=>opts.UPP);	    
	    bin = bin | finished;
	    #unfinished > 0
	) do ();
	bin    
    )	
    )
) 
diff List := G -> (G | {0}) - ({0} | G)
bettiToList := B -> (
    --turns a BettiTally into a list of degrees in the free resolution
    n := max apply(keys B, k -> first k);
    for i from 0 to n list (
    	b := select(keys B, k -> first k == i);
	flatten apply(b, j -> splice{B#j: last j})	
    )    
)
listToBetti := L -> (
    --turns a list of degrees in the free resolution into a BettiTally
    L = L / tally;
    new BettiTally from 
    flatten apply(#L, i -> flatten apply(keys L#i, j -> (i, {j},j) => L#i#j))    
)
degreeMatrix = method()
degreeMatrix BettiTally := Matrix => B -> (
    --turns the BettiTally of an ACM curve into a degree matrix
    if not isACMBetti B then return matrix {{0}};
    L := drop(bettiToList B,1);
    matrix apply(rsort L#0, l -> 
	apply(rsort L#1, m -> m-l))   
)
isACMBetti = method(Options => {Smooth => false})	   
isACMBetti BettiTally := Boolean => opts -> B -> (
    --checks if there is an ACM curve having Betti table B
    L := bettiToList B;
    if #L != 3 then return false;
    if opts.Smooth then (
	all(L#2-drop(L#1,1), i -> i>0) and all(drop(L#2,-1)-drop(L#1,2), i -> i>0)
    ) else all(rsort(L#2)-drop(rsort L#1,-1), i -> i>0)
)
betti List := BettiTally => opts -> H -> (
    --takes a postulation character and returns the Betti table of 
    --the general ACM curve having this character
    L := {0} | drop(diff diff H,1);
    new BettiTally from (
	 {(0,{0},0) => 1} |
	 apply(select(#L, i-> L#i < 0), i-> (1,{i},i) => -L#i) | 
	 apply(select(#L,i->L#i>0),i-> (2,{i},i) => L#i)
    )
)
specialize = method()
specialize BettiTally := List => B -> (
    --returns all possible specialization via one cancellation
    L := bettiToList B;
    if #(L#1) > min(L#1) then return {};	  
    deg := splice{min(L#1)+1..max(L#2)-1};
    Sp := unique apply(deg , d -> {L#0, L#1 | {d}, L#2 | {d}});
    select(Sp / listToBetti, b -> isACMBetti b) 
)
allBetti = method(Options => {Smooth => false})
allBetti List := opts -> H ->(
    --takes a postulation character and returns all Betti tables
    --of ACM curves having that character
    B := betti H;
    final := {B};
    current := {B};
    while (
    	L := bettiToList first current;
	#(L#1) <= min(L#1)
    ) do (
    	current = flatten apply(current, b -> specialize(b));
	if current == {} then break;
	final = unique (final | current);    
    );
    if opts.Smooth then select(final, B -> isACMBetti(B,Smooth => true)) else final   
)
randomDeterminantalIdeal = method()
randomDeterminantalIdeal (Ring,Matrix) := (R,M) -> (
    --produces a random determinantal ideal in the ring R
    --with forms of degrees specified by the matrix M
    --nonpositive degrees entries are set to be 0
    if M != matrix{{}} then (
    	N := matrix apply(entries M, row -> apply(row, a-> if a <= 0 then 0 else random(a,R)))
    ) else return ideal(0);
    minors(numcols N,N)    
)
randomDeterminantalIdeal Matrix := M -> (
    x := getSymbol "x";
    R := (ZZ/101)(monoid[x_0..x_3]);
    randomDeterminantalIdeal(R,M)
)

--Extracting invariants
sectionRing = method()
sectionRing Ideal := Module => I -> (
    HH^0((sheaf comodule I)(*))    
)
spectrum = method()
spectrum Ideal := I -> (
    S := sectionRing I;
    d := 0;
    sp := 0;
    while (
    	sp = hilbertFunction(d,S)-2*hilbertFunction(d-1,S)+hilbertFunction(d-2,S);
	sp != 0	
    ) list sp do (d = d+1;)
)
random(ZZ,Ideal) := opts -> (d,I) -> (
    B := super basis(d,I);
    R := ring I;
    (B*random(R^(numcols B),R^1))_(0,0)
)
planarSection = method()
planarSection Ideal := I -> (
    kk := coefficientRing ring I;
    n := numgens ring I;
    x := getSymbol "x";
    kernel map((ring I)/saturate(I+random(1,ring I)), kk(monoid[x_0..x_(n-2)]), drop(gens ring I,-1))     
)
castelnuovo Ideal := opts -> I -> (
    if dim I > 1 then I = planarSection I;
    d := 0;
    c := 0;
    while (
	c = hilbertFunction(d,I)-hilbertFunction(d-1,I);
	c != 0
    ) list c do (d = d+1;)   
)
postulation = method()
postulation Ideal := List => I -> (
    if dim I > 2 then I = planarSection I;    
    i := 0;
    c := 0;
    while (
	c = hilbertFunction(i,I)-2*hilbertFunction(i-1,I)+hilbertFunction(i-2,I);
	c != 0
    ) list c do (i = i+1;)  
)
hilbertDimension = method()    
hilbertDimension Ideal := ZZ => I -> (
    B := diff diff postulation I;
    M := raoModule I;
    1 + sum apply(#B, i -> -B#i*(hilbertFunction(i-4,M)-hilbertFunction(i,module I)))- 
	numcols basis(0,Hom(M,M))
)

tangentDimension = method()	  --tangent space
tangentDimension Ideal := ZZ => I -> (
    rank HH^0(sheaf Hom(I/I^2,(ring I)/I))  
)

--Plotting
dgTable = method()
dgTable List := L ->(
    --Takes a list of Divisors or Ideals
    --returns a (degree, genus) occurence matrix    
    Ldg := apply(L, C -> (lift(degree C,ZZ), lift(genus C,ZZ)));
    dmax := max apply(Ldg,dg->first dg);
    dmin := min apply(Ldg,dg->first dg);
    gmax := max apply(Ldg,dg->last dg);
    gmin := min apply(Ldg,dg->last dg);
    M := mutableMatrix map(ZZ^(gmax-gmin+1),ZZ^(dmax-dmin+1),0);
    for dg in Ldg do (
	j := first dg - dmin;
	i := gmax - last dg;
    	M_(i,j) = M_(i,j)+1;		
    );
    yaxis := reverse splice{gmin..gmax};
    xaxis := toString splice{dmin..dmax};
    xaxis = replace(" ([0-9]),", "  \\1", replace("\\{", "g/d| ", replace("\\}", "", xaxis)));
    S := toString(transpose matrix{yaxis} | matrix M) | "\n";
    S = replace("matrix ", "", replace("\\{\\{", "{", replace("\\}\\}", "", S)));
    S = replace("\\}, ","\n", S);
    S = replace("\\{([0-9]+)", "\\1 |", S);
    S = replace(" ([0-9]),", "  \\1,", S);
    S = replace(",","",S);
    S = replace("\n([0-9]) ", "\n \\1 ", S);
    S = replace(" ([0-9])\n", "  \\1\n", S);
    S = replace("  0", "  .", S);
    S = net substring(S, 0, #S-1);
    xaxisbar := "---+";
    for i from 4 to width S do xaxisbar = xaxisbar | "-";
    S || xaxisbar || replace(",", "", xaxis)
    --transpose matrix{yaxis} | (matrix M || matrix{xaxis})
)

--Documentations


--Tests
TEST

X = scroll {1,2};
C = divisor({3,4},X);
I = ideal C;
assert(degree I == degree C and genus I == genus C)

X = blowupPlane 6;
C = divisor({4,2,1,1,1,1,1},X);
I = ideal C;
assert(degree I == degree C and genus I == genus C)

end


-------------------------------------------------------------------------------------
restart
uninstallPackage "SpaceCurves2"
installPackage "SpaceCurves2"



X = scroll(2,3);
C = divisor({2,7},X);
I = ideal C;
spectrum I
betti res I
hilbertDimension I
