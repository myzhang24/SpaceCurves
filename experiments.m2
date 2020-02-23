--Minimal curve experiments
needsPackage "SpaceCurves"

minimalCurveAnalysis = method()
minimalCurveAnalysis Module := M -> (
    R := ring M;
    if M == 0 then return ideal(R_0,R_1);
    assert(dim M == 0);
    Q := res M;
    r := 1 + rank Q_3 - rank Q_4;	--This is rank of Q.dd_3
    columns := subsets(rank Q_2,r);
    columns = apply(columns, col-> (-sum (flatten degrees Q_2)_col,col));
    columns = (sort columns) / last;	
    -- This sorts the selection of columns of greatest degree
    -- Note that degress are typically negative
    psi = random(Q_2,Q_2)*Q.dd_3;
    apply(columns, col -> (
	D := -(flatten degrees Q_2)_col;
	J := ideal gens kernel transpose (psi^col);
	(D,codim J,degree J, betti res J)
   ))
{*    
    psi := random(Q_2,Q_2)*Q.dd_3;
    for col in columns do (
    	phi := psi^col;
--	P := res(coker phi,LengthLimit=>2);
	J := ideal gens kernel transpose phi;
	    if codim J == 2 then break J
    )
*}
)

alphaBeta = M -> (
    kk := coefficientRing ring M;
    t := getSymbol "t";
    S := kk[t];
    L := apply(4,i->random(1,S)+random(0,S));
    (A,B,C) := smithNormalForm sub(M,matrix{L});
    D := apply(min(numrows A,numcols A), i-> A_(i,i));
    (numcols M,#select(D,d->d!=0),#select(D,d->d==1))    
)

selectColumns = (d,M) -> (
    L := select(flatten last degrees M,D->D<= d);
    M_(splice{0..#L-1})
)

q = M ->(
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
    	(s,a,b) := alphaBeta selectColumns(deg,Q.dd_2);
	if (s != a or s != b) then (
	    L = L | splice{(min(a-1,b)-#L):deg};
	    ok = 0;
	) else (
	    if ok == 1 then L = L | select(degs,d -> d == deg);
	);
    	degloop = drop(degloop,1);
	deg = first degloop;
    ); 
    L       
)
minimalCurveNew = method()
minimalCurveNew Module := M -> (
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
    	(s,a,b) := alphaBeta selectColumns(deg,Q.dd_2);
	if (s != a or s != b) then (
	    L = L | splice{(min(a-1,b)-#L):deg};
	    ok = 0;
	) else (
	    if ok == 1 then L = L | select(degs,d -> d == deg);
	);
    	degloop = drop(degloop,1);
	deg = first degloop;
    ); 
    cols := for i from 0 to #degs-1 list (	
    	j := position(L, l -> l == degs#i);
	if j === null then (
	    continue    
	) else (    	    
	    L = drop(L,{j,j});
	    i    
	)    		
    );
    psi := random(Q_1,Q_1)*Q.dd_2;
    saturate(minors(r,psi_cols), ideal vars R)   
)

--Boij-Sodeberg experiments
needsPackage "BoijSoederberg"
List - ZZ := (L,P) -> apply(L,l->l-P)
List + ZZ := (L,P) -> apply(L,l->l+P)
pureCurve = method()
pureCurve List := L -> (
    assert(#L == 5 and sort L == L);
    n := getSymbol "n";
    T := getSymbol "T";
    R := QQ(monoid[T,n]);
    B := apply(#L, i -> product ((drop(L,{i,i}) - L#i) / abs));
    B = apply(B, d -> lift(lcm B / d,ZZ)*R_1);
    r := -B#4 + B#3 + 1;
    h := r*L#2-L#3*B#3+L#4*B#4;
    D := {0,L#2-h,L#3-h,L#4-h};
    B = {1,r,B#3,B#4};
    (D,B)
{*    
    x  = getSymbol "x";
    R := ZZ/101[x_0..x_3];
    F := apply(4, i -> R^{B#i:-D#i});    
    Phi := apply(3, i -> random(F#i,F#(i+1)));
    T := betti chainComplex Phi;
    P := hilbertPolynomial(4,T,Projective=>false);
    degree T, 1-sub(P,matrix{{0}}),T
*}
)
dgs = method()
dgs (List,List) := (D,B) -> (
    R := ring B#1;
    P := sum apply(#D, i -> (-1)^i*B#i*binomial(R_0+3-D#i,3));
    (sub(P,{R_0 => 1}) - sub(P, {R_0 => 0})), 1-sub(P,{R_0 => 0}), D#1    
)
binomial (RingElement,ZZ) := (r,k) -> (
    1/k! * product apply(k, i -> r-i)    
)
genusBound = method()
genusBound (RingElement,RingElement,RingElement) := (d,g,s) -> (
    R := ring d;
    sub(1/(2*s)*d^2+1/2*d*(s-4)+1-g,QQ[R_1])    
)

randomElement = (d,I) -> (
    G := mingens I;
    J := ideal(G*random(source G,(ring I)^{-d}));
    J_0
)

end


--Generation 

restart
load "experiments.m2"
(d,g,s) = dgs pureCurve {0,1,2,6,7}
genusBound(d,g,s)

R = ZZ/101[x_0..x_3];
X = quadricSurface(R);
Y = cubicSurface(R);
Z = quarticSurfaceRational(R);
dmax = 10
LD = flatten apply(splice{1..dmax}, j -> 
    smoothDivisors(j,X) | smoothDivisors(j,Y) | smoothDivisors(j,Z))
time LC = apply(LD,D->curve D);
netList (unique LC / ideal / res / betti)

--Conjecture 5: all non-ACM integral curves satisfy r > e, and thus c_+ > b_+.

--6 points in P2 with multiplicity
restart
load "experiments.m2"
S = ZZ/101[x,y,z];
M = diagonalMatrix{1,1,1} | matrix{{1},{1},{1}} | random(S^3,S^2);
P = apply(entries transpose M, l -> minors(2,matrix{gens S,l}));
B = {4,3,2,1,1,0};
I = intersect(apply(6,i-> (P#i)^(B#i)));
apply(10,d->hilbertFunction(d,I))
