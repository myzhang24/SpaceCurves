newPackage(
        "SpaceCurves",
        Version => "1.0", 
        Date => "August 1st 2017",
        Authors => {{Name => "Frank Schreyer", 
                  Email => "schreyer@math.uni-sb.de", 
                  HomePage => "https://www.math.uni-sb.de/ag/schreyer/"},
	      {Name => "Mike Stillman", 
                  Email => "mike@math.cornell.edu", 
                  HomePage => "http://www.math.cornell.edu/~mike/"},
	      {Name => "Mengyuan Zhang", 
                  Email => "myzhang@berkeley.edu", 
                  HomePage => "https://math.berkeley.edu/~myzhang/"}
	      },
        Headline => "Generation and database of space curves",
        DebuggingMode => true
        )

export {
    "AbstractSurface",
    "IntersectionPairing",
    "CanonicalClass",
    "Hyperplane",
    "Chi",
    "AbstractDivisor",
    "DivisorClass",
    "RealizedSurface",
    "ExtraData",    	  
    "RealizedDivisor",
    "Postulation",
    "postulation",	  
    "abstractSurface",
    "implementedSurfaces",	  
    "abstractDivisor",	  	  
    "abstractQuadric",
    "abstractCubic",
    "linesOnCubic",
    "abstractHypersurface",
    "abstractQuartic",
    "ACMPostulations",
    "realize",
    "isIrreducible",
    "isSmooth",
    "dgTable",
    "hartshorneRaoModule",
    "hilbertBurchComputation",
    "degreeMatrix",
    "minimalCurveInLiaisonClass",
    "smoothDivisors",
    "ciCurves",
    "generateSmoothCurves",
    "smooth"
    }

--I. Data types

AbstractSurface = new Type of HashTable
-- Name, IntersectionPairing, Hyperplane, CanonicalClass, Chi
AbstractDivisor = new Type of HashTable
-- AbstractSurface, DivisorClass
RealizedSurface = new Type of HashTable
-- AbstractSurface, Ideal, ExtraData
RealizedDivisor = new Type of HashTable
-- AbstractDivisor, RealizedSurface, Ideal
Postulation = new Type of List
-- The postulation character of a curve

--II. AbstractSurfaces

net AbstractSurface := X -> net X.Name
net RealizedSurface := X -> net X.Ideal
ideal RealizedSurface := X -> X.Ideal

abstractSurface = method()
abstractSurface RealizedSurface := X -> X.AbstractSurface
abstractSurface AbstractDivisor := D -> D.AbstractSurface
abstractSurface List := data -> (
    -- data is a List containing the following keys
    -- Name, IntersectionPairing, Hyperplane, CanonicalClass, Chi
    M := data#1;
    if numRows M != numColumns M then error "expected square matrix";
    -- TODO: add hodge index check.
    new AbstractSurface from {
	symbol Name => data#0,
        symbol IntersectionPairing => data#1,
        symbol Hyperplane => data#2,
        symbol CanonicalClass => data#3,
	symbol Chi => data#4
        }
    )

abstractQuadric = abstractSurface(
    {"Quadric surface",matrix{{0,1},{1,0}}, {1,1}, {-2,-2},1}
)
abstractCubic = abstractSurface(
    -- generators are L, -E1, ..., -E6
    {"Cubic surface",
    diagonalMatrix{1, -1, -1, -1, -1, -1, -1},
    {3,1,1,1,1,1,1}, 
    -{3,1,1,1,1,1,1},
    1}
)
linesOnCubic = method()
linesOnCubic := () -> (
    Ds := apply(entries diagonalMatrix{1, -1, -1, -1, -1, -1, -1}, 
             d -> abstractDivisor(d,abstractCubic)
             );
    L := Ds#0;
    Es := drop(Ds,1);
    join(
        Es,
        for p in subsets(splice {1..6}, 2) list (
            L - Ds#(p#1) - Ds#(p#0)
            ),
        for i from 0 to 5 list (
            2*L - sum drop(Es, {i,i})
            )
        )
    )
abstractHypersurface = method()
abstractHypersurface ZZ := d -> abstractSurface(
	{"Hypersurface",
	 matrix{{d}},
	 {1},	 --Hyperplane class O(1) is denoted by 1
	 {-4+d}, --CanonicalClass is O(-d+4)
	 1+binomial(d-1,3)
	}
    )
abstractQuartic = method()
abstractQuartic String := Input -> (
    if Input == "line" then return abstractSurface(
	 {"Quartic surface with a " | Input,
	matrix{{4,1},{1,-2}},
	{1,0},
	{0,0},
	2});
    if Input == "conic" then return abstractSurface(
	 {"Quartic surface with a " | Input,
	matrix{{4,2},{2,-2}},
	{1,0},
	{0,0},
	2});
    if Input == "twisted cubic" then return abstractSurface(
	 {"Quartic surface with a " | Input,
	matrix{{4,3},{3,-2}},
	{1,0},
	{0,0},
	2});
    if Input == "rational quartic" then return abstractSurface(
	 {"Quartic surface with a " | Input,
	matrix{{4,4},{4,-2}},
	{1,0},
	{0,0},
	2});
    if Input == "plane elliptic" then return abstractSurface(
	 {"Quartic surface with a " | Input,
	matrix{{4,3},{3,0}},
	{1,0},
	{0,0},
	2});
    if Input == "space elliptic" then return abstractSurface(
	 {"Quartic surface with a " | Input,
	matrix{{4,4},{4,0}},
	{1,0},
	{0,0},
	2});
    error "not implemented yet for your type of surface";
)
isSmooth = method()
isSmooth Ideal := (I) -> (
    c := codim I;
    dim(I + minors(c, jacobian I)) == 0
    )
isSmooth RealizedSurface := X -> isSmooth ideal X
implementedSurfaces = () -> (
    {abstractQuadric,
    abstractCubic,
    abstractQuartic "line",
    abstractQuartic "conic",
    abstractQuartic "twisted cubic",
    abstractQuartic "rational quartic",
    abstractQuartic "plane elliptic",
    abstractQuartic "space elliptic"	
   }   
)
--III.AbstractDivisors

net AbstractDivisor := D -> net D.DivisorClass
net RealizedDivisor := D -> net D.Ideal
ideal RealizedDivisor := C -> C.Ideal

abstractDivisor = method()
abstractDivisor(List, AbstractSurface) := (C, X) -> (
    new AbstractDivisor from {
        symbol DivisorClass => C,
        symbol AbstractSurface => X
        }
    )
ZZ * AbstractDivisor := (n,D) -> (
    abstractDivisor(n * D.DivisorClass, D.AbstractSurface)
    )
AbstractDivisor + AbstractDivisor := (C,D) -> (
    assert(C.AbstractSurface === D.AbstractSurface);
    abstractDivisor(C.DivisorClass + D.DivisorClass, D.AbstractSurface)
    )
AbstractDivisor - AbstractDivisor := (C,D) -> (
    assert(C.AbstractSurface === D.AbstractSurface);
    abstractDivisor(C.DivisorClass - D.DivisorClass, D.AbstractSurface)
    )
AbstractDivisor * AbstractDivisor := (C,D) -> (
    X := C.AbstractSurface;
    assert(X === D.AbstractSurface);
    assert(X.IntersectionPairing =!= null);
    (matrix{C.DivisorClass} * X.IntersectionPairing * 
	transpose matrix{D.DivisorClass})_(0,0)
    )
AbstractDivisor == AbstractDivisor := (C,D) -> (
    C.AbstractSurface === D.AbstractSurface and 
    C.DivisorClass == D.DivisorClass
    )
degree AbstractDivisor := C -> (
    X := C.AbstractSurface;
    return (matrix{C.DivisorClass} * X.IntersectionPairing * 
	transpose matrix{X.Hyperplane})_(0,0);
    )
degree RealizedDivisor := C -> degree ideal C
genus AbstractDivisor := C -> (
    X := C.AbstractSurface;
    K := abstractDivisor(X.CanonicalClass,X);
    return 1/2*((K+C)*C)+1;
    )
genus RealizedDivisor := C -> genus ideal C
chi AbstractDivisor := C -> (
    X := C.AbstractSurface;
    K := abstractDivisor(X.CanonicalClass,X);
    1/2 * (C * (C-K)) + X.Chi
    )

isIrreducible = method()
isIrreducible AbstractDivisor := Boolean => C -> (
    X := C.AbstractSurface;
    if X.Name == "Cubic surface" then (
    	H := abstractDivisor(X.Hyperplane,X);
    	twentysevenLines := linesOnCubic();
    	B := any(twentysevenLines, L -> L.DivisorClass == C.DivisorClass) or 
	-- these are the conics:
    	any(twentysevenLines, L -> (H-L).DivisorClass == C.DivisorClass) or 
	(
     	    all(twentysevenLines, L -> L * C >= 0)
      	    and
     	    C*C > 0
     	);
    	return B;
    );
    if X.Name == "Quadric surface" then (
    	a := first C.DivisorClass;
	b := last C.DivisorClass;
	if a > 0 and b > 0 then return true;
	if a*b == 0 and a+b == 1 then return true;
	return false;	
    );
    error "Not implemented for your type of surface yet";
)
isIrreducible RealizedDivisor := Boolean => C -> isPrime ideal C
isSmooth AbstractDivisor := C -> (
    if C.AbstractSurface.Name == "Quadric surface" then return isIrreducible C;
    if C.AbstractSurface.Name == "Cubic surface" then return isIrreducible C;
    if C.AbstractSurface.Name == "Hypersurface" then (
    	if first C.DivisorClass > 0 then return true
	else return false;	
    );
    error "Not implemented yet for this type of surface";  
)
isSmooth RealizedDivisor := C -> isSmooth ideal C

--IV. Realization

realize = method(Options => {Ring => null})
realize AbstractSurface := opts -> X -> (
    R := if opts#Ring =!= null then 
        opts#Ring 
      else (
        x := getSymbol "x";
        ZZ/32003[x_0..x_3]
      );
    assert(numgens R == 4);
    kk := coefficientRing R;
    
    if X.Name == "Cubic surface" then (
        y := getSymbol "y";
        S := kk(monoid[y_0..y_2]);
        RS := R ** S;
        while (
            M := diagonalMatrix({1,1,1}) | matrix{{1},{1},{1}} | random(S^3,S^2);
            points := apply(6,i-> ideal (vars S * syz transpose M_{i}));
            I := intersect points;
            fI := res I;
            phi := map(S,R,fI.dd_1);
            matS := sub(diff(transpose sub(vars S,RS),sub(vars R,RS) * sub(fI.dd_2,RS)),R);
            f := ideal det matS;
            dim (f + ideal jacobian f) != 0
            ) do ();
        return new RealizedSurface from {
            symbol AbstractSurface => X,
            symbol Ideal => f, 
            symbol ExtraData => {phi, points}
            }
        );
    if X.Name == "Quadric surface" then (
        IQ := ideal(R_0*R_3-R_1*R_2);
        return new RealizedSurface from {
	    symbol AbstractSurface => X,
	    symbol Ideal => IQ,
	    symbol ExtraData => {ideal(R_0,R_1),ideal(R_0,R_2)}
	    }
        );
    if X.Name == "Hypersurface" then (        
	return new RealizedSurface from {
	    symbol AbstractSurface => X,
	    symbol Ideal => ideal random(4+first X.CanonicalClass,R),
	    symbol ExtraData => {}
	    }    	
    );
    if select("Quartic",X.Name) != {} then (
    	if select("line",X.Name) != {} then (
	    return new RealizedSurface from {
	    	symbol AbstractSurface => X,
		symbol Ideal => ideal(random(3,R)*R_2+random(3,R)*R_3),
		symbol ExtraData => {ideal(R_2,R_3)}
      	    }     
	);	
    	if select("conic",X.Name) != {} then (
	    return new RealizedSurface from {
	    	symbol AbstractSurface => X,
		symbol Ideal => ideal(random(3,R)*R_3+random(2,R)*(R_1^2-R_0*R_2)),
		symbol ExtraData => {ideal(R_3,R_1^2-R_0*R_2)}
      	    }     
	);
	if select("twisted cubic",X.Name) != {} then (
	    IT := minors(2,matrix{{R_0,R_1,R_2},{R_1,R_2,R_3}}),
	    return new RealizedSurface from {
	    	symbol AbstractSurface => X,
		symbol Ideal => ideal ((gens IT)*random(R^3,R^{-2}))_(0,0),
		symbol ExtraData => {IT}
      	    }     
	);
	if select("rational quartic",X.Name) != {} then (
	    IR := monomialCurveIdeal(R,{1,3,4});
	    IQR := ideal (gens IR)*(transpose random(R^1,R^{-2,-3,-3,-3}))_(0,0),  
	    return new RealizedSurface from {
	    	symbol AbstractSurface => X,
		symbol Ideal => IQR,
		symbol ExtraData => {IR}
      	    }     
	);
    	if select("plane elliptic",X.Name) != {} then (
	    E := R_2*R_1^2-R_0^3+R_0*R_2^2;
	    return new RealizedSurface from {
	    	symbol AbstractSurface => X,
		symbol Ideal => ideal (random(3,R)*R_3+random(1,R)*E),
		symbol ExtraData => {ideal(R_3,E)}
      	    }     
	);  
        if select("space elliptic",X.Name) != {} then (
	    Q := random(2,R);
	    return new RealizedSurface from {
	    	symbol AbstractSurface => X,
		symbol Ideal => ideal (random(2,R)*(R_0*R_3-R_1*R_2)+random(2,R)*Q),
		symbol ExtraData => {ideal(R_0*R_3-R_1*R_2,Q)}
      	    }     
	);    	
    );
    error "Not implemented yet for this type of surface";
    )

realize (AbstractDivisor,RealizedSurface) := opts -> (C, X) -> (
    if C.AbstractSurface =!= X.AbstractSurface then 
    error "expected divisor class on the given surface";
    if X.AbstractSurface.Name == "Cubic surface" then (
        phi := X.ExtraData#0;
	pts := X.ExtraData#1;
        S := target phi;
        R := source phi;
        ab := C.DivisorClass;
        a := ab_0;
        ipts := trim intersect (for i from 1 to 6 list (pts_(i-1))^(ab_i));
        gipts := gens ipts;
        if min flatten degrees source gipts > a then return null else (
            cplane := ideal (gipts*random(source gipts,S^{-a}));
            SC := S/cplane;
            cspace := trim ker map(SC,R,phi.matrix);
            return new RealizedDivisor from {
		symbol AbstractDivisor => C,
		symbol RealizedSurface => X,
		symbol Ideal => cspace
		} ;
        )
    );
    if X.AbstractSurface.Name == "Quadric surface" then (
	RC := ring X.Ideal;
	kk := coefficientRing RC;
	z := getSymbol "z";
	cox := kk(monoid[z_0..z_3,Degrees=>{{0,1},{0,1},{1,0},{1,0}}]);
    	segre := {cox_0*cox_2,cox_0*cox_3,cox_1*cox_2,cox_1*cox_3};
	I := ideal random(C.DivisorClass,cox);
	if I == 0 then return null;
	segre = apply(segre, p -> sub(p,cox/I));
	return new RealizedDivisor from {
	    symbol AbstractDivisor => C,
	    symbol RealizedSurface => X,
	    symbol Ideal => kernel map(cox/I,RC,segre)
	};
    ); 
    if X.AbstractSurface.Name == "Hypersurface" then (
    	SP := ambient ring ideal X;
	f := sub((ideal X)_0,SP);
	return new RealizedDivisor from {
	    symbol AbstractDivisor => C,
	    symbol RealizedSurface => X,
	    symbol Ideal => ideal(random(first C.DivisorClass,SP),f)   
	};	
    );
    error "not implemented yet for your type of surface"
)
realize AbstractDivisor := opts -> C -> (
    realize(C,realize(C.AbstractSurface, Ring => opts#Ring))
)


--V. Minimal curves in liaison class

minimalCurveInLiaisonClass = method()
minimalCurveInLiaisonClass(Ideal):= J-> (
    M := hartshorneRaoModule J;
    minimalCurveInLiaisonClass(M)
    )
minimalCurveInLiaisonClass(Module) := M -> (    
 -- a probalistic algorithm which over large finite fields will produce
 -- a minimal curve in the liaison class corresponding to M with high probability
    S := ring M; 
    assert(dim M ==0);  
    fM:= res(M,LengthLimit=>2); 
    --betti fM
    r:=rank fM_1-rank fM_0; -- rank of the 2nd syzygy module of M
    degs:=sort flatten degrees fM_2;
    degList:=unique subsets(degs,r-1);
    degList=sort apply(degList,c->(sum c,c))/last;
    apply(#degList,i->sum degList_i);
    i:=0;
    while (
	L:=-degList_i;
	G:=S^L;
	I:=hilbertBurchComputation(M,G);
	class I === class null)
        do (i=i+1);
    --betti I, L
    return I;
)
hilbertBurchComputation = method()
hilbertBurchComputation(Module,Module) := (M,G) -> (
    if not ring M === ring G then error "expected modules over the same polynomial ring";
    -- add check: isFree G == true
    fM := res(M,LengthLimit=>2);
    if not 1+rank fM_0-rank fM_1 +rank G == 0 then 
    error "the free module has the wrong rank";
    hom := random(fM_2,G);
    hilbBurch := fM.dd_2*hom;
    degLim := -sum(-flatten degrees G) + sum(-flatten degrees fM_1) -sum(-flatten degrees fM_0);
    syzHilbBurch := syz(transpose hilbBurch,DegreeLimit=>degLim);
    ok := rank source syzHilbBurch == rank fM_0+1 and 
    degrees source syzHilbBurch ==(-degrees fM_0|{{degLim}});
    if ok then return trim ideal(transpose syzHilbBurch_{ rank fM_0} * fM.dd_2) 
    else return null;
)
hartshorneRaoModule=method()
hartshorneRaoModule(Ideal) := I -> (
    S := ring I;
    d := dim S;
    assert( dim I == 2);
    omega := Ext^(d-2)(S^1/I,S^{-d});
    fomega := res omega;
    HRao := coker(Hom(fomega.dd_(d-2)_{0..(rank fomega_(d-2)-2)},S^{-d}));
    return HRao;
)

--VI. Generation and Plotting
dgTable = method()
dgTable List := L ->(
    --Takes a list of AbstractDivisors or RealizedDivisors
    --returns a (degree, genus)    
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
    return matrix M;
)

smoothDivisors = method()
smoothDivisors (ZZ, AbstractSurface) := (d,X) -> (
    --Produces a list of irreducible abstract divisors of degree d on X
    Ld := {};
    if X.Name == "Cubic surface" then (
	return flatten for a from ceiling(d/3) to d list (
	    degreeList := apply(select(partitions(3*a-d),p->#p<=6),q ->
		{a} | toList q | splice{(6-#q):0});
	    degreeList = select(degreeList, L -> L#0 >= L#1+L#2+L#3);
	    --This gives unqiue representation up to change of 6 points 
	    Ld = apply(degreeList, L-> abstractDivisor(L,X));
	    select(Ld, D -> isIrreducible D)  
	);
    );
    if X.Name == "Quadric surface" then (
	maxdeg := floor(1/2*d);
	return for a from 1 to maxdeg list abstractDivisor({a,d - a},X);
    );
    if X.Name == "Hypersurface" then (
	surfd := 4 + first X.CanonicalClass;
	if d % surfd =!= 0 then return {};
	return abstractDivisor({d // surfd},X);
    );
    if select("Quartic", X.Name) != {} then (
    	if select("line",X.Name) != {} then (
	    Ld = for a from floor(-sqrt(d^2/144+1/18)+d/4) to 
	    ceiling(+sqrt(d^2/144+1/18)+d/4) list (
		abstractDivisor({a,d-4*a},X)
		);
	    return select(Ld, ad -> genus ad >= 0);
	);
        if select("conic",X.Name) != {} then (
	    if d % 2 == 1 then return {};
	    Ld = for a from floor(-sqrt(d^2/48+1/6)+d/4) to 
	    ceiling(sqrt(d^2/48+1/6)+d/4) list (
		abstractDivisor({a,lift(d/2-2*a,ZZ)},X)
		);
	    return select(Ld, ad -> genus ad >= 0);
	);
        if select("twisted cubic",X.Name) != {} then (
	    Ld = for a from floor(-sqrt(9*d^2/272+9/34)+d/4) to 
	    ceiling(sqrt(9*d^2/272+9/34)+d/4) list (
		if (d-4*a) % 3 != 0 then continue;
		abstractDivisor({a,lift((d-4*a)/3,ZZ)},X)
		);
	    return select(Ld,ad -> genus ad >= 0);
	);
        if select("rational quartic",X.Name) != {} then (
	    if d % 4 != 0 then return {};
	    Ld = for a from floor(-sqrt(d^2/24+1/3)+d/4) to 
	    ceiling(sqrt(d^2/24+1/3)+d/4) list (
		abstractDivisor({a,lift(d/4-a,ZZ)},X)
		);
	    return select(Ld,ad -> genus ad >= 0);
	);
        if select("plane elliptic",X.Name) != {} then (
	    Ld = for a from floor(-sqrt(d^2/16+1/2)+d/4) to 
	    ceiling(sqrt(d^2/16+1/2)+d/4) list (
		if (d-4*a) % 3 != 0 then continue;
		abstractDivisor({a,lift((d-4*a)/3,ZZ)},X)
		);
	    return select(Ld,ad -> genus ad >= 0);
	);
        if select("space elliptic",X.Name) != {} then (
	    if d % 4 != 0 then return {};
	    Ld = for a from floor(-sqrt(d^2/16+1/2)+d/4) to 
	    ceiling(sqrt(d^2/16+1/2)+d/4) list (
		abstractDivisor({a,lift(d/4-a,ZZ)},X)
		);
	    return select(Ld,ad -> genus ad >= 0);
	);
    );
    error "not implemented yet for your type of surface";	
)
smoothDivisors (ZZ, RealizedSurface) := (d,X) -> (
   --produces a list of irreducible realized curves of degree d on X
   return apply(smoothDivisors(d,X.AbstractSurface), aD -> 
       realize(aD,X));	
)
ciCurves = method(Options => 
    {symbol realize => false, Ring => null})
ciCurves ZZ := opts -> d -> (
    --produce all ci curves of degree d
    div := for i from 2 to floor sqrt d when d % i == 0 list i;
    Ld := apply(div, deg -> 
	abstractDivisor({d // deg},abstractHypersurface(deg)));
    if opts.realize then (
    	return apply(Ld, ad -> realize(ad,Ring=>opts#Ring));
    ) else return Ld;           
)
generateSmoothCurves = method(Options => 
    {symbol realize => false, Ring => null})
generateSmoothCurves ZZ := opts -> d -> (
    generateSmoothCurves({d},realize => opts.realize, Ring => opts#Ring)
)
generateSmoothCurves List := opts -> L -> (
    Surfaces := implementedSurfaces();
    --generates all curves of the degrees in the list on all the implemented surfaces
    Lad := flatten apply(L, d-> flatten apply(Surfaces, S->
	    smoothDivisors(d,S)) | ciCurves(d));
    Lad = delete(null,Lad);
    if opts.realize then (
	error "To be implemented";
    ) else return Lad;
)

--VII.ACM curves
binomial (ZZ,ZZ) := (n,p) -> (
    if p >= 0 and n >= p then return lift(n!/(p!*(n-p)!),ZZ);
    if p >= 0 and n < p then return 0;
    if p < 0 and p <= n and n <= -1 then return (-1)^(-n+p)*binomial(-p-1,-n-1);
    if p < 0 and (n < p or n >= 0) then return 0;  
)
postulation = method()
postulation List := Postulation => L -> (
    while last L == 0 do L = drop(L,-1);
    new Postulation from L
)
postulation Ideal := Postulation => I -> (
    S := (ring I)/I;
    r := regularity I;
    H := (d,F) -> numcols basis(d,F);
    L := -apply(r+1,d-> H(d,S)-3*H(d-1,S)+3*H(d-2,S)-H(d-3,S));
    return postulation L;
)    
{*
postulation QuotientRing := Postulation => S -> "to be done"
postulation HVector
postulation Matrix
*}

degree Postulation := gamma -> (
    --computes the degree given character gamma    
    sum apply(#gamma, k -> k*gamma#k)
)
genus Postulation := gamma -> (
    --compute the genus given character gamma
    sum apply(#gamma, k -> binomial(k-1,2)*gamma#k)
)
ACMPostulations = method(Options => {symbol smooth => false})
ACMPostulations (ZZ,ZZ) := List => opts -> (d,s) -> (
    assert(s >= 1);
    a := getSymbol "a";
    deg := apply(splice{s..(d-1)},i->{1,i});
    R := ZZ/2[a_s..a_(d-1),Degrees=> deg];
    normalize := {s,d-sum apply(s,k-> -k)};
    L := flatten entries basis(normalize,R);
    L = apply(L,p-> postulation (toList(s:-1) | flatten exponents p));
    if opts.smooth then return select(L,p->isConnected p) else
    return L;
)
ACMPostulations ZZ := List => opts -> d -> (
    flatten apply(splice{2..d-1},s->ACMPostulations(d,s,smooth => opts.smooth))    
)
isConnected = method()
isConnected Postulation := Boolean => gamma -> (
    L := sort select(#gamma, i-> gamma#i >0);
    return (#L == last L - first L + 1);
)
hilbertFunction Postulation := gamma -> (
    n -> -sum apply(#gamma,k->binomial(n-k+2,2)*gamma#k)
)
hilbertFunction (ZZ,Postulation) := (d,gamma) -> (
    (hilbertFunction gamma)(d)    
)
degreeMatrix = method()
degreeMatrix Postulation := gamma -> (
    dmax := #gamma;
    H := hilbertFunction gamma;
    B := new MutableList from {1} | splice{dmax:0};
    for i from 1 to dmax do (
    	B#i = H(i) - sum apply(i,j->binomial(3+i-j,3)*B#j);
    );
    B = toList B;
    B = {0} | drop(B,1); 
    L := {};	--degree of generators a_i
    M := {};	--degree of syzygies b_i
    for i from 0 to #B-1 do (
    	if B#i<0 then L = L | splice{(-B#i):i};
	if B#i>0 then M = M | splice{(B#i):i};	
    );
    Ok := false;
    if all(M-drop(L,1),i->i>=0) and all(M-drop(L,-1),i->i>=0) then
    Ok = true;
    if Ok then matrix apply(L,l-> apply(M,m->m-l)) else matrix{{}}        
)
realize Postulation := opts-> gamma -> (
    R := if opts#Ring =!= null then 
        opts#Ring 
      else (
        x := getSymbol "x";
        ZZ/32003[x_0..x_3]
    );
    assert(numgens R == 4);
    
    M := degreeMatrix gamma;
    if M != matrix{{}} then (
    	N := matrix apply(entries M, row -> apply(row, a-> random(a,R)))
    ) else return null;
    minors(numcols N,N)    
)
--VIII.DOCUMENTATIONS

beginDocumentation()
document { 
Key => SpaceCurves,
Headline => "Construction and Database of space curves",
"This package implements methods to collect data and examples of space curve",
PARA{},
SUBSECTION "Abstract surfaces and divisors",  
UL{   TO "AbstractSurface",      
      TO "AbstractDivisor",	  
      TO "abstractSurface",	  
      TO "abstractDivisor",	  	   
      TO "abstractQuadric",
      TO "abstractCubic",
      TO "linesOnCubic",
      TO "abstractHypersurface",
      TO "abstractQuartic",
      TO "CanonicalClass",
      TO "Hyperplane",
      TO "DivisorClass",
      TO "ExtraData",
      TO "IntersectionPairing",
      TO "Chi",
      TO "isIrreducible",
      TO "isSmooth"
},
PARA{},
SUBSECTION "Realizations",  
UL{     TO "RealizedSurface",
        TO "RealizedDivisor",
        TO "realize"
},
PARA{},
SUBSECTION "Hartshorne-Rao module computations",  
UL{   TO "hartshorneRaoModule",
      TO "hilbertBurchComputation",
      TO "minimalCurveInLiaisonClass"
},
PARA{},
SUBSECTION "ACM curves and characters",
UL{    	TO "Postulation",
    	TO "postulation",
	TO "ACMPostulations"
},
PARA{},
SUBSECTION "Collecting examples and information",  
UL{   TO "dgTable",
      TO "smoothDivisors",
      TO "ciCurves",
      TO "generateSmoothCurves",
      TO "implementedSurfaces"
}
}

document{
     Key => AbstractSurface,
     Headline => "type of HashTable",
     "AbstractSurface is a type of Hashtable consisting of the following keys:
     Name, IntersectionPairing, Hyperplane, CanonicalClass, Chi."
}

document {
     Key => AbstractDivisor,
     Headline => "type of HashTable",
     "AbstractDivisor is a type of Hashtable consisting of the following keys:
     AbstractSurface, DivisorClass."
}

document{
     Key => Hyperplane,
     Headline => "key of AbstractSurface",
     "Hyperplane is a Key of AbstractSurface, consists of a list of coordinates
     representing the hyperplane class"
}

document{
     Key => CanonicalClass,
     Headline => "key of AbstractSurface",
     "CanonicalClass is a Key of AbstractSurface, consists of a list of coordinates
     representing the canonical class"
}

document{
     Key => DivisorClass,
     Headline => "key of AbstractDivisor",
     "DivisorClass is a Key of AbstractDivisor, consists of a list of coordinates
     representing the divisor class"
}

document{
     Key => Chi,
     Headline => "key of AbstractSurface",
     "Chi is a Key of AbstractDivisor, consist of an integer specifying
     the sheaf Euler characteristic of the surface."
}

document{
     Key => ExtraData,
     Headline => "key of RealizedSurface",
     "ExtraData is a Key of RealizedSurface consisting of a list a extra data. 
     For example, if RealizedSurface is a cubic sufrace,
     then it contains the ideal of the six points and the matrix of the birational map.
     If RealizedSurface is a quartic with a twisted cubic, 
     then it contains the ideal of the twisted cubic."
}

document{
     Key => IntersectionPairing,
     Headline => "key of AbstractSurface",
     "IntersectionPairing is a Key of the AbstractSurface, 
     consisting of matrix encoding the intersection numbers 
     of the generators of the numerical group of the abstract surface."
}

document{
     Key => RealizedSurface,
     Headline => "type of HashTable",
     "RealizedSurface is a type of HashTable consisting of the keys:
     AbstractSurface, ExtraData, Ideal"
}

document{
     Key => RealizedDivisor,
     Headline => "type of HashTable",
     "RealizedDivisor is a type of HashTable consisting of the keys:
     AbstractDivisor, RealizedSurface, Ideal"
}

document{
     Key => Postulation,
     Headline => "type of List",
     "Postulation is a type of List encoding the postulation character
     of a curve. See Martin-Deschamps and Perrin [1990]."
}

doc ///
  Key
    abstractDivisor
    (abstractDivisor,List,AbstractSurface)
  Headline
    Creates an AbstractDivisor on an AbstractSurface   
  Usage
     C = abstractDivisor(L,X)
  Inputs
    L: List
       of coordinates of a divisor class in Num(X)
    X: Module
       an AbstractSurface
  Outputs
    C: AbstractDivisor
  Description
     Text
       Given a List of coordinates of a divisor class and an AbstractSurface X,
       creates an AbstractDivisor.  
     Example
       abstractDivisor({1,3},abstractQuadric)
       abstractDivisor({3,1,1,1,1,1,1},abstractCubic)
  SeeAlso
///

doc ///
    Key
      abstractHypersurface
      (abstractHypersurface, ZZ)
    Headline
      creates an AbstractSurface corresponding to a hypersurace	
    Usage
      X = abstractHypersurface(d)
    Inputs
      d: ZZ
        a degree
    Outputs
      X: AbstractSurface
    Description
    	Text
	  Creates a hypersurface of degree d of type AbstractSurface.
	Example
	  abstractHypersurface(4)
    SeeAlso
///

doc ///
    Key
      postulation
      (postulation, List)
    Headline
      creates a Postulation from a List	
    Usage
      C = postulation(L)
    Inputs
      L: List
        of values of the postulation character
    Outputs
      C: Postulation 
    Description
    	Text
	Example
	  postulation {-1,-1,2}
    SeeAlso
///

doc ///
  Key
    isSmooth
    (isSmooth, AbstractDivisor)
    (isSmooth, RealizedDivisor)
    (isSmooth, RealizedSurface)
    (isSmooth, Ideal)
  Headline
    checks whether a divisor or a surface is smooth  
  Usage
     B = isSmooth(C)
     B = isSmooth(X)
     B = isSmooth(I)
  Inputs
    C: AbstractDivisor
    C: RealizedDivisor
    X: RealizedSurface
    I: Ideal
  Outputs
    B: Boolean
  Description
     Text
       If the input is an AbstractDivisor, uses numerical criteria to determine 
       whether the divisor class contains an irreducible smooth curve.
       If the input is a RealizedDivisor or a RealizedSurface,
       checks if its ideal is smooth.
     Example
       X = abstractCubic
       C = abstractDivisor(X.Hyperplane,X)
       isSmooth C
       rC = realize C
       isSmooth rC
       isSmooth rC.RealizedSurface
  SeeAlso
///

doc ///
  Key
    isIrreducible
    (isIrreducible,AbstractDivisor)
    (isIrreducible,RealizedDivisor)
  Headline
    checks whether a divisor is irreducible  
  Usage
     B = isIrreducible(C)
  Inputs
    C: AbstractDivisor
    C: RealizedDivisor
  Outputs
    B: Boolean
  Description
     Text
       If the input is an AbstractDivisor, uses numerical criteria to determine 
       whether the divisor class contains an irreducible curve.
       If the input is a RealizedDivisor, checks if its ideal is prime.
     Example
       X = abstractCubic
       C = abstractDivisor(X.Hyperplane,X)
       isIrreducible C
       isIrreducible realize C
  SeeAlso
///

doc ///
    Key
    	realize
	(realize, AbstractSurface)
	(realize, AbstractDivisor, RealizedSurface)
	(realize, AbstractDivisor)
    Headline
    	realizes an AbstractSurface or an AbstractDivisor
    Usage
    	rX = realize(aX)
	rC = realize(aC,rX)
	rC = realize(aC)
    Inputs
    	aX: AbstractSurface
	aC: AbstractDivisor
	rX: RealizedSurface
    Outputs
    	rX: RealizedSurface
	rC: RealizedDivisor
    Description
    	Text
	    Constructs a RealizedSurface given an AbstractSurface. 
	    Constructs a RealizedDivisor given an AbstractDivisor 
	    on a RealizedSurface, if the RealizedSurface is not given,
	    then constructs the RealizedSurface first.
    	Example
	    R = ZZ/101[x_0..x_3]; aC = abstractDivisor({2,3},abstractQuadric);
	    aX = realize(abstractQuadric, Ring=>R)
	    realize(aC,aX);
	    realize(aC);
    SeeAlso    	      
///

doc ///
  Key
    hilbertBurchComputation
    (hilbertBurchComputation, Module, Module)
  Headline
    choose a Hilbert-Burch morphism and compute the corresponding ideal   
  Usage
     I = hilbertBurchComputation(M,G)
  Inputs
    M: Module
       of finite length
    G: Module
       a free module
  Outputs
     I: Ideal
  Description
     Text
       Let $\mathcal F$ be sheafication of the second syzygy module syz_2 M of M, phi be a randomly choosen
       morphism from G -> syz_2 M. The function computes the generators of the homogeneous ideal of coker phi.
       If rank G != rank $\mathcal F$-1 or the morpism does not drop rank in codimension 2, we return null. 
     Example
       S = ZZ/32003[x_0..x_3]
       M=coker matrix{{x_0,x_1,x_2^2,x_3^2}}
       dim M
       reduceHilbert hilbertSeries M
       betti(fM=res M)
       r=rank fM_1-rank fM_0
       degs=sort flatten degrees fM_2
       L=-{3,3}
       G=S^L
       I=hilbertBurchComputation(M,G)
       betti res I
       codim I == 2
       (degree I,genus I) == (4,-1) 
       cI=decompose I     
       tally apply(cI,c->(degree c, genus c))
       I=hilbertBurchComputation(M,S^2)
       I==null
  SeeAlso
///

doc ///
  Key
    hartshorneRaoModule
    (hartshorneRaoModule, Ideal)
  Headline
    compute the Hartshorne-Rao module    
  Usage
     M = hartshorneRaoModule I
  Inputs
    I: Ideal
       of a (locally) Cohen-Macaulay curve
  Outputs
     M: Module
  Description
     Text
       Given I the homogeneous ideal of a (locally) Cohen-Macaulay curve in some projective space P^n, th function computes
       the Hartshorne-Rao module
       $$ M = \oplus H^1(P^r,\mathcal I(n)).$$  
     Example
       S = ZZ/32003[x_0..x_3]
       M=coker random(S^{2:1},S^{5:0})
       dim M
       reduceHilbert hilbertSeries M
       betti(fM=res M)
       r=rank fM_1-rank fM_0
       F=fM_2
       degs=sort flatten degrees F
       L=-degs_{0..r-2}
       G=S^L
       I=hilbertBurchComputation(M,G)
       betti I
       HRao = hartshorneRaoModule(I); betti HRao        
       reduceHilbert hilbertSeries HRao === reduceHilbert hilbertSeries (M**S^{ -2})
  SeeAlso
///

doc ///
  Key
    minimalCurveInLiaisonClass
    ( minimalCurveInLiaisonClass, Module)
    ( minimalCurveInLiaisonClass, Ideal)
  Headline
    probabilistic computation of a minimal curve in the even liaison class   
  Usage
     I = minimalCurveInLiaisonClass M
     I = minimalCurveInLiaisonClass J
  Inputs
    M: Module
       a given Hartshorne-Rao module, or
    J: Ideal
       of a CM curve in P^3
  Outputs
    I: Ideal
        of a locally CM curve in P^3
  Description
     Text
       Given M we compute a (locally) Cohen-Macaulay curve P^3 in the even liaison class represented by M
       (of the curve defined by J).
       The algorithm is only probalistic, i.e. with bad luck we might miss the minimal class due to the eandom choice for the Hilbert-Burch morphism.        
     Example
       S = ZZ/32003[x_0..x_3]
       M=coker matrix{{x_0,x_1,x_2^2,x_3^2}}
       dim M
       reduceHilbert hilbertSeries M
       betti(fM=res M)
       r=rank fM_1-rank fM_0
       degs=sort flatten degrees fM_2
       L=-{3,3}
       G=S^L
       J=hilbertBurchComputation(M,G)
       M=hartshorneRaoModule J
       I=minimalCurveInLiaisonClass M
       degree I, degree J
  SeeAlso
///

doc ///
  Key
    smoothDivisors
    (smoothDivisors, ZZ, AbstractSurface)
    (smoothDivisors, ZZ, RealizedSurface)
  Headline
    creates smooth divisors of a fixed degree on a given surface   
  Usage
     L = smoothDivisors(d,X)
  Inputs
    d: ZZ
       a degree
    X: AbstractSurface
    X: RealizedSurface
  Outputs
    L: List
        of AbstractDivisors or RealizedDivisors of degree d on X 
  Description
     Text
       Produces all smooth divisors of degree d on a given surface X.
       If X is an AbstractSurface, returns a list of AbstractDivisors.
       if X is a RealizedSurface, returns a list of RealizedDivisors.          
     Example
       S = ZZ/32003[x_0..x_3]
       X = abstractCubic
       smoothDivisors(4,X)
       smoothDivisors(4,realize(X, Ring=> S))
  SeeAlso
      ciCurves
///

doc ///
  Key
    ciCurves
    (ciCurves, ZZ)
  Headline
    creates all complete intersection curves of a fixed degree in P^3   
  Usage
     L = ciCurves(d)
  Inputs
    d: ZZ
       a degree
  Outputs
    L: List
        of AbstractDivisors on hypersurfaces
  Description
     Text
       Produces all degree d complete intersection curves in P^3. 
       The list consists of divisors of degree a on hypersurfaces of degree b
       where b <= a and a*b = d.          
     Example
       ciCurves(4)
  SeeAlso
///

doc ///
  Key
    abstractSurface
    (abstractSurface, List)
  Headline
    creates an AbstractSurface from a List of keys   
  Usage
     X = abstractSurface(L)
  Inputs
    L: List
       of Keys of an AbstractSurface in the following order:
       Name, IntersectionPairing, Hyperplane, CanonicalClass, Chi
  Outputs
    X: AbstractSurface
  Description
     Text        
     Example
       abstractSurface {"My surface",
	   matrix{{0,1},{1,0}},
	   {1,1},
	   {-2,-2},
	   1}
  SeeAlso
///

doc ///
    Key
      ACMPostulations
      (ACMPostulations, ZZ)
      (ACMPostulations, ZZ, ZZ)
    Headline
      creates all Postulations of non-degnerate ACM curves of degree d	
    Usage
      L = ACMPostulations(d)
    Inputs
      d: ZZ
        a degree
    Outputs
      L: List
        of Postulations
    Description
    	Text
	Example
	  ACMPostulations 3
    SeeAlso
///

doc ///
  Key
    dgTable
    (dgTable, List)
  Headline
    records occurancecs of (degree,genus) pair from a list of divisors   
  Usage
    M = dgTable(L)
  Inputs
    L: List
       of AbstractDivisors or RealizedDivisors
  Outputs
    M: Matrix
        of occurencies of a (degree,genus) pair 
  Description
     Text
       Produces from a list of divisors an occurence matrix, 
       the rows are indexed by genus and the columns by degree.          
     Example
       R = ZZ/101[x_0..x_3];
       L = flatten apply({2,3,4}, d->smoothDivisors(d,abstractQuadric));
       dgTable L
       dgTable (L / realize)   
  SeeAlso
///

doc ///
  Key
    generateSmoothCurves
    (generateSmoothCurves, List)
  Headline
    generates all smooth curves of the listed degrees on all implemented surfaces   
  Usage
    L = generateSmoothCurves(D)
  Inputs
    D: List
       of degrees
  Outputs
    L: List
        of AbstractDivisor or RealizedDivisor depending on optional arguments 
  Description
     Text          
     Example
       generateSmoothCurves({2,3})   
  SeeAlso
///

{*
doc ///
  Key
    implementedSurfaces
    (implementedSurfaces)
  Headline
    lists all the implemented AbstractSurfaces   
  Usage
    L = implementedSurfaces()
  Outputs
    L: List
        of AbstractSurfaces
  Description
    Example
      implementedSurfaces()
  SeeAlso 
///

doc ///
  Key
    abstractQuadric
    (abstractQuadric)
  Headline
    creates an abstract quadric surface as an AbstractSurface   
  Usage
    X = abstractQuadric
  Outputs
    X: AbstractSurface
  Description
    Example
      X = abstractQuadric
      peek X 
  SeeAlso 
///

doc ///
  Key
    abstractCubic
    (abstractCubic)
  Headline
    creates an abstract cubic surface as an AbstractSurface   
  Usage
    X = abstractCubic
  Outputs
    X: AbstractSurface
  Description
    Example
      X = abstractCubic
      peek X
  SeeAlso 
///

doc ///
  Key
    linesOnCubic
    (linesOnCubic)
  Headline
    lists the 27 lines on the abstractCubic   
  Usage
    L = linesOnCubic()
  Outputs
    L: List
      of 27 lines 
  Description
    Example
      linesOnCubic()
  SeeAlso
    abstractCubic
///
*}

--TEST SECTION

TEST ///
  X = abstractQuadric
  R = QQ[a,b]
  C = abstractDivisor({a,b},X)
  degree C
  genus C
  chi C
///

TEST ///
  X = abstractCubic
  R = QQ[a,b_1..b_6]
  C = abstractDivisor(gens R,X)
  degree C
  genus C
  chi C
///

TEST ///
  S = ZZ/32003[a..d]
  X = realize(abstractCubic, Ring => S)
  C = abstractDivisor({3,1,1,1,0,0,0},abstractCubic)
  isIrreducible C
  assert(degree C == 6)
  assert(genus C == 1)
  I = realize(C,X)
  isSmooth I
  betti res ideal I
  assert(degree I == degree C)
  assert(genus I == genus C)
///

TEST ///
    S = ZZ/101[x_0..x_3];
    X = realize(abstractHypersurface(3), Ring => S)
    C = abstractDivisor({4},X.AbstractSurface)
    degree C
    genus C
    rC = realize(C,X)
    assert(degree rC == degree C);
    assert(genus rC == genus C);
///


TEST ///
  S = ZZ/32003[x_0..x_3]
  M=coker random(S^{2:1},S^{5:0})
  dim M
  reduceHilbert hilbertSeries M
  betti(fM=res M)
  r=rank fM_1-rank fM_0
  F= fM_2
  degs=sort flatten degrees F
  L=-degs_{0..r-2}
  G=S^L
  I=hilbertBurchComputation(M,G)
  betti I
  assert( codim I == 2)
  assert((degree I,genus I) == (7,2))
--I=hilbertBurchComputation(M,S^3)
  I=hilbertBurchComputation(M,S^2)
  I==null
///

TEST ///
  S = ZZ/32003[x_0..x_3]
  M=coker (koszul(2,vars S)|random(S^{4:-1},S^{4:-3}));
  betti M
  dim M == 0
  time I=minimalCurveInLiaisonClass M; -- used 0.58667 seconds
  assert( (degree I, genus I) == (43, 168) )
{*
  omega=Ext^2(S^1/I,S^{-4});
  fomega=res omega
  betti fomega
  HRao= coker(Hom(fomega.dd_2_{0..(rank fomega_2-2)},S^{-4}))
  reduceHilbert hilbertSeries HRao
  reduceHilbert hilbertSeries M
*}
///	


TEST ///
  S = ZZ/32003[x_0..x_3]
  M=coker random(S^{2:1},S^{5:0})
  dim M
  reduceHilbert hilbertSeries M
  betti(fM=res M)
  r=rank fM_1-rank fM_0
  F= fM_2
  degs=sort flatten degrees F
  L=-degs_{0..r-2}
  G=S^L
  I=hilbertBurchComputation(M,G)
  betti I
  HRao = hartshorneRaoModule(I)        
  assert(reduceHilbert hilbertSeries HRao === reduceHilbert hilbertSeries (M**S^{ -2}))
///


end--
restart
uninstallPackage "SpaceCurves"
installPackage "SpaceCurves"
viewHelp "SpaceCurves"



--Generate all curves of degree d
restart
needsPackage "SpaceCurves"
check "SpaceCurves"
dmax = 10
time Lad = generateSmoothCurves splice{1..dmax};  -- used 10.109 seconds
time ACM = flatten apply(splice{1..dmax},d-> ACMPostulations d);	-- used 0.570933 seconds  
time sACM = flatten apply(splice{1..dmax},d
    -> ACMPostulations(d,smooth=>true));  -- used 0.729161 seconds
dgTable Lad
dgTable ACM
dgTable sACM