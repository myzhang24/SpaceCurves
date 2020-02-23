newPackage(
        "SpaceCurves",
        Version => "2.0", 
        Date => "June 2019",
        Authors => {{Name => "Mengyuan Zhang", 
                  Email => "myzhang@berkeley.edu", 
                  HomePage => "https://math.berkeley.edu/~myzhang/"}
	      },
        Headline => "Curves in projective spaces",
        DebuggingMode => true
        )

export {
    	"randomPointsInP2",
    	"PolarizedSurface",
	"SurfaceData",	
	"IntersectionPairing",	      
	"CanonicalClass",
	"HyperplaneClass",
	"LinearSystem",
	"Chi",
	"blowupP2",
	"scroll",
	"Divisor",
	"Coordinate",
	"Surface",
	"divisor",
	"divisors",
	"curve",
	"dgTable"	
}


randomPointsInP2 = method()

randomPointsInP2(ZZ,Ring) := (n,R) -> (
    assert(isPolynomialRing R);
    assert(isField coefficientRing R);
    assert(numgens R == 3);
    apply(entries random(R^n,R^3), r -> minors(2, matrix{gens R, r}))    
)

randomPointsInP2 ZZ := n -> (
    x := getSymbol "x";
    randomPointsInP2(n,(ZZ/101)(monoid[x_0..x_2]))    
)

PolarizedSurface = new Type of HashTable
net PolarizedSurface := X -> (
    if instance(X.SurfaceData#0,Ideal) then return
    concatenate {
    	"P^2 blown-up at ",
	toString(#(X.SurfaceData)),
	" points\n   	  polarized by ",
	toString X.HyperplaneClass	
    };
    if instance(X.SurfaceData#0,ZZ) then concatenate {
    	"A scroll of type ",
	toString sort X.SurfaceData	
    }  
)

blowupP2 = method()

blowupP2(List,List) := PolarizedSurface => (L,H) -> (
    assert(all(L, I -> numgens ring I == 3));
    assert(all(L, I -> codim I == 2));
    assert(#H == #L+1);
    assert(H#0 > 0 and all(H, i -> i >= 0));
    
    new PolarizedSurface from {
    	symbol IntersectionPairing => diagonalMatrix splice{1,#L:-1},
	symbol CanonicalClass => -splice{3,#L:1},
	symbol HyperplaneClass => H,
	symbol SurfaceData => L,
	symbol LinearSystem => super basis(H#0,intersect apply(#L, 
	    i -> L#i^(H#(i+1)))),
	symbol Chi => 1	
    }
) 

blowupP2 List := PolarizedSurface => L -> (
    --default polarization is anti-canonical
    H := splice{3,#L:1};
    blowupP2(L,H)    
)

blowupP2 (ZZ,List) := PolarizedSurface => (n,H) -> (
    assert(n == #H-1);
    L := randomPointsInP2 n;
    blowupP2(L,H)    
)

blowupP2 ZZ := PolarizedSurface => n -> blowupP2 randomPointsInP2 n

scroll = method()

scroll (List,Ring) := (L,kk) -> (
    assert(#L == 2);
    assert(isField kk);
    
    (a,b) := (min L, max L);
    X := getSymbol "X";
    R := kk(monoid[X_0..X_3,Degrees=>{{0,1},{0,1},{1,-a},{1,-b}}]);
    B := basis({1,0},R);    --basis scrollar sections
   
    new PolarizedSurface from {
	symbol SurfaceData => {a,b},
	symbol LinearSystem => B,
	symbol HyperplaneClass => {1,b},
	symbol CanonicalClass => {-2,-(b-a+2)},
	symbol IntersectionPairing => matrix{{-(b-a),1},{1,0}},    
	symbol Chi => 1
    }        
)

scroll List := L -> scroll(L,ZZ/101)

scroll(ZZ,ZZ) := (a,b) -> scroll {a,b}

scroll(ZZ,ZZ,Ring) := (a,b,kk) -> scroll({a,b},kk)

ideal PolarizedSurface := X -> (
    B := X.LinearSystem;
    R := ring source B;
    kk := coefficientRing R;
    x := getSymbol "x";
    S := kk(monoid[x_0..x_(numcols B-1)]);
    kernel map(R,S,B)
)

Divisor = new Type of HashTable

net Divisor := X -> net X.Coordinate

divisor = method()

divisor(List, PolarizedSurface) := (C, X) -> (
    assert(numcols X.IntersectionPairing == #C);
    new Divisor from {
        symbol Coordinate => C,
        symbol Surface => X
        }
    )

QQ * Divisor := Divisor => (k,D) -> (
    divisor(k * D.Coordinate, D.Surface)
)

ZZ * Divisor := Divisor => (n,D) -> (
    divisor(n * D.Coordinate, D.Surface)
)

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
    (matrix{C.Coordinate} * X.IntersectionPairing * 
	transpose matrix{D.Coordinate})_(0,0)
)

degree Divisor := C -> (
    H := divisor(C.Surface.HyperplaneClass,C.Surface);
    C*H
)

genus Divisor := C -> (
    --adjunction    
    K := divisor(C.Surface.CanonicalClass,C.Surface);
    1/2*(C+K)*C+1
)

chi Divisor := C -> (
    --Riemann-Roch
    K := divisor(C.Surface.CanonicalClass,C.Surface);
    1/2*C*(C-K)+C.Surface.Chi
)

random (ZZ,Ideal) := opts -> (d,I) -> (
    B := super basis(d,I);
    R := ring I;
    (B*random(R^(numcols B),R^1))_(0,0)   
)

curve = method()

curve Divisor := Ideal => D -> (
    X := D.Surface;
    L := D.Coordinate;
    B := X.LinearSystem;
    S := ring B;
    kk := coefficientRing S;
    f := 0_S;
    
    if instance(X.SurfaceData#0,Ideal) then (
    	I := intersect apply(#L-1, i-> (X.SurfaceData)#i^(L#(i+1)));
	f = random(L#0,I);
    );
    if instance(X.SurfaceData#0,ZZ) then (
	(a,b) := toSequence X.SurfaceData;
    	f = random({L#0,L#1-b*L#0},S);
    );
    x := getSymbol "x";
    kernel map(S/ideal f,kk(monoid[x_0..x_(numcols B-1)]),B)
)

curve(ZZ,Divisor) := Ideal => (n,D) -> (
    X := D.Surface;
    L := D.Coordinate;
    B := X.LinearSystem;
    S := ring B;
    kk := coefficientRing S;
    f := 0_S;
    
    if instance(X.SurfaceData#0,Ideal) then (
    	I := intersect apply(#L-1, i-> (X.SurfaceData)#i^(L#(i+1)));
	f = random(L#0,I);
    );
    if instance(X.SurfaceData#0,ZZ) then (
	(a,b) := toSequence X.SurfaceData;
    	f = random({L#0,L#1-b*L#0},S);	
    );
    x := getSymbol "x";
    n = min(numcols B,n+1)-1;
    B = B*random(S^(numcols B),S^(n+1));
    kernel map(S/ideal f,kk(monoid[x_0..x_n]),B)  
)

divisors = method()

divisors(ZZ,PolarizedSurface) := List => (d,X) -> (
    --generates effective divisors of degree d on X
    if instance(X.SurfaceData#0,Ideal) then (
    	n := #X.HyperplaneClass-1;
    	return flatten for a from ceiling(d/3) to d list (
	   degs := apply(select(partitions(3*a-d, ceiling(a/3)), p-> #p <= n), 
	       q -> {a} | toList q | splice{(n-#q):0}); 
	   degs = select(degs, L -> L#0 >= L#1 + L#2 + L#3);
	   apply(degs, L-> divisor(L,X)))
    );     
    if instance(X.SurfaceData#0,ZZ) then (
        (p,q) := toSequence X.SurfaceData;
    	n = p-1;
    	e := q-p;
    	t := getSymbol "t";
    	R := (ZZ/2)(monoid[t_0,t_1,Degrees => {n+1,1}]);
    	select(apply(flatten entries basis(d,R), 
		m -> flatten exponents m), P -> 
	    first P != 0 and last P != 0 and last P >= e*first P) / 
	(cord -> divisor(cord,X))
		
    )
)

divisors(ZZ,ZZ) := (d,g) -> (
    X := scroll(1,1);
    Y := blowupP2 6;
    Z := blowupP2(9,{4,2,1,1,1,1,1,1,1,1});
    L := divisors(d, X) |
    	divisors(d, Y) |
	divisors(d, Z);
    select(L, D -> genus D == g)
)

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


beginDocumentation()
document { 
    Key => SpaceCurves,
    Headline => "Curves in Projective Spaces",
    PARA{
    	EM "SpaceCurves", " is a package that generates curves in projective spaces." 
	},
    SUBSECTION "PolarizedSurface",
    PARA { 
    	"The main idea is to generate curves C on surfaces X in P^n."
    },
    PARA { 
	"The surface X can be thought of as the image under a rational map
	S ---> P^n of an abstract surface S. The data of the an abstract surface S along with a linear
	system, also called a polarization, is encoded in ", TO PolarizedSurface, " which is a type of ", TO HashTable,
	". The image of a suitable effective divisor D on S then gives us a curve C on X in P^n."
    },
    PARA {
    	"The package provides two main ways to produce ", TO PolarizedSurface, "s, namely ",
	TO blowupP2, " and ", TO scroll, ", which we explain below in detail."	
    },
    SUBSECTION "Blowing up P^2 at finitely many points", 
    PARA {
    	"Let Z = z_1 .. z_m be finitely many points in P^2.
	The linear system of plane curves of degree d 
	that has multiplicity at least n_i at z_i corresponds to a rational map
	P^2 ---> P^n."
	},
    PARA {
	"Note that this map factors through the blowup P^2 ---> Bl_Z P^2 ---> P^n,
        thus this data also corresponds to a linear system on Bl_Z P^2.
	The numerical group of Bl_Z P^2 has a basis pi^*O(1), -E_1, ..., -E_m, 
	where pi^*O(1) is the pullback of the hyperplane class of P^2 via the blowup map,
	and E_i is the exceptional divisor of z_i."
	},
    PARA {	
	"The method ", TO blowupP2, " produces such a ", TO PolarizedSurface, 
	". The following example shows how to blowup P^2 at one point p and polarize
	by the linear system of conics through p."	
    },
    EXAMPLE {
    	"R = ZZ/101[x_0..x_2];",
	"L = {ideal(x_0,x_1)}",
	"X = blowupP2(L,{2,1})",
	"peek X",
	"ideal X"	
    },
    SUBSECTION "Rational Surface Scrolls",
    PARA {
	"Readers may realize that the above surface is also the 
	projective bundle P(O(1)+O(2)) over P^1 mapped by O(1) into P^1+2+1, 
	the image is a scroll of type (1,2).
	These scrolls are easy to produce and provide interesting ambient surfaces
	for the curves to lie on."
    },
    PARA {
	"We use toric geometry to find a basis of the linear system in the toric ring of
	the Hirzebruch surface H_e corresponding to the line bundle C_e+bf. 
	Here e = |b-a| and C_e is the class of -e curve and f is the class of a fiber.
	The method ", TO scroll, " achieves this."
    },
    EXAMPLE {
    	"Y = scroll(1,2)",
	"peek Y",
	"ideal Y"  
    },
    SUBSECTION "Divisors on PolarizedSurface",
    PARA {
	"The method ", TO divisor,
	" creates a ", TO Divisor, " on a ", TO PolarizedSurface, 
	". Note that the ", TO Coordinate, "s of the ", TO Divisor, 
	" are written in the same basis of that the ", TO IntersectionPairing, " matrix is using."
    },
    PARA {
	"In the example below, although the surface X and Y are essentially the same,
	and the divisors C and D have the same coordinates, they are not the same 
	divisor. On X the basis is taken to be { pi^*O(1), -E_1 }
	 and on Y the basis is taken to be { C_1, f }." 
    },
    EXAMPLE {
    	"C = divisor({2,0},X)",
	"chi C",
	"D = divisor({2,0},Y)",
	"chi D"
    },
    SUBSECTION "Generating a random curve in a Divisor class",
    PARA {
    	"The method ", TO (curve,Divisor), " takes a random effective divisor 
	D in the given class on S, and computes the image of D under the rational map S ---> P^n 
	given by the ", TO PolarizedSurface, "."	
    },
    EXAMPLE {
    	"curve D"	
    },
    PARA {
    	"In case one wants to map D by a general m dimensional
	sub-linear system of the original system instead, 
	i.e. consider the image of D under a general projection S ---> P^m, ",
	TO (curve,ZZ,Divisor), " computes the ideal of the image." 	
    },
    EXAMPLE {
	"curve(3,D)"
    },
    SUBSECTION "Generating Divisors of given degree and genus",
    PARA {
    	"The method ", TO (divisors, ZZ, PolarizedSurface), 
	" produces a ", TO List, " of all ", TO Divisor,
	"s of a given degree
	on a given ", TO PolarizedSurface, "."	
    },
    PARA {
	"The method ", TO (divisors, ZZ, ZZ), 
	" produces a non-exhaustive ", TO List, " of ", 
	TO Divisor, "s of a given degree and genus on the smooth
	quadric and cubic surface as well as the ruled singular
	quartic surface in P^3. According to Gruson-Peskine, 
	whenever such (degree, genus) is achieved by a smooth curve in P^3,
	such a curve can be found on one of the above surfaces."
    },
    EXAMPLE {
    	"divisors(8,5)"	
    },
    PARA {
	"Once we have a ", TO List, " of ", TO Divisor,
	"s or ", TO Ideal, "s, we may want to visualize the 
	occurence of the (degree, genus) pair. This can be done via ",
	TO (dgTable, List), "."
	},
    EXAMPLE {
	"M = flatten apply(splice{3..10}, 
	d -> divisors(d, blowupP2 6))",
	"dgTable M"	
    },
    PARA {
    	"Finally a warning that the (degree, genus) of the ",
	TO Divisor, "s might be different from those of the ",
	TO Ideal, "s of the image curve computed by ",
	 TO (curve, Divisor),
	". This happens when the polarization restricted to the random
	effective sample is not very ample."	
    }
}


document{
     Key => {
	 PolarizedSurface,
	 SurfaceData,
	 IntersectionPairing,
	 HyperplaneClass,
	 CanonicalClass,
	 LinearSystem,
	 Chi,
	 (net, PolarizedSurface)
	 },
     Headline => "A surface with a linear system",
     PARA {
	 TO PolarizedSurface, " is a type of ", TO HashTable, 
     " storing the information of a surface with a linear system."
     },
     PARA {
     	 "The key ", TO SurfaceData, " stores a ", TO List, 
	 " encoding defining characteristics of the ",
	 TO PolarizedSurface, 
	 ". If the surface is the blowup of P^2 at finitely
	 many points, then this list stores the list of ideals of these
	 points. 
	 If the surface is the scroll, then the list stores
	 the type {a,b}."	 
     },
     PARA { 
     	 "The key ", TO IntersectionPairing, " stores a ", TO Matrix, 
     " encoding the intersection matrix of the numerical group of 
     the surface. A basis of the numerical group is implicitly chosen."
     },
     PARA {
     	 "The key ", TO HyperplaneClass, " contains a ",
	 TO List, " encoding the coordinates of the polarizing bundle 
	 with respect to the same basis as in the ", TO IntersectionPairing, "."
	 
     }, 
     PARA { 
 	 "The key ", TO CanonicalClass, " contains a ", TO List, 
     " encoding the coordinates of the canonical bundle 
     with respect to the same basis as in the ", TO IntersectionPairing, "."
     },
     PARA { 
      	 "The key ", TO LinearSystem, " stores a row ", TO Matrix,
     " whose entries form a vector space basis of the linear system of the polarizing
     bundle."
     },
     PARA {
    	"The key ", TO Chi, " stores the Euler characteristic of the sheaf O_X."	 
     },
     EXAMPLE {
    	"X = blowupP2(1,{2,1})",
	"peek X"	 
     },
     PARA {
    	"In the above example, the surface in question is the blowup
	of P^2 at a point p. A basis of its numberical group is given by
	pi^*O(1) and E, where pi^*O(1) is the pullback of the hyperplane class of P2 
	and E is the exceptional divisor of the blowup. 
	
	The second input is {2,1}, which is the coordinates of the polarizing bundle.
	Thus we are mapping the blowup of P^2 at p by the linear system of
	conics passing through p."
     },
     SeeAlso => {(ideal,PolarizedSurface)}
}
document{
    Key => {blowupP2,
	(blowupP2,List),
	(blowupP2,List,List),
	(blowupP2,ZZ,List),
	(blowupP2,ZZ)},
    Headline => "Blowup P^2 at given points and polarize by a given line bundle",
    {"This method produces a ", TO PolarizedSurface, " corresponding
      to the blowup of P^2 at a list of points, and polarized by a given divisor."
      },
    PARA {
	"A basis of the numerical group is given by pi^*O(1), -E_1, ..., -E_n,
      where pi^*O(1) is the pullback of O(1) on P^2 and E_i are the exceptional
      divisors of the blowup."
    },
    SYNOPSIS (   
    	Usage => "X = blowupP2(L,H)",
    	Inputs => { "L" => List => " of Ideals of points in P^2",
	    "H" => List => " giving coordinates of the polarizing bundle"},
	Outputs => {"X" => PolarizedSurface},
    ),
    {
    "If the polarizing line bundle is omitted from the second input,
     then the default polarizing bundle is the anti-canonical bundle."	
    },
    SYNOPSIS (   
    	Usage => "X = blowupP2(L)",
    	Inputs => { "L" => List => " of Ideals of points in P^2"},
	Outputs => {"X" => PolarizedSurface},
    ),
    EXAMPLE {
       	    "L = randomPointsInP2 3",
	    "X = blowupP2(L,{4,2,1,0})",
	    "Y = blowupP2 L"
    	    },
    PARA {
    "If the first input is an integer n,
    then the method blows up P^2 at n random points."	
    },
    SYNOPSIS (   
    	Usage => "X = blowupP2(n,H)",
    	Inputs => { 
	    "n" => ZZ => " number of random points to blowup",
	    "H" => List => " coordinate of the polarizing bundle"},
	Outputs => {"X" => PolarizedSurface},
    ),
    SYNOPSIS (   
    	Usage => "X = blowupP2 n",
    	Inputs => { 
	    "n" => ZZ => " number of random points to blowup"
	    },
	Outputs => {"X" => PolarizedSurface},
    ),
    EXAMPLE {
       	    "X = blowupP2(1,{2,1})",
	    "Y = blowupP2 6"
    	    },
    SeeAlso => {"PolarizedSurface","scroll"}   
}
document {
    Key => {randomPointsInP2,
	(randomPointsInP2,ZZ,Ring),
	(randomPointsInP2,ZZ)},
    Headline => "Creates a list of ideals of random points in P^2",
    {
	"This method produces a list of ideals of random points
	 (over the base field) in P^2."
    },
    SYNOPSIS (
    	Usage => "L = randomPointsInP2(n,R)",
	Inputs => {"n" => ZZ => " number of random points",
	    "R" => Ring => " polynomial ring of P^2"},
	Outputs => {"L" => List => " of ideals of points"},
	"If the Ring input is omitted, the default ring is 
	ZZ/101[x_0..x_2].",
	EXAMPLE {
	    "randomPointsInP2 3"    
	}	
    )	    
}
document {
    Key => {scroll,
	(scroll,List,Ring),
	(scroll,List),
	(scroll,ZZ,ZZ,Ring),
	(scroll,ZZ,ZZ)},
    Headline => "Produces a surface scroll P(O(a)+O(b)) in P^a+b+1",
    {
	"This method produces a ", TO PolarizedSurface, " encoding the
	scroll of type (a,b). More precisely, the underlying surface is
	the Hirzebruch surface H_e where e = |b-a|. The numerical group 
	of H_e has a basis {C_e,f}, where C_e is the class of the -e curve and f
	is the class of a fiber. The polarization is given by the line bundle
	{1,b} in this basis.
	Under a change of basis, this coincides with the projective 
	bundle P(O(a)+O(b)) over P^1 polarized by O(1), whose image in P^a+b+1 
	is called a scroll of type (a,b)."
    },
    SYNOPSIS (
	Usage => "X = scroll(L,kk)",
	Inputs => {
	    "L" => List => "specifying the type {a,b}",
	    "kk" => Ring => "specifying the base field"},
	Outputs => {
	    "X" => PolarizedSurface => "encoding the Hirzebruch surface
	    H_(b-a) polarized by {1,b}"
	    } 
    ),
    SYNOPSIS (
    	Usage => "X = scroll L"	
    ),
    PARA {
	"If the Ring input is omitted, then the default base field
	is ZZ/101."
    },
    EXAMPLE {
    	"X = scroll({3,4},ZZ/7)",
	"X = scroll {3,4}"	
    },
    SYNOPSIS (
	Usage => "X = scroll(a,b,kk)",
	Inputs => {
	    "a" => ZZ,
	    "b" => ZZ, 
	    "kk" => Ring => "specifying the base field"},
	Outputs => {
	    "X" => PolarizedSurface => 
	    "encoding the Hirzebruch surface
	    H_(b-a) polarized by {1,b}"
	    } 
    ),
    SYNOPSIS (
    	Usage => "X = scroll(a,b)"	
    ),   
    EXAMPLE {
    	"scroll(3,4,ZZ/7)",
	"scroll(3,4)"	
    }
}
document {
    Key => {(ideal,PolarizedSurface)},
    Headline => "Computes the ideal of the image surface",
    {
	"Given a ", TO PolarizedSurface, " X, the ", 
	TO LinearSystem, " specifies a map from the polynomial ring
	kk[x_0..x_n] to R, the section ring of the hyperplane bundle H.
	The kernel of this map kk[x_0..x_n] -> R is the ideal of the image of 
	the corresponding rational map X --> P^n."
    },
    SYNOPSIS (
    	Usage => "I = ideal X",
	Inputs => {
	    "X" => PolarizedSurface
	    },
	Outputs => {
	    "I" => Ideal },
	EXAMPLE {
	    "X = scroll(1,2)",
	    "I = ideal X"    
	}		
    ),
    SeeAlso => {"PolarizedSurface"}        
}
document {
    Key => {
	Divisor, 
	Coordinate, 
	Surface,
	(net, Divisor)
	},
    Headline => "Divisors on a PolarizedSurface",
    {
    	TO Divisor, " is a type of ", TO HashTable, 
	" encoding the information of a divisor on a ",
	TO PolarizedSurface, "."
    },
    PARA {
	"The key ", TO Coordinate, " stores a ",
	TO List, " encoding the coordinates of the divisor
	with respect to the same basis as in the ", 
	TO IntersectionPairing, "."
    },
    PARA {
	"The key ", TO Surface, " stores the ",
	TO PolarizedSurface, " the divisor lies on."
    },
    SeeAlso => {
	divisor
	}
}
document {
    Key => {(degree, Divisor)},
    Headline => "Degree of a Divisor",
    PARA {
        TO (degree,Divisor), " computes the degree of an input
	divisor D with respect to the polarization H.
	When D is effective, this gives the degree of the image curve
	under the rational map given by H."
    }
}
document {
    Key => {(genus, Divisor)},
    Headline => "Genus of a Divisor",
    PARA {
    	TO (genus,Divisor), " computes the (virtual) arithmetic
	genus of an input divisor D using adjunction formula.
	When D is effective, this gives the arithmetic genus of
	D on the surface. However if the rational
	map defined by H is not very amply on D, 
	then the arithmetic genus of the image curve may differ."
    }
}
document {
    Key => {(chi, Divisor)},
    Headline => "Euler characteristics of a Divisor",
    PARA {
	TO (chi,Divisor), " computes the Euler characteristic
	H^0(D)-H^1(D)+H^2(D) of an input divisor D using Riemann-Roch
	under the assumption that the surface D lies on is smooth."		    
    } 
}
document {
    Key => {
	(symbol +, Divisor, Divisor),
	(symbol *, Divisor, Divisor),
	(symbol *, ZZ, Divisor),
	(symbol *, QQ, Divisor),
	(symbol -, Divisor, Divisor)
	},
    Headline => "Operations on divisors",
    {
	"One can multiply a ", TO Divisor, " by an integer
	or a rational number, as well as adding and subtracting
	two ", TO Divisor, "s on the same ", TO PolarizedSurface, "."
    },
    PARA {
    	TO (symbol *, Divisor, Divisor), " computes the intersection
	product of two ", TO Divisor, "s on the same ",
	TO PolarizedSurface, " using the ",
	TO IntersectionPairing, "."	
    }     
}
document {
    Key => {
	curve,
	(curve, Divisor),
	(curve, ZZ, Divisor)
	},
    Headline => "Computes the ideal of a random effective divisor",
    PARA {
    	"The method ", TO (curve, Divisor), " takes a random
	effective divisor in the specified class, and computes
	the ideal of the image under the rational map given by
	the ", TO LinearSystem, " of the ", 
	TO PolarizedSurface, " it lies on."	
    },
    SYNOPSIS (
    	Usage => "I = curve D",
	Inputs => {
	    "D" => Divisor
	    },
	Outputs => {
	    "I" => Ideal => " of the image curve"
	    }	
    ),
    PARA {
	"The method ", TO (curve, ZZ, Divisor), " takes a random
	effective divisor in the specified class, and computes
	the ideal of the general projection into P^n of the original
	image under the rational map given by
	the ", TO LinearSystem, " of the ", 
	TO PolarizedSurface, " it lies on."	
    },
    SYNOPSIS (
    	Usage => "I = curve(n,D)",
	Inputs => {
	    "n" => ZZ => " dimension of the general linear subsystem",
	    "D" => Divisor
	    },
	Outputs => {
	    "I" => Ideal => 
	    " of the image curve by a general n dimensional linear subsystem"
	    }	
    ),
    EXAMPLE {
    	"X = scroll(1,2)",
	"D = divisor({2,3},X)",
	"I = curve D",
	"J = curve(3,D)"	
    }
}
document {
    Key => {
	divisor,
	(divisor, List, PolarizedSurface)
	},
    Headline => "Creates a Divisor on a PolarizedSurface",
    { 
	"Creating a ", TO Divisor, " on a ", TO PolarizedSurface, "."
    },
    SYNOPSIS (
    	Usage => "D = divisor(L,X)",
	Inputs => {
	    "L" => List => " of coordinates of the divisor",
	    "X" => PolarizedSurface
	    },
	Outputs => {
	    "D" => Divisor
	    },
	EXAMPLE {
	    "X = scroll(1,2)",
	    "D = divisor({2,3},X)"    
	}	
    ),
    SeeAlso => {
     Divisor
    }
}
document {
    Key => {
	divisors,
	(divisors, ZZ, PolarizedSurface),
	(divisors, ZZ, ZZ)
	},
    Headline => "Produces a list of Divisors",
    PARA {
	"The method ", TO (divisors, ZZ, PolarizedSurface), 
	" produces a ", TO List, " of all ", TO Divisor,
	"s of a given degree
	on a given ", TO PolarizedSurface, "."
    },
    SYNOPSIS (
    	Usage => "L = divisors(d,X)",
	Inputs => {
	    "d" => ZZ => " degree of the divisors",
	    "X" => PolarizedSurface
	    },
	Outputs => {
	    "L" => List => " of all divisors of degree d on X"
	    },
	EXAMPLE {
	    "X = scroll(1,2)",
	    "divisors(6,X)"   
	}	
    ),
    PARA {
    	"The method ", TO (divisors, ZZ, ZZ), 
	" produces a non-exhaustive ", TO List, " of ", 
	TO Divisor, "s of a given degree and genus across different ",
	, TO PolarizedSurface, "s."	
    },
    SYNOPSIS (
        Usage => "L = divisors(d,g)",
	Inputs => {
	    "d" => ZZ => " degree of the Divisors",
	    "g" => ZZ => " genus of the Divisors"
	    },
	Outputs => {
	    "L" => List => " of Divisors"
	    },
	EXAMPLE {
	    "divisors(5,8)"   
	}
    ),
    SeeAlso => {
    	Divisor
	}
}
document {
    Key => {dgTable,(dgTable,List)},
    Headline => "prints the table of (degree,genus) pairs",
    {
    TO "dgTable", " prints the table of (degree,genus) pairs, where the horizontal
    axis is the degree and the vertical is the genus. The input can be a ", TT "List",
    " of ", TO "Divisor", "s as well as ", TO Ideal, "s."
    } 
}

--Tests
TEST
X = scroll(1,2);
D = divisor({3,4},X);
I = curve D;
assert(degree D == 7);

X = blowupP2 6;
D = divisor({4,2,1,1,0,0,0},X);
I = curve D;
assert(degree D == 8);


end


-------------------------------------------------------------------------------------
restart
uninstallPackage "SpaceCurves"
installPackage "SpaceCurves"
viewHelp "SpaceCurves"

