linesOnCubic = (    --27 lines on cubic
    Es := entries transpose (matrix{splice{6:0}} || -id_(ZZ^6));
    Ls := flatten apply(6, i-> apply(splice{i+1..5}, j-> 
	    (apply(7,d -> if (d == 0 or d== i+1 or d == j+1) then 1 else 0))));
    Gs := apply(6, d -> {2,1,1,1,1,1,1} + (Es#d));
    Es | Ls |Gs
)
List ** List := (C,D) -> (    --intersection number
    assert (#C == #D);
    2*(first C)*(first D)- sum apply(#C,i-> (C#i)*(D#i)) 
)
degree List := L -> (
    3*(L#0)-L#1-L#2-L#3-L#4-L#5-L#6  
)
genus List := L ->(
    1/2 * (L#0*(L#0-3)-L#1*(L#1-1)-L#2*(L#2-1)-L#3*(L#3-1)-L#4*(L#4-1)-L#5*(L#5-1)-L#6*(L#6-1)+2)    
)
idealCurve = C -> (
    x := getSymbol "x";
    R := (ZZ/32003)(monoid[x_0..x_3]);
    X := cubicSurface(R);
    ideal curve divisor(C,X)    
)
Delta = L -> (
    L- ({0} | drop(L,-1))    
)

--Zariski Decomposition
fixed = D -> (	  --(virtual) fixed part of a divisor
    lin :=  for L in linesOnCubic list (
	if L ** D >= 0 then continue else -(L ** D)*L);
    if lin == {} then return {0,0,0,0,0,0,0} else return sum lin;  
)
moving = D -> (	   --(virtual) moving part of a divisor
    D - fixed D
)

--Cohomology
h0 = D -> (    --h0 of a line bundle on X
    C := moving D;
    H := {3,1,1,1,1,1,1};
    ef := false;    
    if C == {0,0,0,0,0,0,0} then ef = true;  --moving part is empty
    if all(C,i->i>= 0) and C**C > 0 then ef = true;  --moving part is not composite with a conic
    if C ** C == 0 and first C > 0 and (
	C = {first C} | reverse sort drop(C,1);
	C == (first C)* {1,1,0,0,0,0,0} or 
	C == C#1 * {2,1,1,1,1,0,0} or 
	C == C#2 * {3,2,1,1,1,1,1}
	) then ef = true;    --moving part is multiple conics
    if ef == false then return 0 else return 1/2*C**(C+H)+1;
)
h1 = D -> (    --h1 of a line bundle on X
    H := {3,1,1,1,1,1,1};
    return h0(D)+h2(D)-1/2*D**(D+H)-1;  
)
h2 = D -> (    --h2 of a line bundle on X
   H := {3,1,1,1,1,1,1};
   return h0(-D-H);
)

--Invariants
hilbertFunction (List,ZZ) := (C,n) -> (	  --hilbert function
    H := {3,1,1,1,1,1,1};
    trueBinomial(n+3,3)-trueBinomial(n,3)-h0(n*H-C)    
)
raoFunction = (C,n) -> (    --rao function
    H := {3,1,1,1,1,1,1};
    h1(n*H-C)
)
specialty  = (C,n) -> (	   -- specialty function
    H := {3,1,1,1,1,1,1};
    h2(n*H-C)-trueBinomial(2-n,3)+trueBinomial(-n-1,3)    
)
trueBinomial = (n,c) -> if n <0 then 0 else binomial(n,c) -- true binomial count
h = D -> (    --smallest degree surface not a multiple of X
    n := 1;
    H := {3,1,1,1,1,1,1};
    while (
    	C := n*H-D;
	h0(C) == 0	
    ) do (n = n+1;);
    n    
)
k = D -> (    --smallest degree link giving reduced curve
    n := h(D);
    H := {3,1,1,1,1,1,1};    
    while (
    	C := n*H-D;
	h1(C) != 0	
    ) do (n = n+1);
    n
)
e = C -> (    -- index of specialty
    n := -2;
    H := {3,1,1,1,1,1,1};
    while (
        specialty(C,n) != 0	
    ) do (n = n+1);
    n-1        
)
rho = C -> (  --least degree of rao module
    n := e(C);
    if raoFunction(C,n+1)==0 and raoFunction(C,n+2) == 0 then return "infty";
    n = 1;
    while raoFunction(C,n) == 0 do (n = n+1);
    n            
)    

{*
hilbertPoints = method()
hilbertPoints List := L -> (
    x := getSymbol "x";
    S := (ZZ/32003)(monoid[x_0..x_2]);
    n := #L;
    pts := apply(entries random(S^n,S^3), l -> minors(2,matrix{gens S,l}));
    I := intersect(apply(n, i-> (pts#i)^(L#i)));
    i := 0;
    d := degree I;
    hilb := {};
    while (
	h := hilbertFunction(i,I);
	hilb = hilb | {h};
	h != degree I
	 )
    do (i = i+1;);
    hilb
)
hilbertSixPoints = method()
hilbertSixPoints List := D -> (
    h := effectiveDegree D;
    hilb := apply(h, d-> binomial(d+2,2));
    d := h;
    while (
    	C := zariskiDecomposition ({d} | D);
	h0 :=binomial(d+2,2) - binomial(first C+2,2) + sum apply(drop(C,1),b-> binomial(b+1,2));
	h0 != last hilb	
    ) do (hilb = hilb | {h0}; d = d+1);
    hilb
)
dimHilb = method()
dimHilb List := L -> (
    genus L + degree L + 18 - h0({9,3,3,3,3,3,3}-L)
)
*}
end

----Verification of results of Giuffrida et.al.
restart
needsPackage "SpaceCurves"
load "cubic.m2"
H = {3,1,1,1,1,1,1};
R = ZZ/101[x_0..x_3];
X = cubicSurface R;
Ld = flatten apply(splice{4..15},d-> smoothDivisors(d,X));
Ld = Ld / (D -> D.Coordinate);

--mistake for e+1
C = Ld#230
e(C)
h1(moving(C-e(C)*H)-2*H)
genus fixed(C-(e(C)+1)*H)
moving(C-(e(C)+1)*H)

betti raoModule curveIdeal Ld#230
--apply(30,i-> (C = Ld#i; (h1(moving(C-e(C)*H)-2*H),fixed(C-(e(C)+1)*H)))

--mistake for e
C = Ld#28
degree C, genus C
betti raoModule curveIdeal C
e(C)  
moving(C-H) --not multiple conics
degree(C-H)+h0(H-(C-H))-3

--new strat for second Betti number
investigate Ld#16


---Producting the Betti table of an effective divisor
restart
needsPackage "SpaceCurves"
load "cubic.m2"
R = ZZ/101[x_0..x_3];
X = cubicSurface R;
C = {5,3,2,1,1,0,0};
H = {3,1,1,1,1,1,1};

--first step, check effectiveness
h0(C)

--next compute hilbert polynomial
degree C, genus C

--next bound regularity
regbound = h(C)+k(C)-3

--compute Hilbert function
hilb = apply(regbound+4, d-> hilbertFunction(C,d))
Delta Delta Delta Delta hilb

--compute first Betti number	
h0(h(C)*H-C)	--5 in degree 4
linesOnCubic / (L -> L**C) -- 1 in degree 5

--pick an integral linked curve
n = k(C)+1
D = n*H-C 

--compute index of specialty and check ACM
e(D)
raoFunction(D,e(D)+1), raoFunction(D,e(D)+2)

--compute r0
rho(D)
h1(H-D)
h1(moving(D-H)-2*H)
--Check by M2
betti res ideal curve divisor(C,X)



