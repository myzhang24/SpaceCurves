randomForm = (d,I) -> (
    G := mingens I;
    J := ideal(G*random(source G,(ring I)^{-d}));
    J_0
)
RuledCubicSurface = new Type of HashTable
ruledCubicSurface = method()
ruledCubicSurface Ring := kk -> (
    u := getSymbol "u";
    v := getSymbol "v";
    w := getSymbol "w";
    S := kk(monoid[u_0..u_2]);
    R := kk(monoid[v_0..v_3]);
    T := kk(monoid[w_0..w_4]);
    phi := map(S,T,flatten entries super basis(2,ideal(S_0,S_1)));
    psi := map(T,R,{T_0,T_2,T_3,T_4});
    
    new RuledCubicSurface from {    
    	symbol Embedding => phi,
	symbol Projection => psi,
	Ideal => kernel (phi*psi),
	symbol Conic => ideal(T_2,T_4,T_1^2-T_0*T_3)		
    }            
)
GDivisor = new Type of HashTable
gDivisor = method()
gDivisor (List,RuledCubicSurface) := GDivisor => (L,X) -> (
    assert(#L == 4);
    {a,b,P,Q} := toSequence L;
    assert(isSubset(X.Conic,P) and isSubset(X.Conic,Q) and codim P == 4 and codim Q == 4);
    assert((a - degree P + degree Q) % 2 == 0);
    P = (P:P+Q);
    Q = (Q:P+Q);
    t := (ring P)_1;
    sP := sub(P,{t => -t});
    sQ := sub(Q,{t => -t});
    P = (P:P+sP);
    Q = (Q:Q+sQ);
    new GDivisor from {
    	symbol Preimage => {a,b},
	symbol Points => {P,Q},
	symbol Surface => X	
    }            
)
isEffective = method()
isEffective GDivisor := Boolean => D -> (
    (a,b,P,Q) := toSequence (D.Preimage | D.Points);    
    if a>0 and a>b then return true;
    if P == 0 and Q == 0 and b <= 0 then return true;
    if a == b and a >0 and Q == 0 and a > degree P then return true;
    false 
)
smoothCurve = method()
smoothCurve (List,RuledCubicSurface) := (L,X) -> (
    S := target X.Embedding;
    f := map(S/ideal(randomForm(first L, (ideal(S_0,S_1))^(last L))),S);
    IC := kernel (f*X.Embedding);
    ID := kernel (f*X.Embedding*X.Projection);
    {IC,ID}       
)
end

--
restart
load "curves on a ruled cubic surface.m2"
kk = ZZ/101;
X = ruledCubicSurface(kk);
T = ring X.Conic;
P = X.Conic + ideal(T_1); 
Q = X.Conic + ideal(T_3^2);
D = gDivisor({4,2,P,Q},X)
isEffective D
smoothCurve({6,2},X)
