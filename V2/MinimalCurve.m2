

raoModule = method()
raoModule Ideal := I -> (
    n := numgens ring I-1;
    coker (dual res Ext^n(comodule I,ring I)).dd_(-n)
)
minimalCurve = method(Options =>  {Ideal => false})
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
    assert(isField coefficientRing R);
    assert(numgens R == 4);
    assert(dim M == 0);
    
    if M == 0 then return ideal(R_0,R_1);
    
    Q := res M;
    r := rank Q_2 - rank Q_3 + rank Q_4 - 1;
    degs := flatten last degrees Q.dd_2;
    ok := 1;
    L := {};
    degloop := unique degs;
    deg := first degloop;
    while #L < r do (
	--This algorithm computes the correct columns to select
	--to Brunsify into an ideal
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
    h := sum L - sum flatten degrees Q_2 + sum flatten degrees Q_3 - sum flatten degrees Q_4;	
    cols := for i from 0 to #degs-1 list (	
    	j := position(L, l -> l == degs#i);
	if j === null then (
	    i   
	) else (    	    
	    L = drop(L,{j,j});
	    continue    
	)    		
    );
    if opts#Ideal then (
        ideal gens kernel transpose (random(Q_2,Q_2)*(Q.dd_3))^cols
    ) else (
	betti chainComplex {random(R^1,(target (Q.dd_3)^cols)**R^{-h}),(Q.dd_3)^cols**R^{-h},
	 Q.dd_4**R^{-h}, Q.dd_5**R^{-h}}
    )
)
minimalCurve Ideal := opts-> I -> minimalCurve(raoModule I, Ideal => opts.Ideal)