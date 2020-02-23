--IV.Characters

Character = new Type of HashTable
net Character := H -> net apply(sort delete(inf,keys H), i -> H#i)

-Character := Character => H -> new Character from apply(keys H, i -> i => -H#i)	
truncate Character := H -> (
    --trims leading and ending 0s
    spt := select(delete(inf,keys H), k-> H#k != 0);
    (s,m) := (min(0,min spt),max(0,max spt));
    L := apply(splice{s..m}, k -> k => H#k);
    if H#?inf then new Character from (L | {inf => H#inf})
    else new Character from L
)
Character + Character := Character => (F,G) -> (
    K := keys F | keys G;
    new Character from
    	apply(K, k -> if (not F#?k) then k => G#k  
	else (if not G#?k then F#k else k => F#k+G#k))
)
Character - Character := Character => (F,G) -> (
    K :=  keys F | keys G;
    new Character from
    	apply(K, k -> if (not F#?k) then k => -G#k  
	else (if not G#?k then F#k else k => F#k-G#k))
)
diff Character := Character => H -> (
    K := delete(symbol inf,keys H);
    	L := apply(K, k -> if H#?(k-1) then k => H#k-H#(k-1) else k => H#k);
	if H#?inf then (
	    P := H#inf;
	    if class P === ZZ then 
	    	truncate new Character from (
		    L | {max(K)+1 => P - H#(max K), inf => 0}    
		)
	    else (
	    	i := (ring P)#0;
	    	truncate new Character from (
	    	    L | {max(K)+1 => P[max(K)+1]-H#(max K), inf => P[i]-P[i-1]} 
		)		
	    )
	) else (
       	    new Character from (L | {max(K)+1=>-H#(max K)})
    	)
)
diff(ZZ,Character) := Character => (n,H) -> ( 
    if n<0 then null else if n == 0 then H else if n == 1 then diff H else diff diff(n-1,H)
)
lowerIntegral = method()
lowerIntegral(ZZ,Character) := (p,H) -> (
    if p < 0 then return null;
    if p == 0 then return H;
    if p == 1 then return (
	K := delete(inf,keys H);
    	new Character from for k from min K to 20 list (
    	    	k => sum apply(splice{min K..k}, j -> if H#?j then H#j else 0)
	)
    ); 
    if p > 1 then return lowerIntegral(1,lowerIntegral(p-1,H))      
)

character = method()
character(ZZ,Ideal) := Character => (n,I) -> (
    if n < 0 then return null;
    if n == 0 then return
         new Character from (
	     apply(degree I+n+1, n -> n => hilbertFunction(n,I)) |
	     {symbol inf => hilbertPolynomial(I, Projective => false)}
	 );
    if n > 0 then return diff(n,character(0,I));    
)
character(ZZ,Module) := Character => (n,M) -> (
    if n < 0 then return null;
    if n == 0 then return
         new Character from (
	     apply(regularity M+pdim M-1+n, n -> n => hilbertFunction(n,M)) |
	     {symbol inf => hilbertPolynomial(M, Projective=> false)}
	 );	     	 
    if n > 0 then return diff(n,character(0,M));   
)


--Spectrums
Spectrum = new Type of Character
spectrum = method()
spectrum Character := Spectrum => C -> new Spectrum from C
degree Spectrum := ZZ => sp -> (
    K := delete(symbol inf,keys sp);
    sum apply(K, k -> sp#k)    
)
genus Spectrum := ZZ => sp -> (
    K := delete(symbol inf,keys sp);
    1+sum apply(K, k -> (k-1)*sp#k)    
)

sectionRing = method()
sectionRing Ideal := Module => I -> (
    HH^0((sheaf comodule I)(*))    
)
spectrum Ideal := Spectrum => I -> spectrum character(2,sectionRing I)

connected = method()
connected Character := Boolean => L-> (
    spt := select(delete(inf, keys L), k -> L#k>0);
    spt == splice{min(spt)..max(spt)}    
)
oneProperty = method()
oneProperty Spectrum := Boolean => sp-> (
    L := apply(sort delete(inf,keys sp),k-> sp#k);
    L = drop(drop(L,1),-1);
    if any(L, i -> i == 1) then L == splice{#L:1} else true          
)
twoProperty = method()
twoProperty Spectrum := Boolean => sp-> (
    L := apply(sort delete(inf,keys sp),k-> sp#k);
    L = drop(L,1);
    if any(drop(drop(L,1),-1), i -> i==2) then (
    	drop(L,-1) == splice{#L-2:2} or
	(L#0 == 2 and last L == 1 and all(drop(drop(L,-2),1),i-> i != 2))
    ) else true	
)
stanley = method()
stanley Spectrum := Boolean => sp -> (
    L := drop(apply(sort delete(inf,keys sp), k->sp#k),1);
    all(splice{1..#L-2}, n -> all(splice{1..#L-1-n}, m -> 
	    sum apply(n, i -> L#i) <= sum apply(n, i -> L#(i+m)))
    )
)
spectrums = method()
spectrums (ZZ,ZZ) := (d,g) -> (
    --produces a list of plausible spectrums for integral curves of a given degree and genus
    t := getSymbol "t";
    R := (ZZ/2)(monoid[t_1..t_(d-1), Degrees => splice{{1,0}..{1,d-2}}]);
    exps := apply(flatten entries basis({d-1,g},R), f -> first exponents f);
    L := apply(exps, sp -> 
	truncate new Character from ( 
	    {0 => 1} | 
	    apply(#sp, i -> i+1 => sp#i) |
	    {symbol inf => 0}
	)
    ) / spectrum;
    select(L, sp -> connected sp and oneProperty sp and twoProperty sp and stanley sp)
)


--PostulationCharacter
PostulationCharacter = new Type of Character
degree PostulationCharacter := C -> (
    K := delete(symbol inf,keys C);
    sum apply(K, k -> k*C#k)
)
genus PostulationCharacter := C -> (
    K := delete(symbol inf,keys C);
    1+sum apply(K, k -> binomial(k-1,2)*C#k)
)
postulationCharacter = method()
postulationCharacter Character := PostulationCharacter =>  C -> new PostulationCharacter from C
postulationCharacter Ideal := Character => I-> postulationCharacter (-character(3,I))

postulationCharacters = method(Options => {symbol Connected => false})
postulationCharacters (ZZ,ZZ) := PostulationCharacter => opts -> (d,s) -> (
    --Generates all postive postulation characters of degree d and least degree surface s
    a := getSymbol "a";
    deg := apply(splice{s..d},i->{1,i});
    R := (ZZ/2)(monoid[a_s..a_d,Degrees=> deg]);
    normalize := {s,d-sum apply(s,k-> -k)};
    L := apply(flatten entries basis(normalize,R), p -> 
	postulationCharacter truncate new Character from (
    	    apply(s, i -> i=>-1) |
	    apply(d-s+1, i -> s+i => (flatten exponents p)#i) | 
	    {symbol inf => 0}
	)	
    );
    if opts.Connected then select(L, pc -> connected pc) else L
)
postulationCharacters ZZ := List => opts -> d -> (
    --Generates all positive characters of degree d
    flatten apply(splice{1..d-1},s-> postulationCharacters(d,s, Connected => opts.Connected))
)
