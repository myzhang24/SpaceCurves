--Bounding Hilbert and Rao functions
raoBounds = method()
raoBounds(List,List) := (pc,sp) -> (
    L := int sp - int pc;
    M := int L;
    S := int int sp;
    L = apply(#L, i -> max(L#i,S#i-binomial(i+3,3)));
    apply(#L, i -> if L#i == M#i then toString L#i else 
	concatenate {toString L#i, "-", toString M#i})
)
hilbertBounds = method()
hilbertBounds(List,List) := (pc,sp) -> (
    L := int sp - int pc;
    M := int L;
    S := int int sp;
    M = apply(#M, i-> binomial(i+3,3)-S#i+M#i);
    L = apply(#L, i-> max(0,binomial(i+3,3)-S#i+L#i));
    apply(#L, i -> if L#i == M#i then toString L#i else 
	concatenate {toString L#i, "-", toString M#i})	    
)

