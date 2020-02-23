newPackage(
        "CodimTwoACM",
        Version => "1.0", 
        Date => "June 2019",
        Authors => {{Name => "Mengyuan Zhang", 
                  Email => "myzhang@berkeley.edu", 
                  HomePage => "https://math.berkeley.edu/~myzhang/"}
	      },
        Headline => "Codimension Two ACM subvarieties of P^n",
        DebuggingMode => true
        )

export {
	"castelnuovo",
    	"hilbertBurch",
	"Smooth"	
}


makeCastelnuovo = method(Options => { Smooth => false})
makeCastelnuovo(ZZ,List) := opts -> (d,bin) -> (
    --takes a list of partial castelnuovo functions of degree d
    --produces a one step extension 
    L := flatten apply(bin, C -> (
	m := max C;
    	if opts.Smooth and C#-1 < C#-2 then (
	    m = min(d-sum C,C#-1-1);
	) else m = min(d-sum C,C#-1);     
    	apply(splice{1..m}, i -> C |{i})		    
    )
    );
    (select(L, C -> sum C == d), select(L, C -> sum C < d))   
)

castelnuovo = method(Options => {Smooth => false})
castelnuovo ZZ := opts -> d -> (
    --generates all castelnuovo functions of degree d
    --by default Smooth
    flatten apply(splice{2..floor (sqrt (2*d+1/4-1/2))}, s -> (
	finished := {};
	bin := {};
	unfinished := {splice{1..s}};
    	while (
	    (finished, unfinished) = makeCastelnuovo(d,unfinished,Smooth=>opts.Smooth);	    
	    bin = bin | finished;
	    #unfinished > 0
	) do ();
	bin    
    )	
    )
)

diff List := G -> (G | {0}) - ({0} | G)

hilbertBurch = method(Options => {Smooth => false})
hilbertBurch List := opts -> cs -> (
    --takes a castelnuovo function
    --returns all Hilbert-Burch degree matrices
    cs = {0} | drop(diff diff cs,1);
    B := flatten apply(positions(cs, i -> i>0), j-> splice{cs#j:j});
    A := flatten apply(positions(cs, i -> i<0), j-> splice{-cs#j:j});
    degs := {(A,B)};
    bin := degs;
    sp := {};
    while (
    	sp = flatten for AB in bin list (
	    apply(splice{1+min first AB..-1+max last AB}, 
		j -> (first AB | {j}, last AB | {j}))        
	);
    	sp = select(sp, AB -> 
	    all(rsort last AB - drop(rsort first AB,-1),
		j -> j>0));
    	degs = unique (degs | sp);
	bin = sp;
	sp != {}
    ) do ();
    if opts.Smooth then 
    degs = select(degs, AB -> 
	all(drop(rsort last AB,1)-drop(rsort first AB,-2),
	    j -> j>0));
    apply(degs, AB -> matrix apply(rsort first AB, l -> 
	apply(rsort last AB, m -> m-l)))           
)
hilbertBurch ZZ := opts -> d -> (
    flatten apply(castelnuovo(d, Smooth => opts.Smooth), 
	cs -> hilbertBurch(cs, Smooth => opts.Smooth))    
)
random (Ring,Matrix) := opts -> (R,M) -> (
    --produces a matrix of random forms in R with degrees 
    --specified by M
    matrix apply(entries M, row -> 
	apply(row, a -> if a == 0 then 0 else random(a,R))) 
)
minors Matrix := opts -> M -> (
    n := min(numcols M, numrows M);
    minors(n,M)    
)


beginDocumentation()
document {
    Key => CodimTwoACM,
    Headline => "Codimension two ACM subvarieties of P^n",
    PARA { 
    	"Let X be a be codimension two ACM subvariety of P^n.
	Let R_X be the coordinate ring of X, 
	its free resolution over the polynomial ring R is given by the Hilbert-Burch complex."
    },
    PARA {
    	"This package generates codimension two ACM subvarieties of P^n
	of all possible formats. By format we mean the degrees of the forms
	in the Hilbert-Burch matrix, 
	which is equivalently given by the graded Betti numbers of R_X."		
    },
    PARA {	
    	"Since R_X has high depth, we may quotient by successive linear
	forms and reduce to points in P^2 without changing the Betti numbers."
    },
    PARA {
	"Let Z be a zero dimensional scheme of degree d in P^2.
	The first numerical difference of the Hilbert function H(Z,n)-H(Z,n-1)
	is called a Castelnuovo function of degree d."
    },
    PARA { 
	"The method ", TO (castelnuovo,ZZ), " generates all Castelnuovo functions of a given degree."
    },
    EXAMPLE {
    	"L = castelnuovo 6"
    },
    PARA {
    	"The method ", TO (hilbertBurch,List), " generates all Hilbert-Burch degree matrices
	corresponding to a given Castelnuovo function."	
    },
    EXAMPLE {
    	"D = hilbertBurch L#0"	
    },
    PARA {
	"The method ", TO (random, Ring, Matrix), " generates random
	forms according to the degrees specified by the Hilbert-Burch matrix."
    },
    EXAMPLE {
    	"R = ZZ/101[x_0..x_2]",
	"S = ZZ/101[y_0..y_3]",
	"M1 = random(R, last D)",
	"M2 = random(S, last D)"	
    },
    PARA {
	"The method ", TO (minors, Matrix), " by default computes the ideal of the 
	maximal minor, this way producing the ideal of a codimension two ACM subvariety
	of P^n."
    },
    EXAMPLE {
    	"I = minors M1 -- points in P^2",
	"J = minors M2 -- curve in P^3",
	"betti res I",
	"betti res J"	
    }	
}

document {
    
    
}


end


---
restart
uninstallPackage "CodimTwoACM"
installPackage "CodimTwoACM"
viewHelp "CodimTwoACM"