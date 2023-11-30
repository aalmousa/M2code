newPackage(
    "Positroid",
    AuxiliaryFiles => false,
    Version => "0.1", 
    Date => "",
    Authors => {
        {Name => "Ayah Almousa", 
            Email => "almou007@umn.edu", 
            HomePage => "http://sites.google.com/view/ayah-almousa"},
	{Name=> "Shiliang Gao",
	    Email => "",
	    HomePage => ""},
	{Name => "Daoji Huang",
	    Email => "huan0664@umn.edu",
	    HomePage => "daojihuang.me"}
    },
    Headline => "functions for investigating positroid varieties",
    PackageExports => {
        "Posets"
    },
    DebuggingMode => true
)

export{
    "pluckerPoset",    	       	       	 -- documented ++
    "pluckerRelations",	       	       	 -- NOT DOCUMENTED
    "basicPositroidVariety",	    	 -- NOT DOCUMENTED
    "leadTermBasicPositroid",	     	 -- NOT DOCUMENTED
    "leadTermBasicPositroidWrapAround",	 -- NOT DOCUMENTED
    "hodgeDegenerationBasicPositroid",	 -- NOT DOCUMENTED
    "getMultidegree"	    	    	 -- NOT DOCUMENTED
}
    
------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- **CODE** --
------------------------------------------------------------------------------
------------------------------------------------------------------------------

---------------------------------------
---------------------------------------
-- * PART 0: HELPER FUNCTIONS * --
---------------------------------------
---------------------------------------

multiSubsets := (n,k) -> (
    S := subsets(n+k-1,k);
    apply(S, i-> i - toList(0..k-1))
    )

--------------------------------
--auxiliary function for generating a generic matrix of z variables
--INPUT: integers n,m
--OUTPUT: an n by m generic matrix eith entries z_(i,j)
--NOTE: the ring automatically comes equipped with the antidiagonal term order
-----------------------------------

genMat = method(
    Options => {
	CoefficientRing => QQ,
	Variable => getSymbol "z"
	}
    )

genMat (ZZ,ZZ) := o -> (n,m) -> (
    k := o.CoefficientRing;
    zEntries := flatten table (n,m,(i,j) -> (i,j));
    z := o.Variable;
    Q := k(monoid[z_(1,1)..z_(n,m)]);
    Mmut := mutableMatrix(Q,n,m);
    for box in zEntries do (
        Mmut_(box) = Q_(m*(box_0) + box_1);
    );
    matrix Mmut
    )

--order for creating Plucker poset

cmp := (a,b) -> (
    entryCompare := for i from 0 to #a-1 list (a_i >= b_i);
    entryCompare == toList(#a:true)
    )

---------------------------------------
---------------------------------------
-- * PART 1: Gr(k,n) * --
---------------------------------------
---------------------------------------

----------------------------------------------------------
--computes Plucker poset for Gr(n,m)
----------------------------------------------------------

pluckerPoset = method()
pluckerPoset(ZZ,ZZ) := Poset => (n,m) -> (
    coords := subsets(m,n);
    shiftedCoords := apply(coords, i-> i+toList(n:1));
    poset(shiftedCoords, cmp)
    )

----------------------------------------------------------
--outputs the defining relations for k[Gr(n,m)]
----------------------------------------------------------

pluckerRelations = method(
    Options => {
	CoefficientRing => QQ,
	Variable => getSymbol "T"
	}
    )

pluckerRelations (ZZ,ZZ) := o -> (n,m) -> (
    kk := o.CoefficientRing;
    T := o.Variable;
    P := pluckerPoset(n,m);
    shiftedCoords := reverse flatten rank(P);
    coordVars := apply(shiftedCoords, i-> T_i);
    S := kk[coordVars, MonomialOrder=>RevLex, Global=>false];
    M := genMat(n,m, CoefficientRing => kk, Variable => T);
    Q := ring(M);
    minorRels := apply(shiftedCoords, i-> det(M_(i-toList(n:1))));
    F := map(Q,S,minorRels);
    ker F
    )


-------------------------------------------
-------------------------------------------
-- * PART 2: Basic positroid varieties * --
-------------------------------------------
-------------------------------------------

----------------------------------------------------------
--computes positroid Variety for Gr(k,n) with positroid (L,r)
----------------------------------------------------------

basicPositroidVariety = method(
    Options => {
	CoefficientRing => QQ,
	Variable => getSymbol "T"
	}
    )

basicPositroidVariety (ZZ,ZZ,List,ZZ) := o -> (k,n,L,r) -> (
    kk := o.CoefficientRing;
    T := o.Variable;
    I := pluckerRelations(k,n, CoefficientRing => kk, Variable => T);
    R := ring I;
    killedMinors := subsets(L,r+1);
    killedCoords := new MutableList;
    for i in R_* do (
	for j in killedMinors do(
	    if isSubset(j,(baseName i)#1) then killedCoords#(#killedCoords) = i;
	    );
	);
    ideal mingens(I + ideal toList killedCoords)
    )


--lists possible locations of generalized antidiagonals of length l
--for a standard monomial of degree d in Gr(k,n)
possibleGeneralizedAntidiagonals := (k,d,l) -> (
    possibleRows := apply(select(multiSubsets(d,l), q-> isSubset(toList(0..d-1),q)),reverse);
    possibleCols := subsets(k,l);
    --apply(subsets(k,l),i-> i+toList(k:1));
    apply(possibleRows**possibleCols, p -> pack(mingle p, 2))
    )

----------------------------------------------
--outputs LTs without computing actual equations
--the output is as matrices that are transposes of semistandard tableaux
----------------------------------------------
leadTermBasicPositroid = method()

leadTermBasicPositroid (ZZ,ZZ,List,ZZ) := List => (k,n,L,r) -> (
    P := pluckerPoset(k,n);
    G := P.GroundSet;
 
    badSets := subsets(L,r+1);
    vanishingCoords := new MutableList;
    
    --loop to find coordinates that should vanish
    for g in G do (
    	for b in badSets do (
	    if isSubset(b,g) then (
	    	vanishingCoords#(#vanishingCoords)=g;
	    	break;
	    	);
	    continue;	    
	    );
    	);
    
    vanishingCoords = toList vanishingCoords;

    
    P' := dropElements(P,vanishingCoords);
    incompLTs := apply(antichains(P',2), i-> sort i);
    
    antiDiagLTs := new MutableList;
    
    for d from 2 to r+1 do (
	antidiags := possibleGeneralizedAntidiagonals(k,d,r+1);
	possibleLTs := apply(chains(P',d), i-> matrix sort i);
	for m in possibleLTs do (
	    for a in antidiags do (
		for b in badSets do (
		    if (b==apply(a, j -> m_(toSequence j))) then (
			antiDiagLTs#(#antiDiagLTs) = m;
			break;
			);
		    continue;
		    );
		);
	    );
	);
    antiDiagLTs = unique toList antiDiagLTs;
    
    apply(vanishingCoords, i -> matrix{i})|apply(incompLTs, j-> matrix j)|antiDiagLTs
    );

--------------------------------------------------------------------------
--meant for cases where interval wraps around, i.e. includes both n and 1
--------------------------------------------------------------------------
leadTermBasicPositroidWrapAround = method()

leadTermBasicPositroidWrapAround (ZZ, ZZ, List, ZZ) := List => (k,n,L,r) -> (
    compLTs := leadTermBasicPositroid(n-k,n,toList(set(1..n)-L),n-k-#L+r);
    apply(compLTs, i-> matrix(sort apply(entries i, j-> sort toList(set(1..n)-j))))
    )


hodgeDegenerationBasicPositroid = method(
    Options => {
	CoefficientRing => QQ,
	Variable => getSymbol "T"
	}
    )

hodgeDegenerationBasicPositroid(ZZ,ZZ,List,ZZ) := o -> (k,n,L,r) -> (
    kk := o.CoefficientRing;
    T := o.Variable;
    P := pluckerPoset(k,n);
    shiftedCoords := reverse flatten rank(P);
    coordVars := apply(shiftedCoords, i-> T_i);
    S := kk[coordVars, MonomialOrder=>RevLex, Global=>false];
    varHash := hashTable apply(S_*, v-> last baseName v => v);
    if any(L, i-> i==1) and any(L, i-> i==n) then (
	tabs := leadTermBasicPositroidWrapAround(k,n,L,r);
	)
    else (tabs = leadTermBasicPositroid(k,n,L,r));
    ideal apply(tabs, tab -> product(apply(entries tab, i -> varHash#i)))
    );

getMultidegree = method();

getMultidegree(MonomialIdeal) := I -> (
    t := symbol t;
    R := ring I;
    varList := R_*;
    n := last last baseName varList#(#varList-1);
    Q := ZZ[t_1..t_n];
    comps := decompose I;
    sum apply(comps, c-> product apply(c_*, i-> sum apply(last baseName i, j-> t_j)))
);

----------------------------------------------
----------------------------------------------
-- * PART 3: General positroid varieties * --
----------------------------------------------
----------------------------------------------



-------------------------------------------
-------------------------------------------
-- * PART 4: Cyclic Demazure modules * --
-------------------------------------------
-------------------------------------------



------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- **DOCUMENTATION** --
------------------------------------------------------------------------------
------------------------------------------------------------------------------
beginDocumentation ()    

doc ///
    Key
        Positroid
    Headline
        a package for investigating postroid varieties
    Description
        Text
            This package provides functions for constructing and investigating postroid varieties.
	    This includes understanding Grobner bases and standard monomials for them.
	    This package also includes functions for investigating the torus characters of cyclic Demazure modules.
        Text
            @UL {
	    {"[KLS14] Allen Knutson, Thomas Lam, and David E. Speyer, ",
	    HREF("https://arxiv.org/abs/1008.3939", EM "Projections of Richardson Varieties"),
	    " , Journal für die reine und angewandte Mathematik (Crelles Journal), 2014(687), 133-157."},
            }@  
///


doc ///
    Key
        (pluckerPoset, ZZ, ZZ)
        pluckerPoset
    Headline
        the Plucker poset for Gr(k,n)
    Usage
        pluckerPoset(k,n)
    Inputs
        n:ZZ
	m:ZZ
    Outputs
    	:Poset
    Description
        Text
            Given integers k,n, outputs the poset of Plucker coordinates
        Example
            (pluckerPoset(2,4)).Relations
///
------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- **TESTS** --
------------------------------------------------------------------------------
------------------------------------------------------------------------------




end---------------------------------------------------------------------------     

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- **SCRATCH SPACE** --
------------------------------------------------------------------------------
------------------------------------------------------------------------------

I = 

---------------------
--Ayah's sandbox
---------------------

I1 = hodgeDegenerationBasicPositroid(3,6,{5,6,1,2,3},2);
I2 = sub(hodgeDegenerationBasicPositroid(3,6,{1,2},1),ring I1);
I = I1+I2;
getMultidegree monomialIdeal I
codim I

J2 = sub(hodgeDegenerationBasicPositroid(3,6,{6,1,2},1),ring I1);
J = I1+J2;
codim J



------------------------------------
--Development Section
------------------------------------

restart
uninstallPackage "Positroid"
restart
installPackage "Positroid"
restart
needsPackage "Positroid"
elapsedTime check "Positroid"
viewHelp "Positroid"

