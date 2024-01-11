newPackage(
    "CriticalGroups",
    AuxiliaryFiles => false,
    Version => "0.1", 
    Date => "",
    Keywords => {"Combinatorics"},
    Authors => {
        {Name => "Ayah Almousa", 
            Email => "almou007@umn.edu", 
            HomePage => "http://sites.google.com/view/ayah-almousa"}
    },
    Headline => "functions for investigating critical groups of simplicial complexes",
    PackageExports => {
        "SimplicialComplexes",
        "SimplicialDecomposability",
        "Posets",
    },
    DebuggingMode => true
)

export{
-- ++ means tested
"combinatorialLaplacian",	     --documented ++
"listLaplacians",    	     	     --documented
"invariantFactors",    	     	     --docmented ++
"shiftedComplex",	      	     --documented ++
"reducedLaplacianShifted"    	     --documented ++
}
------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- **CODE** --
------------------------------------------------------------------------------
------------------------------------------------------------------------------

-------------------------------------------
-- ** Part 1 : Combinatorial Laplacians **
-------------------------------------------

combinatorialLaplacian = method()

combinatorialLaplacian(SimplicialComplex,ZZ) := Matrix => (Delta,k) -> (
    C := chainComplex Delta;
    dk := C.dd_k;
    dk*transpose(dk)
    )

listLaplacians = method()
listLaplacians(SimplicialComplex) := List => D -> (
     apply((dim D)+1, i-> combinatorialLaplacian(D,i))
     )

invariantFactors = method()

invariantFactors SimplicialComplex := List => Delta -> (
    L := combinatorialLaplacian(Delta, dim Delta);
    M := (smithNormalForm(L, KeepZeroes => false))_0;
    toList eigenvalues M
)


--isSpanningTree
-----------------------------------
-- ** Part 2: Shifted complexes **
-----------------------------------

cmp := (a,b) -> (
    entryCompare := for i from 0 to #a-1 list (a_i <= b_i);
    entryCompare == toList(#a:true)
    )

galePoset = method()
galePoset(ZZ,ZZ) := Poset => (n,m) -> (
    coords := subsets(m,n);
    shiftedCoords := apply(coords, i-> i+toList(n:1));
    poset(shiftedCoords, cmp)
    )

shiftedComplex = method(
    Options => {
	CoefficientRing => ZZ,
	Variable => getSymbol "x"
	}
    )

shiftedComplex List := o -> L -> (
    --lazy order ideal, make efficient later
    if (#(unique apply(L, i->#i)) != 1) then error("the generating facets should be the same dimension");
    d := #(L_0);
    maxElt := max flatten L;
    P := galePoset(d,maxElt);
    facetGens := orderIdeal(P,L);
    
    --construct simplicial complex
    kk := o.CoefficientRing;
    x := o.Variable;
    indets := apply(1..maxElt, i-> x_i);
    S := kk[indets, DegreeRank => #indets];
    varHash := hashTable apply(S_*, v-> last baseName v => v);
    facetList := apply(facetGens, i-> product(apply(i, j-> varHash#j)));
    simplicialComplex facetList
    )


reducedLaplacianShifted = method()

reducedLaplacianShifted List := Matrix => L -> (
    D := shiftedComplex L;
    Lap := combinatorialLaplacian(D, dim D);
    ridgeList := faces( (dim D)-1, D);
    pos := positions(ridgeList, i-> (degree i)_0 == 1);
    submatrix'(Lap,pos,pos)
    );
     


-------------------------------------------------
-- ** Part 3: Potential statistics to study**
------------------------------------------------


------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- **DOCUMENTATION** --
------------------------------------------------------------------------------
------------------------------------------------------------------------------
beginDocumentation()

doc ///
    Key
        CriticalGroups
    Headline
        critical groups for simplicial complexes
    Description
        Text
            This package provides functions for constructing and investigating critical groups
	    and combinatorial Laplacians for simplicial complexes. It contains functions
	    for exploring combinatorial Laplacians for shifted complexes and independence complexes of Schubert matroids.
        Text
            @UL {
	    {"[Kli18] Klivans, Caroline (2018). The mathematics of chip-firing (1st ed.). Chapman and Hall/CRC."}
	    }@ 
///

doc ///
    Key
        combinatorialLaplacian
        (combinatorialLaplacian, SimplicialComplex, ZZ)
    Headline
        combinatorial Laplacian of a simplicial complex
    Usage
        combinatorialLaplacian(D,k)
    Inputs
        D:SimplicialComplex
	k:ZZ
    Outputs
    	:Matrix
    Description
        Text
            Given a simplicial complex $\Delta$ and an integer $k$ which is less than or equal to the dimension
	    of $\Delta$, outputs the $k$'th combinatorial Laplacian for $\Delta$.
        Example
	    S = ZZ[a..d];
	    D = simplicialComplex {a*b*c,a*b*d,a*c*d,b*c*d}
	    combinatorialLaplacian(D,2)
///

doc ///
    Key
        listLaplacians
        (listLaplacians, SimplicialComplex)
    Headline
        list all combinatorial Laplacians of a simplicial complex
    Usage
        listLaplacians D
    Inputs
        D:SimplicialComplex
    Outputs
    	:List
    Description
        Text
            Given a simplicial complex $\Delta$ and an integer $k$ which is less than or equal to the dimension
	    of $\Delta$, outputs a list of all combinatorial Laplacians for $\Delta$.
        Example
	    S = ZZ[a..d];
	    D = simplicialComplex {a*b*c,a*b*d,a*c*d,b*c*d}
	    listLaplacians D
///

doc ///
    Key
        invariantFactors
        (invariantFactors, SimplicialComplex)
    Headline
        invariant factors of a simplicial complex
    Usage
        invariantFactors D
    Inputs
        D:SimplicialComplex
    Outputs
    	:List
    Description
        Text
            Given a simplicial complex $\Delta$, outputs the invariant factors for $\Delta$.
        Example
	    S = ZZ[a..d];
	    D = simplicialComplex {a*b*c,a*b*d,a*c*d,b*c*d}
	    invariantFactors D
///

doc ///
    Key
        shiftedComplex
        (shiftedComplex, List)
    Headline
        shifted complex generated by a set of facets
    Usage
        shiftedComplex L
    Inputs
        L:List
    Outputs
    	:SimplicialComplex
    Description
        Text
            Given a list of indices, outputs the smallest shifted simplicial complex
	    containing those facets.
        Example
	    shiftedComplex {{2,3,4}}
	    shiftedComplex {{1,3,5},{2,3,4}}
///

doc ///
    Key
        reducedLaplacianShifted
        (reducedLaplacianShifted, List)
    Headline
        reduced Laplacian for a shifted complex
    Usage
        reducedLaplacian L
    Inputs
        L:List
    Outputs
    	:Matrix
    Description
        Text
            Given a list of indices $L$, outputs the reduced Laplacian for the shifted complex
	    with generators in $L$. The spanning tree that is used to reduce the Laplacian
	    is the one corresponding to all codimension $1$ faces containing the vertex labeled $1$.
        Example
	    L = {{2,4,5}};
	    reducedLaplacianShifted L
	    (smithNormalForm oo)_0
	    tally invariantFactors shiftedComplex L
///
------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- **TESTS** --
------------------------------------------------------------------------------
------------------------------------------------------------------------------
TEST ///
--boundary of tetrahedron
S = ZZ[a..d];
D = simplicialComplex({a*b*c,a*b*d,a*c*d,b*c*d})
M = matrix{
    {3,-1,-1,-1},
    {-1,3,-1,-1},
    {-1,-1,3,-1},
    {-1,-1,-1,3}
    };
assert(combinatorialLaplacian(D,1) == M)
assert(sort invariantFactors(D) == {1,1,4})     
///

TEST ///
--build boundary of tetrahedron as a shifted complex
D = shiftedComplex {{2,3,4}};
S = ring D;
assert(simplicialComplex(apply(subsets(S_*,3), i-> product i)) === D)
///


TEST ///
--testing reducedLaplacianShifted
L = {{2,4,5,7}};
redLap = reducedLaplacianShifted L;
L1 = toList eigenvalues (smithNormalForm oo)_0;
L2 = invariantFactors shiftedComplex L;
assert(L1 == L2)
///
end---------------------------------------------------------------------------     

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- **SCRATCH SPACE** --
------------------------------------------------------------------------------
------------------------------------------------------------------------------


--------------------------------
--------------------------------
-- **EXAMPLES / CODE DEMO** --
--------------------------------
--------------------------------

EXAMPLE \\\
--tetrahedron
D = shiftedComplex {{2,3,4}} --tetrahedron
L = listLaplacians D
invariantFactors D

--lists
printingAccuracy = 1 --for rounding the eigenvalues to integers
apply(L, i-> sort toList eigenvalues i) --list eigenvalues for all the Laplacians
--
\\\

EXAMPLE \\\
--Other example from Carly's write-up
D = shiftedComplex {{3,4,6}}
L = listLaplacians D

printingAccuracy = 1  --for rounding the eigenvalues to integers
apply(L, i-> sort toList eigenvalues i)
invariantFactors D
\\\

EXAMPLE \\\
--a shifted complex which is not a shifted matroid
D = shiftedComplex {{1,3,5},{2,3,4}}
L = listLaplacians D

printingAccuracy = 1  --for rounding the eigenvalues to integers
apply(L, i-> sort toList eigenvalues i)
invariantFactors D
\\\

EXAMPLE \\\
--using the reducedLaplacianShifted function
L = {{2,4,6,7}};
reducedLaplacianShifted L
(smithNormalForm oo)_0
tally invariantFactors shiftedComplex L
\\\


------------------------------------
--Development Section
------------------------------------

restart
uninstallPackage "CriticalGroups"
restart
installPackage "CriticalGroups"
restart
needsPackage "CriticalGroups"
elapsedTime check "CriticalGroups"
viewHelp "CriticalGroups"
