needsPackage "SimplicialComplexes"
needsPackage "SimplicialDecomposability"

--------------------------
--Functions
--------------------------
--These are helper functions, not super important
-*
Inputs:
   - n = number of columns
   - m = number of rows
   - Q = polynomial ring
Outputs: an  nxm matrix using the variables in Q
-The point is that this won't be stupid like genericMatrix
*-
genericMat := (n,m,Q) -> (
    use Q;
    Mmut:=mutableMatrix(Q,n,m);
    for i from 0 to n-1 do (
	for j from 0 to m-1 do (
	    Mmut_(i,j)=x_(i+1,j+1);
	    );
	);
    matrix Mmut
    )

-*
Inputs:
   - n = number of rows
   - m = number of columns
   - R = polynomial ring
Outputs: 
    -A list of maps coming from permuting the columns
    -This list of maps is stored in the cache of the ring
*-
permRing := (n,m,R) -> (
    M := genericMat(n,m,R);   
    L := for p in permutations m list
            map(R, R, flatten entries M_p);
    L
    )

-*
Inputs
    -c = number of rows
    -n = max number of columns
Outputs: a sequence of polynomial rings in c x i variables, c<=i<=n
*-
ringSequence := (c,n) -> (
    S := for i from 1 to n list ZZ/101[x_(1,1)..x_(c,i)];
    flatten S
    )

------------------------------------------------------------------------
--**This is the most important one!**
--Inputs: (Ideal, number of rows, min number of columns, max number of columns)
--Outputs: a list of ideals I_k = Sym_k(I) where k ranges from l to n
-------------------------------------------------------------------------
idealSym := (I,c,l,n) -> (
    S := ringSequence(c,n);
    L := new MutableList;
    for i from l to n do (
	use S_(i-1);
	J = sub(I,S_(i-1));
	P = permRing(c,i,S_(i-1));
	k = i-l;
	L#k = ideal mingens sum apply(P,i->i(J));
	);
    new List from L
    )

-*
**Exponent Matrix Code**
Inputs:
    - m: a monomial
    - c: number of rows of matrix
    - n: number of columns of matrix
    - R: polynomial ring with cxn variables
*-
exponentMatrix := (m,c,n,R) -> (
    mon := sub(m,R);
    L := first first listForm mon;
    M  := mutableMatrix(ZZ,c,n);
    for i from 0 to c-1 do (
    	for j from 0 to n-1 do
       	   M_(i,j) = L#(i*n +j);
	   );
    matrix M
    )

--mons a list of monomials, G a list of ring maps
--returns a minimal subset orbits of mons such that G*orbits = Mons

orbitGens := (mons, G) -> (
    if #mons == 0 then return {};
    S := ring mons_0;
    G1 := select(G, s-> s vars S != vars S); --removes identity
    L := new MutableList from mons;
    LH := hashTable for i from 0 to #mons-1 list mons#i => i;
    count := #L;
    if debugLevel > 0 then << "-- " << #L << " ideals" << endl;
    for i from 0 to #L-1 list (
        if L#i === null then continue;
        F := L#i;
        for f in G1 do (
            H := f F;
            if LH#?H then (
                j := LH#H;
                if j > i and L#j =!= null then (
                    L#j = null;
                    count = count - 1;
                    if count % 1000 == 0 and debugLevel > 0 then
                        << "--  remaining count: " << count << endl;
                    );
                );
            );
        F
        )
    )

-*
Inputs:
    - L: a list of monomial ideals
    - c: number of rows
    - n: minimum number of columns in list
    
Outputs: list of exponent matrices of Alexander duals, up to symmetry
*-
listDualGens := (L,c,n) -> (
    duals := L/dual;
    dualOrbits := for i from 0 to #duals-1 list (
    	orbitGens((duals_i)_*, permRing(c,i+n,ring (L_i)))
	);
    K := new MutableList;
    for i from 0 to #dualOrbits-1 do (
    	K#i = apply((dualOrbits_i), j-> exponentMatrix(j,c,i+n, ring (duals_i)));
    	);
    new List from K
)

-*
Inputs:
    - L: a list of monomial ideals
    - c: number of rows
    - n: minimum number of columns in list
    
Outputs: list of exponent matrices of facets of the SR complex, up to symmetry
*-
listFacetGens := (L,c,n) -> (
    deltas := L/simplicialComplex;
    facetOrbits := for i from 0 to #deltas-1 list(
	orbitGens(flatten entries facets deltas_i, permRing(c,i+n, ring L_i))
	);
    K := new MutableList;
    for i from 0 to #facetOrbits-1 do (
	K#i = apply((facetOrbits_i), j-> exponentMatrix(j,c,i+n, ring (deltas_i)));
	);
    new List from K
    )
	
-*	
-one orbit conjectured form
-Inputs: 
    - A: exponent matrix for orbit generator
    	-Note: A must be a 0-1 matrix
*-
conjAD := (A) -> (
    	c:= numrows A;
	n:= numcols A;
	S = subsets c;
	L := for i from 0 to n-1 list(A_i);
	for j in S do (
	    k_j := number(L, i-> i^j == vector toList (length j:1));
	    );
      
      -*
Start by making a ring. The number of variables you put in here
doesn't actually matter since the function makes new rings, anyway.
*-
Q = ZZ/101[x_(1,1)..x_(3,4)];
I = ideal(x_(1,1)*x_(1,2), x_(1,1)*x_(2,1))

--do this to make the sequence all monomial ideals
L = (idealSym(I,2,2,5))/monomialIdeal

--confirmation that orbitGens works
for i from 0 to #L-1 list (
    orbitGens((L_i)_*, permRing(2,i+2,ring (L_i))))
--indeed, we get back the generators we typed for all i

--now you can apply a function to this to see patterns, e.g
deltas = (L/simplicialComplex) --list of simplicialComplexes
duals = (L/dual) --list of Alexander duals
bettis = apply(L,i-> betti res i) -- list of Betti tables
dualBettis = apply(duals, i-> betti res i) --Betti tables of duals

--other things to explore
deltas/fVector
deltas/hVector
deltas/isShellable

--example of making an exponent matrix
apply((duals_1)_*,i->exponentMatrix(i,2,3,ring (duals_1)))

--find all generators of the Alexander dual up to symmetry
netList listDualGens(L,2,2)

--find all facet orbits of the SR complex up to symmetry
netList listFacetGens(L,2,2)
	
	
	
