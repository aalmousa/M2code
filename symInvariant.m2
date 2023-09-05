restart

needsPackage "SimplicialComplexes"
needsPackage "SimplicialDecomposability"
needsPackage "Posets"

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

--input M, an integer matrix
--outputs a monomial m with exponent matrix M
expMatrixToMonomial := (M) -> (
    c := numrows M;
    n := numcols M;
    Q := ZZ/101[x_(1,1)..x_(c,n)];
    L := substitute(1,Q);
    for i from 0 to n-1 do (
	for j from 0 to c-1 do (
	    L = L*x_(j+1,i+1)^(M_(j,i));
	    );
	);
    L
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
	
	
--------------------------------
--**Code for inequalities**
--------------------------------	

--input: S, a string of 0s and 1s
--output: the complement of S

comp := (S) -> (
    concatenate apply(characters S, i->toString(mod((value i)+1,2)))
    )

--input:
    --c: number of rows in generating matrices
    --A = {aa^1..aa^k}
    	--a list of lists aa^i in \NN^{2^[c]}
	--each aa^i gives some k^i_S where S is a subset of [c]
	--ordering of entries of aa^i is lexicographic, e.g.
	    --000, 001, 010, 011, 100, 101, 110, 111
	
--output: a list of inequalities in a format that can be input into Sage
c=2
A = {{0,1,1,2},{1,2,2,0}}
ADineqs:= (c,A) -> (
    B := booleanLattice c;
    G := B.GroundSet;
    N := antichains B; -- if c=2, #N = 20
    Js := toList (set N) ^** #A; --ugh if #A is 2, this is already 400
    polyhedra = new MutableList;
    
    for J in Js do(
        ineqs = new MutableList;
        for i from 0 to #A-1 do (
            P = flatten apply(J_i, j -> position(G, l-> l==j)); --positions of k's
            K = sum((A_i)_P)+1; --sum of k's
            comps = apply(J_i, j -> comp j); --complements list
            Pc = flatten apply(comps, j -> position(G,l->l==j)); --positions of comps
            V = new MutableList from 2^c:0;
            for k from 0 to #Pc-1 do (V#(Pc_k) = -1);
            ineqs#(#ineqs) = toSequence({K}|new List from V);
            );
        ineqString = toString ineqs;
        polyhedra#(#polyhedra) = "Polyhedron(ieqs=["|substring(1,#ineqString-2)|"])";
        );
    toList polyhedra
    )
	
----------------------------------------------------------------------

---------------------
--**Demo of code**
---------------------

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

----------------------------
--Example: 1 orbit
----------------------------
-*
1 1 0      
1 0 1 
*-

Q = ZZ/101[x_(1,1)..x_(2,3)];
I = ideal(x_(1,1)*x_(1,2)*x_(2,1)*x_(2,3));
L = (idealSym(I,2,3,5))/monomialIdeal;

netList listDualGens(L,2,3)
netList listFacetGens(L,2,3)

------------------------------------
--Examples: 2-orbits, coprime
------------------------------------

-*
Simplest 2-orbit coprime case:

1 1     0 0
0 0 and 1 1

*-

Q = ZZ/101[x_(1,1)..x_(2,2)];
I1 = ideal(x_(1,1)*x_(1,2));
I2 = ideal(x_(2,1)*x_(2,2));
I = I1 + I2
L1 = (idealSym(I1,2,2,5))/monomialIdeal
L2 = (idealSym(I2,2,2,5))/monomialIdeal
L = (idealSym(I,2,2,5))/monomialIdeal

--List the Alexander dual generators for L1, L2, and L
netList {listDualGens(L1,2,2), listDualGens(L2,2,2), listDualGens(L,2,2)}
-
--List the facet orbit generators for L1, L2, and L
netList {listFacetGens(L1,2,2), listFacetGens(L2,2,2), listFacetGens(L,2,2)}

-------------------------------------------
-- Still c=2, 2 coprime orbits
-- What if the number of columns differs?
-------------------------------------------

-*

1 1     0 0 0
0 0 and 1 1 1

*-

Q = ZZ/101[x_(1,1)..x_(2,3)];
I1 = ideal(x_(1,1)*x_(1,2));
I2 = ideal(x_(2,1)*x_(2,2)*x_(2,3));
I = I1 + I2;
L1 = (idealSym(I1,2,3,6))/monomialIdeal;
L2 = (idealSym(I2,2,3,6))/monomialIdeal;
L = (idealSym(I,2,3,6))/monomialIdeal;


netList {listDualGens(L1,2,3), listDualGens(L2,2,3), listDualGens(L,2,3)}
netList {listFacetGens(L1,2,3), listFacetGens(L2,2,3), listFacetGens(L,2,3)}

-*

1 1     0 0 0 0
0 0 and 1 1 1 1

*-

Q = ZZ/101[x_(1,1)..x_(2,4)];
I1 = ideal(x_(1,1)*x_(1,2));
I2 = ideal(x_(2,1)*x_(2,2)*x_(2,3)*x_(2,4));
I = I1 + I2;
L1 = (idealSym(I1,2,4,6))/monomialIdeal;
L2 = (idealSym(I2,2,4,6))/monomialIdeal;
L = (idealSym(I,2,4,6))/monomialIdeal;


netList {listDualGens(L1,2,4), listDualGens(L2,2,4), listDualGens(L,2,4)}

netList {listFacetGens(L1,2,4), listFacetGens(L2,2,4), listFacetGens(L,2,4)}




------------------------------------

-*

1 1     0 0 0
0 0 and 1 1 1

*-

Q = ZZ/101[x_(1,1)..x_(2,3)];
I1 = ideal(x_(1,1)*x_(1,2));
I2 = ideal(x_(2,1)*x_(2,2)*x_(2,3));
I = I1 + I2;
L1 = (idealSym(I1,2,3,6))/monomialIdeal;
L2 = (idealSym(I2,2,3,6))/monomialIdeal;
L = (idealSym(I,2,3,6))/monomialIdeal;


netList {listDualGens(L1,2,3), listDualGens(L2,2,3), listDualGens(L,2,3)}
netList {listFacetGens(L1,2,3), listFacetGens(L2,2,3), listFacetGens(L,2,3)}

-*

1 1 1     0 0 0 0
0 0 0 and 1 1 1 1

*-

Q = ZZ/101[x_(1,1)..x_(2,4)];
I1 = ideal(x_(1,1)*x_(1,2)*x_(1,3));
I2 = ideal(x_(2,1)*x_(2,2)*x_(2,3)*x_(2,4));
I = I1 + I2;
L1 = (idealSym(I1,2,4,6))/monomialIdeal;
L2 = (idealSym(I2,2,4,6))/monomialIdeal;
L = (idealSym(I,2,4,6))/monomialIdeal;


netList {listDualGens(L1,2,4), listDualGens(L2,2,4), listDualGens(L,2,4)}

netList {listFacetGens(L1,2,4), listFacetGens(L2,2,4), listFacetGens(L,2,4)}


-----------------------------------
--A c=3, 2 coprime orbits example.
-----------------------------------
-*

1 1       0 0
0 0  and  1 1
0 0       1 1

*-

Q = ZZ/101[x_(1,1)..x_(3,2)];
I1 = ideal(x_(1,1)*x_(1,2));
I2 = ideal(x_(2,1)*x_(2,2)*x_(3,1)*x_(3,2));
I = I1 + I2;
L1 = (idealSym(I1,3,2,5))/monomialIdeal;
L2 = (idealSym(I2,3,2,5))/monomialIdeal;
L = (idealSym(I,3,2,5))/monomialIdeal;


netList {listDualGens(L1,3,2), listDualGens(L2,3,2), listDualGens(L,3,2)}

netList {listFacetGens(L1,3,2), listFacetGens(L2,3,2), listFacetGens(L,3,2)}


-*

1 1      0 0 1
1 0  and 1 1 1
1 0      1 1 0

*-

Q = ZZ/101[x_(1,1)..x_(3,3)];
I1 = ideal(x_(1,1)*x_(1,2)*x_(2,1)*x_(3,1));
I2 = ideal(x_(1,3)*x_(2,1)*x_(2,2)*x_(2,3)*x_(3,1)*x_(3,2));
I = I1 + I2;
L1 = (idealSym(I1,3,3,5))/monomialIdeal;
L2 = (idealSym(I2,3,3,5))/monomialIdeal;
L = (idealSym(I,3,3,5))/monomialIdeal;


netList {listDualGens(L1,3,3), listDualGens(L2,3,3), listDualGens(L,3,3)}

netList {listFacetGens(L1,3,2), listFacetGens(L2,3,2), listFacetGens(L,3,2)}

-*
1 1 1 1 1 0 0 1 0 0
1 1 1 1 0 1 1 0 1 0
1 1 0 0 1 1 1 0 0 1

and

1 1 1 1 0 1 1 0 0 0 0
1 1 0 0 1 0 0 1 1 0 0
1 0 1 1 1 0 0 0 0 1 1

*-

M1 = matrix{{1,1,1,1,1,0,0,1,0,0},{1,1,1,1,0,1,1,0,1,0},{1,1,0,0,1,1,1,0,0,1}};
m1 = expMatrixToMonomial(M1)
M2 = matrix{{1,1,1,1,0,1,1,0,0,0,0},{1,1,0,0,1,0,0,1,1,0,0},{1,0,1,1,1,0,0,0,0,1,1}};
m2 = expMatrixToMonomial(M2)
m1 = sub(m1,ring m2)
I1 = ideal m1;
I2 = ideal m2;
I = I1 + I2;
L = (idealSym(I,3,11,11))

---------------

