newPackage(
    "TropHyperplanes",
    Version => "1.1",
    Date => "March 1, 2023",
    Authors => {
	{Name => "Ayah Almousa", Email => "almou007@umn.edu", HomePage => ""},
	{Name => "Demetrios Case", Email => "", HomePage => ""}},
    Headline => "for computing monomial ideals associated to arrangements",
    Keywords => {""},
    DebuggingMode => true,
    Reload => True,
    PackageImports=>{"SimplicialComplexes"}
    )

--export {"hyperplaneArrangement"}
--export {"hyperplaneSideId"}
export {"fineCotype"}
export {"fineCotype2"}
export {"fineType"}
export {"fineType2"}
export {"weights"}
export {"getPolyRing"}
export {"isRegular"}
export {"isMonomial"}
--export {"weightedRing"}


getPolyRing = method()
getPolyRing (ZZ, ZZ, Matrix) := (m, n, A) -> (
  --use (symbol x);
  x := local x;
  -- 
  Q := ZZ/101[x_(1, 1)..x_(m, n), MonomialOrder=> {Weights=> flatten entries A}]; 
  return Q;   
)

-- inputs:  apex List of Reals
-- outputs: matrix representation of Tropical Hyperplane Arrangement
hyperplaneArrangement = method(TypicalValue => List)
hyperplaneArrangement List := List => apexes -> (
  if isTable apexes then transpose(
    matrix(apply(apexes, apex -> apply(apex, coordinate -> coordinate - last(apex))))
  ) 
  else {"NOT A VALID HYPERPLANE ARRANGEMENT"}
)


-- This is helper function that tests whether or not a point is contained within a k-sector of a single hyperplane
-- TODO: make this min/max adaptable
allLessOrEq = method()
allLessOrEq (ZZ, ZZ, List, List) := (it, akpk, apex, point) -> (
  if it == 0 then (
    (akpk >= apex#it - point#it)
  )
  else (
    (akpk >= apex#it - point#it) and allLessOrEq(it - 1, akpk, apex, point)
  )
)

-- inputs:  apex and a point
-- outputs: the k-th sector where the point lies
hyperplaneSideId = method()
hyperplaneSideId (List, List) := (apex, point) -> (
  for k from 0 to (#apex - 1) do (
    if allLessOrEq(#apex - 1, apex#k - point#k, apex, point) then return (k + 1)
  )
)


-- inputs:  a matrix that contains weights used for computing the fine-type and -cotype ideals of a tropical hyperplane arrangement
-- outputs: a flattened version of this matrix. this doesn't do anything special but it's less to type :)
weights = method()
weights (Matrix) := (A) -> (
  flatten entries A  
)


-- inputs:  the number of columns, number of rows, and ambient ring of a generic matrix used in computing the fine-type and -cotype ideals of a tropical hyperplane arrangement
-- outputs: the generic matrix
genericMat = method()
genericMat (ZZ, ZZ, PolynomialRing) := (n,m,Q) -> (
  use Q;
  Mmut := mutableMatrix(Q,n,m);
  if #(gens Q) == n*m then (
   for i from 0 to n-1 do (
	for j from 0 to m-1 do (
	    Mmut_(i, j) = (gens Q)#(j + (i * m));
	);
   );
   return matrix Mmut;
  );
  --else ( "ERROR" );
)

-- inputs:  a matrix representing a tropical hyperplane arrangement
-- outputs: the fine cotype ideal of the hyperplane arrangement
fineCotype = method()
fineCotype (Matrix) := (A) -> (
  Q := getPolyRing(numRows(A), numColumns(A), A);
  use Q;
  return dual (monomialIdeal leadTerm minors(2, genericMat(numRows(A), numColumns(A), Q)));
)

-- inputs:  ring element
-- outputa: if the ring element is a monomial
isMonomial = method()
isMonomial (RingElement, Matrix) := (M, A) -> (
  Q := getPolyRing(numRows(A), numColumns(A), A);
  use Q;
  return M == (leadTerm M)
)

-- inputs:  a matrix representing a tropical hyperplane arrangement
-- outputs: the fine cotype ideal of the hyperplane arrangement
fineCotype2 = method()
fineCotype2 (Matrix) := (A) -> (
  Q := getPolyRing(numRows(A), numColumns(A), A);
  use Q;
  L := flatten entries leadTerm(1, minors(2, genericMat(numRows(A), numColumns(A), Q)));
  return dual (monomialIdeal select(L, (i -> i == leadTerm i)));
)

-- inputs:  a monomial, a ring generator, and an ambient ring
-- outputs: a boolean value corresponding to whether or not the ring generator is in the monomial
genInMonomial = method()
genInMonomial (RingElement, RingElement, PolynomialRing) := (E, G, Q) -> (
  use Q;
  return numerator(E / G) != E;
)

-- inputs:  a monomial and a polynomial ring
-- outputs: a list of ring generators contained in the monomial. For example, x_1*x_3 maps to {x_1, x_3}.
gensInMonomial = method()
gensInMonomial (RingElement, PolynomialRing) := (E, Q) -> (
  use Q;
  return select((gens Q), g -> genInMonomial(E, g, Q));
)

-- inputs:  an polynomial ring generator
-- outputs: the subscripts corresponding to the ring element. For example, x_(1,2) maps to {1, 2}
ringElementIndex = method()
ringElementIndex (RingElement, PolynomialRing, ZZ, ZZ) := (E, Q, m, n) -> (
  use Q;
  return {floor(index(E) / n) + 1, (index(E) % n) + 1}
  --return index(E);
)

-- inputs:  a list of lists of generators in facets of a simplicial complex, a polynomial ring, and a matrix
-- outputs: a list of 2-element lists that correspond to the respective index of each ring generator of each facet
monomialsToSubscriptLists = method()
monomialsToSubscriptLists (List, PolynomialRing, Matrix) := (mons, Q, A) -> (
  return apply(mons, mon -> apply(mon, ringGen -> ringElementIndex(ringGen, Q, numRows(A), numColumns(A))));
)

-- inputs:  a list of facets of a simplicial complex, a polynomial ring
-- outputs: a list of lists of generators in each facet of the simplicial complex
divideFacets = method()
divideFacets (List, PolynomialRing) := (L, Q) -> (
  use Q;
  return apply(L, facet -> gensInMonomial(facet, Q));
  --return apply(apply(L, facet -> gensInMonomial(facet, Q)), monomialAsList -> apply(monomialAsList, ringGenerator -> ringGenerator * 2));
)

-- inputs:  a list of genetors that correspond to a facet of a simplicial complex and the ambient polynomial ring
-- outputs: a hash table whose keys and entries are divided by the "components" of the products
facetComponents = method()
facetComponents (List, PolynomialRing) := (L, Q) -> (
  use Q;
  return apply(L, monomialIndexes -> partition((monomialIndex -> monomialIndex#1), monomialIndexes));    
)


-- inputs:  a hash table corresponding to factors of the minowski sum, the ambient polynomial ring, and the number of entires in the table
-- outputs: the cartesian product of the elements of each hash table entry
minowskiSumHelperHelper = method()
minowskiSumHelperHelper (HashTable, PolynomialRing, ZZ) := (H, Q, i) -> (
  use Q;
  if i == 1 then (
    return set(H#i);
  )
  else (
    return set(H#i) ** minowskiSumHelperHelper(H, Q, i - 1);
  )
)

-- inputs:  a list of facets of a siplicial complex
-- outouts: the minowski sum of each component
minowskiSumHelper = method()
minowskiSumHelper (List, PolynomialRing) := (L, Q) -> (
  use Q;
  return apply(L, entryAsTable -> minowskiSumHelperHelper(entryAsTable, Q, #keys(entryAsTable)));
)

-- inputs:  a list of lists
-- outputs: the flattened list
flattenListofSets = method()
flattenListofSets (List) := (L) -> (
  return flatten apply(L, setOfIndexTuples -> toList(setOfIndexTuples));
)

-- inputs:  a list of ring generators and a polynomial ring
-- outputs: a monomial
collapse = method()
collapse (List, PolynomialRing) := (L, Q) -> (
  use Q;
  if #L == 1 then return L#0
  else (
    return L#0 * collapse(delete(L#0, L), Q)
  )
)

-- inputs:  a list of tuples representing generator indexes
-- outputs: the monomials with the corresponding indexes
getMonomialsFromTupleLists = method()
getMonomialsFromTupleLists (List, PolynomialRing, ZZ) := (L, Q, m) -> (
  use Q;
  return apply(apply(L, mon -> apply(mon, gen -> (gens Q)#(gen#1 - 1 + ((gen#0 - 1) * m)))), gensAsTuples -> collapse(toList gensAsTuples, Q))
  --
  -- (gens Q)#(j + (i * m))
)

-- inputs:  a list of nested tuples to be "unwound"
-- outputs: the "unwound" lists
tupleUnwind = method()
tupleUnwind (List) := (L) -> (
  return apply(L, tuple -> deepSplice tuple);
)

-- inputs:  a list of facets of a simplicial complex, the ambient polynomial ring, and the matrix associated with the corresponding tropical hyperplane arrangement
-- outputs: the corresponding regular subdivision
tropicalCayleyTrick = method()
tropicalCayleyTrick (List, PolynomialRing, Matrix) := (L, Q, A) -> (
  use Q;
  return ideal(unique(getMonomialsFromTupleLists(flattenListofSets(minowskiSumHelper(facetComponents(monomialsToSubscriptLists(divideFacets(L, Q), Q, A), Q), Q)), Q, numColumns(A))));
)

-- inputs:  a matrix representation of a tropical hyperplane arrangement and a polynomial ring used for computing the ideal
-- outputs: the fine-type deal of the tropical hyperplane arrangement
fineType = method()
fineType (Matrix) := (A) -> (
  Q := getPolyRing(numRows(A), numColumns(A), A);
  use Q;
  return tropicalCayleyTrick ((flatten (entries (facets (simplicialComplex monomialIdeal(leadTerm minors(2, genericMat(numRows(A), numColumns(A), Q))))))), Q, A)
  --return divideFacets ((flatten (entries (facets (simplicialComplex monomialIdeal(leadTerm minors(2, genericMat(numRows(A), numColumns(A), Q))))))), Q)
)


tropicalCayleyTrick2 = method()
tropicalCayleyTrick2 (List, PolynomialRing, Matrix) := (L, Q, A) -> (
  use Q;
  M := flattenListofSets(minowskiSumHelper(facetComponents(monomialsToSubscriptLists(divideFacets(L, Q), Q, A), Q), Q)), Q, numColumns(A);
  return ideal(unique(getMonomialsFromTupleLists((tupleUnwind M), Q, numColumns(A))));
  -- return tupleUnwind M
  -- return minowskiSumHelper(facetComponents(monomialsToSubscriptLists(divideFacets(L, Q), Q, A), Q), Q);
  -- return facetComponents(monomialsToSubscriptLists(divideFacets(L, Q), Q, A), Q), Q;
)

-- inputs:  a matrix representation of a tropical hyperplane arrangement and a polynomial ring used for computing the ideal
-- outputs: the fine-type deal of the tropical hyperplane arrangement
fineType2 = method()
fineType2 (Matrix) := (A) -> (
  Q := getPolyRing(numRows(A), numColumns(A), A);
  use Q;
  return tropicalCayleyTrick2 ((flatten (entries (facets (simplicialComplex monomialIdeal(leadTerm minors(2, genericMat(numRows(A), numColumns(A), Q))))))), Q, A)
  --return divideFacets ((flatten (entries (facets (simplicialComplex monomialIdeal(leadTerm minors(2, genericMat(numRows(A), numColumns(A), Q))))))), Q)
)


-- inputs:  a matrix representation of a tropical hyperplane arrangement
-- outputs: a boolean whose value indicates if the hyperplane arrangement given is reagular
isRegular = method()
isRegular (Matrix) := (A) -> (
  Q := getPolyRing(numRows(A), numColumns(A), A);
  use Q;
  return ideal(leadTerm(1, minors(2, genericMat(numRows(A), numColumns(A), Q)))) == monomialIdeal(leadTerm minors(2, genericMat(numRows(A), numColumns(A), Q)));
)


-*

beginDocumentation()

doc ///
 Node
  Key
   TropHyperplanes
  Headline
     an package for computing Tropical Hyperplane Arrangements
  Subnodes
    :weights
    :fineType
    :fineCotype
 Node
  Key
   (weights, Matrix)
   weights
  Headline
   a function that takes a matrix and produces a list of associated weights (not too complicated, just to shorten things up)
  Usage
   weights hyperplaneArrangementMatrix
  Inputs
   weights:
  Outputs
   :
    a list of associated weights
  Description
   Text
    Here we show an example.
   Example
    weights matrix{{0,0,4},{0,1,0},{0,3,1}}
 Node
  Key
   (fineType, Matrix, PolynomialRing)
   fineType
  Headline
   a function that takes a matrix and a polynomial ring and returns the associated fine type ideal
  Usage
   fineType(mat, polyRing)
  Inputs
   hyperplaneArrangement:
   polyRing:
  Outputs
   :
    the fine type ideal of the tropical hyperplane arrangement
 Node
  Key
   (fineCotype, Matrix, PolynomialRing)
   fineCotype
  Headline
   function that takes a matrix and a polynomial ring and returns the associated fine type ideal
  Usage
   fineCotype(mat, polyRing)
  Inputs
   hyperplaneArrangement:
   polyRing:
  Outputs
   :
    the fine cotype ideal of the tropical hyperplane arrangement
///

*-

end--

restart
uninstallPackage "TropHyperplanes"
restart
installPackage "TropHyperplanes"
restart
needsPackage "TropHyperplanes"
viewHelp TropHyperplanes


FIX INDEXING PROBLEM
WAIT FOR FURTHER INSTRUCTION W THE POLYNOMIAL RING
EXTEND THE CODE TO NOT JUST GENERIC ARRANGEMENTS!!!
THEN GENERATE RANDOEM MATRIX AND TO TESTS W TRANSPOSE
