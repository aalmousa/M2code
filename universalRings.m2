needsPackage "SimplicialComplexes"
needsPackage "SimplicialPosets"
needsPackage "Posets"

ASL := (Delta) -> (
    facesOpp := dual facePoset Delta; --flip face poset
    G := drop(facesOpp.GroundSet,1); --delete empty set from ground set
    numFaces := (sum values fVector Delta)-1;
    R := drop(facesOpp.Relations,numFaces); --delete relations containing empty set
    P := poset(G,R); --poset we want to put the ASL on
    incompPairs := antichains(P,2);
    Q := ZZ/101[apply(G,i->u_i), Degrees => apply(G,i-> first degree (product i))]; --new polynomial ring with faces as variables
    L := new MutableList;
    for i from 0 to #incompPairs-1 do (
	if joinExists(P,incompPairs_i_0, incompPairs_i_1) and meetExists(P, incompPairs_i_0, incompPairs_i_1) then
	    L#i = u_(incompPairs_i_0)*u_(incompPairs_i_1) - u_((posetJoin(P,incompPairs_i_0, incompPairs_i_1))_0)*u_((posetMeet(P, incompPairs_i_0, incompPairs_i_1))_0)
	else (
	    if not(joinExists(P,incompPairs_i_0, incompPairs_i_1)) and meetExists(P, incompPairs_i_0, incompPairs_i_1) then (
	        L#i =  u_(incompPairs_i_0)*u_(incompPairs_i_1) - u_((posetMeet(P, incompPairs_i_0, incompPairs_i_1))_0))
	    else L#i = u_(incompPairs_i_0)*u_(incompPairs_i_1);
	);
	);
    ideal toList L
    );

discreteASL := (Delta) -> (
        facesOpp := dual facePoset Delta; --flip face poset
    G := drop(facesOpp.GroundSet,1); --delete empty set from ground set
    numFaces := (sum values fVector Delta)-1;
    R := drop(facesOpp.Relations,numFaces); --delete relations containing empty set
    P := poset(G,R); --poset we want to put the ASL on
    incompPairs := antichains(P,2);
    Q := ZZ/101[apply(G,i->u_i), Degrees => apply(G,i-> first degree (product i))]; --new polynomial ring with faces as variables
    L := new MutableList;
    for i from 0 to #incompPairs-1 do (
 	L#i = u_(incompPairs_i_0)*u_(incompPairs_i_1);
	);
    ideal toList L
    );

universalRing := (Delta) -> (
    I := ASL(Delta);
    V := flatten entries vars (ring I);
    theta := new MutableList;
    for i from 1 to (dim Delta+1) do (
	K = select(V, j-> degree j == {i});
	theta#(#theta) = sum K;
	);
      phi := map(ring I, ZZ/101[z_1..z_(dim Delta+1), Degrees=>toList(1..dim Delta+1)], matrix{toList theta});
      pushForward(phi, comodule I)
    );
    
universalRingInit := (Delta) -> (
    I := discreteASL(Delta);
    V := flatten entries vars (ring I);
    theta := new MutableList;
    for i from 1 to (dim Delta+1) do (
	K = select(V, j-> degree j == {i});
	theta#(#theta) = sum K;
	);
      phi := map(ring I, ZZ/101[z_1..z_(dim Delta+1), Degrees=>toList(1..dim Delta+1)], matrix{toList theta});
      pushForward(phi, comodule I)
    );

--Delta a simplicial complex
--L a list partitioning the vertices of Delta into color classes
colorfulRing := (Delta, L) -> (
    I := ideal Delta;
    k := ZZ/101;
    A := k[z_1..z_(#L), DegreeRank => #L];
    degs := degrees A;
    numColors := apply(L, i->#i);
    longDegs := splice(for i from 0 to #numColors-1 list ((numColors_i) : degs_i));
    R := k[flatten L, Degrees=>longDegs];
    theta = new MutableList;
    for i from 0 to #L-1 do (
	theta#(#theta) = sum L_i;
	);
    phi := map(R, A, sub(matrix{toList theta},R));
    pushForward(phi, comodule(sub(I,R)))
    );

----------------------------
S = ZZ/101[a..h];
Delta = simplicialComplex{a*b*c,b*d*e,e*f*g, c*g*h};
universalRing Delta --has linear resolution, which is already weird
universalRingInit Delta --one less entry in column for (1,1,1), suspicious

--let's homogenize and see if t's appear in the presenting matrix
I = ASL Delta;
degs = deepSplice{8:7,12:12,4:15,1};
R = ZZ/101[flatten entries vars ring I, t, Degrees=> degs]; --new ring with t
J = homogenize(sub(I,R),t);
use R
M = matrix{{
        u_{a}+ u_{b} + u_{c} + u_{d} + u_{e} + u_{f} + u_{g} + u_{h},
        u_{a,b} + u_{a,c} + u_{b,c} + u_{b,d} + u_{b,e} + u_{c,g} + u_{c,h} + u_{d,e} + u_{e,f} + u_{e,g} + u_{f,g} + u_{g,h},
        u_{a,b,c} + u_{b,d,e} + u_{e,f,g} + u_{c,g,h},
        t
        }}

phi = map(R, ZZ/101[z_1,z_2,z_3,t, Degrees => {7,12,15,1}],M)
pushForward(phi, comodule J) --there is a t^4 in the last column!!


------------------------------------

-------------------------------------------------------------
-------------------------------------------------------------
**SIMPLICIAL POSET EXAMPLES**
-------------------------------------------------------------
-------------------------------------------------------------

----------------------------------------------
--Example 1: 2 facets, double edge ab
----------------------------------------------

--Creating poset
G = {a,b,c,d,ab1,ab2,ac,bc,ad,bd,F1,F2};
R = {
    {a,ab1},{a,ab2},{a,ac},{a,ad},
    {b,ab1},{b,ab2},{b,bc},{b,bd},
    {c,ac},{c,bc},
    {d,ad},{d,bd},
    {ab1,F1},{ac,F1,{bc,F1},
    {ab2,F2},{ad,F2},{bd,F2}};
P = poset(G,R);

I = stanleyPosetIdeal adjoinMin(P); --gives ideal for k[P]

Q = newRing(ring I, Degrees => {1,1,1,1,2,2,2,2,2,2,3,3,0});
I = sub(I,Q);
V = flatten entries vars (ring I);
    theta = new MutableList;
    for i from 1 to 3 do (
	K = select(V, j-> degree j == {i});
	theta#(#theta) = sum K;
	);
 M = sub(matrix{toList theta},Q)
 
 
 phi = map(Q, QQ[z_1..z_3, Degrees=>toList(1,2,3)], M);
 pushForward(phi, comodule I) --resolution of k[P] over A
 --notice: quadratic entry in second column
 --this is the same syzygy as the one with the triangular hole
 
--homogenizing the above this example
degs = deepSplice{4:3,6:4,2:3,0,1}; --setting up weight vector
D = {3,4,3}
R = QQ[flatten entries vars ring I, t, Degrees=> degs]; --new ring with t
J = homogenize(sub(I,R),t); --homogenization of k[P]

V = flatten entries vars (ring J);
theta = {V_0 + V_1 + V_2 + V_3,
    V_4 + V_5 + V_6 + V_7 + V_8 + V_9,
    V_10 + V_11,
    V_13}
M = sub(matrix{toList theta},R) --building map

phi = map(R, QQ[z_1,z_2,z_3,t, Degrees => {3,4,3,1}], M)

pushForward(phi, comodule J) --presents homogenization over k[Theta,t]

-------------------------------------------------------------------------------------

-----------------------------------------------------
--Example 2: 3 facets, triple edge a-b
-----------------------------------------------------

--Creating poset
G = {a,b,c,d,e,ab1,ab2, ab3,ac,bc,ad,bd,ae,be,F1,F2,F3};
R = {
    {a,ab1},{a,ab2},{a,ab3},{a,ac},{a,ad},{a,ae},
    {b,ab1},{b,ab2},{b,ab3},{b,bc},{b,bd},{b,be},
    {c,ac},{c,bc},
    {d,ad},{d,bd},
    {e,ae},{e,be},
    {ab1,F1},{ac,F1},{bc,F1},
    {ab2,F2},{ad,F2},{bd,F2},
    {ab3,F3},{ae,F3},{be,F3}
    };
P = poset(G,R);

I = stanleyPosetIdeal adjoinMin(P); --gives ideal for k[P]

Q = newRing(ring I, Degrees => deepSplice{5:1,9:2,3:3,0});
I = sub(I,Q);
V = flatten entries vars (ring I);
theta = new MutableList;
for i from 1 to 3 do (
    K = select(V, j-> degree j == {i});
    theta#(#theta) = sum K;
    );
M = sub(matrix{toList theta},Q)

phi = map(Q, QQ[z_1..z_3, Degrees=>toList(1,2,3)], M);
pushForward(phi, comodule I) --resolution of k[P] over A

--homogenizing the above this example
degs = deepSplice{5:4,9:6,3:6,0,1}; --setting up weight vector
D = {4,6,6}
R = QQ[flatten entries vars ring I, t, Degrees=> degs]; --new ring with t
J = homogenize(sub(I,R),t); --homogenization of k[P]

V = flatten entries vars (ring J);
theta = {V_0 + V_1 + V_2 + V_3 + V_4,
    V_5 + V_6 + V_7 + V_8 + V_9 + V_10 + V_11 + V_12 + V_13,
    V_14 + V_15 + V_16,
    V_18}
M = sub(matrix{toList theta},R) --building map

phi = map(R, QQ[z_1,z_2,z_3,t, Degrees => {4,6,6,1}], M)

pushForward(phi, comodule J) --presents homogenization over k[Theta,t]

-------------------------------------------------------------------------------------------
-------------------------------------------------
--Example 3: abc a double face, abd a face
-------------------------------------------------

--Creating poset
G = {a,b,c,d,ab1,ab2,ab3,ac,bc,ad,bd,abc1,abc2,abd}
R = {
    {a,ab1},{a,ab2},{a,ab3},{a,ac},{a,ad},
    {b,ab1},{b,ab2},{b,ab3},{b,bc},{b,bd},
    {c,ac},{c,bc},
    {d,ad},{d,bd},
    {ab1,abc1},{ac,abc1},{bc,abc1},
    {ab2,abc2},{ac,abc2},{bc,abc2},
    {ab3,abd},{ad,abd},{bd,abd}
    };
P = poset(G,R);

I = stanleyPosetIdeal adjoinMin(P); --gives ideal for k[P]

Q = newRing(ring I, Degrees => deepSplice{4:1,7:2,3:3,0});
I = sub(I,Q);
V = flatten entries vars (ring I);
theta = new MutableList;
for i from 1 to 3 do (
    K = select(V, j-> degree j == {i});
    theta#(#theta) = sum K;
    );
M = sub(matrix{toList theta},Q)

phi = map(Q, QQ[z_1..z_3, Degrees=>toList(1,2,3)], M);
pushForward(phi, comodule I) --resolution of k[P] over A

--homogenizing the above this example
degs = deepSplice{4:3,7:4,3:3,0,1}; --setting up weight vector
D = {3,4,3}
R = QQ[flatten entries vars ring I, t, Degrees=> degs]; --new ring with t
J = homogenize(sub(I,R),t); --homogenization of k[P]

V = flatten entries vars (ring J);
theta = {V_0 + V_1 + V_2 + V_3,
    V_4 + V_5 + V_6 + V_7 + V_8 + V_9 + V_10,
    V_11 + V_12 + V_13,
    V_15}
M = sub(matrix{toList theta},R) --building map

phi = map(R, QQ[z_1,z_2,z_3,t, Degrees => {3,4,3,1}], M)

pushForward(phi, comodule J) --presents homogenization over k[Theta,t]
--------------------------------------------------------------------------------------------------------------

-------------------------------------
--Example 4: 4 facets, 2 holes
-------------------------------------

--Creating poset
G = {a,b,c,d,e,ab1,ab2,bc1,bc2,ad,bd,cd,ae,be,ce, abd, abe, bcd, bce}
R = {
    {a,ab1},{a,ab2},{a,ad},{a,ae},
    {b,ab1},{b,ab2},{b,bc1},{b,bc2},{b,bd},{b,be},
    {c,bc1},{c,bc2},{c,cd},{c,ce},
    {d,ad},{d,bd},{d,cd},
    {e,ae},{e,be},{e,ce},
    {ab1,abd},{ad,abd},{bd,abd},
    {ab2,abe},{ae,abe},{be,abe},
    {bc1,bcd},{bd,bcd},{cd,bcd},
    {bc2,bce},{be,bce},{ce,bce}
    };
P = poset(G,R);

I = stanleyPosetIdeal adjoinMin(P); --gives ideal for k[P]

Q = newRing(ring I, Degrees => deepSplice{5:1,10:2,4:3,0});
I = sub(I,Q);
V = flatten entries vars (ring I);
theta = new MutableList;
for i from 1 to 3 do (
    K = select(V, j-> degree j == {i});
    theta#(#theta) = sum K;
    );
M = sub(matrix{toList theta},Q)

phi = map(Q, QQ[z_1..z_3, Degrees=>toList(1,2,3)], M);
pushForward(phi, comodule I) --resolution of k[P] over A

--homogenizing the above this example
degs = deepSplice{5:4,10:6,4:6,0,1}; --setting up weight vector
D = {4,6,6}
R = QQ[flatten entries vars ring I, t, Degrees=> degs]; --new ring with t
J = homogenize(sub(I,R),t); --homogenization of k[P]

V = flatten entries vars (ring J);
theta = {V_0 + V_1 + V_2 + V_3 +V_4,
    V_5 + V_6 + V_7 + V_8 + V_9 + V_10 + V_11 + V_12 + V_13 + V_14,
    V_15 + V_16 + V_17 + V_18,
    V_20}
M = sub(matrix{toList theta},R) --building map

phi = map(R, QQ[z_1,z_2,z_3,t, Degrees => {4,6,6,1}], M)

pushForward(phi, comodule J) --presents homogenization over k[Theta,t]
--the presentation it gives originally isn't minimal (it has an extra column), so we'll res it to make it minimal
F = (res oo).dd

--Below I tried doing some column operations to make this matrix nicer
--it actually doesn't help much
M = mutableMatrix F_1
columnAdd(M,1,-1,2)
columnAdd(M,1,-z_1,0)

