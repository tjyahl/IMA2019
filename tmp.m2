restart
needsPackage "ToricMaps";

FF1 = hirzebruchSurface 1;
R = ring FF1
PP2 = normalToricVariety( {{1,0},{0,-1},{-1,1}}, {{0,1},{1,2},{0,2}})
isWellDefined PP2
S = ring PP2;
f = map(PP2,FF1, 1)
isWellDefined f

inducedMap ToricMap := RingMap => opts -> f -> (
    R := ring source f;
    Y := target f;
    if not isSmooth Y then error "-- expected the target variety to be smooth";
    S := ring Y;
    map(R, S, apply(numgens S, i -> (
		exps := entries pullback(f, Y_i);
		product(numgens R, j -> R_j^(exps#j))
	    )))
    )

classGroup ToricMap := Matrix => f -> (
    X := source f;
    Y := target f;
    if not isSmooth Y then error "-- expected the target variety to be smooth";
    divisorMap := map(weilDivisorGroup X, weilDivisorGroup Y,
	transpose matrix apply(# rays Y, i -> entries pullback (f, Y_i))
	);
    transpose ((transpose (fromWDivToCl(X) * divisorMap)) // transpose fromWDivToCl(Y) )
    )

classGroup f
X = source f
Y = target f
weilDivisorGroup Y
weilDivisorGroup X
map(weilDivisorGroup X, weilDivisorGroup Y, transpose matrix apply(# rays Y, i -> entries pullback (f, Y_i)))
g = inducedMap f
ker g

methods inducedMap
code (inducedMap, ChainComplex, ChainComplex)

R = ring FF1
S = ring PP2
g = map(R, S, apply(numgens S, i -> (
	exps := entries pullback(f, PP2_i);
	<< exps << endl;
	product(numgens R, j -> R_j^(exps#j)))))
isWellDefined g
rays PP2
saturate (g ** S^1/ideal(S_0,S_1), ideal R)
saturate (g ** S^1/ideal(S_0,S_2), ideal R)
saturate (g ** S^1/ideal(S_1,S_2), ideal R)

code (symbol **, RingMap, Module)

g ** ideal(S_0, S_1)
pullback(f, PP2_1)
pullback(f, PP2_2)

saturate(ideal(R_0 * R_1, R_1* R_2), ideal FF1)
saturate(ideal(R_3, R_1* R_2), ideal FF1)
ideal R

methods symbol ^**
code o3#12

g = map(ring X, ring Y, {R_0 * R_1, R_3, R_1*R_2})
degree g
degrees (g ** S^2)

InducedToricMap = new Type of HashTable
ToricMap ^* := InducedToricMap =>

ToricMap ^** ToricDivisor := ToricDivisor => (f, D) -> pullback(f,D)
f ^**

ToricMap ^* := Function => f -> (X -> pullback(f,X))

methods map
induc
restart
needsPackage "ToricMaps";
PP1 = toricProjectiveSpace 1
PP2 = toricProjectiveSpace 2

f = map(PP2, PP1, matrix{{1},{2}})
isWellDefined f
pullback(f,PP2_0)
imageCone


code (pullback, ToricMap, ToricDivisor)

imageRho :=
maxConesInTarget = max target f
for sigma in maxConesInTarget list (
    outerNormals(target f, sigma))

f = map(PP2, PP1, matrix{{1},{1}})
isWellDefined f
pullback(f,PP2_0)
imageCone
(f ^*) (PP2_0)
PP2_0
f^* (PP2_0)
break
pullback(f, PP2_0)
maxconeindex
break
showStructure RingMap
