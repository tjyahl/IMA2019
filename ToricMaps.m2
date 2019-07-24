newPackage(
  "ToricMaps",
  AuxiliaryFiles => false,
  Version => "0.1",
  Date => "19 July 2017",
  Authors => {
      {
      Name => "Chris Eur", 
      Email => "chrisweur@gmail.com", 
      HomePage => "https://math.berkeley.edu/~ceur"},
      {
      Name => "Justin Chen", 
      Email => "jchen@math.berkeley.edu", 
      HomePage => "https://math.berkeley.edu/~jchen"},
      {
      Name => "Gregory G. Smith", 
      Email => "ggsmith@mast.queensu.ca", 
      HomePage => "http://www.mast.queensu.ca/~ggsmith"}
      },
  Headline => "routines for working with toric morphisms",
  PackageExports => {
      "NormalToricVarieties"
  },
  PackageImports => {
      "NormalToricVarieties",
      "FourierMotzkin"
  },
  DebuggingMode => true,
  Reload => true
)

export {
    "ToricMap",
    "isFibration",
    "outerNormals",
    "isProper"    
}


------------------------------------------------------------------------------
-- toric morphisms


ToricMap = new Type of HashTable
ToricMap.synonym = "toric map"
source ToricMap := NormalToricVariety => f -> f.source
target ToricMap := NormalToricVariety => f -> f.target
matrix ToricMap := Matrix => opts -> f -> f.matrix

net ToricMap := f -> net matrix f
ToricMap#{Standard,AfterPrint} = ToricMap#{Standard,AfterNoPrint} = f -> (
  << endl;				  -- double space
  << concatenate(interpreterDepth:"o") << lineNumber << " : ToricMap ";
  << net target f << " <--- " << net source f << endl;)

map(NormalToricVariety, NormalToricVariety, Matrix) := ToricMap => opts -> (Y,
  X,A) -> (
  if ring A =!= ZZ then error "expected an integer matrix";
  if rank source A != dim X then error ("expected source to be the lattice " |
    "of one-parameter subgroups in " | toString X);
  if rank target A != dim Y then error ("expected target to be the lattice " |
    "of one-parameter subgroups in " | toString Y);  
  new ToricMap from {
    symbol source => X,
    symbol target => Y,
    symbol matrix => A,
    symbol cache => new CacheTable})

map(NormalToricVariety, NormalToricVariety, ZZ) := ToricMap => opts -> (Y,
  X,i) -> (
  m := dim Y;
  n := dim X;
  if i === 0 then return map(Y,X, map(ZZ^m, ZZ^n, 0))
  else if m === n then return map(Y,X,map(ZZ^m, ZZ^n, i))
  else error "expect 0, or source and target to have same dimension")

NormalToricVariety#id = X -> map(X,X,1)

- ToricMap := ToricMap => f -> new ToricMap from {
  symbol source => source f,
  symbol target => target f,
  symbol matrix => - matrix f,
  symbol cache => new CacheTable}

ZZ * ToricMap := ToricMap => (r,f) -> new ToricMap from {
  symbol source => source f,
  symbol target => target f,
  symbol matrix => r * matrix f,
  symbol cache => new CacheTable}

ToricMap * ToricMap := ToricMap => (g,f) -> (
  if target f =!= source g then error "expected composable maps";
  new ToricMap from {
    symbol source => source f,
    symbol target => target g,
    symbol matrix => (matrix g) * (matrix f),
    symbol cache => new CacheTable})

-- local method; produces the outer normal vectors for each max cone
-- at the moment exported for dubugging purposes
outerNormals = method()
outerNormals (NormalToricVariety,List) := Matrix => (X,sigma) -> (
  if not X.cache.?outerNormals then (
    X.cache.outerNormals = new MutableHashTable);
  if not X.cache.outerNormals#?sigma then (
    V := transpose matrix rays X;
    D := fourierMotzkin V_sigma;
    if D#1 == 0 then X.cache.outerNormals#sigma = transpose D#0 else X.cache.outerNormals#sigma = transpose (D#0 | D#1 | -D#1));
  return X.cache.outerNormals#sigma)



isWellDefined ToricMap := Boolean => f -> (
    -- CHECK DATA STRUCTURE
    -- check keys
    K := keys f;
    expectedKeys := set{ symbol source, symbol target, symbol matrix, symbol cache};
    if set K =!= expectedKeys then (
	if debugLevel > 0 then (
	    added := toList(K - expectedKeys);
	    missing := toList(expectedKeys - K);
	    if #added > 0 then 
	        << "-- unexpected key(s): " << toString added << endl;
	    if #missing > 0 then 
	        << "-- missing keys(s): " << toString missing << endl);
    	return false);
    --Check types
    if not instance(f.source, NormalToricVariety) then (
	if debugLevel > 0 then (
	    << "-- expected `source' to be a NormalToricVariety" << endl);
	return false);
    if not instance(f.target, NormalToricVariety) then (
	if debugLevel > 0 then (
	    << "-- expected `target' to be a NormalToricVariety" << endl);
	return false);
    if not instance(f.matrix, Matrix) then (
	if debugLevel > 0 then (
	    << "-- expected `matrix' to be a Matrix" << endl);
	return false);
    if ring matrix f =!= ZZ then (
    	if debugLevel > 0 then (
	    << "-- expected `matrix' over the integers" << endl);
	return false);	 
    if not instance(f.cache, CacheTable) then (
    	if debugLevel > 0 then (
	    << "-- expected `f.cache' to be a CacheTable" << endl);
    	return false);
    --Check mathematical structure
    X := source f;
    Y := target f;
    A := matrix f;
    if rank source A =!= dim X then (
    	if debugLevel > 0 then (
	    << "-- expected number of columns of the matrix to equal the dimension of the source variety");
	return false);
    if rank target A =!= dim Y then (
    	if debugLevel > 0 then (
	    << "-- expected number of rows of the matrix to equal the dimension of the target variety");
	return false);
    V := transpose matrix rays X;
    if not all(max X, sigma -> any(max Y, 
      	tau -> all(flatten entries ( outerNormals(Y, tau) * A * V_sigma), 
	i -> i <= 0))) then (
    	if debugLevel > 0 then (
	    << "-- expected image of each maximal cone to be contained in some maximal cone");
	return false);
    true
)



isProper = method()
isProper ToricMap := Boolean => f -> (
    if not isWellDefined f then << "the map is not well-defined!" << return false; -- check that f is well-defined first
    X := source f;
    Y := target f;
    if isComplete X then return true;
    if (isComplete Y and not isComplete X) then return false;
    A := matrix f;
    rayMatrixX := transpose matrix rays X; -- rays of X in columns
    rayMatrixY := transpose matrix rays Y; -- rays of Y in columns
    -- make a hash table whose keys are max cones in Y and values are max cones in X mapping into them
    coneTable := new MutableHashTable;
    for sigma in max X do (
	for tau in max Y do ( 
      	if all(flatten entries (outerNormals(Y, tau) * A * rayMatrixX_sigma), i -> i <= 0) then (
	    if not coneTable#?tau then coneTable#tau = {sigma}
	    else coneTable#tau = coneTable#tau|{sigma}
	    )
	)
    );
    K := mingens ker A;
    volA := max flatten entries mingens minors(rank A, A);
    for tau in max Y do (
    	indicesOverTau := unique flatten coneTable#tau; -- indices of rays in X over tau in Y
	raysOverTau := entries transpose rayMatrixX_indicesOverTau; -- rays in X over tau in Y
	conesOverTau := apply(coneTable#tau, sigma -> apply(sigma, i -> position(indicesOverTau, j -> j===i)));
	varietyOverTau := normalToricVariety(raysOverTau, conesOverTau); 
 	-- compute the rays of image(A) intersect tau
	raysTauCapImA := first fourierMotzkin ( (transpose outerNormals(Y,tau)) , last fourierMotzkin (A | -A) );
	liftTau := (volA*raysTauCapImA)//A | K | -K; -- volA is multiplied since over ZZ not QQ
	--first test whether if any of max cones in X over tau are of dimension less than liftTau
	if #orbits(varietyOverTau, dim X - rank liftTau) =!= #conesOverTau then return false;
	--the codimension in dim X of boundaries of liftTau is dim X - rank liftTau +1
	boundaries := select(orbits(varietyOverTau,dim X - rank liftTau + 1), C ->  #select(max varietyOverTau, sig -> isSubset(C,sig))<2);	
	for C in boundaries do (
		supportHyperplanes := first fourierMotzkin liftTau;
		if all(numcols supportHyperplanes, i -> #delete(0, flatten entries ((matrix rays varietyOverTau)^C * supportHyperplanes_i)) > 0) then return false;
	);
    );
    true
)


isFibration = method()
isFibration ToricMap := Boolean => f -> 1 == minors(dim target f, matrix f)

isSurjective ToricMap := Boolean => f -> rank matrix f == dim target f

-- THIS METHOD IS NOT EXPORTED.  Given a toric divisor which is assumed to be
-- Cartier, this method returns the characters on each maximal cone which
-- determine the Cartier divisor.
cartierCoefficients = method ()
cartierCoefficients ToricDivisor := List => D -> (
    X := variety D;
    rayMatrix := matrix rays X;
    coeffs := transpose (matrix {entries D});
    apply (max X, sigma -> coeffs^sigma // rayMatrix^sigma)
    );

pullback = method()
pullback (ToricMap, ToricDivisor) := ToricDivisr => (f, D) -> (
    if not isCartier(D) then error "--expected input to be Cartier";
    cartierData := cartierCoefficients D;
    raylist := rays source f;
    maxcones := max target f;
    Dpullback := toricDivisor(toList(#raylist:0),source f);
    for rho in raylist do (
	imagerho = f(rho);
	--find which max cone each ray gets sent into
	for sigma in maxcones do (
	    if max(transpose outerNormals(sigma) * imagerho) <= 0 then imagecone := sigma;
	    )
	maxconeindex := position(maxcones, sigma -> sigma == imagecone);
	cartierData_(maxconeindex) * imagerho
	    

TEST ///
--Tests for isWellDefined
--TODO: needs more tests
X = normalToricVariety({{1,0,0},{0,0,1},{0,0,-1}},{{0,1},{0,2}})
Y = normalToricVariety({{0,-1}},{{0}})
f = map(Y,X,matrix{{1,0,0},{0,1,0}})
assert not isWellDefined f

--< Tests for isProper (see isProperPics.pdf) >--
--The source and target are proper then the map is proper
H2 = hirzebruchSurface 2
PP1 = toricProjectiveSpace 1
f = map(PP1,H2,matrix{{1,0}})
assert isWellDefined f
assert isProper f

--The source not proper but the target is so the map is not proper
Y = normalToricVariety(rays H2, drop(max H2, -1))
f = map(PP1, Y, matrix{{1,0}})
assert isWellDefined f
assert not isProper f

--The source is proper and the target is not so the map is proper
g = map(Y, PP1, matrix{{0},{1}})
assert isWellDefined g
assert isProper g

--Test A: The source and target are both not proper but the map is proper
P1A1 = (affineSpace 1) ** (toricProjectiveSpace 1)
A1 = affineSpace 1
h = map(A1, P1A1, matrix{{1,0}})
assert isWellDefined h
assert isProper h

--Test B
X = normalToricVariety({{1,0,0},{0,1,0},{0,0,1},{-1,0,0},{0,0,-1}},{{0,1},{1,2,3},{1,3,4}})
Y = (toricProjectiveSpace 1) ** (affineSpace 1)
f = map(Y,X,matrix{{1,0,0},{0,1,0}})
assert isWellDefined f
assert not isProper f

--Test C
X = normalToricVariety({{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0},{1,2,3},{1,2,4}})
Y = (toricProjectiveSpace 1) ** (affineSpace 1)
A = matrix{{1,0,0},{0,1,0}}
f = map(Y,X,A)
assert isWellDefined f
assert not isProper f

--Test D
X = normalToricVariety({{0,1},{1,0},{0,-1}},{{0,1},{1,2}})
Y = normalToricVariety({{-1,-1},{1,0},{0,1}},{{0,1},{1,2}})
A = id_(ZZ^2)
f = map(Y,X,A)
assert isWellDefined f
assert not isProper f

--Test D'
X = normalToricVariety({{0,1},{1,0},{0,-1},{-1,-1}},{{0,1},{1,2},{2,3}})
Y = normalToricVariety({{-1,-1},{1,0},{0,1}},{{0,1},{1,2}})
A = id_(ZZ^2)
f = map(Y,X,A)
assert isWellDefined f
assert isProper f

--Test E
X = normalToricVariety({{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0,3},{1,2,3},{1,2,4}})
Y = normalToricVariety({{1,0},{0,1},{-1,0}},{{0},{1,2}})
A = matrix{{1,0,0},{0,1,0}}
f = map(Y,X,A)
assert isWellDefined f
assert not isProper f

--Test E'
X = normalToricVariety({{0,-1,0},{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0},{1,4},{1,5},{2,3,4},{2,3,5}})
Y = normalToricVariety({{0,-1},{1,0},{0,1},{-1,0}},{{0},{1},{2,3}})
A = matrix{{1,0,0},{0,1,0}}
f = map(Y,X,A)
assert isWellDefined f
assert not isProper f

--Test F
X'' = normalToricVariety({{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0,3},{0,4},{1,2,3},{1,2,4}})
Y' = normalToricVariety({{1,0},{0,1},{-1,0}},{{0},{1,2}})
A = matrix{{1,0,0},{0,1,0}}
f = map(Y',X'',A)
assert isWellDefined f
assert isProper f

--Test G
X = normalToricVariety({{-1,1,0},{0,0,1},{0,0,-1}},{{0,1},{0,2}})
Y = normalToricVariety({{0,1},{1,0}},{{0,1}})
A = matrix{{1,1,0},{1,1,0}}
f = map(Y,X,A)
assert isWellDefined f
assert not isProper f

--Test H
X = normalToricVariety({{1,-1,0},{1,1,0},{-1,1,0},{0,0,1}},{{0,1,3},{1,2,3}})
Y = normalToricVariety({{0,1},{1,0}},{{0,1}})
A = matrix{{1,1,0},{1,1,0}}
f = map(Y,X,A)
assert isWellDefined f
assert not isProper f

--Test H'
X = normalToricVariety({{1,-1,0},{1,1,0},{-1,1,0},{0,0,1},{0,0,-1}},{{0,1,3},{1,2,3},{0,1,4},{1,2,4}})
Y = normalToricVariety({{0,1},{1,0}},{{0,1}})
A = matrix{{1,1,0},{1,1,0}}
f = map(Y,X,A)
assert isWellDefined f
assert isProper f

///



end

beginDocumentation()

doc ///
    Key
        ToricMaps
    Headline
        a type encoding maps between normal toric varieties
    Description
        Text
	    A morphism of normal toric varieties X -> X' corresponds to a map 
	    of lattices N -> N' where the fans of X and X' are contained in
	    N and N' respectively. To specify a map of normal toric varieties,
	    the target and source normal toric varieties need to be specificied
	    as well as a matrix which maps  N into N'.
    SeeAlso
        NormalToricVarieties  	
	"Making normal toric varieties"
	
///


doc ///
   Key
        (isWellDefined, ToricMap)
    Headline 
        checks if a toric map is well defined 
    Usage 
        isWellDefined f
    Inputs 
        f:ToricMap
	    a map between toric varieties
    Outputs 
        :Boolean 
	    returns true if the map is well defined; false if not
    Description
        Text
            This function checks that a toric map f of varieties is well defined by checking that the 
	    dimensions of the matrix match the dimension of the lattices and checking that the image 
	    of each maximal cone is contained in a maximal cone of the target fan. 
    	Text
            This example illustrates the projection from the Hirzenberg surface H2 to P^1 is well defined.
    	Example  
	   H2 = hirzebruchSurface 2
           PP1 = toricProjectiveSpace 1
           f = map(PP1,H2,matrix{{1,0}})
    	   isWellDefined(f)
	Text
	    This example gives two different maps from projective 2-space to weighted projective 
	    space of weight (1,1,2). The map g corresponding to the identity on the lattices is not well-defined, whereas
	    the map f corresponding to a stretch in the lattices is well-defined.
	Example
	   P2 = toricProjectiveSpace 2
	   WP112 = weightedProjectiveSpace {1,1,2}
	   g = map(WP112, P2, 1)
	   isWellDefined(g)
	   f  = map(WP112, P2, matrix{{1,0},{0,2}})
           isWellDefined(f)	   
    SeeAlso
        ToricMaps
	"Making normal toric varieties"   
        (isSmooth, NormalToricVariety)
        (isSimplicial, NormalToricVariety)
///



doc ///
    Key
        (isProper, ToricMap)
    Headline 
        checks if a toric map is proper
    Usage 
        isProper f
    Inputs 
        f:ToricMap
	    a map between toric varieties
    Outputs 
        :Boolean 
	    returns true if the map is proper; false if not
    Description
        Text
            A map f of varieties is proper if it is universally closed. 
	    Letting f be a map of toric varieties and f' the corresponding map of lattices, the map f is
	    proper if and only if the preimage of the support of the target fan under f' is the support 
	    of the source fan. 
    	Text
            This example illustrates that the projection from the Hirzenberg surface H2 to P^1 is proper.
    	Example  
	   H2 = hirzebruchSurface 2
           PP1 = toricProjectiveSpace 1
           f = map(PP1,H2,matrix{{1,0}})
    	   isProper(f)
	Text
	    This example illustrates that the map from the  blow-up of the origin of 
	    affine 2-space to affine 2-space is proper.
	Example
	   AA2 = affineSpace 2;
	   max AA2
	   BlO = toricBlowup({0,1}, AA2)
	   f  = map(AA2, BlO, 1)
           isProper(f)
    SeeAlso
        "Making normal toric varieties"
  
/// 

doc ///
    Key
        (hilbertPolynomial, NormalToricVariety)
    Headline 
        computes the Hilbert polynomial
    Usage 
        hilbertPolynomial X
    Inputs 
        X:NormalToricVariety
	    a smooth projective toric variety
    Outputs 
        :RingElement 
	    the Hilbert polynomial of X
    Description
        Text
            The Hilbert polynomial of a smooth projective toric
    	    variety $X$ is the Euler characteristic of
    	    $OO_X(i_0,...,i_r)$ where $r$ is the rank of the Picard
    	    group of X and i_0,...,i_r are formal variables.  The
    	    Hilbert polynomial agrees with the Hilbert function when
    	    evaluated at any point in the nef cone.
    	Text
            This example illustrates the projective plane.
    	Example  
    	   PP2 = projectiveSpace 2;
	   h = hilbertPolynomial PP2
	   R = ring h;
	   all(5, i -> sub(h,R_0 => i) == hilbertFunction(i,ring PP2))
	   hilbertPolynomial(ring PP2, Projective => false)
	Text
	    This example illustrates the product of two projective 3-spaces.
	Example
           P3P3 = (projectiveSpace 3) ^** 2;
	   factor hilbertPolynomial P3P3
	Text
	    This example illustrates the Hirzebruch surface 5.
    	Example
	   H5 = hirzebruchSurface 5;
	   factor hilbertPolynomial H5
    SeeAlso
        "Making normal toric varieties"
        (isSmooth, NormalToricVariety)
        (isProjective, NormalToricVariety)
///   






uninstallPackage "ToricMaps"
restart
installPackage "ToricMaps"
check ToricMaps
