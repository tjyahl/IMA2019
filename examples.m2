needsPackage "ToricMaps"

H2 = hirzebruchSurface 2
PP1 = toricProjectiveSpace 1
f = map(PP1,H2,matrix{{1,0}})
print("old: " | toString(elapsedTime isProper f))
print("new: " | toString(elapsedTime isProper(f,1)))
print("-----\n")

Y = normalToricVariety(rays H2, drop(max H2, -1))
f = map(PP1, Y, matrix{{1,0}})
print("old: " | toString(elapsedTime isProper f))
print("new: " | toString(elapsedTime isProper(f,2)))
print("-----\n")

g = map(Y, PP1, matrix{{0},{1}})
print("old: " | toString(elapsedTime isProper g))
print("new: " | toString(elapsedTime isProper(g,3)))
print("-----\n")

P1A1 = (affineSpace 1) ** (toricProjectiveSpace 1)
A1 = affineSpace 1
h = map(A1, P1A1, matrix{{1,0}})
print("old: " | toString(elapsedTime isProper h))
print("new: " | toString(elapsedTime isProper(h,4)))
print("-----\n")

X = normalToricVariety({{1,0,0},{0,1,0},{0,0,1},{-1,0,0},{0,0,-1}},{{0,1},{1,2,3},{1,3,4}})
Y = (toricProjectiveSpace 1) ** (affineSpace 1)
f = map(Y,X,matrix{{1,0,0},{0,1,0}})
print("old: " | toString(elapsedTime isProper f))
print("new: " | toString(elapsedTime isProper(f,5)))
print("-----\n")

X = normalToricVariety({{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0},{1,2,3},{1,2,4}})
Y = (toricProjectiveSpace 1) ** (affineSpace 1)
A = matrix{{1,0,0},{0,1,0}}
f = map(Y,X,A)
print("old: " | toString(elapsedTime isProper f))
print("new: " | toString(elapsedTime isProper(f,6)))
print("-----\n")

X = normalToricVariety({{0,1},{1,0},{0,-1}},{{0,1},{1,2}})
Y = normalToricVariety({{-1,-1},{1,0},{0,1}},{{0,1},{1,2}})
A = id_(ZZ^2)
f = map(Y,X,A)
print("old: " | toString(elapsedTime isProper f))
print("new: " | toString(elapsedTime isProper(f,7)))
print("-----\n")

X = normalToricVariety({{0,1},{1,0},{0,-1},{-1,-1}},{{0,1},{1,2},{2,3}})
Y = normalToricVariety({{-1,-1},{1,0},{0,1}},{{0,1},{1,2}})
A = id_(ZZ^2)
f = map(Y,X,A)
print("old: " | toString(elapsedTime isProper f))
print("new: " | toString(elapsedTime isProper(f,8)))
print("-----\n")

X = normalToricVariety({{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0,3},{1,2,3},{1,2,4}})
Y = normalToricVariety({{1,0},{0,1},{-1,0}},{{0},{1,2}})
A = matrix{{1,0,0},{0,1,0}}
f = map(Y,X,A)
print("old: " | toString(elapsedTime isProper f))
print("new: " | toString(elapsedTime isProper(f,9)))
print("-----\n")

X = normalToricVariety({{0,-1,0},{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0},{1,4},{1,5},{2,3,4},{2,3,5}})
Y = normalToricVariety({{0,-1},{1,0},{0,1},{-1,0}},{{0},{1},{2,3}})
A = matrix{{1,0,0},{0,1,0}}
f = map(Y,X,A)
print("old: " | toString(elapsedTime isProper f))
print("new: " | toString(elapsedTime isProper(f,10)))
print("-----\n")

X'' = normalToricVariety({{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0,3},{0,4},{1,2,3},{1,2,4}})
Y' = normalToricVariety({{1,0},{0,1},{-1,0}},{{0},{1,2}})
A = matrix{{1,0,0},{0,1,0}}
f = map(Y',X'',A)
print("old: " | toString(elapsedTime isProper f))
print("new: " | toString(elapsedTime isProper(f,11)))
print("-----\n")

X = normalToricVariety({{-1,1,0},{0,0,1},{0,0,-1}},{{0,1},{0,2}})
Y = normalToricVariety({{0,1},{1,0}},{{0,1}})
A = matrix{{1,1,0},{1,1,0}}
f = map(Y,X,A)
print("old: " | toString(elapsedTime isProper f))
print("new: " | toString(elapsedTime isProper(f,12)))
print("-----\n")

X = normalToricVariety({{1,-1,0},{1,1,0},{-1,1,0},{0,0,1}},{{0,1,3},{1,2,3}})
Y = normalToricVariety({{0,1},{1,0}},{{0,1}})
A = matrix{{1,1,0},{1,1,0}}
f = map(Y,X,A)
print("old: " | toString(elapsedTime isProper f))
print("new: " | toString(elapsedTime isProper(f,13)))
print("-----\n")

X = normalToricVariety({{1,-1,0},{1,1,0},{-1,1,0},{0,0,1},{0,0,-1}},{{0,1,3},{1,2,3},{0,1,4},{1,2,4}})
Y = normalToricVariety({{0,1},{1,0}},{{0,1}})
A = matrix{{1,1,0},{1,1,0}}
f = map(Y,X,A)
print("old: " | toString(elapsedTime isProper f))
print("new: " | toString(elapsedTime isProper(f,14)))
print("-----\n")

