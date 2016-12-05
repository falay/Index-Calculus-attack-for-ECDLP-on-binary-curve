import sage.schemes.elliptic_curves.ell_finite_field
import sage.schemes.elliptic_curves.ell_generic
import itertools
import sys

from sage.rings.polynomial.toy_buchberger import buchberger_improved


R.<x1,x2,x3,x4,X> = PolynomialRing(GF(2),5,order='lex')


def SumPoly(m):
	if len(m) < 2:
		return 0
	elif len(m) == 2:
		return 	m[0]-m[1]
	elif len(m) == 3:
		return (m[0]*m[1]+m[0]*m[2]+m[1]*m[2])^2+m[0]*m[1]*m[2]+1
	else:
		left  = m[0:len(m)-2] + [X]
		right = m[len(m)-2:] + [X]
		return SumPoly(left).resultant(SumPoly(right),X)

	
def S3(x1,x2,x3):
	return (x1*x2+x1*x3+x2*x3)^2 + x1*x2*x3 + 1
	
def S4(x1,x2,x3,x4):
	return x1^4*x2^4*x3^4 + x1^4*x2^4*x4^4 + x1^4*x3^4*x4^4 + x2^4*x3^4*x4^4 + x1^3*x2^3*x3^3*x4 + x1^4*x2^2*x3^2*x4^2 + x1^2*x2^4*x3^2*x4^2 + x1^2*x2^2*x3^4*x4^2 + x1^3*x2^3*x3*x4^3 + x1^3*x2*x3^3*x4^3 + x1*x2^3*x3^3*x4^3 + x1^2*x2^2*x3^2*x4^4 + x1^2*x2^2*x3^2 + x1^3*x2*x3*x4 + x1*x2^3*x3*x4 + x1*x2*x3^3*x4 + x1^2*x2^2*x4^2 + x1^2*x3^2*x4^2 + x2^2*x3^2*x4^2 + x1*x2*x3*x4^3 + x1^4 + x2^4 + x3^4 + x4^4	
				
		
		
def FactorBaseChecker(Fv):
			
	if len(Fv) == 0:
		sys.exit("Empty factor basis")		

	for basePoint in Fv:	
		if not E.is_on_curve(basePoint[0],basePoint[1]):
			sys.exit("Invalid point")		
	
	print "Pass factor basis test"		


def SubSpaceGenerator(subV):	
	
	V = []
	
	for L in range(0, len(subV)+1):
		for subset in itertools.combinations(subV, L):
			Poly = 0
			for xTerm in subset:
				Poly += xTerm	
			V.append( Poly )	
	
	return V
	
	
def ExpressionParser(Exp):
	
	## Exponent dict : expDict[xTerm] = coefficient
	expDict = {}
	
	if len(Exp) == 0:
		return 

	isInBracket = False	
	newExp = ""	
	for symbol in Exp:
		
		if symbol == '(':
			isInBracket = True
		elif symbol == ')':	
			isInBracket = False
		
		if isInBracket and symbol == '+':
			symbol = '#'
		
		newExp += symbol
		
	parsedVector = newExp.split(' + ')
	
	for item in parsedVector:
	
		if ')' in item:
			endBracket = item.index(')')
			coef   = item[endBracket+2:]
			subExp = item[1:endBracket]
			subVector = subExp.split(' # ')
			
			for subItem in subVector:
				if subItem in expDict:
					expDict[subItem] += " + " + coef  
				else:
					expDict[subItem] = coef
		
		elif 'x' in item:	
			
			if '*' in item:
				firstMul = item.index('*')
				coef = item[firstMul+1:]	
				xTerm = item[0:firstMul]
			else:
				coef = "1"
				xTerm = item
			
			if xTerm in expDict:
				expDict[xTerm] += " + " + coef
			else:
				expDict[xTerm] = coef
		
		else: # constant
			if '1' in expDict:
				expDict['1'] += " + " + item
			else:
				expDict['1'] = item
			
	return expDict ;	

	
def rowGenerator(*argv):	
	
	global Fv, m
	
	row = [0]*len(Fv)
	
	firstArgXcord  = argv[1][0]
	firstCoeft	   = argv[0]
	secondArgXcord = argv[3][0]
	secondCoeft	   = argv[2]	
	
	for i in range(len(Fv)):
		
		baseXcord = Fv[i][0]	
				
		if baseXcord == firstArgXcord:
			row[i] += firstCoeft	
		if baseXcord == secondArgXcord:
			row[i] += secondCoeft
	
	return row

	
def SolutionCollector(SolutionSet):
	
	global R, E, m, a, b, abSet
	
	rowSet = []
	
	if len(SolutionSet) > 0:
		
		for sol in SolutionSet:
			
			thisSol = str( sol )
			thisSol = thisSol[1:len(thisSol)-1]
			solVec	= thisSol.split(', ')
			
			varA, varB, varC = 0, 0, 0	
			for root in solVec:
				if root[0] == 'a' and root[-1] == '1':
					varA += x^(int(root[1]))	
				elif root[0] == 'b' and root[-1] == '1':
					varB += x^(int(root[1]))
				elif root[0] == 'c' and root[-1] == '1':
					varC += x^(int(root[1]))					
										
			if m == 2:
				try:
					firstArg  = E.lift_x( varA )
					secondArg = E.lift_x( varB )
				except ValueError:
					continue	
				
				for i in [-1,1]:
					for j in [-1,1]:
						if i*firstArg + j*secondArg + R == E(0,1,0):
							
							myRow = rowGenerator(i, firstArg, j, secondArg)
							if not myRow in rowSet: 
								rowSet.append( myRow )
								abSet.append( (a,b) )
								print "Solution found in a=", a, ", b=", b  	

			else:
				try:
					firstArg  = E.lift_x( varA )
					secondArg = E.lift_x( varB )
					thirdArg  = E.lift_x( varC )
				except ValueError:
					continue

				for i in [-1,1]:
					for j in [-1,1]:
						for k in [-1,1]:
								if i*firstArg + j*secondArg + k*thirdArg + R == E(0,1,0):		
									rowSet.append( rowGenerator(i, firstArg, j, secondArg, k, thirdArg) )
									abSet.append( (a,b) )
									print "Solution found in a=", a, ", b=", b	
									

	#else:
	#	print "No solution for a=", a, ", b=", b		

	return rowSet	
	
	
def LinearAlgebraHandler( Vectors, abSet ):	
	
	global P, Q
	
	M = matrix( Vectors )
	v = M.kernel().basis_matrix()	
		
	newKernel = [0]*len(abSet)
	for Row in v:
		for i in range(len(Row)):
			newKernel[i] += Row[i]
	
	A, B = 0, 0
	for i in range(len(abSet)):
		A += abSet[i][0]*newKernel[i]
		B += abSet[i][1]*newKernel[i]

		
	return -A*B^(-1) % P.order()	


	
def DegreeReduction( sysEquations ):
	
	possibleExp = ["^2", "^3", "^4"]
	
	for removedItem in possibleExp:
		sysEquations = sysEquations.replace(removedItem, "") 
			
	#print sysEquations
	
	return sysEquations
	

	
	
'''''''''''''''''''''''''''					
##	 Main Subroutine     ##
'''''''''''''''''''''''''''			
	
if len(sys.argv) == 2:
	m = int( sys.argv[1] )
		
	if m != 2 and m != 3:
		sys.exit("Error: support m = 2 and 3 only")
	
else:
	sys.exit("Usage: ./sage " + sys.argv[0] + " [Value of m]")	
	
	
# Input 

n = input("Enter n ")
F.<x> = GF(2^n)

# Curve generating: order must be 2*prime

a6 = 1 # n = 7, 11, 17, 19, 23

'''
if n == 13:
	a6 = x^11+x^10+x^9+x^6+x^4+1
elif n == 15:	
	a6 = x^12 + x^10 + x^8 + x^6 + x^4 + x
elif n == 29:
	a6 = x^28 + x^26 + x^20 + x^17 + x^14 + x^12 + x^8 + x^7 + x^4 + x^3 + x + 1	
'''	
	
E = EllipticCurve(F,[1,1,0,0,a6])


# Construct random point

P = E.random_element()

while True:
	if 2*P == E(0,1,0):
		P = E.random_element()
	else:
		P = 2*P
		break
	
k = randint(1,P.order()-1)
Q = k*P

print "P's order =", P.order()
print "k =", k

# Algorithm 

## Chose a subspace V
nPr = ceil(n / m)
#nPr = floor(n / m)

subV = list(x^i for i in range(0,nPr))
V = SubSpaceGenerator( subV )


## Find a Factor Basis
Fv = []
for xCoord in V:
	try:
		curvePoint = E.lift_x( xCoord )		
		Fv.append( curvePoint )
	except ValueError:
		continue	
	
		
## Checker for factor basis
FactorBaseChecker( Fv )



## Compute relations
Counter = 0
Vectors = [] 
Rlist 	= []
abSet   = []

while Counter <= 2^nPr:
	
	a = randint(0, 2^n)
	b = randint(0, 2^n)
	R = a*P + b*Q
	
	if not R in Rlist:
		Rlist.append( R )
	else:
		continue
	
	# X1, X2, ... Xm variable in Weil descent format
	A = list(var('a%d' % i) for i in range(nPr))	
	B = list(var('b%d' % i) for i in range(nPr))
	C = list(var('c%d' % i) for i in range(nPr))
	X1, X2, X3 = 0, 0, 0
	for i in range(nPr):
		X1 += A[i]*x^i
		X2 += B[i]*x^i
		if m == 3:	
			X3 += C[i]*x^i
	
	if m == 3:	
		expDict = ExpressionParser( str(S4(X1,X2,X3,R[0]).expand()) )	
	else:
		expDict = ExpressionParser( str(S3(X1,X2,R[0]).expand()) )	
	
	
	systemEquations = ""
	Variables = ""
	for xTerm in expDict:
		systemEquations += expDict[xTerm] + ","
	
	
	for i in range(nPr):
		
		if m == 3:
		#	systemEquations += str(A[i])+"^2-"+str(A[i])+","
		#	systemEquations += str(B[i])+"^2-"+str(B[i])+","
		#	systemEquations += str(C[i])+"^2-"+str(C[i])+","
			Variables += str(A[i])+","+str(B[i])+","+str(C[i])+","
		
		else:
			#systemEquations += str(A[i])+"^2-"+str(A[i])+","
			#systemEquations += str(B[i])+"^2-"+str(B[i])+","
			Variables += str(A[i])+","+str(B[i])+","
	
				
	systemEquations = systemEquations[:-1]
	Variables = Variables[:-1]
		
	Pring = PolynomialRing(GF(2),Variables,order='lex')
	Pring.inject_variables(verbose=False)
	
	systemEquations = DegreeReduction( systemEquations )
	
	I = Ideal( sage_eval(systemEquations, locals=Pring.gens_dict()) )	
	

	#print "Start computing Groebner basis ..."
	#I = Ideal( I.groebner_basis() )		
	#print "End of computing"
	
	J = I + sage.rings.ideal.FieldIdeal( Pring )
		
	rowSet = SolutionCollector( list( J.variety() ))	


	if len(rowSet) > 0:
		Vectors += rowSet
		Counter += 1

	

ansK = LinearAlgebraHandler( Vectors, abSet )

print "Ans k=", ansK


	
	
	