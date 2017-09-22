import sympy

# Compute the CRS and proof size of a GS-like proof system
# Sizes are given as a 2-dimensional array with 2 columns, that is,
# size = [a1,a2] and a1,a2 are 1 dimensional array. size[0] is a polynomial
# which represents the number of elements in G1 and size[1] the number of elements
# in G2

#def toString(poly, vname):
#
#    if len(poly) == 1:
#        return str(int(poly[0]))
#    s =''
#    for i in range(len(poly)-1,0,-1):
#        coef = ''
#        if poly[i] == 1:
#            coef = ''
#        if poly[i] > 1:
#            coef += str(int(poly[i]))
#        power = ''
#        if poly[i] != 0 and i==1:
#            power = vname
#        elif poly[i] != 0  and i>1:
#            power = vname+'^'+str(i)
#        s += coef+power+'+'
#    if poly[0]:
#        s += str(int(poly[0]))
#    else:
#        s = s[:len(s)-1]
#    return s

def log2(x):
    return sympy.log(x)


#this class should be an abstract class (i.e. not instantiable)
class PrintableProofSystem(object):

    def __init__(self,crs,proof, pTime = -1, vTime = -1):
        self.crs = crs
        self.proof = proof
        self.pTime = pTime
        self.vTime = vTime
 
    def printCRS(self):
        print 'G1: '+self.crs[0] + 'G2: '+self.crs[1]
        #print 'G1: '+toString(self.crs[0],self.vname) + ' G2: ' + toString(self.crs[1],self.vname) 

    def printProof(self):
        print 'G1: '+self.proof[0] + 'G2: '+self.proof[1]
        #print 'G1: '+toString(self.proof[0],self.vname) + ' G2: ' + toString(self.proof[1],self.vname)   

class GS(PrintableProofSystem):

    # [#elements in G1, #elements in G2, #elements in Zq]
    # Follows [SIAMJC:GroSah12] http://www0.cs.ucl.ac.uk/staff/J.Groth/WImoduleFull.pdf, table 3 at page 1221
    crs = [4,4,0]
    comm = [2,2,0]
    
    PPE = [4,4,0]
    lPPE1 = [2,0,0]
    lPPE2 = [0,2,0]
    
    MME1 = [2,4,0]
    lMME1a = [1,0,0]
    lMME1b = [0,0,2]
    MME2 = [4,2,0]
    lMME2a = [0,0,2]
    lMME2b = [0,1,0]
    
    QE = [2,2,0]
    lE = [0,0,2]

    # For an equation of the form
    #
    # \sum_{j=1}^nTermsLin2 \alpha_j*y_j + \sum_{i=1}^nTermsLin1 x_i*\beta_i + \sum_{(i,j)\in I} \lambda{i,j}x_i*y_j = t (eq)
    #
    # Define nTermsQuad := |I|, and nVars1 and nVars2 the total number of variables in the the first and second module, respectively
    def __init__(self, typ, nVars1, nVars2, nTermsLin1 = None, nTermsLin2 = None, nTermsQuad = 0):
        self.nVars1 = nVars1
        self.nVars2 = nVars2
        self.nTermsLin1 = nTermsLin1 if nTermsLin1 != None else nVars1
        self.nTermsLin2 = nTermsLin2 if nTermsLin2 != None else nVars2
        self.nTermsQuad = nTermsQuad
        proof = [0,0]
        vTime = 0
        if typ == 'PPE':
                proof = GS.PPE
                vTime = 16 # Number of pairing in the right side (proof) of the verification equation
        elif typ == 'lPPE1':
            proof = GS.lPPE1
            vTime = 4  # Number of pairing in the right side (proof) of the verification equation
            nTermsQuad = 0 # Hey smart guy, do not put quadratic terms if the equation is linear
        elif typ == 'lPPE2':
            proof = GS.lPPE2 
            vTime = 4 # Number of pairing in the right side (proof) of the verification equation
            nTermsQuad = 0 # Hey smart guy, do not put quadratic terms if the equation is linear
        elif typ ==  'MME1':
            proof = GS.MME1
            vTime = 12 # Number of pairing in the right side (proof) of the verification equation
        elif typ == 'lMME1a':
            proof = GS.lMME1a
            vTime = 4 # TODO Check if this is the number of parings in the right side
        elif typ == 'lMME1b':
            proof = GS.lMME1b
            vTime = 0 # TODO No pairings in the right side? No pairings at all?
        elif typ == 'MME2':
            proof = GS.MME2
            vTime = 12 # Number of pairing in the right side (proof) of the verification equation
        elif typ == 'lMME2a':
            proof = GS.lMME2a
            vTime = 0 # TODO No pairings in the right side? No pairings at all? 
        elif typ == 'lMME2b':
            proof = GS.lMME2b
            vTime = 4 # TODO Check if this is the number of parings in the right side
        elif typ == 'QE':
            proof = GS.QE
            vTime = 8 # Number of pairing in the right side (proof) of the verification equation
        else:
            proof = GS.lE
            vTime = 0 # TODO No pairings in the right side? No pairings at all? 

        pTime = 2*(self.nVars1+self.nVars2) # exponentiations for computing commitment to variables
        pTime += proof[0]+proof[1] # exponentiations for computing the proof

        vTime += 2*(self.nTermsLin1+self.nTermsLin2) # Number of pairings in the linear part of the left side side of the verifications equation
        vTime += 4*self.nTermsQuad # Number of pairings in the quadratic part of the left side of the verification equation
        #TODO No pairings when the proof is in Zq?
        if proof[0] == 0 and proof[1] == 0:
            vTime = 0
        
        super(GS,self).__init__(GS.crs,proof,pTime,vTime)

#this doesn't has a proof ...
class MP(PrintableProofSystem):

    #k = 1
    def __init__(self, n):
        crs = [
                2*(n[0]+1) if n[0] != 0 else 0, 
                2*(n[1]+1) if n[1] != 0 else 0]
        self.com = [
                0 if n[0] == 0 else 2,
                0 if n[1] == 0 else 2]
        pTime = 2*(n[0]+n[1]) # Number of exponentiations for computing the MP commitment
        super(MP,self).__init__(crs,self.com,pTime)


class Lin(PrintableProofSystem):

    #k = 1 and k~ = k


    # if n[0] and n[1] != 0 it creates 2 proof systems, one for proofs in G1 and the other for G2
    # M is of size n x t and A is of size 1x1
    def __init__(self,n,t) :
        self.A = [1 if n[1] != 0 else 0, 1 if n[0] != 0 else 0]
        self.A_delta = [n[1],n[0]]
        self.M_delta = [t[0],t[1]]
        crs = [
                self.A[0]+self.A_delta[0]+self.M_delta[0],
                self.A[1]+self.A_delta[1]+self.M_delta[1]]
        proof = [1 if n[0] != 0 else 0, 1 if n[1] != 0 else 0]
        pTime = t[0] if t[0] != 0 else t[1] # Number of exponentiations for computing the proof
        vTime = n[0]+1 if n[0] != 0 else n[1]+1 #Number of pairings in the verification equations, n in the left side and 1 in the right side
        
        super(Lin,self).__init__(crs,proof,pTime,vTime)

class LinSplit(PrintableProofSystem):

    # k = 2 and k~ = k
    # M is of size m x t, N is of size n x t, and A is of size 2 x 2
    def __init__(self, m, n, t):
        self.A = [4, 4]
        self.A_lambda = 2*m
        self.A_xi = 2*n
        self.M_lambda = 2*t
        self.N_xi = 2*t
        crs = [
                self.M_lambda + self.A_xi + self.A[0],
                self.A_lambda + self.A[1] + self.N_xi]
        proof = [2,2]
        pTime = 2*(2*t+2) # Number of exponentiations on both groups (2*t plus 2 for z in each group)
        vTime = 2*(2*n+4) # Number of pairings for the verification equation (2*n for the statement plus 4 for the proof for each side of the verification equation)
        
        super(LinSplit,self).__init__(crs,proof,pTime,vTime)

class Sum(LinSplit):

    def __init__(self,n,t):
        super(Sum,self).__init__(n,n,t)

class EqCom(LinSplit):

    def __init__(self,m_rows, m_cols, n_rows, n_cols, witness):
        super(EqCom,self).__init__(m_rows, n_rows, m_cols+n_cols-witness)

# This follows the proof system of Sect 4.2.2
class Bits(PrintableProofSystem):

    def __init__(self,m):
        self.mp = MP([0,m]) # H
        self.CDmatrs = 4*((m+1)*(m+1)-m) # (C_{i,j},D_{i,j}) matrices
        self.pi_sum = Sum((m-1)*(m-1)-m,4)
        self.pi_eqcom = EqCom(2, m+1, 2, m+1, m)
        crs = [
                self.CDmatrs + self.pi_sum.crs[0] + self.pi_eqcom.crs[0],
                self.mp.crs[1] + self.CDmatrs + self.pi_sum.crs[1] + self.pi_eqcom.crs[1]]
        proof = [
                4 + self.pi_sum.proof[0] + self.pi_eqcom.proof[0],
                self.mp.com[1] + 4 + self.pi_sum.proof[1] + self.pi_eqcom.proof[1]]
        
        pTime = self.mp.pTime # Time for computing d
        pTime += 8 # Time for computing ([R]_1,[-R]_2)
        pTime += 2*m*8 # Time for computing the rest of ([\Theta]_1,[\Pi]_2). Note that the b_i(b_j-1) are either 0 or 1 and thus do not require exponentiations
        pTime += self.pi_sum.pTime + self.pi_eqcom.pTime # Time for the sub-proof-systems

        vTime = 4+4+4 # Time for the verification equation (step 1 of the verifier)
        vTime += self.pi_sum.pTime + self.pi_eqcom.pTime

        super(Bits,self).__init__(crs,proof,pTime,vTime)

# Bits with Hamming wight = 1
class Bits1(Bits):

    def __init__(self,m):
        super(Bits1,self).__init__(m)
        self.CDmatrs = 4*m+4*m+4*(m-1) # (|C_{i,!=},D_{i,!=})| + |C_{m+1,i},D_{m+1,i}|+|C_{i,m+1},D_{m+1,i}| matrices
        self.pi_sum = Sum(3*m-1,4)
        self.crs = [
                self.CDmatrs + self.pi_sum.crs[0] + self.pi_eqcom.crs[0],
                self.mp.crs[1] + self.CDmatrs + self.pi_sum.crs[1] + self.pi_eqcom.crs[1]]
        self.proof = [
                4 + self.pi_sum.proof[0] + self.pi_eqcom.proof[0],
                self.mp.com[1] + 4 + self.pi_sum.proof[1] + self.pi_eqcom.proof[1]]
        # Maybe pTime and vTime are smaller in this case


class Bitsn(PrintableProofSystem):

    # m = witness size, n = agg parameter
    def __init__(self,m,n, hamming_weight_1 =  False):
        self.mp = MP([m*n,0])
        self.pi_eqcom = EqCom(2*n, m*n+n, 2, m*n+1, m*n)
        self.pi_bits = Bits(m*n) if not hamming_weight_1 else Bits1(m*n)
        # \bar{G} + crs_bits+crs_eqcom
        crs = [ 
                self.mp.crs[0] + self.pi_eqcom.crs[0] + self.pi_bits.crs[0],
                self.mp.crs[1] + self.pi_eqcom.crs[1] + self.pi_bits.crs[1]]
        proof = [
                self.mp.com[0] + self.pi_eqcom.proof[0] + self.pi_bits.proof[0],
                self.mp.com[1] + self.pi_eqcom.proof[1] + self.pi_bits.proof[1]]
        pTime = self.mp.pTime + self.pi_eqcom.pTime + self.pi_bits.pTime
        vTime = self.pi_eqcom.vTime + self.pi_bits.vTime
        super(Bitsn, self).__init__(crs, proof,pTime,vTime)

class SetMemb(PrintableProofSystem):

    def __init__(self, m_rows, lambda_rows, m_cols, n_cols, n_agg, repeated_elements = True):
        self.mp = MP([n_agg,0])
        self.Xi_rows = n_agg*(m_rows+lambda_rows) + 2*m_cols
        self.Xi_cols = n_agg*(m_cols+n_cols)+m_cols
        self.pi_lin = Lin([self.Xi_rows,0], [self.Xi_cols,0])
        self.pi_bits = Bitsn(n_agg, m_cols, not repeated_elements)
        crs = [
                self.mp.crs[0] + self.pi_lin.crs[0] + self.pi_bits.crs[0],
                self.mp.crs[1] + self.pi_lin.crs[1] + self.pi_bits.crs[1]]
        proof = [
                self.mp.com[0]*m_cols + self.pi_lin.proof[0] + self.pi_bits.proof[0],
                self.mp.com[1]*m_cols + self.pi_lin.proof[1] + self.pi_bits.proof[1]]
        pTime = self.mp.pTime + self.pi_lin.pTime + self.pi_bits.pTime
        vTime = self.pi_lin.vTime + self.pi_lin.vTime
        super(SetMemb, self).__init__(crs, proof,pTime,vTime)


class SetMembSimple(SetMemb):

    def __init__(self, setSize, nAgg):
        super(SetMembSimple, self).__init__(2, 1, setSize, 2, nAgg)


class Shuffle(PrintableProofSystem):
    
    def __init__(self, size):
        self.eq1 = GS('lMME1b', size, 0, 0)
        # eq2 can be expressed as two linear PPEs with variables in G1 (look at the 2 factor for computing the proof size)
        self.eq2 = GS('lPPE2', size+1, 0, 0)
        self.s = size
        self.pi_set = SetMemb(2, 1, size, 2, size)
        crs = [
                self.s + self.eq1.crs[0] + self.pi_set.crs[0], # eq1 and eq2 share the same CRS
                self.eq1.crs[1] + self.pi_set.crs[1]]
        proof = [
                2*self.s + 2 + self.eq1.proof[0] + 2*self.eq2.proof[0]  + self.pi_set.proof[0], # eq2 represents two different equations
                self.eq1.proof[1] + 2*self.eq2.proof[1] + + self.pi_set.proof[1]] # com(Ps), com(s^T * \delta), 2 GS proofs, set memb proof
      
        pTime = size # exponentiations for computing [y]_1
        pTime += self.eq1.pTime + 2*self.eq2.pTime # eq2 represents two equations
        pTime += self.pi_set.pTime


        vTime = self.eq1.vTime + 2*self.eq2.vTime + self.pi_set.vTime
        
        super(Shuffle, self).__init__(crs, proof, pTime, vTime)

class Range(PrintableProofSystem):

    # Proof of membership in [0,2^n-1]
    # c == k
    def __init__(self, n, c):
        self.n = n
        self.c = c
        self.d = n**c
        self.m = log2(self.d)
        self.l = n/self.m
        self.eq = GS('lMME2', self.l+1, 0, 0)
        self.pi_set = SetMemb(2, 0, self.m, 1, self.l)
        crs = [
                self.eq.crs[0] + self.pi_set.crs[0],
                self.eq.crs[1] + self.pi_set.crs[1]]
        proof = [
                2*self.l + self.eq.proof[0] + self.pi_set.proof[0],
                 self.eq.proof[1] + self.pi_set.proof[1]]

        pTime = self.eq.pTime + self.pi_set.pTime
        vTime = self.eq.vTime + self.pi_set.vTime

        super(Range, self).__init__(crs,proof,pTime,vTime)


def test():
    (n,c) = sympy.symbols('n,c')
    sympy.init_printing()
    rp = Range(n,c)
    print rp.crs[0]
