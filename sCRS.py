import sympy
from sympy.plotting import plots

# Symmetric version

# kasjhksajhdkjashd

# Compute the CRS and proof size of a GS-like proof system
# Sizes are given as a 2-dimensional array with 2 columns, that is,
# size = [a1,a2] and a1,a2 are 1 dimensional array. size[0] is a polynomial
# which represents the number of elements in G1 and size[1] the number of elements
# in G2

def log2(x): # FIXME Just for showing $\mathrm{log}(c)$ 
    return sympy.log(x)

# Compute l[1][1]*l[1][2]+...l[n][1]+l[n][2]
def getLLSize(llist):
        return reduce(
                lambda x,y: x+y,
                map(
                    lambda M: M[0]*M[1],
                    llist))

class MP(object):

    # Com(x;r) = G_0x + G_1r
    def __init__(self, n):
        self.ck= [3,(n+2)]
        self.size = 3
        self.rand = 2 #number of random coins (each coin chosen from Z_q)
        self.cTime = 3*(n+2) # Number of exponentiations for computing the MP commitment

class ProofSystem(object):

    # crs and proof are lists of rectangular matrices..
    def __init__(self, crs, proof, pTime, vTime):
        # We also allow crs be an Int or crs  of type [...,Int,...]
        if isinstance(crs, list):
           for i,c in enumerate(crs):
               if not isinstance(c, list):
                   crs[i] = [c,1]
               elif len(c) > 2:
                   raise ValueError("Only rectangular matrices are allowed in the crs")
        else:
            crs=[[crs,1]]
        if isinstance(proof, list):
           for i,p in enumerate(proof):
               if not isinstance(p, list):
                   proof[i]=[p,1]
               elif len(c) > 2:
                   raise ValueError("Only rectangular matrices are allowed in the proof")
        else:
            proof=[[proof,1]]
        self.crs = crs
        self.proof = proof
        self.pTime = pTime
        self.vTime = vTime

    def getCRSSize(self):
        return getLLSize(self.crs)

    def getProofSize(self):
        return getLLSize(self.proof)

# Note that proof nor pTime consider, respec., size and time of commitments to variables
class GS(ProofSystem):

    # In general, it should be [#elements in G, #elements in Zq] but I'm ignoring Z_q elements
    crs = [[3,3]]
    comSize = 3 # size of GS commitments
    rand = 3    # number of random bits (measured in number of group elements)
    comTime = 3*3 # 9 exponentiations for computing a GS commitment
    
    # Proof sizes
    # Follows [SIAMJC:GroSah12] http://www0.cs.ucl.ac.uk/staff/J.Groth/WImoduleFull.pdf, table 4 at page 1226
    PPE = 9
    lPPE = 3
    
    MME = 3
    # It should be [0,3] but I'm ignoring Z_q values
    lMMEa = 0 #var in G
    lMMEb = 2 #var in Z
    
    QE = 6
    # It should be [0] but I'm ignoring Z_q values
    lE = 0

    # For an equation of the form
    #
    # \sum_{i=1}^nTermsLin \alpha_i*x_i + \sum_{(i,j)\in I} \lambda{i,j}x_i*x_i = t (eq)
    #
    # Define nTermsQuad := |I|, and nVars the total number of variables in the module
    def __init__(self, typ, nVars, nTermsLin = None, nTermsQuad = 0):
    
        nTermsLin = nTermsLin if nTermsLin != None else 0
        proof = 0
        vTime = 0
        if typ == 'PPE':
            proof = GS.PPE
            vTime = 52 # Number of pairing in the right side (proof) of the verification equation
        elif typ == 'lPPE':
            proof = GS.lPPE
            vTime = 9  # Number of pairing in the right side (proof) of the verification equation
            nTermsQuad = 0 # Hey smart guy, do not put quadratic terms if the equation is linear
        elif typ ==  'MME':
            proof = GS.MME
            vTime = 54 # Number of pairing in the right side (proof) of the verification equation
        elif typ == 'lMMEa':
            proof = GS.lMMEa
            vTime = 0 # TODO No pairings in the right side? No pairings at all?
        elif typ == 'MMEb':
            proof = GS.MMEb
            vTime = 6 # Number of pairing in the right side (proof) of the verification equation
            # The proof is of size 2. E.g. eq: x[a] = [b]
            # => verification equation e([U](x,r1,r2)^T,[a]) = e([U](1,0,0)^T,[b]) 
            # => proof is (r1[a],r2[a]) which is independent of the witness x
        elif typ == 'QE':
            proof = GS.QE
            vTime = 18 # Number of pairing in the right side (proof) of the verification equation
        else:
            proof = GS.lE

            vTime = 0 # TODO No pairings in the right side? No pairings at all? 

        #pTime = GS.comSize*nVars # exponentiations for computing commitment to variables
        pTime = proof # TODO Check this: exponentiations for computing the proof

        vTime += 3*nTermsLin # Number of pairings in the linear part of the left side side of the verifications equation
        vTime += 9*nTermsQuad # Number of pairings in the quadratic part of the left side of the verification equation
        #TODO No pairings when the proof is in Zq? For shure!
        if proof == 0:
            vTime = 0

        self.nVars = nVars
        self.nTermsLin = nTermsLin
        self.nTermsQuad = nTermsQuad
        super(GS,self).__init__(self.crs,proof,pTime,vTime)

    def getComTime(self):
        return GS.rand*GS.comSize*self.nVars

    def getComSize(self):
        return GS.comSize*self.nVars

class Lin(ProofSystem):

    #k = 2 and k~ = k (DLin)


    # M is of size n x t and A is of size 2x2
    def __init__(self, n,t) :
        A = [2,2]
        A_delta = [2,n]
        M_delta = [2,t]
        crs = [A, A_delta, M_delta]
        #self.crsSize = 4 + self.A_delta + self.A_delta + self.M_delta
        proof =  2
        pTime = 2*t # Number of exponentiations for computing the proof
        vTime = 2*n+4 #Number of pairings in the verification equations, 2n in the left side and 4 in the right side

        self.A = A
        self.A_delta = A_delta
        self.M_delta = M_delta
        super(Lin,self).__init__(crs,proof,pTime,vTime)
        
#
#class Sum(Lin):
#
#    def __init__(self,n,t):
#        super(Sum,self).__init__(n,n,t)
#
class EqCom(Lin):

    # proof in 
    #      / M_0 M_1  0  \
    # Span \ N_0  0  N_1 /
    # where M = (M_0 M_1) and N = (N_0 N_1) are commitment keys
    # for committing to vector of size n.
    # M_0,N_0 are matrices of size m_rows x m_cols, n_rows x n_cols 

    def __init__(self,m_rows, m_cols, n_rows, n_cols, n):
        super(EqCom,self).__init__(m_rows+n_rows, m_cols+n_cols-n)

# This is an adaptation of the proof system of Sect 4.2.2 to symmetric groups
class Bits(ProofSystem):

    def __init__(self,m):
        Com1 = MP(m) # for committing to c
        Com2 = MP(m) # for committing to d
        CDmatrs = Com1.size*Com2.size*( # This is equal to size(Tensor(Com1.ck,Com2.ck)),
                (m + Com1.rand)*(m + Com2.rand)
                -m) # C_{i,j} matrices
        pi_lin = Lin(
                Com1.size*Com2.size,
                (m+Com1.rand)*(m+Com2.rand)-m) # proving membership in Span({C_{i,j}: i!=j})
        pi_eqcom = EqCom(
                Com1.size, m+Com1.rand,
                Com2.size, m+Com2.rand,
                m) # proving that c and open to the same value

        crs = [Com1.ck] + [Com2.ck] + [CDmatrs] + pi_lin.crs + pi_eqcom.crs
        #       (     c      ,        d         ,  \Pi ,  pi_lin           , pi_eqcom) 
        proof = [Com1.size] + [Com2.size] +  [Com1.size*Com2.size] + pi_lin.proof + pi_eqcom.proof
        
        pTime = Com1.cTime + Com2.cTime # Time for computing c,d
        #        C_{m+i,j} and C_{i,m+j}   C_{n+i,n+j}
        pTime += Com1.size*Com2.size*(
                 Com1.rand*m + Com2.rand*m + Com1.rand*Com2.rand) # Time for computing the rest of [\Pi]. Note that the b_i(b_j-1) are either 0 or 1 and thus do not require exponentiations
        pTime += pi_lin.pTime + pi_eqcom.pTime # Time for the sub-proof-systems

        vTime = 2*Com1.size*Com2.size # Time for the verification equation (step 1 of the verifier). Com1.size*Com2.size parings at each side of the equation
        vTime += pi_lin.vTime + pi_eqcom.vTime

        self.Com1 = Com1
        self.Com2 = Com2
        self.CDmatrs = CDmatrs
        self.pi_lin = pi_lin
        self.pi_eqcom = pi_eqcom
        super(Bits,self).__init__(crs,proof,pTime,vTime)

# Bits with Hamming wight = 1
class Bits1(ProofSystem):

    def __init__(self,m):
        Com1 = MP(m) # for committing to c
        Com2 = MP(m) # for committing to d
        CDmatrs = Com1.size*Com2.size*(
                m + Com1.rand*m + Com2.rand*m + Com1.rand*Com2.rand) # C_{i,!=}, C_{m+i,j}, C_{i,m+j} matrices
        pi_lin = Lin(
                Com1.size*Com2.size,
                m + Com1.rand*m + Com2.rand*m + Com1.rand*Com2.rand) # proving membership in Span(XXX)
        pi_eqcom = EqCom(
                Com1.size, m + Com1.rand,
                Com2.size, m + Com2.rand, m) # proving that c and open to the same value

        crs = [Com1.ck] + [Com2.ck] + [CDmatrs] + pi_lin.crs + pi_eqcom.crs
        #       (     c      ,        d         ,  \Pi ,  pi_lin           , pi_eqcom) 
        proof = [Com1.size] + [Com2.size] + [Com1.size*Com2.size] + pi_lin.proof + pi_eqcom.proof
        
        pTime = Com1.cTime + Com2.cTime # Time for computing c,d
        #        C_{m+i,j} and C_{i,m+j}   C_{n+i,n+j}
        pTime += Com1.size*Com1.size*(Com1.rand*m + Com2.rand*m + Com1.rand*Com2.rand) # Time for computing the rest of [\Pi]. Note that the b_i(b_j-1) are either 0 or 1 and thus do not require exponentiations
        pTime += pi_lin.pTime + pi_eqcom.pTime # Time for the sub-proof-systems

        vTime = 2*Com1.size*Com2.size # Time for the verification equation (step 1 of the verifier). 9 parings at each side of the equation
        vTime += pi_lin.vTime + pi_eqcom.vTime

        self.Com1 = Com1
        self.Com2 = Com2
        self.CDmatrs = CDmatrs
        self.pi_lin = pi_lin
        self.pi_eqcom = pi_eqcom
        super(Bits1,self).__init__(crs, proof, pTime, vTime)

class Bitsn(ProofSystem):

    # m = witness size, n = agg parameter
    def __init__(self,m,n, hamming_weight_1 =  False):
        Com = MP(m*n)
        pi_eqcom = EqCom(3*n, m*n+2*n, 3, m*n+2, m*n)
        pi_bits = Bits(m*n) if not hamming_weight_1 else Bits1(m*n)
        # \bar{G} + crs_bits+crs_eqcom
        crs = [Com.ck] + pi_eqcom.crs + pi_bits.crs 
        proof = [Com.size] + pi_eqcom.proof + pi_bits.proof
        pTime = Com.cTime + pi_eqcom.pTime + pi_bits.pTime
        vTime = pi_eqcom.vTime + pi_bits.vTime

        self.Com = Com
        self.pi_eqcom = pi_eqcom
        self.pi_bits = pi_bits
        super(Bitsn, self).__init__(crs, proof, pTime, vTime)

class SetMemb(ProofSystem):

    def __init__(self, m_rows, lambda_rows, m_cols, n_cols, n_agg, repeated_elements = True):
        Com = MP(n_agg)
        #
        #           /  Sigma       0        0       0    \           /     M    N \
        #           |                       0       0    |   Sigma = \  \Lambda 0 /
        #    Xi =   |   0         Sigma     0       0    | 
        #           | g_i  0    g_n   0  g_{n+1}    0    |   Xi is of size n_agg*(m_rows+lambda_rows) + Com.size*m_cols
        #           \  0  g_i    0   g_n    0    g_{n+1} /   (If Com.rand=1, otherwise the matrix should be extended in the natural way)
        #
        Xi = [n_agg*(m_rows+lambda_rows) + Com.size*m_cols,
                n_agg*(m_cols+n_cols) + Com.rand*m_cols]
        pi_lin = Lin(Xi[0], Xi[1])
        pi_bits = Bitsn(n_agg, m_cols, not repeated_elements)

        crs = [Com.ck] + pi_lin.crs + pi_bits.crs
        proof = [Com.size*m_cols] + pi_lin.proof + pi_bits.proof
        pTime = Com.cTime + pi_lin.pTime + pi_bits.pTime
        vTime = pi_lin.vTime + pi_lin.vTime
        
        self.Xi = Xi
        self.pi_lin = pi_lin
        self.pi_bits = pi_bits
        super(SetMemb, self).__init__(crs, proof,pTime,vTime)


class SetMembSimple(SetMemb):

    # Proof that the openings of nAgg GS commitments open to elements in a set of size setSize
    def __init__(self, setSize, nAgg, repeated_elements = True):
        super(SetMembSimple, self).__init__(GS.comSize, 1, setSize, GS.rand, nAgg, repeated_elements)


class Shuffle(ProofSystem):
    
    def __init__(self, size):
        
        # eq: \sum_i s_i - \sum_j x_j = 0 
        eq1 = GS('lMMEa', size, 0, 0)
        # s^T C - x^T D = delta_1 v_1 + delta_2 v_2, where (v_1, v_2) is enc scheme public key
        # C = / 0   0   ... 0      \
        #     | 0   0   ... 0      | + r_1 v_1 + r_2 v_2
        #     \ m_1 m_2 ... m_size /
        # eq2 can be expressed as three linear PPEs with size+2 variables in (look at the factor number of times that eq2.poof appears when computing the proof size)
        # the 2 from size+2 comes from the number of random coins of a linear encryption in symmetric groups
        # TODO Generalize for other enc schemes?
        eq2 = GS('lPPE', size+2, 0, 0)
        pi_set = SetMembSimple(size, size, False) # No repeated elements
        
        crs = [size] + GS.crs + pi_set.crs # eq1 and eq2 share the same CRS
        # we consider only commitments of eq2 (which include comms of eq1), 2 GS proofs, set memb proof
        proof = [eq2.getComSize()] + eq1.proof + eq2.proof + eq2.proof + eq2.proof + pi_set.proof # each eq2.prof represents a different coordinate of eq2
        pTime = 2*size # exponentiations for computing (delta_1, delta_2) = s^\top (randCoins(C)-randCoins(D))
        pTime += eq2.getComTime() # exps for computing comms of eq2 (which include comms of eq1)
        pTime += eq1.pTime + 3*eq2.pTime # eq2 represents 3 equations
        pTime += pi_set.pTime
        vTime = eq1.vTime + 3*eq2.vTime + pi_set.vTime
        
        self.eq1 = eq1
        self.eq2 = eq2
        self.pi_set = pi_set
        self.size = size
        super(Shuffle, self).__init__(crs, proof, pTime, vTime)

class Range(ProofSystem):

    # Proof of membership of c = GS.Com(x;r_1,r_2) in [0,2^n-1]
    def __init__(self, n, k):
        d = n**k
        m = log2(d)
        l = n/m
        # eq:  - \sum_{i\in[l]} y_id^{i-1}u_1 = r_1u_2 + r_2u_3
        eq = GS('lMMEa', l+2, l+2, 0)
        pi_set = SetMemb(GS.comSize, 0, m, GS.rand-1, l)

        crs = [GS.crs] + pi_set.crs
        proof = [eq.getComSize()] + eq.proof + pi_set.proof

        pTime = eq.getComTime() + eq.pTime + pi_set.pTime
        vTime = eq.vTime + pi_set.vTime

        self.n = n
        self.c = c
        self.d = d
        self.m = m
        self.l = l
        self.eq = eq
        super(Range, self).__init__(crs,proof,pTime,vTime)

# Proof that x \in \{s_1, ..., s_n\} of Chandran et al. (ICALP 2007)
# plus optimizations for proofs that b \in {0,1}^m st HW(b)=1
class ChanSetMemb(ProofSystem):

    # Proof that for c = GS.Com(x;r_1,r_2)  x \in \{s_1,...,s_n\}
    def __init__(self, size):
        m = sympy.sqrt(size)
        Comb = GS.comSize*m
        Combb = GS.comSize*m

        # b_1+...+b_m = 1 and bb_1+...+bb_m = 1 (I'm using only one instance of GS)
        eq1 = GS('lMME', m, m, 0)
        nEq1 = 2

        # b_i(b_i-1) = 0 and bb_i(bb_i-1) = 0 (again, only one instance)
        eq_bits = GS('QE', 1, 0, 1)
        nEq_bits = 2*m

        # b_1 s_{i,1} + ... + b_m s_{i,m} = s_{i,j*} (one instance)
        eq2 = GS('MME', m+1, m+1, 0) #TODO maybe is a lPPE?
        nEq2 = m

        # bb_1 s_{1,j*} + ... + bb_m s_{m,j*} - c = r_1 u_1 + r_2 u_2
        eq3 = GS('MME', 2*m+2, 2, m)
        nEq3 = 1
                     
        crs = GS.crs

        proof = [Comb] + [Combb] +[nEq1*eq1.getProofSize()] + [nEq_bits*eq_bits.getProofSize()]
        # eq3 has all vars except b and we already considered the bb
        proof += [eq3.getComSize()-Combb]
        proof += [nEq2*eq2.getProofSize()] + [nEq3*eq3.getProofSize()]

        pTime = 2*m*GS.comTime # Comb and Combb
        # eq3 has all vars except b and we already considered the bb
        pTime += eq3.getComTime() - m*GS.comTime 
        pTime += nEq1*eq1.pTime + nEq_bits*eq_bits.pTime + nEq2*eq2.pTime + nEq3*eq3.pTime
        vTime = nEq1*eq1.vTime + nEq_bits*eq_bits.vTime + nEq2*eq2.vTime + nEq3*eq3.vTime

        self.m = m
        self.nEq1 = nEq1
        self.nEq_bits = nEq_bits
        self.nEq2 = nEq2
        self.nEq3 = nEq3
        self.Comb = Comb
        self.Combb = Combb
        self.eq1 = eq1
        self.eq_bits = eq_bits
        self.eq2 = eq2
        self.eq3 = eq3
        super(ChanSetMemb,self).__init__(crs,proof,pTime,vTime)

# Many Chandran proofs, for different sets, using the same b and bb
class ChanSetMembMulti(ChanSetMemb):

    def __init__(self, size, nAgg):
        super(ChanSetMembMulti,self).__init__(size)

        # newProof1 [Comb] + [Combb] +[nEq1*eq1.getProofSize()] + [nEq_bits*eq_bits.getProofSize()] 
        newProof1 = self.proof[:4]
        # The rest of the proofs are repeated nAgg times.
        # (The variables s_{i,j*}), r_1, u_1, and the proofs of eq2 and eq3
        newProof2 = map(lambda M: [nAgg*M[0], M[1]], self.proof[4:])
        self.proof = newProof1 + newProof2
       
        self.pTime += (nAgg-1)*(
                self.eq3.getComSize() - self.m*GS.comTime +
                self.nEq2*self.eq2.pTime + self.nEq3*self.eq3.pTime)
        self.vTime += (nAgg-1)*(self.nEq2*self.eq2.vTime + self.nEq3*self.eq3.vTime)

class ChanRingSignature(object):

    crs = GS.crs
    vk = [[1,1]] # [vk]
    sk = 1
    timeBBsign = 1

    def getCRSSize(self):
        return getLLSize(ChanRingSignature.crs)

    def getVKSize(self):
        return getLLSize(ChanRingSignature.vk)

    # sOTsign: size of OT signature
    # sOTvk: size of the OT signature verification key
    def __init__(self, sizeOTsign = 0, sizeOTvk = 0, timeOTsign = 0, timeOTgen = 0):
        # Boneh-Boyen verification equation
        self.eq_BB = GS('PPE',2, 0, 1)
        self.sizeOTsign = sizeOTsign
        self.sizeOTvk = sizeOTvk
        self.timeOTsign = timeOTsign
        self.timeOTgen = timeOTgen

    # n: size of the ring
    def getSignatureSize(self, n):
        chan = ChanSetMemb(n)
        # signature  = (OTvk, OTsignature, GS.Com(vk), GS.Com(sigma = BB.Sign_{sk}(OTsign)),
        #               proof that Ver_{vk}(sigma,Tvk) = 1, proof that vk \in {vk_1,...vk_n})
        signSize = self.sizeOTvk + self.sizeOTsign + 2*GS.comSize + self.eq_BB.getProofSize() + chan.getProofSize()
        return signSize

    # Number of exponentiations required for computing one signature
    def getSignatureTime(self, n):
        chan  = ChanSetMemb(n)
        signTime = self.timeOTgen + self.timeOTsign + 2*GS.comTime + ChanRingSignature.timeBBsign + self.eq_BB.pTime + chan.pTime
        return signTime

    # Number of pairings required for verification (assuming that verifying the OTsign requires no pairigns)
    def getVerTime(self, n):
        chan = ChanSetMemb(n)
        return self.eq_BB.vTime + chan.vTime

class RingSignature(object):

    crs = GS.crs
    vk =  [[1,1], [2,1], [2,1]] # ([vk],[a],a[vk])
    sk = 1
    timeBBsign = 1

    def getCRSSize(self):
        return getLLSize(RingSignature.crs)

    def getVKSize(self):
        return getLLSize(RingSignature.vk)

    def __init__(self, sizeOTsign, sizeOTvk, timeOTsign = 0, timeOTgen = 0):
        # Boneh-Boyen verification equation
        self.eq_BB = GS('PPE', 2, 0, 1)
        self.sizeOTsign = sizeOTsign
        self.sizeOTvk = sizeOTvk
        self.timeOTsign = timeOTsign
        self.timeOTgen = timeOTgen

    # n: size of the ring
    def getSignatureSize(self, n):
        m = sympy.cbrt(n)
        # 2 proofs of membership in sets of size n^{2/3}
        chan = ChanSetMembMulti(m**2, 2)
        # 1 proof of membership in a set of size n^{1/3}
        chan2 = ChanSetMembMulti(m, 2)
        # [kappa_1][z_1]+...+[kappa_m][z_m] = [y][1]
        eq_kappa = GS('PPE', m+1, 1, m)
        # [z_1]+...+[z_m] = [x]
        # FIXME Falta la ecuacion [z_{i,2}][1] = [z_{i,1}][z_{i,1}]
        eq_z = GS('lMMEa', m+1, m+1, 0)

        # signature = (OTvk, OTsignature, GS.Com(vk), GS.Com(sigma = BB.Sign_{sk}(OTvk)),
        #              proof that Ver_{vk}(OTvk,sigma)=1, GS.Com([x]), GS.Com([y]),
        #              proof that [x] \in S, proof that [y]\in S',
        #              GS.Com([kappa_1]), ..., GS.Com([kappa_m]), GS.Com([z_1]), ..., GS.Com([z_m])),
        #              proof of eq_kappa, proof of eq_z, proof that [vk] \in \{[kappa_1], ...,[kappa_m]\}
        signSize = self.sizeOTvk + self.sizeOTsign + 2*GS.comSize + self.eq_BB.getProofSize()
        # GS.Com([x]) and GS.Com([y]) (note that both [x] and [y] are vectors of size 2)
        signSize += 4*GS.comSize
        # proofs of membership in S_1 and S_2 reusing b and bb
        signSize += chan.getProofSize()
        # Commitments to [kappa_1],...,[kappa_m] and to [z_1],...[z_m] (note that [z_i] is a vector of size 2)
        signSize += m*GS.comSize + 2*m*GS.comSize
        # proofs that \sum_{i\in[m]} [\kappa_i][z_i] = [y][1] and that \sum_{i\in[m]} [z_i] = [x] (note that [z_i] is a vector)
        signSize += 2*eq_kappa.getProofSize() + 2*eq_z.getProofSize()
        #proof that [vk] belongs to \{[kappa_1],...,[kappa_m]\}
        signSize += chan2.getProofSize()
        return signSize

    # Number of exponentiations required for computing one signature
    def getSignatureTime(self, n):
        m = sympy.cbrt(n)
        chan = ChanSetMembMulti(m**2,2)
        chan2 = ChanSetMembMulti(m,2)
        eq_kappa = GS('PPE',m+1, 1, m)
        eq_z = GS('lMMEa', m+1, m+1, 0)

        signTime = self.timeOTgen + self.timeOTsign + 2*GS.comTime + ChanRingSignature.timeBBsign + self.eq_BB.pTime
        # GS.Com([x]) and GS.Com([y]) (note that [x] and [y] are vectors of size 2)
        signTime += 4*GS.comTime
        # proofs of membership in S_1 and S_2
        signTime += chan.pTime
        # Commitments to [kappa_1],...,[kappa_m] and to [z_1],...[z_m] (note that [z_i] is a vector)
        signTime += m*GS.comTime + 2*m*GS.comTime
        # proofs that \sum_{i\in[m]} [\kappa_i][z_i] = [y][1] and that \sum_{i\in[m]} [z_i] = [x] (note that [z_i] is a vector)
        signTime += 2*eq_kappa.pTime + 2*eq_z.pTime
        #proof that [vk] belongs to \{[kappa_1],...,[kappa_m]\}
        signTime += chan2.pTime

        return signTime

    # Number of pairings required for verification (assuming that verifying the OTsign requires no pairins)
    def getVerTime(self, n):
        m = sympy.cbrt(n)
        chan = ChanSetMembMulti(m**2,2)
        chan2 = ChanSetMembMulti(m,2)
        eq_kappa = GS('PPE',m+1, 1, m)
        eq_z = GS('lMMEa', m+1, m+1, 0)
        return self.eq_BB.vTime + chan.vTime + 2*eq_kappa.vTime + 2*eq_z.vTime + chan2.vTime

def plot():

    p1

def test():
    (n,c) = sympy.symbols('n,c')
    sympy.init_printing()
    rp = Range(n,c)
    print rp.crs[0]


