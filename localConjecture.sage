print('---Straightening check:')
load('straightening.sage')

from sage.combinat.q_analogues import q_multinomial
from sage.combinat.q_analogues import q_pochhammer
import copy

RRing.<SS1,SS2,SS3,SS4,SS5,SS6,SS7,SS8,SS9,Tprime,Tprimeinv> = PolynomialRing(Qring)

def SS(i):
    if i == 0:
        return 1
    return RRing('SS'+str(i))

##############################################################################
# Define phi_e                                                               #
##############################################################################
def Q(n,m,l):
    return (-q0)^(n*l)*q_multinomial([n,2*m,l],q=-q0)*q_pochhammer(m,-q0,q=q0^2)

def allnml(e,f):
    if len(f)==0:
        yield ({},{},{})
        return
    i = f[0]
    limax = min(f.count(i), e.count(i+2))
    mimax = (min(f.count(i), e.count(i+1))/2).floor()
    nimax = min(f.count(i), e.count(i))
    for mi in range(0,mimax+1):
        for ni in range(0,min(nimax,f.count(i)-2*mi)+1):
            li = f.count(i)-2*mi-ni
            if li > limax:
                continue
            fnew = list(f)
            for j in range(0,ni+2*mi+li):
                fnew.remove(i)
            fnew = tuple(fnew)
            enew = list(e)
            for j in range(0,2*mi):
                enew.remove(i+1)
            for j in range(0,ni):
                enew.remove(i)
            for j in range(0,li):
                enew.remove(i+2)
            enew = tuple(enew)
            for (nnew,mnew,lnew) in allnml(enew,fnew):
                n=copy.deepcopy(nnew)
                m=copy.deepcopy(mnew)
                l=copy.deepcopy(lnew)
                n[i] = ni
                m[i] = mi
                l[i] = li
                yield (n,m,l)
    return


dplusCache = {}
def dplus(e,f):
    if (sum(e)-sum(f)) % 2 == 1:
        return 0
    e0 = e[0]
    f = tuple([fi-e0 for fi in f])
    e = tuple([ei-e0 for ei in e])
    if (e,f) in dplusCache:
        return dplusCache[(e,f)]
    ans = 0
    for (n,m,l) in allnml(e,f):
        term = 1
        for i in set(n.keys()) | set(m.keys()) | set(l.keys()):
            term = term * Q(n.get(i,0), m.get(i,0), l.get(i,0))
        exp = 0
        indices = set(m.keys()) | set(l.keys())
        for i in indices:
            for j in indices:
                if i > j:
                    exp = exp + (m.get(i,0) + l.get(i,0)) * (m.get(j,0) + n.get(j,0))
        term = term * q0^(2*exp)
        ans = ans + term
    dplusCache[(e,f)] = ans
    return ans

def ismore(e,f):
    for i in range(0,len(e)):
        if e[i] < f[i]:
            return False
    return True

def between(e,f):
    if len(f) == 0:
        return
    if e[0] < f[0]:
        return
    if len(f) == 1:
        for g in range(f[0],e[0]+1):
            yield (g,)
        return
    for g0 in range(f[0],e[0]+1):
        enew = list(e)
        enew.remove(e[0])
        enew=tuple(enew)
        fnew = list(f)
        fnew.remove(f[0])
        fnew=tuple(fnew)
        for gnew in between(enew,fnew):
            if g0 < gnew[0]:
                continue
            g = copy.deepcopy(gnew)
            g = list(g)
            g = [g0]+g
            g = tuple(g)
            yield g
    return
def betweenpar(e,f):
    if (sum(e)-sum(f)) % 2 == 1:
        return
    for g in between(e,f):
        if (sum(e)-sum(g)) % 2 == 1:
            continue
        yield g

dCache = {}
def dterm(e,f):
    if e==f:
        return 1
    if ismore(e,f)==False:
        return 0
    e0 = e[0]
    f = tuple([fi-e0 for fi in f])
    e = tuple([ei-e0 for ei in e])
    if (e,f) in dCache:
        return dCache[(e,f)]
    ans = 0
    for g in betweenpar(e,f):
        if g == f:
            continue
        dif = ((sum(g)-sum(f))/2).floor()
        ans = ans - dterm(e,g)*dplus(g,f)*q0^(dif^2-dif)*(-1)^(dif)
    dCache[(e,f)] = ans
    return ans


phitermCache = {}
def phiterm(e,f):
    if e==f:
        return 1
    if ismore(e,f)==False:
        return 0
    e0 = e[0]
    f = tuple([fi-e0 for fi in f])
    e = tuple([ei-e0 for ei in e])
    if (e,f) in phitermCache:
        return phitermCache[(e,f)]
    ans = 0
    for g in betweenpar(e,f):
        dif = ((sum(g)-sum(f))/2).floor()
        ans = ans + dterm(e,g)*dplus(g,f)*q0^(dif^2+dif)*(-1)^(dif)
    phitermCache[(e,f)] = ans
    return ans

phiCache = {}
def phi(e):
    if e in phiCache:
        return phiCache[e]
    ans = SphericalFunction()
    m = tuple([0]*len(e))
    if sum(e)%2==1:
        m = tuple([1]+[0]*(len(e)-1))
    for f in betweenpar(e,m):
        term = phiterm(e,f)
        ans = ans + SphericalFunction(f)*term
    phiCache[e] = ans
    return ans

simplifiedphiCache = {}
def simplifiedphi(e):
    if e in simplifiedphiCache:
        return simplifiedphiCache[e]
    ans = simplify(phi(e))
    simplifiedphiCache[e] = ans
    return ans

##############################################################################
# Define Hecke operators in case uH flat                                     #
##############################################################################
import itertools
Str = Straightener('uH','flat')

def widetilde(epsilon):
    ans = 0
    for i in range(0, len(epsilon)):
        for j in range(i + 1, len(epsilon)):
            ans = ans + max(0, epsilon[i] - epsilon[j])
    return ans
def d(n):
    return q0^(n^2)
def t2(epsilon, f):
    ans = SphericalFunction()
    for key in f.d:
        newkey = [key[0][i] + 2 * epsilon[i] for i in range(0,len(key[0]))]
        ans = ans + SphericalFunction(newkey) * f.d[key]
    return ans
def t1(epsilon, f):
    ans = SphericalFunction()
    for key in f.d:
        newkey = [key[0][i] + epsilon[i] for i in range(0,len(key[0]))]
        ans = ans + SphericalFunction(newkey) * f.d[key]
    return ans
def Sdual(k, r, f):
    ans = SphericalFunction()
    for epsilon in itertools.product([-1,0,1], repeat=r):
        if epsilon.count(0) != r-k:
            continue
        factor = q0^(2*widetilde(epsilon)) * d(epsilon.count(1)) * d(r-epsilon.count(-1)) / d(epsilon.count(0))
        ans = ans + t2(epsilon,f) * factor
    return Str.straighten(ans)

def pair(f,g):
    ans = 0
    for key in set(f.d.keys()) & set(g.d.keys()):
        ans = ans + f.d[key] * g.d[key]
    return ans

StermCache = {}
# compute the Hecke operator for f = {term:1}
def Sterm(k, r, f):
    assert len(f.d) == 1
    e = list(f.d.keys())[0][0]
    cachekey = (k, r, e)
    if cachekey in StermCache:
        return StermCache[cachekey]
    assert r == len(e)
    temp = Sdual(k, r, SphericalFunction(e))
    ans = SphericalFunction()
    for key in temp.d.keys():
        e = key[0]
        deltae = SphericalFunction(e)
        ans = ans + deltae * pair(f, Sdual(k, r, deltae))
    StermCache[cachekey] = ans
    return ans
# compute the Hecke operators as in [FJ Spherical Functions, Theorem 4.7.1]
def S(k, r, f):
    ans = SphericalFunction()
    if len(f.d) == 0:
        return ans
    for key in f.d:
        ans = ans + Sterm(k, r, SphericalFunction(key[0])) * f.d[key]
    return ans

def intertdual(r, f):
    ans = SphericalFunction()
    for epsilon in itertools.product([-1,1], repeat=r):
        exp = 0
        for i in range(0,r):
            if epsilon[i] == 1:
                exp = exp + 2*(r-i-1) + 1
        ans = ans + t1(epsilon,f) * (q0^exp)
    return Str.straighten(ans)
# compute the intertwining operator as in [FJ Spherical Functions, Theorem 4.4.6]
def intert(r, f):
    ans = SphericalFunction()
    if len(f.d) == 0:
        return ans
    maxei = 0
    for key in f.d:
        maxei = max(maxei, key[0][0])
        paritysum = sum(key[0])
    maxei = maxei + 2
    naivemax = [maxei]*r
    naivemax = tuple(naivemax)
    naivemin = [0]*r
    naivemin = tuple(naivemin)
    for e in between(naivemax,naivemin):
        deltae = SphericalFunction(e)
        ans = ans + deltae * pair(f, intertdual(r, deltae))
    return ans

##############################################################################
# Write a spherical function in terms of the basis given in                  #
# [FJ Spherical Functions, Theorem 5.1.3]                                    #
##############################################################################
simplifyCache = {}
def simplify(f):
    if len(f.d) == 0:
        return f
    ans = SphericalFunction()
    for key in f.d.keys():
        ans = ans + simplifyTerm(SphericalFunction(key[0])) * f[key]
    return ans
def simplifyTerm(f):
    assert len(f.d)==1

    e = list(f.d.keys())[0][0]
    key = list(f.d.keys())[0]
    if e in simplifyCache:
        return simplifyCache[e]

    r = len(e)
    basis = [e[r-1]%2]
    for i in reversed(range(0,r-1)):
        basis = [basis[0] + (e[i]-e[i+1])%2] + basis
    if tuple(e) == tuple(basis):
        return f
    aa = []
    asum = 0
    for i in reversed(range(0,len(e))):
        newa = (e[i]-basis[i])//2 - asum
        asum = asum + newa
        aa = [newa] + aa

    sub = SphericalFunction(basis)
    add = SphericalFunction(basis)
    for i in range(0,len(e)):
        for j in range(0,aa[i]):
            sub = S(i+1,len(e), sub)
            add = add * SS(i+1)
    sub = sub * f.d[key]
    add = add * f.d[key]
    f = f + add - sub
    
    ans = simplify(f)
    simplifyCache[e] = ans
    return ans

##############################################################################
# Elements in [1st reciprocity law for unitary FJ periods]                   #
##############################################################################
def phibc(r):
    return intert(r, SphericalFunction(tuple([0]*r)))

def Tprimepoly(rr):
     ans = 0
     for i in range(0,rr):
        ans = ans + SS(i)*(-1)^(rr-i-1)*(rr-i)*(q0^2+1)^(rr-i-1)*q0^((rr-i)^2-(rr-i))
     return ans

def Tpoly(rr):
    ans = 0
    for i in range(0,rr+1):
        ans = ans + SS(i)*(-1)^(rr-i)*(q0^2+1)^(rr-i)*q0^((rr-i)^2-(rr-i))
    return ans

##############################################################################
# Groebner basis computations                                                #
##############################################################################

import sage.libs.singular.function_factory
groebner = sage.libs.singular.function_factory.ff.groebner
from sage.modules.free_module_element import FreeModuleElement_generic_dense as module_elem
from sage.libs.singular.option import opt
import datetime
opt['prot'] =  True
opt['redSB'] = True

def basisEs(r):
    if r == 0:
        yield []
        return
    if r == 1:
        yield (0,)
        yield (1,)
        return
    for eold in basisEs(r-1):
        yield tuple([eold[0]] + list(eold))
        yield tuple([eold[0]+1] + list(eold))
def basisEs2(r): #only yields the ones in the same parity as phibc(r)
    for key in list(basisEs(r)):
        if (sum(key)-r)%2==0:
            yield key
        
# Compute groebner bases, by default on the submodule corresponding to phibc(r)
# Phi: list of e for which we are including phi(e)
# track: boolean that if true, introduce an extra dimension for each element in
#        Phi which keeps track of the linear combinations; the extra dimensions
#        are before the normal ones
# opt: if 'T', also includes the elements Tpoly(r); if 'Tprime', also includes the
#      elements Tprimepoly(r)*Tprimeinv - 1; if 'both', computes on both submodules,
#      not just the one corresponding to phibc(r)
def computeG(Phi, track, opt = ['T','Tprime']):
    if len(Phi) == 0:
        return None
    r = len(Phi[0])
    rr = len(Phi[0]) - 1
    if 'both' in opt:
        rr = rr + 1
    basislen = 2^(rr)
    N = basislen
    if track:
        N = N + len(Phi)
    M=RRing^(N)
    elements = []
    
    tstart = datetime.datetime.now()
    index = N-basislen-len(Phi)
    for e in Phi:
        doIprint = True
        if e in simplifiedphiCache:
            doIprint = False
        tt1 = datetime.datetime.now()
        temp = simplifiedphi(e)
        tt2 = datetime.datetime.now()
        if doIprint:
            print(e,'simplifiedphi',tt2-tt1)
        temparray = [0]*(N-basislen)
        if 'both' in opt:
            for key in basisEs(r):
                temparray += [temp.d.get((key,tuple([1]*r)),0)]
        else:
            for key in basisEs2(r):
                temparray += [temp.d.get((key,tuple([1]*r)),0)]
        if track:
            temparray[index] = 1
        elements += [module_elem(M, temparray)]
        index = index + 1

    for i in range(0, basislen):
        temparray1 = [0]*(N)
        temparray2 = [0]*(N)
        temparray1[N-1-i] = Tprimepoly(r)*Tprimeinv-1
        temparray2[N-1-i] = Tpoly(r)
        if 'T' in opt:
            elements = [module_elem(M, temparray2)] + elements
        if 'Tprime' in opt:
            elements = [module_elem(M, temparray1)] + elements
    
    tt1 = datetime.datetime.now()
    gbasis = groebner(Sequence(elements))
    tt2 = datetime.datetime.now()
    print('Groebner',tt2-tt1)
    tend = datetime.datetime.now()
    print('Elapsed time:',tend-tstart)
    return gbasis

##############################################################################
# Testing the conjectures in [1st reciprocity law for unitary FJ periods]    #
##############################################################################
def alles(r):
    if r == 0:
        yield []
        return
    
    i = 0
    while True:
        for eold in alles(r-1):
            if len(eold) != 0 and eold[0] > i:
                break
            yield tuple([i]+list(eold))
        i = i+1

def esuntil(rr,k,both=False):
    ans = []
    for e in alles(rr):
        if e[0] > k:
            break
        if e[len(e)-1] == 0:
            continue
        if (sum(e) - rr)%2==0 or both:
            ans = ans + [e]
    return ans

# test whether the span of Phi contains phibc in the weak sense
def simpleTest(Phi):
    r = len(Phi[0])
    gbasis = computeG(Phi,False)
    f = phibc(r)
    temparray = []
    for key in basisEs2(r):
        temparray += [f.d.get((key,tuple([1]*r)),0)]
    elements = copy.deepcopy(gbasis)
    elements += [module_elem(RRing^(2^(r-1)), temparray)]
    gbasis2 = groebner(Sequence(elements))
    return gbasis == gbasis2
# test whether Phi generates the entire module in the strong sense
def fullGenerationTest(Phi):
    r = len(Phi[0])
    gbasis = computeG(Phi,False,['Tprime','both'])
    count = 0
    for e in basisEs(r):
        evec = [0]*(2^r)
        evec[count] = 1
        if module_elem(RRing^(2^r),evec) not in gbasis:
            return False
        count = count + 1
    return True


# weak conjecture
for r,m in [(1,1),(2,2),(3,3),(4,3),(5,4),(6,4),(7,4)]:
    print()
    print()
    print('---Testing weak conjecture: r = '+str(r)+' with Phi[1,'+str(m)+']')
    assert simpleTest(esuntil(r,m)) == True
    print('---Done')

# strong conjecture
for r,m in [(1,4),(2,4),(3,4),(4,4),(5,5)]:
    print()
    print()
    print('---Testing strong conjecture: r = '+str(r)+' with Phi[1,'+str(m)+']')
    assert fullGenerationTest(esuntil(r,m,True))==True
    print('---Done')
