Qring.<q0>=QQ[]
Qring = FractionField(Qring)
Qringx.<tempx,tempy> = Qring[]
R.<epsilon,psi> = QuotientRing(Qringx, Qringx.ideal(tempx^2 - 1, tempy^2-1))

###############################################################################
# Implements the R-algebra structure of R[Typ]                                #
#                                                                             #
# An element f of R[Typ_r] is represented by a dictionary df where:           #
# - keys are of the form tuple(e,s) for tuples e,s of length r                #
# - values are elements of R                                                  #
# For such a dictionary df, the corresponding element is                      #
#       f = sum_{(e,s) keys of df} delta_s(e) * df[(e,s)]                     #
###############################################################################
class SphericalFunction:
    d = None
    
    def clean(self):
        self.d = {x:y for x,y in self.d.items() if y != 0}
    
    def __init__(self, e = None, s = None):
        if e == None:
            self.d = {}
        else:
            if s == None:
                s = [1]*len(e)
            self.d = {(tuple(e), tuple(s)): 1}
    
    def __eq__(self, other):
        return self.d == other.d
    
    def __add__(self, other):
        ans = SphericalFunction()
        ans.d = {k: self.d.get(k, 0) + other.d.get(k, 0) for k in set(self.d) | set(other.d)}
        ans.clean()
        return ans
    
    def __sub__(self, other):
        ans = SphericalFunction()
        ans.d = {k: self.d.get(k, 0) - other.d.get(k, 0) for k in set(self.d) | set(other.d)}
        ans.clean()
        return ans
    
    def __mul__(self, other):
        if isinstance(other, SphericalFunction):
            ans = SphericalFunction()
            for key1 in self.d:
                for key2 in other.d:
                    key = (key1[0]+key2[0], key1[1]+key2[1])
                    ans += SphericalFunction(key[0], key[1]) * (self.d[key1] * other.d[key2])
            return ans
        else:
            ans = SphericalFunction()
            ans.d = {k: self.d[k] * other for k in set(self.d)}
            ans.clean()
            return ans
    
    def terms(self):
        return self.d.keys()
    def __getitem__(self, key):
        return self.d[key]

    
    
class Straightener:
    case = None
    mod = None
    q = None
    Sign = None
    
    caching = None
    straightenCache = None
    
    def __init__(self, case, mod):
        assert case in ['uH','S','A']
        assert mod in ['natural','flat','sharp']
        if case == 'A':
            assert mod != 'sharp'
        self.case = case
        self.mod = mod
        
        self.q = q0
        if case == 'uH':
            self.q = q0^2
    
        self.Sign = [1]
        if case == 'S':
            self.Sign = [1,-1]
        
        self.caching = True
        self.straightenCache = {}
    
    ###########################################################################
    # Define the elements in [Hironaka's Conjecture, Proposition 4.11]        #
    ###########################################################################
    def r(self, a, b, s1, s2):
        assert a < b or (a == b and s1 != s2)
        q = self.q
        
        if self.case == 'uH':
            f  = SphericalFunction([a,  b  ]) * ( 1            )
            f += SphericalFunction([a+1,b-1]) * (-1            )
            f += SphericalFunction([b,  a  ]) * (-(-q0)^(b-a-1))
            f += SphericalFunction([b-1,a+1]) * ( (-q0)^(b-a-1))
            if b == a + 1:
                f *= (1/2)
            return f
        elif self.case == 'S':
            if (b-a)%2 == 1:
                f  = SphericalFunction([a,  b  ], [s1,s2]) * ( 1            )
                f += SphericalFunction([a+1,b-1], [s2,s1]) * (-1            )
                f += SphericalFunction([b,  a  ], [s2,s1]) * (-q^((b-a-1)/2))
                f += SphericalFunction([b-1,a+1], [s1,s2]) * ( q^((b-a-1)/2))
                if b == a + 1:
                    f *= (1/2)
                return f
            elif s1 != s2:
                f  = SphericalFunction([a,b], [s1,s2]) * (1          )
                f += SphericalFunction([b,a], [s1,s2]) * (q^((b-a)/2))
                if b == a:
                    f *= (1/2)
                return f
            else:
                f  = SphericalFunction([a,  b  ], [ s1, s2]) * ( 1                      )
                f += SphericalFunction([a+1,b-1], [ s2, s1]) * (-1                      )
                f += SphericalFunction([a+1,b-1], [-s2,-s1]) * (-epsilon                )
                f += SphericalFunction([a+2,b-2], [-s2,-s1]) * ( epsilon                )
                f += SphericalFunction([b,  a  ], [-s1,-s2]) * ( q^((b-a)/2-1) * epsilon)
                f += SphericalFunction([b-1,a+1], [-s1,-s2]) * (-q^((b-a)/2-1) * epsilon)
                f += SphericalFunction([b-1,a+1], [ s1, s2]) * (-q^((b-a)/2-1)          )
                f += SphericalFunction([b-2,a+2], [ s1, s2]) * ( q^((b-a)/2-1)          )
                if b == a + 2:
                    f *= (1/2)
                return f
        elif self.case == 'A':
            f  = SphericalFunction([a,  b  ]) * ( 1            )
            f += SphericalFunction([a+1,b-1]) * (-1            )
            f += SphericalFunction([b,  a  ]) * (-q^(2*(b-a-1)))
            f += SphericalFunction([b-1,a+1]) * ( q^(2*(b-a-1)))
            if b == a + 1:
                f *= (1/2)
            return f
    
    def D(self, e, s = None):
        if s == None:
            s = [1]*len(e)
        assert len(e) == 3 and len(s) == 3
        a,b,c    = e
        s1,s2,s3 = s
        f  = SphericalFunction([a],[s1]) * self.r(b, c, s2, s3)
        f -= self.r(a, b, s1, s2) * SphericalFunction([c],[s3])
        return f
    ###########################################################################
    # Define the elements in [FJ spherical functions, Proposition 4.2.7]      #
    ###########################################################################
    def rFS(self, a, s):
        assert a < 0
        q = self.q
        if self.case == 'uH' and self.mod == 'flat':
            f  = SphericalFunction([ a  ]) * ( 1        )
            f += SphericalFunction([ a+2]) * (-1        )
            f += SphericalFunction([-a  ]) * (-q0^(-a-1))
            f += SphericalFunction([-a-2]) * ( q0^(-a-1))
            if a == -1:
                f *= (1/2)
            return f
        elif self.case == 'uH' and self.mod == 'sharp':
            f  = SphericalFunction([ a  ]) * ( 1          )
            f += SphericalFunction([ a+2]) * (-1          )
            f += SphericalFunction([-a  ]) * (-(-q)^(-a-1))
            f += SphericalFunction([-a-2]) * ( (-q)^(-a-1))
            if a == -1:
                f *= (1/2)
            return f
        elif self.case == 'S' and self.mod == 'flat':
            f  = SphericalFunction([ a], [s]) * ( 1)
            f += SphericalFunction([-a], [s]) * (-1)
            return f
        elif self.case == 'S' and self.mod == 'sharp':
            if a % 2 == 1:
                f  = SphericalFunction([ a  ], [s]) * ( 1           )
                f += SphericalFunction([ a+2], [s]) * (-1           )
                f += SphericalFunction([-a  ], [s]) * (-q^((-a-1)/2))
                f += SphericalFunction([-a-2], [s]) * ( q^((-a-1)/2))
                if a == -1:
                    f *= (1/2)
                return f
            else:
                f  = SphericalFunction([ a  ], [ s]) * ( 1               )
                f += SphericalFunction([ a+2], [ s]) * (-1               )
                f += SphericalFunction([ a+2], [-s]) * (-psi             )
                f += SphericalFunction([ a+4], [-s]) * ( psi             )
                f += SphericalFunction([-a  ], [-s]) * ( q^(-a/2-1) * psi)
                f += SphericalFunction([-a-2], [-s]) * (-q^(-a/2-1) * psi)
                f += SphericalFunction([-a-2], [ s]) * (-q^(-a/2-1)      )
                f += SphericalFunction([-a-4], [ s]) * ( q^(-a/2-1)      )
                if a == -2:
                    f *= (1/2)
                return f
        elif self.case == 'A' and self.mod == 'flat':
            f  = SphericalFunction([ a  ]) * ( 1                 )
            f += SphericalFunction([ a+1]) * (-(q+1)             )
            f += SphericalFunction([ a+2]) * ( q                 )
            f += SphericalFunction([-a  ]) * ( q^(-3*a-3) * q    )
            f += SphericalFunction([-a-1]) * (-q^(-3*a-3) * (q+1))
            f += SphericalFunction([-a-2]) * ( q^(-3*a-3)        )
            if a == -1:
                f *= (1/2)
            return f
        else:
            assert False
    
    def DFS(self, e, s = None):
        if s == None:
            s = [1]*len(e)
        assert len(e) == 2 and len(s) == 2
        a,b   = e
        s1,s2 = s
        f  = self.r(a, b, s1, s2)
        f -= SphericalFunction([a], [s1]) * self.rFS(b, s2)
        return f



    ###########################################################################
    # Implements the straightening maps in                                    #
    # [Hironaka's Conjecture, Proposition 4.11] and                           #
    # [FJ spherical functions, Proposition 4.2.7]                             #
    ###########################################################################
    # straighten the function f = {term:1}
    def straightenTerm(self, e, s):
        key = (e, s)
        if self.caching and key in self.straightenCache:
            return self.straightenCache[key]
        l = len(e)
        for i in range(0,l-1):
            # if there is a pair which is not in standard order, apply the
            # straightening relation and recursively straighten the result
            if e[i] < e[i+1] or (e[i] == e[i+1] and s[i] != s[i+1]):
                eBefore     = tuple([e[j] for j in range(0,  i)])
                eAfter      = tuple([e[j] for j in range(i+2,l)])
                sBefore     = tuple([s[j] for j in range(0,  i)])
                sAfter      = tuple([s[j] for j in range(i+2,l)])
                termBefore  = SphericalFunction(eBefore,       sBefore      )
                termAfter   = SphericalFunction(eAfter,        sAfter       )
                termMiddle  = SphericalFunction([e[i],e[i+1]], [s[i],s[i+1]])
                termMiddle -= self.r(e[i], e[i+1], s[i], s[i+1])
                ans = self.straighten(termBefore * termMiddle * termAfter)
                if self.caching:
                    self.straightenCache[key] = ans
                return ans
        # in cases flat and sharp, if the last term is less than 0, apply the
        # straightening relation and recursively straighten the result
        if self.mod in ['flat','sharp'] and e[l-1] < 0:
            i = l-1
            eBefore    = tuple([e[j] for j in range(0,i)])
            sBefore    = tuple([s[j] for j in range(0,i)])
            termEnd    = SphericalFunction([e[i]], [s[i]])
            termEnd   -= self.rFS(e[i], s[i])
            termBefore = SphericalFunction(eBefore, sBefore)
            ans = self.straighten(termBefore * termEnd)
            if self.caching:
                self.straightenCache[key] = ans
            return ans
        return SphericalFunction(e, s)

    def straighten(self, f):
        ans = SphericalFunction()
        for term in f.terms():
            ans += self.straightenTerm(term[0], term[1]) * f[term]
        return ans




##############################################################################
# Verifies the end of the proof of [Hironaka's Conjecture, Proposition 4.11] #
##############################################################################
S = Straightener('uH', 'natural')
assert S.straighten( S.D([0,1,2]) ) == SphericalFunction()

S = Straightener('S','natural')
for s1 in S.Sign:
    assert         S.straighten( S.D([0, 0, 0], [-s1, s1,-s1]) ) == SphericalFunction()
    assert         S.straighten( S.D([0, 0, 2], [-s1, s1, s1]) ) == SphericalFunction()
    assert         S.straighten( S.D([0, 2, 4], [ s1, s1, s1]) ) == SphericalFunction()
    for s2 in S.Sign:
        assert     S.straighten( S.D([0, 0, 1], [-s1, s1, s2]) ) == SphericalFunction()
        assert     S.straighten( S.D([0, 1, 3], [ s1, s2, s2]) ) == SphericalFunction()
        for s3 in S.Sign:
            assert S.straighten( S.D([0, 1, 2], [ s1, s2, s3]) ) == SphericalFunction()

S = Straightener('A','natural')
assert S.straighten( S.D([0,1,2]) ) == SphericalFunction()

##############################################################################
#Verifies the end of the proof of [FJ spherical functions, Proposition 4.2.7]#
##############################################################################

S = Straightener('uH','flat')
assert S.straighten( S.DFS([-2,-1]) ) == SphericalFunction()

S = Straightener('uH','sharp')
assert S.straighten( S.DFS([-2,-1]) ) == SphericalFunction()

S = Straightener('S','flat')
for s1 in S.Sign:
    assert     S.straighten( S.DFS([-1, -1], [-s1, s1]) ) == SphericalFunction()
    assert     S.straighten( S.DFS([-2, -2], [-s1, s1]) ) == SphericalFunction()
    assert     S.straighten( S.DFS([-3, -1], [ s1, s1]) ) == SphericalFunction()
    assert     S.straighten( S.DFS([-4, -2], [ s1, s1]) ) == SphericalFunction()
    for s2 in S.Sign:
        assert S.straighten( S.DFS([-2, -1], [ s1, s2]) ) == SphericalFunction()
        assert S.straighten( S.DFS([-3, -2], [ s1, s2]) ) == SphericalFunction()

S = Straightener('S','sharp')
for s1 in S.Sign:
    assert     S.straighten( S.DFS([-1, -1], [-s1, s1]) ) == SphericalFunction()
    assert     S.straighten( S.DFS([-2, -2], [-s1, s1]) ) == SphericalFunction()
    assert     S.straighten( S.DFS([-3, -1], [ s1, s1]) ) == SphericalFunction()
    assert     S.straighten( S.DFS([-4, -2], [ s1, s1]) ) == SphericalFunction()
    for s2 in S.Sign:
        assert S.straighten( S.DFS([-2, -1], [ s1, s2]) ) == SphericalFunction()
        assert S.straighten( S.DFS([-3, -2], [ s1, s2]) ) == SphericalFunction()

S = Straightener('A','flat')
assert S.straighten( S.DFS([-2,-1]) ) == SphericalFunction()

print('All done')
