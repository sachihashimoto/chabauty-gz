from sage.functions.log import logb

#TODO: add functionality for without torsion points / weierstrass

r"""
Quadratic Chabauty fors elliptic curves over `\QQ` of rank `1`.

Modified code from Francesca Bianchi's code for the elliptic curves computations of [Bia19].
The main functions is `quadratic_chabauty_rank_1`.

REFERENCES:

- [Bia19] \F. Bianchi, "Quadratic Chabauty for (bi)elliptic curves
  and Kim's conjecture".

AUTHORS:

- FRANCESCA BIANCHI (started: April 2018; this version: March 2019)

- SACHI HASHIMOTO (August 2020) changed height implementation to double integrals and added a better p-adic power series solver

"""

############## AUXILIARY FUNCTIONS ##############

import itertools
import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer

def pHeight(E,p,prec):
    '''Computes (up to a rational constant) the p-adic regulator of the elliptic curve E using the Mazur-Tate-Teitelbaum L-function via the method of Perrin-Riou
    p must be an ordinary prime of good reduction for E
    Returns this value of the height along with the unit root of Frobenius'''

    L = E.padic_lseries(p, precision=3)
    Lser= L.series(n=prec)
    Lser1 = Lser[1]
    alpha = L.alpha()
    afactor =(1-alpha^(-1))^(-2)
    R = Qp(p,prec)
    logfactor = log(R(p+1))
    if E.cm_discriminant() == -4:
        u = 2
    elif E.cm_discriminant() == -3:
        u = 3
    else:
        u = 1
    ht = afactor*logfactor*Lser1*u
    return ht, alpha


def findtauofT(E,Eshort,T,K,psi):
    '''Finds a 3-torsion point on the elliptic curve E and returns the local height of the three torsion point as per Balakrishnan--Besser Crelle prop 6.1
    This code a version of .b_to_P_doub_AB from the QC II github repository by Jennifer Balakrishnan
    '''
    EshortK = Eshort.change_ring(K)
    EK = E.change_ring(K)
    Dnew = ZZ(Eshort.discriminant()/E.discriminant())**(ZZ(1)/ZZ(12))
    if T != None:
        #user has provided a 3-torsion point on Eshort
        localhtT = ZZ(1)/ZZ(3)*K(2*T[1]).log() - K(Dnew).log()
        return localhtT, T
    else:
        #go find your own T
        f = EshortK.division_polynomial(3)
        if len(f.roots()) != 0:
            #instead we found a 3-torsion point on this other model
            try:
                T = EshortK.lift_x(f.roots()[0][0]) #try first root, is the y-coord defined?
                localhtT = ZZ(1)/ZZ(3)*K(2*T[1]).log() - K(Dnew).log()
                return localhtT, T
            except (ValueError,IndexError):
                try:
                    T = EshortK.lift_x(f.roots()[1][0]) #try second (third is negative of first, so we give up after this)
                    localhtT = ZZ(1)/ZZ(3)*K(2*T[1]).log() - K(Dnew).log()
                    return localhtT, T
                except (ValueError,IndexError):
                    T = None
                    localhtT = -1
                    return localhtT, T
             #here we adjust by the log of the discriminants -- because we are computing everything on the Short Weierstrass model?  
        else:
            T = None
            localhtT = -1
            return localhtT, T


def findtwoTors(E,Eshort,P,K):
    '''Finds a two-torsion point in the residue disk of P on the short weierstrass model of E base changed to K if possible
    Returns the double integral of w0w1 as per prop 6.1 of Balakrishnan--Besser Crelle
    This code is a version part of the .b_to_P_doub_AB function in QC II github repository by Jennifer Balakrishnan  
    '''

    EshortK = Eshort.change_ring(K)
    EK = E.change_ring(K)
    Dnew = ZZ(Eshort.discriminant()/E.discriminant())**(ZZ(1)/ZZ(12))
    if EshortK.is_in_weierstrass_disc(P):
        T = EshortK.find_char_zero_weier_point(P)
        f = EshortK.hyperelliptic_polynomials()[0]
        fprime = f.derivative()
        ainvs = EshortK.a_invariants()
        inner = fprime(T[0]) -ainvs[0]*T[1]
        localhtT = ZZ(1)/ZZ(4)*K(inner).log() -K(Dnew).log()
    else:
        T = None
        localhtT= -1
    return localhtT, T



def coleman_integrals_on_basis(H, P, Q, inverse_frob, forms, algorithm=None):
    r"""
    Compute the Coleman integrals `\{\int_P^Q x^i dx/2y \}_{i=0}^{2g-1}`.
    The only difference with the built-in function coleman_integrals_on_basis
    is that we input the Frobenius data `(inverse_frob, forms)`.

    INPUT:

    - ``H`` -- a hyperelliptic curve over a `p`-adic field `K`.

    - ``P`` -- a point on `H`.

    - ``Q`` -- a point on `H`.

    - ``inverse_frob`` -- `(M_frob^T-1)^(-1)` where `M_frob` is the matrix of Frobenius
      on Monsky-Washnitzer cohomology, with respect to the basis `(dx/2y, x dx/2y, ...x^{d-2} dx/2y)`
      and with coefficients in `K`.

    - ``forms`` -- list of differentials `\{f_i\}` such that
      `\phi^* (x^i dx/2y) = df_i + M_frob[i]*vec(dx/2y, ..., x^{d-2} dx/2y)`;
      the coefficients of the `f_i` should be in `K`.

    - ``algorithm`` (optional) --  None (uses Frobenius) or teichmuller
      (uses Teichmuller points).

    OUTPUT:

    The Coleman integrals `\{\int_P^Q x^i dx/2y \}_{i=0}^{2g-1}`.

    EXAMPLES:

    This example illustrates how to compute the data `(inverse_frob,forms)` for `H`::

        sage: import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer
        sage: K = H.base_ring()
        sage: M_frob, forms = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(H)
        sage: forms = [form.change_ring(K) for form in forms]
        sage: M_sys = matrix(K, M_frob).transpose() - 1
        sage: inverse_frob = M_sys**(-1)
    """
    K = H.base_ring()
    p = K.prime()
    prec = K.precision_cap()
    g = H.genus()
    dim = 2*g
    V = VectorSpace(K, dim)
    #if P or Q is Weierstrass, use the Frobenius algorithm
    if H.is_weierstrass(P):
        if H.is_weierstrass(Q):
            return V(0)
        else:
            PP = None
            QQ = Q
            TP = None
            TQ = H.frobenius(Q)
    elif H.is_weierstrass(Q):
        PP = P
        QQ = None
        TQ = None
        TP = H.frobenius(P)
    elif H.is_same_disc(P, Q):
        return H.tiny_integrals_on_basis(P, Q)
    elif algorithm == 'teichmuller':
        PP = TP = H.teichmuller(P)
        QQ = TQ = H.teichmuller(Q)
        evalP, evalQ = TP, TQ
    else:
        TP = H.frobenius(P)
        TQ = H.frobenius(Q)
        PP, QQ = P, Q
    if TP is None:
        P_to_TP = V(0)
    else:
        if TP is not None:
            TPv = (TP[0]**g/TP[1]).valuation()
            xTPv = TP[0].valuation()
        else:
            xTPv = TPv = +Infinity
        if TQ is not None:
            TQv = (TQ[0]**g/TQ[1]).valuation()
            xTQv = TQ[0].valuation()
        else:
            xTQv = TQv = +Infinity
        offset = (2*g-1)*max(TPv, TQv)
        if offset == +Infinity:
            offset = (2*g-1)*min(TPv,TQv)
        if (offset > prec and (xTPv < 0 or xTQv < 0) and (H.residue_disc(P) == H.change_ring(GF(p))(0, 1, 0) or H.residue_disc(Q) == H.change_ring(GF(p))(0, 1, 0))):
            newprec = offset + prec
            K = pAdicField(p,newprec)
            A = PolynomialRing(RationalField(),'x')
            f = A(H.hyperelliptic_polynomials()[0])
            from sage.schemes.hyperelliptic_curves.constructor import HyperellipticCurve
            H = HyperellipticCurve(f).change_ring(K)
            xP = P[0]
            xPv = xP.valuation()
            xPnew = K(sum(c * p**(xPv + i) for i, c in enumerate(xP.expansion())))
            PP = P = H.lift_x(xPnew)
            TP = H.frobenius(P)
            xQ = Q[0]
            xQv = xQ.valuation()
            xQnew = K(sum(c * p**(xQv + i) for i, c in enumerate(xQ.expansion())))
            QQ = Q = H.lift_x(xQnew)
            TQ = H.frobenius(Q)
            V = VectorSpace(K,dim)
        P_to_TP = V(H.tiny_integrals_on_basis(P, TP))
    if TQ is None:
        TQ_to_Q = V(0)
    else:
        TQ_to_Q = V(H.tiny_integrals_on_basis(TQ, Q))
    if PP is None:
        L = [-f(QQ[0], QQ[1]) for f in forms]  ##changed
    elif QQ is None:
        L = [f(PP[0], PP[1]) for f in forms]
    else:
        L = [f(PP[0], PP[1]) - f(QQ[0], QQ[1]) for f in forms]
    b = V(L)
    if PP is None:
        b -= TQ_to_Q
    elif QQ is None:
        b -= P_to_TP
    elif algorithm != 'teichmuller':
        b -= P_to_TP + TQ_to_Q
    #M_sys = matrix(K, M_frob).transpose() - 1
    TP_to_TQ = inverse_frob * b
    if algorithm == 'teichmuller':
        return P_to_TP + TP_to_TQ + TQ_to_Q
    else:
        return TP_to_TQ


def Q_lift(CK, Q, p):
    r"""
    Compute the Teichmueller point lifting a given point over `GF(p)`.

    INPUT:

    - ``CK`` -- a hyperelliptic curve over `\QQ_p`.

    - ``Q`` -- a point in `CK(GF(p))`.

    - ``p`` -- the prime of the first two inputs.

    OUTPUT: The point on `CK` lifting `Q` and fixed by Frobenius.
    """
    xQ = Integers()(Q[0])
    yQ = Integers()(Q[1])
    if yQ == 0:
        r = CK.hyperelliptic_polynomials()[0].roots()
        Q_lift = CK(exists(r, lambda a : (Integers()(a[0])-xQ) % p == 0)[1][0],0)
    else:
        K = CK.base_ring()
        xQ = K.teichmuller(K(xQ))
        lifts = CK.lift_x(xQ, all=True)
        for i in range(len(lifts)):
            if (Integers()(lifts[i][1])-yQ) % p == 0:
                Q_lift = lifts[i]
    return Q_lift

def local_heights_at_bad_primes(E, K):
    r"""
    Compute all possible sums of local heights at bad places for an integral point.

    INPUT:

    - ``E`` -- an elliptic curve over `\QQ`. `E` should be given by a
      minimal Weierstrass equation.

    - ``K`` -- `\QQ_p` for some `p` at which `E` has good reduction.

    OUTPUT: A list of all possible values of the sum of the `p`-adic local heights
    away from `p` for an integral point on `E`.
    """
    bad_primes = E.base_ring()(E.integral_model().discriminant()).support()
    W = []
    bad_primes_new = []
    for q in bad_primes:
        if E.tamagawa_number(q) == 1:
            continue
        bad_primes_new.append(q)
        ks = E.kodaira_symbol(q)
        if E.has_additive_reduction(q):
            if ks == KodairaSymbol(3): #III
                W.append([-1/2*(K(q)).log()])
            elif ks == KodairaSymbol(4): #IV
                W.append([-2/3*K(q).log()])
            elif ks == KodairaSymbol(-1): #I0*
                W.append([-K(q).log()])
            elif ks == KodairaSymbol(-4): #IV*
                W.append([-(4/3)*K(q).log()])
            elif ks == KodairaSymbol(-3): #III*
                W.append([-(3/2)*K(q).log()])
            else: #Im*
                if E.tamagawa_number(q) == 2:
                    W.append([-K(q).log()])
                else:
                    n = -5
                    while ks != KodairaSymbol(n):
                        n = n-1
                    m = -n-4
                    W.append([-K(q).log(), -(m+4)/4*K(q).log()])
        else: #multiplicative
            n = 5
            while ks != KodairaSymbol(n):
                n = n+1
            m = n-4
            if E.tamagawa_number(q) == 2:
                W.append([-m/4*K(q).log()])
            else:
                W.append([-i*(m-i)/m*(K(q)).log() for i in range(1, (m/2).floor() + 1)])

    for j in range(len(W)):
        q = bad_primes_new[j]
        if q == 2:
            if E.has_split_multiplicative_reduction(q):
                continue
        W[j] = [0] + W[j]

    W = list(itertools.product(*W))
    possible_sums = []
    for i in W:
        possible_sums.append(sum(list(i)))

    return possible_sums

def sorting_fct(P):
    r"""
    Return `0` if input is a tuple, `1` otherwise.
    """
    if type(P) == tuple:
        return 0
    else:
        return 1

def my_roots_Zpt(f,nprime,p):
    #custom solver p-adic power series that hensel lifts to precision
    #after lifting, one needs to check derivative square does not vanish to precision
    #this is a Sage version of code by Travis Morrison and Sachi Hashimoto in applications.m of the forked Coleman github repository for Coleman integrals on general curves
    #fixes several precision problems from the preovious version
    #in particular the code should now always return the same number of points, no matter the input precision, or an error
    n = nprime
    val = min(x.valuation() for x in f.coefficients())
    Zpn = Zp(p,n-val) 
    Zpt.<t> = PolynomialRing(Zpn)
    Fp = Zpn.residue_field()
    Fps.<s> = PolynomialRing(Fp)
    newf =  0
    for i in f.dict().keys():
        newf = newf + t^i *f.dict()[i]/p^val
    f = Zpt(newf)
    modproots= Fps(f).roots()
    Fproots = []
    for i in range(len(modproots)):
        Fproots.append(modproots[i][0])
    candidates = [[Zpn(Integers()(e)),1] for e in Fproots]
    Zproots = []
    while len(candidates) > 0:
        candidate = candidates.pop(0)
        z = candidate[0]
        Nz = candidate[1]
        znew = Zpt(z+ p^Nz*t)
        g = f.subs(t = znew)
        gval = min(x.valuation() for x in g.coefficients())
        if gval < n - val: #so g is not yet zero to prec
            newg =  0
            for i in g.dict().keys():
                newg = newg + t^i *g.dict()[i]/p^gval
            g = Fps(newg)
            Fproots=g.roots()
            for j in range(len(Fproots)):
                candidates.insert(0,[z+p^Nz*(Zpn(Integers()(Fproots[j][0]))),Nz+1])
        else:
            candidate[0] = candidate[0].add_bigoh(candidate[1]) #fix the precision of the root that found
            Zproots.append(candidate)
    return Zproots

############## MAIN FUNCTION ###############


def quadratic_chabauty_rank_1(E, p, C, T=None):
    r"""
    Do quadratic Chabauty on a rank 1 elliptic curve.

    INPUT:

    - ``E`` -- an elliptic curve over `\QQ` of rank `1`. ASSUME E MINIMAL, required in everything below. (Remove this assumption later.)

    - ``p`` -- an odd prime `\ge 5` of good ordinary reduction for E.

    - ``C`` -- the (p-adic) value of h(P)/log(P)^2 for an infinite order point P in E(Q) tensor Qp to some precision
    
    - ``T`` -- a 3- torsion point on the short weierstrass model of E (over Q_p) (default None)

    OUTPUT:

    A tuple consisting of:

    - A sorted list of all the integral points on E.
      (Warning: if the precision is low, it could happen that an integral
      point is not recognised. In that case, it will appear in the third item of
      the tuple and will be counted in the second one.)

    - The size of `X({\ZZ}_p)^{\prime}_2/<\pm 1> \setminus X(\ZZ)/<\pm 1>`.

    - The list of points in `X(\ZZ_p)^{\prime}_2/<\pm 1> \setminus X(\ZZ)/<\pm 1>`.
      If a point is recognised as algebraic, it is represented as a tuple of
      minimal polynomials/rational numbers. The list is sorted so that the recognised
      algebraic points appear first.
      If `X(\ZZ_p)_2` is trivial because either `E` has good reduction at `q \in \{2,3\}`
      and `E(GF(q))` has size `1` or `E` has split multiplicative reduction at `2` with
      Tamagawa number `1`, then ``trival`` is returned as the third output.

    """
    #Trivial cases:
    if E.has_good_reduction(2) == True:
        if E.Np(2) == 1:
            return [], 0, "trivial"

    if E.has_good_reduction(3) == True:
        if E.Np(3) == 1:
            return [], 0, "trivial"

    if E.has_split_multiplicative_reduction(2) == True:
        if E.kodaira_symbol(2) == KodairaSymbol(5):
            return [], 0, "trivial"

    #Non-trivial cases:
    n = C.precision_relative() #I changed this line
    K = Qp(p, n)
    Zpn = Zp(p, prec = n)
    C = K(C)
    _.<x> = PolynomialRing(Rationals())
    assert E == E.minimal_model()
    Eshort = E.short_weierstrass_model()
    phi = Eshort.isomorphism_to(E)
    EshortK = Eshort.change_ring(K)
    EK=E.change_ring(K)
    psi = E.isomorphism_to(Eshort)
    a4 = Eshort.a4()
    a6 = Eshort.a6()
    [u, r, s, tt] = psi.tuple()
    H = HyperellipticCurve(x^3 + a4*x + a6)
    HK = H.change_ring(K)
    HZpn = H.change_ring(Zpn)
    Hp = H.change_ring(GF(p))
    SK = K[['t']]
    t = SK.gen()
    SK.set_default_prec(n+2) 

    #Compute Frobenius data only once:
    M_frob, forms = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(HK)
    forms = [form.change_ring(K) for form in forms]
    M_sys = matrix(K, M_frob).transpose() - 1
    inverse_frob = M_sys**(-1)

    #compute E2
    assert p > 3
    #Mn = inverse_frob^(-n) #we lose p-adic prec here, maybe
    #a01= Mn[0][1] #this code doesn't agree with sage's computation?
    #a11 = Mn[1][1]
    #E2 = -12*a01/a11  #this didn't agree?
    E2 = E.padic_E2(p,n+2)
    #c = K(1/12*(EK.a1()^2+4*EK.a2()))- E2/12 #this is not correct?
    c = -E2/12 #this currently gives the correct constant term
    #print(c)

    classes_to_consider = [Q for Q in list(Hp.points()) if ZZ(Q[1]) < p/2] #create list of residue disks

    W = local_heights_at_bad_primes(E, K) #This currently assumes that E is minimal
    #print(W)

    Threetors = True
    tauT, T = findtauofT(E,Eshort,T,K,psi)
    if T == None:
        Threetors = False

    points_new_all_classes = []
    all_integral_points = []
    count_extra_points = 0

    for Q in classes_to_consider: #iterate over residue disks
        print(Q)
        if Q == Hp(0, 1, 0):
            continue
        indexQ = classes_to_consider.index(Q)
        R = Q_lift(HK, Q, p)
        RZpn = HZpn(R)
        xR, yR =  HZpn.local_coord(RZpn, prec=n+2) 
        xR = SK(xR)
        yR = SK(yR)
        dx = xR.derivative()
        const_term = coleman_integrals_on_basis(HK, HK(0,1,0), R, inverse_frob, forms)[0]
        log_near_R = (dx/(2*yR)).integral() + const_term #maybe it's only the constant term
        log_near_R = log_near_R(p*t) #this seems to be off by one digit of precision sometimes?
        if Threetors and Q[1] != 0:
            #print("threetors")
            intdoubleTtoR= HK.double_integrals_on_basis(T,R)[1] #doesn't work if R is weierstrass
            intinftoTw1=HK.coleman_integrals_on_basis(HK(0,1,0),T)[1]
            intTtoRw0 = HK.coleman_integrals_on_basis(T,R)[0]
            localhtTor = 2*tauT + 2*intdoubleTtoR +2*intinftoTw1*intTtoRw0 #this is D_2(R) computed through T, why doesn't it need at 1/u squared?
            #Note: w1 is not holomorphic so the first integral here is NOT zero
            #print(localhtTor)
            #print(2*HK.b_to_P_doub_AB(R))
        else:
            #print("twotwors")
            tauT2, T2 = findtwoTors(E,Eshort,R,K) #finds two torsion T in the residue disk of R, computes height of T
            if T2 != None:
                I2 = (xR*xR.derivative()/(2*yR)).integral() #NOTE: must use the xR, yR coordinates bc (0,0) has no local coords at EK
                I1 = (xR.derivative()*I2/(2*yR)).integral()
                intdoubleTtoR = I1(R[1])
                localhtTor = 2*tauT2 + 2*intdoubleTtoR
            else:
                raise ValueError('No 3-torsion point on the short weierstrass model of E and not every residue disk has a 2-torsion point on that model')

        intinftoRw0, intinftoRw1= HK.coleman_integrals_on_basis(HK(0,1,0),R)
        intdoubleRtoz = HK.tiny_double_integrals_on_basis_to_z(R)[1] #an error on this line about z vs t is secretly a precision error
        int0,int1 = HK.tiny_integrals_on_basis_to_z(R)
        #need to compare integral (psi^* dx/2y)^2 vs integral dx/2y, this gives conversion of log on the min model vs log on the short weierstrass model
        log_change = (1/u)^2 #somehow 1/u^2 doesn't give the same value
        #Silverman Ch III table 3.1

        lambda_p_near_R = localhtTor + c*intinftoRw0^2*log_change + 2*intdoubleRtoz(p*t) + 2*int0(p*t)*intinftoRw1 +2*c*intinftoRw0*int0(p*t)*log_change +c*(int0(p*t))^2*log_change
        #first two terms should give tau(R) also those are the only ones that contribute to the constant term
        #localhtTor should agree with 2*Hk.b_to_P_doub_AB(R)
        #then we have tau(R) + clog(R)^2
        #the problem I had before is that when expanding the clog(R)^2 term we need to pull this back via psi to compute the correct log
        #ie this is c*log(R)^2 *(1/u)^2

        lambda_p_near_R = SK(lambda_p_near_R)

        #correct equations when C = log^2/ht
        #hW = [lambda_p_near_R + w for w in W]
        #fW = [hw*log_change^(-1)*C - log_near_R^2 for hw in hW] 

        hW = [lambda_p_near_R + w for w in W] #correct eqns when C = ht/log^2
        fW = [hw - log_change*C*log_near_R^2 for hw in hW] 
       

        #print(log_change*C) 
        #print(lambda_p_near_R)
        #print(log_near_R)
        #print(W)


#replacing gp's polrootspadic with a custom function since the gp function is mysterious / requires high precision
        badroots = []
        goodroots = []
        roots = []
        for f in fW:
            M= f.precision_absolute() #could change to relative?
            fval = min(f[i].valuation(p) for i in range(M)) #now try the strategy from my paper, modified
            negative = True
            nprime = n
            #find true p-adic prec from t-adic prec
            while(negative):
                if (M-3) -  fval - logb(M-3,p) > nprime: #why 3 and not 1? is this somehow because of the +2 earlier? #FIX THIS
                    negative = False
                    break
                nprime = nprime - 1
            fnew = 0
            #print(nprime)
            for i in range(M):
                fnew = fnew +t^i* f[i].add_bigoh(nprime)
            fnew = SK(fnew)
            f = fnew
            #print(fnew)
            roots.append(my_roots_Zpt(f.truncate(M),nprime,p)) #roots are the union of the roots of fW
       
        for (i,f) in enumerate(fW): #check the Hensel condition for every root    
            derivs=[]
            #print(roots[i])
            for R in roots[i]: #see if we can salvage a bad root by checking if R is a good root for at least one f in fW
                Polys.<x> =PolynomialRing(Qp(p,n))
                tR = f.parent().gens()[0]
                tval = f.valuation()
                if tval == 2: #allow double roots at zero? --  I think rho should be an even function when the constant is 0, but double check
                    f= f/tR^(tval-1)
                #print(tval) #it doesn't eval power series but it also doesn't like coercion to polys in Zpn, so this is maybe a hack
                if Polys(f).derivative().subs(x = R[0])^2 ==0 and R not in goodroots:
                    badroots.append(R)
                else:
                    goodroots.append(R)
                    if R in badroots:
                        badroots.remove(R)
            Rnew = [R[0]*p for R in roots[i]]
            points = [HK(xR(K(sage_eval('%s'%t0))), yR(K(sage_eval('%s'%t0)))) for t0 in Rnew]
            pointsneg = [HK(xR(K(sage_eval('%s'%t0))), -yR(K(sage_eval('%s'%t0)))) for t0 in Rnew]
            points = Set(points + pointsneg)
            points = [E.change_ring(K)(u^2*QP[0] + r, u^3*QP[1] + s*u^2*QP[0] + tt) for QP in points]

            integral_points = []
            points_new = []

            for A in points: #tries to recognize the p-adic points as integral vs p-adic (this code is a shortened version of Francesca Bianchi's code with bug fixes)
                try:
                    NIP = E.lift_x(QQ(A[0]))
                    if NIP[1] - A[1] == 0:
                        integral_points.append(NIP)
                    else:
                        NIP = -E(NIP[0],NIP[1])
                        integral_points.append(NIP)
                except ValueError:
                    points_new.append(A)
            if points_new != []:
                for (i,A) in enumerate(points_new):
                    p1 = algdep(A[0],2)
                    p2 = algdep(A[1],2)
                    if p1.is_irreducible() and p2.is_irreducible():
                        if p2.is_constant():
                            Lf = QQ
                        else:
                            Lf.<par> = NumberField(p2)
                        if p1.degree() == 1:
                            try:
                                OTP = E.change_ring(Lf).lift_x(QQ(A[0]))
                                if p2(OTP[1]) == 0 or p2((-OTP)[1]) == 0:
                                    points_new[i] = (QQ(A[0]), p2)
                            except ValueError:
                                pass
                        else:
                            if p1.is_constant():
                                Lf = QQ
                            else:
                                Lf.<par> = NumberField(p1)
                            try:
                                OTP = E.change_ring(Lf).lift_x(par)
                                if p2(OTP[1]) == 0 or p2((-OTP)[1]) == 0:
                                    if p2.degree() == 1:
                                        points_new[i] = (p1, QQ(A[1]))
                                    else:
                                        points_new[i] = (p1, p2)
                                else:
                                    continue
                            except ValueError:
                                continue
            points_new_all_classes.extend(points_new)
            all_integral_points.extend(integral_points)
            count_extra_points += len(points_new)

        if len(badroots)>0: #if there are still bad roots, we do not provably have the answer, raise an exception
            print(badroots)
            raise ValueError("Some root does not satisfy Hensel: try raising the precision of C")
    all_integral_points.sort()
    points_new_all_classes.sort(key=sorting_fct)
    return all_integral_points, count_extra_points, points_new_all_classes