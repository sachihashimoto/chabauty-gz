def pHeight(E,p,D, prec):
    #idea is to break up Lp'(E/K, 1) = product of the MTT of E, Etwist as above and then the vanishing of
    #Lp(E, 1) by BSD plus the interpolation formula this is equal to Lp'(E, 1) L'(E, 1)/Omega_E^+ * const
    periods=E.minimal_model().period_lattice()
    Ereal = periods.omega()
    Evol = periods.complex_area()

    Etwist = E.quadratic_twist(D)
    Etwistperiods = Etwist.minimal_model().period_lattice()

    Etwistreal=Etwistperiods.omega()

    Lvaltwist = Etwist.lseries().L_ratio() #uses interpolation
    print("computed L ratio for E twist")
    print(Lvaltwist)

    pconst=(2*Evol) /(Ereal *Etwistreal *N(sqrt(-D))) 
    #Assumes stevens conjecture to compute modular degree
    print("this is the period constant")
    print(pconst)

    cf = QQ(pconst).continued_fraction() #rewrite with algdep?
    cfclass = cf.parent()
    conv=[]
    for c in cf:
        if c <100:
            conv.append(c)
        else: break
    pconst = cfclass(conv).value()

    L=E.padic_lseries(p, precision=prec, implementation = 'pollackstevens')
    Lser=L.series(prec)
    print("finished computing L series for E")
    print(Lser)

    Lval0 =Lser[1] #finds derivative of the L-series

    Lprod =  Lvaltwist* Lval0

    alpha =E.padic_lseries(p).alpha()
    alphafactor = (1-1/alpha)^2
    print(alphafactor)

    R=Qp(p,prec)
    logfactor=log(R(p+1)) 

    constPR = (alphafactor * pconst)^(-1) #this solves for the height of the Heegner point exactly

    ht = 1/2*(constPR * logfactor * Lprod)

    return ht