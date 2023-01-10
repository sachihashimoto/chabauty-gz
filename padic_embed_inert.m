//Basic idea is we take algebraic values then use rubin_BDP makepAdic function to embed using different embedding choices

function setup(p, prec, K, M, KM, injK, emb)

    Qp := pAdicField(p, prec);
    Qpz<z> := PolynomialRing(Qp);
    minpoly:= MinimalPolynomial(KM.1);
    coeffpoly:= Qpz!DefiningPolynomial(M);
    deg:= Degree(coeffpoly);
    rts := Roots(coeffpoly);

    if #rts eq 0 then
        //p doesn't split in coeff field, this works if p is inert
        L<b> := SplittingField(coeffpoly);
        R_L<xL> := PolynomialRing(L);
        rtsL :=Roots(R_L!minpoly);
        r:= rtsL[emb][1];
        embKM := hom<KM -> L|r>;
        print "this embedding is", emb; 
        print ChangePrecision(embKM(M.1),5);
    else
        //p splits in K but not in M
        r:= Roots(Qpz!minpoly)[emb][1];  //change this value to change the embedding that we are doing
        embKM := hom<KM -> Qp|r>;  
    end if;

    OK := MaximalOrder(K);
    pSplitting := Factorization(p*OK);
    primeOverp1 := pSplitting[1][1]; //fix frakp to be the valuation 1 thing
    primeOverp2 := pSplitting[2][1];
    bool, gen1:= IsPrincipal(primeOverp1);
    bool, gen2:= IsPrincipal(primeOverp2);

    if Valuation(embKM(injK(gen1))) eq 1 then
        beta1 := gen1;
        beta2:= gen2;
    else
        beta1 := gen2;
        beta2:= gen1;
    end if;

    return beta1, beta2, embKM; 
end function;


function makepAdic(value, f, p, s, beta1, beta2, embKM)
    //make everything p-adic and construct the Euler factor
    ap:=Coefficient(f,p); //note that AbsEltSeq starts at the first NONZERO coefficient, so the indexing is off, whereas Coefficient(f,n) gives the coefficient of q^n

    value :=embKM(value);
    eulerFactor := 1 - ap * beta1^s *K!beta2^(-2 - s)  + K!beta1^(2 + 2*s - 1) * K!beta2^(-2 - 2*s-1);
    globalEF := (1 - ap  + p)/p;
    globalEF := embKM(KM!(globalEF));
    ef:=embKM(eulerFactor); 
    return value, ef, embKM, globalEF;
end function;

function hzero(B,p,lv)
    //print("computing h(0)");
    //compute h(0) using Theorem 9 mod p^B
    L := Parent(lv[1]);
    outersum :=L!0;
    for j in [1 .. B] do
        innersum := L!0;
        for l in [j .. B] do
            hj:=lv[j]^((p-1) div 2); 
            innersum := innersum + ((-1)^(j-1))*Binomial(l-1,j-1);
        end for;
        outersum := outersum + innersum*hj;
    end for;
    //print(outersum);
    return outersum; //only accurate to p^B
end function;


function findRoot(h0,B,p,l0)
//now l(0) mod p1^B is a (p-1)/2 root of h(0)
//we need to pick the right root by applying prop 7 (ii)
    //print("finding root");
    valh0 := Valuation(h0); 
    h0 := ChangePrecision(h0, B);
    KMp := Parent(h0);
    _<z>:=PolynomialRing(KMp);
    deg := (p-1) div 2;
    roots:=Roots(z^deg - h0);
    newroots:=[];
    if Valuation(l0) gt 0 then
        for r in roots do
            v:= Valuation(r[1]);
            rnew := ChangePrecision(r[1], B - v*2);
            Append(~newroots, rnew);
        end for;
        return newroots; //return all roots, try all possible values
    end if;
    for r in roots do

        if ChangePrecision(r[1],1) eq KMp!ChangePrecision(l0,1) then 
         //  print("this is the root");
          //  print(r[1]);
            return [r[1]];
        end if;
    end for;
    return "failure";
end function;


function mainLoop(f, B, D, p, algans, K, M, KM : emb:=1)
    res :=[];
    a:= KM!K.1;
    injK := hom<K->KM|a>;
    beta1, beta2, embKM :=  setup(p, 5000,  K, M, KM, injK, emb);
    lv:=[ ];
    for i in [1 .. B] do
        QqAns, ef, embedKM, globalEF :=makepAdic(algans[i],f, p, (p - 1)*i-1, beta1, beta2, embKM);
        Append(~lv, QqAns^2 * ef^2);
    end for;

    refvalue:= (p-1) div 2; 

    small_lv:=[ ]; 
    for val in lv do
    	Append(~small_lv,ChangePrecision(val,B)); 
    end for;
    print("list of ell(stuff)");
    print(small_lv);

    l0:= lv[refvalue];
    h0:= hzero(B,p,small_lv); 
    Lp1:=findRoot(h0,B,p,l0);
    print("ell(0)");
    print(Lp1); //This is the special value of the anticyclotomic p-adic L-function under the chosen embedding
    
    print("(Log_f^sigma dq/q yK )^2  under embedding"), emb;
    for ell in Lp1 do
        Append(~res, ell *(globalEF)^(-2)); 
    end for;

    return Lp1, res;
end function;
