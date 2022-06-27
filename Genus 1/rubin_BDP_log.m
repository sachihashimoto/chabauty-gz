load "../canring.m";
load "../rubin_BDP_log_X0.m";


function makepAdic(value, p, prec, f, s, k, D, K)
    //make everything p-adic and construct the Euler factor
    //assumes p splits in K and K has class number 1
    //construct it as a local field extension rather than a completion
    //temporarilly takes in emb a choice of number embedding, 1  - 4
    Qp := pAdicField(p, prec);
    Qpz<z> := PolynomialRing(Qp);
    Qp := pAdicField(p, prec);
    Qpz<z> := PolynomialRing(Qp);
    r := Roots(Qpz!(z^2-D))[2][1];
    embK := hom<K -> Qp|r>;

    ap:=Coefficient(f,p); //note that EltSeq starts at the first NONZERO coefficient, so the indexing is off, whereas Coefficient(f,n) gives the coefficient of q^n
    OK := MaximalOrder(K);
    pSplitting := Factorization(p*OK);
    primeOverp1 := pSplitting[1][1]; //fix frakp to be the valuation 1 thing
    primeOverp2 := pSplitting[2][1];
    bool, gen1:= IsPrincipal(primeOverp1);
    bool, gen2:= IsPrincipal(primeOverp2);

    if Valuation(embK(gen1)) eq 1 then
        beta1 := gen1;
        beta2:= gen2;
    else
        beta1 := gen2;
        beta2:= gen1;
    end if;

    value :=embK(value);
    eulerFactor := 1 - ap * beta1^s *beta2^(-k - s)  + beta1^(k + 2*s - 1) * beta2^(-k - 2*s-1);
    ef:=embK(eulerFactor);
    return value, ef;
end function;

function ellval(E, D, p, B, file: bigqprec:= 2000, complexprec:= 100)
	//r = i * (p-1)^2 for now
	//B if p = 5 then (p-1)^2 already divides 4(p-1)
	//B is the prec so we work up to i = 1, ..., B
	//then we define ell(r) = L(f, K, 1+ r, 1 -r)* Omega_p^( - 4r)
	//in the old BDP notation j = r-1
	//compute l(i*(p-1)^2) for i = 1, 2, .., B
	//this function really has no purpose other than to call the other function and rename/reindex it in terms of Rubin's paper
	k:= 2; //fixme, just write 2 everywhere
	f:= ModularForm(E);
	algAns, K, KM, injK := runLeibniz(f, D, p, B, file: bigqprec:= bigqprec, complexprec:= complexprec);

	pAdicAns:=[];
    for i in [1 .. B] do
    	QqAns, ef := makepAdic(algAns[i], p, 5000, f, (p - 1)*i-1, k, D, K);
    	Append(~pAdicAns, QqAns^2 * ef^2);
    end for;
	return pAdicAns;
end function;

function hzero(B,p,lv)
	print("computing h(0)");
	//compute h(0) using Theorem 9 mod p^B
	outersum :=0;
	for j in [1 .. B] do
		innersum := 0;
		for l in [j .. B] do
			hj:=lv[j]^((p-1) div 2); 
			innersum := innersum + ((-1)^(j-1))*Binomial(l-1,j-1);
		end for;
		outersum := outersum + innersum*hj;
	end for;
	print(outersum);
	return outersum; //only accurate to p^B
end function;


function findRoot(h0,B,p,l0)
//now l(0) mod p1^B is a (p-1)/2 root of h(0)
//we need to pick the right root by applying prop 7 (ii)
	print("finding root");
	valh0 := Valuation(h0); 
	h0 := ChangePrecision(h0, B-valh0); //fix to do absolute precision
	Kp := Parent(h0);
	_<z>:=PolynomialRing(Kp);
	deg := (p-1) div 2;
	roots:=Roots(z^deg - h0);
	if Valuation(l0) gt 0 then
		return roots; //return all roots, try all possible values
	end if;
	for r in roots do
		if ChangePrecision(r[1],1) eq ChangePrecision(l0,1) then 
			return r[1];
		end if;
	end for;
	return "failure";
end function;

function computeLogConst(E,D,p,B, file: bigqprec:= 2000, complexprec:= 100)
	//computes L*(0) which is, up to a constant, the log^2
	//we will iterate on r = (p-1)* i , so 1- r = -j
	// j = r - 1 = (p-1) i  - 1 
	refvalue:= (p-1) div 2; //this can be (p-1)/2, or (p-1), or a multiple
	assert B ge refvalue;
	
	lv := ellval(E, D, p, B, file: bigqprec:= bigqprec, complexprec:= complexprec);

	small_lv:=[]; //cut them down to precision-ish, otherwise we get precision errors sometimes
	for val in lv do
		Append(~small_lv,ChangePrecision(val,B));  //this will do relative prec, but hopefully that's enough
	end for;
	print("list of ell(stuff)");
	print(small_lv);

	l0:= lv[refvalue]; //reference value for l0 mod p, this is l((p-1)^2/2)
	h0:= hzero(B,p,small_lv); //compute h(0) mod p^B,  
	Lstar1:=findRoot(h0,B,p,l0); //compute l(0) mod p^B to obtain value of L^*_p(1) Omega_p
	//at this point we have done what Rubin has done in the monodromy paper
	//we have computed Lp(f, 1) to any precision B that we want
	//we will use this info to find the log of the rational point generator

	//we will get rid of the Euler factor and just return log^2 of the Heegner point
	f := ModularForm(E);	
	ap := Coefficient(f, p);
	ef := (1 - ap + p )/p;
	print("L_p(f,1)");
	if Valuation(l0) eq 0 then //one correct choice of log
		print(Lstar1);
		inventans:=[Lstar1 *(ef)^(-2)]; 
		return inventans;
	else //multiple choices
		inventans:=[];
		for root in Lstar1 do
			print(root[1]);
			Append(~inventans,root[1]*(ef)^(-2));
		end for;
		return inventans;
	end if;
end function;
