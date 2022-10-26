// Code for computing the special value of the anticyclotomic p-adic L-function of Bertolini, Darmon, Prasanna

// Authors: 
// Sachi Hashimoto, 2022
// Edgar Costa, 2022 improvements to evalPoly and evalMonomials functions


function df(f,r)
//atkin serre derivative
	R := Parent(f);
	q := R.1;
	for i in [1..r] do
		f := Derivative(f)*q;
	end for;
	return f;
end function;

function theta(g,gk, phi)
//the derivative theta phi
	PSring:= Parent(g);
	phi := PSring!phi;
	dg := df(g, 1);
	thetag := dg - gk * phi* g;
	return thetag;
end function;

function chowlaselbergrevised(d, F)
//chowla selberg derivative, d should be positive
	P := F!1;
	for j in [1..d-1] do
		P := P* Gamma(F!(j/d))^(LegendreSymbol(j,d));
	end for;
	P := (F!P)^(1/2);
	CS := ((1/Sqrt(F!(2*d)* Pi(F)))*P);
	if d eq 11 then
		CS := (CS/(2* F.1 * Root(F!(11), 4))) ;
	elif d eq 19 then
		CS := CS/(2* F.1 * Root(F!(1/304), 4)) ;
	elif d eq 7 then
		CS := CS/(2 * F.1 * Root(F!(7/16), 4));
	elif d eq 43 then
		CS := CS/(2 * F.1 * (1/2) * Root(F!(1/43),4));
	else
		print("This has not been normalized properly!");
		return CS;
	end if;
	return CS;
end function;

function algebraize(value, K, N, wt, epscomp)
	emb:=hom<K->F|Conjugates(K.1)[1]>;
	repart := Re(value);
	impart := Im(value);
	traceval := repart *2; 
	normval := repart^2 + impart^2;
	if IsPrime(N) then
		B := N^Ceiling(wt*N/(N - 1));
	else
		//now z^2 - traceval*z + normval is the minpoly for something in O_K[1/N]
		//figure out  the power of N
		success := false;
		for i in [0..2*N] do
			B := N^i;
			t := traceval*B;
			n := normval*B^2;

			if Abs((Round(n) - n)/n) lt epscomp  or  normval lt epscomp then
				if traceval lt epscomp or Abs((Round(t) - t)/t) lt epscomp then
					success := true;
					print i;
					print success;
					print traceval lt epscomp;
					print traceval;
					break i;
				end if;
			end if;
		end for;
		if not success then
			error "foo bar";
		end if;
	
		print "not implemented error...";
	end if;
	// B*value belongs to O_K
	traceval *:= B;
	normval *:= B^2;

	//now z^2 - traceval*z + normval is the minpoly
	//also traceval, normval are integers
	traceval := Round(traceval); //How do I do this better?
	normval := Round(normval);

	assert Abs(Round(normval) - normval) lt epscomp;
	assert Abs(Round(normval) - normval) lt epscomp;
	_<z>:= PolynomialRing(Integers());
	minpoly := z^2 - traceval*z + normval;
	rts := Roots(minpoly, K); //need to return the root wih the correct sign
	// FIXME do like
	for r in rts do
		if (Sign(Re(emb(r[1]))) eq Sign(Re(value)) or Sign(Re(emb(r[1]))) eq 0) and (Sign(Im(emb(r[1]))) eq Sign(Im(value)) or  Sign(Im(emb(r[1]))) eq 0) then
			if true then
				print "sanity check algebrize";
				print value;
				print r[1][1]/B, r[1][2]*K.1/B;
			end if;
			return r[1][1]/B, r[1][2]*K.1/B;
		end if;
	end for;

end function;

function constructPhi(wt2forms, E2z0real, E2z0im, E2starofCM, AlgField, qofjinv, Omegasq, N, E2, bigqprec)
//do some linear algebra to construct the modular form phi
	fvalues := [];
	for f in wt2forms do
		coeffs := Eltseq(qExpansion(f,bigqprec));
		den := LCM([Denominator(c) : c in coeffs]);
		fqexp:=qExpansion(den*f,bigqprec);
		feval := Evaluate(fqexp,qofjinv)/Omegasq;
		f0, f1 := algebraize(feval, AlgField, N, 2, epscomp);
		print feval;
		print "sanity check new algebraize";
		print f0/den, f1/den;
		Append(~fvalues,[f0/den, f1/den]);
	end for;
	//print(fvalues);
	l := #wt2forms;
	v:= Vector([E2z0real, E2z0im]);
	s:= Solution(Matrix(fvalues), v);
	soln := 0;
	qprec := MinimumPrecision(N, 4);
	S:=PowerSeriesRing(Rationals(),qprec);//eisenstein series can't be over QQ??
	for i in [1 .. #wt2forms] do
		soln := soln + qExpansion(wt2forms[i],qprec)* S!s[i];
	end for;
	phi := (E2)*(1/12) - S!(soln)*(1/12); //we are going to need the coeffs of E2 to be defined over QQ not over CC for the exact linear algebra later
	phistarofz := E2starofCM*(1/12)  - Evaluate(soln,qofjinv)*(1/12);
	print("this should be zero");
	print(phistarofz);
	print("sanity check solution");
	Evaluate(soln, qofjinv)/Omegasq;
	print "phi=", phi;
	return phi, phistarofz;
end function;

function solveSystem(modform, indexbasis, basis, M, qprec, RM)
	// basis is an associativeArray monomials -> evaluated monomials
	// we are using later on as SeqEnum, and expect things to be in the same order
	keys := indexbasis;
	assert Set(keys) eq Keys(basis);
	//does linear algebra
	//writes modform in terms of a basis
	len := Min(qprec, #AbsEltseq(modform));

	mat := [[AbsEltseq(qExpansion(basis[k], qprec))[j] : j in [1 ..len]]: i-> k in keys];
	modformvect := AbsEltseq(modform)[1..len];
	makeMat := Matrix(Rationals(), mat);
	//vect is over a number field, M
	try 
		vect := Vector(Rationals(), modformvect);
		components := Solution(makeMat, vect);
	catch err
		vect := [];
		for i in [1 .. Degree(M)] do
			vectj := [];
			for j in [1..len] do 
				Append(~vectj, modformvect[j][i]);	
			end for;
			Append(~vect, Vector(Rationals(), vectj));
		end for;
		components := [];
		//solve over QQ
		for i in [1 .. Degree(M)] do
			Append(~components, Solution(makeMat, vect[i]));
		end for;
		if true then
			print "Nrows(makeMat), Ncols(makeMat) = ", Nrows(makeMat), Ncols(makeMat);
			print "Rank(makeMat) = ", Rank(makeMat);
			print "len = ", len;
			//print "components = ", components;
		end if;
		components:=&+[ChangeRing(components[j],M)*(M.1)^(j-1): j in [ 1.. Degree(M)]];
	end try;
	sum := &+[components[i]*RM!k : i->k in keys];
	return components, sum;
end function;

function makeMonomials(wt, R, GB);
	//makes monomials of weighted degree that span a given weighted space in the quotient ring
	M := MonomialsOfWeightedDegree(R,wt,GB); // this function seems to not work in some way that at least produce more things than usual?
	formalmons := [M[i] : i in [1 .. #M]| Degree(M[i]) eq wt];
	return formalmons;
end function;

procedure assure_power(~gpowers, e)
	b, _ := IsDefined(gpowers, e);
	if not b then
		e0 := Max(Keys(gpowers));
		assert e0 lt e;
		v := gpowers[e0];
		$$(~gpowers, e-e0);
		gpowers[e] := gpowers[e-e0] * v;
		//assert gpowers[e] eq gpowers[1]^e;
	end if;
end procedure;

function PowersOfGenerators(monomials, genlist : res:=false)
	if res cmpeq false then
		res := [AssociativeArray() : _ in genlist];
		for i->g in genlist do
			res[i][0] := 1;
			res[i][1] := g;
		end for;
	end if;
	E := [Exponents(m) : m in monomials];
	for k->gk in genlist do
		for e in {e[k] : e in E | e[k] gt 0} do
			assure_power(~res[k], e);
		end for;
	end for;
	return res;
end function;

function prod(lst)
	res := 1;
	for elt in lst do
		res *:= elt;
	end for;
	return res;
end function;

function evalMonomials(formalmons, genlist : powers:=false);
	powers := PowersOfGenerators(formalmons, genlist : res:=false);
	res := AssociativeArray();
	for j->mon in formalmons do
		Exp := Exponents(mon);
		res[mon] := prod([* powers[k][Exp[k]] : k->gk in genlist | Exp[k] gt 0 *]);
	end for;
	return res, powers;
end function;

function solveFormalSystem(thetaphif, cfbasis, wt, R, genList, prec, M, RM);
	//writes thetaphif in poly in terms of cfbasis using linear algebra in q-expansions after evaluation
	//cfbasis is a formal set of vectors spanning the wt graded part of graded ring
	evalmons := evalMonomials(cfbasis, genList);
	_, sum := solveSystem(thetaphif, cfbasis, evalmons, M, prec, RM);
	return sum;
end function;

function evalAtCMPoint(cpoly, fbasis, genvals, D, R, K, M, KM);
	//evaluates at the CM point
	sum := 0;
	if M ne Rationals() then
		a:= KM!K.1;
		injK := hom<K->KM|a>;
	else
		injK := hom<K->K|K.1>;
	end if;
	for s in [1 .. #fbasis] do
		evalmon := KM!(cpoly[s]);

		if cpoly[s] eq 0 then
			continue;
		end if;
		mon := fbasis[s];
		fact:= Factorization(mon);
		for elt in fact do
			var:= elt[1];
			m:= elt[2];
			evalmon := evalmon * (injK(genvals[elt[1]]))^m;
		end for;
		sum := sum + evalmon;
	end for;
	sum := sum;

	return sum, K, KM, injK; //have to return injK so that the makepAdic function knows what K is...this is pretty hacky
end function;


function evalPoly(formalpoly, genList, gen_powers, prec, RM)
	// formalpoly = multivariable polynomial
	// genlist = list of modular forms matching the generators of formalpoly

	//evaluates a polynomial in q-expansions
	//Mons := Monomials(formalpoly);
	//C := Coefficients(formalpoly);
	genqexp := [qExpansion(g, prec) : g in genList];
	coeffs, mons := CoefficientsAndMonomials(formalpoly);
	evalmons := evalMonomials(mons, genqexp : powers:=gen_powers);
	M := BaseRing(RM);
	PS<q> := PowerSeriesRing(M, prec);

	sum := 0;
	for i-> mon in mons do // Mons[i] == mon
		sum +:= PS!evalmons[mon] * coeffs[i];
	end for;
	return sum;
end function;


function computeDerivatives(cfbasis, cpoly, thetapolys, RM, R)
	thetacurrent := RM!0;
	for j in [1 .. #cfbasis] do
		sum := 0;
		formalmon := cfbasis[j];
		fact := Factorization(formalmon);
		for elt in fact do //for each element, take deriv wrt that element 
			res := RM!1;
			m:= elt[2];
			fnonderiv:= elt[1];
			fderiv:= thetapolys[elt[1]];
			res := RM!res * m * RM!fderiv * RM!(fnonderiv^(m-1));//deriv wrt to l, using chain rule
			res := RM!(res) *RM!( R!(formalmon/elt[1]^m));
			sum := sum + res; //add in the derivatives with respect to the other variables
		end for;
	thetacurrent := thetacurrent + cpoly[j]*RM!(sum);
	end for;
	return thetacurrent;
end function;


function leibnizThetaPhi(fmodform, n,  phi, genList, genWeights, R, GB, thetapolys, genvals, p, D, K, KM, file, RM:  bigqprec := 8000)
	//main function, iteratively computes the theta phi values using the leibniz rule strategy
	//keeps things algebraic except to do the linear algebra in q-expansions
	//increases prec when evaluating at the CM point at the final step

	N:= Level(fmodform);
	k:=Weight(fmodform);
	M := CoefficientField(fmodform);

	algAns := [* *];
	smallprec := MinimumPrecision(N,k+2);
	falgebraized := qExpansion(fmodform,bigqprec);
	if M eq Rationals() then
		falgebraized :=  PowerSeriesRing(M, smallprec)!falgebraized;
	end if;
	if n eq 0 then
		fkbasis := makeMonomials(k, R, GB);
		prec := MinimumPrecision(N, k); //need to find base value for induction
		wtkbasis := evalMonomials(fkbasis, genList);
		fpoly, _ := solveSystem(falgebraized, fkbasis, wtkbasis, M, prec, RM);
		print wtkbasis;
		print("Finished n = 0 case");
		Write(file, "Finished n = 0");
		return algAns, K, KM, fpoly, fkbasis, prec, 0;
	elif n eq 1 then
		thetaphif := theta(falgebraized, k, phi);
		prec := MinimumPrecision(N,k+2);
		fkplus2basis := makeMonomials(k+2, R, GB);
		wtkplus2basis := evalMonomials(fkplus2basis, genList);
		f1poly, _ := solveSystem(thetaphif, fkplus2basis, wtkplus2basis,M, prec, RM);
		print("Finished n = 1 case");
		Write(file, "Finished n = 1");
		return algAns, K, KM, f1poly, fkplus2basis, prec, 0;
	else
		prec:= MinimumPrecision(N,4);
		CapitalPPhi := df(phi, 1) - phi^2;
		fwt4basis := makeMonomials(4, R, GB);
		wt4basis := evalMonomials(fwt4basis, genList);
		phipoly, sum := solveSystem(CapitalPPhi, fwt4basis, wt4basis, M, prec, RM);
		sum := RM!sum;
		CapitalPPhi := RM!0;
		for s in [1 .. #fwt4basis] do
			CapitalPPhi := CapitalPPhi + RM!fwt4basis[s] * phipoly[s];
		end for;
		print "CapitalPPhi";
		print Parent(CapitalPPhi), Parent(sum);
		print CapitalPPhi eq sum;
		print CapitalPPhi;
		print sum;
		i := 2;
		algAns, K, KM, pvspoly, pvsfbasis, prec, _  := leibnizThetaPhi(fmodform, 0,  phi, genList, genWeights, R, GB, thetapolys, genvals, p, D, K, KM, file, RM : bigqprec:= bigqprec); //agrees with other step 0
		algAns, K, KM, cpoly, cfbasis, prec, _ := leibnizThetaPhi(fmodform, 1, phi, genList, genWeights, R, GB, thetapolys, genvals, p, D, K, KM, file, RM: bigqprec:= bigqprec); //agrees with other step 1
		//when p = 3, (p-1) - 1 = 1, so we need to eval at 1
		if IsDivisibleBy(i, (p-1)) then
			intans, K, KM, injK:= evalAtCMPoint(cpoly, cfbasis, genvals, D, RM, K, M, KM);
			Append(~algAns, intans);
			Write(file, Sprint(intans));
			Write(file, ",");
			print(intans);
		end if;

		while (i le n) do
			print("precision");
			print(prec);
			print("computing derivatives");
			thetacurrent := computeDerivatives(cfbasis, cpoly, thetapolys, RM, R);
			print "done computing derivatives";
			pvs:=RM!0;
			for s in [1 .. #pvsfbasis] do
				pvs := pvs + RM!(pvsfbasis[s]) * M!(pvspoly[s]);
			end for;
			prec:= MinimumPrecision(N,k+2*i);
			thetaphif := thetacurrent + (i-1) * (i+ k - 2)* CapitalPPhi* pvs ;
			pvspoly := cpoly;
			pvsfbasis := cfbasis;
			print("making new monomial basis");

			cfbasis := makeMonomials(k+2*i, R, GB);
			print("eval monomials");
			wtkplus2ibasis, gen_powers := evalMonomials(cfbasis, genList);
			print("eval poly!!!");
			time thetaeval := evalPoly(thetaphif, genList, gen_powers, prec, RM);
			print("solve system");
			time cpoly, _ := solveSystem(thetaeval, cfbasis, wtkplus2ibasis, M, prec, RM);
			print("increased i");
			i := i+1;
			print(i);
			fact := Factorization(i);
			if IsDivisibleBy(i, (p-1)) then
				intans, K, KM, injK := evalAtCMPoint(cpoly, cfbasis, genvals, D, R, K, M, KM);
				Write(file, Sprint(intans));
				Write(file, ",");
				print(intans);
				print(Parent(intans));
				Append(~algAns, intans);
			end if;
		end while;

		return algAns, K, KM, cpoly, cfbasis, prec, injK;
	end if;
end function;


function setUp(f, D: bigqprec := 8000, complexprec:=100)
	//sets up data for iteration



	F<I>:=ComplexFieldExtra(complexprec);
	epscomp := RealField(Precision(F)) ! (10^(-Precision(F) + 10));

	verbose:=true;
	
	PS<z> := PowerSeriesRing(F, bigqprec);

	E2<q>:=Eisenstein(2, z);
	PS<q> := PowerSeriesRing(Rationals(), bigqprec);
	vE2 := [Rationals()!Round(AbsEltseq(E2)[i]): i in [1 .. bigqprec]];
	E2:= Rationals()!0;
	for i in [1 .. bigqprec] do
		E2 := E2 + q^(i-1) * vE2[i];
	end for;
	
	N:= Level(f);
	k:=Weight(f);
	M := CoefficientField(f);

	P:=HeegnerForms(N,D)[1];
	_<x>:=PolynomialRing(F);
	qf :=P[1]*x^2 + P[2]*x + P[3];

	r1:=Roots(qf)[1][1];
	r2:=Roots(qf)[2][1];

	Omega := chowlaselbergrevised(-D, F);//This is the wrong normalized value of omega, need to fix because we want *I
	Omegasq:= Omega * F!(1/-D) *Omega;
	qofjinv := Exp(F!(2*(Pi(F))*I*r2));
	y := F!Im(r2);

	_<z>:= PolynomialRing(Rationals());
	K<a>:=NumberFieldExtra(z^2-D);
	KM := CompositeFields(K, M)[1];

	E2starofCM := Evaluate(E2, qofjinv)-3/(Pi(F)*(y));
	E2z0 := E2starofCM*Omegasq^(-1);

	print(E2z0);
	E2z0real, E2z0im := algebraize(E2z0,K,N,2, epscomp);
	print "sanity check new algebraize";
	print E2z0real, E2z0im;

	R, RIdeal, MGamma, quo, genList, genWeights := CanonicalRing(N : MaxWeight := 12);
	RM := ChangeRing(R, M);

	GB:= GroebnerBasis(RIdeal);

	wt2basis := [];
	for i->g  in genList do
		if genWeights[i] eq 2 then
			Append(~wt2basis,g);
		end if;
	end for;

 	phi, phistarofz := constructPhi(wt2basis, E2z0real, E2z0im, E2starofCM, K, qofjinv, Omegasq, N, E2, bigqprec);
	print("making theta polys");

	thetapolys := AssociativeArray();
	for i->g in genList do
		qprec := MinimumPrecision(N, genWeights[i]);
		gexp:=qExpansion(g,qprec);
		thetag :=theta(gexp, genWeights[i], phi);
		tbasis := makeMonomials(genWeights[i]+2, R, GB);
		thetapoly := solveFormalSystem(thetag, tbasis, genWeights[i]+2,R,genList, qprec, M, RM);
		thetapolys[R.i]:= thetapoly;
	end for;

	genvals:= AssociativeArray();
	for i->g in genList do
		coeffs := Eltseq(qExpansion(g,bigqprec));
		den := LCM([Denominator(c) : c in coeffs]);
		gexp:=qExpansion(den*g,bigqprec);
		w:= genWeights[i];
		wprime := w div 2;
		val := Evaluate(gexp, qofjinv)*Omegasq^(-wprime);
		reval, imval := algebraize(val, K, N, w, epscomp);
		genvals[R.i]:= K!(reval+imval)/den;
	end for;
	return  phi, genList, genWeights, R, GB, thetapolys, genvals, K, KM, RM;
end function;


function runLeibniz(f, D, p, B, file : multiple := true, bigqprec:= 8000, complexprec:= 100)
	//runs main loop for f, D, p
	//B is the prec so we work up to i = 1, ..., B
	//then we define ell(r) = L(f, K, 1+ B(p-1), 1 -B(p-1))* Omega_p^( - 4(B(p-1))
	//in the old BDP notation j = r-1
	//returns a list of ell(i*(p-1)) for i = 1, 2, .., B as algebraic values


	phi, genList, genWeights, R, GB, thetapolys, genvals, K, KM, RM:= setUp(f, D: bigqprec := bigqprec, complexprec:= complexprec);

	// if mult is false, then we just take n = B, instead of B * (p-1) - 1 for testing / debugging purposes only

	if multiple then
		n := B *(p -1 ) - 1;
	else 
		n := B;
	end if;

	algAns, K, KM, fnpoly, fwtnbasis, prec, injK:= leibnizThetaPhi(f, n, phi, genList, genWeights, R, GB, thetapolys, genvals, p, D, K, KM, file, RM: bigqprec:= bigqprec);

	return algAns, K, KM, injK;
end function;





