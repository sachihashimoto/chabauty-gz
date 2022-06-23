
// Make newform 85.2.a.b in Magma, downloaded from the LMFDB on 11 December 2021.
function ConvertToHeckeField(input: pass_field := false, Kf := [])
    if not pass_field then
        poly := [*-2, 0, 1*];
        Kf := NumberField(Polynomial([elt : elt in poly]));
        AssignNames(~Kf, ["nu"]);
    end if;
    Rfbasis := [Kf.1^i : i in [0..Degree(Kf)-1]];
    inp_vec := Vector(Rfbasis)*ChangeRing(Transpose(Matrix([[elt : elt in row] : row in input])),Kf);
    return Eltseq(inp_vec);
end function;


// To make the character of type GrpDrchElt, type "MakeCharacter_85_a();"
function MakeCharacter_85_a()
    N := 85;
    order := 1;
    char_gens := [*52, 71*];
    v := [*\
1,
1*];
    // chi(gens[i]) = zeta^v[i]
    assert SequenceToList(UnitGenerators(DirichletGroup(N))) eq char_gens;
    F := CyclotomicField(order);
    chi := DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^e:e in v]);
    return MinimalBaseRingCharacter(chi);
end function;

function MakeCharacter_85_a_Hecke(Kf)
    return MakeCharacter_85_a();
end function;


function ExtendMultiplicatively(weight, aps, character)
    prec := NextPrime(NthPrime(#aps)) - 1; // we will able to figure out a_0 ... a_prec
    primes := PrimesUpTo(prec);
    prime_powers := primes;
    assert #primes eq #aps;
    log_prec := Floor(Log(prec)/Log(2)); // prec < 2^(log_prec+1)
    F := Universe(aps);
    FXY<X, Y> := PolynomialRing(F, 2);
    // 1/(1 - a_p T + p^(weight - 1) * char(p) T^2) = 1 + a_p T + a_{p^2} T^2 + ...
    R<T> := PowerSeriesRing(FXY : Precision := log_prec + 1);
    recursion := Coefficients(1/(1 - X*T + Y*T^2));
    coeffs := [F!0: i in [1..(prec+1)]];
    coeffs[1] := 1; //a_1
    for i := 1 to #primes do
        p := primes[i];
        coeffs[p] := aps[i];
        b := p^(weight - 1) * F!character(p);
        r := 2;
        p_power := p * p;
        //deals with powers of p
        while p_power le prec do
            Append(~prime_powers, p_power);
            coeffs[p_power] := Evaluate(recursion[r + 1], [aps[i], b]);
            p_power *:= p;
            r +:= 1;
        end while;    
    end for;
    Sort(~prime_powers);
    for pp in prime_powers do
        for k := 1 to Floor(prec/pp) do
            if GCD(k, pp) eq 1 then
                coeffs[pp*k] := coeffs[pp]*coeffs[k];
            end if;
        end for;
    end for;
    return coeffs;
end function;


function qexpCoeffs()
    // To make the coeffs of the qexp of the newform in the Hecke field type "qexpCoeffs();"
    weight := 2;
    raw_aps := [*\
[*-1, 1*],
        [*-2, -1*],
        [*-1, 0*],
        [*-2, 1*],
        [*-4, 1*],
        [*0, -2*],
        [*-1, 0*],
        [*0, -2*],
        [*-2, -1*],
        [*-2, -2*],
        [*0, 3*],
        [*-2, 6*],
        [*2, -6*],
        [*2, 4*],
        [*-2, -2*],
        [*6, -4*],
        [*-12, 2*],
        [*2, 4*],
        [*-6, 2*],
        [*0, -3*],
        [*-2, -2*],
        [*4, 1*],
        [*-2, 8*],
        [*-8, 4*],
        [*-2, 4*],
        [*-8, 0*],
        [*2, -2*],
        [*2, 7*],
        [*-6, -8*],
        [*-6, 2*],
        [*-6, -8*],
        [*-4, -7*],
        [*4, -2*],
        [*8, 7*],
        [*2, 0*],
        [*16, -6*],
        [*-10, -8*],
        [*2, -1*],
        [*-2, 3*],
        [*10, 2*],
        [*-4, -2*],
        [*-6, 6*],
        [*12, 0*],
        [*-18, -2*],
        [*10, 2*],
        [*20, 3*],
        [*-12, 7*],
        [*6, 0*],
        [*-10, -9*],
        [*-12, 8*],
        [*-2, 8*],
        [*20, 0*],
        [*10, 2*],
        [*-12, 0*],
        [*0, -2*],
        [*-2, 8*],
        [*2, 12*],
        [*-8, -4*],
        [*-10, 0*],
        [*-10, 4*],
        [*10, 3*],
        [*18, 0*],
        [*-14, -2*],
        [*8, 5*],
        [*14, -14*],
        [*-10, -8*],
        [*24, 2*],
        [*2, -16*],
        [*6, -21*],
        [*26, 4*],
        [*-22, -4*],
        [*-12, -14*],
        [*-10, -3*],
        [*-8, 14*],
        [*0, -19*],
        [*-6, -20*],
        [*-16, 0*],
        [*2, 8*],
        [*-22, 4*],
        [*-6, 0*],
        [*8, 3*],
        [*-12, -12*],
        [*0, 1*],
        [*0, 2*],
        [*4, 1*],
        [*-6, -6*],
        [*-18, -6*],
        [*8, 22*],
        [*2, 28*],
        [*-6, 2*],
        [*-6, 4*],
        [*-20, 3*],
        [*6, -7*],
        [*-8, -6*],
        [*8, 3*],
        [*2, 21*],
        [*-2, 16*],
        [*-6, 0*],
        [*14, -10*],
        [*-6, -26*],
        [*-14, 15*],
        [*24, 2*],
        [*-26, 4*],
        [*2, -20*],
        [*-20, 11*],
        [*20, 2*],
        [*6, 16*],
        [*30, 0*],
        [*12, 24*],
        [*-6, -14*],
        [*-6, 1*],
        [*-30, -12*],
        [*34, -6*],
        [*-24, 5*],
        [*4, -14*],
        [*14, 10*],
        [*-18, -21*],
        [*-18, -2*],
        [*10, 6*],
        [*-16, 8*],
        [*2, 8*],
        [*-14, -10*],
        [*-18, 16*],
        [*-2, -9*],
        [*4, -15*],
        [*36, -4*],
        [*6, 14*],
        [*-4, -35*],
        [*-14, 18*],
        [*18, 20*],
        [*8, 14*],
        [*-10, 17*],
        [*-8, -27*],
        [*44, -2*],
        [*24, -8*],
        [*-40, 4*],
        [*-4, 22*],
        [*-10, -15*],
        [*-14, -16*],
        [*-26, -4*],
        [*20, -1*],
        [*14, 16*],
        [*-18, -5*],
        [*-14, -11*],
        [*6, 24*],
        [*4, 27*],
        [*-34, 2*],
        [*22, -6*],
        [*0, 26*],
        [*-2, 6*],
        [*26, -20*],
        [*34, 10*],
        [*18, -2*],
        [*-22, 5*],
        [*6, -9*],
        [*8, 3*],
        [*24, 12*],
        [*10, 18*],
        [*6, 20*],
        [*22, -18*],
        [*-26, -7*],
        [*-36, 10*],
        [*-18, 12*],
        [*-28, 14*],
        [*14, 32*],
        [*-6, -25*],
        [*32, 1*],
        [*26, 10*]*];
    aps := ConvertToHeckeField(raw_aps);
    chi := MakeCharacter_85_a_Hecke(Universe(aps));
    return ExtendMultiplicatively(weight, aps, chi);
end function;


// To make the newform (type ModFrm), type "MakeNewformModFrm_85_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
function MakeNewformModFrm_85_2_a_b(:prec:=2)
    chi := MakeCharacter_85_a();
    f_vec := qexpCoeffs();
    Kf := Universe(f_vec);
    // SetVerbose("ModularForms", true);
    // SetVerbose("ModularSymbols", true);
    S := CuspidalSubspace(ModularForms(chi, 2));
    S := BaseChange(S, Kf);
    maxprec := NextPrime(997) - 1;
    while true do
        trunc_vec := Vector(Kf, [0] cat [f_vec[i]: i in [1..prec]]);
        B := Basis(S, prec + 1);
        S_basismat := Matrix([AbsEltseq(g): g in B]);
        if Rank(S_basismat) eq Min(NumberOfRows(S_basismat), NumberOfColumns(S_basismat)) then
            S_basismat := ChangeRing(S_basismat,Kf);
            f_lincom := Solution(S_basismat,trunc_vec);
            f := &+[f_lincom[i]*Basis(S)[i] : i in [1..#Basis(S)]];
            return f;
        end if;
        error if prec eq maxprec, "Unable to distinguish newform within newspace";
        prec := Min(Ceiling(1.25 * prec), maxprec);
    end while;
end function;


// To make the Hecke irreducible modular symbols subspace (type ModSym)
// containing the newform, type "MakeNewformModSym_85_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
function MakeNewformModSym_85_2_a_b()
    R<x> := PolynomialRing(Rationals());
    chi := MakeCharacter_85_a();
    // SetVerbose("ModularSymbols", true);
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2,-1)));
    Vf := Kernel([<2,R![-1, 2, 1]>],Snew);
    return Vf;
end function;