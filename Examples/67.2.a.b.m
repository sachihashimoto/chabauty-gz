
// Make newform 67.2.a.b in Magma, downloaded from the LMFDB on 15 May 2022.
// To make the character of type GrpDrchElt, type "MakeCharacter_67_a();"
// To make the coeffs of the qexp of the newform in the Hecke field type "qexpCoeffs();"
// To make the newform (type ModFrm), type "MakeNewformModFrm_67_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
// To make the Hecke irreducible modular symbols subspace (type ModSym)
// containing the newform, type "MakeNewformModSym_67_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
function ConvertToHeckeField(input: pass_field := false, Kf := [])
    if not pass_field then
        poly := [*-1, -1, 1*];
        Kf := NumberField(Polynomial([elt : elt in poly]));
        AssignNames(~Kf, ["nu"]);
    end if;
    Rfbasis := [Kf.1^i : i in [0..Degree(Kf)-1]];
    inp_vec := Vector(Rfbasis)*ChangeRing(Transpose(Matrix([[elt : elt in row] : row in input])),Kf);
    return Eltseq(inp_vec);
end function;


// To make the character of type GrpDrchElt, type "MakeCharacter_67_a();"
function MakeCharacter_67_a()
    N := 67;
    order := 1;
    char_gens := [*2*];
    v := [*\
1*];
    // chi(gens[i]) = zeta^v[i]
    assert SequenceToList(UnitGenerators(DirichletGroup(N))) eq char_gens;
    F := CyclotomicField(order);
    chi := DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^e:e in v]);
    return MinimalBaseRingCharacter(chi);
end function;

function MakeCharacter_67_a_Hecke(Kf)
    return MakeCharacter_67_a();
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
[*-1, -1*],
        [*-2, 1*],
        [*-3, 0*],
        [*1, -3*],
        [*-1, 2*],
        [*-5, 3*],
        [*-4, 2*],
        [*2, -3*],
        [*1, 4*],
        [*-1, -4*],
        [*-1, 0*],
        [*1, -3*],
        [*-2, 1*],
        [*0, 3*],
        [*-7, -1*],
        [*-9, 0*],
        [*6, 0*],
        [*1, -9*],
        [*-1, 0*],
        [*7, -2*],
        [*-4, 0*],
        [*-8, 9*],
        [*-4, -7*],
        [*1, -2*],
        [*-5, 12*],
        [*-2, -5*],
        [*-7, 9*],
        [*15, -6*],
        [*0, -3*],
        [*17, -1*],
        [*-1, -3*],
        [*-3, 0*],
        [*-9, 6*],
        [*-3, 0*],
        [*-2, 13*],
        [*-1, 0*],
        [*11, -9*],
        [*-2, -3*],
        [*14, -16*],
        [*-22, 5*],
        [*-10, 2*],
        [*-8, 9*],
        [*-5, 4*],
        [*12, 3*],
        [*-11, 4*],
        [*-14, 15*],
        [*-7, 3*],
        [*6, 6*],
        [*7, -17*],
        [*-14, -3*],
        [*8, -4*],
        [*-11, -5*],
        [*21, 3*],
        [*8, 2*],
        [*-1, -16*],
        [*-6, 9*],
        [*-1, 11*],
        [*15, 6*],
        [*-6, 24*],
        [*7, 1*],
        [*-3, -12*],
        [*-15, 12*],
        [*-2, 12*],
        [*12, -24*],
        [*-9, -3*],
        [*-17, 22*],
        [*16, -12*],
        [*16, -15*],
        [*5, -10*],
        [*-6, 0*],
        [*10, -17*],
        [*-18, 0*],
        [*10, -18*],
        [*-4, -9*],
        [*4, 0*],
        [*-25, 11*],
        [*4, -14*],
        [*-21, -9*],
        [*3, 3*],
        [*-16, 18*],
        [*-10, 20*],
        [*-26, -3*],
        [*31, -2*],
        [*13, -33*],
        [*5, -27*],
        [*-17, 4*],
        [*20, -7*],
        [*-29, 12*],
        [*-9, -3*],
        [*-13, -9*],
        [*7, 10*],
        [*8, 14*],
        [*1, 24*],
        [*9, 12*],
        [*-25, 0*],
        [*29, 8*],
        [*-12, 12*],
        [*-18, 0*],
        [*13, -9*],
        [*12, 12*],
        [*20, -9*],
        [*-32, 1*],
        [*0, -6*],
        [*4, 10*],
        [*-8, 21*],
        [*19, -6*],
        [*31, -5*],
        [*-28, -4*],
        [*4, 4*],
        [*22, -18*],
        [*38, -9*],
        [*5, -12*],
        [*-33, 21*],
        [*-44, 6*],
        [*-19, 9*],
        [*25, -26*],
        [*-6, -9*],
        [*-28, 2*],
        [*-2, 4*],
        [*-17, -8*],
        [*21, 18*],
        [*8, -27*],
        [*-5, 10*],
        [*11, -1*],
        [*8, 0*],
        [*8, 20*],
        [*14, -12*],
        [*47, -4*],
        [*28, 0*],
        [*4, 0*],
        [*13, -15*],
        [*-11, 22*],
        [*15, 18*],
        [*19, 12*],
        [*-12, 0*],
        [*-1, -6*],
        [*7, -20*],
        [*-13, 12*],
        [*22, -35*],
        [*-12, 9*],
        [*-19, -18*],
        [*-19, 2*],
        [*10, -27*],
        [*16, -2*],
        [*25, -18*],
        [*26, -28*],
        [*-4, 27*],
        [*-3, -12*],
        [*32, -21*],
        [*21, 9*],
        [*17, -18*],
        [*-23, -2*],
        [*11, 6*],
        [*-19, 26*],
        [*-26, 3*],
        [*-48, 3*],
        [*-31, -12*],
        [*5, 8*],
        [*21, -6*],
        [*-39, 24*],
        [*-27, 15*],
        [*-1, 20*],
        [*-43, 24*],
        [*-1, 32*],
        [*-19, 14*],
        [*9, -24*],
        [*36, 9*],
        [*-21, 30*]*];
    aps := ConvertToHeckeField(raw_aps);
    chi := MakeCharacter_67_a_Hecke(Universe(aps));
    return ExtendMultiplicatively(weight, aps, chi);
end function;


// To make the newform (type ModFrm), type "MakeNewformModFrm_67_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
function MakeNewformModFrm_67_2_a_b(:prec:=2)
    chi := MakeCharacter_67_a();
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
// containing the newform, type "MakeNewformModSym_67_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
function MakeNewformModSym_67_2_a_b()
    R<x> := PolynomialRing(Rationals());
    chi := MakeCharacter_67_a();
    // SetVerbose("ModularSymbols", true);
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2,-1)));
    Vf := Kernel([<2,R![1, 3, 1]>],Snew);
    return Vf;
end function;