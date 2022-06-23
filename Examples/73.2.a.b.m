
// Make newform 73.2.a.b in Magma, downloaded from the LMFDB on 15 May 2022.
// To make the character of type GrpDrchElt, type "MakeCharacter_73_a();"
// To make the coeffs of the qexp of the newform in the Hecke field type "qexpCoeffs();"
// To make the newform (type ModFrm), type "MakeNewformModFrm_73_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
// To make the Hecke irreducible modular symbols subspace (type ModSym)
// containing the newform, type "MakeNewformModSym_73_2_a_b();".
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


// To make the character of type GrpDrchElt, type "MakeCharacter_73_a();"
function MakeCharacter_73_a()
    N := 73;
    order := 1;
    char_gens := [*5*];
    v := [*\
1*];
    // chi(gens[i]) = zeta^v[i]
    assert SequenceToList(UnitGenerators(DirichletGroup(N))) eq char_gens;
    F := CyclotomicField(order);
    chi := DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^e:e in v]);
    return MinimalBaseRingCharacter(chi);
end function;

function MakeCharacter_73_a_Hecke(Kf)
    return MakeCharacter_73_a();
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
        [*-1, -1*],
        [*-3, 0*],
        [*-2, 1*],
        [*2, -3*],
        [*-3, 6*],
        [*1, 0*],
        [*-7, -1*],
        [*1, 4*],
        [*4, -6*],
        [*-5, 6*],
        [*2, -4*],
        [*-1, 0*],
        [*-5, 4*],
        [*7, -8*],
        [*-4, -4*],
        [*5, -3*],
        [*11, -6*],
        [*-10, -1*],
        [*-1, 0*],
        [*-8, -3*],
        [*-3, 3*],
        [*5, 2*],
        [*-6, 3*],
        [*-8, 10*],
        [*9, 0*],
        [*-7, -1*],
        [*-10, 3*],
        [*-14, 7*],
        [*-5, 3*],
        [*8, -1*],
        [*9, -12*],
        [*9, 3*],
        [*-2, 4*],
        [*1, 3*],
        [*7, 3*],
        [*0, 3*],
        [*9, -3*],
        [*-9, -3*],
        [*8, -7*],
        [*1, -12*],
        [*-7, -10*],
        [*10, -6*],
        [*-9, 12*],
        [*-4, 3*],
        [*-9, 12*],
        [*-2, 0*],
        [*9, -9*],
        [*-6, 15*],
        [*11, -22*],
        [*-1, 5*],
        [*-3, -6*],
        [*1, 13*],
        [*14, 5*],
        [*-7, -4*],
        [*5, -19*],
        [*-6, -6*],
        [*-1, 15*],
        [*11, 2*],
        [*12, 12*],
        [*-24, 12*],
        [*20, -12*],
        [*1, 13*],
        [*-21, 15*],
        [*-16, -4*],
        [*-16, 12*],
        [*7, -21*],
        [*16, -26*],
        [*-8, 9*],
        [*1, 19*],
        [*-20, 19*],
        [*-26, 18*],
        [*-3, -6*],
        [*-4, 0*],
        [*-29, -2*],
        [*-12, -3*],
        [*-2, -18*],
        [*-2, -2*],
        [*5, 0*],
        [*-16, 5*],
        [*9, 0*],
        [*12, 12*],
        [*1, -15*],
        [*-3, -18*],
        [*2, -22*],
        [*4, 1*],
        [*5, 9*],
        [*11, -4*],
        [*1, -6*],
        [*13, -2*],
        [*-8, -14*],
        [*-16, 0*],
        [*31, -17*],
        [*-25, 0*],
        [*9, -15*],
        [*23, 2*],
        [*-1, 2*],
        [*-26, -6*],
        [*18, 15*],
        [*-2, -27*],
        [*27, -6*],
        [*-16, 14*],
        [*22, -8*],
        [*-26, 12*],
        [*-6, -18*],
        [*9, 18*],
        [*6, -3*],
        [*-1, 29*],
        [*1, -9*],
        [*-23, 30*],
        [*-28, -9*],
        [*-31, 8*],
        [*-19, 30*],
        [*26, 9*],
        [*7, -2*],
        [*-16, -12*],
        [*9, 21*],
        [*4, 7*],
        [*13, -8*],
        [*-28, 3*],
        [*43, -6*],
        [*22, -32*],
        [*-11, 16*],
        [*-7, -18*],
        [*-28, 14*],
        [*-6, -27*],
        [*16, -14*],
        [*-9, 3*],
        [*-9, 6*],
        [*-45, -3*],
        [*-7, -10*],
        [*-6, 18*],
        [*20, 0*],
        [*19, -23*],
        [*-22, 27*],
        [*1, -20*],
        [*32, -24*],
        [*-4, 29*],
        [*2, -22*],
        [*34, 0*],
        [*31, 4*],
        [*25, -3*],
        [*-30, -9*],
        [*-19, 24*],
        [*-31, 35*],
        [*-28, 12*],
        [*-32, 19*],
        [*-5, 0*],
        [*-11, 25*],
        [*15, 12*],
        [*-19, -1*],
        [*27, -15*],
        [*2, -13*],
        [*-4, -12*],
        [*-29, -2*],
        [*30, 6*],
        [*38, -22*],
        [*22, -18*],
        [*6, -39*],
        [*-29, 49*],
        [*34, -2*],
        [*-23, -3*],
        [*42, 0*],
        [*5, -19*],
        [*-31, 2*],
        [*13, -30*],
        [*22, -3*]*];
    aps := ConvertToHeckeField(raw_aps);
    chi := MakeCharacter_73_a_Hecke(Universe(aps));
    return ExtendMultiplicatively(weight, aps, chi);
end function;


// To make the newform (type ModFrm), type "MakeNewformModFrm_73_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
function MakeNewformModFrm_73_2_a_b(:prec:=2)
    chi := MakeCharacter_73_a();
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
// containing the newform, type "MakeNewformModSym_73_2_a_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
function MakeNewformModSym_73_2_a_b()
    R<x> := PolynomialRing(Rationals());
    chi := MakeCharacter_73_a();
    // SetVerbose("ModularSymbols", true);
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2,-1)));
    Vf := Kernel([<2,R![1, 3, 1]>],Snew);
    return Vf;
end function;