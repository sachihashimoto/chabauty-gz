
// Make newform 107.2.a.a in Magma, downloaded from the LMFDB on 15 May 2022.
// To make the character of type GrpDrchElt, type "MakeCharacter_107_a();"
// To make the coeffs of the qexp of the newform in the Hecke field type "qexpCoeffs();"
// To make the newform (type ModFrm), type "MakeNewformModFrm_107_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
// To make the Hecke irreducible modular symbols subspace (type ModSym)
// containing the newform, type "MakeNewformModSym_107_2_a_a();".
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


// To make the character of type GrpDrchElt, type "MakeCharacter_107_a();"
function MakeCharacter_107_a()
    N := 107;
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

function MakeCharacter_107_a_Hecke(Kf)
    return MakeCharacter_107_a();
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
[*0, -1*],
        [*-2, 1*],
        [*-2, 1*],
        [*-1, -2*],
        [*3, -2*],
        [*-6, 0*],
        [*-1, -1*],
        [*-2, 6*],
        [*1, 4*],
        [*-3, 4*],
        [*1, -4*],
        [*-8, 3*],
        [*6, -2*],
        [*6, -3*],
        [*-6, -2*],
        [*1, -8*],
        [*6, -9*],
        [*-8, 3*],
        [*-6, 2*],
        [*-6, 9*],
        [*-7, 6*],
        [*2, -3*],
        [*0, 3*],
        [*11, -2*],
        [*-3, -6*],
        [*3, -6*],
        [*5, -3*],
        [*-1, 0*],
        [*9, -10*],
        [*-6, -1*],
        [*-1, -6*],
        [*-15, 0*],
        [*-6, 11*],
        [*-9, 5*],
        [*-2, 5*],
        [*5, 7*],
        [*-16, 9*],
        [*-5, 12*],
        [*-3, 12*],
        [*7, 1*],
        [*10, -13*],
        [*-5, -10*],
        [*-11, -7*],
        [*16, -4*],
        [*-9, 6*],
        [*-9, 2*],
        [*0, 6*],
        [*5, -3*],
        [*1, 1*],
        [*-14, 0*],
        [*3, 15*],
        [*6, 0*],
        [*2, 3*],
        [*-9, 9*],
        [*19, 1*],
        [*21, 0*],
        [*-11, -2*],
        [*24, -6*],
        [*13, -16*],
        [*-14, 11*],
        [*-9, -11*],
        [*1, -1*],
        [*26, -6*],
        [*-2, 4*],
        [*-7, -15*],
        [*-17, 8*],
        [*9, -12*],
        [*-13, 0*],
        [*9, -3*],
        [*6, -23*],
        [*15, -12*],
        [*-27, 15*],
        [*0, -3*],
        [*3, 12*],
        [*-5, 5*],
        [*2, 10*],
        [*7, -20*],
        [*-15, -9*],
        [*3, 18*],
        [*-20, 6*],
        [*14, -23*],
        [*27, 3*],
        [*-16, -4*],
        [*-1, 10*],
        [*10, 0*],
        [*27, 6*],
        [*-3, -2*],
        [*-6, 14*],
        [*-32, 8*],
        [*-11, 15*],
        [*7, -8*],
        [*-22, 4*],
        [*-29, -1*],
        [*5, -2*],
        [*-8, 5*],
        [*-12, -14*],
        [*-18, -3*],
        [*-17, 5*],
        [*-22, 7*],
        [*-14, 12*],
        [*0, -19*],
        [*29, 1*],
        [*1, 8*],
        [*17, 1*],
        [*7, -1*],
        [*4, -22*],
        [*27, -18*],
        [*8, -16*],
        [*12, -24*],
        [*-15, -14*],
        [*-18, 12*],
        [*-2, 17*],
        [*7, -17*],
        [*-27, 18*],
        [*-36, 6*],
        [*-28, 32*],
        [*24, -20*],
        [*36, 5*],
        [*-8, -2*],
        [*-3, 15*],
        [*-9, -8*],
        [*-24, 33*],
        [*-19, -19*],
        [*-20, -13*],
        [*27, -12*],
        [*9, 2*],
        [*3, -1*],
        [*-31, -5*],
        [*-17, 20*],
        [*10, -15*],
        [*-19, 21*],
        [*7, -10*],
        [*34, -6*],
        [*-15, -4*],
        [*3, -11*],
        [*12, -35*],
        [*-20, -8*],
        [*39, -14*],
        [*14, -1*],
        [*-11, -20*],
        [*15, 12*],
        [*-6, -16*],
        [*-9, 30*],
        [*-5, 17*],
        [*-11, 15*],
        [*38, -1*],
        [*-20, 38*],
        [*1, 7*],
        [*-8, -27*],
        [*-14, 25*],
        [*0, -22*],
        [*-18, 30*],
        [*12, -31*],
        [*-8, -23*],
        [*28, 0*],
        [*30, -12*],
        [*0, 18*],
        [*11, 26*],
        [*-43, 10*],
        [*2, 32*],
        [*-17, -11*],
        [*20, -43*],
        [*7, 2*],
        [*-25, -5*],
        [*24, -19*],
        [*20, 8*],
        [*3, 19*],
        [*-18, 21*]*];
    aps := ConvertToHeckeField(raw_aps);
    chi := MakeCharacter_107_a_Hecke(Universe(aps));
    return ExtendMultiplicatively(weight, aps, chi);
end function;


// To make the newform (type ModFrm), type "MakeNewformModFrm_107_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
// The precision argument determines an initial guess on how many Fourier coefficients to use.
// This guess is increased enough to uniquely determine the newform.
function MakeNewformModFrm_107_2_a_a(:prec:=2)
    chi := MakeCharacter_107_a();
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
// containing the newform, type "MakeNewformModSym_107_2_a_a();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
function MakeNewformModSym_107_2_a_a()
    R<x> := PolynomialRing(Rationals());
    chi := MakeCharacter_107_a();
    // SetVerbose("ModularSymbols", true);
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,2,-1)));
    Vf := Kernel([<2,R![-1, 1, 1]>],Snew);
    return Vf;
end function;