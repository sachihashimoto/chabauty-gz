load "../canring.m";
load "../rubin_BDP_log_X0.m";
load "../padic_embed.m";
load "107.2.a.a.m";


file := "X073data";
t := Cputime();
f := MakeNewformModFrm_107_2_a_a();
p := 11;
D := -7;
M :=CoefficientField(f);

B:= 5;
n := B *(p -1 ) - 1;

phi, genList, genWeights, R, GB, thetapolys, genvals, K, KM, RM:= setUp(f, D: bigqprec:= 4000);
algAns, K, KM, fnpoly, fwtnbasis, prec, injK:= leibnizThetaPhi(f, n, phi, genList, genWeights, R, GB, thetapolys, genvals, p, D, K, KM, file, RM);

print Cputime(t);


ans:= [];
for i in [1..4] do 
	Lp1, res := mainLoop(f, B, D, p, algAns, K, M, KM : emb:= i);
	Append(~ans, res);
end for;

ans := SetToSequence(Set(ans)); //these are the values of the logarithm of the Heegner point squared