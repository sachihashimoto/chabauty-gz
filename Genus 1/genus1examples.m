load "rubin_BDP_log.m";

//Compare runtimes for B large and fixed N

// file := "path/to/file"; //where you want the output to be written

//To run, uncomment any block below

// t := Cputime();
// E:=EllipticCurve("37a1");  p:=5; D:= -11; B:= 6;
// computeLogConst(E,D,p,B, file);
// print(B);
// print Cputime(t);
// t := Cputime();


// E:=EllipticCurve("37a1");  p:=5; D:= -11; B:= 7;
// computeLogConst(E,D,p,B,file);
// print(B);
// print Cputime(t);
// t := Cputime();


// E:=EllipticCurve("37a1");  p:=5; D:= -11; B:= 8;
// computeLogConst(E,D,p,B,file);
// print(B);
// print Cputime(t);
// t := Cputime();


// E:=EllipticCurve("37a1");  p:=5; D:= -11; B:= 9;
// computeLogConst(E,D,p,B,file);
// print(B);
// print Cputime(t);
// t := Cputime();


// E:=EllipticCurve("37a1");  p:=5; D:= -11; B:= 10;
// computeLogConst(E,D,p,B,file);
// print(B);
// print Cputime(t);
// t := Cputime();


// E:=EllipticCurve("37a1");  p:=5; D:= -11; B:= 11;
// computeLogConst(E,D,p,B,file);
// print(B);
// print Cputime(t);
// t := Cputime();


// E:=EllipticCurve("37a1");  p:=5; D:= -11; B:= 12;
// computeLogConst(E,D,p,B,file);
// print(B);
// print Cputime(t);


//Varying N and fixed B

file := "timings";

// t := Cputime();
// E:=EllipticCurve("37a1");  p:=5; D:= -11; B:= 5;
// computeLogConst(E,D,p,B,file);
// print("time for 37a1");
// print Cputime(t);

// t := Cputime();
// E:= EllipticCurve("43a1");  D:=-19; p:=5; B:= 5; 
// computeLogConst(E,D,p,B,file);
// print("time for 43a1");
// print Cputime(t);

// t := Cputime();
// E:= EllipticCurve("58a1"); p:= 11;D:=-7; B:= 5; 
// computeLogConst(E,D,p,B,file);
// print("time for 58a1");
// print Cputime(t);

// t := Cputime();
// E:= EllipticCurve("61a1");  p:= 5; D:=-19; B:= 5; 
// print("time for 61a1");
// computeLogConst(E,D,p,B,file);
// print Cputime(t);

// t := Cputime();
// E := EllipticCurve("77a1"); D:= -19; p:= 5; B:= 5;
// computeLogConst(E,D,p,B,file);
// print("time for 77a1");
// print Cputime(t);

// t := Cputime();
// E := EllipticCurve("83a1"); D:= -19; p:= 5; B:= 5;
// computeLogConst(E,D,p,B,file);
// print("time for 83a1");
// print Cputime(t);

// t := Cputime();
// E:= EllipticCurve("89a1"); D:= -11; p:=3; B:=5;
// computeLogConst(E,D,p,B,file);
// print("time for 89a1");
// print Cputime(t);

// t := Cputime();
// E := EllipticCurve("101a1"); p:= 5; D:= -19; B:= 5;
// computeLogConst(E,D,p,B,file);
// print("time for 101a1");
// print Cputime(t);

// t := Cputime();
// E:= EllipticCurve("131a1");  p:=5; D:= -19; B:= 5; 
// computeLogConst(E,D,p,B,file : bigqprec:= 3000);
// print("time for 131a1");
// print Cputime(t);


//Some sample pre-computed output values below for L(p, 1) the special value of the anticyclotomic p-adic L-function, for reference

//computeLogConst(E,D,p,B);

// [ 1256 + O(5^5) ] E:=EllipticCurve("37a1");  p:=5; D:= -11; B:= 5;
// [ 3619 + O(5^6) ] E := EllipticCurve("83a1"); D:= -19; p:= 5; B:= 6; 
// [ 7396 + O(5^6) ] E:= EllipticCurve("43a1");  D:=-19; p:=5; B:= 6;,  [ -23854 + O(5^7) ] for B:= 7;
// [ 19 + O(3^5) ] E:= EllipticCurve("89a1"); D:= -11; p:=3; B:=5; and for B:= 8; [ -3140 + O(3^8) ]  for B:= 7; [ -953 + O(3^7) ]
// [ 1114 + O(5^5) ] E := EllipticCurve("77a1"); D:= -19; p:= 5; B:= 5;  and for B:= 7[ -30136 + O(5^7) ] 

//E:= EllipticCurve("61a1");  p:= 5; D:=-19; B:= 5;  
//[ -19*5^2  + O(5^5), 19*5^2  + O(5^5) ] for B:= 9
//[ -1269*5^2  + O(5^7), 1269*5^2  + O(5^7) ] for B:= 9
//[ -4394*5^2 + O(5^8), 4394*5^2 + O(5^8) ] for B := 10;
//[ -54535 + O(7^6) ] E:= EllipticCurve("61a1");  p:= 7; D:=-19; B:= 6; 
//[ 25760 + O(11^5) ] E:= EllipticCurve("58a1"); p:= 11;D:=-7; B:= 5;   
//[ -586 + O(5^5) ] E := EllipticCurve("101a1"); p:= 5; D:= -19; B:= 5;
//[ -841 + O(5^5) ] E:= EllipticCurve("131a1");  p:=5; D:= -19; B:= 5; 
