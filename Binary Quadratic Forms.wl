(* ::Package:: *)

(* ::Title:: *)
(*Binary Quadratic Forms*)

(* ::Subtitle:: *)
(*Jack Heimrath 2024*)

(* ::Section:: *)
(*BeginPackage*)

BeginPackage["QuadraticForms`"];
(*Throughout this package, when talking about a (quadratic) form {a, b, c}, we will mean the quadratic form ax^2+bxy+cy^2*)

(* ::Subsubsubsection:: *)
(*Elementary Theory of Quadratic Forms*)
QuadraticFormDiscriminant::usage = "QuadraticFormDiscriminant[{a, b, c}] computes the discriminant of the form {a, b, c}";
PositiveDefiniteFormQ::usage = "PositiveDefiniteFormQ[{a, b, c}] returns True if the form {a, b, c} is positive definite, and False otherwise";
PrimitiveFormQ::usage = "PrimitiveFormQ[{a, b, c}] returns True if the form {a, b, c} is primitive, and False otherwise";
ReducedFormQ::usage = "ReducedFormQ[{a, b, c}] returns True if the form {a, b, c} is reduced, and False otherwise";
ReduceForm::usage = "ReduceForm[{a, b, c}] returns the unique reduced form {a1, b1, c1} which is properly equivalent to {a, b, c}";
EquivalentFormsQ::usage = "EquivalentFormsQ[f, g] returns True if and only if the forms f and g are properly equivalent";
ReducedForms::usage = "ReducedForms[d] returns all reduced quadratic forms of discriminant d<0";
ClassNumber::usage = "ClassNumber[d] returns the number of reduced qudratic forms of discriminant d<0";

(* ::Subsubsubsection:: *)
(*Elementary Genus Theory*)
GenusRepresentatives::usage = "";
SameGenusQ::usage = "";
PrincipalForm::usage = "";
DirichletComposition::usage = "";

Begin["`Private`"];

(* ::Subsection::Closed:: *)
(*Elementary Theory of Quadratic Forms*)

QuadraticFormDiscriminant[{a_, b_, c_}] := b^2 - 4 a c
QuadraticFormDiscriminant[f_List, forms__List] := QuadraticFormDiscriminant /@ {f, forms}

PositiveDefiniteFormQ[{a_, b_, c_}] := (a > 0 && QuadraticFormDiscriminant[{a, b, c}] < 0)

PrimitiveFormQ[{a_, b_, c_}] := (GCD[a, b, c] == 1)

ReducedFormQ[f: {a_, b_, c_}] := (PrimitiveFormQ[f] && (Abs[b] <= a <= c) && If[Abs[b] == a || a == c, b >= 0, True])
ReducedFormQ[f_List, forms__List] := And @@ (ReducedFormQ /@ {f, forms})

ReduceForm[f: {a_, b_, c_}] /; PositiveDefiniteFormQ[f] && PrimitiveFormQ[f] := Module[
	{a1, b1, c1, m},
	(* Enforce a\[LessEqual]c *)
	{a1, b1, c1} = If[a > c, {c, b, a}, f];
	(* Enforce |b|\[LessEqual]a *)
	{a1, b1, c1} = With[
		{newVars = Minimize[Abs[2 a1 m + b1], m, Integers]},
		{a1, newVars[[1]], c1 + b1 m + a1 m^2} /. newVars[[2]]
	];
	(* Repeat the process, if necessary *)
	If[
		ReducedFormQ[{a1, b1, c1}],
		{a1, b1, c1},
		ReduceForm[{a1, b1, c1}]
	]
]

EquivalentFormsQ[f1: {a1_, b1_, c1_}, f2: {a2_, b2_, c2_}] := (ReduceForm[f1] === ReduceForm[f2])

ReducedForms[d_Integer?Negative] /; (Mod[d, 4] == 0 || Mod[d, 4] == 1) := Module[
	{a, b, c, bound = Sqrt[-d/3]},
	a = Range[1, bound];
	b = Select[Range[-a, a], (Mod[#, 2] == Mod[d, 4])&];
	c = Cases[
		Flatten[Table[Table[{i, j, SolveValues[d == QuadraticFormDiscriminant[{i, j, c}], c, Integers]}, {j, Range[-i, i]}], {i, Range[1, bound]}], 1],
		{p_Integer, q_Integer, {r_Integer}} /; ReducedFormQ[{p, q, r}] :> {p, q, r}
	]
]
ReducedForms[d_Integer?Negative] /; (Mod[d, 4] == 2 || Mod[d, 4] == 3) := {}

ClassNumber[d_Integer?Negative] := Length[ReducedForms[d]]

(* ::Subsection::Closed:: *)
(*Elementary Genus Theory*)

(* ::Subsubsection::Closed:: *)
(*Helper Functions*)
ClearAll[equalDiscriminantQ, dirichletB]

equalDiscriminantQ[f1: {a1_, b1_, c1_}, f2: {a2_, b2_, c2_}] := Equal @@ QuadraticFormDiscriminant[f1, f2]

ClearAll[dirichletB];
dirichletB[f1: {a1_, b1_, c2_}, f2: {a2_, b2_, c2_}] /; (equalDiscriminantQ[f1, f2] && GCD[a1, a2, (b1 + b2)/2] == 1) := Module[
	{disc = QuadraticFormDiscriminant[f1]},
	If[
		b1 + b2 == 0,
		SolveValues[(a2 b) == (a2 b1) && (a1 b) == (a1 b2), b, Modulus -> (2 a1 a2)][[1]],
		SolveValues[(a2 b) == (a2 b1) && (a1 b) == (a1 b2) && (b1+b2)/2 b == (b1 b2 + disc)/2, b, Modulus -> (2 a1 a2)][[1]]
	]
]

(* ::Subsubsection:: *)
(*Main Functions*)

GenusRepresentatives[f: {a_, b_, c_}] /; PrimitiveFormQ[f] := Module[
	{disc = -QuadraticFormDiscriminant[f], bound},
    bound = Ceiling[disc/2];
	Select[Union@Flatten[Table[Mod[f . {x^2, x y, y^2}, disc], {x, -bound, bound}, {y, -bound, bound}]], GCD[disc, #] == 1&]
]

SameGenusQ[f1: {a1_, b1_, c1_}, f2: {a2_, b2_, c2_}] /; equalDiscriminantQ[f1, f2] := Equal @@ (GenusRepresentatives /@ {f1, f2})
SameGenusQ[{a1_, b1_, c1_}, {a2_, b2_, c2_}] := False;

PrincipalForm[d_Integer?Negative] /; Mod[d, 4] == 0 := {1, 0, -d/4}
PrincipalForm[d_Integer?Negative] /; Mod[d, 4] == 1 := {1, 1, (1-d)/4}

Options[DirichletComposition] = {"Reduce" -> False};

(* Computes the Dirichlet composition of the forms f1 and f2 *)
DirichletComposition[f1: {a1_, b1_, c1_}, f2: {a2_, b2_, c2_}, ops: OptionsPattern[]] /; equalDiscriminantQ[f1, f2] && GCD[a1, a2, (b1 + b2)/2] == 1 && ReducedFormQ[f1, f2] (*&& ReducedFormQ[f2]*) := Module[
	{disc = QuadraticFormDiscriminant[f1], b = dirichletB[f1, f2], prod = a1 a2},
	If[
		OptionValue["Reduce"],
		ReduceForm[{prod, b, (b^2 - disc)/(4 prod)}],
		{prod, b, (b^2 - disc)/(4 prod)}
	]
]

(* If the forms f1 and f2 do not satisfy the necessary congruence condition, f2 must be properly equivalent to a form f3 such that f1 and f3
satisfy the necessary congruence condition *)
DirichletComposition[f1: {a1_, b1_, c1_}, f2: {a2_, b2_, c2_}, ops: OptionsPattern[]] /; equalDiscriminantQ[f1, f2] := Module[
	{disc = QuadraticFormDiscriminant[f1], m, factors, residues, f3, p, q, r, s, b, prod},
	(* Construct an integer m which is properly represented by f2 and coprime to a1 *)
	factors = FactorInteger[a1][[;;, 1]];
	residues = Table[
		SelectFirst[
			{{1, 0}, {0, 1}, {1, 1}},
			GCD[# . {{a2, b2/2}, {b2/2, c2}} . #, i] == 1&
		],
		{i, factors}
	];
	{p, q} = {#1, #2}/GCD[#1, #2]& @@ Table[ChineseRemainder[residues[[;;, i]], factors], {i, 2}];
	m = {p, q} . {{a2, b2/2}, {b2/2, c2}} . {p, q};
	(* Construct a qf f3(x,y)=mx^2+Bxy+Cy^2, which is properly equivalent to f2 *)
	{s, r} = {#1, #2}& @@ ExtendedGCD[p, q][[2]];
	f3 = {m, 2a2 p r + b2 p s + b2 r q + 2c2 q s, {r, s} . {{a2, b2/2}, {b2/2, c2}} . {r, s}};
	
	(* By construction GCD[a1, m]=1, so we can compute the constant B which is needed to Dirichlet compose the forms f1 and f3 *)
	b = dirichletB[f1, f3];
	prod = a1 m;
	
	If[
		OptionValue["Reduce"],
		ReduceForm[{prod, b, (b^2 - disc)/(4 prod)}],
		{prod, b, (b^2 - disc)/(4 prod)}
	]
]

End[];
EndPackage[];