(* ::Package:: *)

(* ::Title:: *)
(*Binary Quadratic Forms*)

(* ::Subtitle:: *)
(*Jack Heimrath 2024*)

(* ::Section:: *)
(*BeginPackage*)

BeginPackage["QuadraticForms`"];

(*Throughout this package, when talking about a (quadratic) form {a, b, c}, we will mean the quadratic form ax^2+bxy+cy^2*)

Unprotect[Discriminant];
Discriminant::usage = "Discriminant[{a, b, c}] computes the discriminant of the form {a, b, c}";
PositiveDefiniteFormQ::usage = "PositiveDefiniteFormQ[{a, b, c}] returns True if the form {a, b, c} is positive definite, and False otherwise";
PrimitiveFormQ::usage = "PrimitiveFormQ[{a, b, c}] returns True if the form {a, b, c} is primitive, and False otherwise";
ReducedFormQ::usage = "ReducedFormQ[{a, b, c}] returns True if the form {a, b, c} is reduced, and False otherwise";
ReduceForm::usage = "ReduceForm[{a, b, c}] returns the unique reduced form {a1, b1, c1} which is properly equivalent to {a, b, c}";
EquivalentFormsQ::usage = "EquivalentFormsQ[f, g] returns True if and only if the forms f and g are properly equivalent";
ReducedForms::usage = "ReducedForms[d] returns all reduced quadratic forms of discriminant d<0";
ClassNumber::usage = "ClassNumber[d] returns the number of reduced qudratic forms of discriminant d<0";


Begin["`Private`"];

(* ::Subsection::Closed:: *)
(*Fundamental Concepts*)

Discriminant[{a_, b_, c_}] := b^2 - 4 a c
Protect[Discriminant];

PositiveDefiniteFormQ[{a_, b_, c_}] := (a > 0 && Discriminant[{a, b, c}] < 0)

PrimitiveFormQ[{a_, b_, c_}] := (GCD[a, b, c] == 1)

ReducedFormQ[form: {a_, b_, c_}] := (PrimitiveFormQ[form] && (Abs[b] <= a <= c) && If[Abs[b] == a || a == c, b >= 0, True])

ReduceForm[form: {a_, b_, c_}] /; PositiveDefiniteFormQ[form] && PrimitiveFormQ[form] := Module[
	{a1, b1, c1, m},
	(* Enforce a\[LessEqual]c *)
	{a1, b1, c1} = If[a > c, {c, b, a}, form];
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
		Flatten[Table[Table[{i, j, SolveValues[d == Discriminant[{i, j, c}], c, Integers]}, {j, Range[-i, i]}], {i, Range[1, bound]}], 1],
		{p_Integer, q_Integer, {r_Integer}} /; ReducedFormQ[{p, q, r}] :> {p, q, r}
	]
]
ReducedForms[d_Integer?Negative] /; (Mod[d, 4] == 2 || Mod[d, 4] == 3) := {}

ClassNumber[d_Integer?Negative] := Length[ReducedForms[d]]

(* ::Subsection::Closed:: *)
(*Genus Theory*)



End[];
EndPackage[];