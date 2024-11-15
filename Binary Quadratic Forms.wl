(* ::Package:: *)

(* ::Title:: *)
(*Binary Quadratic Forms*)

(* ::Subtitle:: *)
(*Jack Heimrath 2024*)

(* ::Section:: *)
(*BeginPackage*)

BeginPackage["QuadraticForms`"];
(*Throughout this package, when talking about a (quadratic) form {a, b, c}, we will mean the quadratic form ax^2+bxy+cy^2*)
ClearAll[QuadraticFormDiscriminant, PositiveDefiniteFormQ, PositiveDefiniteFormQ, PrimitiveFormQ, ReducedFormQ, ReduceForm, EquivalentFormsQ,
ReducedForms, ClassNumber, GenusRepresentatives, SameGenusQ, PrincipalForm, DirichletComposition, ClassGroup]

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
GenusRepresentatives::usage = "GenusRepresentatives[f] returns the values represented by the genus containing the form f";
SameGenusQ::usage = "SameGenusQ[f, g] returns True if the forms f and g belong to the same genus, and False otherwise";
PrincipalForm::usage = "PrincipalForm[d] returns the principle form of discriminant d";
DirichletComposition::usage = "DirichletComposition[f, g] returns the Dirichlet Composition of the forms f and g";
ClassGroup::usage = "ClassGroup[d] returns the multiplication table for the Class Group of discriminant d";

Begin["`Private`"];

(* ::Subsection::Closed:: *)
(*Elementary Theory of Quadratic Forms*)

(* ::Subsubsection::Closed:: *)
(*Helper Functions*)
ClearAll[matrixForm, sl2Action];

matrixForm[{a_, b_, c_}] := {{a, b/2}, {b/2, c}}

sl2Action[m_, f_] := Block[
	{x, y},
	With[
		{u = x^2, v = x y, w = y^2},
		Coefficient[m.{x, y}.matrixForm[f].m.{x, y}, #]& /@ {u, v, w}
	]
]

(* ::Subsubsection::Closed:: *)
(*Helper Functions*)

QuadraticFormDiscriminant[{a_, b_, c_}] := b^2 - 4 a c
QuadraticFormDiscriminant[f_List, forms__List] := QuadraticFormDiscriminant /@ {f, forms}

PositiveDefiniteFormQ[{a_, b_, c_}] := (a > 0 && QuadraticFormDiscriminant[{a, b, c}] < 0)

PrimitiveFormQ[{a_, b_, c_}] := (GCD[a, b, c] == 1)

ReducedFormQ[f: {a_, b_, c_}] := (PrimitiveFormQ[f] && (Abs[b] <= a <= c) && If[Abs[b] == a || a == c, b >= 0, True])
ReducedFormQ[f_List, forms__List] := And @@ (ReducedFormQ /@ {f, forms})

ReduceForm[f: {a_, b_, c_}] /; PositiveDefiniteFormQ[f] && PrimitiveFormQ[f] := Module[
	{a1 = a, b1 = b, c1 = c, m, rule},
	Which[
		(* Ensure a\[LessEqual]c *)
		a1 > c1,
			ReduceForm[sl2Action[{{0, -1}, {1, 0}}, f]],
		(* Ensure |b|\[LessEqual]a *)
		Abs[b1] > a1,
			{rule} = Minimize[Abs[b1 + 2a1 m], m, Integers][[2]];
			ReduceForm[sl2Action[{{1, m}, {0, 1}}, {a1, b1, c1}] /. rule],
		(* Ensure b>0 if |b|==a *)
		b1 == -a1,
			ReduceForm[sl2Action[{{1, 1}, {0, 1}}, {a1, b1, c1}]],
		True,
			{a1, b1, c1}
	]
]

(* Keeping the old implementation for now, might remove later *)
(* ReduceForm[f: {a_, b_, c_}] /; PositiveDefiniteFormQ[f] && PrimitiveFormQ[f] := Module[
	{a1 = a, b1 = b, c1 = c, m, rule},
	(* Ensure a\[LessEqual]c *)
	{a1, b1, c1} = If[
		a1 > c1,
		sl2Action[{{0, -1}, {1, 0}}, f],
		{a1, b1, c1}
	];
	(* Ensure |b|\[LessEqual]a *)
	{a1, b1, c1} = If[
		Abs[b1] > a1,
		{rule} = Minimize[Abs[b1 + 2a1 m], m, Integers][[2]];
		sl2Action[{{1, m}, {0, 1}}, {a1, b1, c1}] /. rule,
		{a1, b1, c1}
	];
	(* Ensure b>0 if |b|==a *)
	{a1, b1, c1} = If[
		b1 == -a1,
		sl2Action[{{1, 1}, {0, 1}}, {a1, b1, c1}],
		{a1, b1, c1}
	];
	(* Repeat procedure, if necessary *)
	If[
		!ReducedFormQ[{a1, b1, c1}],
		ReduceForm[{a1, b1, c1}],
		{a1, b1, c1}
	]
] *)

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
ClearAll[equalDiscriminantQ, dirichletB, coprimeRepresentative]

equalDiscriminantQ[f1: {a1_, b1_, c1_}, f2: {a2_, b2_, c2_}] := Equal @@ QuadraticFormDiscriminant[f1, f2]

dirichletB[f1: {a1_, b1_, c1_}, f2: {a2_, b2_, c2_}] /; equalDiscriminantQ[f1, f2] && (GCD[a1, a2, (b1 + b2)/2] == 1) := Module[
	{disc = QuadraticFormDiscriminant[f1], b},
	(* SelectFirst[Range[0, 2a1 a2 - 1], Mod[# - b1, 2a1] == Mod[# - b2, 2a2] == Mod[#^2 - disc, 4a1 a2] == 0&] *)
	(* The above method is a brute force method, even if it's reasoanbly efficient. This is not brute force, but is buggy. *)
	If[
		b1 + b2 == 0,
		SolveValues[(a2 b) == (a2 b1) && (a1 b) == (a1 b2), b, Modulus -> (2 a1 a2)][[1]],
		SolveValues[(a2 b) == (a2 b1) && (a1 b) == (a1 b2) && (b1+b2)/2 b == (b1 b2 + disc)/2, b, Modulus -> (2 a1 a2)][[1]]
	]
]

coprimeRepresentative[f_, m_] := Module[
	{factors = FactorInteger[m][[;;, 1]], remainders, p, q},
	remainders = Table[
		SelectFirst[
			{{1, 0}, {0, 1}, {1, 1}},
			GCD[# . matrixForm[f] . #, i] == 1&
		],
		{i, factors}
	];
	{p, q} = {#1, #2}/GCD[#1, #2]& @@ Table[ChineseRemainder[remainders[[;;, i]], factors], {i, 2}];
	{{p, q}.matrixForm[f].{p, q}, {p, q}}
]

(* ::Subsubsection:: *)
(*Main Functions*)

GenusRepresentatives[f: {a_, b_, c_}] /; PrimitiveFormQ[f] := Module[
	{disc = -QuadraticFormDiscriminant[f], bound},
    bound = Ceiling[disc/2];
	Select[Union[Flatten[Table[Mod[f . {x^2, x y, y^2}, disc], {x, -bound, bound}, {y, -bound, bound}]]], GCD[disc, #] == 1&]
]

SameGenusQ[f1: {a1_, b1_, c1_}, f2: {a2_, b2_, c2_}] /; equalDiscriminantQ[f1, f2] := Equal @@ (GenusRepresentatives /@ {f1, f2})
SameGenusQ[{a1_, b1_, c1_}, {a2_, b2_, c2_}] := False;

PrincipalForm[d_Integer?Negative] /; Mod[d, 4] == 0 := {1, 0, -d/4}
PrincipalForm[d_Integer?Negative] /; Mod[d, 4] == 1 := {1, 1, (1-d)/4}

Options[DirichletComposition] = {"Reduce" -> False};

(* Computes the Dirichlet composition of the forms f1 and f2 *)
DirichletComposition[f1: {a1_, b1_, c1_}, f2: {a2_, b2_, c2_}, ops: OptionsPattern[]] /; equalDiscriminantQ[f1, f2] && ReducedFormQ[f1, f2] && GCD[a1, a2, (b1 + b2)/2] == 1 := Module[
	{disc = QuadraticFormDiscriminant[f1], b = dirichletB[f1, f2], prod = a1 a2, f3},
	f3 = {prod, b, (b^2 - disc)/(4 prod)};
	If[
		OptionValue["Reduce"] && !ReducedFormQ[f3],
		ReduceForm[f3],
		f3
	]
]

(* If the forms f1 and f2 do not satisfy the necessary congruence condition, f2 must be properly equivalent to a form f3 such that f1 and f3
satisfy the necessary congruence condition *)
DirichletComposition[f1: {a1_, b1_, c1_}, f2: {a2_, b2_, c2_}, ops: OptionsPattern[]] /; equalDiscriminantQ[f1, f2] && ReducedFormQ[f1, f2] := Module[
	{disc = QuadraticFormDiscriminant[f1], m, f3, p, q, r, s, b, prod},
	(* Construct an integer m which is properly represented by f2 and coprime to a1 *)
	{m, {p, q}} = coprimeRepresentative[f2, a1];
	(* Construct a form f3(x,y)=mx^2+Bxy+Cy^2, which is properly equivalent to f2 *)
	{s, r} = {#1, -#2}& @@ ExtendedGCD[p, q][[2]];
	f3 = {#1, #2, #3}/GCD[#1, #2, #3]& @@ {m, 2a2 p r + b2 p s + b2 r q + 2c2 q s, {r, s}.matrixForm[f2].{r, s}};
	
	(* By construction GCD[a1, m]=1, so we can compute the constant b which is needed to Dirichlet compose the forms f1 and f3 *)
	b = dirichletB[f1, f3];
	prod = a1 f3[[1]];
	
	If[
		OptionValue["Reduce"],
		ReduceForm[{prod, b, (b^2 - disc)/(4 prod)}],
		{prod, b, (b^2 - disc)/(4 prod)}
	]
]

DirichletComposition[f1_, f2_, ops: OptionsPattern[]] /; equalDiscriminantQ[f1, f2] := DirichletComposition[#1, #2, ops]& @@ (ReduceForm /@ {f1, f2})

ClassGroup[d_Integer?Negative] /; Mod[d, 4] == 0 || Mod[d, 4] == 1 := Module[
	{classes = ReducedForms[d], classNumber},
	classNumber = Length[classes];
	Grid[
		Table[
			Which[
				i == j == 1,
					Null,
				i == 1,
					classes[[j - 1]],
				j == 1,
					classes[[i - 1]],
				True,
					DirichletComposition[classes[[j - 1]], classes[[i - 1]], "Reduce" -> True]
			],
			{i, classNumber + 1},
			{j, classNumber + 1}
		],
		Dividers -> {2 -> True, 2 -> True}
	]
]

ClassGroup[d_Integer] := {}

End[];
EndPackage[];