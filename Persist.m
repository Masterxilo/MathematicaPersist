(* ::Package:: *)
(* depends on MathematicaOverloadings.m *)
BeginPackage["Persist`"]


Begin["`Private`"];
With[{seb=Persist`$SavedExpressionsBase},
  Unprotect["Persist`*", "Persist`Private`*"];
ClearAll["Persist`*", "Persist`Private`*"];
Persist`$SavedExpressionsBase=seb;
];
End[];

Persist::usage = "Persist[name, body] persists body unevaluated under the given name,
and persists the EvaluatingCell this is called from. Finally it evaluates body"
PersistDef::usage = "Saves only the body, not the cell, and evaluates it"

Global`MakeUndefinedFunction /@ Unevaluated@{
  PersistDef,Persist,
DepersistHeldDef,
DepersistDef,
DepersistCell,
DepersistCellPrint,
Depersist,
PersistedNames,
PersistedCells,
DepersistDefAll,
DepersistHeldDefAll,
DepersistCellAll,
$SavedExpressionsBase,
SaveExpression,
LoadExpression,
SavedExpressions
}

Print@"allok"

Depersist::trace = "``"
Off[Depersist::trace];

Begin["`Private`"];

EvaluatingCell[] := EvaluationCell[] // NotebookRead;
FullSymbolName[_[s_Symbol,___]] := FullSymbolName@s
FullSymbolName[s_Symbol] := Context@s <> SymbolName@Unevaluated@s;
FullSymbolName~SetAttributes~HoldAll;


$DepersistingAll = False;
DepersistDefAll[] /; !$DepersistingAll := (Message[Depersist::trace,"DepersistDefAll"];$DepersistingAll = True; DepersistDef ~Scan~PersistedNames[]; $DepersistingAll = False; );
DepersistDefAll[] /; $DepersistingAll := Echo@"DepersistDefAll already in progress";

DepersistHeldDefAll[] := DepersistHeldDef /@ PersistedNames[];

DepersistCellAll[] := DepersistCell /@ PersistedCells[];


(* Storage: uses def and cell prefixed SaveExpression (faster than LocalSymbol/LocalObjects) *)
(* SavedExpressions *)
toFileName@name_ := FileNameJoin@{$SavedExpressionsBase,name<>".m"}


SaveExpression[name_String,e_]:=Block[{$Context = "unusedContext`", $ContextPath = {}},
    (*mx not much faster and is not Gitable!*)
    (*Put[e,toFileName@name]*) (* does not deal with Format[] properly (evaluates it!) *)
    Print[SaveExpression,": ", name];
    Export[toFileName@name, FullForm@e, "String"]
];



LoadExpression[name_String]:=Get[toFileName@name];
SavedExpressions[]:=FileBaseName/@FileNames["*",$SavedExpressionsBase]
(* end of SavedExpressions, besides
$SavedExpressionsBase="C:\\Users\\Paul\\Dropbox\\Paul\\MasterarbeitShared\\Research\\MathematicaLibraries\\SavedExpressions"

in init.m
 *)

DepersistHeldDef[name_String] := LoadExpression["def"<>name];
DepersistCell[name_String] := LoadExpression["cell"<>name];

SavedExpressionsTotalOrderAdd[name_String] := Global`AppendLineToFileIfNotPresent[FindFile@"SavedExpressionsTotalOrder.txt", name];

Persist~SetAttributes~HoldRest;
Persist[n_String /; StringLength@n > 0, x_] :=
    With[{cell = EvaluatingCell[]},
    SaveExpression["cell" <> n, cell]; (* TODO should Cells be held, can they have evaluating variables? Well inside ToBoxes yes but otherwise?*)
    SavedExpressionsTotalOrderAdd[n];
    PersistDef[n, x] (*do not suppress this output: we want to see the result of PTest, for example *)
];
Persist[ns_Symbol, x_] :=  {n=(*FullSymbolName@*)ToString@Unevaluated@ns}~With~Persist[n,x]

PersistDef~SetAttributes~HoldRest;
PersistDef[n_String, x_] := (Assert[Not[n~StringStartsQ~"System`"]];SaveExpression["def" <> n, HoldComplete[x]];x);


PersistedCells[] := Flatten@StringCases[SavedExpressions[], StartOfString~~"cell"~~name__~~EndOfString :> name];
    
PersistedNames[] := Flatten@StringCases[SavedExpressions[], StartOfString~~"def"~~name__~~EndOfString :> name];

PersistedNames[se_StringExpression] := Flatten[PersistedNames[]~StringCases~(StartOfString~~se~~ EndOfString)];
PersistedNames[s_String] := PersistedNames[s~~___]
(* Usability: *)

DepersistHeldDef[s_Symbol] := {n=FullSymbolName@Unevaluated@s}~With~DepersistHeldDef@n
DepersistHeldDef[se_StringExpression] := DepersistHeldDef /@ PersistedNames@se;

DepersistDef[name_String] := ReleaseHold@DepersistHeldDef[name];
DepersistDef[names : {___String}] := ReleaseHold@*DepersistHeldDef ~Scan~ names;
DepersistDef[s_Symbol] := {n=FullSymbolName@Unevaluated@s}~With~DepersistDef@n
DepersistDef[se_StringExpression] := DepersistDef ~Scan~ PersistedNames@se;

DepersistCellPrint[s_Symbol] := {n=FullSymbolName@Unevaluated@s}~With~DepersistCellPrint@n


DepersistCellPrint[name_String] := CellPrint@DepersistCell[name];

DepersistCellPrint[se_StringExpression] := DepersistCellPrint ~Scan~ PersistedNames[se];

Depersist[s_] := DepersistCellPrint@s;

(*Persist*)


End[];

Protect["Persist`*"]
EndPackage[];



