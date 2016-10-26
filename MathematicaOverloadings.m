(* :Warning:

* This package Makes ArrayReshape work with any expression, despite this generting
{ArrayReshape::list, Part::partd, Part::partd, Part::partd,
 General::stop}

* This package adds the attribute HoldFirst to HoldFirst to make it act like an anonymous data-structure with this property.

*)

(* --- New symbol discipline --- *)
(* external code is not supposed to e.g. pollute Global` *)
(* Global` is intended for local variables and workspace (lost when mathematica is closed) *)

(* using only few local variables so that we won't have to protect much to keep up what we promise *)
Protect[s, ass, symbol, symbolName, context, name, a];

Unprotect@StringFirst; ClearAll@StringFirst;
StringFirst[s_] := StringTake[s,1];
Protect@StringFirst;

Unprotect@StringLast; ClearAll@StringLast;
StringLast[s_] := StringTake[s,{-1}];
Protect@StringLast;

Unprotect@StringSecond; ClearAll@StringSecond;
StringSecond[s_] := StringTake[s,{2}];
Protect@StringSecond;

$NewSymbol::$disallowed =
    "````: $ in user-defined contexts are disallowed - don't use globals.\n``";

$NewSymbol::lowercase =
    "````: Symbols not in Global`.` may not start with lowercase \
letters.\n``";

Undefined::msg = "``. Check argument counts and patterns and definition conditions.\n``"

Unprotect@NoOwnValues; ClearAll@NoOwnValues;
NoOwnValues::msg =
    "Cannot set ``. `` cannot have OwnValues.\n``";
Protect[NoOwnValues];


Unprotect@NoDownValues; ClearAll@NoDownValues;
NoDownValues::msg =
    "Cannot define ``. `` cannot have DownValues/TagValues/SubValues.\n\
``";
Protect[NoDownValues];

Unprotect@UnsupportedSymbol; ClearAll@UnsupportedSymbol;
UnsupportedSymbol::msg =
    "Don't know what to do with symbol ``.\n``";
Protect[UnsupportedSymbol];


Unprotect@MessageAbort; ClearAll@MessageAbort;
MessageAbort~SetAttributes~HoldAll;
MessageAbort[s___] := StackInhibit@(Message[s, StackTrace[]]; Abort[]);
Protect[MessageAbort];


Unprotect@MessageUndefined; ClearAll@MessageUndefined;
MessageUndefined~SetAttributes~HoldAll;
MessageUndefined[s_] := MessageAbort[Undefined::msg, Block[{$ContextPath={"System`"},$Context="other`"},ToString@HoldForm@s]]
Protect[MessageUndefined];


Unprotect@DisallowDownValues; ClearAll@DisallowDownValues;

DisallowDownValues[s_Symbol] := (
    (* TODO why not assign these rules to s instead of Set etc.?*)
  Unprotect[SetDelayed, Set, TagSetDelayed, TagSet];

  SetDelayed /: ass : SetDelayed[s[___], _] :=
      MessageAbort[NoDownValues::msg, HoldForm@ass, HoldForm@s];

  Set /: ass : Set[s[___], _] :=
      MessageAbort[NoDownValues::msg, HoldForm@ass, HoldForm@s];

  TagSet /: ass : TagSet[s, _, _] :=
      MessageAbort[NoDownValues::msg, HoldForm@ass, HoldForm@s];

  TagSetDelayed /: ass : TagSetDelayed[s, _, _] :=
      MessageAbort[NoDownValues::msg, HoldForm@ass,
        HoldForm@s];

  Protect[SetDelayed, Set, TagSetDelayed, TagSet];
);
Protect[DisallowDownValues];



Unprotect@DisallowOwnValues; ClearAll@DisallowOwnValues;

DisallowOwnValues::usage = "DisallowOwnValues[s] makes assigning a value to s crash the system while allowing DownValues etc."
DisallowOwnValues[s_Symbol] := (
  Unprotect[Set];
  Set /: ass : Set[s, _] :=
      MessageAbort[NoOwnValues::msg, HoldForm@ass, HoldForm@s];

  Protect[Set];
);
Protect[DisallowOwnValues];

Unprotect@MakeUndefinedFunction; ClearAll@MakeUndefinedFunction;
MakeUndefinedFunction::usage = "MakeUndefinedFunction[s] Makes s called on unknown arguments, i.e. s[___], crash the system.";
MakeUndefinedFunction[s_Symbol] := a : s[___] := MessageUndefined[a];
Protect[MakeUndefinedFunction];

(* note: $NewSymbol does not really depend on this, but it is convenient to have it near MakeUndefinedFunction *)
Unprotect@RemoveUndefinedFunction; ClearAll@RemoveUndefinedFunction;
RemoveUndefinedFunction[symbol_Symbol] := a : symbol[___]=.;
Protect[RemoveUndefinedFunction];

$NewSymbol =
    Function[{name, context}, With[{symbolName = context <> name}, {symbol = Symbol@symbolName},
      If[StringLength@name === 0, Return[]];

      (* Global`:
       - OwnValues disallowed on uppercase variables
       - lowercase for symbolic variables, arguments, With statements and Replacements, no own values (Protected)
       - $x can have own values (todo (check) but no up/sub/down values)
       *)

      If[context == "Global`",

        Which[
        (* uppercase globals: no OwnValues, use for functions *)
          context == "Global`" && (
            UpperCaseQ@StringFirst@name
                || (StringFirst@name == "$" && UpperCaseQ@StringSecond@name)
          ),
          DisallowOwnValues[symbol]; MakeUndefinedFunction[symbol],

        (* $ globals: no down Values *)
          StringFirst@name == "$", DisallowDownValues[symbol],

        (* lowercase Globals: no values whatsoever, any symbolic combination allowed (and unevaluated) *)
        (* use like $Formal symbols *)
          LowerCaseQ@StringFirst@name, Protect[symbol],

        (*this should have covered all cases *)
          True, MessageAbort[UnsupportedSymbol, symbolName]
        ];
        Return[];
      ];

    (* Allow any symbols in non-Global` *)
    ]];

(* from now on, symbols will follow the discipline automatically *)

(* --- End New symbol discipline --- *)

(* -- Extend HoldForm for more clear display --*)

(* TODO fix recursion bugs, WordTranslate["全部"] seems to give very big result? double error message? 
Unprotect@HoldForm;
Format[HoldForm[x_], 
   StandardForm] := {boxes = MakeBoxes@x, bg = LightBlue}~With~
   RawBoxes@
    InterpretationBox[
     TagBox[StyleBox[boxes, Background -> bg], "", 
      Selectable -> False], HoldForm[x]];
Protect@HoldForm;
*)
(*
(* TODO this one causes StackTrace window to show lots of Interpretation [] Style[] sprinkled across*)
MakeBoxes[x_HoldForm, StandardForm] :=
    Block[{$holdstyle = True},
      Interpretation[
        Style[x, Background -> LightBlue, StripOnInput -> False,
          Selectable -> False], x] // ToBoxes] /; ! TrueQ[$holdstyle]
        *)
(* -- Extend ArrayReshape --*)
ArrayReshape; (* cache it *)
Unprotect@ArrayReshape;

ArrayReshape[v_Symbol, dims : {w_Integer}] :=
    (*Array[v[[#]] &, h]; or *) Table[v[[x]], {x, w}];
ArrayReshape[v_Symbol, dims : {h_Integer, w_Integer}] :=
    Table[v[[(y - 1)*w + x]], {y, h}, {x, w}];
ArrayReshape[v_Symbol, dims : {d_Integer, h_Integer, w_Integer}] :=
    Table[v[[(z - 1)*w*d + (y-1)*w + x]], {z, d}, {y, h}, {x, w}];

Protect@ArrayReshape;

(* -- Extend HoldFirst --*)
HoldFirst~SetAttributes~HoldFirst

(* -- Extend FileNameJoin --*)
Unprotect[FileNameJoin];
FileNameJoin[a_String, b_String] := FileNameJoin[{a, b}];
Protect[FileNameJoin];

(*Operator form extension to FileNameTake*)
Unprotect@FileNameTake;
FileNameTake[n_Integer] := FileNameTake[#, n] &;
Protect@FileNameTake;

(* -- Extend Assert --*)
Unprotect@Assert;

StackTraceRemovedContexts[] := {"System`"}

$Pre = StackComplete

StackTrace[] :=
(* use in combination with StackComplete for a more complete stack trace, best use that as $Pre *)
    Module[{innerHead},

    (*must pass by HoldForm that is used in Stack*)
      innerHead[HoldForm[h_[___]]] := HoldForm@h;
      innerHead[HoldForm[h_Symbol]] := HoldForm@h;

      innerHead /@ Stack[x_Symbol /; StackTraceRemovedContexts[]~FreeQ~With[{y=x (* Evaluate Symbol["str"]*)},Context[y]]]
    ];

(* final `3` is for user's message, \n`4` is for stackTrace[] *)
Assert::asrttf = 
  "Assertion test `1` evaluated to `2` that is neither True nor \
False. `3`\n`4`"; (* TODO show at least which Head there was when the expressions are very long *)
Assert::asrtfr = 
  "Assertion failed. Assertion test `1` evaluated to `2` which is \
False. `3`\n`4`";
Assert::asrtf = "Assertion `1` failed. `2`\n`3`";

Unprotect[AssertSub, HeldInputForm, formatExtra,call$AssertFunction];
ClearAll[AssertSub, HeldInputForm, formatExtra,call$AssertFunction];


AssertSub~SetAttributes~HoldAllComplete;(*HoldAll to avoid undesired \
re-evaluations*)

HeldInputForm~SetAttributes~HoldAllComplete;
HeldInputForm[x_] := RawBoxes@MakeBoxes@HoldForm@InputForm@x;

formatExtra[extra___] := Row[(*HeldInputForm/@*){extra}];
call$AssertFunction~SetAttributes~HoldAllComplete;
call$AssertFunction[test_, extra___] := $AssertFunction[
  HoldComplete[Assert[test, extra]]]

(* base-case *)
AssertSub[True, ___] := Null;

(* Message generating functions *)
AssertSub[False, test_, HoldComplete@op_, 
  HoldComplete@dummy_[ops___], {extra___}] := (Message[Assert::asrtfr,
    HeldInputForm@test, HeldInputForm@op[ops], formatExtra@extra, StackTrace[]];
  call$AssertFunction[test, extra];)

AssertSub[False, 
  test_, {extra___}] := (Message[Assert::asrtf, HeldInputForm@test,
   formatExtra@extra, StackTrace[]]; call$AssertFunction[test, extra];)

AssertSub[result_, 
  test_, _HoldComplete | PatternSequence[], _HoldComplete | 
   PatternSequence[], {extra___}] := (Message[Assert::asrttf, 
   HeldInputForm@test, HeldInputForm@result, formatExtra@extra, StackTrace[]];
  call$AssertFunction[test, extra];)

(* TODO this does not play nicely with up-values *)
Assert[test : logicalOperation_[operands__], extra___] :=
    StackInhibit@Module[{dummy}, With[
    {(*evaluate parts in standard order: first the head*)
     op = logicalOperation, 
     ops = (If[logicalOperation~MatchQ~_Symbol?AtomQ,dummy~SetAttributes~Attributes@logicalOperation];dummy[
       operands])(*use inert dummy Head instead of 'List' to not eliminate Nothing. Furthermore, the head must have the same Attributes as the operation*)
     },
    {result = logicalOperation @@ ops(*finish evaluation*)},
    (*HoldComplete op and ops: 
    they might evaluate again now that result is computed, 
    but that would not usually happen*)
    AssertSub[result, test, HoldComplete@op, HoldComplete@ops, {extra}]
    ]];

Assert[test_, extra___] :=
    StackInhibit@With[{result = test}, AssertSub[result, test, {extra}]]

Protect@Assert;
Protect@AssertSub;
(* -- End of Assert extension --*)
$AssertFunction = Abort[] &;



(* -- Extend Message ::shdw --*)
(*
Unprotect@Message;
Message[MessageName[s_, "shdw"],___] := Null;
Protect@Message;

(* disable ::shdw, convert to note *)
Unprotect;
Message; (* make sure the symbol is available *)
Unprotect@Message;
Message[MessageName[s_, "shdw"], 
   rest : PatternSequence[snHeld_, pathsHeld_, newpath_]] := 
  With[{paths = ReleaseHold@pathsHeld},
   {memberpaths = Select[$ContextPath, MemberQ[paths, #] &], 
    sn = ReleaseHold@snHeld},
    If[Length@memberpaths > 0,

   Print@StringTemplate[
      "Note: Symbol `` added in context ``, so that it now appears in \
multiple contexts: ``. On the context path, it is currently found in: \
``. Definitions in the first context of the context path, ``, will \
shadow any other definitions."][sn, newpath, paths, memberpaths, 
     First@memberpaths];
   (*symbol name*)
   Assert[SymbolName@s === sn];
   
   (*demonstrate that First@
   memberpaths is the context used for short names*)
   Assert[ToExpression@StringTemplate[
       "Unevaluated@`` === Unevaluated@````"
       ][sn, First@memberpaths, sn
      ]
    ];
   
   (*and not any other context*)
   Assert@AllTrue[TrueQ][ToExpression@StringTemplate[
          "Unevaluated@`` =!= Unevaluated@````"
          ][sn, #, sn
         ] & /@ DeleteCases[paths, First@memberpaths]
     ];
   ]];

Protect@Message;
*)
(* -- End Extend Message ::shdw --*)

(* -- Extend OptionValue --*)
(*make it a bug that OptionValue stays unevaluated

I hope this doesn't break built-in functions in weird ways*)
Unprotect@OptionValue
OptionValue::neval =
    "OptionValue did not evaluate when used as ``. Did you specify \
OptionsPattern[] in the parameter list and is the given parameter \
part of the Options[]? Is this begin evaluated within a := function, not an assignment =?\n``";

$checkingOptionValue = True;
oe : OptionValue[x_] /; $checkingOptionValue &&
    Block[{$checkingOptionValue = False},
      Unevaluated@OptionValue@x === OptionValue@x] :=
    StackInhibit@Message[OptionValue::neval, HoldForm@oe, StackTrace[]];
Protect@OptionValue;
(*after this, the following creates a message:
ClearAll[f];
f[]:=Echo@OptionValue@Method;
Options@f={Method\[Rule]"CPU"};
f[]
*)
(* -- End Extend OptionValue --*)

