(* ::Package:: *)

(* ::Section:: *)
(*Begin*)


BeginPackage["lily`index`",{"lily`class`"}];
(*delete the class before clearing all symbols.*)
classUnset["index"]//Quiet;
Unprotect@@Names[$Context<>"*"];
ClearAll@@Names[$Context<>"*"];


(* ::Subsection:: *)
(*lily`list`*)


{
    classData,instanceData,instanceDefaultData,
    classDefine,classProtect,classUnset,
    instancePreIntercept,instancePostIntercept,
    instanceDefine,instanceDefault,
    instanceReset,instanceUnset,
    instanceAdd,instanceDelete
};


(* ::Subsection:: *)
(*Class index*)


contextDefine::usage = 
    "define and initiate contexts.";
contextDefineQ::usage = 
    "check whether a context is defined.";

contextDefault::usage = 
    "set default contexts.";

contextReset::usage = 
    "reset the contexts.";
contextUnset::usage = 
    "unset the contexts.";

contextAdd::usage = 
    "add to the contexts.";
contextDelete::usage = 
    "delete from the contexts.";

contextShow::usage = 
    "show the context.";


(* ::Subsection:: *)
(*Kernel functions*)


variableQ::usage = 
    "Symbol/String: \"variable\" or \"variableString\".";
labelQ::usage = 
    "Symbol/String: \"label\" or \"labelString\".";
variableLabelQ::usage = 
    "Symbol/String: \"variableLabel\" or \"variableLabelString\".";
scriptQ::usage = 
    "Integer/Symbol/String: null/\"\", natural number or single letter.";
labelScriptQ::usage = 
    "Integer/Symbol/String: label + script.";
variableLabelScriptQ::usage = 
    "Symbol/String: variable + label + script.";

variableMatchQ::usage = 
    "Symbol/String: symbol starting from variable.";
labelMatchQ::usage = 
    "Symbol/String: symbol containing label.";
variableLabelMatchQ::usage = 
    "Symbol/String: symbol starting from variableLabel or variable + label.";


null::usage = 
    "null <-> \"\".";
toString::usage = 
    "toString.";
toSymbol::usage = 
    "toSymbol.";


indexify::usage = 
    "indexify the variables in an expression by checking the labels and scripts. "<>
    "indexify[f[indices],g[indices],\"head\"->True/False,\"context\"->context]."<>
    "when the head f is List, Total@*List will be used."
indexifyAll::usage = 
    "indexify the variables in an expression without checking the labels and scripts. "<>
    "indexify[f[indices],g[indices],\"head\"->True/False,\"context\"->context]."<>
    "when the head f is List, Total@*List will be used."

indexSplit::usage = 
    "split Symbol/String into variable + label + script.";

indexForm::usage = 
    "format indexed variables in the the expression with Subsuperscript.";
indexFormBack::usage = 
    "collape the Subsuperscript in the expression back to indexed variable."


indexArray::usage = 
    "indexify + Array.";
indexPolynomial::usage = 
    "multi-variable polynomials.";


Begin["`Private`"];


(* ::Section:: *)
(*Private*)


(* ::Subsection:: *)
(*lily`base`*)


pink[expr_] :=
    Style[expr,RGBColor[1,0.5,0.5]];
violet[expr_] :=
    Style[expr,RGBColor[0.5,0.5,1]];
orange[expr_] :=
    Style[expr,RGBColor[1,0.5,0]];
    
symbolListQ[{___Symbol}] = True;
symbolListQ[_] = False;

systemQ[symbol_Symbol] :=
    Context@symbol==="System`";
systemQ[_] = False;

echo//Attributes = {HoldAll};
echo[code_] :=
    Module[ {codeResult},
        codeResult = code;
        Print[
            pink@ToString@Unevaluated@code,
            " = ",
            violet@codeResult
        ];
        codeResult
    ];

messageHideContext//Attributes = {HoldFirst};
messageHideContext[args__] :=
    Block[ {Internal`$ContextMarks = False},
        Message[args]
    ];


(* ::Subsection:: *)
(*Class index*)


(* ::Subsubsection:: *)
(*Argument patterns*)


ctx = _String|_Symbol;
ctxs = (_String|_Symbol)..;
ctxsList = {(_String|_Symbol)..};
site = Subscript|Superscript;


(* ::Subsubsection:: *)
(*contextDefine*)


contextDefine[contextList:ctxsList,scriptSite:site:Subscript,labelSite:site:Superscript] :=
    instanceDefine["index",contextList,<|"defaultScriptSiteByVariable"->scriptSite,"defaultLabelSite"->labelSite|>];
contextDefine[context:ctx,scriptSite:site:Subscript,labelSite:site:Superscript] :=
    instanceDefine["index",{context},<|"defaultScriptSiteByVariable"->scriptSite,"defaultLabelSite"->labelSite|>];

contextDefineQ::reportundef =
    "the context `` has not been defined.";    
contextDefineQ[context:ctx] :=
    KeyExistsQ[instanceData["index"],context];
contextDefineQ[_] = False;


(* ::Subsubsection:: *)
(*contextDefault*)


contextDefault[contextList:ctxsList] :=
    Module[ {},
        instanceDefault["index",contextList];
        Print["The default contexts: ",Row[contextList,", "],"."];
    ];
contextDefault[context:ctx] :=
    contextDefault[{context}];


(* ::Subsubsection:: *)
(*contextReset, contextUnset*)


contextReset[contextList:ctxsList] :=
    instanceReset["index",contextList];
contextReset[context:ctx] :=
    contextReset[{context}];


contextUnset[contextList:ctxsList] :=
    instanceUnset["index",contextList];
contextUnset[context:ctx] :=
    contextUnset[{context}];


(* ::Subsubsection:: *)
(*contextAdd*)


contextAdd[context:ctx,variableList_,labelList_] :=
    contextAdd`kernel[context,variableList,labelList];
contextAdd[context:ctx][variableList_,labelList_] :=
    contextAdd`kernel[context,variableList,labelList];    
contextAdd[contextList:ctxsList,variableList_,labelList_] :=
    Module[ {},
        contextAdd`kernel[#,variableList,labelList]&/@contextList;
    ];
contextAdd[contextList:ctxsList][variableList_,labelList_] :=
    Module[ {},
        contextAdd`kernel[#,variableList,labelList]&/@contextList;
    ];


contextAdd`kernel[context:ctx,variableList_,labelList_] :=
    instanceAdd["index",{context},<|
        "variable"->contextAdd`getSymbol[variableList],
        "label"->contextAdd`getSymbol[labelList],
        "scriptSiteByVariable"->contextAdd`padRule[variableList,classData["index","instanceProperty",context,"defaultScriptSiteByVariable"]],
        "labelSite"->contextAdd`padRule[labelList,classData["index","instanceProperty",context,"defaultLabelSite"]]
    |>];
contextAdd`padRule[list_,site_] :=
    Association@Replace[list,{x_Symbol:>Rule[x,site]},{1}];
contextAdd`getSymbol[list_] :=
    Replace[list,{Verbatim[Rule][x_,site_]:>x},{1}];


(* ::Subsubsection:: *)
(*contextDelete*)


contextDelete[context:ctx,variableList_,labelList_] :=
    contextDelete`kernel[{context},variableList,labelList];
contextDelete[context:ctx][variableList_,labelList_] :=
    contextDelete`kernel[{context},variableList,labelList];    
contextDelete[contextList:ctxsList,variableList_,labelList_] :=
    contextDelete`kernel[contextList,variableList,labelList];
contextDelete[contextList:ctxsList][variableList_,labelList_] :=
    contextDelete`kernel[contextList,variableList,labelList];


contextDelete`kernel[contextList:ctxsList,variableList_,labelList_] :=
    instanceDelete["index",contextList,<|
        "variable"->contextDelete`getSymbol[variableList],
        "label"->contextDelete`getSymbol[labelList],
        "scriptSiteByVariable"->contextDelete`padRule[variableList],
        "labelSite"->contextDelete`padRule[labelList]
    |>];
contextDelete`padRule[list_] :=
    Association@Replace[list,{x_Symbol:>Rule[x,Null]},{1}];
contextDelete`getSymbol =
    contextAdd`getSymbol;


(* ::Subsubsection:: *)
(*contextShow*)


contextShow[context:ctx]/;contextDefineQ[context] :=
    contextShow`kernel[
        "context"->context,
        instanceData["index",context]
    ];
contextShow[] :=
    contextShow`kernel[
        "default contexts"->classData["index","instanceDefaultList"],
        instanceDefaultData["index"]
    ];


contextShow`kernel[title_,assoc_] :=
    assoc//Query[<|
        title,
        "variable"->#variable,
        "label"->#label,
        "variable + label"->#variableLabel
    |>&]//Dataset;


(* ::Subsubsection:: *)
(*Intercepts*)


instancePreIntercept//Unprotect;
instancePreIntercept["instanceAdd"]["index",context_,"variable",list_] :=
    contextAddCheck["index",context,"variable",list];
instancePreIntercept["instanceAdd"]["index",context_,"label",list_] :=
    contextAddCheck["index",context,"label",list];    
instancePreIntercept//Protect;

contextAddCheck::varnonsymbol =
    "there are non symbols in \"variable\".";
contextAddCheck::varsyssymbol = 
    "there are System symbols in \"variable\".";
contextAddCheck::labelnonsymbol = 
    "there are non symbols in \"label\".";
contextAddCheck::labelsyssymbol = 
    "there are System symbols in \"label\".";
contextAddCheck::varlabeldup = 
    "there are duplicates in \"variable\" and \"label\": ``.";
contextAddCheck["index",context_,"variable",list_] :=
    Module[ {labelList},
        labelList = instanceData["index",context,"label"];
        Which[
            symbolListQ[list]===False,
                messageHideContext[contextAddCheck::varnonsymbol];
                Abort[],
            Or@@systemQ/@list===True,
                messageHideContext[contextAddCheck::varsyssymbol];
                Abort[],
            Intersection[list,labelList]=!={},
                messageHideContext[contextAddCheck::varlabeldup,
                    Intersection[list,labelList]
                ];
                Abort[]
        ];
    ];
contextAddCheck["index",context_,"label",list_] :=
    Module[ {variableList},
        variableList = instanceData["index",context,"variable"];
        Which[
            symbolListQ[list]===False,
                messageHideContext[contextAddCheck::labelnonsymbol];
                Abort[],
            Or@@systemQ/@list===True,
                messageHideContext[contextAddCheck::labelsyssymbol];
                Abort[],
            Intersection[list,variableList]=!={},
                messageHideContext[contextAddCheck::varlabeldup,
                    Intersection[list,variableList]
                ];
                Abort[]
        ];
    ];


(*firstly get the string version, then update to the default*)
instancePostIntercept//Unprotect;
instancePostIntercept["instanceReset"]["index",context_] :=
    contextUpdateString["index",context];
instancePostIntercept["instanceAdd"|"instanceDelete"]["index",context_,member_,list_] :=
    contextUpdateString["index",context];
instancePostIntercept//Protect;

contextUpdateString["index",context_] :=
    Module[ {variableString,labelString,variableLabelString,variableLabel},
        variableString = toString/@instanceData["index",context,"variable"];
        labelString = toString/@instanceData["index",context,"label"];
        variableLabelString = Flatten@Outer[StringJoin,variableString,labelString];
        variableLabel = toSymbol/@variableLabelString;
        AssociateTo[
            instanceData["index",context],
            {
                "variableString"->variableString,
                "labelString"->labelString,
                "variableLabelString"->variableLabelString,
                "variableLabel"->variableLabel
            }
        ];
    ];


(* ::Subsection:: *)
(*Default arguments*)


contextDefine[] :=
    Keys@instanceData["index"];
contextDefault[] :=
    classData["index","instanceDefaultList"];


(*reset/unset the default contexts*)
contextReset[] :=
    (contextReset@contextDefault[];);
contextUnset[] :=
    (contextUnset@contextDefault[];);


(*reset/unset all the defined contexts*)
contextReset[All] :=
    (contextReset@contextDefine[];);
contextUnset[All] :=
    (contextUnset@contextDefine[];);


(* ::Subsection:: *)
(*Kernel functions*)


variableQ[__] = False;

variableQ[string_String] :=
    MemberQ[instanceDefaultData["index","variableString"],string];
variableQ[symbol_Symbol] :=
    MemberQ[instanceDefaultData["index","variable"],symbol];

variableQ[string_String,context_] :=
    MemberQ[instanceData["index",context,"variableString"],string];
variableQ[symbol_Symbol,context_] :=
    MemberQ[instanceData["index",context,"variable"],symbol];


labelQ[__] = False;

labelQ[string_String] :=
    MemberQ[instanceDefaultData["index","labelString"],string];
labelQ[symbol_Symbol] :=
    MemberQ[instanceDefaultData["index","label"],symbol];

labelQ[string_String,context_] :=
    MemberQ[instanceData["index",context,"labelString"],string];
labelQ[symbol_Symbol,context_] :=
    MemberQ[instanceData["index",context,"label"],symbol];


variableLabelQ[__] = False;

variableLabelQ[string_String] :=
    MemberQ[instanceDefaultData["index","variableLabelString"],string];
variableLabelQ[symbol_Symbol] :=
    MemberQ[instanceDefaultData["index","variableLabel"],symbol];

variableLabelQ[string_String,context_] :=
    MemberQ[instanceData["index",context,"variableLabelString"],string];
variableLabelQ[symbol_Symbol,context_] :=
    MemberQ[instanceData["index",context,"variableLabel"],symbol];


scriptQ[_] = False;

scriptQ[null|""|"0"] = True;
scriptQ[string_String] :=
    DigitQ@string&&!StringStartsQ[string,"0"]||
        StringLength@string===1&&LetterQ@string;
scriptQ[symbol_Symbol] :=
    (StringLength@#===1&&LetterQ@#)&@toString@symbol;
scriptQ[natural_Integer] :=
    NonNegative@natural;


labelScriptQ[__] = False;

labelScriptQ[string_String] :=
    StringMatchQ[string, 
        StartOfString~~label___~~script___~~EndOfString/;
            MemberQ[instanceDefaultData["index","labelString"],label]&&scriptQ@script
    ];
labelScriptQ[string_String,context_] :=
    StringMatchQ[string, 
        StartOfString~~label___~~script___~~EndOfString/;
            MemberQ[instanceData["index",context,"labelString"],label]&&scriptQ@script
    ];    

labelScriptQ[symbol_Symbol] :=
    labelScriptQ@toString@symbol;
labelScriptQ[symbol_Symbol,context_] :=
    labelScriptQ[toString@symbol,context];

labelScriptQ[natural_Integer] :=
    NonNegative@natural;
labelScriptQ[natural_Integer,context_] :=
    NonNegative@natural;


variableLabelScriptQ[__] = False;

variableLabelScriptQ[string_String] :=
    StringMatchQ[string, 
        StartOfString~~variableLabel___~~script___~~EndOfString/;
            MemberQ[instanceDefaultData["index","variableLabelString"],variableLabel]&&scriptQ@script
        ];
variableLabelScriptQ[string_String,context_] :=
    StringMatchQ[string, 
        StartOfString~~variableLabel___~~script___~~EndOfString/;
            MemberQ[instanceData["index",context,"variableLabelString"],variableLabel]&&scriptQ@script
    ];

variableLabelScriptQ[symbol_Symbol] :=
    variableLabelScriptQ@toString@symbol;
variableLabelScriptQ[symbol_Symbol,context_] :=
    variableLabelScriptQ[toString@symbol,context];


variableMatchQ[__] = False;

variableMatchQ[string_String,variable_String?variableQ] :=
    StringMatchQ[string, 
        StartOfString~~variable~~labelScript___~~EndOfString/;
            labelScriptQ@labelScript
    ];
variableMatchQ[symbol_Symbol,variable_Symbol] :=
    variableMatchQ[toString@symbol,toString@variable];


labelMatchQ[__] = False;

labelMatchQ[string_String,label_String?labelQ] :=
    StringMatchQ[string, 
        StartOfString~~variable___~~label~~script___~~EndOfString/;
            variableQ@variable&&scriptQ@script
    ];
labelMatchQ[symbol_Symbol,label_Symbol] :=
    labelMatchQ[toString@symbol,toString@label];


variableLabelMatchQ[__] = False;

variableLabelMatchQ[string_String,variableLabel_String?variableLabelQ] :=
    StringMatchQ[string,
        StartOfString~~variableLabel~~script___~~EndOfString/;
            scriptQ@script
    ];
variableLabelMatchQ[symbol_Symbol,variableLabel_Symbol] :=
    variableLabelMatchQ[toString@symbol,toString@variableLabel];

variableLabelMatchQ[string_String,variable_String?variableQ,label_String?labelQ] :=
    StringMatchQ[string,
        StartOfString~~variable~~label~~script___~~EndOfString/;scriptQ@script
    ];
variableLabelMatchQ[symbol_Symbol,variable_Symbol,label_Symbol] :=
    variableLabelMatchQ[toString@symbol,toString@variable,toString@label];


(* ::Subsection:: *)
(*Kernul functions*)


(* ::Subsubsection:: *)
(*toString/toSymbol*)


(*to deal with the non-invertibility of ToString and ToExpression at Null.*)
toString[null] = "";
toString[Null] = "Null";
toString[string_String] :=
    string;
toString[symbol_Symbol] :=
    SymbolName[symbol];
toString[integer_Integer] :=
    ToString[integer];

toSymbol[""] = null;
toSymbol[string_String] :=
    ToExpression[string];


(* ::Subsubsection:: *)
(*indexify/indexifyAll*)


indexify[labelScript_?labelScriptQ][expr_] :=
    indexify`singleIndexOnExpression[labelScript][expr];
    
indexify[labelScripts___?labelScriptQ][expr_] :=
    indexify`multiIndexOnExpression[labelScripts][expr];

indexify[arg:_Symbol[___?labelScriptQ]][expr_] :=
    indexify`singleWrappedIndexOnExpr[arg][expr];

indexify[args:_Symbol[___?labelScriptQ]..,linker_Symbol:indexify`linker][expr_] :=
    indexify`multiWrappedIndexOnExpr[args,linker][expr];

indexify[labelScript_?labelScriptQ,opts:OptionsPattern[]][expr_] :=
    indexify`singleIndexOnExpression`withOptions[labelScript,opts][expr];

indexify[labelScripts___?labelScriptQ,opts:OptionsPattern[]][expr_] :=
    indexify`multiIndexOnExpression`withOptions[labelScripts,opts][expr];

indexify[arg:_Symbol[___?labelScriptQ],opts:OptionsPattern[]][expr_] :=
    indexify`singleWrappedIndexOnExpression`withOptions[arg,opts][expr];

indexify[args:_Symbol[___?labelScriptQ]..,linker_Symbol:indexify`linker,opts:OptionsPattern[]][expr_] :=
    indexify`multiWrappedIndexOnExpression`withOptions[args,linker,opts][expr];


indexifyAll[labelScript_][expr_] :=
    indexify`singleIndexOnExpression[labelScript][expr];
    
indexifyAll[labelScripts___][expr_] :=
    indexify`multiIndexOnExpression[labelScripts][expr];

indexifyAll[arg:_Symbol[___]][expr_] :=
    indexify`singleWrappedIndexOnExpr[arg][expr];

indexifyAll[args:_Symbol[___]..,linker_Symbol:indexify`linker][expr_] :=
    indexify`multiWrappedIndexOnExpr[args,linker][expr];

indexifyAll[labelScript_,opts:OptionsPattern[]][expr_] :=
    indexify`singleIndexOnExpression`withOptions[labelScript,opts][expr];

indexifyAll[labelScripts___,opts:OptionsPattern[]][expr_] :=
    indexify`multiIndexOnExpression`withOptions[labelScripts,opts][expr];

indexifyAll[arg:_Symbol[___],opts:OptionsPattern[]][expr_] :=
    indexify`singleWrappedIndexOnExpression`withOptions[arg,opts][expr];

indexifyAll[args:_Symbol[___]..,linker_Symbol:indexify`linker,opts:OptionsPattern[]][expr_] :=
    indexify`multiWrappedIndexOnExpression`withOptions[args,linker,opts][expr];


(*single index acting on symbol*)
indexify`singleIndexOnSymbol[labelScript_][variable_] :=
    toSymbol[
        toString@variable<>toString@labelScript
    ];
(*multiple indices acting on symbol*)
indexify`multiIndexOnSymbol[labelScripts___][variable_] :=
    Through[(indexify`singleIndexOnSymbol/@{labelScripts})@variable];

(*single index acting on expression*)
indexify`singleIndexOnExpression[labelScript_][expr_] :=
    Replace[expr,
        subexpr_Symbol?variableQ:>RuleCondition@indexify`singleIndexOnSymbol[labelScript][subexpr],
        All
    ];

(*multiple indices acting on expression*)
indexify`multiIndexOnExpression[labelScripts___][expr_] :=
    Through[(indexify`singleIndexOnExpression/@{labelScripts})@expr];

(*multiple indices wrapped by Symbol acting on expression*)
indexify`singleWrappedIndexOnExpr[fun_[labelScripts___]][expr_] :=
    indexify`headExceptList[fun]@@indexify`multiIndexOnExpression[labelScripts][expr];
indexify`multiWrappedIndexOnExpr[args:_[___]..,linker_Symbol][expr_] :=
    linker@@Map[indexify`singleWrappedIndexOnExpr[#][expr]&,{args}];

(*other helper functions*)
indexify`headExceptList[List] :=
    Total@*List;
indexify`headExceptList[fun_] :=
    fun;
indexify`linker[x_,y_] :=
    x-y;


(Options[#] = {"head"->False,"context"->Automatic})&/@{
    indexify,
    indexifyAll,
    indexify`singleIndexOnExpression`headAndContext,
    indexify`singleIndexOnExpression`withOptions,
    indexify`multiIndexOnExpression`withOptions,
    indexify`singleWrappedIndexOnExpression`withOptions,
    indexify`multiWrappedIndexOnExpression`withOptions
};

indexify`singleIndexOnExpression`headAndContext[labelScript_,opts:OptionsPattern[]][expr_] :=
    Replace[expr,
        subexpr_Symbol?variableQ:>RuleCondition[indexify`singleIndexOnSymbol[labelScript][subexpr]],
        All,
        Heads->OptionValue["head"]
    ];
indexify`singleIndexOnExpression`headAndContext[labelScript_,context_,opts:OptionsPattern[]][expr_] :=
    Replace[expr,
        subexpr_Symbol?(variableQ[#,context]&):>RuleCondition[indexify`singleIndexOnSymbol[labelScript][subexpr]],
        All,
        Heads->OptionValue["head"]
    ];

indexify`singleIndexOnExpression`withOptions[labelScript_,opts:OptionsPattern[]][expr_] :=
    Which[
        OptionValue["context"]===Automatic,
            indexify`singleIndexOnExpression`headAndContext[labelScript,opts][expr],
        contextDefineQ@OptionValue["context"]===True,
            indexify`singleIndexOnExpression`headAndContext[labelScript,OptionValue["context"],opts][expr],
        True,
            Message[contextDefineQ::reportundef,OptionValue["context"]];
            expr
    ];
    
indexify`multiIndexOnExpression`withOptions[labelScripts___,opts:OptionsPattern[]][expr_] :=
    Through[(indexify`singleIndexOnExpression`withOptions[#,opts]&/@{labelScripts})@expr];

indexify`singleWrappedIndexOnExpression`withOptions[fun_[labelScripts___],opts:OptionsPattern[]][expr_] :=
    indexify`headExceptList[fun]@@indexify`multiIndexOnExpression`withOptions[labelScripts,opts][expr];

indexify`multiWrappedIndexOnExpression`withOptions[args:_[___]..,linker_Symbol,opts:OptionsPattern[]][expr_] :=
    linker@@Map[indexify`singleWrappedIndexOnExpression`withOptions[#,opts][expr]&,{args}];


(* ::Subsubsection:: *)
(*indexSplit*)


indexSplit[string_String,splitter_:0] :=
    indexSplit`string[string,splitter];
indexSplit[symbol_Symbol,splitter_:0] :=
    If[ indexSplit`symbolSelector@symbol,
        indexSplit`symbol[symbol,splitter],
        symbol
    ];
(*to improve the performance by escaping specific contexts *)
indexSplit`symbolSelector[symbol_Symbol] :=
    Context@symbol=!="System`";
indexSplit`symbolSelector[_] = False;


indexSplit`string[string_String,splitter_] :=
    Module[ {list},
        list = Which[
            splitter===0,
                indexSplit`varAndLabelAndScript[string],
            splitter===1,
                indexSplit`varLabelAndScript[string],                
            splitter===2,
                indexSplit`varAndLabelScript[string]
        ];
        If[ list==={},
            string,
            list[[1,1]]
        ]
    ];
    
indexSplit`symbol[symbol_Symbol,splitter_] :=
    indexSplit`string[toString@symbol,splitter];

indexSplit`varAndLabelAndScript[string_String] :=
    StringReplaceList[
        string,
        StartOfString~~variable___~~label___~~script___~~EndOfString/;
            variableQ@variable&&labelQ@label&&scriptQ@script:>
                <|"variable"->variable,"label"->label,"script"->script|>
    ];
indexSplit`varLabelAndScript[string_String] :=
    StringReplaceList[
        string,
        StartOfString~~variableLabel___~~script___~~EndOfString/;
            variableLabelQ@variableLabel&&scriptQ@script:>
                <|"variableLabel"->variableLabel,"script"->script|>
    ];
indexSplit`varAndLabelScript[string_String] :=
    StringReplaceList[
        string,
        StartOfString~~variable___~~labelScript___~~EndOfString/;
            variableQ@variable&&labelScriptQ@labelScript:>
                <|"variable"->variable,"labelScript"->labelScript|>
    ];


(* ::Subsubsection:: *)
(*indexForm/indexFormBack*)


indexForm//Options = {"head"->True};
indexForm[symbol_Symbol] :=
    If[ indexSplit`symbolSelector@symbol&&Not@variableQ@symbol,
        indexForm`kernel[symbol],
        symbol
    ];
indexForm`symbolSelector =
    indexSplit`symbolSelector;

indexForm[expr_,opts:OptionsPattern[]] :=
    Replace[expr,
        symbol_Symbol?(indexSplit`symbolSelector[#]&&Not@variableQ[#]&):>indexForm`kernel@symbol,
        All,
        Heads->OptionValue["head"]
    ];


indexForm`kernel[symbol_Symbol] :=
    Module[ {assoc,siteList},
        (*split into var + label + script*)
        assoc = indexSplit`symbol[symbol,0];
        (*escape if no association returned*)
        If[ Head@assoc=!=Association,
            symbol//Throw
        ];
        (*transform the variable from string to Symbol*)
        assoc = MapAt[toSymbol,"variable"]@assoc;
        (*get the sites*)
        siteList = {
            instanceDefaultData["index","labelSite",toSymbol@assoc["label"]],
            instanceDefaultData["index","scriptSiteByVariable",assoc["variable"]]
        };
        (*format*)
        indexForm`subsuperscript[assoc,siteList]
    ]//Catch;
indexForm`subsuperscript[assoc_,siteList_] :=
    Which[
        siteList==={Superscript,Superscript},
            Superscript[assoc["variable"],Row[{assoc["label"],assoc["script"]},indexForm`separator]],
        siteList==={Subscript,Subscript},
            Subscript[assoc["variable"],Row[{assoc["label"],assoc["script"]},indexForm`separator]],
        siteList==={Superscript,Subscript},
            Subsuperscript[assoc["variable"],assoc["script"],assoc["label"]],
        siteList==={Subscript,Superscript},
            Subsuperscript[assoc["variable"],assoc["label"],assoc["script"]]
    ];
indexForm`separator = "";


indexFormBack[expr_,opts:OptionsPattern[]] :=
    expr/.{
        Subsuperscript[variable_?variableQ,label_?labelQ,script_?scriptQ]:>
            toSymbol[toString@variable<>toString@label<>toString@script],
        Subsuperscript[variable_?variableQ,script_?scriptQ,label_?labelQ]:>
            toSymbol[toString@variable<>toString@label<>toString@script],
        Superscript[variable_?variableQ,Row[{label_?labelQ,script_?scriptQ},_]]:>
            toSymbol[toString@variable<>toString@label<>toString@script],
        Subscript[variable_?variableQ,Row[{label_?labelQ,script_?scriptQ},_]]:>
            toSymbol[toString@variable<>toString@label<>toString@script]
    };


(* ::Subsubsection:: *)
(*indexArray/indexPolynomial*)


indexArray[dim_List,args___][symbol_] :=
    Array[indexArray`singleIndexOnSymbol[##][symbol]&,dim,args];
indexArray[labelScripts___][symbol_] :=
    Through[(indexArray`singleIndexOnSymbol/@{labelScripts})@symbol];

indexArray`singleIndexOnSymbol[labelScripts__][symbol_] :=
    toSymbol[
        toString@symbol<>
        StringJoin@@toString/@{labelScripts}
    ];


indexPolynomial[dim_List,args___][coefficient_,variables___] :=
    Dot[
        Flatten@indexArray[dim,args]@coefficient,
        Flatten@Array[Times@@Power[{variables},{##}]&,dim,args]
    ];
indexPolynomial[degrees___][coefficient_,variable_] :=
    Dot[
        indexArray[degrees][coefficient],
        Power[variable,{degrees}]
    ];


(* ::Section:: *)
(*Defining class*)


classDefine[
    "index",
    {"variable","label","variableString","variableLabel","labelString","variableLabelString","scriptSiteByVariable","labelSite"},
    {"setSorted","setSorted","setSorted","setSorted","setSorted","setSorted","assocUnsorted","assocUnsorted"},
    {{},{null},{},{},{},{},<|null->Subscript|>,<|null->Subscript|>},
    {{},{null},{},{},{},{},<|null->Subscript|>,<|null->Subscript|>}
];


(* ::Section:: *)
(*End*)


End[];

Protect@@Names[$Context<>"*"];

EndPackage[];
