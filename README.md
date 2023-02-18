# Package ``lily`index` ``

A Mathematica package for coding/decoding a variable indexed by label and script into/from a single symbol.

The documentation can also be found on [my website](https://yuriever.github.io/symbolic/package-lily-index/).

* Dependency: 
    
    * ``lily`class` ``

* Object:

    * class: `"index"`

    * instance: `"context"`

    * primitive member: `"variable", "label", "scriptSiteByVariable", "labelSite"`

    * derived member: `"variableLabel", "variableString", "labelString", "variableLabelString"`

## Designing ideas

### Member

The package ``lily`index` `` provides the functionality of coding/decoding a variable indexed by label and script into/from a single symbol. For example, `"x"<>"dagger"<>"0"` will be coded as `xdagger0` and formatted as $x^{\dagger}_{0}$. 

``` wl
_Subsuperscript <=> "variable"<>"label"<>"script" <=> _Symbol
```

In order to tokenize the symbol `xdagger0` as `"x"<>"dagger"<>"0"` we need to pre-store the variable $x$ and the label $\dagger$ in the members `"variable"` and `"label"`. 
Allowed script types include single letters or natural numbers. 
The position of label $\dagger$ is stored in the member `"labelSite"`. The position of script $0$ is determined by the associated variable $x$ and is stored in the member `"scriptSiteByVariable"`. 

Also for efficiency, the combinations of `"variable"` and `"label"` are cached in the member `"variableLabel"`, while the string versions are cached in members `"*String"`. These four members will be automatically updated when `"variable"` and `"label"` get changed.

### Instance

The instances `"context"` are to distinguish different sets of variables and labels. Then all the `"context"` constitute an `"index"`.

### Non-invertibility of `ToExpression` and `ToString`

The kernel functions will first convert symbols to strings, use string pattern matching to perform evaluation, and finally convert back to symbols if necessary. The system function pair `ToExpression, ToString` is non-invertible at `Null`. To override this, we introduce the public symbol `null` representing empty string and the function pair `toSymbol, toString`. 

Every context and the default context contains the symbol `null` by default.

## Methods

* `contextDefine[contextList_|context_,scriptSite_,labelSite_]` - define and initiate contexts. The arguments `scriptSite_` and `labelSite_` determine the default sites of scripts and labels and serve as class attributes for the instance `"context"`. They accept inputs `Subscript|Superscript` with default values `Subscript` and `Superscript` respectively.

* `contextDefineQ[context_]` - check whether a context is defined.

* `contextDefault[contextList_|context_]` - set default contexts.

* `contextReset|contextUnset[contextList_|context_]` - reset/unset the contexts.

* `contextAdd|contextDelete[contextList_|context_,variableList_,labelList_]` - add/delete variables and labels to/from the contexts. The positions can be specified e.g. `x->Superscript`, otherwise the default positions will be used.

* `contextShow[context_]` - show the context.

<h3 class="nocount">Some shortcuts</h3>

* `contextDefine[]` - return the list of defined contexts.

* `contextDefault[]` - return the list of default contexts.

* `contextReset|contextUnset[]` - reset/unset the default contexts.

* `contextReset|contextUnset[All]` - reset/unset all the defined contexts.

* `contextShow[]` - show the default contexts.

## Functionality

### Questing functions

* `variableQ[_Symbol|_String]` - variable/variableString.

* `labelQ[_Symbol|_String]` - Symbol/String: label/labelString.

* `variableLabelQ[_Symbol|_String]` - Symbol/String: variableLabel/variableLabelString.

* `scriptQ[_Integer|_Symbol|_String]` - null/"", natural number or single letter.

* `labelScriptQ[_Integer|_Symbol|_String]` - label + script.

* `variableLabelScriptQ[_Symbol|_String]` - variable + label + script.

* `variableMatchQ[_Symbol|_String,variable_]` - symbol starting from variable.

* `labelMatchQ[_Symbol|_String,label_]` - symbol containing label.

* `variableLabelMatchQ[_,_]`

    * `variableLabelMatchQ[_Symbol|_String,variableLabel_]` - symbol starting from variableLabel.

    * `variableLabelMatchQ[_Symbol|_String,variable_,label_]` - symbol starting from variable + label.

### Kernel functions

The usages of kernel functions are as follows.

``` wl
(*define and set default the context*)
contextDefine["ctx"]
contextAdd["ctx"][{x,y,f->Superscript},{star}]
contextDefault["ctx"]
```

* `toString|toSymbol[_]` - invertible version of `ToString` and `ToExpression`.

* `indexify|indexifyAll[_[___]..,linker_][expr_]` - indexify the variables in an expression by checking the labels and scripts. `indexify` will check the inputs by `labelScriptQ`, while `indexifyAll` accepts all inputs and hence is faster. The default value of `linker_` is `Subtract`.

    ``` wl
    indexify[star0][x^2]
    indexify[{1,2,3},{0}][x y]
    indexify[g[a,b],g[c,d],h][x^2]
    ```

    ``` wl
    Out[]= xstar0^2
    Out[]= -x0 y0+x1 y1+x2 y2+x3 y3
    Out[]= h[g[xa^2,xb^2],g[xc^2,xd^2]]
    ```

    Default options: 

    * `"head"->False` - the variables as heads will not be indexified. This option is originated from the option `"Heads"` of `Replace`.

    * `"context"->Automatic` - the variables and labels are checked against the default context. This option can be specified to be any other defined context.

* `indexSplit[_String|_Symbol,splitter_:0]` - split the input into strings of the form: variable + label + script. The splitter accepts `0, 1, 2`, whose meanings are explained by the following examples.

    ``` wl
    indexSplit[xstar0,0]
    indexSplit[xstar0,1]
    indexSplit[xstar0,2]
    indexSplit[x,0]//Map[toSymbol]
    ```

    ``` wl
    Out[]= <|"variable"->"x","label"->"star","script"->"0"|>
    Out[]= <|"variableLabel"->"xstar","script"->"0"|>
    Out[]= <|"variable"->"x","labelScript"->"star0"|>
    Out[]= <|"variable"->x,"label"->null,"script"->null|>
    ```

* `indexForm[expr_]` - format indexed variables in the the expression with Subsuperscript. 

    ``` wl
    indexify[{1,2,3},{0},"head"->True][f[x y]]//indexForm
    ```

    \begin{equation}
    -f_{\text{}}^0\left(x_{\text{}0} y_{\text{}0}\right)+f_{\text{}}^1\left(x_{\text{}1} y_{\text{}1}\right)+f_{\text{}}^2\left(x_{\text{}2} y_{\text{}2}\right)+f_{\text{}}^3\left(x_{\text{}3} y_{\text{}3}\right)
    \end{equation}

    Default options: 

    * `"head"->True` - the variables as heads will be transformed to Subsuperscript. This option is originated from the option `"Heads"` of `Replace`.

* `indexFormBack[expr_]` - collape the Subsuperscript in the expression back to indexed variable, e.g.

    ``` wl
    indexify[{1,2,3},{0},"head"->True][f[x y]]//indexForm//indexFormBack
    ```

    ``` wl
    Out[]= -f0[x0 y0]+f1[x1 y1]+f2[x2 y2]+f3[x3 y3]
    ```

## To-do list and other issues

