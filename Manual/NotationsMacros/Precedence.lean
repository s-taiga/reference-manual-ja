/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

/-
#doc (Manual) "Precedence" =>
-/
#doc (Manual) "優先順位（Precedence）" =>
%%%
tag := "precedence"
%%%

:::comment
Infix operators, notations, and other syntactic extensions to Lean make use of explicit {tech}[precedence] annotations.
While precedences in Lean can technically be any natural number, by convention they range from {evalPrec}`min` to {evalPrec}`max`, respectively denoted `min` and `max`.{TODO}[Fix the keywordOf operator and use it here]
Function application has the highest precedence.

:::

Lean における中置演算子・記法・その他の構文拡張では明示的な {tech}[優先順位] の注釈を使用します。Lean の優先順位は、技術的には任意の自然数にすることができますが、慣例的には {evalPrec}`min` から {evalPrec}`max` の範囲を用い、それぞれ `min` と `max` と表記します。関数適用が最も高い優先順位を持ちます。

::::syntax prec (open := false)
:::comment
Most operator precedences consist of explicit numbers.
The named precedence levels denote the outer edges of the range, close to the minimum or maximum, and are typically used by more involved syntax extensions.
:::

ほとんどの演算子の優先順位は明示的な数値で構成されています。名前付きの優先順位レベルは、最小・最大で閉じられた範囲の外側の端を示し、通常、より複雑な構文拡張で使用されます。

```grammar
$n:num
```

:::comment
Precedences may also be denoted as sums or differences of precedences; these are typically used to assign precedences that are relative to one of the named precedences.
:::

優先順位は、優先順位の和や差で示されることもあります；これらは通常、指定された優先順位の1つに対して相対的な優先順位を割り当てるために使用されます。

```grammar
$p + $p
```
```grammar
$p - $p
```
```grammar
($p)
```

:::comment
The maximum precedence is used to parse terms that occur in a function position.
Operators should typically not use use this level, because it can interfere with users' expectation that function application binds more tightly than any other operator, but it is useful in more involved syntax extensions to indicate how other constructs interact with function application.
:::

最大の優先順位は関数の位置で発生する項をパースするために使用されます。演算子では基本的にこのレベルを使用すべきではありません。なぜなら、関数の適用が他のどの演算子よりも強く束縛されるだろうというユーザの期待を妨げる可能性があるからです。しかし、他の構成が関数適用とどのように相互作用するかを示すより発展した構文拡張では有用です。

```grammar
max
```

:::comment
Argument precedence is one less than the maximum precedence.
This level is useful for defining syntax that should be treated as an argument to a function, such as {keywordOf Lean.Parser.Term.fun}`fun` or {keywordOf Lean.Parser.Term.do}`do`.
:::

引数優先順位は最大優先順位より1つ小さい値です。このレベルは {keywordOf Lean.Parser.Term.fun}`fun` や {keywordOf Lean.Parser.Term.do}`do` などのように、関数の引数として扱われる構文を定義するのに便利です。

```grammar
arg
```

:::comment
Lead precedence is less that argument precedence, and should be used for custom syntax that should not occur as a function argument, such as {keywordOf Lean.Parser.Term.let}`let`.
:::

リードの優先順位は引数の優先順位より低く、 {keywordOf Lean.Parser.Term.let}`let` のような関数の引数として使用すべきではないカスタム構文に使用されます。

```grammar
lead
```

:::comment
The minimum precedence can be used to ensure that an operator binds less tightly than all other operators.
:::

最小の優先順位はある演算子が他のすべての演算子よりも小さく結合することを保証するために使用できます。

```grammar
min
```
::::
