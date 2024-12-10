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
#doc (Manual) "Custom Operators" =>
-/
#doc (Manual) "カスタム演算子（Custom Operators）" =>
%%%
tag := "operators"
%%%

:::comment
Lean supports custom infix, prefix, and postfix operators.
New operators can be added by any Lean library, and the new operators have equal status to those that are part of the language.
Each new operator is assigned an interpretation as a function, after which uses of the operator are translated into uses of the function.
The operator's translation into a function call is referred to as its {deftech}_expansion_.
If this function is a {tech}[type class] {tech}[method], then the resulting operator can be overloaded by defining instances of the class.

:::

Lean はカスタムの中置・前置・後置演算子をサポートしています。新しい演算子はどの Lean ライブラリでも追加することができ、新しい演算子は言語の一部である演算子と同等の地位を持ちます。新しい演算子にはそれぞれ関数としての解釈が割り当てられ、演算子の使用は関数の使用に変換されます。演算子の関数呼び出しへの変換は {deftech}_展開_ （expansion）と呼ばれます。この関数が {tech}[型クラス] の {tech}[メソッド] である場合、そのクラスのインスタンスを定義することで、結果の演算子をオーバーロードすることができます。

:::comment
All operators have a {deftech}_precedence_.
Operator precedence determines the order of operations for unparenthesized expressions: because multiplication has a higher precedence than addition, {lean}`2 + 3 * 4` is equivalent to {lean}`2 + (3 * 4)`, and {lean}`2 * 3 + 4` is equivalent to {lean}`(2 * 3) + 4`.
Infix operators additionally have an {deftech}_associativity_ that determines the meaning of a chain of operators that have the same precedence:

:::

すべての演算子は {deftech}_優先順位_ （precedence）を持ちます。演算子の優先順位は括弧を持たない式の演算順序を決定します：乗算は加算よりも優先順位が高いため、 {lean}`2 + 3 * 4` は {lean}`2 + (3 * 4)` と同値であり、 {lean}`2 * 3 + 4` は {lean}`(2 * 3) + 4` と同値です。中置演算子はさらに {deftech}_結合性_ （associativity）を持ち、同じ優先順位を持つ演算子の連鎖の意味を決定します：

:::comment
: {deftech}[Left-associative]

  These operators nest to the left.
  Addition is left- associative, so {lean}`2 + 3 + 4 + 5` is equivalent to {lean}`((2 + 3) + 4) + 5`.

:::

: {deftech}[左結合] （Left-associative）

  これらの演算子は左に入れ子になります。加算は左結合であるため、 {lean}`2 + 3 + 4 + 5` は {lean}`((2 + 3) + 4) + 5` と同値です。


:::comment
: {deftech}[Right-associative]

  These operators nest to the right.
  The product type is right-associative, so {lean}`Nat × String × Unit × Option Int` is equivalent to {lean}`Nat × (String × (Unit × Option Int))`.

:::

: {deftech}[右結合] （Right-associative）

  これらの演算子は右に入れ子になります。直積型は右結合であるため、 {lean}`Nat × String × Unit × Option Int` は {lean}`Nat × (String × (Unit × Option Int))` と同値です。

:::comment
: {deftech}[Non-associative]

  Chaining these operators is a syntax error.
  Explicit parenthesization is required.
  Equality is non-associative, so the following is an error:

:::

: {deftech}[非結合] （Non-associative）

  これらの演算子を連鎖させると構文エラーになります。明示的な括弧が必要です。等式は非結合であるため、以下はエラーになります：

  ```syntaxError eqs (category := term)
  1 + 2 = 3 = 2 + 1
  ```
  The parser error is:
  ```leanOutput eqs
  <example>:1:10: expected end of input
  ```
:::::keepEnv
:::comment
::example "Precedence for Prefix and Infix Operators"
:::
::::example "前置・中置演算子の優先順位"
```lean (show := false)
axiom A : Prop
axiom B : Prop
example : (¬A ∧ B = (¬A) ∧ B) = (¬A ∧ ((B = ¬A) ∧ B)) := rfl
example : (¬A ∧ B) = ((¬A) ∧ B) := rfl
```

:::comment
The proposition {lean}`¬A ∧ B` is equivalent to {lean}`(¬A) ∧ B`, because `¬` has a higher precedence than `∧`.
Because `∧` has higher precedence than `=` and is right-associative, {lean}`¬A ∧ B = (¬A) ∧ B` is equivalent to {lean}`¬A ∧ ((B = ¬A) ∧ B)`.
:::

命題 {lean}`¬A ∧ B` は `¬` が `∧` よりも優先順位が高いため {lean}`(¬A) ∧ B` と同値です。`∧` は `=` よりも優先順位が高く、また右結合であるため、 {lean}`¬A ∧ B = (¬A) ∧ B` は {lean}`¬A ∧ ((B = ¬A) ∧ B)` と同値です。

::::
:::::

:::comment
Lean provides commands for defining new operators:
:::

Lean は新しい演算子を定義するためのコマンドを提供しています：

::::syntax command
:::comment
Non-associative infix operators are defined using {keywordOf Lean.Parser.Command.mixfix}`infix`:
:::

非結合中置演算子は {keywordOf Lean.Parser.Command.mixfix}`infix` で定義されます：

```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind infix:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

:::comment
Left-associative infix operators are defined using {keywordOf Lean.Parser.Command.mixfix}`infixl`:
:::

左結合中置演算子は {keywordOf Lean.Parser.Command.mixfix}`infixl` で定義されます：

```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind infixl:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

:::comment
Right-associative infix operators are defined using {keywordOf Lean.Parser.Command.mixfix}`infixr`:
:::

右結合中置演算子は {keywordOf Lean.Parser.Command.mixfix}`infixr` で定義されます：

```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind infixr:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

:::comment
Prefix operators are defined using {keywordOf Lean.Parser.Command.mixfix}`prefix`:
:::

前置演算子は {keywordOf Lean.Parser.Command.mixfix}`prefix` で定義されます：

```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind prefix:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

:::comment
Postfix operators are defined using {keywordOf Lean.Parser.Command.mixfix}`postfix`:
:::

後置演算子は {keywordOf Lean.Parser.Command.mixfix}`postfix` で定義されます：

```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind postfix:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```
::::

:::comment
Each of these commands may be preceded by {tech}[documentation comments] and {tech}[attributes].
The documentation comment is shown when the user hovers their mouse over the operator, and attributes may invoke arbitrary metaprograms, just as for any other declaration.
The attribute {attr}`inherit_doc` causes the documentation of the function that implements the operator to be re-used for the operator itself.

:::

これらのコマンドの前には {tech}[documentation comments] と {tech}[attributes] を付けることができます。ドキュメントコメントはユーザが演算子の上にマウスを置くと表示され、属性は他の宣言と同様に任意のメタプログラムを呼び出すことができます。 {attr}`inherit_doc` 属性は演算子を実装する関数のドキュメントを演算子自身に再利用させます。

:::comment
Operators interact with {tech}[section scopes] in the same manner as attributes.
By default, operators are available in any module that transitively imports the one in which they are established, but they may be declared `scoped` or `local` to restrict their availability either to contexts in which the current namespace has been opened or to the current {tech}[section scope], respectively.

:::

演算子は属性と同じように、 {tech}[section scopes] と相互作用します。デフォルトでは、記法はそれが確立されたモジュールをインポートした任意のモジュールで遷移的に利用可能です。しかし、`scoped` または `local` と宣言することで、それぞれ現在の名前空間が開かれているコンテキストか、現在の {tech}[section scope] に限定することができます。

:::comment
Custom operators require a {ref "precedence"}[precedence] specifier, following a colon.
There is no default precedence to fall back to for custom operators.

:::

カスタム演算子には、コロンに続く {ref "precedence"}[優先順位] 指定子が必要です。カスタム演算子にはデフォルトの優先順位はありません。

:::comment
Operators may be explicitly named.
This name denotes the extension to Lean's syntax, and is primarily used for metaprogramming.
If no name is explicitly provided, then Lean generates one based on the operator.
The specifics of the assignment of this name should not be relied upon, both because the internal name assignment algorithm may change and because the introduction of similar operators in upstream dependencies may lead to a clash, in which case Lean will modify the assigned name until it is unique.

:::

演算子には明示的に名前を付けることができます。この名前は Lean の構文の拡張を表し、主にメタプログラミングに使用されます。名前が明示的に与えられない場合、Lean は演算子に基づいて名前を生成します。この名前の割り当ての特定に頼るべきではありません。なぜなら内部的な名前の割り当てアルゴリズムは変更される可能性があり、また上流の依存関係で似たような演算子が導入されると衝突する可能性があるからです。このような場合、Lean は名前が一意になるまで名前の割り当てを変更します。

:::::keepEnv
:::comment
::example "Assigned Operator Names"
:::
::::example "演算子の名前の割り当て"
:::comment
Given this infix operator:
:::

この中置演算子に対して：

```lean
infix:90 " ⤴ " => Option.getD
```
:::comment
the internal name {name}`«term_⤴_»` is assigned to the resulting parser extension.
:::

内部的な名前 {name}`«term_⤴_»` が結果のパーサ拡張に割り当てられます。

::::
:::::

:::::keepEnv
:::comment
::example "Provided Operator Names"
:::
::::example "演算子名の提供"
:::comment
Given this infix operator:
:::

この中置演算子に対して：

```lean
infix:90 (name := getDOp) " ⤴ " => Option.getD
```
:::comment
the resulting parser extension is named {name}`getDOp`.
:::

結果のパーサ拡張は {name}`getDOp` と命名されます。

::::
:::::

:::::keepEnv
:::comment
::example "Inheriting Documentation"
:::
::::example "ドキュメントの継承"
:::comment
Given this infix operator:
:::

この中置演算子に対して：

```lean
@[inherit_doc]
infix:90 " ⤴ " => Option.getD
```
:::comment
the resulting parser extension has the same documentation as {name}`Option.getD`.
:::

結果のパーサ拡張は {name}`Option.getD` と同じドキュメントを持ちます。

::::
:::::



:::comment
When multiple operators are defined that share the same syntax, Lean's parser attempts all of them.
If more than one succeed, the one that used the most input is selected—this is called the {deftech}_local longest-match rule_.
In some cases, parsing multiple operators may succeed, all of them covering the same range of the input.
In these cases, the operator's {tech}[priority] is used to select the appropriate result.
Finally, if multiple operators with the same priority tie for the longest match, the parser saves all of the results, and the elaborator attempts each in turn, failing if elaboration does not succeed on exactly one of them.

:::

同じ構文を持つ演算子が複数定義されている場合、Lean のパーサはそのすべてを試行します。複数の演算子が成功した場合、最も多くの入力を使用したものが選択されます。これは {deftech}_ローカル最長一致規則_ （local longest-match rule）と呼ばれます。場合によっては、複数の演算子のパースが成功し、すべての演算子が同じ入力範囲をカバーすることがあります。この場合、演算子の {tech}[優先度] を使用して適切な結果が選択されます。最後に、同じ優先度を持つ複数の演算子が最長一致で並んだ場合、パーサはすべての結果を保存し、エラボレータは順番にそれぞれを試行し、そのうちの正確に1つのみがエラボレーションに成功しなかった場合失敗します。

::::::keepEnv

:::comment
::example "Ambiguous Operators and Priorities"
:::
:::::example "あいまいな演算子と優先度"

::::keepEnv
:::comment
Defining an alternative implementation of `+` as {lean}`Or` requires only an infix operator declaration.
:::

{lean}`Or` としての `+` の代替実装を定義するには中置演算子宣言だけが必要です。

```lean
infix:65  " + " => Or
```

:::comment
With this declaration, Lean attempts to elaborate addition both using the built-in syntax for {name}`HAdd.hAdd` and the new syntax for {lean}`Or`:
:::

この宣言によって、Lean は {name}`HAdd.hAdd` の組み込み構文と {lean}`Or` の新しい構文の両方を使用して加算をエラボレートしようと試みます：

```lean (name := trueOrFalse1)
#check True + False
```
```leanOutput trueOrFalse1
True + False : Prop
```
```lean (name := twoPlusTwo1)
#check 2 + 2
```
```leanOutput twoPlusTwo1
2 + 2 : Nat
```

:::comment
However, because the new operator is not associative, the {tech}[local longest-match rule] means that only {name}`HAdd.hAdd` applies to an unparenthesized three-argument version:
:::

しかし、新しい演算子は結合的ではないため、 {tech}[ローカル最長一致規則] から {name}`HAdd.hAdd` だけが括弧を用いない3引数バージョンに適用されることが導かれます：

```lean (error := true) (name := trueOrFalseOrTrue1)
#check True + False + True
```
```leanOutput trueOrFalseOrTrue1
failed to synthesize
  HAdd Prop Prop ?m.38
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

::::

::::keepEnv
:::comment
If the infix operator is declared with high priority, then Lean does not try the built-in {name}`HAdd.hAdd` operator in ambiguous cases:
:::

中置演算子が高い優先度で宣言された時、Lean はあいまいなケースで組み込みの {name}`HAdd.hAdd` 演算子を試行しません：

```lean
infix:65 (priority := high)  " + " => Or
```

```lean (name := trueOrFalse2)
#check True + False
```
```leanOutput trueOrFalse2
True + False : Prop
```
```lean (name := twoPlusTwo2) (error := true)
#check 2 + 2
```
```leanOutput twoPlusTwo2
failed to synthesize
  OfNat Prop 2
numerals are polymorphic in Lean, but the numeral `2` cannot be used in a context where the expected type is
  Prop
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

:::comment
The new operator is not associative, so the {tech}[local longest-match rule] means that only {name}`HAdd.hAdd` applies to the three-argument version:
:::

新しい演算子は結合的ではないため、 {tech}[ローカル最長一致規則] から {name}`HAdd.hAdd` だけが括弧を用いない3引数バージョンに適用されることが導かれます：

```lean (error := true) (name := trueOrFalseOrTrue2)
#check True + False + True
```
```leanOutput trueOrFalseOrTrue2
failed to synthesize
  HAdd Prop Prop ?m.20
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
::::

:::::
::::::


:::comment
The actual operator is provided as a string literal.
The new operator must satisfy the following requirements:
 * It must contain at least one character.
 * The first character may not be a single or double quote (`'` or `"`), unless the operator is `''`.
 * It may not begin with a backtick (`` ` ``) followed by a character that would be a valid prefix of a quoted name.
 * It may not begin with a digit.
 * It may not include internal whitespace.

:::

実際の演算子は文字列リテラルによって指定されます。新しい演算子は以下の要件を満たす必要があります：
 * 最低1文字を含む
 * 演算子が `''` でない限り、最初の文字はシングル・ダブルクォート（`'` または `"`）であってはなりません。
 * バックティック（``​`​``）で始まり、その後に quote された名前として有効な接頭辞である文字を続けてはなりません。
 * 数値から始まってはいけません。
 * 内部に空白を含んではいけません。

:::comment
The operator string literal may begin or end with a space.
These are not part of the operator's syntax, and their presence does not require spaces around uses of the operator.
However, the presence of spaces cause Lean to insert spaces when showing the operator to the user.
Omitting them causes the operator's arguments to be displayed immediately next to the operator itself.


:::

演算子の文字列リテラルはスペースで開始・終了することがあります。これらは演算子の一部ではないため、スペースがあっても演算子の使用時にスペースを入れる必要はありません。しかし、スペースがあると、Lean は演算子をユーザに表示する際にスペースを挿入します。スペースを省略すると、演算子の引数が演算子のすぐ隣に表示されます。

:::keepEnv
```lean (show := false)
-- Test claim about internal whitespace in preceding paragraph
/--
error: invalid atom
---
error: invalid syntax node kind '«term_<<<<_>>>>_»'
-/
#guard_msgs in
infix:99 " <<<< >>>> " => Nat.add


--- Test further claims about allowed atoms
/--
error: invalid atom
---
error: invalid syntax node kind 'bogus'
-/
#guard_msgs in
infix:9 (name := bogus) "" => Nat.mul


/--
error: invalid atom
---
error: invalid syntax node kind 'alsobogus'
-/
#guard_msgs in
infix:9 (name := alsobogus) " ` " => Nat.mul

-- this one's OK
#guard_msgs in
infix:9 (name := nonbogus) " `` " => Nat.mul

/--
error: invalid atom
---
error: invalid syntax node kind 'bogus'
-/
#guard_msgs in
infix:9 (name := bogus) "`a" => Nat.mul

```
:::

:::comment
Finally, the operator's meaning is provided, separated from the operator by {keywordOf Lean.Parser.Command.mixfix}`=>`.
This may be any Lean term.
Uses of the operator are desugared into function applications, with the provided term in the function position.
Prefix and postfix operators apply the term to their single argument as an explicit argument.
Infix operators apply the term to the left and right arguments, in that order.
Other than its ability to accept arguments at each call site, there are no specific requirements imposed on the term.
Operators may construct functions, so the term may expect more parameters than the operator.
Implicit and {tech}[instance-implicit] parameters are resolved at each application site, which allows the operator to be defined by a {tech}[type class] {tech}[method].

:::

最後に、演算子の意味を {keywordOf Lean.Parser.Command.mixfix}`=>` で区切って指定します。これは Lean のどんな項でも構いません。演算子の使用は提供された項が関数の位置にある関数適用に脱糖されます。前置・後置演算子は明示的な引数として、その項を単一の引数に適用します。中置演算子は引数を左右の順に項を適用します。各呼び出し位置で引数を受け付けること以外に項に課される特別な要件はありません。演算子は関数を構築することができるため、項は演算子よりも多くのパラメータを期待することができます。暗黙と {tech}[インスタンス暗黙] のパラメータは各適用位置で解決されるため、演算子は {tech}[型クラス] の {tech}[メソッド] で定義することができます。

```lean (show := false) (keep := false)
-- Double-check claims about operators above
prefix:max "blah" => Nat.add
#check (blah 5)
```

:::comment
If the term consists either of a name from the global environment or of an application of such a name to one or more arguments, then Lean automatically generates an {tech}[unexpander] for the operator.
This means that the operator will be displayed in {tech}[proof states], error messages, and other output from Lean when the function term otherwise would have been displayed.
Lean does not track whether the operator was used in the original term; it is inserted at every opportunity.

:::

項がグローバル環境からの名前か、そのような名前を1つ以上の引数に適用したものである場合、Lean は自動的に演算子に {tech}[unexpander] を生成します。これは {tech}[証明状態] ・エラーメッセージ・その他の Lean からの出力にて、マッチする関数適用項が表示される場合に表示されます。Lean はもとの項がその演算子で使われていたかどうかを追跡しません；これは Lean の出力にていたるところで用いられます。

:::::keepEnv
:::comment
::example "Custom Operators in Lean's Output"
:::
::::example "Lean の出力におけるカスタム演算子"
:::comment
The function {lean}`perhapsFactorial` computes a factorial for a number if it's not too large.
:::

関数 {lean}`perhapsFactorial` はあまり大きくない数値に対して階乗を計算します。

```lean
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n + 1) * fact n

def perhapsFactorial (n : Nat) : Option Nat :=
  if n < 8 then some (fact n) else none
```

:::comment
The postfix interrobang operator can be used to represent it.
:::

後置するインテロバング演算子を使って表現することができます。

```lean
postfix:90 "‽" => perhapsFactorial
```

:::comment
When attempting to prove that {lean}`∀ n, n ≥ 8 → (perhapsFactorial n).isNone`, the initial proof state uses the new operator, even though the theorem as written does not:
:::

 {lean}`∀ n, n ≥ 8 → (perhapsFactorial n).isNone` を証明しようとすると、たとえそのように書かなかったとしても最初の証明状態では新しい演算子が使われます：

```proofState
∀ n, n ≥ 8 → (perhapsFactorial n).isNone := by skip
/--
⊢ ∀ (n : Nat), n ≥ 8 → n‽.isNone = true
-/

```
::::
:::::
