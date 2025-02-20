/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen, Joachim Breitner
-/

import VersoManual
import Manual.RecursiveDefs.Structural.RecursorExample
import Manual.RecursiveDefs.Structural.CourseOfValuesExample

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

/-
#doc (Manual) "Structural Recursion" =>
-/
#doc (Manual) "構造的再帰（Structural Recursion）" =>
%%%
tag := "structural-recursion"
%%%

:::comment
Structurally recursive functions are those in which each recursive call is on a structurally smaller term than the argument.
The same parameter must decrease in all recursive calls; this parameter is called the {deftech}_decreasing parameter_.
Structural recursion is stronger than the primitive recursion that recursors provide, because the recursive call can use more deeply nested sub-terms of the argument, rather than only an immediate sub-term.
The constructions used to implement structural recursion are, however, implemented using the recursor; these helper constructions are described in the {ref "recursor-elaboration-helpers"}[section on inductive types].

:::

構造的再帰関数とは、各再帰呼び出しが引数よりも構造的に小さい項に対して行われる関数のことです。同じパラメータはすべての再帰呼び出しで減少しなければなりません；このパラメータは {deftech}_減少パラメータ_ （decreasing parameter）と呼ばれます。構造的再帰は、再帰子が提供する原始再帰よりも強力です。なぜなら、再帰呼び出しが引数の直前の部分項だけでなく、任意の部分項を使用できるからです。しかし、構造的再帰を実装するために使用される構成は再帰子を使用して実装されます；これらの補助構成は {ref "recursor-elaboration-helpers"}[帰納型の節] で説明されています。

:::comment
The rules that govern structural recursion are fundamentally _syntactic_ in nature.
There are many recursive definitions that exhibit structurally recursive computational behavior, but which are not accepted by these rules; this is a fundamental consequence of the analysis being fully automatic.
{tech}[Well-founded recursion] provides a semantic approach to demonstrating termination that can be used in situations where a recursive function is not structurally recursive, but it can also be used when a function that computes according to structural recursion doesn't satisfy the syntactic requirements.

:::

構造的再帰を支配する規則は性質からして _構文的_ なものです。再帰的定義の中には構造的再帰である計算動作を示すものの、これらの規則では受け入れられないものが数多く存在します；これは解析が完全に自動化されていることの基本的な結果です。 {tech}[整礎再帰] は再帰関数が構造的再帰ではない状況でも停止性を示すために使用できる意味論的アプローチを提供しますが、構造的再帰に従って計算される関数が構文的要件を満たさない場合にも使用できます。

```lean (show := false)
section
variable (n n' : Nat)
```
:::comment
::example "Structural Recursion vs Subtraction"
:::
::::example "構造的再帰と引き算"
:::comment
The function {lean}`countdown` is structurally recursive.
The parameter {lean}`n` was matched against the pattern {lean}`n' + 1`, which means that {lean}`n'` is a direct subterm of {lean}`n` in the second branch of the pattern match:
:::

以下の関数 {lean}`countdown` は構造的再帰です。パターンマッチで2番目の分岐において、パラメータ {lean}`n` はパターン {lean}`n' + 1` に対してマッチしますが、これは {lean}`n'` が {lean}`n` の直接の部分項であることを意味します：

```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown n'
```

:::comment
Replacing pattern matching with an equivalent Boolean test and subtraction results in an error:
:::

パターンマッチを同等な真偽値のテストと引き算に置き換えるとエラーになります：

```lean (error := true) (name := countdown') (keep := false)
def countdown' (n : Nat) : List Nat :=
  if n == 0 then []
  else
    let n' := n - 1
    n' :: countdown' n'
```
```leanOutput countdown'
fail to show termination for
  countdown'
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    countdown' n'


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : Nat
h✝ : ¬(n == 0) = true
n' : Nat := n - 1
⊢ n - 1 < n
```
:::comment
This is because there was no pattern matching on the parameter {lean}`n`.
While this function indeed terminates, the argument that it does so is based on properties of if, the equality test, and subtraction, rather than being a generic feature of {lean}`Nat` being an {tech}[inductive type].
These arguments are expressed using {tech}[well-founded recursion], and a slight change to the function definition allows Lean's automatic support for well-founded recursion to construct an alternative termination proof.
This version branches on the decidability of propositional equality for {lean}`Nat` rather than the result of a Boolean equality test:

:::

これはパラメータ {lean}`n` に対するパターンマッチが無いためです。この関数は確実に停止しますが、それをもたらす引数の性質として {lean}`Nat` が {tech}[帰納型] であるという一般的な特徴ではなく、if・等号のテスト・引き算などの特徴に基づいています。これらの引数は {tech}[整礎再帰] を使って表現され、関数の定義に少し変更を加えることで、Lean の整礎再帰の自動サポートが代替的な終了証明を構築できるようになります。このバージョンは、真偽値の等号テストではなく、 {lean}`Nat` についての propositional equality の決定可能性に対して分岐します：

```lean
def countdown' (n : Nat) : List Nat :=
  if n = 0 then []
  else
    let n' := n - 1
    n' :: countdown' n'
```

:::comment
Here, Lean's automation automatically constructs a termination proof from facts about propositional equality and subtraction.
It uses well-founded recursion rather than structure recursion behind the scenes.
:::

ここでは、Lean の自動化は propositional equality と引き算に関する事実から停止性の証明を自動的に構築します。その裏では、構造的再帰ではなく整礎再帰を使っています。

::::
```lean (show := false)
end
```

:::comment
Structural recursion may be used explicitly or automatically.
With explicit structural recursion, the function definition declares which parameter is the {tech}[decreasing parameter].
If no termination strategy is explicitly declared, Lean performs a search for a decreasing parameter as well as a decreasing measure for use with {tech}[well-founded recursion].
Explicitly annotating structural recursion has the following benefits:
 * It can speed up elaboration, because no search occurs.
 * It documents the termination argument for readers.
 * In situations where structural recursion is explicitly desired, it prevents the accidental use of well-founded recursion.

:::

構造的再帰は明示的にも自動的にも使用することができます。明示的な構造的再帰では、関数定義で {tech}[減少パラメータ] がどのパラメータであるかを宣言します。停止に関する戦略が明示的に宣言されていない場合、Lean は {tech}[整礎再帰] で使用する減少する測度と同様に、減少パラメータの検索を実行します。構造的再帰を明示的に注釈すると、次のような利点があります：
 * 検索が発生しないため、エラボレーションの速度が上がります。
 * コードを読む人のために停止引数が文書化されます。
 * 構造的再帰が明示的に望まれている状況では、整礎再帰が誤って使用されることを防ぐことができます。

:::comment
# Explicit Structural Recursion
:::

# 明示的な構造的再帰（Explicit Structural Recursion）

:::comment
To explicitly use structural recursion, a function or theorem definition can be annotated with a {keywordOf Lean.Parser.Command.declaration}`termination_by structural` clause that specifies the {tech}[decreasing parameter].
The decreasing parameter may be a reference to a parameter named in the signature.
When the signature specifies a function type, the decreasing parameter may additionally be a parameter not named in the signature; in this case, names for the remaining parameters may be introduced by writing them before an arrow ({keywordOf Lean.Parser.Command.declaration}`=>`).

:::

構造的再帰を明示的に使用するには、関数または定理の定義に {tech}[減少パラメータ] を指定した {keywordOf Lean.Parser.Command.declaration}`termination_by structural` 句を注釈します。減少パラメータはシグネチャで指定されたパラメータを参照することができます。シグネチャが関数型となっている場合、減少パラメータはシグネチャ内の名前のないパラメータとなる場合があります；この場合、残りのパラメータの名前を矢印（ {keywordOf Lean.Parser.Command.declaration}`=>` ）の前に書いて導入することができます。

:::comment
::example "Specifying Decreasing Parameters"
:::
::::example "減少パラメータの指定"

:::comment
When the decreasing parameter is a named parameter to the function, it can be specified by referring to its name.

:::

減少パラメータが関数の名前付きパラメータである場合、その名前を参照して指定することができます。

```lean (keep := false)
def half (n : Nat) : Nat :=
  match n with
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by structural n
```

:::comment
When the decreasing parameter is not named in the signature, a name can be introduced locally in the {keywordOf Lean.Parser.Command.declaration}`termination_by` clause.

:::

減少パラメータの名前がシグネチャに無い場合、 {keywordOf Lean.Parser.Command.declaration}`termination_by` 句でローカルに名前を導入することができます。

```lean (keep := false)
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by structural n => n
```
::::

::::syntax Lean.Parser.Termination.terminationBy (title := "Explicit Structural Recursion")

:::comment
The `termination_by structural` clause introduces a decreasing parameter.

:::

`termination_by structural` 句は減少パラメータを導入します。

```grammar
termination_by structural $[$_:ident* =>]? $term
```

:::comment
The identifiers before the optional `=>` can bring function parameters into scope that are not
already bound in the declaration header, and the mandatory term must indicate one of the function's parameters, whether introduced in the header or locally in the clause.
:::


オプショナルな `=>` の前の識別子は、その関数の宣言ヘッダでまだ束縛されていない関数パラメータをスコープに入れることができ、必須の項はヘッダやローカルで導入された関数のパラメータのうち1つを指定しなければなりません。
::::

:::comment
The decreasing parameter must satisfy the following conditions:

:::

減少パラメータは以下の条件を満たさなければなりません：

:::comment
* Its type must be an {tech}[inductive type].

:::

* 型が {tech}[帰納型] でなければなりません。

:::comment
* If its type is an {tech}[indexed family], then all indices must be parameters of the function.

:::

* 型が {tech}[添字付けられた型の族] である場合、すべての添字は関数のパラメータでなければなりません。

:::comment
* If the inductive or indexed family of the decreasing parameter has data type parameters, then these data type parameters may themselves only depend on function parameters that are part of the {tech}[fixed prefix].

:::

* 減少パラメータの帰納型または添字付けられた型の族がデータ型のパラメータを持つ場合、これらのデータ型パラメータは、それ自身が {tech}[fixed 接頭辞] の一部である関数パラメータにのみ依存することができます。

:::comment
A {deftech}_fixed parameter_ is a function parameter that is passed unmodified in all recursive calls and is not an index of the recursive parameter's type.
The {deftech}_fixed prefix_ is the longest prefix of the function's parameters in which all are fixed.

:::

{deftech}_fixed パラメータ_ （fixed parameter）はすべての再帰呼び出しで変更されずに渡される関数パラメータであり、再帰パラメータの型の添字ではありません。 {deftech}_fixed 接頭辞_ （fixed prefix）は、関数パラメータの中で、すべてが fixed である最長の接頭辞です。

:::comment
::example "Ineligible decreasing parameters"
:::
::::example "不適格な減少パラメータ"

:::comment
The decreasing parameter's type must be an inductive type.
In {lean}`notInductive`, a function is specified as the decreasing parameter:

:::

減少パラメータは帰納型でなければなりません。 {lean}`notInductive` では、減少パラメータとして関数が指定されています：

```lean (error := true) (name := badnoindct)
def notInductive (x : Nat → Nat) : Nat := notInductive (fun n => x (n+1))
termination_by structural x
```
```leanOutput badnoindct
cannot use specified parameter for structural recursion:
  its type is not an inductive
```

:::comment
If the decreasing parameter is an indexed family, all the indices must be variables.
In {lean}`constantIndex`, the indexed family {lean}`Fin'` is instead applied to a constant value:

:::

減少パラメータが添字付けられた型の族の場合、添字はすべて変数でなければなりません。 {lean}`constantIndex` では、代わりに添字付けられた型の族 {lean}`Fin'` が定数に適用されます：

```lean (error := true) (name := badidx)
inductive Fin' : Nat → Type where
  | zero : Fin' (n+1)
  | succ : Fin' n → Fin' (n+1)

def constantIndex (x : Fin' 100) : Nat := constantIndex .zero
termination_by structural x
```
```leanOutput badidx
cannot use specified parameter for structural recursion:
  its type Fin' is an inductive family and indices are not variables
    Fin' 100
```

:::comment
The parameters of the decreasing parameter's type must not depend on function parameters that come after varying parameters or indices.
In {lean}`afterVarying`, the {tech}[fixed prefix] is empty, because the first parameter `n` varies, so `p` is not part of the fixed prefix:

:::

減少パラメータの型のパラメータは、変化するパラメータや添字の後に来る関数パラメータに依存してはいけません。 {lean}`afterVarying` では、 {tech}[fixed 接頭辞] は空です。なぜなら、最初のパラメータ `n` は変化するため、`p` は fixed 接頭辞の一部ではないからです：

```lean (error := true) (name := badparam)
inductive WithParam' (p : Nat) : Nat → Type where
  | zero : WithParam' p (n+1)
  | succ : WithParam' p n → WithParam' p (n+1)

def afterVarying (n : Nat) (p : Nat) (x : WithParam' p n) : Nat :=
  afterVarying (n+1) p .zero
termination_by structural x
```
```leanOutput badparam
cannot use specified parameter for structural recursion:
  its type is an inductive datatype
    WithParam' p n
  and the datatype parameter
    p
  depends on the function parameter
    p
  which does not come before the varying parameters and before the indices of the recursion parameter.
```
::::

:::comment
Furthermore, every recursive call of the functions must be on a {deftech}_strict sub-term_ of the decreasing
parameter.

:::

さらに、すべての再帰的な関数呼び出しは減少パラメータの {deftech}_厳密な部分項_ （strict sub-term）に対して行われなければなりません。

:::comment
 * The decreasing parameter itself is a sub-term, but not a strict sub-term.
 * If a sub-term is the {tech key:="match discriminant"}[discriminant] of a {keywordOf Lean.Parser.Term.match}`match` expression or other pattern-matching syntax, the pattern that matches the discriminant is a sub-term in the {tech}[right-hand side] of each {tech}[match alternative].
   In particular, the rules of {ref "match-generalization"}[match generalization] are used to connect the discriminant to the occurrences of the pattern term in the right-hand side; thus, it respects {tech}[definitional equality].
   The pattern is a _strict_ sub-term if and only if the discriminant is a strict sub-term.
 * If a sub-term is a constructor applied to arguments, then its recursive arguments are strict sub-terms.

:::

 * 減少パラメータはそれ自体が部分項ですが、厳密な部分項ではありません。
 * 部分項が {keywordOf Lean.Parser.Term.match}`match` 式やその他のパターンマッチ構文の {tech key:="マッチ判別子"}[判別子] の場合、判別子にマッチするパターンは各 {tech}[マッチ選択肢] の {tech}[右辺] の部分項です。特に {ref "match-generalization"}[マッチの一般化] の規則は、判別子を右辺におけるパターン項の出現に接続するために使用されます；つまり、 {tech}[definitional equality] を考慮します。判別子が厳密な部分項である場合に限り、パターンは _厳密な_ 部分項となります。
 * 部分項が引数に適用されるコンストラクタである場合、その再帰的引数は厳密な部分項です。

```lean (show := false)
section
variable (n : Nat)
```
:::comment
::example "Nested Patterns and Sub-Terms"
:::
::::example "入れ子のパターンと部分項"

:::comment
In the following example, the decreasing parameter {lean}`n` is matched against the nested pattern {lean type:="Nat"}`.succ (.succ n)`. Therefore {lean type:="Nat"}`.succ (.succ n)` is a (non-strict) sub-term of {lean type:="Nat"}`n`, and consequently  both {lean type:="Nat"}`n` and {lean type:="Nat"}`.succ n` are strict sub-terms, and the definition is accepted.

:::

以下の例では、減少パラメータ {lean}`n` は入れ子のパターン {lean type:="Nat"}`.succ (.succ n)` にマッチします。したがって、 {lean type:="Nat"}`.succ (.succ n)` は {lean type:="Nat"}`n` の（非厳密な）部分項であり、その結果 {lean type:="Nat"}`n` と {lean type:="Nat"}`.succ n` はともに厳密な部分項であるため、この定義は受け入れられます。

```lean
def fib : Nat → Nat
  | 0 | 1 => 1
  | .succ (.succ n) =>  fib n + fib (.succ n)
termination_by structural n => n
```

:::comment
For clarity, this example uses {lean type:="Nat"}`.succ n` and {lean type:="Nat"}`.succ (.succ n)` instead of the equivalent {lean}`Nat`-specific {lean}`n+1` and {lean}`n+2`.

:::

このことをわかりやすくするために、この例では {lean}`Nat` 固有の書き方である {lean}`n+1` と {lean}`n+2` の代わりに {lean type:="Nat"}`.succ n` と {lean type:="Nat"}`.succ (.succ n)` を使用しています。

:::TODO
Link to where this special syntax is documented.
:::

::::
```lean (show := false)
end
```

```lean (show := false)
section
variable {α : Type u} (n n' : Nat) (xs : List α)
```
:::comment
::example "Matching on Complex Expressions Can Prevent Elaboration"
:::
::::example "複雑な式へのマッチによるエラボレーションの阻害"

:::comment
In the following example, the decreasing parameter {lean}`n` is not directly the {tech key:="match discriminant"}[discriminant] of the {keywordOf Lean.Parser.Term.match}`match` expression.
Therefore, {lean}`n'` is not considered a sub-term of {lean}`n`.

:::

以下の例では、減少パラメータ {lean}`n` は {keywordOf Lean.Parser.Term.match}`match` 式の直接の {tech key:="マッチ判別子"}[判別子] ではありません。したがって、 {lean}`n'` は {lean}`n` の部分項とはみなされません。

```lean (error := true) (keep := false) (name := badtarget)
def half (n : Nat) : Nat :=
  match Option.some n with
  | .some (n' + 2) => half n' + 1
  | _ => 0
termination_by structural n
```
```leanOutput badtarget
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    half n'
```

:::comment
Using {tech}[well-founded recursion], and explicitly connecting the discriminant to the pattern of the match, this definition can be accepted.

:::

{tech}[整礎再帰] を使うことで、判別子をマッチのパターンに明示的に結び付けることで、この定義は許容されます。

```lean
def half (n : Nat) : Nat :=
  match h : Option.some n with
  | .some (n' + 2) => half n' + 1
  | _ => 0
termination_by n
decreasing_by simp_all; omega
```

:::comment
Similarly, the following example fails: although {lean}`xs.tail` would reduce to a strict sub-term of {lean}`xs`, this is not visible to Lean according to the rules above.
In particular, {lean}`xs.tail` is not {tech key:="definitional equality"}[definitionally equal] to a strict sub-term of {lean}`xs`.

:::

同様に、以下の例は失敗します： {lean}`xs.tail` は {lean}`xs` の厳密な部分項に簡約されるにもかかわらず、上記の規則によりこの事実を Lean が見ることができません。具体的には、 {lean}`xs.tail` は {lean}`xs` の厳密な部分項に対して {tech key:="definitional equality"}[definitionally equal] ではありません。

```lean (error := true) (keep := false)
def listLen : List α → Nat
  | [] => 0
  | xs => listLen xs.tail + 1
termination_by structural xs => xs
```

::::
```lean (show := false)
end
```


:::comment
::example "Simultaneous Matching vs Matching Pairs for Structural Recursion"
:::
::::example "構造的再帰に対する同時マッチとマッチペア"

:::comment
An important consequence of the strategies that are used to prove termination is that *simultaneous matching of two {tech key:="match discriminant"}[discriminants] is not equivalent to matching a pair*.
Simultaneous matching maintains the connection between the discriminants and the patterns, allowing the pattern matching to refine the types of the assumptions in the local context as well as the expected type of the {keywordOf Lean.Parser.Term.match}`match`.
Essentially, the elaboration rules for {keywordOf Lean.Parser.Term.match}`match` treat the discriminants specially, and changing discriminants in a way that preserves the run-time meaning of a program does not necessarily preserve the compile-time meaning.

:::

停止性を証明するために使用される戦略の重要な帰結は、 *2つの {tech key:="マッチ判別子"}[判別子] の同時マッチはペアのマッチと同等ではない* ということです。同時マッチは判別子とパターンの間の繋がりを維持し、その {keywordOf Lean.Parser.Term.match}`match` における期待される型と同様に、ローカルコンテキストにおける仮定の型を絞り込むことを可能にします。基本的に、 {keywordOf Lean.Parser.Term.match}`match` に対するエラボレーションの規則では判別子を特別に扱っており、プログラムの実行時の意味を保持する方法で判別子を変更してもコンパイル時の意味が保持されるとは限りません。

:::comment
This function that finds the minimum of two natural numbers is defined by structural recursion on its first parameter:
:::

2つの自然数の最小値を求めるこの関数は、最初のパラメータに対する構造的再帰によって定義されます：

```lean (keep := false)
def min' (n k : Nat) : Nat :=
  match n, k with
  | 0, _ => 0
  | _, 0 => 0
  | n' + 1, k' + 1 => min' n' k' + 1
termination_by structural n
```

:::comment
Replacing the simultaneous pattern match on both parameters with a match on a pair causes termination analysis to fail:
:::

両方のパラメータに対する同時マッチをペアのマッチに置き換えると停止分析が失敗します：

```lean (error := true) (name := noMin)
def min' (n k : Nat) : Nat :=
  match (n, k) with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' n' k' + 1
termination_by structural n
```
```leanOutput noMin
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    min' n' k'
```

:::comment
This is because the analysis only considers direct pattern matching on parameters when matching recursive calls to strictly-smaller argument values.
Wrapping the discriminants in a pair breaks the connection.
:::

これは、狭義により小さな引数の値への再帰呼び出しをマッチさせる際に、分析がパラメータの直接的なパターンマッチしか考慮しないためです。判別子をペアで包むと、そのつながりが断ち切られます。

::::

:::comment
::example "Structural Recursion Under Pairs"
:::
::::example "ペア内の値に対する構造的再帰"

:::comment
This function that finds the minimum of the two components of a pair can't be elaborated via structural recursion.
:::

ペアの2つの成分の最小値を求めるこの関数は、構造的再帰によってエラボレートすることができません。

```lean (error := true) (name := minpair)
def min' (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' (n', k') + 1
termination_by structural nk
```
```leanOutput minpair
failed to infer structural recursion:
Cannot use parameter nk:
  the type Nat × Nat does not have a `.brecOn` recursor
```

:::comment
This is because the parameter's type, {name}`Prod`, is not recursive.
Thus, its constructor has no recursive parameters that can be exposed by pattern matching.

:::

これは、パラメータの型 {name}`Prod` が再帰的ではないからです。したがって、そのコンストラクタにはパターンマッチで公開できる再帰的なパラメータはありません。

:::comment
This definition is accepted using {tech}[well-founded recursion], however:
:::

しかし、この定義は {tech}[整礎再帰] を使うことで受け入れられます：

```lean (keep := false)
def min' (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' (n', k') + 1
termination_by nk
```
::::

```lean (show := false)
section
variable (n n' : Nat)
```
:::comment
::example "Structural Recursion and Definitional Equality"
:::
::::example "構造的再帰と definitional equality"

:::comment
Even though the recursive occurrence of {lean}`countdown` is applied to a term that is not a strict sub-term of the decreasing parameter, the following definition is accepted:
:::

{lean}`countdown` の再帰的な出現が減少パラメータの厳密な部分項ではない項に適用されているにもかかわらず、以下の定義は許容されます：

```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown (n' + 0)
termination_by structural n
```

:::comment
This is because {lean}`n' + 0` is {tech key:="definitional equality"}[definitionally equal] to {lean}`n'`, which is a strict sub-term of {lean}`n`.
{tech key:="strict sub-term"}[Sub-terms] that result from pattern matching are connected to the {tech key:="match discriminant"}[discriminant] using the rules for {ref "match-generalization"}[match generalization], which respect definitional equality.

:::

これは {lean}`n' + 0` が、 {lean}`n` の厳密な部分項である {lean}`n'` と {tech key:="definitional equality"}[definitionally equal] であるからです。パターンマッチで得られる {tech key:="厳密な部分項"}[部分項] は、definitional equality を考慮している {ref "match-generalization"}[マッチの一般化] の規則を用いて {tech key:="マッチ判別子"}[判別子] に接続されます。

:::comment
In {lean}`countdown'`, the recursive occurrence is applied to {lean}`0 + n'`, which is not definitionally equal to `n'` because addition on natural numbers is structurally recursive in its second parameter:
:::

{lean}`countdown'` において、その再帰的な出現は {lean}`0 + n'` に適用されますが、自然数の足し算は第2引数に対して構造的再帰であるため `n'` に definitionally equal ではありません：

```lean (error := true) (name := countdownNonDefEq)
def countdown' (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown' (0 + n')
termination_by structural n
```
```leanOutput countdownNonDefEq
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    countdown' (0 + n')
```

::::
```lean (show := false)
end
```

:::comment
# Mutual Structural Recursion
:::

# 相互構造的再帰（Mutual Structural Recursion）

%%%
tag := "mutual-structural-recursion"
%%%

:::comment
Lean supports the definition of {tech}[mutually recursive] functions using structural recursion.
Mutual recursion may be introduced using a {tech}[mutual block], but it also results from {keywordOf Lean.Parser.Term.letrec}`let rec` expressions and {keywordOf Lean.Parser.Command.declaration}`where` blocks.
The rules for mutual structural recursion are applied to a group of actually mutually recursive, lifted definitions, that results from the {ref "mutual-syntax"}[elaboration steps] for mutual groups.
If every function in the mutual group has a {keyword}`termination_by structural` annotation indicating that function’s decreasing argument, then structural recursion is used to translate the definitions.

:::

Lean は構造的再帰を利用した {tech}[相互再帰] 関数の定義をサポートしています。相互再帰は {tech}[相互ブロック] を使って導入できますが、 {keywordOf Lean.Parser.Term.letrec}`let rec` 式と {keywordOf Lean.Parser.Command.declaration}`where` ブロックにおいても得ることができます。相互再帰の規則は、相互グループの {ref "mutual-syntax"}[エラボレーションのステップ] から得られる、実際に相互再帰的で持ち上げられた定義のグループに適用されます。相互グループ内のすべての関数が、その関数の減少引数を示す {keyword}`termination_by structural` 注釈を持っている場合、構造的再帰は定義の翻訳に使用されます。

:::comment
The requirements on the decreasing argument above are extended:

:::

減少引数に対する要件は上述のものから拡張されます：

:::comment
 * All the types of all the decreasing arguments must be from the same inductive type, or more generally from the same {ref "mutual-inductive-types"}[mutual group of inductive types].

:::

 * すべての減少引数の型は、同じ帰納型、またはより一般的には同じ {ref "mutual-inductive-types"}[帰納型の相互グループ] からのものでなければなりません。

:::comment
 * The parameters of the decreasing parameter's types must be the same for all functions, and may depend only on the _common_ fixed prefix of function arguments.

:::

 * 減少パラメータの型におけるパラメータは、すべての関数で同じでなければならず、関数引数の _共通の_ fixed 接頭辞にのみ依存することができます・

:::comment
The functions do not have to be in a one-to-one correspondence to the mutual inductive types.
Multiple functions can have a decreasing argument of the same type, and not all types that are mutually recursive with the decreasing argument need have a corresponding function.

:::

関数は相互帰納型と一対一に対応している必要はありません。複数の関数が同じ型である減少引数を持つことができ、減少引数を持つ相互再帰なすべての型が対応する関数を持つ必要はありません。

:::comment
::example "Mutual Structural Recursion Over Non-Mutual Types"
:::
::::example "非相互型に対する相互構造的再帰"

:::comment
The following example demonstrates mutual recursion over a non-mutual inductive data type:

:::

以下の例は非相互帰納データ型に対する相互再帰を示しています：

```lean
mutual
  def even : Nat → Prop
    | 0 => True
    | n+1 => odd n
  termination_by structural n => n

  def odd : Nat → Prop
    | 0 => False
    | n+1 => even n
  termination_by structural n => n
end
```
::::

:::comment
::example "Mutual Structural Recursion Over Mutual Types"
:::
::::example "相互型に対する相互構造的再帰"

:::comment
The following example demonstrates recursion over mutually inductive types.
The functions {lean}`Exp.size` and {lean}`App.size` are mutually recursive.

:::

以下の例は相互帰納型に対する相互再帰を示しています。関数 {lean}`Exp.size` と {lean}`App.size` は相互再帰的です。

```lean
mutual
  inductive Exp where
    | var : String → Exp
    | app : App → Exp

  inductive App where
    | fn : String → App
    | app : App → Exp → App
end

mutual
  def Exp.size : Exp → Nat
    | .var _ => 1
    | .app a => a.size
  termination_by structural e => e

  def App.size : App → Nat
    | .fn _ => 1
    | .app a e => a.size + e.size + 1
  termination_by structural a => a
end
```

:::comment
The definition of {lean}`App.numArgs` is structurally recursive over type {lean}`App`.
It demonstrates that not all inductive types in the mutual group need to be handled.

:::

{lean}`App.numArgs` の定義は、 {lean}`App` 型に対して構造的再帰です。これは相互グループ内のすべての帰納型を処理する必要がないことを示しています。

```lean
def App.numArgs : App → Nat
  | .fn _ => 0
  | .app a _ => a.numArgs + 1
termination_by structural a => a
```

::::

:::planned 235

Describe mutual structural recursion over {ref "nested-inductive-types"}[nested inductive types].

:::


:::comment
# Inferring Structural Recursion
:::

# 構造的再帰の推論（Inferring Structural Recursion）

%%%
tag := "inferring-structural-recursion"
%%%


:::comment
If no {keyword}`termination_by` clauses are present in a recursive or mutually recursive function definition, then Lean attempts to infer a suitable structurally decreasing argument, effectively by trying all suitable parameters in sequence.
If this search fails, Lean then attempts to infer {tech}[well-founded recursion].

:::

{keyword}`termination_by` 句が再帰または相互再帰関数定義に存在しない場合、Lean はすべての該当するパラメータに対して順番に効率よく、構造的に減少する適切な引数の推論を試みます。この探索が失敗した場合、Lean は {tech}[整礎再帰] の推論を試みます。

:::comment
For mutually recursive functions, all combinations of parameters are tried, up to a limit to avoid combinatorial explosion.
If only some of the mutually recursive functions have {keyword}`termination_by structural` clauses, then only those parameters are considered, while for the other functions all parameters are considered for structural recursion.

:::

相互再帰関数に対しては、組み合わせ爆発を避けるために、限界まですべてのパラメータの組み合わせが試行されます。一部の相互再帰関数にのみ {keyword}`termination_by structural` 句がある場合、それらのパラメータのみが考慮され、それ以外の関数ではすべてのパラメータが構造的再帰の候補となります。

:::comment
A {keyword}`termination_by?` clause causes the inferred termination annotation to be shown.
It can be automatically added to the source file using the offered suggestion or code action.

:::

{keyword}`termination_by?` 句を指定すると、推論された停止注釈が表示されます。この内容は提案に対するサジェスト、またはコードアクションを使用することでソースファイルに自動で追加することができます。

:::comment
::example "Inferred Termination Annotations"
:::
::::example "推論された停止注釈"
:::comment
Lean automatically infers that the function {lean}`half` is structurally recursive.
The {keyword}`termination_by?` clause causes the inferred termination annotation to be displayed, and it can be automatically added to the source file with a single click.

:::

Lean は関数 {lean}`half` が構造的再帰であることを自動的に推論します。 {keyword}`termination_by?` 句を使用すると、推論された停止注釈が表示され、ワンクリックでソースファイルに自動的に追加されます。

```lean (name := inferStruct)
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by?
```
```leanOutput inferStruct
Try this: termination_by structural x => x
```
::::

:::comment
# Elaboration Using Course-of-Values Recursion
:::

# 累積再帰を使用したエラボレーション（Elaboration Using Course-of-Values Recursion）

:::comment
In this section, the construction used to elaborate structurally recursive functions is explained in more detail.
This elaboration uses the {ref "recursor-elaboration-helpers"}[`below` and `brecOn` constructions] that are automatically generated from inductive types' recursors.

:::

本節では、構造的再帰関数をさらに詳しく説明します。このエラボレーションは帰納型の再帰子から自動生成される {ref "recursor-elaboration-helpers"}[`below` と `brecOn` 構成] を使用します。

{spliceContents Manual.RecursiveDefs.Structural.RecursorExample}

:::comment
The structural recursion analysis attempts to translate the recursive pre-definition into a use of the appropriate structural recursion constructions.
At this step, pattern matching has already been translated into the use of matcher functions; these are treated specially by the termination checker.
Next, for each group of parameters, a translation using `brecOn` is attempted.

:::

構造的再帰分析は再帰的な事前定義を適切な構造的再帰の構成の利用に変換しようと試みます。このステップでは、パターンマッチはすでにマッチ関数の使用に変換されています；これらの関数は停止チェッカによって特別に扱われます。次に、各パラメータのグループに対して `brecOn` を使った変換が試みられます。

{spliceContents Manual.RecursiveDefs.Structural.CourseOfValuesExample}

:::comment
The `below` construction is a mapping from each value of a type to the results of some function call on _all_ smaller values; it can be understood as a memoization table that already contains the results for all smaller values.
The notion of “smaller value” that is expressed in the `below` construction corresponds directly to the definition of {tech}[strict sub-terms].

:::

`below` 構成は型の各値から _すべての_ 小さい値に対する関数呼び出しの結果へのマッピングです；これはすべての小さい値の結果をすでの格納したメモ化テーブルとして理解することができます。`below` 構成において表現される「小さい値」という概念は {tech}[厳密な部分項] の定義に直接対応します。

:::comment
Recursors expect an argument for each of the inductive type's constructors; these arguments are called with the constructor's arguments (and the result of recursion on recursive parameters) during {tech}[ι-reduction].
The course-of-values recursion operator `brecOn`, on the other hand, expects just a single case that covers all constructors at once.
This case is provided with a value and a `below` table that contains the results of recursion on all values smaller than the given value; it should use the contents of the table to satisfy the motive for the provided value.
If the function is structurally recursive over a given parameter (or parameter group), then the results of all recursive calls will be present in this table already.

:::

再帰子は帰納型のコンストラクタの各引数を期待します；これらの引数は {tech}[ι簡約] の間にコンストラクタの引数（および再帰パラメータに対する再帰の結果）とともに呼び出されます。一方、累積再帰の演算子 `brecOn` は一度にすべてのコンストラクタをカバーする単一のケースだけを期待します。このケースには値と、与えられた値よりも小さいすべての値に対する再帰の結果を含む `below` テーブルが提供されます；これは与えられた値に対する動機を満たすテーブルの内容を使用するべきです。関数が与えられたパラメータ（もしくはパラメータグループ）に対して構造的再帰である場合、すべての再帰呼び出しの結果はすでにこのテーブルに存在することになります。

:::comment
When the body of the recursive function is transformed into an invocation of `brecOn` on one of the function's parameters, the parameter and its course-of-values table are in scope.
The analysis traverses the body of the function, looking for recursive calls.
If the parameter is matched against, then its occurrences in the local context are {ref "match-generalization"}[generalized] and then instantiated with the pattern; this is also true for the type of the course-of-values table.
Typically, this pattern matching results in the type of the course-of-values table becoming more specific, which gives access to the recursive results for smaller values.
This generalization process implements the rule that patterns are {tech key:="strict sub-term"}[sub-terms] of match discriminants.
When an recursive occurrence of the function is detected, the course-of-values table is consulted to see whether it contains a result for the argument being checked.
If so, the recursive call can be replaced with a projection from the table.
If not, then the parameter in question doesn't support structural recursion.

:::

再帰関数の本体が関数のパラメータの1つに対する `brecOn` の呼び出しに変換されると、そのパラメータと値の累積テーブルがスコープに入ります。この解析は関数本体を走査し、再帰的な呼び出しを探します。パラメータがマッチした場合、ローカルコンテキストに出現するパラメータは {ref "match-generalization"}[一般化] され、そのパターンでインスタンス化されます；これは累積テーブルの型についても真です。通常、このパターンマッチの結果、累積テーブルの型はより具体的になり、より小さな値の再帰結果にアクセスできるようになります。この一般化処理は、パターンがマッチ識別子の {tech key:="厳密な部分項"}[部分項] であるという規則を実装します。関数の再帰的な出現が検出されると、累積テーブルが参照され、チェックされている引数の結果が含まれているかどうかが確認されます。もし含まれていれば、再帰呼び出しはテーブルからの射影で置き換えることができます。含まれていない場合は、当該パラメータは構造的再帰をサポートしていません。

```lean (show := false)
section
```

:::comment
::example "Elaboration Walkthrough"
:::
::::example "エラボレーションの一連の流れ"
:::comment
The first step in walking through the elaboration of {name}`half` is to manually desugar it to a simpler form.
This doesn't match the way Lean works, but its output is much easier to read when there are fewer {name}`OfNat` instances present.
This readable definition:
:::

{name}`half` のエラボレーションを進める最初のステップは、手作業でより単純な形に脱糖することです。これは Lean の動作方法とは一致しませんが、 {name}`OfNat` インスタンスの数が少なければその出力はずっと読みやすくなります。この読みやすい定義：

```lean (keep := false)
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
```
:::comment
can be rewritten to this somewhat lower-level version:
:::

は、以下のやや低レベルのバージョンに書き換えることができます：

```lean (keep := false)
def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```

:::comment
The elaborator begins by elaborating a pre-definition in which recursion is still present but the definition is otherwise in Lean's core type theory.
Turning on the compiler's tracing of pre-definitions, as well as making the pretty printer more explicit, makes the resulting pre-definition visible:
:::

エラボレータは、再帰はまだ存在するものの、それ以外は Lean のコア型理論に沿った事前定義をエラボレートすることから始めます。コンパイラの事前定義の追跡をオンにすると、プリティプリンタがより明示的になり、その結果事前定義が見えるようになります：

```lean (keep := false) (show := false)
-- Test of next block - visually check correspondence when updating!
set_option trace.Elab.definition.body true in
set_option pp.all true in

/--
info: [Elab.definition.body] half : Nat → Nat :=
    fun (x : Nat) =>
      half.match_1.{1} (fun (x : Nat) => Nat) x (fun (_ : Unit) => Nat.zero) (fun (_ : Unit) => Nat.zero)
        fun (n : Nat) => Nat.succ (half n)
-/
#guard_msgs in
def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```
```lean (name := tracedHalf)
set_option trace.Elab.definition.body true in
set_option pp.all true in

def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```
:::comment
The returned trace message is:{TODO}[Trace not showing up in serialized info - figure out why so this test can work better, or better yet, add proper trace rendering to Verso]
:::

返される追跡メッセージは以下です：

```
[Elab.definition.body] half : Nat → Nat :=
    fun (x : Nat) =>
      half.match_1.{1} (fun (x : Nat) => Nat) x
        (fun (_ : Unit) => Nat.zero)
        (fun (_ : Unit) => Nat.zero)
        fun (n : Nat) => Nat.succ (half n)
```
:::comment
The auxiliary match function's definition is:
:::

この補助マッチ関数の定義は以下です：

```lean (name := halfmatch)
#print half.match_1
```
```leanOutput halfmatch (whitespace := lax)
def half.match_1.{u_1} :
    (motive : Nat → Sort u_1) → (x : Nat) →
    (Unit → motive Nat.zero) → (Unit → motive 1) →
    ((n : Nat) → motive n.succ.succ) →
    motive x :=
  fun motive x h_1 h_2 h_3 =>
    Nat.casesOn x (h_1 ()) fun n =>
      Nat.casesOn n (h_2 ()) fun n =>
        h_3 n
```
:::comment
Formatted more readably, this definition is:
:::

より読みやすくフォーマットすると、この定義は以下のようになります：

```lean
def half.match_1'.{u} :
    (motive : Nat → Sort u) → (x : Nat) →
    (Unit → motive Nat.zero) → (Unit → motive 1) →
    ((n : Nat) → motive n.succ.succ) →
    motive x :=
  fun motive x h_1 h_2 h_3 =>
    Nat.casesOn x (h_1 ()) fun n =>
      Nat.casesOn n (h_2 ()) fun n =>
        h_3 n
```
:::comment
In other words, the specific configuration of patterns used in {name}`half` are captured in {name}`half.match_1`.

:::

つまり、 {name}`half` で使用されるパターンの特定の構成は {name}`half.match_1` に取り込まれます。

:::comment
This definition is a more readable version of {name}`half`'s pre-definition:
:::

以下の定義は {name}`half` の事前定義をより読みやすくしたものです：

```lean
def half' : Nat → Nat :=
  fun (x : Nat) =>
    half.match_1 (motive := fun _ => Nat) x
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
```

:::comment
To elaborate it as a structurally recursive function, the first step is to establish the `bRecOn` invocation.
The definition must be marked {keywordOf Lean.Parser.Command.declaration}`noncomputable` because Lean does not support code generation for recursors such as {name}`Nat.brecOn`.
:::

この関数を構造的再帰関数として定義するには、まず `bRecOn` の呼び出しを確立します。この定義は {keywordOf Lean.Parser.Command.declaration}`noncomputable` とマークしなければなりません。なぜなら Lean は {name}`Nat.brecOn` のような再帰子のためのコード生成をサポートしていないからです。

```lean (error := true) (keep := false)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      _
/- To translate:
    half.match_1 (motive := fun _ => Nat) x
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```

:::comment
The next step is to replace occurrences of `x` in the original function body with the `n` provided by {name Nat.brecOn}`brecOn`.
Because `table`'s type depends on `x`, it must also be generalized when splitting cases with {name}`half.match_1`, leading to a motive with an extra parameter.

:::

次のステップは、もとの関数本体にある `x` を {name Nat.brecOn}`brecOn` が提供する `n` で置き換えることです。`table` の型は `x` に依存するため、 {name}`half.match_1` でケースを分割する際にも一般化する必要があり、追加のパラメータを持つ同期となります。

```lean (error := true) (keep := false) (name := threeCases)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        _
        _
        _)
      table
/- To translate:
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```
:::comment
The three cases' placeholders expect the following types:
:::

3つのケースのプレースホルダは以下の型を期待します：

```leanOutput threeCases
don't know how to synthesize placeholder for argument 'h_1'
context:
x n : Nat
table : Nat.below n
⊢ Unit → (fun k => Nat.below k → Nat) Nat.zero
```

```leanOutput threeCases
don't know how to synthesize placeholder for argument 'h_2'
context:
x n : Nat
table : Nat.below n
⊢ Unit → (fun k => Nat.below k → Nat) 1
```

```leanOutput threeCases
don't know how to synthesize placeholder for argument 'h_3'
context:
x n : Nat
table : Nat.below n
⊢ (n : Nat) → (fun k => Nat.below k → Nat) n.succ.succ
```

:::comment
The first two cases in the pre-definition are constant functions, with no recursion to check:

:::

事前定義にある最初の2つのケースは定数関数で、チェックする再帰はありません：

```lean (error := true) (keep := false) (name := oneMore)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        (fun () _ => .zero)
        (fun () _ => .zero)
        _)
      table
/- To translate:
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```

:::comment
The final case contains a recursive call.
It should be translated into a lookup into the course-of-values table.
A more readable representation of the last hole's type is:
:::

最後のケースには再帰呼び出しが含まれています。これは累積テーブルへの検索に変換されるべきです。最後のホールの型をより読みやすく表現すると次のようになります：

```leanTerm
(n : Nat) →
Nat.below (motive := fun _ => Nat) n.succ.succ →
Nat
```
:::comment
which is equivalent to
:::

これは以下と同等です：

```leanTerm
(n : Nat) →
Nat ×' (Nat ×' Nat.below (motive := fun _ => Nat) n) →
Nat
```

```lean (show := false)
example : ((n : Nat) →
Nat.below (motive := fun _ => Nat) n.succ.succ →
Nat) = ((n : Nat) →
Nat ×' (Nat ×' Nat.below (motive := fun _ => Nat) n) →
Nat) := rfl
```

```lean (show := false)

variable {n : Nat}
```

:::comment
The first {lean}`Nat` in the course-of-values table is the result of recursion on {lean}`n + 1`, and the second is the result of recursion on {lean}`n`.
The recursive call can thus be replaced by a lookup, and the elaboration is successful:

:::

累積テーブルの最初の {lean}`Nat` は {lean}`n + 1` に対する再帰の結果であり、2番目は {lean}`n` に対する再帰の結果です。したがって、再帰呼び出しは検索に置き換えることができ、エラボレーションが成功します：

```lean (error := true) (keep := false) (name := oneMore)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        (fun () _ => .zero)
        (fun () _ => .zero)
        (fun _ table => Nat.succ table.2.1)
      table
```

:::comment
The actual elaborator keeps track of the relationship between the parameter being checked for structural recursion and the positions in the course-of-values tables by inserting sentinel types with fresh names into the motive.
:::

実際のエラボレータは新しい名前を持つ番兵型を動機に挿入することによって、構造的再帰のためにチェックされるパラメータと累積テーブル内での位置との間の関係を追跡します。

::::

```lean (show := false)
end
```

::: planned 56
A description of the elaboration of mutually recursive functions
:::
