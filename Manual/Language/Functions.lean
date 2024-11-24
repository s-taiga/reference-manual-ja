/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

/-
#doc (Manual) "Functions" =>
-/
#doc (Manual) "関数（Functions）" =>
%%%
tag := "functions"
%%%


:::comment
Function types are a built-in feature of Lean.
{deftech}[Functions] map the values of one type (the {deftech}_domain_) into those of another type (the {deftech}_range_), and {deftech}_function types_ specify the domain and range of functions.
:::

関数型は Lean の組み込み機能です。 {deftech}[関数] （function）とはある型の値（ {deftech}_定義域_ 、domain）から別の型の値（ {deftech}_値域_ 、range）へとマッピングし、 {deftech}_関数型_ （function type） は関数の定義域と値域を指定します。

:::comment
There are two kinds of function type:
:::

関数型には2種類あります：

:::comment
 : {deftech}[Dependent]

   Dependent function types explicitly name the parameter, and the function's range may refer explicitly to this name.
   Because types can be computed from values, a dependent function may return values from any number of different types, depending on its argument.{margin}[Dependent functions are sometimes referred to as {deftech}_dependent products_, because they correspond to an indexed product of sets.]
:::

 : {deftech}[依存的] （dependent）

   依存関数の型はパラメータに明示的に名前を付け、関数の値域はこの名前を明示的に参照することができます。型は値から計算できるため、依存関数はその引数に応じて任意の数の異なる型の値を返すことができます。 {margin}[依存関数は集合の添字付き積に対応するため、 {deftech}_依存積_ （dependent product）と呼ばれることもあります。]

:::comment
 : {deftech}[Non-Dependent]

   Non-dependent function types do not include a name for the parameter, and the range does not vary based on the specific argument provided.
:::

 : {deftech}[非依存的] （non-dependent）

   非依存関数の型はパラメータの名前を含まず、提供される特定の引数によって値域が変わることはありません。

:::::keepEnv
:::comment
::example "Dependent Function Types"
:::
::::example "依存関数型"

:::comment
The function {lean}`two` returns values in different types, depending on which argument it is called with:

:::

関数 {lean}`two` はどの引数で呼び出されるかに応じて異なる型の値を返します：

```lean
def two : (b : Bool) → if b then Unit × Unit else String :=
  fun b =>
    match b with
    | true => ((), ())
    | false => "two"
```

:::comment
The body of the function cannot be written with `if...then...else...` because it does not refine types the same way that {keywordOf Lean.Parser.Term.match}`match` does.
:::

関数の本体は `if...then...else...` と書くことができません。なぜならこの書き方は {keywordOf Lean.Parser.Term.match}`match` と同じように型を絞り込むわけではないからです。

::::
:::::

:::comment
In Lean's core language, all function types are dependent: non-dependent function types are dependent function types in which the parameter name does not occur in the range.
Additionally, two dependent function types that have different parameter names may be definitionally equal if renaming the parameter makes them equal.
However, the Lean elaborator does not introduce a local binding for non-dependent functions' parameters.

:::

Lean のコア言語では、すべての関数型は依存的です：非依存関数型はパラメータ名が値域内に存在しない依存関数型のことです。さらに、パラメータ名が異なる2つの依存関数型について、パラメータ名をリネームしたものが等しい場合、これら2つは定義上等しくなります。しかし、Lean のエラボレータは非依存関数のパラメータにローカル束縛を導入しません。

:::comment
::example "Definitional Equality of Dependent and Non-Dependent Functions"
:::
::::example "依存・非依存関数の定義上の等価性"
:::comment
The types {lean}`(x : Nat) → String` and {lean}`Nat → String` are definitionally equal:
:::

型 {lean}`(x : Nat) → String` と {lean}`Nat → String` は定義上等価です：

```lean
example : ((x : Nat) → String) = (Nat → String) := rfl
```
:::comment
Similarly, the types {lean}`(n : Nat) → n + 1 = 1 + n` and {lean}`(k : Nat) → k + 1 = 1 + k` are definitionally equal:
:::

同様に、型 {lean}`(n : Nat) → n + 1 = 1 + n` と {lean}`(k : Nat) → k + 1 = 1 + k` は定義上等価です：


```lean
example : ((n : Nat) → n + 1 = 1 + n) = ((k : Nat) → k + 1 = 1 + k) := rfl
```
::::

::::::keepEnv
:::comment
::example "Non-Dependent Functions Don't Bind Variables"
:::
:::::example "非依存関数は変数を束縛しない"

::::keepEnv
:::comment
A dependent function is required in the following statement that all elements of an array are non-zero:
:::

以下の文では、配列のすべての要素が0でないことを示す依存関数が必要です：

```lean
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (lt : i < xs.size) → xs[i] ≠ 0
```
::::

::::keepEnv
:::comment
This is because the elaborator for array access requires a proof that the index is in bounds.
The non-dependent version of the statement does not introduce this assumption:
:::

これは配列アクセスのためのエラボレータが、インデックスが範囲内にあることの証明を必要とするためです。非依存バージョンの文では、この仮定は導入されていません：

```lean (error := true) (name := nondepOops)
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (i < xs.size) → xs[i] ≠ 0
```
```leanOutput nondepOops
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
xs : Array Nat
i : Nat
⊢ i < xs.size
```
::::
:::::
::::::

:::comment
While the core type theory does not feature {tech}[implicit] parameters, function types do include an indication of whether the parameter is implicit.
This information is used by the Lean elaborator, but it does not affect type checking or definitional equality in the core theory and can be ignored when thinking only about the core type theory.

:::

コア型理論には {tech}[implicit] パラメータはありませんが、関数型にはパラメータが暗黙かどうかの表示があります。この情報は Lean のエラボレータに使用されますが、コア型理論における型チェックや定義上の等価性には影響しないため、コア型理論についてだけ考える場合は無視しても構いません。

:::comment
::example "Definitional Equality of Implicit and Explicit Function Types"
:::
::::example "暗黙・明示の関数型の定義上の等価性"
:::comment
The types {lean}`{α : Type} → (x : α) → α` and {lean}`(α : Type) → (x : α) → α` are definitionally equal, even though the first parameter is implicit in one and explicit in the other.
:::

型 {lean}`{α : Type} → (x : α) → α` と {lean}`(α : Type) → (x : α) → α` は最初のパラメータが一方が暗黙的で他方では明示的でありながら、定義上等価です。

```lean
example :
    ({α : Type} → (x : α) → α)
    =
    ((α : Type) → (x : α) → α)
  := rfl
```

::::

:::comment
# Function Abstractions
:::

# 関数抽象（Function Abstractions）


:::comment
In Lean's type theory, functions are created using {deftech}_function abstractions_ that bind a variable.
{margin}[In various communities, function abstractions are also known as _lambdas_, due to Alonzo Church's notation for them, or _anonymous functions_ because they don't need to be defined with a name in the global environment.]
When the function is applied, the result is found by {tech key:="β"}[β-reduction]: substituting the argument for the bound variable.
In compiled code, this happens strictly: the argument must already be a value.
When type checking, there are no such restrictions; the equational theory of definitional equality allows β-reduction with any term.

:::

Lean の型理論では、関数は変数を束縛する {deftech}_関数抽象_ （function abstraction）を使用して作成されます。 {margin}[様々なコミュニティでは、関数抽象は Alonzo Church の記法に由来する _ラムダ式_ としても知られており、グローバル環境で名前を定義する必要がないことから _無名関数_ （anonymous function）としても知られています。] 関数を適用すると、 {tech key:="β"}[β簡約] によって結果が求められます。コンパイルされたコードでは、これは正格に行われます：引数はすでに値でなければなりません。型チェックの際には、このような制約はありません；定義上の等価における等式の理論では、どのような項でもβ簡約が許可されます。

:::comment
In Lean's {ref "function-terms"}[term language], function abstractions may take multiple parameters or use pattern matching.
These features are translated to simpler operations in the core language, where all functions abstractions take exactly one parameter.
Not all functions originate from abstractions: {tech}[type constructors], {tech}[constructors], and {tech}[recursors] may have function types, but they cannot be defined using function abstractions alone.


:::

Lean の {ref "function-terms"}[項の言語] では、関数抽象は複数のパラメータを取ったりパターンマッチを使ったりすることができます。これらの機能はコア言語ではより単純な操作に変換され、抽象化された関数はすべてちょうど1つだけのパラメータを取ります。すべての関数が抽象に由来するわけではありません： {tech}[型コンストラクタ] ・ {tech}[コンストラクタ] ・ {tech}[再帰子] は関数型を持ちえますが、関数抽象だけでは定義できません。

:::comment
# Currying
:::

# カリー化（Currying）
%%%
tag := "currying"
%%%



:::comment
In Lean's core type theory, every function maps each element of the domain to a single element of the range.
In other words, every function expects exactly one parameter.
Multiple-parameter functions are implemented by defining higher-order functions that, when supplied with the first parameter, return a new function that expects the remaining parameters.
This encoding is called {deftech}_currying_, popularized by and named after Haskell B. Curry.
Lean's syntax for defining functions, specifying their types, and applying them creates the illusion of multiple-parameter functions, but the result of elaboration contains only single-parameter functions.

:::

Lean のコア型理論では、すべての関数は定義域の要素をそれぞれ値域の単一の要素にマッピングします。言い換えれば、すべての関数は正確に1つのパラメータを必要とします。複数のパラメータを持つ関数は、高階関数を定義することで実装されます。これは最初のパラメータを与えると、残りのパラメータを持つ新しい関数を返します。このエンコーディングは {deftech}[カリー化] （currying）と呼ばれ、Haskell B. Curry にちなんで命名されました。関数を定義し、型を指定し、それを適用するための Lean の構文は、複数パラメータの関数のような錯覚を引き起こしますが、エラボレーションの結果は単一パラメータの関数のみが含まれます。

:::comment
# Extensionality
:::

# 外延性（Extensionality）
%%%
tag := "function-extensionality"
%%%



:::comment
Definitional equality of functions in Lean is {deftech}_intensional_.
This means that definitional equality is defined _syntactically_, modulo renaming of bound variables and {tech}[reduction].
To a first approximation, this means that two functions are definitionally equal if they implement the same algorithm, rather than the usual mathematical notion of equality that states that two functions are equal if they map equal elements of the domain to equal elements of the range.

:::

Lean における関数の定義上の等価性は {deftech}_内包的_ （intensional）です。つまり、この定義上の等価性は、束縛変数のリネームと {tech}[簡約] によって _構文上_ （syntactically）で定義されます。大まかに言えば、これは2つの関数が同じアルゴリズムを実装していれば定義上等しいということを意味し、定義域の等しい要素を値域の等しい要素にマッピングしていれば等しいという通常の数学的な等値性の概念とは異なります。

:::comment
Definitional equality is used by the type checker, so it's important that it be predictable.
The syntactic character of intensional equality means that the algorithm to check it can be feasibly specified.
Checking extensional equality involves proving essentially arbitrary theorems about equality of functions, and there is no clear specification for an algorithm to check it.
This makes extensional equality a poor choice for a type checker.
Function extensionality is instead made available as a reasoning principle that can be invoked when proving the {tech}[proposition] that two functions are equal.

:::

定義上の等価性は型チェッカで使用されるため、予測可能であることが重要です。内包的な等価性の構文的特徴によって、それをチェックするアルゴリズムが適切に指定できます。外延的な等価性のチェックには、関数の等価性に関する本質的に任意の定理を証明する必要があり、それをチェックするアルゴリズムの明確な仕様はありません。このため、外延的な等価性は型チェッカに向きません。その代わりに関数の外延性は、2つの関数が等しいという {tech}[命題] を証明する時に推論原理として利用できるようにします。

::::keepEnv
```lean (show := false)
axiom α : Type
axiom β : α → Type
axiom f : (x : α) → β x

-- test claims in next para
example : (fun x => f x) = f := by rfl
```

:::comment
In addition to reduction and renaming of bound variables, definitional equality does support one limited form of extensionality, called {deftech}_η-equivalence_, in which functions are equal to abstractions whose bodies apply them to the argument.
Given {lean}`f` with type {lean}`(x : α) → β x`, {lean}`f` is definitionally equal to {lean}`fun x => f x`.
:::

束縛変数の簡約とリネームに加えて、 {deftech}[η同値] （η-equivalence）と呼ばれる外延性の1つの限定された形式をサポートします。これは関数はその本体が引数に適用する抽象と等しいことを指します。 {lean}`f` の型が {lean}`(x : α) → β x` であるとすると、 {lean}`f` は {lean}`fun x => f x` と定義上等価です。

::::

:::comment
When reasoning about functions, the theorem {lean}`funext`{margin}[Unlike some intensional type theories, {lean}`funext` is a theorem in Lean. It can be proved using {tech}[quotient] types.] or the corresponding tactics {tactic}`funext` or {tactic}`ext` can be used to prove that two functions are equal if they map equal inputs to equal outputs.

:::

関数について推論するとき、定理 {lean}`funext`{margin}[いくつかの拡張された型理論とは異なり、 {lean}`funext` は Lean における定理です。これは {tech}[quotient] 型を使って証明できます。] または対応するタクティク {tactic}`ext` を使用して、2つの関数が等しい入力を等しい出力にマッピングする場合に等しいことを証明することができます。

{docstring funext}

:::comment
# Totality and Termination
:::

# 全域性と停止（Totality and Termination）
%%%
tag := "totality"
%%%



:::comment
Functions can be defined recursively using {keywordOf Lean.Parser.Command.declaration}`def`.
From the perspective of Lean's logic, all functions are {deftech}_total_, meaning that they map each element of the domain to an element of the range in finite time.{margin}[Some programming language communities use the term _total_ in a different sense, where functions are considered total if they do not crash due to unhandled cases but non-termination is ignored.]
The values of total functions are defined for all type-correct arguments, and they cannot fail to terminate or crash due to a missing case in a pattern match.

:::

関数は {keywordOf Lean.Parser.Command.declaration}`def` を使って再帰的に定義することができます。Lean の論理の観点から、すべての関数は {deftech}_全域_ （total）です。これは関数が定義域の各要素を値域の要素に有限時間でマッピングすることを意味します。 {margin}[プログラミング言語のコミュニティによっては、より限定的な意味で _全域_ という用語を使用するものもあり、その場合、関数はクラッシュしなければ全域と見なされますが、非停止は無視されます。] 全域関数の値はすべての型が正しい引数に対して定義され、パターンマッチでケースが漏れて停止に失敗したりクラッシュしたりすることはありません。

:::comment
While the logical model of Lean considers all functions to be total, Lean is also a practical programming language that provides certain "escape hatches".
Functions that have not been proven to terminate can still be used in Lean's logic as long as their range is proven nonempty.
These functions are treated as uninterpreted functions by Lean's logic, and their computational behavior is ignored.
In compiled code, these functions are treated just like any others.
Other functions may be marked unsafe; these functions are not available to Lean's logic at all.
The section on {ref "partial-unsafe"}[partial and unsafe function definitions] contains more detail on programming with recursive functions.

:::

Lean の論理モデルはすべての関数を全域関数と見なしますが、Lean は実用的なプログラミング言語でもあり、ある種の「逃げ道」を用意しています。停止することが証明されていない関数は、その値域が空でないことが証明されている限り Lean の論理で使用することができます。これらの関数は Lean の論理では未解釈の関数として扱われ、その計算動作は無視されます。コンパイルされたコードでは、これらの関数は他の関数と同様に扱われます。そうではない関数は unsafe とマークされることがあります；これらの関数は Lean の論理では全く使用することができません。 {ref "partial-unsafe"}[partial と unsafe 関数定義] の節で再帰関数を使ったプログラミングの詳細があります。

:::comment
Similarly, operations that should fail at runtime in compiled code, such as out-of-bounds access to an array, can only be used when the resulting type is known to be inhabited.
These operations result in an arbitrarily chosen inhabitant of the type in Lean's logic (specifically, the one specified in the type's {name}`Inhabited` instance).

:::

同様に、配列への範囲外アクセスなど、コンパイルされたコードではランタイムに失敗するはずの操作は、結果の型が inhabited であることが分かっている場合にのみ使用することができます。これらの操作の結果、Lean のロジックでは型の住人が任意に選ばれます（具体的には、その型の {name}`Inhabited` インスタンスで指定されたもの）。

:::comment
::example "Panic"
:::
::::example "パニック"
:::comment
The function {name}`thirdChar` extracts the third element of an array, or panics if the array has two or fewer elements:
:::

関数 {name}`thirdChar` は配列の3番目の要素を取り出します。配列の要素が2個以下の場合はパニックになります：

```lean
def thirdChar (xs : Array Char) : Char := xs[2]!
```
:::comment
The (nonexistent) third elements of {lean}`#['!']` and {lean}`#['-', 'x']` are equal, because they result in the same arbitrarily-chosen character:
:::

{lean}`#['!']` と {lean}`#['-', 'x']` の（存在しない）3番目の要素は等しいです。なぜなら、どちらも同じ任意に選ばれた文字を返すからです：

```lean
example : thirdChar #['!'] = thirdChar #['-', 'x'] := rfl
```
:::comment
Indeed, both are equal to {lean}`'A'`, which happens to be the default fallback for {lean}`Char`:
:::

実際、どちらも {lean}`'A'` に等しく、これは偶然にも {lean}`Char` のデフォルトのフォールバックです：

```lean
example : thirdChar #['!'] = 'A' := rfl
example : thirdChar #['-', 'x'] = 'A' := rfl
```
::::
