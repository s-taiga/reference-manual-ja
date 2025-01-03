/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option linter.constructorNameAsVariable false

/-
#doc (Manual) "Terms" =>
-/
#doc (Manual) "項（Terms）" =>
%%%
tag := "terms"
%%%

::: planned 66
This chapter will describe Lean's term language, including the following features:
 * Name resolution, including variable occurrences, `open` declarations and terms
 * `fun`, with and without pattern matching
 * Literals (some via cross-references to the appropriate types, e.g. {name}`String`)
:::

:::comment
{deftech}_Terms_ are the principal means of writing mathematics and programs in Lean.
The {tech}[elaborator] translates them to Lean's minimal core language, which is then checked by the kernel and compiled for execution.
The syntax of terms is {ref "syntax-ext"}[arbitrarily extensible]; this chapter documents the term syntax that Lean provides out-of-the-box.

:::

{deftech}_項_ （term）は Lean で数学やプログラムを書くための主要な手段です。 {tech}[エラボレータ] によって Lean の最小限のコア言語に翻訳・カーネルによってチェック・そして実行のためにコンパイルされます。項の構文は、 {ref "syntax-ext"}[任意に拡張可能です] ；本章では Lean にデフォルトで備わっている項の構文を説明します。

:::comment
# Identifiers
:::

# 識別子（Identifiers）


:::syntax term (title := "Identifiers")
```
$x:ident
```
:::

:::comment
An identifier term is a reference to a name.{margin}[The specific lexical syntax of identifiers is described {ref "keywords-and-identifiers"}[in the section on Lean's concrete syntax].]
Identifiers also occur in contexts where they bind names, such as {keywordOf Lean.Parser.Term.let}`let` and {keywordOf Lean.Parser.Term.fun}`fun`; however, these binding occurrences are not complete terms in and of them selves.
The mapping from identifiers to names is not trivial: at any point in a {tech}[module], some number of {tech}[namespaces] will be open, there may be {tech}[section variables], and there may be local bindings.
Furthermore, identifiers may contain multiple dot-separated atomic identifiers; the dot both separates namespaces from their contents and variables from fields or functions that use {tech}[field notation].
This creates ambiguity, because an identifier `A.B.C.D.e.f` could refer to any of the following:

:::

識別子の項は名前への参照です。 {margin}[識別子についての具体的なレキシカル構文は {ref "keywords-and-identifiers"}[Lean での具体的な構文の節] で説明されています。] {keywordOf Lean.Parser.Term.let}`let` や {keywordOf Lean.Parser.Term.fun}`fun` のように、識別子は名前を束縛するコンテキストでも出現します；しかし、この場合の束縛の出現はそれらだけでは完全な項にはなりません。識別子から名前へのマッピングは自明ではありません： {tech}[module] 内の任意のポイントでも、 {tech}[namespaces] を開くことができ、そこでは {tech}[section variables] やローカルの束縛があるかもしれません。さらに、識別子はドットで区切られた複数のアトミック識別子を含むことがあります；ドットは名前空間とその内容、または変数と {tech}[フィールド記法] を使用するフィールドまたは関数の両方を区切ります。これはあいまいさを生みます。なぜなら、識別子 `A.B.C.D.e.f` は以下のいずれかを指す可能性があるからです：

:::comment
 * A name `f` in the namespace `A.B.C.D.e` (for instance, a function defined in `e`'s {keywordOf Lean.Parser.Command.declaration}`where` block).
 * An application of `T.f` to `A.B.C.D.e` if `A.B.C.D.e` has type `T`
 * A projection of field `f` from a structure named `A.B.C.D.e`
 * A series of field projections `B.C.D.e` from structure value `A`, followed by an application of `f` using field notation
 * If namespace `Q` is opened, it could be a reference to any of the above with a `Q` prefix, such as a name `f` in the namespace `Q.A.B.C.D.e`

:::

 * 名前空間 `A.B.C.D.e` にある名前 `f`（例えば、`e` の {keywordOf Lean.Parser.Command.declaration}`where` ブロックで定義された関数）
 * `A.B.C.D.e` が `T` 型を持つ場合、`T.f` の `A.B.C.D.e` への適用
 * 構造体 `A.B.C.D.e` からのフィールド `f` の射影
 * 構造体の値 `A` から一連のフィールド射影の列 `B.C.D.e` を適用し、フィールド記法を用いて `f` を適用したもの
 * 名前空間 `Q` が開いている場合は `Q` 接頭辞を持つ任意を参照できるため、`Q.A.B.C.D.e` に含まれる名前 `f` など

:::comment
This list is not exhaustive.
Given an identifier, the elaborator must discover which name or names an identifier refers to, and whether any of the trailing components are fields or functions applied via field notation.
This is called {deftech key:="resolve"}_resolving_ the name.

:::

このリストは網羅的ではありません。識別子が与えられると、エラボレータは識別子がどの名前（複数の場合もある）を参照しているのか、後続のコンポーネントのフィールドかフィールド記法で適用される関数なのかを発見しなければなりません。これは名前 {deftech}_解決_ （resolve）と呼ばれます。

:::comment
Some declarations in the global environment are lazily created the first time they are referenced.
Resolving an identifier in a way that both creates one of these declarations and results in a reference to it is called {deftech}_realizing_ the name.
The rules for resolving and realizing a name are the same, so even though this section refers only to resolving names, it applies to both.

:::

グローバル環境内のいくつかの宣言は、最初に参照された時に遅延して作成されます。これらの宣言の1つを作成し、その宣言を参照するように識別子を解決することを名前の {deftech}_実現_ （realizing）と呼びます。名前解決と名前実現の規則は同じであるため、この節では名前解決のみに言及しますが、両方に適用されます。

:::comment
Name resolution is affected by the following:
 * {tech key:="pre-resolved identifier"}[Pre-resolved names] attached to the identifier
 * The {tech}[macro scopes] attached to the identifier
 * The local bindings in scope, including auxiliary definitions created as part of the elaboration of {keywordOf Lean.Parser.Term.letrec}`let rec`.
 * Aliases created with {keywordOf Lean.Parser.Command.export}`export` in modules transitively imported by the current module
 * The current {tech}[section scope], in particular the current namespace, opened namespaces, and section variables


:::

名前解決は以下の影響を受けます：
 * 識別子にアタッチされた {tech key:="事前解決された識別子"}[事前解決された名前]
 * 識別子にアタッチされた {tech}[マクロスコープ]
 * {keywordOf Lean.Parser.Term.letrec}`let rec` のエラボレーションの一部として作成された補助定義を含む、スコープ内のローカル束縛
 * 現在のモジュールによってインポートされたモジュール内で {keywordOf Lean.Parser.Command.export}`export` で作成されたエイリアス
 * 現在の {tech}[section scope] 、特に、現在の名前空間・開いている名前空間・セクション変数

:::comment
Any prefix of an identifier can resolve to a set of names.
The suffix that was not included in the resolution process is then treated as field projections or field notation.
Resolutions of longer prefixes take precedence over resolutions of shorter prefixes; in other words, as few components as of the identifier as possible are treated as field notation.
An identifier prefix may refer to any of the following, with earlier items taking precedence over later ones:
 1. A locally-bound variable whose name is identical to the identifier prefix, including macro scopes, with closer local bindings taking precedence over outer local bindings.
 2. A local auxiliary definition whose name is identical to the identifier prefix
 3. A {tech}[section variable] whose name is identical to the identifier prefix
 3. A global name that is identical to a prefix of the {tech}[current namespace] appended to the identifier prefix, or for which an alias exists in a prefix of the current namespace, with longer prefixes of the current namespace taking precedence over shorter ones
 4. A global name that has been brought into scope via {keywordOf Lean.Parser.Command.open}`open` commands that is identical to the identifier prefix


:::

識別子のどの接頭辞も一連の名前へ解決することができます。解決プロセスに含まれなかった接尾辞は、フィールドの射影またはフィールド記法として扱われます。接頭辞は短いものより長いものの解決が優先されます；言い換えれば、識別子のできるだけ少ない構成要素がフィールド記法として扱われます。識別子の接頭辞は上から優先的に以下のいずれかを指すことがあります：
 1. 識別子の接頭辞と同じ名前を持つローカル束縛変数。これはマクロスコープを含め、最も近いローカル束縛がそれより外側のものよりも優先されます。
 2. 識別子の接頭辞と同じ名前を持つローカルの補助定義
 3. 識別子の接頭辞と同じ名前を持つ {tech}[section variable]
 4. {tech}[current namespace] の接頭辞に識別子の接頭辞を付加したものと同じグローバル名、または現在の名前空間の接頭辞にエイリアスが存在するもの。これは現在の名前空間においてより長い接頭辞が短いものよりも優先されます。
 5. {keywordOf Lean.Parser.Command.open}`open` コマンドによってスコープに入れられた、識別子の接頭辞と同じグローバル名

:::comment
If an identifier resolves to multiple names, then the elaborator attempts to use all of them.
If exactly one of them succeeds, then it is used as the meaning of the identifier.
It is an error if more than one succeed or if all fail.

:::

識別子が複数の名前に解決される場合は、エラボレータはそれらすべてを使おうとします。そのうち1つだけが成功すればそれが識別子の意味として使用されます。2つ以上成功するか、すべて失敗するとエラーになります。

:::::keepEnv
:::comment
::example "Local Names Take Precedence"
:::
::::example "ローカル名が優先される"
:::comment
Local bindings take precedence over global bindings:
:::

ローカル束縛はグローバル束縛よりも優先されます：

```lean (name := localOverGlobal)
def x := "global"

#eval
  let x := "local"
  x
```
```leanOutput localOverGlobal
"local"
```
:::comment
The innermost local binding of a name takes precedence over others:
:::

名前の最も内側のローカル束縛が優先されます：

```lean (name := innermostLocal)
#eval
  let x := "outer"
  let x := "inner"
  x
```
```leanOutput innermostLocal
"inner"
```
::::
:::::

:::::keepEnv
:::comment
::example "Longer Prefixes of Current Namespace Take Precedence"
:::
::::example "より長い現在の名前空間の接頭辞が優先される"
:::comment
The  namespaces `A`, `B`, and `C` are nested, and `A` and `C` each contain a definition of `x`.
:::

名前空間 `A` ・ `B` ・ `C` が入れ子になっており、`A` と `C` にはそれぞれ `x` の定義を含んでいます。

```lean (name := NS)
namespace A
def x := "A.x"
namespace B
namespace C
def x := "A.B.C.x"
```

:::comment
When the current namespace is `A.B.C`, {lean}`x` resolves to {lean}`A.B.C.x`.
:::

現在の名前空間が `A.B.C` の場合、 {lean}`x` は {lean}`A.B.C.x` に解決されます。

```lean (name := NSC)
#eval x
```
```leanOutput NSC
"A.B.C.x"
```
:::comment
When the current namespace is `A.B`, {lean}`x` resolves to {lean}`A.x`.
:::

現在の名前空間が `A.B` の場合、 {lean}`x` は {lean}`A.x` に解決されます。

```lean (name := NSB)
end C
#eval x
```
```leanOutput NSB
"A.x"
```
::::
:::::

:::::keepEnv
:::comment
::example "Longer Identifier Prefixes Take Precedence"
:::
::::example "より長い識別子の接頭辞が優先される"
:::comment
When an identifier could refer to different projections from names, the one with the longest name takes precedence:
:::

識別子が名前によって異なる射影で参照できる場合、名前が最も長いものが優先されます：

```lean
structure A where
  y : String
deriving Repr

structure B where
  y : A
deriving Repr

def y : B := ⟨⟨"shorter"⟩⟩
def y.y : A := ⟨"longer"⟩
```
:::comment
Given the above declarations, {lean}`y.y.y` could in principle refer either to the {name A.y}`y` field of the {name B.y}`y` field of {name}`y`, or to the {name A.y}`y` field of {name}`y.y`.
It refers to the {name A.y}`y` field of {name}`y.y`, because the name {name}`y.y` is a longer prefix of `y.y.y` than the name {name}`y`:
:::

上記の宣言の下、 {lean}`y.y.y` は原則として {name}`y` の {name B.y}`y` フィールドの {name A.y}`y` フィールドを指すことも、 {name}`y.y` の {name A.y}`y` フィールドを指すこともできます。これは {name}`y.y` の {name A.y}`y` フィールドを指します。なぜなら、`y.y.y` において {name}`y.y` は {name}`y` よりも長い接頭辞になるからです：

```lean (name := yyy)
#eval y.y.y
```
```leanOutput yyy
"longer"
```
::::
:::::

:::::keepEnv
:::comment
::example "Current Namespace Contents Take Precedence Over Opened Namespaces"
:::
::::example "現在の名前空間がオープンされた名前空間よりも優先される"
:::comment
When an identifier could refer either to a name defined in a prefix of the current namespace or to an opened namespace, the former takes precedence.
:::

識別子が、現在の名前空間の接頭辞で定義されている名前と、オープンされている名前空間のどちらかを指す可能性がある場合、前者が優先されます。

```lean
namespace A
def x := "A.x"
end A

namespace B
def x := "B.x"
namespace C
open A
#eval x
```
:::comment
Even though `A` was opened more recently than the declaration of {name}`B.x`, the identifier `x` resolves to {name}`B.x` rather than {name}`A.x` because `B` is a prefix of the current namespace `B.C`.
:::

`A` は {name}`B.x` の宣言よりも後にオープンされたにもかかわらず、識別子 `x` は {name}`A.x` ではなく {name}`B.x` に解決されます。なぜなら `B` は現在の名前空間 `B.C` の接頭辞であるからです。

```lean (name := nestedVsOpen)
#eval x
```
```leanOutput nestedVsOpen
"B.x"
```
::::
:::::

:::::keepEnv
:::comment
::example "Ambiguous Identifiers"
:::
::::example "あいまいな識別子"
:::comment
In this example, `x` could refer either to {name}`A.x` or {name}`B.x`, and neither takes precedence.
Because both have the same type, it is an error.
:::

この例では、`x` は {name}`A.x` または {name}`B.x` のどちらかを指す可能性があり、どちらも優先されません。どちらも同じ型であるため、これはエラーになります。

```lean (name := ambi)
def A.x := "A.x"
def B.x := "B.x"
open A
open B
#eval x
```
```leanOutput ambi (whitespace := lax)
ambiguous, possible interpretations
  B.x : String

  A.x : String
```
```lean (show := false)
```
::::
:::::
:::::keepEnv
:::comment
::example "Disambiguation via Typing"
:::
::::example "型付けによるあいまいさの解消"
:::comment
When they have different types, the types are used to disambiguate:
:::

型が異なる場合は、あいまいさをなくすために型が使われます：

```lean (name := ambiNo)
def C.x := "C.x"
def D.x := 3
open C
open D
#eval (x : String)
```
```leanOutput ambiNo
"C.x"
```
::::
:::::


:::comment
## Leading `.`
:::

## 先頭の（Leading `.`）


:::comment
When an identifier beings with a dot (`.`), the type that the elaborator expects for the expression is used to resolve it, rather than the current namespace and set of open namespaces.
{tech}[Generalized field notation] is related: leading dot notation uses the expect type of the identifier to resolve it to a name, while field notation uses the inferred type of the term immediately prior to the dot.

:::

識別子がドット（`.`）で始まる場合、現在の名前空間や開いている名前空間のセットではなく、エラボレータがその式に期待する型が解決に使用されます。これには {tech}[一般化されたフィールド記法] が関連しています：先頭のドット記法は識別子の期待される型を使用して名前に解決しますが、フィールド記法はドットの直前の項の推測される型を使用します。

:::comment
Identifiers with a leading `.` are to be looked up in the {deftech}_expected type's namespace_.
If the type expected for a term is a constant applied to zero or more arguments, then its namespace is the constant's name.
If the type is not an application of a constant (e.g., a function, a metavariable, or a universe) then it doesn't have a namespace.

:::

先頭が `.` である識別子は {deftech}_期待された型の名前空間_ （expected type's namespace）にて検索されます。ある項に対して期待される型が0個以上の引数に適用される定数である場合、その名前空間はその定数の名前になります。型が定数の適用ではない場合（関数・メタ変数・宇宙等）、名前空間はありません。

:::comment
If the name is not found in the expected type's namespace, but the constant can be unfolded to yield another constant, then its namespace is consulted.
This process is repeated until something other than an application of a constant is encountered, or until the constant can't be unfolded.

:::

その名前が期待される型の名前空間に見つからないが、定数を展開して別の定数を得ることができる場合、その名前空間が参照されます。この処理は定数の適用以外のものに遭遇するか、定数が展開できなくなるまで繰り返されます。

:::::keepEnv
:::comment
::example "Leading `.`"
:::
::::example "先頭の `.`"
:::comment
The expected type for {name List.replicate}`.replicate` is `List Unit`.
This type's namespace is `List`, so {name List.replicate}`.replicate` resolves to {name List.replicate}`List.replicate`.
:::

{name List.replicate}`.replicate` に期待される型は `List Unit` です。この型の名前空間は `List` であるため、 {name List.replicate}`.replicate` は {name List.replicate}`List.replicate` に解決されます。

```lean (name := dotRep)
#eval show List Unit from .replicate 3 ()
```
```leanOutput dotRep
[(), (), ()]
```
::::

:::comment
::example "Leading `.` and Unfolding Definitions"
:::
::::example "先頭の `.` と定義の展開"
:::comment
The expected type for {name List.replicate}`.replicate` is `MyList Unit`.
This type's namespace is `MyList`, but there is no definition `MyList.replicate`.
Unfolding {lean}`MyList Unit` yields {lean}`List Unit`, so {name List.replicate}`.replicate` resolves to {name List.replicate}`List.replicate`.
:::

{name List.replicate}`.replicate` に期待される型は `MyList Unit` です。この型の名前空間は `MyList` ですが、`MyList.replicate` という定義はありません。 {lean}`MyList Unit` を展開すると {lean}`List Unit` が得られるため、 {name List.replicate}`.replicate` は {name List.replicate}`List.replicate` に解決されます。

```lean (name := dotRep)
def MyList α := List α
#eval show MyList Unit from .replicate 3 ()
```
```leanOutput dotRep
[(), (), ()]
```
::::
:::::

:::comment
# Function Types
:::

# 関数型（Function Types）


:::comment
Lean's function types describe more than just the function's domain and range.
They also provide instructions for elaborating application sites by indicating that some parameters are to be discovered automatically via unification or {ref "instance-synth"}[type class synthesis], that others are optional with default values, and that yet others should be synthesized using a custom tactic script.
Furthermore, their syntax contains support for abbreviating {tech key:="currying"}[curried] functions.

:::

Lean の関数型は、関数の定義域と値域以上のものを記述します。関数型はその適用位置をエラボレートするための指示も提供します。これはいくつかのパラメータは単一化または {ref "instance-synth"}[型クラス統合] によって自動的に検出され、他のパラメータはデフォルトでオプションであり、さらに他のパラメータはカスタムのタクティクスクリプトを使用して統合すべきであることによって示されます。さらに、その構文には {tech key:="カリー化"}[カリー化された] 関数を省略するためのサポートが含まれています。

::::syntax term title:="Function types"
:::comment
Dependent function types include an explicit name:
:::

依存関数型には明示的な名前が含まれます：

```grammar
($x:ident : $t) → $t2
```

:::comment
Non-dependent function types do not:
:::

非依存関数型では含まれません：

```grammar
$t1:term → $t2
```
::::

::::syntax term title:="Curried Function Types"
:::comment
Dependent function types may include multiple parameters that have the same type in a single set of parentheses:
:::

依存関数型は、同じ型を持つ複数のパラメータを1つの括弧の中に含めることができます：

```grammar
($x:ident* : $t) → $t
```
:::comment
This is equivalent to repeating the type annotation for each parameter name in a nested function type.
:::

これは入れ子になった関数型の各パラメータ名に対して、型注釈を繰り返すことと同じです。

::::

::::syntax term title:="Implicit, Optional, and Auto Parameters"
:::comment
Function types can describe functions that take implicit, instance implicit, optional, and automatic parameters.
All but instance implicit parameters require one or more names.
:::

関数型は暗黙・インスタンス暗黙・オプショナル・自動的なパラメータを取る関数を記述することができます。インスタンス暗黙パラメータを除くすべてのパラメータは1つ以上の名前を必要とします。

```grammar
($x:ident* : $t := $e) → $t
```
```grammar
($x:ident* : $t := by $tacs) → $t
```
```grammar
{$x:ident* : $t} → $t
```
```grammar
[$t] → $t
```
```grammar
[$x:ident : $t] → $t
```
```grammar
⦃$x:ident* : $t⦄ → $t
```

::::

:::comment
::example "Multiple Parameters, Same Type"
:::
::::example "同じ型の複数のパラメータ"
:::comment
The type of {name}`Nat.add` can be written in the following ways:

:::

{name}`Nat.add` の型は以下のように書くことができます：

 * {lean}`Nat → Nat → Nat`

 * {lean}`(a : Nat) → (b : Nat) → Nat`

 * {lean}`(a b : Nat) → Nat`

:::comment
The last two types allow the function to be used with {tech}[named arguments]; aside from this, all three are equivalent.
:::

最後の2つの型は関数を {tech}[名前付き引数] と一緒に使うことができます；これを除けばこれら3つはすべて同等です。

::::

:::comment
# Functions
:::

# 関数（Functions）


%%%
tag := "function-terms"
%%%


:::comment
Terms with function types can be created via abstractions, introduced with the {keywordOf Lean.Parser.Term.fun}`fun` keyword.{margin}[In various communities, function abstractions are also known as _lambdas_, due to Alonzo Church's notation for them, or _anonymous functions_ because they don't need to be defined with a name in the global environment.]
While abstractions in the core type theory only allow a single variable to be bound, function terms are quite flexible in the high-level Lean syntax.

:::

関数型を持つ項は {keywordOf Lean.Parser.Term.fun}`fun` キーワードで導入される抽象化によって作成することができます。 {margin}[多くのコミュニティでは、関数抽象は Alonzo Church の記法に由来する _ラムダ式_ （lambda）や、これがグローバル環境で名前を与えて定義する必要がないことから _匿名関数_ （anonymous function）とよばれます。] コア型理論の抽象化では1つの変数しか束縛できませんが、高レベルの Lean での構文では関数項は非常に柔軟です。

::::syntax term title:="Function Abstraction"
:::comment
The most basic function abstraction introduces a variable to stand for the function's parameter:

:::

最も基本的な関数抽象では関数のパラメータを表す変数を導入します：

```grammar
fun $x:ident => $t
```

:::comment
At elaboration time, Lean must be able to determine the function's domain.
A type ascription is one way to provide this information:

:::

エラボレーション時に、Lean は関数の定義域を決定できなければなりません。type ascription はこの情報を提供する1つの方法です：

```grammar
fun $x:ident : term => $t
```
::::

:::comment
Function definitions defined with keywords such as {keywordOf Lean.Parser.Command.declaration parser:=Lean.Parser.Command.definition}`def` desugar to {keywordOf Lean.Parser.Term.fun}`fun`.
Inductive type declarations, on the other hand, introduce new values with function types (constructors and type constructors) that cannot themselves be implemented using just {keywordOf Lean.Parser.Term.fun}`fun`.

:::

{keywordOf Lean.Parser.Command.declaration parser:=Lean.Parser.Command.definition}`def` のようなキーワードで定義された関数定義は {keywordOf Lean.Parser.Term.fun}`fun` に脱糖されます。一方、帰納型の宣言は {keywordOf Lean.Parser.Term.fun}`fun` だけでは実装できない関数型（コンストラクタと型コンストラクタ）を持つ新しい値を導入します。

::::syntax term title:="Curried Functions"


:::comment
Multiple parameter names are accepted after after {keywordOf Lean.Parser.Term.fun}`fun`:
:::

{keywordOf Lean.Parser.Term.fun}`fun` の後に複数のパラメータ名を指定することができます：

```grammar
fun $x:ident $x:ident* => $t
```

```grammar
fun $x:ident $x:ident* : $t:term => $t
```

:::comment
Different type annotations for multiple parameters requires parentheses:

:::

複数のパラメータに対して異なる型注釈を付けるには、括弧が必要です：

```grammar
free{"fun " "(" (ident)* ": " term")" " =>" term}
```

:::comment
These are equivalent to writing nested {keywordOf Lean.Parser.Term.fun}`fun` terms.
:::

これらは {keywordOf Lean.Parser.Term.fun}`fun` 項を入れ子にして書くことと同じです。

::::

:::comment
The {keywordOf Lean.Parser.Term.fun}`=>` may be replaced by {keywordOf Lean.Parser.Term.fun}`↦` in all of the syntax described in this section.

:::

本節で説明するすべての構文において {keywordOf Lean.Parser.Term.fun}`=>` は {keywordOf Lean.Parser.Term.fun}`↦` に置き換えることができます。

:::comment
Function abstractions may also use pattern matching syntax as part of their parameter specification, avoiding the need to introduce a local variable that is immediately destructured.
This syntax is described in the {ref "pattern-fun"}[section on pattern matching].

:::

関数抽象では、パラメータ指定の一部としてパターンマッチ構文を使用することもでき、すぐに分解されてしまうローカル変数をわざわざ導入する必要性を避けることができます。この構文は {ref "pattern-fun"}[パターンマッチの節] で説明されています。

:::comment
## Implicit Parameters
:::

## 暗黙のパラメータ（Implicit Parameters）

%%%
tag := "implicit-functions"
%%%


:::comment
Lean supports implicit parameters to functions.
This means that Lean itself can supply arguments to functions, rather than requiring users to supply all needed arguments.
Implicit parameters come in three varieties:

:::

Lean は関数への暗黙のパラメータをサポートしています。これはユーザが必要な引数をすべて与えるのではなく、Lean 自身が関数に引数を与えられることを意味します。暗黙のパラメータには3種類あります：

:::comment
  : Ordinary implicit parameters

    Ordinary {deftech}[implicit] parameters are function parameters that Lean should determine values for via unification.
    In other words, each call site should have exactly one potential argument value that would cause the function call as a whole to be well-typed.
    The Lean elaborator attempts to find values for all implicit arguments at each occurrence of a function.
    Ordinary implicit parameters are written in curly braces (`{` and `}`).

:::

  : 通常の暗黙のパラメータ

    通常の {deftech}[暗黙] （implicit）のパラメータは、Lean が単一化によって値を決定すべき関数パラメータです。言い換えると、各呼び出し位置において、関数呼び出し全体が適切に型付けされるような潜在的な引数値を1つだけ持つべきです。Lean エラボレータは関数の各出現に対してすべての暗黙の引数の値を見つけようとします。通常の暗黙のパラメータは波括弧（`{` と `}`）で囲んで記述します。

:::comment
  : Strict implicit parameters

    {deftech}_Strict implicit_ parameters are identical to ordinary implicit parameters, except Lean will only attempt to find argument values when subsequent explicit arguments are provided at a call site.
    Strict implicit parameters are written in double curly braces (`⦃` and `⦄`, or `{{` and `}}`).

:::

  : 厳密な暗黙のパラメータ

    {deftech}_厳密な暗黙_ （strict implicit）なパラメータは通常の暗黙のパラメータと同じですが、Lean は呼び出し先で明示的な引数が指定された場合にのみ引数の値を見つけようとします。厳密な暗黙のパラメータは二重の波括弧（`⦃` と `⦄`、もしくは `{{` と `}}`）で記述します。

:::comment
  : Instance implicit parameters

    Arguments for {deftech}_instance implicit_ parameters are found via {ref "instance-synth"}[type class synthesis].
    Instance implicit parameters are written in square brackets (`[` and `]`).
    Unlike the other kinds of implicit parameter, instance implicit parameters that are written without a `:` specify the parameter's type rather than providing a name.
    Furthermore, only a single name is allowed.
    Most instance implicit parameters omit the parameter name because instances synthesized as parameters to functions are already available in the functions' bodies, even without being named explicitly.

:::

  : インスタンス暗黙のパラメータ

    {deftech}_インスタンス暗黙_ （instance implicit）のパラメータは {ref "instance-synth"}[型クラス統合] を介して見つかります。インスタンス暗黙のパラメータは角括弧（`[` と `]`）で囲まれます。他の種類の暗黙のパラメータとは異なり、インスタンス暗黙のパラメータは `:` 無しで記述され、名前を指定するのではなく、パラメータの型を指定します。さらに、単一の名前しか許されません。関数のパラメータとして統合されたインスタンスは、明示的に名前をつけなくても関数の本体ですでに利用可能であるため、ほとんどのインスタンス暗黙のパラメータはパラメータ名を省略します。

:::::keepEnv
:::comment
::example "Ordinary vs Strict Implicit Parameters"
:::
::::example "通常と厳密な暗黙のパラメータ"
:::comment
The difference between the functions {lean}`f` and {lean}`g` is that `α` is strictly implicit in {lean}`f`:
:::

{lean}`f` と {lean}`g` の違いは、 {lean}`f` では `α` が厳密に暗黙であることです：

```lean
def f ⦃α : Type⦄ : α → α := fun x => x
def g {α : Type} : α → α := fun x => x
```

:::comment
These functions are elaborated identically when applied to concrete arguments:
:::

これらの関数は具体的な引数に適用される際にも同じものとしてエラボレートされます：

```lean
example : f 2 = g 2 := rfl
```

:::comment
However, when the explicit argument is not provided, uses of {lean}`f` do not require the implicit `α` to be solved:
:::

しかし、明示的な引数が与えられない場合、 {lean}`f` の使用は暗黙の `α` を解決する必要はありません：

```lean
example := f
```
:::comment
However, uses of `g` do require it to be solved, and fail to elaborate if there is insufficient information available:
:::

一方で、`g` を利用する際はその解決を要求し、利用可能な情報が不十分な場合はエラボレートに失敗します：

```lean (error := true) (name := noAlpha)
example := g
```
```leanOutput noAlpha
don't know how to synthesize implicit argument 'α'
  @g ?m.6
context:
⊢ Type
```
::::
:::::


::::syntax term title := "Functions with Varying Binders"
:::comment
The most general syntax for {keywordOf Lean.Parser.Term.fun}`fun` accepts a sequence of binders:
:::

{keywordOf Lean.Parser.Term.fun}`fun` の最も一般的な構文では、束縛子のシーケンスを受け入れます：

```grammar
fun $p:funBinder $p:funBinder* => $t
```
::::


::::syntax Lean.Parser.Term.funBinder title:="Function Binders"
:::comment
Function binders may be identifiers:
:::

関数の束縛子には以下のいずれかの形式が可能です。単一の識別子：

```grammar
$x:ident
```
:::comment
parenthesized sequences of identifiers:
:::

括弧をつけた識別子の列：

```grammar
($x:ident $y:ident*)
```
:::comment
sequences of identifiers with a type ascription:
:::

type ascription の付いた識別子の列：

```grammar
($x:ident $y:ident* : $t)
```
:::comment
implicit parameters, with or without a type ascription:
:::

type ascription が有る・無い暗黙のパラメータ：

```grammar
{$x:ident $x:ident*}
```
```grammar
{$x:ident $x:ident* : $t}
```
:::comment
instance implicits, anonymous or named:
:::

無名・命名されたインスタンス暗黙：

```grammar
[$t:term]
```
```grammar
[$x:ident : $t]
```
:::comment
or strict implicit parameters, with or without a type ascription:
:::

type ascription が有る・無い厳密な暗黙のパラメータ：

```grammar
⦃$x:ident $x:ident*⦄
```
```grammar
⦃$x:ident* : $t⦄
```

:::comment
As usual, an `_` may be used instead of an identifier to create an anonymous parameter, and `⦃` and `⦄` may alternatively be written using `{{` and `}}`, respectively.
:::

通常通り、識別子の代わりに `_` を使って無名のパラメータを作成することができ、 `⦃` と `⦄` はそれぞれ `{{` と `}}` を使って書くことができます。

::::



:::comment
Lean's core language does not distinguish between implicit, instance, and explicit parameters: the various kinds of function and function type are definitionally equal.
The differences can be observed only during elaboration.

:::

Lean のコア言語では暗黙・インスタンス暗黙・明示的なパラメータを区別しません：様々な種類の関数と関数型は定義上等価です。これらの違いはエラボレーション時においてのみ観測されます。

```lean (show := false)
-- Evidence of claims in prior paragraph
example : ({x : Nat} → Nat) = (Nat → Nat) := rfl
example : (fun {x} => 2 : {x : Nat} → Nat) = (fun x => 2 : Nat → Nat) := rfl
example : ([x : Repr Nat] → Nat) = (Repr Nat → Nat) := rfl
example : (⦃x : Nat⦄ → Nat) = (Nat → Nat) := rfl
```


:::comment
If the expected type of a function includes implicit parameters, but its binders do not, then the resulting function may end up with more parameters than the binders indicated in the code.
This is because the implicit parameters are added automatically.

:::

関数の型に暗黙のパラメータが含まれており、束縛子には含まれていない場合、結果の関数にはコードで示された束縛子よりも多くのパラメータが含まれるようになる場合があります。これは暗黙のパラメータが自動的に追加されるためです。

:::comment
::example "Implicit Parameters from Types"
:::
::::example "型の暗黙のパラメータ"
:::comment
The identity function can be written with a single explicit parameter.
As long as its type is known, the implicit type parameter is added automatically.
:::

恒等関数は1つの明示的なパラメータで書くことができます。型が既知である限り、暗黙の型パラメータは自動的に追加されます。

```lean (name := funImplAdd)
#check (fun x => x : {α : Type} → α → α)
```
```leanOutput funImplAdd
fun {α} x => x : {α : Type} → α → α
```

:::comment
The following are all equivalent:
:::

下記はすべて同等です：

```lean (name := funImplThere)
#check (fun {α} x => x : {α : Type} → α → α)
```
```leanOutput funImplThere
fun {α} x => x : {α : Type} → α → α
```

```lean (name := funImplAnn)
#check (fun {α} (x : α) => x : {α : Type} → α → α)
```
```leanOutput funImplAnn
fun {α} x => x : {α : Type} → α → α
```

```lean (name := funImplAnn2)
#check (fun {α : Type} (x : α) => x : {α : Type} → α → α)
```
```leanOutput funImplAnn2
fun {α} x => x : {α : Type} → α → α
```

::::

:::comment
# Function Application
:::

# 関数適用（Function Application）

%%%
tag := "function-application"
%%%

:::comment
Ordinarily, function application is written using juxtaposition: the argument is placed after the function, with at least one space between them.
In Lean's type theory, all functions take exactly one argument and produce exactly one value.
All function applications combine a single function with a single argument.
Multiple arguments are represented via currying.

:::

通常、関数適用は並置するように記述されます：引数は関数の後ろに置かれ、その間には少なくとも1つの空白が入ります。Lean の型理論では、すべての関数は正確に1つの引数を取り、正確に1つの値を生成します。すべての関数適用は1つの関数と1つの引数を組み合わせたものです。複数引数はカリー化で表現されます。

:::comment
The high-level term language treats a function together with one or more arguments as a single unit, and supports additional features such as implicit, optional, and by-name arguments along with ordinary positional arguments.
The elaborator converts these to the simpler model of the core type theory.

:::

高レベルの項言語は、関数を1つ以上の引数と共に1つのユニットとして扱い、通常の位置引数と共に暗黙・オプショナル・名前によって指定される引数などの追加機能をサポートします。エラボレータはこれらをコア型理論の単純なモデルに変換します。

::::freeSyntax term
:::comment
A function application consists of a term followed by one or more arguments, or by zero or more arguments and a final {deftech}[ellipsis].
:::

関数適用は項とそれに続く1つ以上の引数、または0個以上の引数と最後の {deftech}[ellipsis] から構成されます。

```grammar
$e:term $e:argument+
***************
$e:term $e:argument* ".."
```
::::

{TODO}[Annotate with syntax kinds for incoming hyperlinks during traversal pass]
::::freeSyntax Lean.Parser.Term.argument (title := "Arguments")
:::comment
Function arguments are either terms or {deftech}[named arguments].
:::

関数引数は項または {deftech}[名前付き引数] （named argument）です。

```grammar
$e:term
***********
"("$x:ident ":=" $e:term")"
```
::::

:::comment
The function's core-language type determines the placement of the arguments in the final expression.
Function types include names for their expected parameters.
In Lean's core language, non-dependent function types are encoded as dependent function types in which the parameter name does not occur in the body.
Furthermore, they are chosen internally such that they cannot be written as the name of a named argument; this is important to prevent accidental capture.

:::

関数のコア言語型は、最終的にできた式における引数の配置を決定します。関数型には期待されるパラメータの名前が含まれます。Lean のコア言語において非依存関数型は、そのパラメータ名が本体に出現しないような依存関数型としてエンコードされます。さらに、この場合の名前は、名前付き引数の名前として書けないように内部的に選択されます；これは偶発的なキャプチャを防ぐために重要です。

:::comment
Each parameter expected by the function has a name.
Recurring over the function's argument types, arguments are selected from the sequence of arguments as follows:
 * If the parameter's name matches the name provided for a named argument, then that argument is selected.
 * If the parameter is {tech}[implicit], a fresh metavariable is created with the parameter's type and selected.
 * If the parameter is {tech}[instance implicit], a fresh instance metavariable is created with the parameter's type and inserted. Instance metavariables are scheduled for later synthesis.
 * If the parameter is a {tech}[strict implicit] parameter and there are any named or positional arguments that have not yet been selected, a fresh metavariable is created with the parameter's type and selected.
 * If the parameter is explicit, then the next positional argument is selected and elaborated. If there are no positional arguments:
   * If the parameter is declared as an {tech}[optional parameter], then its default value is selected as the argument.
   * If the parameter is an {tech}[automatic parameter] then its associated tactic script is executed to construct the argument.
   * If the parameter is neither optional nor automatic, and no ellipsis is present, then a fresh variable is selected as the argument. If there is an ellipsis, a fresh metavariable is selected as if the argument were implicit.

:::

関数が期待する各パラメータには名前があります。関数の引数の型を繰り返しながら、引数は以下のように引数の列から選択されます：
 * パラメータ名が名前付き引数の名前と一致する場合、その引数が選択されます。
 * パラメータが {tech}[暗黙] である場合、そのパラメータの型で新しいメタ変数が作成・選択されます。
 * パラメータが {tech}[インスタンス暗黙] である場合、そのパラメータの型で新しいインスタンスのメタ変数が作成され、挿入されます。インスタンスのメタ変数は後で統合するようスケジュールされます。
 * パラメータが {tech}[厳密な暗黙] パラメータであり、まだ選択されていない名前付き引数または位置引数がある場合、そのパラメータの型で新しいメタ変数が作成・選択されます。
 * パラメータが明示的な場合、次の位置引数が選択され、エラボレートされます。位置引数が無い場合：
   * パラメータが {tech}[optional parameter] として宣言されている場合、そのデフォルト値が引数として選択されます。
   * パラメータが {tech}[automatic parameter] である場合、関連するタクティクスクリプトが引数を構築するために実行されます。
   * パラメータがオプショナルでも自動パラメータでもなく、ellipsis もない場合、引数として新しい変数が選択されます。ellipsis がある場合、引数が暗黙的であるかのように、新しいメタ変数が選択されます。

:::comment
As a special case, when the function application occurs in a {ref "pattern-matching"}[pattern] and there is an ellipsis, optional and automatic arguments become universal patterns (`_`) instead of being inserted.

:::

特殊なケースとして、 {ref "pattern-matching"}[パターン] の中で関数適用が発生し、ellipsis がある場合、オプショナル引数や自動引数は挿入されずに、ユニバーサルパターン（`_`）になります。

:::comment
It is an error if the type is not a function type and arguments remain.
After all arguments have been inserted and there is an ellipsis, then the missing arguments are all set to fresh metavariables, just as if they were implicit arguments.
If any fresh variables were created for missing explicit positional arguments, the entire application is wrapped in a {keywordOf Lean.Parser.Term.fun}`fun` term that binds them.
Finally, instance synthesis is invoked and as many metavariables as possible are solved:
 1. A type is inferred for the entire function application. This may cause some metavariables to be solved due to unification that occurs during type inference.
 2. The instance metavariables are synthesized. {tech}[Default instances] are only used if the inferred type is a metavariable that is the output parameter of one of the instances.
 3. If there is an expected type, it is unified with the inferred type; however, errors resulting from this unification are discarded. If the expected and inferred types can be equal, unification can solve leftover implicit argument metavariables. If they can't be equal, an error is not thrown because a surrounding elaborator may be able to insert {tech}[coercions] or {tech key:="lift"}[monad lifts].


:::

型が関数型でなく、引数が残っている場合はエラーとなります。すべての引数が挿入され、ellipsis がある場合、暗黙の引数であるかのように、欠落している引数にはすべて新しいメタ変数として設定されます。もし足りない明示的な位置変数のために新しい変数が作成された場合、適用全体はそれらを束縛する {keywordOf Lean.Parser.Term.fun}`fun` 項でラップされます。最後に、インスタンス統合が呼び出され、可能な限り多くのメタ変数が解決されます：
 1. 関数適用全体に対して型が推論されます。このため、型推論中に発生する単一化により、いくつかのメタ変数が解決されることがあります。
 2. インスタンスのメタ変数が統合されます。 {tech}[デフォルトインスタンス] は、推論された型がインスタンスの1つの出力パラメータであるメタ変数である場合にのみ使用されます。
 3. 期待される型がある場合、それは推論される型に単一化されます；しかし、この単一化の結果生じたエラーは破棄されます。期待される型と推論される型が等しい場合、単一化によって残された暗黙の引数のメタ変数を解決することができます。等しくない場合、周囲のエラボレータが {tech}[coercions] を挿入したり、 {tech key:="持ち上げ"}[モナド持ち上げ] ができる可能性があるため、エラーは投げられません。

:::::keepEnv
:::comment
::example "Named Arguments"
:::
::::example "名前付き引数"
:::comment
The {keywordOf Lean.Parser.Command.check}`#check` command can be used to inspect the arguments that were inserted for a function call.

:::

{keywordOf Lean.Parser.Command.check}`#check` コマンドは、関数呼び出しのために挿入された引数を検査するために使用することができます。

:::comment
The function {name}`sum3` takes three explicit {lean}`Nat` parameters, named `x`, `y`, and `z`.
:::

関数 {name}`sum3` は3つの明示的な {lean}`Nat` パラメータを取り、名前は `x`・`y`・`z` です。

```lean
def sum3 (x y z : Nat) : Nat := x + y + z
```

:::comment
All three arguments can be provided positionally.
:::

この3つの引数はすべて、位置引数として提供することができます。

```lean (name := sum31)
#check sum3 1 3 8
```
```leanOutput sum31
sum3 1 3 8 : Nat
```

:::comment
They can also be provided by name.
:::

また名前での提供も可能です。

```lean (name := sum32)
#check sum3 (x := 1) (y := 3) (z := 8)
```
```leanOutput sum32
sum3 1 3 8 : Nat
```

:::comment
When arguments are provided by name, it can be in any order.
:::

引数を名前で指定する場合、順序は問いません。

```lean (name := sum33)
#check sum3 (y := 3) (z := 8) (x := 1)
```
```leanOutput sum33
sum3 1 3 8 : Nat
```

:::comment
Named and positional arguments may be freely intermixed.
:::

名前付き引数と位置引数は自由に混在させることができます。

```lean (name := sum34)
#check sum3 1 (z := 8) (y := 3)
```
```leanOutput sum34
sum3 1 3 8 : Nat
```

:::comment
Named and positional arguments may be freely intermixed.
If an argument is provided by name, it is used, even if it occurs after a positional argument that could have been used.
:::

名前付き引数と位置引数は自由に混在させることができます。ある引数が名前で指定された場合、それが位置引数で使用される可能性があったとしてもその引数が使用されます。

```lean (name := sum342)
#check sum3 1 (x := 8) (y := 3)
```
```leanOutput sum342
sum3 8 3 1 : Nat
```

:::comment
If a named argument is to be inserted after arguments that aren't provided, a function is created in which the provided argument is filled out.
:::

ある名前付き引数が提供されていない引数の後に挿入される場合、提供された引数が記述された関数が作成されます。

```lean (name := sum35)
#check sum3 (z := 8)
```
```leanOutput sum35
fun x y => sum3 x y 8 : Nat → Nat → Nat
```

:::comment
Behind the scenes, the names of the arguments are preserved in the function type.
This means that the remaining arguments can again be passed by name.
:::

裏側では、引数の名前は関数型に保存されます。つまり、残りの引数は再び名前で呼び出すことができます。

```lean (name := sum36)
#check (sum3 (z := 8)) (y := 1)
```
```leanOutput sum36
fun x => (fun x y => sum3 x y 8) x 1 : Nat → Nat
```

```lean (show := false)
-- This is not shown in the manual pending #6373
-- https://github.com/leanprover/lean4/issues/6373
-- When the issue is fixed, this code will stop working and the text can be updated.

/--
info: let x := 15;
fun x y => sum3 x y x : Nat → Nat → Nat
-/
#guard_msgs in
#check let x := 15; sum3 (z := x)
```

::::
:::::


:::comment
Optional and automatic parameters are not part of Lean's core type theory.
They are encoded using the {name}`optParam` and {name}`autoParam` {tech}[gadgets].

:::

オプショナルパラメータと自動パラメータは Lean のコア型理論の一部ではありません。これらは {name}`optParam` ・ {name}`autoParam` {tech}[ガジェット] を使ってエンコードされます。

{docstring optParam}

{docstring autoParam}

:::comment
## Generalized Field Notation
:::

## 一般化されたフィールド記法（Generalized Field Notation）


:::comment
The {ref "structure-fields"}[section on structure fields] describes the notation for projecting a field from a term whose type is a structure.
Generalized field notation consists of a term followed by a dot (`.`) and an identifier, not separated by spaces.

:::

{ref "structure-fields"}[構造体フィールドの節] では、型が構造体である項からフィールドを射影するための記法を説明しています。一般的なフィールド記法は、空白で区切られていないドット（`.`）と識別子が続く項で構成されます。

:::syntax term (title := "Field Notation")
```grammar
$e:term.$f:ident
```
:::

:::comment
If a term's type is a constant applied to zero or more arguments, then {deftech}[field notation] can be used to apply a function to it, regardless of whether the term is a structure or type class instance that has fields.
The use of field notation to apply other functions is called {deftech}_generalized field notation_.

:::

項の型が0個以上の引数に適用される定数である場合、項がフィールドを持つ構造体または型クラスのインスタンスであるかどうかに関わらず、 {deftech}[フィールド記法] （field notation）を使用して関数を適用することができます。フィールド記法を使用して他の関数を適用することを {deftech}_一般化されたフィールド記法_ （generalized field notation）と呼びます。

:::comment
The identifier after the dot is looked up in the namespace of the term's type, which is the constant's name.
If the type is not an application of a constant (e.g., a function, a metavariable, or a universe) then it doesn't have a namespace and generalized field notation cannot be used.
If the field is not found, but the constant can be unfolded to yield a further type which is a constant or application of a constant, then the process is repeated with the new constant.

:::

ドットに続く識別子は、その項の型の名前空間で検索されます。これはその定数の名前です。その型が定数の適用でない場合（関数・メタ変数・宇宙など）、名前空間はないため一般化されたフィールド記法は使用できません。フィールドが見つからなくても、定数を展開することで定数または定数の応用である型が得られる場合は、その新しい定数で処理を繰り返します。

:::comment
When a function is found, the term before the dot becomes an argument to the function.
Specifically, it becomes the first explicit argument that would not be a type error.
Aside from that, the application is elaborated as usual.

:::

関数が見つかると、ドットの前の項がその関数の引数になります。具体的には、その関数の型エラーとならない最初の明示的な引数になります。それを除けば、適用は通常通りにエラボレートされます。

:::::keepEnv
```lean (show := false)
section
variable (name : Username)
```
:::comment
::example "Generalized Field Notation"
:::
::::example "一般化されたフィールド記法"
:::comment
The type {lean}`Username` is a constant, so functions in the {name}`Username` namespace can be applied to terms with type {lean}`Username` with generalized field notation.
:::

型 {lean}`Username` は定数であるため、 {name}`Username` 名前空間の関数は一般化されたフィールド記法を用いて {lean}`Username` 型を持つ項に適用することができます。

```lean
def Username := String
```

:::comment
One such function is {name}`Username.validate`, which checks that a username contains no leading whitespace and that only a small set of acceptable characters are used.
In its definition, generalized field notation is used to call the functions {lean}`String.isPrefixOf`, {lean}`String.any`, {lean}`Char.isAlpha`, and {lean}`Char.isDigit`.
In the case of {lean}`String.isPrefixOf`, which takes two {lean}`String` arguments, {lean}`" "` is used as the first  because it's the term before the dot.
{lean}`String.any` can be called on {lean}`name` using generalized field notation even though it has type {lean}`Username` because `Username.any` is not defined and {lean}`Username` unfolds to {lean}`String`.

:::

このような関数として {name}`Username.validate` は、ユーザ名に先頭の空白文字が含まれていないこと、および許容される文字種のみが使用されていることをチェックします。その定義では、関数 {lean}`String.isPrefixOf` ・ {lean}`String.any` ・ {lean}`Char.isAlpha` ・ {lean}`Char.isDigit` の呼び出しで一般化されたフィールド記法が使用されています。 {lean}`String.isPrefixOf` では、2つの {lean}`String` 引数を取りますが、 {lean}`" "` はドットの前の項であるため、最初の引数として使用されます。`Username.any` は定義されておらず、 {lean}`Username` は {lean}`String` に展開されるため、 {lean}`String.any` は {lean}`name` が {lean}`Username` 型であるにも関わらず呼び出すことができます。

```lean
def Username.validate (name : Username) : Except String Unit := do
  if " ".isPrefixOf name then
    throw "Unexpected leading whitespace"
  if name.any notOk then
    throw "Unexpected character"
  return ()
where
  notOk (c : Char) : Bool :=
    !c.isAlpha &&
    !c.isDigit &&
    !c ∈ ['_', ' ']

def root : Username := "root"
```

:::comment
However, {lean}`Username.validate` can't be called on {lean}`"root"` using field notation, because {lean}`String` does not unfold to {lean}`Username`.
:::

しかし、 {lean}`Username.validate` は {lean}`String` が {lean}`Username` に展開されないため、 {lean}`"root"` に対してフィールド記法を使って呼び出すことができません。

```lean (error := true) (name := notString)
#eval "root".validate
```
```leanOutput notString
invalid field 'validate', the environment does not contain 'String.validate'
  "root"
has type
  String
```

:::comment
{lean}`root`, on the other hand, has type {lean}`Username`:
:::

一方で {lean}`root` は {lean}`Username` 型を持ちます：

```lean (name := isUsername)
#eval root.validate
```
```leanOutput isUsername
Except.ok ()
```
::::
```lean (show := false)
end
```
:::::

{optionDocs pp.fieldNotation}

::::syntax attr (title := "Controlling Field Notation")
:::comment
The {attr}`pp_nodot` attribute causes Lean's pretty printer to not use field notation when printing a function.
:::

{attr}`pp_nodot` 属性は、関数を表示する際に Lean のプリティプリンタがフィールド記法を使わないようにします。

```grammar
pp_nodot
```
::::

:::::keepEnv
:::comment
::example "Turning Off Field Notation"
:::
::::example "フィールド記法の表示オフ"
:::comment
{lean}`Nat.half` is printed using field notation by default.
:::

{lean}`Nat.half` はデフォルトでフィールド記法として表示されます。

```lean
def Nat.half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => n.half + 1
```
```lean (name := succ1)
#check Nat.half Nat.zero
```
```leanOutput succ1
Nat.zero.half : Nat
```
:::comment
Adding {attr}`pp_nodot` to {name}`Nat.half` causes ordinary function application syntax to be used instead when displaying the term.
:::

{attr}`pp_nodot` に {name}`Nat.half` を追加すると、項を表示する際に、フィールド記法の代わりに通常の関数適用構文が使用されるようになります。

```lean (name := succ2)
attribute [pp_nodot] Nat.half

#check Nat.half Nat.zero
```
```leanOutput succ2
Nat.half Nat.zero : Nat
```
::::
:::::

:::comment
## Pipeline Syntax
:::

## パイプライン構文（Pipeline Syntax）


:::comment
Pipeline syntax provides alternative ways to write function applications.
Repeated pipelines use parsing precedence instead of nested parentheses to nest applications of functions to positional arguments.

:::

パイプライン構文は、関数適用を記述する代替方法を提供します。繰り返されたパイプラインでは、入れ子になった括弧の代わりにパースの優先順位を使用して、位置引数への関数の適用を入れ子にします。

::::syntax term (title := "Pipelines")
:::comment
Right pipe notation applies the term to the right of the pipe to the one on its left.
:::

右パイプ記法は、パイプの右側の項をその左側の項に適用します。

```grammar
e |> e
```
:::comment
Left pipe notation applies the term on the left of the pipe to the one on its right.
:::

左パイプ記法は、パイプの左側の項をその右側の項に適用します。

```grammar
e <| e
```
::::

:::comment
The intuition behind right pipeline notation is that the values on the left are being fed to the first function, its results are fed to the second one, and so forth.
In left pipeline notation, values on the right are fed leftwards.

:::

右パイプライン記法の直観的な考え方は、左側の値が最初の関数に送られ、その結果が2番目の関数に送られるというものです。左パイプライン記法では、右側の値が左方向に与えられます。

:::comment
::example "Right pipeline notation"
:::
::::example "右パイプライン記法"
:::comment
Right pipelines can be used to call a series of functions on a term.
For readers, they tend to emphasize the data that's being transformed.
:::

右パイプラインは、ある項に対して一連の関数を呼び出すために使用できます。コードを読む人に対して、変換されるデータが強調されやすくなります。

```lean (name := rightPipe)
#eval "Hello!" |> String.toList |> List.reverse |> List.head!
```
```leanOutput rightPipe
'!'
```
::::

:::comment
::example "Left pipeline notation"
:::
::::example "左パイプライン記法"
:::comment
Left pipelines can be used to call a series of functions on a term.
They tend to emphasize the functions over the data.
:::

左パイプラインは、ある項に対して一連の関数を呼び出すために使用できます。データよりも関数が強調されやすくなります。

```lean (name := lPipe)
#eval List.head! <| List.reverse <| String.toList <| "Hello!"
```
```leanOutput lPipe
'!'
```
::::

::::syntax term (title := "Pipeline Fields")
:::comment
There is a version of pipeline notation that's used for {tech}[generalized field notation].
:::

パイプライン記法には {tech}[一般化されたフィールド記法] を用いているバージョンがあります。

```grammar
$e |>.$_:ident
```
```grammar
$e |>.$_:fieldIdx
```
::::

:::::keepEnv
```lean (show := false)
section
universe u
axiom T : Nat → Type u
variable {e : T 3} {arg : Char}
axiom T.f : {n : Nat} → Char → T n → String
```

:::comment
{lean}`e |>.f arg` is an alternative syntax for {lean}`(e).f arg`.


:::

{lean}`e |>.f arg` は {lean}`(e).f arg` の別の構文です。

:::comment
::example "Pipeline Fields"
:::
::::example "パイプラインのフィールド"

:::comment
Some functions are inconvenient to use with pipelines because their argument order is not conducive.
For example, {name}`Array.push` takes an array as its first argument, not a {lean}`Nat`, leading to this error:
:::

引数の順序が適切ではないため、パイプラインで使用するには不便な関数もあります。例えば、 {name}`Array.push` は第1引数に {lean}`Nat` ではなく配列を取るため次のようなエラーが発生します：

```lean (name := arrPush)
#eval #[1, 2, 3] |> Array.push 4
```
```leanOutput arrPush
failed to synthesize
  OfNat (Array ?m.4) 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  Array ?m.4
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

:::comment
Using pipeline field notation causes the array to be inserted at the first type-correct position:
:::

パイプラインのフィールド記法を使うと、配列は型が正しい最初に位置に挿入されます：

```lean (name := arrPush2)
#eval #[1, 2, 3] |>.push 4
```
```leanOutput arrPush2
#[1, 2, 3, 4]
```

:::comment
This process can be iterated:
:::

このプロセスは繰り返すことができます：

```lean (name := arrPush3)
#eval #[1, 2, 3] |>.push 4 |>.reverse |>.push 0 |>.reverse
```
```leanOutput arrPush3
#[0, 1, 2, 3, 4]
```
::::


```lean (show := false)
end
```
:::::

:::comment
# Literals
:::

# リテラル（Literals）


:::comment
There are two kinds of numeric literal: natural number literals and {deftech}[scientific literals].
Both are overloaded via {tech key:="type class"}[type classes].

:::

数値リテラルには2種類あります：自然数リテラルと {deftech}[科学的リテラル] （scientific literal）です。どちらも {tech}[型クラス] によってオーバーロードされます。

:::comment
## Natural Numbers
:::

## 自然数（Natural Numbers）


```lean (show := false)
section
variable {n : Nat}
```

:::comment
When Lean encounters a natural number literal {lean}`n`, it interprets it via the overloaded method {lean}`OfNat.ofNat n`.
A {tech}[default instance] of {lean}`OfNat Nat n` ensures that the type {lean}`Nat` can be inferred when no other type information is present.

:::

Lean は自然数リテラル {lean}`n` に遭遇すると、オーバーロードされたメソッド {lean}`OfNat.ofNat n` によってそれを解釈します。 {lean}`OfNat Nat n` の {tech}[デフォルトインスタンス] は他の型情報が存在しない時に {lean}`Nat` の型を推論できることを保証します。

{docstring OfNat}

```lean (show := false)
end
```

:::comment
::example "Custom Natural Number Literals"
:::
::::example "カスタムの自然数リテラル"
:::comment
The structure {lean}`NatInterval` represents an interval of natural numbers.
:::

構造体 {lean}`NatInterval` は自然数の区間を表します。

```lean
structure NatInterval where
  low : Nat
  high : Nat
  low_le_high : low ≤ high

instance : Add NatInterval where
  add
    | ⟨lo1, hi1, le1⟩, ⟨lo2, hi2, le2⟩ => ⟨lo1 + lo2, hi1 + hi2, by omega⟩
```

:::comment
An {name}`OfNat` instance allows natural number literals to be used to represent intervals:
:::

{name}`OfNat` インスタンスによって、自然数リテラルを使って区間を表すことができます：

```lean
instance : OfNat NatInterval n where
  ofNat := ⟨n, n, by omega⟩
```
```lean (name := eval8Interval)
#eval (8 : NatInterval)
```
```leanOutput eval8Interval
{ low := 8, high := 8, low_le_high := _ }
```
::::

:::comment
There are no separate integer literals.
Terms such as {lean}`-5` consist of a prefix negation (which can be overloaded via the {name}`Neg` type class) applied to a natural number literal.

:::

整数リテラルという独立したものはありません。 {lean}`-5` のような項は、自然数リテラルに適用される前置否定（ {name}`Neg` 型クラスでオーバーロード可能）で構成されます。

:::comment
## Scientific Numbers
:::

## 科学的数値（Scientific Numbers）


:::comment
Scientific number literals consist of a sequence of digits followed by an optional period and decimal part and an optional exponent.
If no period or exponent is present, then the term is instead a natural number literal.
Scientific numbers are overloaded via the {name}`OfScientific` type class.

:::

科学的数値リテラルは、数字列の後ろにピリオド（任意）・小数部・指数（任意）が続くものです。ピリオドや指数が無い場合は、自然数リテラルになります。科学的数値は {name}`OfScientific` 型クラスによってオーバーロードされます。

{docstring OfScientific}

:::comment
There is an {lean}`OfScientific` instance for {name}`Float`, but no separate floating-point literals.

:::

{name}`Float` に対する {lean}`OfScientific` インスタンスはありますが、個別の浮動小数点リテラルはありません。 {margin}[訳注：16, 32, 64bitのそれぞれの精度の浮動小数点に対して存在しないという意味と思われる。]

:::comment
## Strings
:::

## 文字列（Strings）


:::comment
String literals are described in the {ref "string-syntax"}[chapter on strings.]

:::

文字列リテラルは {ref "string-syntax"}[文字列の章] で説明されています。

:::comment
## Lists and Arrays
:::

## リストと配列（Lists and Arrays）


:::comment
List and array literals contain comma-separated sequences of elements inside of brackets, with arrays prefixed by a hash mark (`#`).
Array literals are interpreted as list literals wrapped in a call to a conversion.
For performance reasons, very large list and array literals are converted to sequences of local definitions, rather than just iterated applications of the list constructor.

:::

リストと配列は、カンマで区切られたカッコ内の要素の列として構成されます。配列の場合はハッシュマーク（`#`）を先頭に付けます。配列リテラルは、変換の呼び出しでラップされたリストリテラルとして解釈されます。パフォーマンス上の理由から、非常に大きなリストや配列リテラルは、リストコンストラクタの繰り返し適用ではなく、ローカル定義の列に変換されます。

:::syntax term (title := "List Literals")
```grammar
[$_,*]
```
:::

:::syntax term (title := "Array Literals")
```grammar
#[$_,*]
```
:::

:::comment
::example "Long List Literals"
:::
::::example "長いリストリテラル"
:::comment
This list contains 32 elements.
The generated code is an iterated application of {name}`List.cons`:
:::

このリストは32個の要素を含みます。生成されたコードは {name}`List.cons` を繰り返し適用したものです：

```lean (name := almostLong)
#check
  [1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1]
```
```leanOutput almostLong
[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List Nat
```

:::comment
With 33 elements, the list literal becomes a sequence of local definitions:
:::

33個の要素を持つリストリテラルは、ローカル定義の列になります：

```lean (name := indeedLong)
#check
  [1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1]
```
```leanOutput indeedLong
let y :=
  let y :=
    let y := [1, 1, 1, 1, 1];
    1 :: 1 :: 1 :: 1 :: y;
  let y := 1 :: 1 :: 1 :: 1 :: y;
  1 :: 1 :: 1 :: 1 :: y;
let y :=
  let y := 1 :: 1 :: 1 :: 1 :: y;
  1 :: 1 :: 1 :: 1 :: y;
let y := 1 :: 1 :: 1 :: 1 :: y;
1 :: 1 :: 1 :: 1 :: y : List Nat
```

::::

:::comment
# Structures and Constructors
:::

# 構造体とコンストラクタ（Structures and Constructors）


:::comment
{ref "anonymous-constructor-syntax"}[Anonymous constructors] and {ref "structure-constructors"}[structure instance syntax] are described in their respective sections.

:::

{ref "anonymous-constructor-syntax"}[匿名コンストラクタ] と {ref "structure-constructors"}[構造体インスタンスの構文] はそれぞれの節で説明されています。

:::comment
# Conditionals
:::

# 条件（Conditionals）

%%%
tag := "if-then-else"
%%%

:::comment
The conditional expression is used to check whether a proposition is true or false.{margin}[Despite their syntactic similarity, the {keywordOf Lean.Parser.Tactic.tacIfThenElse}`if` used {ref "tactic-language-branching"}[in the tactic language] and the {keywordOf Lean.Parser.Term.doIf}`if` used {ref "tactic-language-branching"}[in `do`-notation] are separate syntactic forms, documented in their own sections.]
This requires that the proposition has a {name}`Decidable` instance, because it's not possible to check whether _arbitrary_ propositions are true or false.
There is also a {tech}[coercion] from {name}`Bool` to {lean}`Prop` that results in a decidable proposition (namely, that the {name}`Bool` in question is equal to {name}`true`), described in the {ref "decidable-propositions"}[section on decidability].

:::

条件式は命題が真か偽かをチェックするために使用されます。 {margin}[構文は似ていますが、 {keywordOf Lean.Parser.Tactic.tacIfThenElse}`if` は {ref "tactic-language-branching"}[タクティク言語] の、 {keywordOf Lean.Parser.Term.doIf}`if` は {ref "tactic-language-branching"}[`do` 記法] のそれぞれ別の構文形式であり、専用の節で説明されています。] 条件式は命題が {name}`Decidable` インスタンスを持っていることを必要とします。なぜなら、 _任意の_ 命題が真か偽であるかチェックすることはできないからです。また {name}`Bool` から決定可能な命題（すなわち、問題の {name}`Bool` が {name}`true` と等しいという命題）の {lean}`Prop` への {tech}[coercion] があり、これは {ref "decidable-propositions"}[決定可能性の節] で説明されています。

:::comment
There are two versions of the conditional expression: one simply performs a case distinction, while the other additionally adds an assumption about the proposition's truth or falsity to the local context.
This allows run-time checks to generate compile-time evidence that can be used to statically rule out errors.

:::

条件式には2つのバージョンがあります：1つは単純にケース分割を行うもので、もう1つは命題の真偽に関する仮定をローカルコンテキストに追加するものです。これによって実行時のチェックでコンパイル時の根拠を生成し、それを使って静的にエラーを除外することができます。

::::syntax term (title := "Conditionals")
:::comment
Without a name annotation, the conditional expression expresses only control flow.
:::

名前の注釈が無い場合、条件式はフローの制御のみを表現します。

```grammar
if $e then
  $e
else
  $e
```

:::comment
With the name annotation, the branches of the {keywordOf termDepIfThenElse}`if` have access to a local assumption that the proposition is respectively true or false.
:::

名前の注釈によって、 {keywordOf termDepIfThenElse}`if` のそれぞれの分岐は命題がそれぞれ真または偽であるというローカルな仮定にアクセスできます。

```grammar
if h : $e then
  $e
else
  $e
```
::::


:::::keepEnv
:::comment
::example "Checking Array Bounds"
:::
::::example "配列の範囲チェック"

:::comment
Array indexing requires evidence that the index in question is within the bounds of the array, so {name}`getThird` does not elaborate.

:::

配列のインデックス付けには、当該インデックスが配列の範囲内にあるという根拠が必要であるため、 {name}`getThird` はエラボレートしません。

```lean (error := true) (keep := false) (name := getThird1)
def getThird (xs : Array α) : α := xs[2]
```
```leanOutput getThird1
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.7
xs : Array α
⊢ 2 < xs.size
```

:::comment
Relaxing the return type to {name}`Option` and adding a bounds check results the same error.
This is because the proof that the index is in bounds was not added to the local context.
:::

戻り値の型を {name}`Option` に緩和し、範囲チェックを追加しても同じエラーになります。これはインデックスが範囲内にあるという証明がローカルコンテキストに追加されていないためです。

```lean (error := true) (keep := false) (name := getThird2)
def getThird (xs : Array α) : Option α :=
  if xs.size ≥ 3 then none
  else xs[2]
```
```leanOutput getThird2
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.7
xs : Array α
⊢ 2 < xs.size
```

:::comment
Naming the proof `h` is sufficient to enable the tactics that perform bounds checking to succeed, even though it does not occur explicitly in the text of the program.
:::

証明に `h` という名前をつけるだけで、たとえプログラムの本文中に明示的に出てこなくても範囲チェックを行うタクティクを成功させることができます。

```lean
def getThird (xs : Array α) : Option α :=
  if h : xs.size ≥ 3 then none
  else xs[2]
```

::::
:::::

:::comment
There is also a pattern-matching version of {keywordOf termIfLet}`if`.
If the pattern matches, then it takes the first branch, binding the pattern variables.
If the pattern does not match, then it takes the second branch.

:::

{keywordOf termIfLet}`if` のパターンマッチバージョンも存在します。パターンがマッチした場合、パターンの変数を束縛して最初の分岐が取られます。マッチしない場合は2番目の分岐が取られます。

:::syntax term (title := "Pattern-Matching Conditionals")
```grammar
if let $p := $e then
  $e
else
  $e
```
:::


:::comment
If a {name}`Bool`-only conditional statement is ever needed, the {keywordOf boolIfThenElse}`bif` variant can be used.
:::

{name}`Bool` のみの条件文が必要になった場合は、変種の {keywordOf boolIfThenElse}`bif` を使用することができます。

:::syntax term (title := "Boolean-Only Conditional")
```grammar
bif $e then
  $e
else
  $e
```
:::


:::comment
# Pattern Matching
:::

# パターンマッチ（Pattern Matching）

%%%
tag := "pattern-matching"
%%%


:::comment
{deftech}_Pattern matching_ is a way to recognize and destructure values using a syntax of {deftech}_patterns_ that are a subset of the terms.
A pattern that recognizes and destructures a value is similar to the syntax that would be used to construct the value.
One or more {deftech}_match discriminants_ are simultaneously compared to a series of {deftech}_match alternatives_.
Discriminants may be named.
Each alternative contains one or more comma-separated sequences of patterns; all pattern sequences must contain the same number of patterns as there are discriminants.
When a pattern sequence matches all of the discriminants, the term following the corresponding {keywordOf Lean.Parser.Term.match}`=>` is evaluated in an environment extended with values for each {tech}[pattern variable] as well as an equality hypothesis for each named discriminant.
This term is called the {deftech}_right-hand side_ of the match alternative.

:::

{deftech}_パターンマッチ_ （pattern matching）は項のサブセットである {deftech}_パターン_ （pattern）の構文を使用して、値を認識・分解するための手段です。値を認識して分解するパターンは、値を構成するために使用される構文に似ています。1つ以上の {deftech}_マッチ判別子_ （match discriminant）が一連の {deftech}_マッチ選択肢_ （match alternative）と同時に比較されます。判別子には名前を付けることができます。各選択肢は、カンマで区切られた1つ以上のパターン列を含んでいます；すべてのパターン列は、識別子の数と同じ数のパターンを含んでいなければなりません。パターン列がすべての判別子にマッチすると、対応する {keywordOf Lean.Parser.Term.match}`=>` に続く項が、各 {tech}[パターン変数] の値と各名前付き判別子に対する等式の仮定が追加された環境で評価されます。この項はマッチ選択肢の {deftech}_右辺_ （right-hand side）と呼ばれます。

:::syntax term (title := "Pattern Matching")
```grammar
match
    $[(generalizing := $e)]?
    $[(motive := $e)]?
    $[$d:matchDiscr],*
  with
$[| $[$e,*]|* => $e]*
```
:::

:::syntax matchDiscr (title := "Match Discriminants") (open := false)
```grammar
$e:term
```
```grammar
$h:ident : $e:term
```
:::

:::comment
Pattern matching expressions may alternatively use {tech}[quasiquotations] as patterns, matching the corresponding {name}`Lean.Syntax` values and treating the contents of {tech}[antiquotations] as ordinary patterns.
Quotation patterns are compiled differently than other patterns, so if one pattern in a {keywordOf Lean.Parser.Term.match}`match` is syntax, then all of them must be.
Quotation patterns are described in {ref "quote-patterns"}[the section on quotations].

:::

パターンマッチ式は代わりに {tech}[quasiquotations] をパターンとして使用することができ、対応する {name}`Lean.Syntax` 値にマッチし、 {tech}[antiquotations] の内容は通常のパターンとして扱われます。quotation のパターンはその他のパターンとは異なるコンパイルをされるため、 {keywordOf Lean.Parser.Term.match}`match` の中のどれか1つのパターンが構文であれば、すべてのパターンも構文でなければなりません。quotation パターンは {ref "quote-patterns"}[quotation の節] で説明されています。

:::comment
Patterns are a subset of the terms.
They consist of the following:

:::

パターンは項のサブセットです。これらは以下から構成されます：

:::comment
: Catch-All Patterns

  The hole syntax {lean}`_` is a pattern that matches any value and binds no pattern variables.
  Catch-all patterns are not entirely equivalent to unused pattern variables.
  They can be used in positions where the pattern's typing would otherwise require a more specific {tech}[inaccessible pattern], while variables cannot be used in these positions.

:::

: Catch-All パターン

  ホールの構文 {lean}`_` は任意の値にマッチし、パターン変数を束縛しないパターンです。Catch-All パターンは未使用のパターン変数を完全に同等ではありません。Catch-All パターンはパターンの型付けがより具体的な {tech}[アクセス不能パターン] を必要とするような位置で使用することができますが、変数はこのような位置では使用できません。

:::comment
: Identifiers

  If an identifier is not bound in the current scope and is not applied to arguments, then it represents a pattern variable.
  {deftech}_Pattern variables_ match any value, and the values thus matched are bound to the pattern variable in the local environment in which the {tech}[right-hand side] is evaluated.
  If the identifier is bound, it is a pattern if it is bound to the {tech}[constructor] of an {tech}[inductive type] or if its definition has the {attr}`match_pattern` attribute.

:::

: 識別子

  識別子が現在のスコープで束縛されず、引数にも適用されない場合、これはパターン変数を表します。 {deftech}_パターン変数_ （pattern variable）は任意の値にマッチし、こうしてマッチした値は {tech}[右辺] が評価されるローカル環境でパターン変数に束縛されます。識別子が束縛される場合、 {tech}[帰納型] の {tech}[コンストラクタ] に束縛されるか、その定義に {attr}`match_pattern` 属性があれば、それはパターンです。

:::comment
: Applications

  Function applications are patterns if the function being applied is an identifier that is bound to a constructor or that has the {attr}`match_pattern` attribute and if all arguments are also patterns.
  If the identifier is a constructor, the pattern matches values built with that constructor if the argument patterns match the constructor's arguments.
  If it is a function with the {attr}`match_pattern` attribute, then the function application is unfolded and the resulting term's {tech}[normal form] is used as the pattern.
  Default arguments are inserted as usual, and their normal forms are used as patterns.
  {tech key:="ellipsis"}[Ellipses], however, result in all further arguments being treated as universal patterns, even those with associated default values or tactics.

:::

: 適用

  関数適用はパターンになります。これは適用される関数がコンストラクタに束縛されている識別子であるか、 {attr}`match_pattern` 属性を持ち、すべての引数もパターンである場合です。識別子がコンストラクタの場合、引数のパターンがコンストラクタの引数にマッチすると、パターンはそのコンストラクタで構築された値にマッチします。 {attr}`match_pattern` 属性を持つ関数である場合、関数適用は展開され、結果の項の {tech}[正規形] がパターンとして使用されます。デフォルト引数は通常通り挿入され、その正規形がパターンとして使用されます。しかし、{tech}[ellipsis] は関連するデフォルト値やタクティクを持つものであっても、それ以降のすべての引数がユニバーサルパターンとして扱われてしまいます。

:::comment
: Literals

  {ref "char-syntax"}[Character literals] and {ref "string-syntax"}[string literals] are patterns that match the corresponding character or string.
  {ref "raw-string-literals"}[Raw string literals] are allowed as patterns, but {ref "string-interpolation"}[interpolated strings] are not.
  {ref "nat-syntax"}[Natural number literals] in patterns are interpreted by synthesizing the corresponding {name}`OfNat` instance and reducing the resulting term to {tech}[normal form], which must be a pattern.
  Similarly, {tech}[scientific literals] are interpreted via the corresponding {name}`OfScientific` instance.
  While {lean}`Float` has such an instance, {lean}`Float`s cannot be used as patterns because the instance relies on an opaque function that can't be reduced to a valid pattern.

:::

: リテラル

  {ref "char-syntax"}[文字リテラル] と {ref "string-syntax"}[文字列リテラル] は、対応する文字または文字列にマッチするパターンです。 {ref "raw-string-literals"}[生文字列リテラル] はパターンとして許容されますが、 {ref "string-interpolation"}[補間文字列] は許容されません。パターン内の {ref "nat-syntax"}[自然数リテラル] は、対応する {name}`OfNat` インスタンスを統合し、その結果の項を {tech}[正規形] に簡約することで解釈されます。同様に、 {tech}[科学的リテラル] は対応する {name}`OfScientific` インスタンスを介して解釈されます。 {lean}`Float` にはそのようなインスタンスがありますが、そのインスタンスは有効なパターンに簡約できない不透明な関数に依存しているため、 {lean}`Float` をパターンとして使用することはできません。

:::comment
: Structure Instances

  {tech}[Structure instances] may be used as patterns.
  They are interpreted as the corresponding structure constructor.

:::

: 構造体インスタンス

  {tech}[構造体インスタンス] はパターンとして使用することができます。それらは対応する構造体インスタンスとして解釈されます。

:::comment
: Quoted names

  Quoted names, such as {lean}`` `x `` and {lean}``` ``plus ```, match the corresponding {name}`Lean.Name` value.

:::

: quote された名前

  {lean}`` `x `` や {lean}``` ``plus ``` などの quote された名前は、対応する {name}`Lean.Name` 値をマッチします。

:::comment
: Macros

  Macros in patterns are expanded.
  They are patterns if the resulting expansions are patterns.

:::

: マクロ

  パターン内のマクロは展開されます。展開の結果がパターンであれば、それらはパターンです。

:::comment
: Inaccessible patterns

  {deftech}[Inaccessible patterns] are patterns that are forced to have a particular value by later typing constraints.
  Any term may be used as an inaccessible term.
  Inaccessible terms are parenthesized, with a preceding period (`.`).

:::

: アクセス不能パターン

  {deftech}[アクセス不能パターン] （inaccessible pattern）は、後の型付け制約によって特定の値を持つことを強制されるパターンです。任意の項をアクセス不能な項として使用することができます。アクセス不能項は括弧でくくられ、その前にピリオド（`.`）が付きます。

:::syntax term (title := "Inaccessible Patterns")
```grammar
.($e)
```
:::

:::comment
::example "Inaccessible Patterns"
:::
::::example "アクセス不能パターン"
:::comment
A number's _parity_ is whether it's even or odd:
:::

数値の _パリティ_ （parity）とはその値が偶か奇かを指します：

```lean
inductive Parity : Nat → Type where
  | even (h : Nat) : Parity (h + h)
  | odd (h : Nat) : Parity ((h + h) + 1)

def Nat.parity (n : Nat) : Parity n :=
  match n with
  | 0 => .even 0
  | n' + 1 =>
    match n'.parity with
    | .even h => .odd h
    | .odd h =>
      have eq : (h + 1) + (h + 1) = (h + h + 1 + 1) :=
        by omega
      eq ▸ .even (h + 1)
```

:::comment
Because a value of type {lean}`Parity` contains half of a number (rounded down) as part of its representation of evenness or oddness, division by two can be implemented (in an unconventional manner) by finding a parity and then extracting the number.
:::

{lean}`Parity` 型の値は、偶数または奇数の表現の一部として、数の半分（切り捨て）を含むため、パリティを判定してから数を抽出することで、（一般的ではないですが）2による除算を実装することができます。

```lean
def half (n : Nat) : Nat :=
  match n, n.parity with
  | .(h + h),     .even h => h
  | .(h + h + 1), .odd h  => h
```
:::comment
Because the index structure of {name}`Parity.even` and {name}`Parity.odd` force the number to have a certain form that is not otherwise a valid pattern, patterns that match on it must use inaccessible patterns for the number being divided.
:::

{name}`Parity.even` と {name}`Parity.odd` のインデックス構造は、それ以外の有効なパターンではない特定の形式を持つ数を強制するため、これにマッチするパターンは割られる数に対してアクセス不能パターンを使用しなければなりません。

::::

:::comment
Patterns may additionally be named.
{deftech}[Named patterns] associate a name with a pattern; in subsequent patterns and on the right-hand side of the match alternative, the name refers to the part of the value that was matched by the given pattern.
Named patterns are written with an `@` between the name and the pattern.
Just like discriminants, named patterns may also be provided with names for equality assumptions.

:::

パターンはさらに名前を付けることができます。 {deftech}[名前付きパターン] （named pattern）はパターンに名前を付けます；後続のパターンとマッチ選択肢の右側では、名前は指定されたパターンにマッチした値の部分を指します。名前付きパターンは名前とパターンの間に `@` を付けて記述します。判別子と同じように、名前付きパターンによって等価性の仮定にも名前を与えることができます。

:::syntax term (title := "Named Patterns")
```grammar
$x:ident@$e
```
```grammar
$x:ident@$h:ident:$e
```
:::


```lean (show := false) (keep := false)
-- Check claims about patterns

-- Literals
/-- error: invalid pattern, constructor or constant marked with '[match_pattern]' expected -/
#guard_msgs in
def foo (x : String) : String :=
  match x with
  | "abc" => ""
  | r#"hey"# => ""
  | s!"a{x}y" => _
  | _ => default

structure Blah where
  n : Nat
deriving Inhabited

instance : OfNat Blah n where
  ofNat := ⟨n + 1⟩

/--
error: missing cases:
(Blah.mk (Nat.succ (Nat.succ _)))
(Blah.mk Nat.zero)
-/
#guard_msgs in
def abc (n : Blah) : Bool :=
  match n with
  | 0 => true

partial instance : OfNat Blah n where
  ofNat :=
    let rec f (x : Nat) : Blah :=
      match x with
      | 0 => f 99
      | n + 1 => f n
    f n

-- This shows that the partial instance was not unfolded
/--
error: dependent elimination failed, type mismatch when solving alternative with type
  motive (instOfNatBlah_1.f 0)
but expected
  motive n✝
-/
#guard_msgs in
def defg (n : Blah) : Bool :=
  match n with
  | 0 => true

/--
error: dependent elimination failed, type mismatch when solving alternative with type
  motive (Float.ofScientific 25 true 1)
but expected
  motive x✝
-/
#guard_msgs in
def twoPointFive? : Float → Option Float
  | 2.5 => some 2.5
  | _ => none

/--
info: @Neg.neg.{0} Float instNegFloat (@OfScientific.ofScientific.{0} Float instOfScientificFloat 320 Bool.true 1) : Float
-/
#guard_msgs in
set_option pp.all true in
#check -32.0

structure OnlyThreeOrFive where
  val : Nat
  val2 := false
  ok : val = 3 ∨ val = 5 := by rfl


-- Default args are synthesized in patterns too!
/--
error: tactic 'rfl' failed, the left-hand side
  n = 3
is not definitionally equal to the right-hand side
  n = 5
x✝ : OnlyThreeOrFive
n : Nat
⊢ n = 3 ∨ n = 5
-/
#guard_msgs in
def ggg : OnlyThreeOrFive → Nat
  | {val := n} => n

/--
error: missing cases:
(OnlyThreeOrFive.mk _ true _)
-/
#guard_msgs in
def hhh : OnlyThreeOrFive → Nat
  | {val := n, ok := p} => n

-- Ellipses don't synth default args in patterns
def ggg' : OnlyThreeOrFive → Nat
  | .mk n .. => n

-- Ellipses do synth default args via tactics, but not exprs, otherwise
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: tactic 'rfl' failed, the left-hand side
  3 = 3
is not definitionally equal to the right-hand side
  3 = 5
⊢ 3 = 3 ∨ 3 = 5
---
info: { val := 3, val2 := ?m.1487, ok := ⋯ } : OnlyThreeOrFive
-/
#guard_msgs in
#check OnlyThreeOrFive.mk 3 ..

/-- info: { val := 3, val2 := ?_, ok := ⋯ } : OnlyThreeOrFive -/
#guard_msgs in
set_option pp.mvars.anonymous false in
#check OnlyThreeOrFive.mk 3 (ok := .inl rfl) ..

/--
info: fun y =>
  match
    let_fun this := ⟨y * 3, ⋯⟩;
    this with
  | ⟨x, z⟩ =>
    match x, z with
    | .(y * 3), ⋯ => () : Nat → Unit
-/
#guard_msgs in
#check fun (y : Nat) => match show {n : Nat// n = y * 3} from ⟨y*3, rfl⟩ with
  | ⟨x, z⟩ =>
    match x, z with
    | .(y * 3), rfl => ()

```

:::comment
## Types
:::

## 型（Types）


:::comment
Each discriminant must be well typed.
Because patterns are a subset of terms, their types can also be checked.
Each pattern that matches a given discriminant must have the same type as the corresponding discriminant.

:::

各判別子は適切に型付けされていなければなりません。パターンは項のサブセットであるため、その型もチェックできます。与えられた判別子にマッチする各パターンは、対応する判別子と同じ型を持っていなければなりません。

:::comment
The {tech}[right-hand side] of each match alternative should have the same type as the overall {keywordOf Lean.Parser.Term.match}`match` term.
To support dependent types, matching a discriminant against a pattern refines the types that are expected within the scope of the pattern.
In both subsequent patterns in the same match alternative and the right-hand side's type, occurrences of the discriminant are replaced by the pattern that it was matched against.


:::

各マッチ選択肢の {tech}[右辺] は、 {keywordOf Lean.Parser.Term.match}`match` 項全体と同じ型を持つ必要があります。依存型をサポートするために、判別子をパターンにマッチさせると、パターンの範囲内で期待される型が絞り込まれます。同じマッチ選択肢の後続パターンと右辺の型の両方において、判別子の出現はそれがマッチされたパターンに置き換えられます。

:::::keepEnv
```lean (show := false)
variable {α : Type u}
```

:::comment
::example "Type Refinement"
:::
::::example "型の絞り込み"
:::comment
This {tech}[添字族]indexed family describes mostly-balanced trees, with the depth encoded in the type.
:::

この {tech}[添字族] は深さが型にエンコードされた平衡に近い木を記述します。

```lean
inductive BalancedTree (α : Type u) : Nat → Type u where
  | empty : BalancedTree α 0
  | branch (left : BalancedTree α n) (val : α) (right : BalancedTree α n) : BalancedTree α (n + 1)
  | lbranch (left : BalancedTree α (n + 1)) (val : α) (right : BalancedTree α n) : BalancedTree α (n + 2)
  | rbranch (left : BalancedTree α n) (val : α) (right : BalancedTree α (n + 1)) : BalancedTree α (n + 2)
```

:::comment
To begin the implementation of a function to construct a perfectly balanced tree with some initial element and a given depth, a {tech}[hole] can be used for the definition.
:::

ある初期要素と与えられた深さに対して完全な平衡木を構成する関数の実装を始めるには、定義に {deftech}[ホール] を使います。

```lean (keep := false) (name := fill1) (error := true)
def BalancedTree.filledWith (x : α) (depth : Nat) : BalancedTree α depth := _
```
:::comment
The error message demonstrates that the tree should have the indicated depth.
:::

エラーメッセージはその木が指定された深さを持つべきであることを示しています。

```leanOutput fill1
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α depth
```

:::comment
Matching on the expected depth and inserting holes results in an error message for each hole.
These messages demonstrate that the expected type has been refined, with `depth` replaced by the matched values.
:::

期待される深さに対してマッチしてホールを挿入すると、それぞれのホールに対してエラーメッセージが表示されます。これらのメッセージは `depth` がマッチした値で置き換えられ、期待される型が絞り込まれたことを示します。

```lean (error := true) (name := fill2)
def BalancedTree.filledWith (x : α) (depth : Nat) : BalancedTree α depth :=
  match depth with
  | 0 => _
  | n + 1 => _
```
:::comment
The first hole yields the following message:
:::

一つ目のホールは以下のメッセージを生成します：

```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α 0
```
:::comment
The second hole yields the following message:
:::

二つ目のホールは以下のメッセージを生成します：

```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth n : Nat
⊢ BalancedTree α (n + 1)
```

:::comment
Matching on the depth of a tree and the tree itself leads to a refinement of the tree's type according to the depth's pattern.
This means that certain combinations are not well-typed, such as {lean}`0` and {name BalancedTree.branch}`branch`, because refining the second discriminant's type yields {lean}`BalancedTree α 0` which does not match the constructor's type.
:::

木の深さと木自体でマッチすると、深さのパターンに従って木の型が絞り込まれます。これは {lean}`0` と {name BalancedTree.branch}`branch` のような特定の組み合わせがうまく型付けされないことを意味します。なぜなら、2番目の判別子の型を絞り込むと {lean}`BalancedTree α 0` が生成され、コンストラクタの型と一致しないからです。

````lean (name := patfail) (error := true)
def BalancedTree.isPerfectlyBalanced (n : Nat) (t : BalancedTree α n) : Bool :=
  match n, t with
  | 0, .empty => true
  | 0, .branch left val right => isPerfectlyBalanced left && isPerfectlyBalanced right
  | _, _ => false
````
```leanOutput patfail
type mismatch
  left.branch val right
has type
  BalancedTree ?m.53 (?m.50 + 1) : Type ?u.46
but is expected to have type
  BalancedTree α 0 : Type u
```
::::
:::::

:::comment
### Pattern Equality Proofs
:::

### パターンの等価性の証明（Pattern Equality Proofs）


:::comment
When a discriminant is named, {keywordOf Lean.Parser.Term.match}`match` generates a proof that the pattern and discriminant are equal, binding it to the provided name in the {tech}[right-hand side].
This is useful to bridge the gap between dependent pattern matching on indexed families and APIs that expect explicit propositional arguments, and it can help tactics that make use of assumptions to succeed.

:::

判別子の名前が指定されると、 {keywordOf Lean.Parser.Term.match}`match` はパターンと判別子が等しいという証明を生成し、 {tech}[右辺] で指定された名前に束縛します。これは添字族に対する依存パターンマッチと明示的な命題引数を期待する API とのギャップを埋めるにあたって便利であり、仮定を利用するタクティクを成功させるために役立ちます。

:::comment
::example "Pattern Equality Proofs"
:::
::::example "パターンの等価性の証明"
:::comment
The function {lean}`last?`, which either throws an exception or returns the last element of its argument, uses the standard library function {lean}`List.getLast`.
This function expects a proof that the list in question is nonempty.
Naming the match on `xs` ensures that there's an assumption in scope that states that `xs` is equal to `_ :: _`, which {tactic}`simp_all` uses to discharge the goal.
:::

関数 {lean}`last?` は例外を投げるか、引数の最後の要素を返す関数です。これは標準ライブラリの関数 {lean}`List.getLast` を使用しています。この関数は当該リストが空でないことの証明を期待します。`xs` にマッチする名前を付けることで、`xs` が `_ :: _` に等しいことを記述する仮定がスコープに含まれることが保証されます。この仮定は {tactic}`simp_all` がゴールを達成するために使用されます。

```lean
def last? (xs : List α) : Except String α :=
  match h : xs with
  | [] =>
    .error "Can't take first element of empty list"
  | _ :: _ =>
    .ok <| xs.getLast (show xs ≠ [] by intro h'; simp_all)
```

:::comment
Without the name, {tactic}`simp_all` is unable to find the contradiction.
:::

名前がない場合、 {tactic}`simp_all` は矛盾を見つけることができません。

```lean (error := true) (name := namedHyp)
def last?' (xs : List α) : Except String α :=
  match xs with
  | [] =>
    .error "Can't take first element of empty list"
  | _ :: _ =>
    .ok <| xs.getLast (show xs ≠ [] by intro h'; simp_all)
```
```leanOutput namedHyp
simp_all made no progress
```
::::

:::comment
### Explicit Motives
:::

### 明示的な動機（Explicit Motives）


:::comment
Pattern matching is not a built-in primitive of Lean.
Instead, it is translated to applications of {tech}[recursors] via {tech}[auxiliary matching functions].
Both require a {tech}_motive_ that explains the relationship between the discriminant and the resulting type.
Generally, the {keywordOf Lean.Parser.Term.match}`match` elaborator is capable of synthesizing an appropriate motive, and the refinement of types that occurs during pattern matching is a result of the motive that was selected.
In some specialized circumstances, a different motive may be needed and may be provided explicitly using the `(motive := …)` syntax of {keywordOf Lean.Parser.Term.match}`match`.
This motive should be a function type that expects at least as many parameters as there are discriminants.
The type that results from applying a function with this type to the discriminants in order is the type of the entire {keywordOf Lean.Parser.Term.match}`match` term, and the type that results from applying a function with this type to all patterns in each alternative is the type of that alternative's {tech}[right-hand side].

:::

パターンマッチは Lean の組み込みのプリミティブではありません。これは {tech}[補助マッチ関数] を介して {tech}[再帰子] の適用に変換されます。どちらも、判別子と結果の型の関係を説明する {tech}_動機_ （motive）を必要とします。一般的に、 {keywordOf Lean.Parser.Term.match}`match` エラボレータは適切な動機を統合することができ、パターンマッチ中に発生する型の絞り込みは選択された動機の結果です。特殊な状況化では別の動機が必要になることがあり、その場合は {keywordOf Lean.Parser.Term.match}`match` の `(motive := …)` 構文を使用して明示的に提供することができます。この動機は、少なくとも識別子の数と同じ数のパラメータを必要とする関数型でなければなりません。この型を持つ関数を判別子に順番に適用した結果の型は {keywordOf Lean.Parser.Term.match}`match` 項全体の型であり、この型を持つ関数を各選択肢のすべてのパターンに適用した結果の型はその選択肢の {tech}[右辺] の型です。

:::comment
::example "Matching with an Explicit Motive"
:::
::::example "明示的な動機によるマッチ"
:::comment
An explicit motive can be used to provide type information that is otherwise unavailable from the surrounding context.
Attempting to match on a number and a proof that it is in fact {lean}`5` is an error, because there's no reason to connect the number to the proof:
:::

明示的な動機は、周囲の文脈からは得られない型情報を提供するために使用することができます。ある数字とそれが実際には {lean}`5` であるという証明のマッチを試みると、数字と証明を結び付ける推論ができないためエラーとなります：

```lean (error := true) (name := noMotive)
#eval
  match 5, rfl with
  | 5, rfl => "ok"
```
```leanOutput noMotive
invalid match-expression, pattern contains metavariables
  Eq.refl ?m.73
```
:::comment
An explicit motive explains the relationship between the discriminants:
:::

明示的な動機は、判別子の間の関係を説明します：

```lean (name := withMotive)
#eval
  match (motive := (n : Nat) → n = 5 → String) 5, rfl with
  | 5, rfl => "ok"
```
```leanOutput withMotive
"ok"
```
::::

:::comment
### Discriminant Refinement
:::

### 判別子の絞り込み（Discriminant Refinement）


:::comment
When matching on an indexed family, the indices must also be discriminants.
Otherwise, the pattern would not be well typed: it is a type error if an index is just a variable but the type of a constructor requires a more specific value.
However, a process called {deftech}[discriminant refinement] automatically adds indices as additional discriminants.

:::

添字族にマッチする場合、添字も判別子でなければなりません。一方で、パターンは正しく型付けされない可能性があります：添字が単なる変数であるにもかかわらず、コンストラクタの型がより具体的な値を必要とする場合は型エラーとなります。しかし、 {deftech}[判別子の絞り込み] （discriminant refinement）と呼ばれる処理によって自動的に添字が追加の判別子として追加されます。

:::::keepEnv
:::comment
::example "Discriminant Refinement"
:::
::::example "判別子の絞り込み"
:::comment
In the definition of {lean}`f`, the equality proof is the only discriminant.
However, equality is an indexed family, and the match is only valid when `n` is an additional discriminant.
:::

{lean}`f` の定義では、等式の証明が唯一の判別子です。しかし、等式は添字族であり、マッチは `n` が追加の判別子である場合にのみ有効です。

```lean
def f (n : Nat) (p : n = 3) : String :=
  match p with
  | rfl => "ok"
```
:::comment
Using {keywordOf Lean.Parser.Command.print}`#print` demonstrates that the additional discriminant was added automatically.
:::

{keywordOf Lean.Parser.Command.print}`#print` を使用することで、追加の判別子が自動的に追加されたことを確認できます。

```lean (name := fDef)
#print f
```
```leanOutput fDef
def f : (n : Nat) → n = 3 → String :=
fun n p =>
  match 3, p with
  | .(n), ⋯ => "ok"
```
::::
:::::

:::comment
### Generalization
:::

### 一般化（Generalization）

%%%
tag := "match-generalization"
%%%

:::comment
The pattern match elaborator automatically determines the motive by finding occurrences of the discriminants in the expected type, generalizing them in the types of subsequent discriminants so that the appropriate pattern can be substituted.
Additionally, occurrences of the discriminants in the types of variables in the context are generalized and substituted by default.
This latter behavior can be turned off by passing the `(generalizing := false)` flag to {keywordOf Lean.Parser.Term.match}`match`.

:::

パターンマッチのエラボレータは、適切なパターンを代入できるように、期待される型で判別子の出現を見つけ、後続の判別子の型でそれらを一般化することによって動機を自動的に決定します。さらに、コンテキスト中の変数の型に判別子が出現した場合は、デフォルトで一般化・置換されます。この後者の動作は {keywordOf Lean.Parser.Term.match}`match` にフラグ `(generalizing := false)` を渡すことでオフにすることができます。

:::::keepEnv
:::comment
::example "Matching, With and Without Generalization"
:::
::::example "一般化の有無によるマッチ"
```lean (show := false)
variable {α : Type u} (b : Bool) (ifTrue : b = true → α) (ifFalse : b = false → α)
```
:::comment
In this definition of {lean}`boolCases`, the assumption {lean}`b` is generalized in the type of `h` and then replaced with the actual pattern.
This means that {lean}`ifTrue` and {lean}`ifFalse` have the types {lean}`true = true → α` and {lean}`false = false → α` in their respective cases, but `h`'s type mentions the original discriminant.

:::

この {lean}`boolCases` の定義では、仮定 {lean}`b` は `h` の型で一般化され、実際のパターンに置き換えられます。つまり、 {lean}`ifTrue` と {lean}`ifFalse` はそれぞれのケースで {lean}`true = true → α` と {lean}`false = false → α` の型を持ちますが、`h` の型はもとの判別子に言及しています。

```lean (error := true) (name := boolCases1) (keep := false)
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α :=
  match h : b with
  | true  => ifTrue h
  | false => ifFalse h
```
:::comment
The error for the first case is typical of both:
:::

最初のケースのエラーが両者に典型的なものです：

```leanOutput boolCases1
application type mismatch
  ifTrue h
argument
  h
has type
  b = true : Prop
but is expected to have type
  true = true : Prop
```
:::comment
Turning off generalization allows type checking to succeed, because {lean}`b` remains in the types of {lean}`ifTrue` and {lean}`ifFalse`.
:::

一般化をオフにすると {lean}`b` は {lean}`ifTrue` と {lean}`ifFalse` の型のままであるため、型チェックが成功します。

```lean
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α :=
  match (generalizing := false) h : b with
  | true  => ifTrue h
  | false => ifFalse h
```
:::comment
In the generalized version, {name}`rfl` could have been used as the proof arguments as an alternative.
:::

一般化されたバージョンでは、選択肢として {name}`rfl` を証明引数として使うこともできます。

::::
:::::

:::comment
## Custom Pattern Functions
:::

## カスタムのパターン関数（Custom Pattern Functions）

%%%
tag := "match_pattern-functions"
%%%

```lean (show := false)
section
variable {n : Nat}
```

:::comment
In patterns, defined constants with the {attr}`match_pattern` attribute are unfolded and normalized rather than rejected.
This allows a more convenient syntax to be used for many patterns.
In the standard library, {name}`Nat.add`, {name}`HAdd.hAdd`, {name}`Add.add`, and {name}`Neg.neg` all have this attribute, which allows patterns like {lean}`n + 1` instead of {lean}`Nat.succ n`.
Similarly, {name}`Unit` and {name}`Unit.unit` are definitions that set the respective {tech}[universe parameters] of {name}`PUnit` and {name}`PUnit.unit` to 0; the {attr}`match_pattern` attribute on {name}`Unit.unit` allows it to be used in patterns, where it expands to {lean}`PUnit.unit.{0}`.

:::

パターンでは、 {attr}`match_pattern` 属性で定義された定数は拒否されずに展開・正規化されます。これにより、多くのパターンでより便利な構文を使用することができます。標準ライブラリでは、 {name}`Nat.add` ・ {name}`HAdd.hAdd` ・ {name}`Add.add` ・ {name}`Neg.neg` はすべてこの属性を持っており、 {lean}`Nat.succ n` の代わりに {lean}`n + 1` のようなパターンを使用できます。同様に、 {name}`Unit` と {name}`Unit.unit` は {name}`PUnit` と {name}`PUnit.unit` のそれぞれの {tech}[宇宙パラメータ] を0に設定したものに対する定義です； {name}`Unit.unit` の {attr}`match_pattern` 属性により、 {lean}`PUnit.unit.{0}` に展開されるパターンで使用することができます。

::::syntax attr (title := "Attribute for Match Patterns")
:::comment
The {attr}`match_pattern` attribute indicates that a definition should be unfolded, rather than rejected, in a pattern.
:::

{attr}`match_pattern` 属性は、定義がパターンで拒否されるのではなく、展開されるべきであることを示します。

```grammar
match_pattern
```
::::

:::::keepEnv
```lean (show := false)
section
variable {k : Nat}
```
:::comment
::example "Match Patterns Follow Reduction"
:::
::::example "マッチパターンが簡約に従う"
:::comment
The following function can't be compiled:
:::

次の関数はコンパイルできません：

```lean (error := true) (name := nonPat)
def nonzero (n : Nat) : Bool :=
  match n with
  | 0 => false
  | 1 + k => true
```
:::comment
The error message on the pattern `1 + _` is:
:::

パターン `1 + _` に対するエラーメッセージは次の通りです：

```leanOutput nonPat
invalid patterns, `k` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching
  .(Nat.add 1 k)
```

:::comment
This is because {name}`Nat.add` is defined by recursion on its second parameter, equivalently to:
:::

これは、 {name}`Nat.add` が2番目のパラメータに対して再帰的に定義されているからです：

```lean
def add : Nat → Nat → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
```

:::comment
No {tech}[ι-reduction] is possible, because the value being matched is a variable, not a constructor.
{lean}`1 + k` gets stuck as {lean}`Nat.add 1 k`, which is not a valid pattern.

:::

マッチする値はコンストラクタではなく変数であるため、 {tech}[ι簡約] はできません。 {lean}`1 + k` は {lean}`Nat.add 1 k` という有効でないパターンとして引っかかります。

:::comment
In the case of {lean}`k + 1`, that is, {lean}`Nat.add k (.succ .zero)`, the second pattern matches, so it reduces to {lean}`Nat.succ (Nat.add k .zero)`.
The second pattern now matches, yielding {lean}`Nat.succ k`, which is a valid pattern.
:::

{lean}`k + 1` の場合、つまり {lean}`Nat.add k (.succ .zero)` の場合、2番目のパターンがマッチするため、 {lean}`Nat.succ (Nat.add k .zero)` に簡約されます。再度2番目のパターンがマッチし、有効なパターン {lean}`Nat.succ k` が得られます。

::::
````lean (show := false)
end
````

:::::


```lean (show := false)
end
```


:::comment
## Pattern Matching Functions
:::

## パターンマッチ関数（Pattern Matching Functions）

%%%
tag := "pattern-fun"
%%%

::::syntax term
:::comment
Functions may be specified via pattern matching by writing a sequence of patterns after {keywordOf Lean.Parser.Term.fun}`fun`, each preceded by a vertical bar (`|`).
:::

関数は {keywordOf Lean.Parser.Term.fun}`fun` の後に縦棒（`|`）で始まる一連のパターンを書くことで、パターンマッチとして指定をすることができます。

```grammar
fun
  $[| $pat,* => $term]*
```
:::comment
This desugars to a function that immediately pattern-matches on its arguments.
:::

これは引数を即座にパターンマッチする関数に脱糖されます。

::::

:::::keepEnv
:::comment
::example "Pattern-Matching Functions"
:::
::::example "パターンマッチ関数"
:::comment
{lean}`isZero` is defined using a pattern-matching function abstraction, while {lean}`isZero'` is defined using a pattern match expression:
:::

{lean}`isZero` はパターンマッチ関数抽象を使って定義される一方、 {lean}`isZero'` はパターンマッチ式を使って定義されています：

```lean
def isZero : Nat → Bool :=
  fun
    | 0 => true
    | _ => false

def isZero' : Nat → Bool :=
  fun n =>
    match n with
    | 0 => true
    | _ => false
```
:::comment
Because the former is syntactic sugar for the latter, they are definitionally equal:
:::

前者は後者のための構文糖衣であるため、定義上等価です：

```lean
example : isZero = isZero' := rfl
```
:::comment
The desugaring is visible in the output of {keywordOf Lean.Parser.Command.print}`#print`:
:::

脱糖は {keywordOf Lean.Parser.Command.print}`#print` の出力で見ることができます：

```lean (name := isZero)
#print isZero
```
:::comment
outputs
:::

上記は以下を出力し、

```leanOutput isZero
def isZero : Nat → Bool :=
fun x =>
  match x with
  | 0 => true
  | x => false
```
:::comment
while
:::

一方で、

```lean (name := isZero')
#print isZero'
```
:::comment
outputs
:::

上記は以下を出力します。

```leanOutput isZero'
def isZero' : Nat → Bool :=
fun n =>
  match n with
  | 0 => true
  | x => false
```
::::
:::::

:::comment
## Other Pattern Matching Operators
:::

## その他のパターンマッチ演算子（Other Pattern Matching Operators）


:::comment
In addition to {keywordOf Lean.Parser.Term.match}`match` and {keywordOf termIfLet}`if let`, there are a few other operators that perform pattern matching.

:::

{keywordOf Lean.Parser.Term.match}`match` と {keywordOf termIfLet}`if let` に加え、パターンマッチを行う演算子がいくつかあります。

::::syntax term
:::comment
The {keywordOf Lean.«term_Matches_|»}`matches` operator returns {lean}`true` if the term on the left matches the pattern on the right.
:::

{keywordOf Lean.«term_Matches_|»}`matches` 演算子は左側の項が右側の項にマッチする場合に {lean}`true` を返します。

```grammar
$e matches $e
```
::::

:::comment
When branching on the result of {keywordOf Lean.«term_Matches_|»}`matches`, it's usually better to use {keywordOf termIfLet}`if let`, which can bind pattern variables in addition to checking whether a pattern matches.

:::

{keywordOf Lean.«term_Matches_|»}`matches` の結果で分岐するような場合、通常は {keywordOf termIfLet}`if let` を使う方が良いです。こちらではパターンがマッチしたかどうかに加え、パターン変数を束縛することができます。

```lean (show := false)
/--
info: match 4 with
| n.succ => true
| x => false : Bool
-/
#guard_msgs in
#check 4 matches (n + 1)
```

:::comment
If there are no constructor patterns that could match a discriminant or sequence of discriminants, then the code in question is unreachable, as there must be a false assumption in the local context.
The {keywordOf Lean.Parser.Term.nomatch}`nomatch` expression is a match with zero cases that can have any type whatsoever, so long as there are no possible cases that could match the discriminants.

:::

判別子または判別子の列にマッチするコンストラクタのパターンが無い場合、ローカルコンテキストに誤った仮定が存在するはずであるため、問題のコードは到達不可能です。 {keywordOf Lean.Parser.Term.nomatch}`nomatch` 式は、判別子にマッチする可能性のあるケースが存在しない限り、任意の型を持つことができるゼロケースとのマッチです。

:::syntax term (title := "Caseless Pattern Matches")
```grammar
nomatch $e,*
```
:::

:::::keepEnv
:::comment
::example "Inconsistent Indices"
:::
::::example "一貫性のない添字"
:::comment
There are no constructor patterns that can match both proofs in this example:
:::

この例では、両方の証明にマッチするコンストラクタのパターンはありません：

```lean
example (p1 : x = "Hello") (p2 : x = "world") : False :=
  nomatch p1, p2
```

:::comment
This is because they separately refine the value of `x` to unequal strings.
Thus, the {keywordOf Lean.Parser.Term.nomatch}`nomatch` operator allows the example's body to prove {lean}`False` (or any other proposition or type).
:::

これは `x` の値を別々に等しくない文字列に絞り込むためです。したがって、 {keywordOf Lean.Parser.Term.nomatch}`nomatch` 演算子によって、この例の本体は {lean}`False` （またはその他の命題や型）を証明することができます。

::::
:::::

:::comment
When the expected type is a function type, {keywordOf Lean.Parser.Term.nofun}`nofun` is shorthand for a function that takes as many parameters as the type indicates in which the body is {keywordOf Lean.Parser.Term.nomatch}`nomatch` applied to all of the parameters.
:::

期待される型が関数型である場合、 {keywordOf Lean.Parser.Term.nofun}`nofun` はその型が示す数だけパラメータを取る関数の省略形であり、その関数の本体は全てのパラメータに適用された {keywordOf Lean.Parser.Term.nomatch}`nomatch` です。

:::syntax term (title := "Caseless Functions")
```grammar
nofun
```
:::

:::::keepEnv
:::comment
::example "Impossible Functions"
:::
::::example "不可能な関数"
:::comment
Instead of introducing arguments for both equality proofs and then using both in a {keywordOf Lean.Parser.Term.nomatch}`nomatch`, it is possible to use {keywordOf Lean.Parser.Term.nofun}`nofun`.
:::

両方の等式証明の引数を導入し、 {keywordOf Lean.Parser.Term.nomatch}`nomatch` で両方を使用する代わりに、 {keywordOf Lean.Parser.Term.nofun}`nofun` を使用することができます。

```lean
example : x = "Hello" → x = "world" → False := nofun
```
::::
:::::

## Elaborating Pattern Matching
%%%
tag := "pattern-match-elaboration"
%%%

:::planned 209
Specify the elaboration of pattern matching to {deftech}[auxiliary match functions].
:::

:::comment
# Holes
:::

# ホール（Holes）


:::comment
A {deftech}_hole_ or {deftech}_placeholder term_ is a term that indicates the absence of instructions to the elaborator.{index}[placeholder term]{index subterm:="placeholder"}[term]
In terms, holes can be automatically filled when the surrounding context would only allow one type-correct term to be written where the hole is.
Otherwise, a hole is an error.
In patterns, holes represent universal patterns that can match anything.


:::

{deftech}_ホール_ （hole）または {deftech}_プレースホルダ項_ （placeholder term）はエラボレータに対する支持がないことを示す項です。 {index}[placeholder term]{index subterm:="placeholder"}[term] 項において、ホールは周囲のコンテキストがホールのある場所に対して、1つの正しい型の項を書くことしか許されない場合に、自動的に埋めることができます。そうでない場合、ホールはエラーになります。パターンでは、ホールは何にでもマッチするユニバーサルパターンを表します。

::::syntax term (title := "Holes")
:::comment
Holes are written with underscores.
:::

ホールはアンダースコアで記述されます。

```grammar
_
```
::::

:::::keepEnv
:::comment
::example "Filling Holes with Unification"
:::
::::example "単一化によるホール埋め"
:::comment
The function {lean}`the` can be used similarly to {keywordOf Lean.Parser.Term.show}`show` or a {tech}[type ascription].
:::

関数 {lean}`the` は {keywordOf Lean.Parser.Term.show}`show` もしくは {tech}[type ascription] と同じように使うことができます。

```lean
def the (α : Sort u) (x : α) : α := x
```
:::comment
If the second parameter's type can be inferred, then the first parameter can be a hole.
Both of these commands are equivalent:
:::

2番目のパラメータの型が推測できる場合、第1パラメータはホールにすることができます。これらのコマンドはどちらも同等です：

```lean
#check the String "Hello!"

#check the _ "Hello"
```
::::
:::::


:::comment
When writing proofs, it can be convenient to explicitly introduce unknown values.
This is done via {deftech}_synthetic holes_, which are never solved by unification and may occur in multiple positions.
They are primarily useful in tactic proofs, and are described in {ref "metavariables-in-proofs"}[the section on metavariables in proofs].

:::

証明を書く際、未知の値を明示的に導入すると便利なことがあります。これは {deftech}_統合的ホール_ （synthetic hole）によって行われ、単一化によって解決されることはなく、複数の位置で出現させることができます。これは主にタクティク証明で有用であり、 {ref "metavariables-in-proofs"}[証明中のメタ変数についての節] で説明されています。

:::syntax term (title := "Synthetic Holes")
```grammar
?$x:ident
```
```grammar
?_
```
:::

# Type Ascription

:::comment
{deftech}_Type ascriptions_ explicitly annotate terms with their types.
They are a way to provide Lean with the expected type for a term.
This type must be definitionally equal to the type that is expected based on the term's context.
Type ascriptions are useful for more than just documenting a program:
 * There may not be sufficient information in the program text to derive a type for a term. Ascriptions are one way to provide the type.
 * An inferred type may not be the one that was desired for a term.
 * The expected type of a term is used to drive the insertion of {tech}[coercions], and ascriptions are one way to control where coercions are inserted.

:::

{deftech}_Type ascriptions_ は項の型を明示的に注釈します。これは Lean に対して、項に期待される型を提供する方法です。この型は定義上、項の文脈から予想される型と等しくなければなりません。type ascription は単にプログラムを文書化する以外にも役立ちます：
 * プログラムのテキストには、項の型を導くのに十分な情報がない場合があります。ascription はそのような型を提供する方法の1つです。
 * 推論された型は項に望まれた型ではないかもしれません。
 * 項の期待される型は {tech}[coercions] の挿入を推進するために使用され、ascription はどこに強制が挿入されるかを制御する方法の1つです。

::::syntax term (title := "Postfix Type Ascriptions")
:::comment
Type ascriptions must be surrounded by parentheses.
They indicate that the first term's type is the second term.
:::

Type ascriptions はカッコで囲まなければなりません。これは最初の項の型が2番目の項であることを示します。

```grammar
($_ : $_)
```
::::


:::comment
In cases where the term that requires a type ascription is long, such as a tactic proof or a {keywordOf Lean.Parser.Term.do}`do` block, the postfix type ascription with its mandatory parentheses can be difficult to read.
Additionally, for both proofs and {keywordOf Lean.Parser.Term.do}`do` blocks, the term's type is essential to its interpretation.
In these cases, the prefix versions can be easier to read.
:::

タクティク証明や {keywordOf Lean.Parser.Term.do}`do` ブロックのように、type ascription を必要とする項が長い場合、必須の括弧を持ち後置される type ascription は読みにくい場合があります。さらに、証明と {keywordOf Lean.Parser.Term.do}`do` ブロックの両方で項の型はその解釈に不可欠です。このような場合、前置する方が読みやすくなります。

::::syntax term (title := "Prefix Type Ascriptions")
```grammar
show $_ from $_
```
:::comment
When the term in the body of {keywordOf Lean.Parser.Term.show}`show` is a proof, the keyword {keywordOf Lean.Parser.Term.show}`from` may be omitted.
:::

{keywordOf Lean.Parser.Term.show}`show` の本体中の項が証明である場合、 {keywordOf Lean.Parser.Term.show}`from` は省略することができます。

```grammar
show $_ by $_
```
::::

:::comment
::example "Ascribing Statements to Proofs"
:::
::::example "証明に対する ascription 文"
:::comment
This example is unable to execute the tactic proof because the desired proposition is not known.
As part of running the earlier tactics, the proposition is automatically refined to be one that the tactics could prove.
However, their default cases fill it out incorrectly, leading to a proof that fails.
:::

この例では、目的の命題がわからないため、タクティクによる証明を実行できません。先に実行されたタクティクによって、命題はタクティクが証明できるものに自動的に絞り込まれます。しかし、デフォルトのケースはそれを間違って埋めてしまい、証明は失敗します。

```lean (name := byBusted) (error := true)
example (n : Nat) := by
  induction n
  next => rfl
  next n' ih =>
    simp only [HAdd.hAdd, Add.add, Nat.add] at *
    rewrite [ih]
    rfl
```
```leanOutput byBusted
tactic 'rewrite' failed, equality or iff proof expected
  HEq 0 n'
n' : Nat
ih : HEq 0 n'
⊢ HEq 0 n'.succ
```

:::comment
A prefix type ascription with {keywordOf Lean.Parser.Term.show}`show` can be used to provide the proposition being proved.
This can be useful in syntactic contexts where adding it as a local definition would be inconvenient.
:::

{keywordOf Lean.Parser.Term.show}`show` による前置された ascription を、証明される命題を提供するために使用できます。これはローカル定義として追加すると不便な構文コンテキストで役立ちます。

```lean
example (n : Nat) := show 0 + n = n by
  induction n
  next => rfl
  next n' ih =>
    simp only [HAdd.hAdd, Add.add, Nat.add] at *
    rewrite [ih]
    rfl
```
::::

:::comment
::example "Ascribing Types to {keywordOf Lean.Parser.Term.do}`do` Blocks"
:::
::::example "{keywordOf Lean.Parser.Term.do}`do` ブロックに対する type ascription"
:::comment
This example lacks sufficient type information to synthesize the {name}`Pure` instance.
:::

この例では、 {name}`Pure` インスタンスを統合するのに十分な型情報がありません。

```lean (name := doBusted) (error := true)
example := do
  return 5
```
```leanOutput doBusted
typeclass instance problem is stuck, it is often due to metavariables
  Pure ?m.75
```

:::comment
A prefix type ascription with {keywordOf Lean.Parser.Term.show}`show`, together with a {tech}[hole], can be used to indicate the monad.
The {tech key:="default instance"}[default] {lean}`OfNat _ 5` instance provides enough type information to fill the hole with {lean}`Nat`.
:::

{keywordOf Lean.Parser.Term.show}`show` による前置された ascription と {tech}[ホール] を併用することで、モナドを示すことができます。 {tech key:="デフォルトインスタンス"}[デフォルトの] {lean}`OfNat _ 5` インスタンスは、 {lean}`Nat` でホールを埋めるのに十分な型情報を提供します。

```lean
example := show StateM String _ from do
  return 5
```
::::

:::comment
# Quotation and Antiquotation
:::

# Quotation と Antiquotation（Quotation and Antiquotation）


:::comment
Quotation terms are described in the {ref "quotation"}[section on quotation].

:::

quotation の項は {ref "quotation"}[quotation の節] で説明されています。

:::comment
# `do`-Notation
:::

# `do` 記法（`do`-Notation）


:::comment
{keywordOf Lean.Parser.Term.do}`do`-notation is described {ref "do-notation"}[in the chapter on monads.]

:::

{keywordOf Lean.Parser.Term.do}`do` 記法は {ref "do-notation"}[モナドの章] で説明されています。

:::comment
# Proofs
:::

# 証明（Proofs）


:::comment
The syntax for invoking tactics ({keywordOf Lean.Parser.Term.byTactic}`by`) is described in {ref "by"}[the section on proofs].

:::

タクティクを呼び出す構文（ {keywordOf Lean.Parser.Term.byTactic}`by` ）は {ref "by"}[証明の節] で説明されています。
