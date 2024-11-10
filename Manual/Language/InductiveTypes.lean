/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Language.InductiveTypes.LogicalModel
import Manual.Language.InductiveTypes.Structures

open Verso.Genre Manual

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

set_option maxRecDepth 800

/-
#doc (Manual) "Inductive Types" =>
-/
#doc (Manual) "帰納型" =>
%%%
tag := "inductive-types"
%%%


:::comment
{deftech}_Inductive types_ are the primary means of introducing new types to Lean.
While {tech}[universes] and {tech}[functions] are built-in primitives that could not be added by users, every other type in Lean is either an inductive type or defined in terms of universes, functions, and inductive types.
Inductive types are specified by their {deftech}_type constructors_ {index}[type constructor] and their {deftech}_constructors_; {index}[constructor] their other properties are derived from these.
Each inductive type has a single type constructor, which may take both {tech}[universe parameters] and ordinary parameters.
Inductive types may have any number of constructors; these constructors introduce new values whose types are headed by the inductive type's type constructor.

:::

{deftech}_帰納型_ （inductive type）は Lean に新しい型を導入する主な手段です。 {tech}[universes] と {tech}[関数] は組み込みのプリミティブでユーザが追加することはできませんが、Lean の他のすべての型は帰納型であるか、宇宙・関数・帰納型によって定義されたものであるかのどちらかです。帰納型は {deftech}_型コンストラクタ_ （type constructor）{index}[type constructor] と {deftech}_コンストラクタ_ （constructor） {index}[constructor] によって指定されます；帰納型の性質はこれらから導かれます。各帰納型は1つの型コンストラクタを持ち、 {tech}[universe parameters] と通常のパラメータの両方を取ることができます。帰納型は任意の数のコンストラクタを持つことができます；これらのコンストラクタは帰納型の型コンストラクタによって型が導かれる新しい値を導入します。

:::comment
Based on the type constructor and the constructors for an inductive type, Lean derives a {deftech}_recursor_{index}[recursor]{see "recursor"}[eliminator].
Logically, recursors represent induction principles or elimination rules; computationally, they represent primitive recursive computations.
The termination of recursive functions is justified by translating them into uses of the recursors, so Lean's kernel only needs to perform type checking of recursor applications, rather than including a separate termination analysis.
Lean additionally produces a number of helper constructions based on the recursor,{margin}[The term _recursor_ is always used, even for non-recursive types.] which are used elsewhere in the system.


:::

帰納型の型コンストラクタとコンストラクタに基づいて、Lean は {deftech}_再帰子_{index}[recursor]{see "recursor"}[eliminator] （recursor）を導出します。論理的には、再帰子は帰納原理や除去則を表し、計算上はプリミティブな再帰計算を表します。再帰関数の停止は、再帰子の使用に変換することで正当化されるため、Lean のカーネルは再帰子の適用の型チェックを行うだけでよく、停止性の分析を別途行う必要はありません。Lean はさらに、システムの他の場所でも使用される再帰子 {margin}[_再帰子_ という用語は再帰的でないデータ型でも常に使用されます。] に基づいた数多くの補助的な構成を提供しています。

:::comment
_Structures_ are a special case of inductive types that have exactly one constructor.
When a structure is declared, Lean generates helpers that enable additional language features to be used with the new structure.

:::

_構造体_ （structure）はコンストラクタを1つだけ持つ帰納型の特殊なケースです。構造体が宣言されると、Lean は新しい構造体で追加の言語機能を使用できるようにする補助関数を生成します。

:::comment
This section describes the specific details of the syntax used to specify both inductive types and structures, the new constants and definitions in the environment that result from inductive type declarations, and the run-time representation of inductive types' values in compiled code.

:::

本節では、帰納型と構造体の両方を指定するために使用される構文の具体的な詳細・帰納型の宣言から生じる環境内の新しい定数と定義・コンパイルされたコードにおける帰納型の値のランタイム表現について説明します。

:::comment
# Inductive Type Declarations
%%%
tag := "inductive-declarations"
%%%

:::

# 帰納型の宣言

::::syntax command (alias := «inductive»)
```grammar
$_:declModifiers
inductive $d:declId $_:optDeclSig where
  $[| $_ $c:ident $_]*
$[deriving $[$x:ident],*]?
```

:::comment
Declares a new inductive type.
The meaning of the {syntaxKind}`declModifiers` is as described in the section {ref "declaration-modifiers"}[on declaration modifiers].
:::

新しい帰納型を宣言します。 {syntaxKind}`declModifiers` の意味は {ref "declaration-modifiers"}[宣言修飾子について] の節で説明した通りです。

::::

:::comment
After declaring an inductive type, its type constructor, constructors, and recursor are present in the environment.
New inductive types extend Lean's core logic—they are not encoded or represented by some other already-present data.
Inductive type declarations must satisfy {ref "well-formed-inductives"}[a number of well-formedness requirements] to ensure that the logic remains consistent.

:::

帰納型を宣言すると、その型コンストラクタ・コンストラクタ・再帰子が環境に現れます。新しい帰納型は Lean のコア論理を拡張します。それらは既に存在する他のデータによってエンコードされたり表現されたりすることはありません。帰納型の宣言は、論理の一貫性を保つために {ref "well-formed-inductives"}[多くの適格な要件] を満たす必要があります。

:::comment
The first line of the declaration, from {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`inductive` to {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where`, specifies the new {tech}[type constructor]'s name and type.
If a type signature for the type constructor is provided, then its result type must be a {tech}[universe], but the parameters do not need to be types.
If no signature is provided, then Lean will attempt to infer a universe that's just big enough to contain the resulting type.
In some situations, this process may fail to find a minimal universe or fail to find one at all, necessitating an annotation.

:::

宣言の最初の行にて、 {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`inductive` から {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where` までは新しい {tech}[型コンストラクタ] の名前と型を指定しています。型コンストラクタの型シグネチャが提供されている場合、その結果の型は {tech}[universe] でなければなりませんが、パラメータは型である必要はありません。シグネチャが提供されない場合、Lean は結果の型を含むのに十分な大きさの宇宙を推論しようとします。状況によってはこのプロセスは最小の宇宙を見つけることができなかったり、全く見つけることができなかったりすることがあり、その場合は注釈が必要です。

:::comment
The constructor specifications follow {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where`.
Constructors are not mandatory, as constructorless inductive types such as {lean}`False` and {lean}`Empty` are perfectly sensible.
Each constructor specification begins with a vertical bar (`'|'`, Unicode `'VERTICAL BAR' (U+007c)`), declaration modifiers, and a name.
The name is a {tech}[raw identifier].
A declaration signature follows the name.
The signature may specify any parameters, modulo the well-formedness requirements for inductive type declarations, but the return type in the signature must be a saturated application of the type constructor of the inductive type being specified.
If no signature is provided, then the constructor's type is inferred by inserting sufficient implicit parameters to construct a well-formed return type.

:::

コンストラクタの仕様は {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where` の後に続きます。コンストラクタは必須ではありません。コンストラクタのないデータ型としては {lean}`False` と {lean}`Empty` などがまさに当てはまります。各コンストラクタの指定は、縦棒（`'|'`、Unicode `'VERTICAL BAR' (U+007c)`）・宣言修飾子・名前で始まります。名前は {tech}[生識別子] です。宣言シグネチャは名前の後に続きます。シグネチャは帰納的宣言の適格要件に従って任意のパラメータを指定することができますが、シグネチャの戻り型は指定された帰納型の型コンストラクタを完全に適用したものでなければなりません。シグネチャが提供されない場合、コンストラクタの型は適格な戻り値を構成するのに十分な暗黙のパラメータを挿入することによって推測されます。

:::comment
The new inductive type's name is defined in the {tech}[current namespace].
Each constructor's name is in the inductive type's namespace.{index subterm:="of inductive type"}[namespace]

:::

新しい帰納型の名前は {tech}[current namespace] で定義されます。各コンストラクタの名前は帰納型の名前空間にあります。 {index subterm:="of inductive type"}[namespace]

:::comment
## Parameters and Indices
%%%
tag := "inductive-datatypes-parameters-and-indices"
%%%

:::

## パラメータと添字

:::comment
Type constructors may take two kinds of arguments: {deftech}_parameters_ {index subterm:="of inductive type"}[parameter] and {deftech key:="index"}_indices_.{index subterm:="of inductive type"}[index]
Parameters must be used consistently in the entire definition; all occurrences of the type constructor in each constructor in the declaration must take precisely the same argument.
Indices may vary among the occurrences of the type constructor.
All parameters must precede all indices in the type constructor's signature.

:::

型コンストラクタは2種類の引数を取ることができます： {deftech}_パラメータ_ {index subterm:="of inductive type"}[parameter] （parameter）と {deftech key:="index"}_添字_ {index subterm:="of inductive type"}[index] （index, indices）です。パラメータは定義全体で一貫して使用されなければなりません；宣言内の各コンストラクタで型コンストラクタが出現する場合は、すべて正確に同じ引数を取る必要があります。添字は型コンストラクタの出現箇所によって異なっていてもかまいません。すべてのパラメータは、型コンストラクタのシグネチャのすべての添字の前にいなければなりません。

:::comment
Parameters that occur prior to the colon (`':'`) in the type constructor's signature are considered parameters to the entire inductive type declaration.
They are always parameters that must be uniform throughout the type's definition.
Generally speaking, parameters that occur after the colon are indices that may vary throughout the definition of the type.
However, if the option {option}`inductive.autoPromoteIndices` is {lean}`true`, then syntactic indices that could have been parameters are made into parameters.
An index could have been a parameter if all of its type dependencies are themselves parameters and it is used uniformly as an uninstantiated variable in all occurrences of the inductive type's type constructor in all constructors.

:::

型コンストラクタのシグネチャのコロン（`':'`）より前に現れるパラメータは帰納型宣言全体に対するパラメータと見なされます。これらは常に型の定義全体を通して一様でなければならないパラメータです。一般的に言えば、コロンの後にあるパラメータは型の定義全体を通して変化する可能性のある添字です。しかし、オプション {option}`inductive.autoPromoteIndices` が {lean}`true` の場合、パラメータになる可能性のある構文としては添字のものがパラメータになります。添字がパラメータである可能性があるのは、その型の依存関係がすべてパラメータであり、帰納型の型コンストラクタのすべてのコンストラクタで一律にインスタンス化されていない変数として使用される場合です。

{optionDocs inductive.autoPromoteIndices}

:::comment
Indices can be seen as defining a _family_ of types.
Each choice of indices selects a type from the family, which has its own set of available constructors.
Type constructors with indices are said to specify {deftech}_indexed families_ {index subterm:="of types"}[indexed family] of types.

:::

添字は型の _族_ （family）を定義していると見なすことができます。添字を選択するごとに、その族から型が選択され、その型は使用可能なコンストラクタのあつまりを持ちます。添字のパラメータを取る型のコンストラクタは {deftech}_添字族_ {index subterm:="of types"}[indexed family] （indexed family）と呼ばれます、

:::comment
## Example Inductive Types
:::

## 帰納型の例
%%%
tag := "example-inductive-types"
%%%


:::comment
::example "A constructorless type"
:::
::::example "コンストラクタの無い型"
:::comment
{lean}`Vacant` is an empty inductive type, equivalent to Lean's {lean}`Empty` type:
:::

{lean}`Vacant` は空の帰納型であり、Lean の {lean}`Empty` 型と同値です：

```lean
inductive Vacant : Type where
```

:::comment
Empty inductive types are not useless; they can be used to indicate unreachable code.
:::

空の帰納型は無用なものではありません；到達不可能なコードを示すために使うことができます。

::::

:::comment
::example "A constructorless proposition"
:::
::::example "コンストラクタの無い命題"
:::comment
{lean}`No` is a false {tech}[proposition], equivalent to Lean's {lean}`False`:
:::

{lean}`No` は偽の {tech}[proposition] であり、Lean の {lean}`False` と同値です：

```lean
inductive No : Prop where
```

```lean (show := false) (keep := false)
theorem no_is_false : No = False := by
  apply propext
  constructor <;> intro h <;> cases h
```
::::

:::comment
::example "A unit type" (keep := true)
:::
::::example "ユニット型" (keep := true)
:::comment
{lean}`One` is equivalent to Lean's {lean}`Unit` type:
:::

{lean}`One` は Lean の {lean}`Unit` 型と同値です：

```lean
inductive One where
  | one
```
:::comment
It is an example of an inductive type in which the signatures have been omitted for both the type constructor and the constructor.
Lean assigns {lean}`One` to {lean}`Type`:
:::

これは型コンストラクタとコンストラクタの両方のシグネチャが省略された帰納型の例です。Lean は {lean}`One` を {lean}`Type` に割り当てます：

```lean (name := OneTy)
#check One
```
```leanOutput OneTy
One : Type
```
:::comment
The constructor is named {lean}`One.one`, because constructor names are the type constructor's namespace.
Because {lean}`One` expects no arguments, the signature inferred for {lean}`One.one` is:
:::

コンストラクタ名は型コンストラクタの名前空間にあるため、コンストラクタ名は {lean}`One.one` です。 {lean}`One` は引数を期待しないため、 {lean}`One.one` のシグネチャは次のようになります：

```lean (name := oneTy)
#check One.one
```
```leanOutput oneTy
One.one : One
```
::::


:::comment
::example "A true proposition"
:::
::::example "真である命題"
:::comment
{lean}`Yes` is equivalent to Lean's {lean}`True` proposition:

:::

{lean}`Yes` は Lean の {lean}`True` 命題と同値です：

```lean
inductive Yes : Prop where
  | intro
```
:::comment
Unlike {lean}`One`, the new inductive type {lean}`Yes` is specified to be in the {lean}`Prop` universe.
:::

{lean}`One` と異なり、この新しい帰納型 {lean}`Yes` は {lean}`Prop` 宇宙にあることが指定されています。

```lean (name := YesTy)
#check Yes
```
```leanOutput YesTy
Yes : Prop
```
:::comment
The signature inferred for {lean}`Yes.intro` is:
:::

{lean}`Yes.intro` のシグネチャは以下のように推測されます：

```lean (name := yesTy)
#check Yes.intro
```
```leanOutput yesTy
Yes.intro : Yes
```

```lean (show := false) (keep := false)
theorem yes_is_true : Yes = True := by
  apply propext
  constructor <;> intros <;> constructor
```
::::

:::comment
::example "A type with parameter and index" (keep := true)
:::
:::::example "パラメータと添字のある型" (keep := true)

::::keepEnv
```lean (show:=false)
universe u
axiom α : Type u
axiom b : Bool
```

:::comment
An {lean}`EvenOddList α b` is a list where {lean}`α` is the type of the data stored in the list and {lean}`b` is {lean}`true` when there are an even number of entries:
:::

{lean}`EvenOddList α b` はリストで、 {lean}`α` はリストに格納されているデータの型、 {lean}`b` はエントリの数が偶数の時に {lean}`true` となります：

::::

```lean
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
```

:::comment
This example is well typed because there are two entries in the list:
:::

この例では、リストに2つのエントリがあるため、正しく型付けられています：

```lean
example : EvenOddList String true :=
  .cons "a" (.cons "b" .nil)
```

:::comment
This example is not well typed because there are three entries in the list:
:::

この例では、リストに3つのエントリがあるため、型付けは正しくありません：

```lean (error := true) (name := evenOddOops)
example : EvenOddList String true :=
  .cons "a" (.cons "b" (.cons "c" .nil))
```
```leanOutput evenOddOops
type mismatch
  EvenOddList.cons "a" (EvenOddList.cons "b" (EvenOddList.cons "c" EvenOddList.nil))
has type
  EvenOddList String !!!true : Type
but is expected to have type
  EvenOddList String true : Type
```

::::keepEnv
```lean (show:=false)
universe u
axiom α : Type u
axiom b : Bool
```

:::comment
In this declaration, {lean}`α` is a {tech}[parameter], because it is used consistently in all occurrences of {name}`EvenOddList`.
{lean}`b` is an {tech}[index], because different {lean}`Bool` values are used for it at different occurrences.
:::

この宣言では、 {lean}`α` は {tech}[パラメータ] です。なぜなら、これは {name}`EvenOddList` のすべての出現で一貫して使用されているからです。 {lean}`b` は {tech}[index] であり、異なる出現で異なる {lean}`Bool` 値が使用されるからです。

::::


```lean (show:=false) (keep:=false)
def EvenOddList.length : EvenOddList α b → Nat
  | .nil => 0
  | .cons _ xs => xs.length + 1

theorem EvenOddList.length_matches_evenness (xs : EvenOddList α b) : b = (xs.length % 2 = 0) := by
  induction xs
  . simp [length]
  next b' _ xs ih =>
    simp [length]
    cases b' <;> simp only [Bool.true_eq_false, false_iff, true_iff] <;> simp at ih <;> omega
```
:::::

::::::keepEnv
:::comment
::example "Parameters before and after the colon"
:::
:::::example "コロンの前後にあるパラメータ"

:::comment
In this example, both parameters are specified before the colon in {name}`Either`'s signature.

:::

この例では、パラメータはどちらも {name}`Either` のシグネチャにおいてコロンの前に指定されています。

```lean
inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | left : α → Either α β
  | right : α → Either α β
```

:::comment
In this version, there are two types named `α` that might not be identical:
:::

このバージョンでは `α` という名前の型が2つあり、同一ではないかもしれません：

```lean (name := Either') (error := true)
inductive Either' (α : Type u) (β : Type v) : Type (max u v) where
  | left : {α : Type u} → {β : Type v} → α → Either' α β
  | right : α → Either' α β
```
```leanOutput Either'
inductive datatype parameter mismatch
  α
expected
  α✝
```

:::comment
Placing the parameters after the colon results in parameters that can be instantiated by the constructors:
:::

コロンの後にパラメータを置くと、コンストラクタでインスタンス化できるパラメータになります：

```lean (name := Either'')
inductive Either'' : Type u → Type v → Type (max u v) where
  | left : {α : Type u} → {β : Type v} → α → Either'' α β
  | right : α → Either'' α β
```
:::comment
{name}`Either''.right`'s type parameters are discovered via Lean's ordinary rules for {tech}[automatic implicit] parameters.
:::

{name}`Either''.right` の型パラメータは Lean の {tech}[automatic implicit] パラメータに関する通常の規則によって発見されます。

:::::
::::::


:::comment
## Anonymous Constructor Syntax
%%%
tag := "anonymous-constructor-syntax"
%%%

:::

## 匿名コンストラクタ構文

:::comment
If an inductive type has just one constructor, then this constructor is eligible for {deftech}_anonymous constructor syntax_.
Instead of writing the constructor's name applied to its arguments, the explicit arguments can be enclosed in angle brackets (`'⟨'` and `'⟩'`, Unicode `MATHEMATICAL LEFT ANGLE BRACKET	(U+0x27e8)` and `MATHEMATICAL RIGHT ANGLE BRACKET	(U+0x27e9)`) and separated with commas.
This works in both pattern and expression contexts.
Providing arguments by name or converting all implicit parameters to explicit parameters with `@` requires using the ordinary constructor syntax.

:::

帰納型がコンストラクタを1つだけ持つ場合、このコンストラクタは {deftech}_匿名コンストラクタ構文_ （anonymous constructor syntax）の対象となります。コンストラクタの名前を引数に適用して書く代わりに、明示的な引数を角括弧（`'⟨'` と `'⟩'`、Unicode `MATHEMATICAL LEFT ANGLE BRACKET	(U+0x27e8)` と `MATHEMATICAL RIGHT ANGLE BRACKET	(U+0x27e9)`）で囲み、カンマで区切ることができます。これはパターンと式の両方のコンテキストで動作します。引数を名前で指定したり、すべての暗黙的なパラメータを `@` で明示的なものに変換したりするには、通常のコンストラクタ構文を使用する必要があります。

:::comment
::example "Anonymous constructors"
:::
:::::example "匿名コンストラクタ"

::::keepEnv
```lean (show:=false)
axiom α : Type
```
:::comment
The type {lean}`AtLeastOne α` is similar to `List α`, except there's always at least one element present:
:::

型 {lean}`AtLeastOne α` は `List α` と似ていますが、少なくとも1つの要素が常に存在します：

::::

```lean
inductive AtLeastOne (α : Type u) : Type u where
  | mk : α → Option (AtLeastOne α) → AtLeastOne α
```

:::comment
Anonymous constructor syntax can be used to construct them:
:::

匿名コンストラクタ構文を使ってこれを構成することができます：

```lean
def oneTwoThree : AtLeastOne Nat :=
  ⟨1, some ⟨2, some ⟨3, none⟩⟩⟩
```
:::comment
and to match against them:
:::

また、この型の値にマッチすることができます：

```lean
def AtLeastOne.head : AtLeastOne α → α
  | ⟨x, _⟩ => x
```

:::comment
Equivalently, traditional constructor syntax could have been used:
:::

上記と同等に、通常のコンストラクタ構文も使うことが可能です：

```lean
def oneTwoThree' : AtLeastOne Nat :=
  .mk 1 (some (.mk 2 (some (.mk 3 none))))

def AtLeastOne.head' : AtLeastOne α → α
  | .mk x _ => x
```
:::::


:::comment
## Deriving Instances
%%%
tag := "inductive-declarations-deriving-instances"
%%%

:::

## インスタンスの導出

:::comment
The optional {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`deriving` clause of an inductive type declaration can be used to derive instances of type classes.
Please refer to {ref "deriving-instances"}[the section on instance deriving] for more information.


:::

帰納的宣言のオプションとして、 {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`deriving` 節は、型クラスのインスタンスを導出するために使用することができます。詳細は {ref "deriving-instances"}[インスタンス導出についての節] を参照してください。

{include 0 Manual.Language.InductiveTypes.Structures}

{include 0 Manual.Language.InductiveTypes.LogicalModel}

# ランタイム表現
%%%
tag := "run-time-inductives"
%%%

:::comment
// include の直後だとエラーになったため場所移動
# Run-Time Representation
:::

:::comment
An inductive type's run-time representation depends both on how many constructors it has, how many arguments each constructor takes, and whether these arguments are {tech}[relevant].

:::

帰納型のランタイム表現は、それがいくつのコンストラクタを持つか・各コンストラクタがいくつの引数を取り、それらの引数が {tech}[relevant] であるかどうかの両方に依存します。

:::comment
## Exceptions
%%%
tag := "inductive-types-runtime-special-support"
%%%

:::

## 例外

:::comment
Not every inductive type is represented as indicated here—some inductive types have special support from the Lean compiler:
:::

すべての帰納型がここで示されているように表現されるわけではありません。いくつかの帰納型は Lean のコンパイラによって特別にサポートされています：

::::keepEnv
````lean (show := false)
axiom α : Prop
````

:::comment
 * The fixed-width integer types {lean}`UInt8`, ..., {lean}`UInt64`, and {lean}`USize` are represented by the C types `uint8_t`, ..., `uint64_t`, and `size_t`, respectively.

:::

 * 固定幅整数 {lean}`UInt8`, ..., {lean}`UInt64` ・ {lean}`USize` は、それぞれ C の `uint8_t`, ..., `uint64_t` と `size_t` 型で表されます。

:::comment
 * {lean}`Char` is represented by `uint32_t`

:::

 * {lean}`Char` は `uint32_t` で表現されます。

:::comment
 * {lean}`Float` is represented by `double`

:::

 * {lean}`Float` は `double` で表現されます。

:::comment
 * An {deftech}_enum inductive_ type of at least 2 and at most $`2^{32}` constructors, each of which has no parameters, is represented by the first type of `uint8_t`, `uint16_t`, `uint32_t` that is sufficient to assign a unique value to each constructor. For example, the type {lean}`Bool` is represented by `uint8_t`, with values `0` for {lean}`false` and `1` for {lean}`true`. {TODO}[Find out whether this should say "no relevant parameters"]

:::

 * {deftech}_列挙帰納的_ （enum inductive）型は少なくとも2個から最大 $`2^{32}` 個のコンストラクタを持ち、各コンストラクタはパラメータを持ちませんが、 `uint8_t` ・ `uint16_t` ・ `uint32_t` のうち各コンストラクタに一意な値を割り当てるのに十分な最初の型によって表現されます。例えば、 {lean}`Bool` 型は `uint8_t` で表現され、 {lean}`false` の場合は `0` 、 {lean}`true` の場合は `1` になります。

:::comment
 * {lean}`Decidable α` is represented the same way as `Bool` {TODO}[Aren't Decidable and Bool just special cases of the rules for trivial constructors and irrelevance?]

:::

 * {lean}`Decidable α` は `Bool` と同じように表現されます。

:::comment
 * {lean}`Nat` is represented by `lean_object *`. Its run-time value is either a pointer to an opaque arbitrary-precision integer object or, if the lowest bit of the “pointer” is `1` (checked by `lean_is_scalar`), an encoded unboxed natural number (`lean_box`/`lean_unbox`). {TODO}[Move these to FFI section or Nat chapter]

:::

 * {lean}`Nat` は `lean_object *` で表現されます。そのランタイム値は不透明な任意精度整数オブジェクトへのポインタか、または「ポインタ」の最下位ビットが `1` の場合（`lean_is_scalar` でチェックされます）、ボックス化解除された整数にエンコードされます（`lean_box`/`lean_unbox`）。

::::

## Relevance
%%%
tag := "inductive-types-runtime-relevance"
%%%


:::comment
Types and proofs have no run-time representation.
That is, if an inductive type is a `Prop`, then its values are erased prior to compilation.
Similarly, all theorem statements and types are erased.
Types with run-time representations are called {deftech}_relevant_, while types without run-time representations are called {deftech}_irrelevant_.

:::

型と証明はランタイム表現を持ちません。つまり、帰納型が `Prop` である場合、その値はコンパイル前に消去されます。同様に、すべての定理文と型は消去されます。ランタイム表現を持つ型を {deftech}_relevant_ と呼び、ランタイム表現を持たない型を {deftech}_irrelevant_ と呼びます。

:::comment
::example "Types are irrelevant"
:::
::::example "型は irrelevant である"
:::comment
Even though {name}`List.cons` has the following signature, which indicates three parameters:
:::

{name}`List.cons` は以下のように3つのパラメータを持つシグネチャにも関わらず：

```signature
List.cons.{u} {α : Type u} : α → List α → List α
```
:::comment
its run-time representation has only two, because the type argument is run-time irrelevant.
:::

このランタイム表現では2つのみのパラメータとなります。なぜなら、型引数はランタイムでは irrelevant だからです。

::::

:::comment
::example "Proofs are irrelevant"
:::
::::example "証明は irrelevant である"
:::comment
Even though {name}`Fin.mk` has the following signature, which indicates three parameters:
:::

{name}`Fin.mk` は以下のように3つのパラメータを持つシグネチャにも関わらず：

```signature
Fin.mk {n : Nat} (val : Nat) : val < n → Fin n
```
:::comment
its run-time representation has only two, because the proof is erased.
:::

このランタイム表現では2つのみのパラメータとなります。なぜなら、証明は消去されるからです。

::::

:::comment
In most cases, irrelevant values simply disappear from compiled code.
However, in cases where some representation is required (such as when they are arguments to polymorphic constructors), they are represented by a trivial value.

:::

ほとんどの場合、irrelevant な値は単にコンパイルされたコードから消えるだけです。しかし、何らかの表現が必要な場合（多相コンストラクタの引数など）、自明な値で表現されます。

:::comment
## Trivial Wrappers
%%%
tag := "inductive-types-trivial-wrappers"
%%%

:::

## 自明なラッパ

:::comment
If an inductive type has exactly one constructor, and that constructor has exactly one run-time relevant parameter, then the inductive type is represented identically to its parameter.

:::

帰納型が正確に1つのコンストラクタを持ち、そのコンストラクタが正確に1つのランタイムにおいて relevant なパラメータを持つならば、帰納型はそのパラメータと同一のものとして表現されます。

:::comment
::example "Zero-Overhead Subtypes"
:::
::::example "オーバーヘッドのない部分型"
:::comment
The structure {name}`Subtype` bundles an element of some type with a proof that it satisfies a predicate.
Its constructor takes four arguments, but three of them are irrelevant:
:::

構造体 {name}`Subtype` はある型の要素と、それがある述語を満たすことの証明を束ねたものです。コンストラクタは4つの引数を取りますが、そのうち3つは irrelevant です：

```signature
Subtype.mk.{u} {α : Sort u} {p : α → Prop}
  (val : α) (property : p val) : Subtype p
```
:::comment
Thus, subtypes impose no runtime overhead in compiled code, and are represented identically to the type of the {name Subtype.val}`val` field.
:::

このように、部分型はコンパイルされたコードにおいてランタイムのオーバーヘッドを発生させず、 {name Subtype.val}`val` フィールドの型と同一のものとして表現されます。

::::

:::comment
## Other Inductive Types
%%%
tag := "inductive-types-standard-representation"
%%%


:::

## その他の帰納型

:::comment
If an inductive type doesn't fall into one of the categories above, then its representation is determined by its constructors.
Constructors without relevant parameters are represented by their index into the list of constructors, as unboxed unsigned machine integers (scalars).
Constructors with relevant parameters are represented as an object with a header, the constructor's index, an array of pointers to other objects, and then arrays of scalar fields sorted by their types.
The header tracks the object's reference count and other necessary bookkeeping.

:::

帰納型が上記のカテゴリのいずれにも属さない場合、その表現はコンストラクタによって決定されます。relevant なパラメータを持たないコンストラクタは、コンストラクタのリストへのインデックスによって表現され、ボックス化解除された符号なし機械整数（スカラー）として表現されます。relevant なパラメータを持つコンストラクタは、ヘッダ・コンストラクタのインデックス・他のオブジェクトへのポインタの配列・型の順に並べられたスカラーのフィールドの配列を持つオブジェクトとして表現されます。ヘッダはオブジェクトの参照カウントやその他の必要な記録を追跡します。

:::comment
Recursive functions are compiled as they are in most programming languages, rather than by using the inductive type's recursor.
Elaborating recursive functions to recursors serves to provide reliable termination evidence, not executable code.

:::

再帰関数は帰納型の再帰子を使用するのではなく、ほとんどのプログラミング言語と同じようにコンパイルされます。再帰関数を再帰子にエラボレートするのは、実行ファイルのコードではなく、信頼された停止の根拠を提供するために役立てられます。

### FFI
%%%
tag := "inductive-types-ffi"
%%%

:::comment
From the perspective of C, these other inductive types are represented by `lean_object *`.
Each constructor is stored as a `lean_ctor_object`, and `lean_is_ctor` will return true.
A `lean_ctor_object` stores the constructor index in its header, and the fields are stored in the `m_objs` portion of the object.
Lean assumes that `sizeof(size_t) == sizeof(void*)`—while this is not guaranteed by C, the Lean run-time system contains an assertion that fails if this is not the case.


:::

C の観点では、これらの帰納型は `lean_object *` として表現されます。各コンストラクタは `lean_ctor_object` として格納され、`lean_is_ctor` は真を返します。`lean_ctor_object` はコンストラクタのインデックスをヘッダに格納し、フィールドはオブジェクトの `m_objs` 部分に格納されます。

:::comment
The memory order of the fields is derived from the types and order of the fields in the declaration. They are ordered as follows:

:::

フィールドのメモリ順序は、宣言のフィールドの型とその並び順から導かれます。フィールドの並び順は以下に従います：

:::comment
* Non-scalar fields stored as `lean_object *`
* Fields of type {lean}`USize`
* Other scalar fields, in decreasing order by size

:::

* `lean_object *` として格納される非スカラーのフィールド
* {lean}`USize` 型のフィールド
* その他のスカラーのフィールドはサイズの降順で並ぶ

:::comment
Within each group the fields are ordered in declaration order. **Warning**: Trivial wrapper types still count toward a field being treated as non-scalar for this purpose.

:::

各グループ内では、フィールドは宣言順に並んでいます。**警告**：自明なラッパ型は、この目的のためにフィールドが非スカラーとして扱われます。

:::comment
* To access fields of the first kind, use `lean_ctor_get(val, i)` to get the `i`th non-scalar field.
* To access {lean}`USize` fields, use `lean_ctor_get_usize(val, n+i)` to get the `i`th `USize` field and `n` is the total number of fields of the first kind.
* To access other scalar fields, use `lean_ctor_get_uintN(val, off)` or `lean_ctor_get_usize(val, off)` as appropriate. Here `off` is the byte offset of the field in the structure, starting at `n*sizeof(void*)` where `n` is the number of fields of the first two kinds.

:::

* 最初の種類のフィールドにアクセスするには、 `lean_ctor_get(val, i)` を使って `i` 番目の非スカラーフィールドを取得します。
* {lean}`USize` フィールドにアクセスするには、`lean_ctor_get_usize(val, n+i)` を使って `i` 番目の usize フィールドを取得します。`n` は最初の種類のフィールドの総数です。
* その他のスカラーフィールドにアクセスするには、`lean_ctor_get_uintN(vai, off)` または `lean_ctor_get_usize(val, off)` を適切に使用します。ここで `off` は構造体内のフィールドのバイトオフセットであり、`n*sizeof(void*)` から始まります。`n` はその前の2種類のフィールドの数です。

::::keepEnv

:::comment
For example, a structure such as
:::

例えば、以下のような構造体があるとして、

```lean
structure S where
  ptr_1 : Array Nat
  usize_1 : USize
  sc64_1 : UInt64
  ptr_2 : { x : UInt64 // x > 0 } -- wrappers don't count as scalars
  sc64_2 : Float -- `Float` is 64 bit
  sc8_1 : Bool
  sc16_1 : UInt16
  sc8_2 : UInt8
  sc64_3 : UInt64
  usize_2 : USize
  ptr_3 : Char -- trivial wrapper around `UInt32`
  sc32_1 : UInt32
  sc16_2 : UInt16
```
:::comment
would get re-sorted into the following memory order:

:::

これは以下のメモリ順序に再ソートされます：

* {name}`S.ptr_1` - `lean_ctor_get(val, 0)`
* {name}`S.ptr_2` - `lean_ctor_get(val, 1)`
* {name}`S.ptr_3` - `lean_ctor_get(val, 2)`
* {name}`S.usize_1` - `lean_ctor_get_usize(val, 3)`
* {name}`S.usize_2` - `lean_ctor_get_usize(val, 4)`
* {name}`S.sc64_1` - `lean_ctor_get_uint64(val, sizeof(void*)*5)`
* {name}`S.sc64_2` - `lean_ctor_get_float(val, sizeof(void*)*5 + 8)`
* {name}`S.sc64_3` - `lean_ctor_get_uint64(val, sizeof(void*)*5 + 16)`
* {name}`S.sc32_1` - `lean_ctor_get_uint32(val, sizeof(void*)*5 + 24)`
* {name}`S.sc16_1` - `lean_ctor_get_uint16(val, sizeof(void*)*5 + 28)`
* {name}`S.sc16_2` - `lean_ctor_get_uint16(val, sizeof(void*)*5 + 30)`
* {name}`S.sc8_1` - `lean_ctor_get_uint8(val, sizeof(void*)*5 + 32)`
* {name}`S.sc8_2` - `lean_ctor_get_uint8(val, sizeof(void*)*5 + 33)`

::::

::: TODO
Figure out how to test/validate/CI these statements
:::


:::comment
# Mutual Inductive Types
%%%
tag := "mutual-inductive-types"
%%%


:::

# 相互帰納型

:::comment
Inductive types may be mutually recursive.
Mutually recursive definitions of inductive types are specified by defining the types in a `mutual ... end` block.

:::

帰納型は相互に再帰することができます。帰納型の相互再帰定義は `mutual ... end` ブロックの中での型の定義として指定されます。

:::comment
::example "Mutually Defined Inductive Types"
:::
::::example "相互に定義された帰納型"
:::comment
The type {name}`EvenOddList` in a prior example used a Boolean index to select whether the list in question should have an even or odd number of elements.
This distinction can also be expressed by the choice of one of two mutually inductive types {name}`EvenList` and {name}`OddList`:

:::

先の例の型 {name}`EvenOddList` は真偽値の添字を使用して問題のリストの要素数が偶数か奇数かを選択しました。この区別は、2つの相互帰納的データ型 {name}`EvenList` と {name}`OddList` のどちらかを選択することでも表現できます：

```lean
mutual
  inductive EvenList (α : Type u) : Type u where
    | nil : EvenList α
    | cons : α → OddList α → EvenList α
  inductive OddList (α : Type u) : Type u where
    | cons : α → EvenList α → OddList α
end

example : EvenList String := .cons "x" (.cons "y" .nil)
example : OddList String := .cons "x" (.cons "y" (.cons "z" .nil))
```
```lean (error := true) (name := evenOddMut)
example : OddList String := .cons "x" (.cons "y" .nil)
```
```leanOutput evenOddMut
invalid dotted identifier notation, unknown identifier `OddList.nil` from expected type
  OddList String
```
::::

:::comment
## Requirements
%%%
tag := "mutual-inductive-types-requirements"
%%%


:::

## 要件

:::comment
The inductive types declared in a `mutual` block are considered as a group; they must collectively satisfy generalized versions of the well-formedness criteria for non-mutually-recursive inductive types.
This is true even if they could be defined without the `mutual` block, because they are not in fact mutually recursive.

:::

`mutual` ブロックで宣言された帰納型は1つのグループとして扱われます；これらはすべて非相互再帰帰納型の適格な基準を一般化したものを満たさなければなりません。これらは実は相互に再帰的ではないため、`mutual` ブロック無しで定義できた場合でも同様です。

:::comment
### Mutual Dependencies
%%%
tag := "mutual-inductive-types-dependencies"
%%%

:::

### 相互依存

:::comment
Each type constructor's signature must be able to be elaborated without reference to the other inductive types in the `mutual` group.
In other words, the inductive types in the `mutual` group may not take each other as arguments.
The constructors of each inductive type may mention the other type constructors in the group in their parameter types, with restrictions that are a generalization of those for recursive occurrences in non-mutual inductive types.

:::

それぞれの型コンストラクタのシグネチャは、`mutual` グループ内の他の帰納型を参照することなくエラボレートできなければなりません。言い換えると、`mutual` グループ内の帰納型はお互いを引数として取ることはできません。それぞれの帰納型のコンストラクタは、非相互帰納型における再帰的な出現のための制限を一般化したもので、パラメータ型においてグループ内の他の型コンストラクタに言及することができます。

:::comment
::example "Mutual inductive type constructors may not mention each other"
:::
::::example "お互いに言及しない相互帰納型コンストラクタ"
:::comment
These inductive types are not accepted by Lean:
:::

これらの帰納型は Lean に許容されません：

```lean (error:=true) (name := mutualNoMention)
mutual
  inductive FreshList (α : Type) (r : α → α → Prop) : Type where
    | nil : FreshList α r
    | cons (x : α) (xs : FreshList α r) (fresh : Fresh r x xs)
  inductive Fresh (r : α → FreshList α → Prop) : α → FreshList α r → Prop where
    | nil : Fresh r x .nil
    | cons : r x y → (f : Fresh r x ys) → Fresh r x (.cons y ys f)
end
```

:::comment
The type constructors may not refer to the other type constructors in the `mutual` group, so `FreshList` is not in scope in the type constructor of `Fresh`:
:::

型コンストラクタは `mutual` グループの他の型コンストラクタを参照することはできないため、 `FreshList` は `Fresh` の型コンストラクタのスコープにありません：

```leanOutput mutualNoMention
unknown identifier 'FreshList'
```
::::


:::comment
### Parameters Must Match
%%%
tag := "mutual-inductive-types-same-parameters"
%%%

:::

### マッチすべきパラメータ

:::comment
All inductive types in the `mutual` group must have the same {tech}[parameters].
Their indices may differ.

:::

`mutual` グループ内のすべての帰納型は同じ {tech}[パラメータ] を持たなければなりません。それらの添字は異なっていてもかまいません。

:::::keepEnv
:::comment
:: example "Differing numbers of parameters"
:::
:::: example "パラメータ数が異なる場合"
:::comment
Even though `Both` and `OneOf` are not mutually recursive, they are declared in the same `mutual` block and must therefore have identical parameters:
:::

`Both` と `OneOf` は相互再帰的ではありませんが、同じ `mutual` ブロックで宣言されているため、同じパラメータを持たなければなりません：

```lean (name := bothOptional) (error := true)
mutual
  inductive Both (α : Type u) (β : Type v) where
    | mk : α → β → Both α β
  inductive Optional (α : Type u) where
    | none
    | some : α → Optional α
end
```
```leanOutput bothOptional
invalid inductive type, number of parameters mismatch in mutually inductive datatypes
```
::::
:::::

:::::keepEnv
:::comment
:: example "Differing parameter types"
:::
:::: example "パラメータの型が異なる場合"
:::comment
Even though `Many` and `OneOf` are not mutually recursive, they are declared in the same `mutual` block and must therefore have identical parameters.
They both have exactly one parameter, but `Many`'s parameter is not necessarily in the same universe as `Optional`'s:
:::

`Many` と `OneOf` は相互再帰的ではありませんが、同じ `mutual` ブロックで宣言されているため、同じパラメータを持たなければなりません。両者は正確に1つのパラメータを持っていますが、`Many` のパラメータは `Optional` のパラメータと同じ宇宙にあるとは限りません：

```lean (name := manyOptional) (error := true)
mutual
  inductive Many (α : Type) : Type u where
    | nil : Many α
    | cons : α → Many α → Many α
  inductive Optional (α : Type u) where
    | none
    | some : α → Optional α
end
```
```leanOutput manyOptional
invalid mutually inductive types, parameter 'α' has type
  Type u : Type (u + 1)
but is expected to have type
  Type : Type 1
```
::::
:::::

:::comment
### Universe Levels
%%%
tag := "mutual-inductive-types-same-universe"
%%%

:::

### 宇宙レベル

:::comment
The universe levels of each inductive type in a mutual group must obey the same requirements as non-mutually-recursive inductive types.
Additionally, all the inductive types in a mutual group must be in the same universe, which implies that their constructors are similarly limited with respect to their parameters' universes.

:::

相互グループ内の各帰納型の宇宙レベルは、非相互再帰的な帰納型と同じ要件に従わなければなりません。さらに、相互グループ内のすべての帰納型は同じ宇宙でなければならず、これはそれらのコンストラクタがパラメータの宇宙に関して同様に制限されることを意味します。

:::comment
::example "Universe mismatch"
:::
:::::example "宇宙のミスマッチ"
::::keepEnv
:::comment
These mutually-inductive types are a somewhat complicated way to represent run-length encoding of a list:
:::

これらの相互帰納型はリストの連長圧縮を表すやや複雑な方法です：

```lean
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run (x : α) (n : Nat) : n ≠ 0 → PrefixRunOf n x xs ys → RLE ys → RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Type where
  | zero (noMore : ¬∃zs, xs = x :: zs := by simp) : PrefixRunOf 0 x xs xs
  | succ : PrefixRunOf n x xs ys → PrefixRunOf (n + 1) x (x :: xs) ys
end

example : RLE [1, 1, 2, 2, 3, 1, 1, 1] :=
  .run 1 2 (by decide) (.succ (.succ .zero)) <|
  .run 2 2 (by decide) (.succ (.succ .zero)) <|
  .run 3 1 (by decide) (.succ .zero) <|
  .run 1 3 (by decide) (.succ (.succ (.succ (.zero)))) <|
  .nil
```

:::comment
Specifying {name}`PrefixRunOf` as a {lean}`Prop` would be sensible, but it cannot be done because the types would be in different universes:
:::

{name}`PrefixRunOf` を {lean}`Prop` として指定するほうが感覚的ですが、型が異なる宇宙になるためできません：

::::

::::keepEnv
```lean (error :=true) (name := rleBad)
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run (x : α) (n : Nat) : n ≠ 0 → PrefixRunOf n x xs ys → RLE ys → RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Prop where
  | zero (noMore : ¬∃zs, xs = x :: zs := by simp) : PrefixRunOf 0 x xs xs
  | succ : PrefixRunOf n x xs ys → PrefixRunOf (n + 1) x (x :: xs) ys
end
```
```leanOutput rleBad
invalid mutually inductive types, resulting universe mismatch, given
  Prop
expected type
  Type
```
::::

::::keepEnv
:::comment
This particular property can be expressed by separately defining the well-formedness condition and using a subtype:
:::

この特殊な性質は、適格条件を個別に定義し、部分型を使用することで表現できます：

```lean
def RunLengths α := List (α × Nat)
def NoRepeats : RunLengths α → Prop
  | [] => True
  | [_] => True
  | (x, _) :: ((y, n) :: xs) =>
    x ≠ y ∧ NoRepeats ((y, n) :: xs)
def RunsMatch : RunLengths α → List α → Prop
  | [], [] => True
  | (x, n) :: xs, ys =>
    ys.take n = List.replicate n x ∧
    RunsMatch xs (ys.drop n)
  | _, _ => False
def NonZero : RunLengths α → Prop
  | [] => True
  | (_, n) :: xs => n ≠ 0 ∧ NonZero xs
structure RLE (xs : List α) where
  rle : RunLengths α
  noRepeats : NoRepeats rle
  runsMatch : RunsMatch rle xs
  nonZero : NonZero rle

example : RLE [1, 1, 2, 2, 3, 1, 1, 1] where
  rle := [(1, 2), (2, 2), (3, 1), (1, 3)]
  noRepeats := by simp [NoRepeats]
  runsMatch := by simp [RunsMatch]
  nonZero := by simp [NonZero]
```
::::
:::::


### Positivity
%%%
tag := "mutual-inductive-types-positivity"
%%%

:::comment
Each inductive type that is defined in the `mutual` group may occur only strictly positively in the types of the parameters of the constructors of all the types in the group.
In other words, in the type of each parameter to each constructor in all the types of the group, none of the type constructors in the group occur to the left of any arrows, and none of them occur in argument positions unless they are an argument to an inductive type's type constructor.

:::

`mutual` グループで定義される各帰納型は、グループ内のすべての型のコンストラクタのパラメータの型中において strict positively にのみ出現可能です。言い換えると、グループ内のすべての型の各コンストラクタのパラメータの型では、グループ内のどの型コンストラクタも矢印の左側には出現せず、帰納的データ型の型コンストラクタの引き数でない限り引数の位置に出現しません。

:::comment
:: example "Mutual strict positivity"
:::
:::: example "相互に strict positivity"
:::comment
In the following mutual group, `Tm` occurs in a negative position in the argument to `Binding.scope`:
:::

以下の相互グループでは、`Tm` が `Binding.scope` の引数の negative な位置に出現しています：

```lean (error := true) (name := mutualHoas)
mutual
  inductive Tm where
    | app : Tm → Tm → Tm
    | lam : Binding → Tm
  inductive Binding where
    | scope : (Tm → Tm) → Binding
end
```
:::comment
Because `Tm` is part of the same mutual group, it must occur only strictly positively in the arguments to the constructors of `Binding`.
It occurs, however, negatively:
:::

`Tm` は同じ相互グループの一部であるため、`Binding` のコンストラクタの引数としては strict positive にのみ出現しなければなりません。しかし、ここでは negative に出現しています：

```leanOutput mutualHoas
(kernel) arg #1 of 'Binding.scope' has a non positive occurrence of the datatypes being declared
```
::::

:::comment
:: example "Nested positions"
:::
:::: example "ネストされた位置"
:::comment
The definitions of {name}`LocatedStx` and {name}`Stx` satisfy the positivity condition because the recursive occurrences are not to the left of any arrows and, when they are arguments, they are arguments to inductive type constructors.

:::

{name}`LocatedStx` と {name}`Stx` の定義は、再帰的な出現がどの矢印の左にもなく、引数である場合は帰納的な型コンストラクタの引数であるため、positivity の条件を満たします。

```lean
mutual
  inductive LocatedStx where
    | mk (line col : Nat) (val : Stx)
  inductive Stx where
    | atom (str : String)
    | node (kind : String) (args : List LocatedStx)
end
```
::::

:::comment
## Recursors
%%%
tag := "mutual-inductive-types-recursors"
%%%

:::

## 再帰子

:::comment
Mutual inductive types are provided with primitive recursors, just like non-mutually-defined inductive types.
These recursors take into account that they must process the other types in the group, and thus will have a motive for each inductive type.
Because all inductive types in the `mutual` group are required to have identical parameters, the recursors still take the parameters first, abstracting them over the motives and the rest of the recursor.
Additionally, because the recursor must process the group's other types, it will require cases for each constructor of each of the types in the group.
The actual dependency structure between the types is not taken into account; even if an additional motive or constructor case is not really required due to there being fewer mutual dependencies than there could be, the generated recursor still requires them.

:::

相互帰納型には、非相互に定義された帰納型と同様に、プリミティブな再帰子が用意されています。これらの再帰子は、グループ内の他の型を処理しなければならないことを考慮し、それぞれの帰納型に対して動機を持つことになります。`mutual` グループ内のすべての帰納型は同一のパラメータを持つ必要があるため、再帰子はパラメータを最初に受け取り、動機と再帰子の残りの部分を抽象化します。さらに、再帰子はグループの他の型を処理する必要があるため、グループ内の各型コンストラクタについてのケースが必要になります。型の間の実施あの依存構造は考慮されません；相互依存関係が少ないことで追加の動機またはコンストラクタのケースが実際には必要ない場合でも、生成された再帰子はそれらを必要とします。

:::comment
:: example "Even and odd"
:::
::::keepEnv
::: example "偶奇"
```lean
mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : Odd n → Even (n + 1)
  inductive Odd : Nat → Prop where
    | succ : Even n → Odd (n + 1)
end
```

```signature
Even.rec
  {motive_1 : (a : Nat) → Even a → Prop}
  {motive_2 : (a : Nat) → Odd a → Prop}
  (zero : motive_1 0 Even.zero)
  (succ : {n : Nat} → (a : Odd n) → motive_2 n a → motive_1 (n + 1) (Even.succ a)) :
  (∀ {n : Nat} (a : Even n), motive_1 n a → motive_2 (n + 1) (Odd.succ a)) →
  ∀ {a : Nat} (t : Even a), motive_1 a t
```

```signature
Odd.rec
  {motive_1 : (a : Nat) → Even a → Prop}
  {motive_2 : (a : Nat) → Odd a → Prop}
  (zero : motive_1 0 Even.zero)
  (succ : ∀ {n : Nat} (a : Odd n), motive_2 n a → motive_1 (n + 1) (Even.succ a)) :
  (∀ {n : Nat} (a : Even n), motive_1 n a → motive_2 (n + 1) (Odd.succ a)) → ∀ {a : Nat} (t : Odd a), motive_2 a t
```

:::
::::

:::comment
::example "Spuriously mutual types"
:::
:::::keepEnv
::::example "疑似的な相互型"
:::comment
The types {name}`Two` and {name}`Three` are defined in a mutual block, even though they do not refer to each other:
:::

型 {name}`Two` と {name}`Three` はお互いを参照しないにもかかわらず、相互ブロック内で定義されています：

```lean
mutual
  inductive Two (α : Type) where
    | mk : α → α → Two α
  inductive Three (α : Type) where
    | mk : α → α → α → Three α
end
```
:::comment
{name}`Two`'s recursor, {name}`Two.rec`, nonetheless requires a motive and a case for {name}`Three`:
:::

それにもかかわらず、 {name}`Two` の再帰子である {name}`Two.rec` は {name}`Three` の動機とケースを必要とします。

```signature
Two.rec.{u} {α : Type}
  {motive_1 : Two α → Sort u}
  {motive_2 : Three α → Sort u}
  (mk : (a a_1 : α) → motive_1 (Two.mk a a_1)) :
  ((a a_1 a_2 : α) → motive_2 (Three.mk a a_1 a_2)) → (t : Two α) → motive_1 t
```

::::
:::::

:::comment
## Run-Time Representation
%%%
tag := "mutual-inductive-types-run-time"
%%%

:::

## ランタイム表現

:::comment
Mutual inductive types are represented identically to {ref "run-time-inductives"}[non-mutual inductive types] in compiled code and in the runtime.
The restrictions on mutual inductive types exist to ensure Lean's consistency as a logic, and do not impact compiled code.

:::

相互帰納型はコンパイルされたコードでもランタイムでも {ref "run-time-inductives"}[非相互帰納型] と同一に表現されます。相互帰納型に対する制限は、Lean の論理としての一貫性を保証するために存在し、コンパイルされたコードには影響しません。

## Nested inductive types
%%%
tag := "nested-inductive-types"
%%%

:::planned 235
TODO
:::
