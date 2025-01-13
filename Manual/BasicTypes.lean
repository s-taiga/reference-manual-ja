/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.BasicTypes.Nat
import Manual.BasicTypes.Int
import Manual.BasicTypes.String
import Manual.BasicTypes.Array
import Manual.BasicTypes.Fin
import Manual.BasicTypes.UInt
import Manual.BasicTypes.Option
import Manual.BasicTypes.Empty

open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true


/-
#doc (Manual) "Basic Types" =>
-/
#doc (Manual) "基本的な型（Basic Types）" =>
%%%
tag := "basic-types"
%%%


:::comment
Lean includes a number of built-in types that are specially supported by the compiler.
Some, such as {lean}`Nat`, additionally have special support in the kernel.
Other types don't have special compiler support _per se_, but rely in important ways on the internal representation of types for performance reasons.

:::

Lean にはコンパイラが特別にサポートする組み込みの型が多数あります。 {lean}`Nat` のように、カーネルで特別にサポートされているものもあります。その他の型はコンパイラからの特別なサポート _自体_ はありませんが、パフォーマンス上の理由から型の内部表現に依存しています。

{include 0 Manual.BasicTypes.Nat}

{include 0 Manual.BasicTypes.Int}

{include 0 Manual.BasicTypes.Fin}

{include 0 Manual.BasicTypes.UInt}


# Bitvectors
%%%
tag := "BitVec"
%%%


:::planned 106
 * Run-time and kernel representations of {name}`BitVec`
 * API reference
 * Cross-reference to TBW chapter on `bv_decide`
:::

# Floating-Point Numbers
%%%
tag := "Float"
%%%


:::planned 107
 * Run-time and kernel representations
 * Precision, and whether it's platform-dependent
 * Relationship between IEEE floats and decidable equality
:::

:::comment
# Characters
:::

# 文字（Characters）
%%%
tag := "Char"
%%%



{docstring Char}

:::comment
## Syntax
:::

## 構文（Syntax）
%%%
tag := "char-syntax"
%%%



:::comment
## Logical Model
:::

## 論理モデル（Logical Model）
%%%
tag := "char-model"
%%%


:::comment
## Run-Time Representation
:::

## ランタイム表現（Run-Time Representation）
%%%
tag := "char-runtime"
%%%


:::comment
In monomorphic contexts, characters are represented as 32-bit immediate values. In other words, a field of a constructor or structure of type {lean}`Char` does not require indirection to access. In polymorphic contexts, characters are boxed.


:::

モノ射なコンテキストでは、文字は32ビットの即値として表現されます。言い換えると、{lean}`Char` 型のコンストラクタや構造体のフィールドにアクセスする際にインダイレクトは必要ありません。多相なコンテキストでは文字はボックス化されます。

:::comment
## API Reference
:::

## API リファレンス（API Reference）
%%%
tag := "char-api"
%%%



:::comment
### Character Classes
:::

### 文字クラス（Character Classes）
%%%
tag := "char-api-classes"
%%%



{docstring Char.isAlpha}

{docstring Char.isAlphanum}

{docstring Char.isDigit}

{docstring Char.isLower}

{docstring Char.isUpper}

{docstring Char.isWhitespace}

{include 0 Manual.BasicTypes.String}

# ユニット型（The Unit Type）

:::comment
# The Unit Type
:::

:::comment
The unit type is the least informative type.
It is used when a value is needed, but no further information is relevant.
There are two varieties of the unit type:

:::

ユニット型は最も情報量の少ない型です。これは、値は必要だがそれ以上の情報は必要ない場合に使用されます。ユニット型には2種類あります：

:::comment
 * {lean}`Unit` is a {lean}`Type` that exists in the smallest non-propositional {tech}[universe].

:::

 * {lean}`Unit` は {lean}`Type` であり、最小の非命題 {tech}[宇宙] に存在します。

:::comment
 * {lean}`PUnit` is {tech key:="universe polymorphism"}[universe polymorphic] and can be used in any non-propositional {tech}[universe].

:::

 * {lean}`PUnit` は {tech}[宇宙多相] であり、任意の非命題 {tech}[宇宙] で使用することができます。

:::comment
If in doubt, use {lean}`Unit` until universe errors occur.

:::

悩ましい場合は、宇宙に関するエラーが発生するまでは {lean}`Unit` を使ってください。

{docstring Unit}

{docstring Unit.unit}

{docstring PUnit}

## Definitional Equality


:::comment
{deftech}_Unit-like types_ are inductive types that have a single constructor which takes no non-proof parameters.
{lean}`PUnit` is one such type.
All elements of unit-like types are {tech key:="definitional equality"}[definitionally equal] to all other elements.

:::

{deftech}_unit-like 型_ （unit-like type）は非証明のパラメータを取らない単一のコンストラクタを持つ帰納型です。 {lean}`PUnit` はそのような型の1つです。unit-like 型のすべての要素は、他のすべての要素と {tech key:="definitional equality"}[definitionally equal] です。

:::comment
::example "Definitional Equality of {lean}`Unit`"
:::
::::example "{lean}`Unit` の definitional equality"
:::comment
Every term with type {lean}`Unit` is definitionally equal to every other term with type {lean}`Unit`:

:::

{lean}`Unit` 型を持つすべての項は、 {lean}`Unit` 型を持つすべての項と definitionally equal tです：

```lean
example (e1 e2 : Unit) : e1 = e2 := rfl
```
::::

:::::keepEnv
:::comment
::example "Definitional Equality of Unit-Like Types"
:::
::::example "unit-like 型の definitional equality"

:::comment
Both {lean}`CustomUnit` and {lean}`AlsoUnit` are unit-like types, with a single constructor that takes no parameters.
Every pair of terms with either type is definitionally equal.

:::

{lean}`CustomUnit` と {lean}`AlsoUnit` はどちらも unit-like 型であり、パラメータを取らないコンストラクタを1つ持ちます。どちらの型を持つ項のペアも definitionally equal tです。

```lean
inductive CustomUnit where
  | customUnit

example (e1 e2 : CustomUnit) : e1 = e2 := rfl

structure AlsoUnit where

example (e1 e2 : AlsoUnit) : e1 = e2 := rfl
```

:::comment
Types with parameters, such as {lean}`WithParam`, are also unit-like if they have a single constructor that does not take parameters.

:::

{lean}`WithParam` のようなパラメータを持つ型も、パラメータを取らないコンストラクタが1つあれば unit-like です。

```lean
inductive WithParam (n : Nat) where
  | mk

example (x y : WithParam 3) : x = y := rfl
```

:::comment
Constructors with non-proof parameters are not unit-like, even if the parameters are all unit-like types.
:::

証明ではないパラメータを持つコンストラクタは、パラメータがすべて unit-like 型であっても unit-like になりません。

```lean
inductive NotUnitLike where
  | mk (u : Unit)
```

```lean (error:=true) (name := NotUnitLike)
example (e1 e2 : NotUnitLike) : e1 = e2 := rfl
```
```leanOutput NotUnitLike
type mismatch
  rfl
has type
  ?m.13 = ?m.13 : Prop
but is expected to have type
  e1 = e2 : Prop
```

:::comment
Constructors of unit-like types may take parameters that are proofs.
:::

unit-like 型のコンストラクタは証明であるパラメータを取ることができます。

```lean
inductive ProofUnitLike where
  | mk : 2 = 2 → ProofUnitLike

example (e1 e2 : ProofUnitLike) : e1 = e2 := rfl
```
::::
:::::

{include 0 Manual.BasicTypes.Empty}


:::comment
# Booleans
:::

# 真偽値（Booleans）


{docstring Bool}

:::comment
The constructors {lean}`Bool.true` and {lean}`Bool.false` are exported from the {lean}`Bool` namespace, so they can be written {lean}`true` and {lean}`false`.

:::

コンストラクタ {lean}`Bool.true` と {lean}`Bool.false` は {lean}`Bool` 名前空間からエクスポートされるため、 {lean}`true` と {lean}`false` と書くことができます。

:::comment
## Run-Time Representation
:::

## ランタイム表現（Run-Time Representation）


:::comment
Because {lean}`Bool` is an {tech}[enum inductive] type, it is represented by a single byte in compiled code.

:::

{lean}`Bool` は {tech}[列挙帰納的] 型であるため、コンパイルされたコードでは1バイトで表現されます。

:::comment
## Booleans and Propositions
:::

## 真偽値と命題（Booleans and Propositions）


:::comment
Both {lean}`Bool` and {lean}`Prop` represent notions of truth.
From a purely logical perspective, they are equivalent: {tech}[propositional extensionality] means that there are fundamentally only two propositions, namely {lean}`True` and {lean}`False`.
However, there is an important pragmatic difference: {lean}`Bool` classifies _values_ that can be computed by programs, while {lean}`Prop` classifies statements for which code generation doesn't make sense.
In other words, {lean}`Bool` is the notion of truth and falsehood that's appropriate for programs, while {lean}`Prop` is the notion that's appropriate for mathematics.
Because proofs are erased from compiled programs, keeping {lean}`Bool` and {lean}`Prop` distinct makes it clear which parts of a Lean file are intended for computation.

:::

{lean}`Bool` と {lean}`Prop` はどちらも真理の概念を表します。純粋論理の観点から見ると、両者は同等です： {tech}[propositional extensionality] は基本的に2つの命題、すなわち {lean}`True` と {lean}`False` しか存在しないことを意味します。しかし、実用上は重要な違いがあります： {lean}`Bool` はプログラムで計算できる _値_ を分類し、 {lean}`Prop` はコード生成が意味を為さない文を分類します。言い換えると、 {lean}`Bool` はプログラムに適した真偽の概念であり、 {lean}`Prop` は数学に適した概念です。コンパイルされたプログラムから証明は消去されるため、 {lean}`Bool` と {lean}`Prop` を区別しておくことで Lean ファイルのどの部分が計算を目的としているかが明確になります。

```lean (show := false)
section BoolProp

axiom b : Bool

/-- info: b = true : Prop -/
#guard_msgs in
#check (b : Prop)

example : (true = true) = True := by simp

#check decide
```

:::comment
A {lean}`Bool` can be used wherever a {lean}`Prop` is expected.
There is a {tech}[coercion] from every {lean}`Bool` {lean}`b` to the proposition {lean}`b = true`.
By {lean}`propext`, {lean}`true = true` is equal to {lean}`True`, and {lean}`false = true` is equal to {lean}`False`.

:::

{lean}`Bool` は {lean}`Prop` が期待されているところではどこでも使うことができます。すべての {lean}`Bool` {lean}`b` から命題 {lean}`b = true` への {tech}[coercion] が存在します。 {lean}`propext` により、 {lean}`true = true` は {lean}`True` に、 {lean}`false = true` は {lean}`False` にそれぞれ等しいです。

:::comment
Not every proposition can be used by programs to make run-time decisions.
Otherwise, a program could branch on whether the Collatz conjecture is true or false!
Many propositions, however, can be checked algorithmically.
These propositions are called {tech}_decidable_ propositions, and have instances of the {lean}`Decidable` type class.
The function {name}`Decidable.decide` converts a proof-carrying {lean}`Decidable` result into a {lean}`Bool`.
This function is also a coercion from decidable propositions to {lean}`Bool`, so {lean}`(2 = 2 : Bool)` evaluates to {lean}`true`.

:::

全ての命題をプログラムがランタイム時の判断に使えるわけではありません。そうでなければコラッツ予想が真か偽かでプログラムが分岐してしまいます！しかし、多くの命題はアルゴリズムでチェックすることができます。これらの命題は {tech}_決定可能_ な命題と呼ばれ、 {lean}`Decidable` 型クラスを持ちます。関数 {name}`Decidable.decide` は証明を格納した {lean}`Decidable` の結果を {lean}`Bool` に変換します。この関数は決定可能な命題から {lean}`Bool` への強制演算でもあるため、 {lean}`(2 = 2 : Bool)` は {lean}`true` と評価されます。

```lean (show := false)
/-- info: true -/
#guard_msgs in
#eval (2 = 2 : Bool)
end BoolProp
```

:::comment
## Syntax
:::

## 構文（Syntax）


::::syntax term
:::comment
The infix operators `&&`, `||`, and `^^` are notations for {lean}`Bool.and`, {lean}`Bool.or`, and {lean}`Bool.xor`, respectively.

:::

中置演算子 `&&` ・ `||` ・ `^^` はそれぞれ {lean}`Bool.and` ・ {lean}`Bool.or` ・ {lean}`Bool.xor` の表記です。

```grammar
$_:term && $_:term
```
```grammar
$_:term || $_:term
```
```grammar
$_:term ^^ $_:term
```
::::

::::syntax term
:::comment
The prefix operator `!` is notation for {lean}`Bool.not`.
:::

前置演算子 `!` は {lean}`Bool.not` の表記です。

```grammar
!$_:term
```
::::


:::comment
## API Reference
:::

## API リファレンス（API Reference）


:::comment
### Logical Operations
:::

### 論理演算子（Logical Operations）


```lean (show := false)
section ShortCircuit

axiom BIG_EXPENSIVE_COMPUTATION : Bool
```

:::comment
The functions {name}`cond`, {name Bool.and}`and`, and {name Bool.or}`or` are short-circuiting.
In other words, {lean}`false && BIG_EXPENSIVE_COMPUTATION` does not need to execute {lean}`BIG_EXPENSIVE_COMPUTATION` before returning `false`.
These functions are defined using the {attr}`macro_inline` attribute, which causes the compiler to replace calls to them with their definitions while generating code, and the definitions use nested pattern matching to achieve the short-circuiting behavior.

:::

関数 {name}`cond` ・ {name Bool.and}`and` ・ {name Bool.or}`or` は短絡します。つまり、 {lean}`false && BIG_EXPENSIVE_COMPUTATION` は `false` を返す前に {lean}`BIG_EXPENSIVE_COMPUTATION` を実行する必要はありません。これらの関数は {attr}`macro_inline` 属性を使用して定義されています。これによりコンパイラはコードを生成する際に関数の呼び出しを定義に置き換え、入れ子のパターンマッチを用いる定義が短絡評価されるようになります。

```lean (show := false)
end ShortCircuit
```


{docstring cond}

{docstring Bool.not}

{docstring Bool.and}

{docstring Bool.or}

{docstring Bool.xor}

{docstring Bool.atLeastTwo}

:::comment
### Comparisons
:::

### 比較（Comparisons）


{docstring Bool.decEq}

:::comment
### Conversions
:::

### 変換（Conversions）


{docstring Bool.toISize}

{docstring Bool.toUInt8}

{docstring Bool.toUInt16}

{docstring Bool.toUInt32}

{docstring Bool.toUInt64}

{docstring Bool.toUSize}

{docstring Bool.toInt8}

{docstring Bool.toInt16}

{docstring Bool.toInt32}

{docstring Bool.toInt64}

{docstring Bool.toNat}


{include 0 Manual.BasicTypes.Option}

# Tuples
%%%
tag := "tuples"
%%%

:::planned 171
Describe {name}`Prod` and {name}`PProd`, their syntax and API
:::

{docstring Prod}

{docstring PProd}

{docstring MProd}

# Sum Types
%%%
tag := "sum-types"
%%%

:::planned 172
Describe {name}`Sum` and {name}`PSum`, their syntax and API
:::

{docstring Sum}

{docstring PSum}

# Dependent Pairs
%%%
tag := "sigma-types"
%%%

:::planned 176
Describe {name}`Sigma` and {name}`PSigma`, their syntax and API. What is the relationship to {lean}`Subtype` and {lean}`Exists`?
:::

{docstring Sigma}

{docstring PSigma}

# Linked Lists
%%%
tag := "List"
%%%


::: planned 108
 * Representation at compile time and run time
 * API reference
 * Literal syntax
 * Constructor/pattern syntax
:::

{docstring List}

{include 0 Manual.BasicTypes.Array}

# Subtypes

:::planned 173
 * When to use them?
 * Run-time representation
:::

{docstring Subtype}

# Lazy Computations
%%%
tag := "Thunk"
%%%


::: planned 92
Description and API reference for {name}`Thunk`:
 * Logical model as wrapper around a function from {lean}`Unit`
 * Run-time realization as a lazy computation
 * API reference
:::

# Tasks and Threads
%%%
tag := "concurrency"
%%%


::: planned 90
Description and API reference for {name}`Task` and runtime threads, including {lean}`IO.Promise`

 * Scheduling model
 * Things to be careful of

This section may be moved to the section on {name}`IO` in particular.
:::
