/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual

/-
#doc (Manual) "Integers" =>
-/
#doc (Manual) "整数" =>
%%%
tag := "Int"
%%%

:::comment
The integers are whole numbers, both positive and negative.
Integers are arbitrary-precision, limited only by the capability of the hardware on which Lean is running; for fixed-width integers that are used in programming and computer science, please see the {ref "fixed-ints"}[section on fixed-precision integers].

:::

整数は正負両方全体の数値です。整数は任意精度であり、Lean が動いているハードウェアの能力によってのみ制限されます；通常のプログラミングや計算機科学で使われる固定長整数については {ref "fixed-ints"}[固定長整数についての節] を参照してください。

:::comment
Integers are specially supported by Lean's implementation.
The logical model of the integers is based on the natural numbers: each integer is modeled as either a natural number or the negative successor of a natural number.
Operations on the integers are specified using this model, which is used in the kernel and in interpreted code.
In these contexts, integer code inherits the performance benefits of the natural numbers' special support.
In compiled code, integers are represented as efficient arbitrary-precision integers, and sufficiently small numbers are stored as unboxed values that don't require indirection through a pointer.
Arithmetic operations are implemented by primitives that take advantage of the efficient representations.

:::

Lean の実装において、整数は特別にサポートされています。整数の論理モデルは自然数に基づいています：各整数は自然数か自然数の負の後続としてモデル化されています。整数の演算はこのモデルを用いて指定されており、カーネルとインタプリタコードで使用されます。これらのコンテキストでは、整数のコードは自然数への特別なサポートによる性能上の利点を継承します。コンパイルされたコードでは、整数は効率的な任意精度整数として表現され、十分に小さい値はボックス化解除された値として格納され、ポインタを介したインダイレクトを必要としません。算術演算は、効率的な表現を利用するプリミティブによって実装されています。

:::comment
# Logical Model
:::

# 論理モデル（Logical Model）

%%%
tag := "int-model"
%%%
:::comment
Integers are represented either as a natural number or as the negation of the successor of a natural number.

:::

整数は自然数か自然数の負の後続として表現されています。

{docstring Int}

:::comment
This representation of the integers has a number of useful properties.
It is relatively simple to use and to understand.
Unlike a pair of a sign and a {lean}`Nat`, there is a unique representation for $`0`, which simplifies reasoning about equality.
Integers can also be represented as a pair of natural numbers in which one is subtracted from the other, but this requires a {ref "quotients"}[quotient type] to be well-behaved, and quotient types can be laborious to work with due to the need to prove that functions respect the equivalence relation.

:::

この整数の表現にはいくつかの便利な性質があります。これは使い方が比較的簡単であり、理解しやすいです。符号と {lean}`Nat` のペアとは異なり、 $`0` には一意な表現があるため、等号に関する推論が簡単になります。整数は片方から他方を引くような自然数のペアとして表現することも可能ですが、この場合は {ref "quotients"}[商の型] をうまく扱う必要があり、商の型は関数が同値関係に従うことを証明する必要があるため、扱いに手間がかかります。

:::comment
# Run-Time Representation
:::

# ランタイム表現（Run-Time Representation）

%%%
tag := "int-runtime"
%%%

:::comment
Like {ref "nat-runtime"}[natural numbers], sufficiently-small integers are represented as unboxed values: the lowest-order bit in an object pointer is used to indicate that the value is not, in fact, a pointer.
If an integer is too large to fit in the remaining bits, it is instead allocated as an ordinary Lean object that consists of an object header and an arbitrary-precision integer.

:::

{ref "nat-runtime"}[自然数] と同様に、十分に小さい整数はボックス化解除された値として表現されます：オブジェクトのポインタの最下位ビットは値が実際にポインタではないかどうかを示すために使用されます。整数が残りのビットに収まらないほど大きすぎる場合、代わりにオブジェクトヘッダと任意精度の整数からなる通常の Lean オブジェクトとして割り当てられます。

:::comment
# Syntax
:::

# 構文（Syntax）

%%%
tag := "int-syntax"
%%%

```lean (show := false)
section
variable (n : Nat)
```

:::comment
The {lean}`OfNat Int` instance allows numerals to be used as literals, both in expression and in pattern contexts.
{lean}`(OfNat.ofNat n : Int)` reduces to the constructor application {lean}`Int.ofNat n`.
The {inst}`Neg Int` instance allows negation to be used as well.

:::

{lean}`OfNat Int` インスタンスによって、式とパターンの両方のコンテキストで数値をリテラルとして使用することができます。 {lean}`(OfNat.ofNat n : Int)` はコンストラクタの適用 {lean}`Int.ofNat n` に簡約されます。 {inst}`Neg Int` インスタンスによって負の値も使用できます。

```lean (show := false)
open Int
```

:::comment
On top of these instances, there is special syntax for the constructor {lean}`Int.negSucc` that is available when the `Int` namespace is opened.
The notation {lean}`-[ n +1]` is suggestive of $`-(n + 1)`, which is the meaning of {lean}`Int.negSucc n`.

:::

これらのインスタンスに加え、コンストラクタ {lean}`Int.negSucc` には `Int` 名前空間を開いたときにのみ使用できる特別な構文があります。 {lean}`-[ n +1]` という記法は $`-(n + 1)` を示唆するものであり、 {lean}`Int.negSucc n` を意味します。

::::syntax term (title := "Negative Successor")

:::comment
{lean}`-[ n +1]` is notation for {lean}`Int.negSucc n`.

:::

{lean}`-[ n +1]` は {lean}`Int.negSucc n` を表す記法です。

```grammar
-[ $_ +1]
```
::::

```lean (show := false)
end
```


:::comment
# API Reference
:::

# API リファレンス（API Reference）

:::comment
## Properties
:::

## 性質（Properties）

{docstring Int.sign}

:::comment
## Conversions
:::

## 変換（Conversions）

{docstring Int.natAbs}

{docstring Int.toNat}

{docstring Int.toNat'}

{docstring Int.toISize}

{docstring Int.toInt16}

{docstring Int.toInt32}

{docstring Int.toInt64}

{docstring Int.toInt8}

{docstring Int.repr}

:::comment
### Casts
:::

### キャスト（Casts）

{docstring IntCast}

{docstring Int.cast}

:::comment
## Arithmetic
:::

## 算術（Arithmetic）

:::comment
Typically, arithmetic operations on integers are accessed using Lean's overloaded arithmetic notation.
In particular, the instances of {inst}`Add Int`, {inst}`Neg Int`, {inst}`Sub Int`, and {inst}`Mul Int` allow ordinary infix operators to be used.
{ref "int-div"}[Division] is somewhat more intricate, because there are multiple sensible notions of division on integers.

:::

通常、整数に対する算術操作は Lean のオーバーロードされた算術記法を用いてアクセスします。特に、 {inst}`Add Int` ・ {inst}`Neg Int` ・ {inst}`Sub Int` ・ and {inst}`Mul Int` インスタンスによって通常の中置演算子を使うことができます。 {ref "int-div"}[除算] は、整数の除算に複数の意味があるため、やや複雑です。

{docstring Int.add}

{docstring Int.sub}

{docstring Int.subNatNat}

{docstring Int.neg}

{docstring Int.negOfNat}

{docstring Int.mul}

{docstring Int.pow}

{docstring Int.gcd}

{docstring Int.lcm}

:::comment
### Division
:::

### 除算（Division）

%%%
tag := "int-div"
%%%
:::comment
The {inst}`Div Int` and {inst}`Mod Int` instances implement Euclidean division, described in the reference for {name}`Int.ediv`.
This is not, however, the only sensible convention for rounding and remainders in division.
Four pairs of division and modulus functions are available, implementing various conventions.

:::

{inst}`Div Int` と {inst}`Mod Int` のインスタンスは {name}`Int.ediv` のリファレンスで説明されているユークリッド除算を実装しています。しかし、これは除算における丸めや余りのための唯一の賢明な慣習ではありません。除算と剰余の関数の4つのペアが利用可能であり、さまざまな慣習を実装しています。

:::comment
::example "Division by 0"
:::
::::example "ゼロ除算"
:::comment
In all integer division conventions, division by {lean type:="Int"}`0` is defined to be {lean type:="Int"}`0`:

:::

すべての整数の除算の慣習において、 {lean type:="Int"}`0` による除算は {lean type:="Int"}`0` として定義されます：

```lean (name := div0)
#eval Int.ediv 5 0
#eval Int.ediv 0 0
#eval Int.ediv (-5) 0
#eval Int.bdiv 5 0
#eval Int.bdiv 0 0
#eval Int.bdiv (-5) 0
#eval Int.fdiv 5 0
#eval Int.fdiv 0 0
#eval Int.fdiv (-5) 0
#eval Int.tdiv 5 0
#eval Int.tdiv 0 0
#eval Int.tdiv (-5) 0
```
:::comment
All evaluate to 0.
:::

すべて 0 に評価されます。

```leanOutput div0
0
```
::::

{docstring Int.ediv}

{docstring Int.emod}

{docstring Int.bdiv}

{docstring Int.bmod}

{docstring Int.fdiv}

{docstring Int.fmod}

{docstring Int.tdiv}

{docstring Int.tmod}

:::comment
## Bitwise Operators
:::

## ビット演算子（Bitwise Operators）

:::comment
Bitwise operators on {name}`Int` can be understood as bitwise operators on an infinite stream of bits that are the twos-complement representation of integers.

:::

{name}`Int` に対するビット演算子は、整数の 2 の補数表現であるビットの無限ストリームに対するビット演算子として理解されます。

{docstring Int.not}

{docstring Int.shiftRight}

:::comment
## Comparisons
:::

## 比較（Comparisons）

:::comment
Equality and inequality tests on {lean}`Int` are typically performed using the decidability of its equality and ordering relations or using the {inst}`BEq Int` and {inst}`Ord Int` instances.

:::

{lean}`Int` の等式と不等式のテストは通常、その等式の順序関係の決定可能性を使用するか、 {inst}`BEq Int` と {inst}`Ord Int` インスタンスを使用して実行されます。

```lean (show := false)
example (i j : Int) : Decidable (i ≤ j) := inferInstance
example (i j : Int) : Decidable (i < j) := inferInstance
example (i j : Int) : Decidable (i = j) := inferInstance
```

{docstring Int.le}

{docstring Int.lt}

{docstring Int.decEq}

:::comment
## Proof Automation
:::

## 証明の自動化（Proof Automation）

:::comment
The functions in this section are primarily parts of the implementation of simplification rules employed by {tactic}`simp`.
They are probably only of interest to users who are implementing custom proof automation that involves integers.


:::

本節の関数は主に {tactic}`simp` で採用される単純化規則の実装の一部です。これらはおそらく、整数を含むカスタムの証明自動化を実装しているユーザにとっては興味深いものになるでしょう。

{docstring Int.fromExpr?}

{docstring Int.isPosValue}

{docstring Int.reduceAbs}

{docstring Int.reduceAdd}

{docstring Int.reduceBEq}

{docstring Int.reduceBNe}

{docstring Int.reduceBdiv}

{docstring Int.reduceBin}

{docstring Int.reduceBinIntNatOp}

{docstring Int.reduceBinPred}

{docstring Int.reduceBmod}

{docstring Int.reduceBoolPred}

{docstring Int.reduceDiv}

{docstring Int.reduceEq}

{docstring Int.reduceFDiv}

{docstring Int.reduceFMod}

{docstring Int.reduceGE}

{docstring Int.reduceGT}

{docstring Int.reduceLE}

{docstring Int.reduceLT}

{docstring Int.reduceMod}

{docstring Int.reduceMul}

{docstring Int.reduceNatCore}

{docstring Int.reduceNe}

{docstring Int.reduceNeg}

{docstring Int.reduceNegSucc}

{docstring Int.reduceOfNat}

{docstring Int.reducePow}

{docstring Int.reduceSub}

{docstring Int.reduceTDiv}

{docstring Int.reduceTMod}

{docstring Int.reduceToNat}

{docstring Int.reduceUnary}
