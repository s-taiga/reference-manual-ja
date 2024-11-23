/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual

/-
#doc (Manual) "Natural Numbers" =>
-/
#doc (Manual) "自然数（Natural Numbers）" =>
%%%
tag := "Nat"
%%%

:::comment
The natural numbers are nonnegative integers.
Logically, they are the numbers 0, 1, 2, 3, …, generated from the constructors {lean}`Nat.zero` and {lean}`Nat.succ`.
Lean imposes no upper bound on the representation of natural numbers other than physical constraints imposed by the available memory of the computer.

:::

自然数は非負の整数です。論理的には 0・1・2・3・……であり、コンストラクタ {lean}`Nat.zero` と {lean}`Nat.succ` から生成されます。Lean はコンピュータの利用可能なメモリによって課される物理的制約以外に、自然数の表現に上限を課していません。

:::comment
Because the natural numbers are fundamental to both mathematical reasoning and programming, they are specially supported by Lean's implementation. The logical model of the natural numbers is as an {tech}[inductive type], and arithmetic operations are specified using this model. In Lean's kernel, the interpreter, and compiled code, closed natural numbers are represented as efficient arbitrary-precision integers. Sufficiently small numbers are immediate values that don't require indirection through a pointer. Arithmetic operations are implemented by primitives that take advantage of the efficient representations.

:::

自然数は数学的推論とプログラミングの基本であるため、Lean の実装では特別なサポートを受けています。自然数の論理モデルは {tech}[帰納型] であり、算術演算はこのモデルを用いて指定されます。Lean のカーネル・インタプリタ・コンパイルされたコードでは、閉じた自然数は効率的な任意精度の整数として表現されます。十分に小さい数値はポインタによるインダイレクトを必要としない即値です。算術演算は効率的な表現を利用するプリミティブによって実装されます。

:::comment
# Logical Model
%%%
tag := "nat-model"
%%%


:::

# 論理モデル（Logical Model）

{docstring Nat}

:::comment
The Peano axioms are a consequence of this definition.
The induction principle generated for {lean}`Nat` is the one demanded by the axiom of induction:
:::

ペアノの公理はこの定義の帰結です。 {lean}`Nat` に対して生成される帰納原理は、帰納の公理が要求するものです。

```signature
Nat.rec.{u} {motive : Nat → Sort u}
  (zero : motive zero)
  (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat) :
  motive t
```
:::comment
This induction principle also implements primitive recursion.
The injectivity of {lean}`Nat.succ` and the disjointness of {lean}`Nat.succ` and `Nat.zero` are consequences of the induction principle, using a construction typically called “no confusion”:
:::

この帰納原理は原始再帰も実装しています。 {lean}`Nat.succ` の単射性、 {lean}`Nat.succ` と `Nat.zero` の不連結性は一般的に「no confusion」と呼ばれる構造を用いた帰納原理の帰結です：

```lean
def NoConfusion : Nat → Nat → Prop
  | 0, 0 => True
  | 0, _ + 1 | _ + 1, 0 => False
  | n + 1, k + 1 => n = k

theorem noConfusionDiagonal (n : Nat) : NoConfusion n n :=
  Nat.rec True.intro (fun _ _ => rfl) n

theorem noConfusion (n k : Nat) (eq : n = k) : NoConfusion n k :=
  eq ▸ noConfusionDiagonal n

theorem succ_injective : n + 1 = k + 1 → n = k := noConfusion (n + 1) (k + 1)

theorem succ_not_zero : ¬n + 1 = 0 := noConfusion (n + 1) 0
```

# Run-Time Representation
%%%
tag := "nat-runtime"
%%%


:::TODO

Look up and document

:::

:::comment
## Performance Notes
%%%
tag := "nat-performance"
%%%


:::

## パフォーマンスについての注記（Performance Notes）

:::comment
Using Lean's built-in arithmetic operators, rather than redefining them, is essential.
The logical model of {lean}`Nat` is essentially a linked list, so addition would take time linear in the size of one argument.
Still worse, multiplication takes quadratic time in this model.
While defining arithmetic from scratch can be a useful learning exercise, these redefined operations will not be nearly as fast.

:::

演算子について再定義せずに Lean の組み込み演算子を利用することが重要です。 {lean}`Nat` の論理モデルは基本的に連結リストであるため、足し算には引数のサイズに対して線形な時間がかかります。さらに悪いことに、このモデルでは掛け算に2乗の時間がかかります。0から算術演算を定義することは有用な学習の練習にはなりますが、これらの再定義された演算はほとんど速くなりません。

:::comment
# Syntax
%%%
tag := "nat-syntax"
%%%


:::

# 構文（Syntax）

:::comment
Natural number literals are overridden using the {lean}`OfNat` type class.

:::

自然数リテラルは {lean}`OfNat` 型クラスを使って上書きされます。

:::TODO
Document this elsewhere, insert a cross-reference here
:::


:::comment
# API Reference
%%%
tag := "nat-api"
%%%


:::

# API リファレンス（API Reference）

:::comment
## Arithmetic
%%%
tag := "nat-api-arithmetic"
%%%

:::

## 算術（Arithmetic）

{docstring Nat.pred}

{docstring Nat.add}

{docstring Nat.sub}

{docstring Nat.mul}

{docstring Nat.div}

{docstring Nat.mod}

{docstring Nat.modCore}

{docstring Nat.pow}

{docstring Nat.log2}

:::comment
### Bitwise Operations
%%%
tag := "nat-api-bitwise"
%%%

:::

### ビット演算（Bitwise Operations）

{docstring Nat.shiftLeft}

{docstring Nat.shiftRight}

{docstring Nat.xor}

{docstring Nat.lor}

{docstring Nat.land}

{docstring Nat.bitwise}

{docstring Nat.testBit}

:::comment
## Minimum and Maximum
%%%
tag := "nat-api-minmax"
%%%


:::

## 最小・最大（Minimum and Maximum）

{docstring Nat.min}

{docstring Nat.max}

{docstring Nat.imax}

:::comment
## GCD and LCM
%%%
tag := "nat-api-gcd-lcm"
%%%


:::

## 最大公約数と最小公倍数（GCD and LCM）

{docstring Nat.gcd}

{docstring Nat.lcm}

:::comment
## Powers of Two
%%%
tag := "nat-api-pow2"
%%%


:::

## 2の累乗（Powers of Two）

{docstring Nat.isPowerOfTwo}

{docstring Nat.nextPowerOfTwo}

:::comment
## Comparisons
%%%
tag := "nat-api-comparison"
%%%


:::

## 比較（Comparisons）

:::comment
### Boolean Comparisons
%%%
tag := "nat-api-comparison-bool"
%%%


:::

### 真偽値の比較（Boolean Comparisons）

{docstring Nat.beq}

{docstring Nat.ble}

{docstring Nat.blt}

:::comment
### Decidable Equality
%%%
tag := "nat-api-deceq"
%%%

:::

### 決定的な等価性（Decidable Equality）

{docstring Nat.decEq}

{docstring Nat.decLe}

{docstring Nat.decLt}

:::comment
### Predicates
%%%
tag := "nat-api-predicates"
%%%

:::

### 述語（Predicates）

{docstring Nat.le}

{docstring Nat.lt}

{docstring Nat.lt_wfRel}

:::comment
## Iteration
%%%
tag := "nat-api-iteration"
%%%

:::

## 反復（Iteration）

:::comment
Many iteration operators come in two versions: a structurally recursive version and a tail-recursive version.
The structurally recursive version is typically easier to use in contexts where definitional equality is important, as it will compute when only some prefix of a natural number is known.

:::

多くの反復演算子には、構造的再帰バージョンと末尾再帰バージョンの2種類があります。構造的再帰バージョンは自然数の接頭辞のみが分かっている場合に計算されるため、定義上の等価性が重要な文脈では一般的に使いやすいです。

{docstring Nat.repeat}

{docstring Nat.repeatTR}

{docstring Nat.fold}

{docstring Nat.foldTR}

{docstring Nat.foldM}

{docstring Nat.foldRev}

{docstring Nat.foldRevM}

{docstring Nat.forM}

{docstring Nat.forRevM}

{docstring Nat.all}

{docstring Nat.allTR}

{docstring Nat.any}

{docstring Nat.anyTR}

{docstring Nat.allM}

{docstring Nat.anyM}

:::comment
## Conversion
%%%
tag := "nat-api-conversion"
%%%

:::

## 変換（Conversion）

{docstring Nat.toUInt8}

{docstring Nat.toUInt16}

{docstring Nat.toUInt32}

{docstring Nat.toUInt64}

{docstring Nat.toUSize}

{docstring Nat.toFloat}

{docstring Nat.isValidChar}

{docstring Nat.repr}

{docstring Nat.toDigits}

{docstring Nat.toDigitsCore}

{docstring Nat.digitChar}

{docstring Nat.toSubscriptString}

{docstring Nat.toSuperscriptString}

{docstring Nat.toSuperDigits}

{docstring Nat.toSubDigits}

{docstring Nat.subDigitChar}

{docstring Nat.superDigitChar}

:::comment
### Metaprogramming and Internals
%%%
tag := "nat-api-meta"
%%%

:::

### メタプログラミングと内部（Metaprogramming and Internals）

{docstring Nat.fromExpr?}

{docstring Nat.toLevel}

:::comment
## Casts
%%%
tag := "nat-api-cast"
%%%


:::

## キャスト（Casts）

{docstring NatCast}

{docstring Nat.cast}

:::comment
## Elimination
%%%
tag := "nat-api-elim"
%%%


:::

## 除去（Elimination）

:::comment
The recursion principle that is automatically generated for {lean}`Nat` results in proof goals that are phrased in terms of {lean}`Nat.zero` and {lean}`Nat.succ`.
This is not particularly user-friendly, so an alternative logically-equivalent recursion principle is provided that results in goals that are phrased in terms of {lean}`0` and `n + 1`.

:::

{lean}`Nat` に対して自動的に生成される再帰原理は、 {lean}`Nat.zero` と {lean}`Nat.succ` で表現される証明ゴールをもたらします。これは特にユーザフレンドリではないため、 {lean}`0` と `n + 1` で表現されたゴールとなる論理的に同値な別の再帰原理が提供されます。

:::TODO
Insert reference to section on how to do this
:::

{docstring Nat.rec}

{docstring Nat.recOn}

{docstring Nat.casesOn}

{docstring Nat.below}

{docstring Nat.noConfusionType}

{docstring Nat.noConfusion}

{docstring Nat.ibelow}

{docstring Nat.elimOffset}

:::comment
### Alternative Induction Principles
%%%
tag := "nat-api-induction"
%%%


:::

### 代替の帰納原理（Alternative Induction Principles）

{docstring Nat.strongInductionOn}

{docstring Nat.caseStrongInductionOn}

{docstring Nat.div.inductionOn}

{docstring Nat.div2Induction}

{docstring Nat.mod.inductionOn}

:::comment
# Simplification
:::

# 単純化（Simplification）
%%%
tag := "nat-simp"
%%%


{docstring Nat.isValue}

{docstring Nat.reduceUnary}

{docstring Nat.reduceBin}

{docstring Nat.reduceBinPred}

{docstring Nat.reduceBoolPred}

{docstring Nat.reduceSucc}

{docstring Nat.reduceAdd}

{docstring Nat.reduceSub}

{docstring Nat.reduceMul}

{docstring Nat.reducePow}

{docstring Nat.reduceDiv}

{docstring Nat.reduceMod}

{docstring Nat.reduceGcd}

{docstring Nat.reduceLT}

{docstring Nat.reduceLTLE}

{docstring Nat.reduceLeDiff}

{docstring Nat.reduceSubDiff}

{docstring Nat.reduceGT}

{docstring Nat.reduceBEq}

{docstring Nat.reduceBeqDiff}

{docstring Nat.reduceBneDiff}

{docstring Nat.reduceEqDiff}

{docstring Nat.reduceBNe}

{docstring Nat.reduceNatEqExpr}

{docstring Nat.applyEqLemma}

{docstring Nat.applySimprocConst}
