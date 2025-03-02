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
#doc (Manual) "Finite Natural Numbers" =>
-/
#doc (Manual) "有限な自然数" =>
%%%
tag := "Fin"
%%%

```lean (show := false)
section
variable (n : Nat)
```

:::comment
For any {tech}[natural number] {lean}`n`, the {lean}`Fin n` is a type that contains all the natural numbers that are strictly less than {lean}`n`.
In other words, {lean}`Fin n` has exactly {lean}`n` elements.
It can be used to represent the valid indices into a list or array, or it can serve as a canonical {lean}`n`-element type.

:::

任意の {tech}[自然数] {lean}`n` に対して、 {lean}`Fin n` は {lean}`n` より狭義に小さいすべての自然数を含む型です。言い換えると、 {lean}`Fin n` はちょうど {lean}`n` 個の要素を持ちます。この型はリストや配列への有効なインデックスの表現や、標準的な {lean}`n` 個の要素を持つ型として使用することができます。

{docstring Fin}

:::comment
{lean}`Fin` is closely related to {name}`UInt8`, {name}`UInt16`, {name}`UInt32`, {name}`UInt64`, and {name}`USize`, which also represent finite non-negative integral types.
However, these types are backed by bitvectors rather than by natural numbers, and they have fixed bounds.
{lean}`Fin` is comparatively more flexible, but also less convenient for low-level reasoning.
In particular, using bitvectors rather than proofs that a number is less than some power of two avoids needing to take care to avoid evaluating the concrete bound.

:::

{lean}`Fin` は、同じく有限の非負整数型を表す {name}`UInt8` ・ {name}`UInt16` ・ {name}`UInt32` ・ {name}`UInt64` ・ {name}`USize` と密接に関連しています。ただし、これらの型は自然数ではなくビットベクタが背後にあり、固定の境界を持ちます。これらに対して {lean}`Fin` は比較的柔軟ですが、低レベルの推論にはあまり便利ではありません。特に、ある数が2のべき乗より小さいという証明ではなくビットベクタを使用することで、具体的な境界を評価しないように注意する必要がなくなります。

:::comment
# Run-Time Characteristics
:::

# ランタイムの特徴（Run-Time Characteristics）

:::comment
Because {lean}`Fin n` is a structure in which only a single field is not a proof, it is a {ref "inductive-types-trivial-wrappers"}[trivial wrapper].
This means that it is represented identically to the underlying natural number in compiled code.

:::

{lean}`Fin n` は証明ではないただ1つのフィールドを持つ構造体であるため、 {ref "inductive-types-trivial-wrappers"}[自明なラッパ] です。これはコンパイルされたコードではベースの自然数と同じように表現されることを意味します。

:::comment
# Coercions and Literals
:::

# 強制とリテラル（Coercions and Literals）

:::comment
There is a {tech}[coercion] from {lean}`Fin n` to {lean}`Nat` that discards the proof that the number is less than the bound.
In particular, this coercion is precisely the projection {name}`Fin.val`.
One consequence of this is that uses of {name}`Fin.val` are displayed as coercions rather than explicit projections in proof states.
:::

{lean}`Fin n` には {lean}`Nat` への {tech}[coercion] があり、その数値が境界より小さいことの証明を破棄します。特に、この強制はまさに射影 {name}`Fin.val` です。これによって、 {name}`Fin.val` を使用すると証明状態において、明示的な射影ではなく強制として表示されます。

:::comment
::example "Coercing from {name}`Fin` to {name}`Nat`"
:::
::::example "{name}`Fin` から {name}`Nat` への強制"
:::comment
A {lean}`Fin n` can be used where a {lean}`Nat` is expected:
:::

{lean}`Nat` が期待される場合に {lean}`Fin n` を使うことができます：

```lean (name := oneFinCoe)
#eval let one : Fin 3 := ⟨1, by omega⟩; (one : Nat)
```
```leanOutput oneFinCoe
1
```

:::comment
Uses of {name}`Fin.val` show up as coercions in proof states:
:::

{name}`Fin.val` の使用は証明状態では強制として表示されます：

```proofState
∀(n : Nat) (i : Fin n), i < n := by
  intro n i
/--
n : Nat
i : Fin n
⊢ ↑i < n
-/

```
::::

:::comment
Natural number literals may be used for {lean}`Fin` types, implemented as usual via an {name}`OfNat` instance.
The {name}`OfNat` instance for {lean}`Fin n` requires that the upper bound {lean}`n` is not zero, but does not check that the literal is less than {lean}`n`.
If the literal is larger than the type can represent, the remainder when dividing it by {lean}`n` is used.

:::

自然数リテラルは {lean}`Fin` 型に用いることができます。これは {name}`OfNat` インスタンスによって通常通り実装されています。 {lean}`Fin n` の {name}`OfNat` インスタンスは、上界 {lean}`n` が0ではないことを要求しますが、リテラルが {lean}`n` より小さいかどうかはチェックしません。リテラルが型で表現されるものよりも大きい場合は、 {lean}`n` で割った余りが使用されます。

:::comment
::example "Numeric Literals for {name}`Fin`"
:::
::::example "{name}`Fin` の数値リテラル"

:::comment
If {lean}`n > 0`, then natural number literals can be used for {lean}`Fin n`:
:::

{lean}`n > 0` の場合、 {lean}`Fin n` には自然数リテラルを使うことができます：

```lean
example : Fin 5 := 3
example : Fin 20 := 19
```
:::comment
When the literal is greater than or equal to {lean}`n`, the remainder when dividing by {lean}`n` is used:
:::

リテラルが {lean}`n` 以上の場合、 {lean}`n` で割った余りが使われます：

```lean (name := fivethree)
#eval (5 : Fin 3)
```
```leanOutput fivethree
2
```
```lean (name := fourthree)
#eval ([0, 1, 2, 3, 4, 5, 6] : List (Fin 3))
```
```leanOutput fourthree
[0, 1, 2, 0, 1, 2, 0]
```

:::comment
If Lean can't synthesize an instance of {lean}`NeZero n`, then there is no {lean}`OfNat (Fin n)` instance:
:::

Lean が {lean}`NeZero n` のインスタンスを統合できない場合、 {lean}`OfNat (Fin n)` のインスタンスは存在しません：

```lean (error := true) (name := fin0)
example : Fin 0 := 0
```
```leanOutput fin0
failed to synthesize
  OfNat (Fin 0) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Fin 0
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

```lean (error := true) (name := finK)
example (k : Nat) : Fin k := 0
```
```leanOutput finK
failed to synthesize
  OfNat (Fin k) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Fin k
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

::::

:::comment
# API Reference
:::

# API リファレンス（API Reference）

:::comment
## Construction
:::

## 構成（Construction）

{docstring Fin.last}

{docstring Fin.succ}

{docstring Fin.pred}

:::comment
## Arithmetic
:::

## 算術（Arithmetic）

:::comment
Typically, arithmetic operations on {name}`Fin` should be accessed using Lean's overloaded arithmetic notation, particularly via the instances {inst}`Add (Fin n)`, {inst}`Sub (Fin n)`, {inst}`Mul (Fin n)`, {inst}`Div (Fin n)`,  and {inst}`Mod (Fin n)`.
Heterogeneous operators such as {lean}`Fin.natAdd` do not have corresponding heterogeneous instances (e.g. {name}`HAdd`) to avoid confusing type inference behavior.

:::

通常、 {name}`Fin` に対する算術操作は Lean のオーバーロードされた算術記法を用いてアクセスするべきであり、特に {inst}`Add (Fin n)` ・ {inst}`Sub (Fin n)` ・ {inst}`Mul (Fin n)` ・ {inst}`Div (Fin n)` ・ {inst}`Mod (Fin n)` のインスタンスを使用します。 {lean}`Fin.natAdd` のような heterogeneous な演算子は、型推論の動作の混乱を避けるために、対応する heterogeneous インスタンス（例えば {name}`HAdd` ）を持ちません。

{docstring Fin.add}

{docstring Fin.natAdd}

{docstring Fin.addNat}

{docstring Fin.mul}

{docstring Fin.sub}

{docstring Fin.subNat}

{docstring Fin.div}

{docstring Fin.mod}

{docstring Fin.modn}

{docstring Fin.log2}

:::comment
## Bitwise Operations
:::

## ビット演算（Bitwise Operations）

:::comment
Typically, bitwise operations on {name}`Fin` should be accessed using Lean's overloaded bitwise operators, particularly via the instances {inst}`ShiftLeft (Fin n)`, {inst}`ShiftRight (Fin n)`, {inst}`AndOp (Fin n)`, {inst}`OrOp (Fin n)`, {inst}`Xor (Fin n)`

:::

通常、 {name}`Fin` に対するビット演算は Lean のオーバーロードされたビット演算を用いてアクセスするべきであり、特に {inst}`ShiftLeft (Fin n)` ・ {inst}`ShiftRight (Fin n)` ・ {inst}`AndOp (Fin n)` ・ {inst}`OrOp (Fin n)` ・ {inst}`Xor (Fin n)` のインスタンスを使用します。

{docstring Fin.shiftLeft}

{docstring Fin.shiftRight}

{docstring Fin.land}

{docstring Fin.lor}

{docstring Fin.xor}


:::comment
## Conversions
:::

## 変換（Conversions）

{docstring Fin.ofNat'}

{docstring Fin.cast}

{docstring Fin.castAdd}

{docstring Fin.castLE}

{docstring Fin.castSucc}

{docstring Fin.castLT}

{docstring Fin.rev}

{docstring Fin.elim0}

:::comment
## Iteration
:::

## 反復（Iteration）

{docstring Fin.foldr}

{docstring Fin.foldrM}

{docstring Fin.foldl}

{docstring Fin.foldlM}

{docstring Fin.hIterate}

{docstring Fin.hIterateFrom}

:::comment
## Reasoning
:::

## 推論（Reasoning）

{docstring Fin.induction}

{docstring Fin.inductionOn}

{docstring Fin.reverseInduction}

{docstring Fin.cases}

{docstring Fin.lastCases}

{docstring Fin.addCases}

{docstring Fin.succRec}

{docstring Fin.succRecOn}

:::comment
## Proof Automation
:::

## 証明の自動化（Proof Automation）

{docstring Fin.isValue}

{docstring Fin.fromExpr?}

{docstring Fin.reduceOfNat'}

{docstring Fin.reduceSucc}

{docstring Fin.reduceAdd}

{docstring Fin.reduceNatOp}

{docstring Fin.reduceNatAdd}

{docstring Fin.reduceAddNat}

{docstring Fin.reduceSub}

{docstring Fin.reduceSubNat}

{docstring Fin.reduceMul}

{docstring Fin.reduceDiv}

{docstring Fin.reduceMod}

{docstring Fin.reduceBin}

{docstring Fin.reducePred}

{docstring Fin.reduceBinPred}

{docstring Fin.reduceBoolPred}

{docstring Fin.reduceBNe}

{docstring Fin.reduceEq}

{docstring Fin.reduceLT}

{docstring Fin.reduceGE}

{docstring Fin.reduceGT}

{docstring Fin.reduceLE}

{docstring Fin.reduceNe}

{docstring Fin.reduceBEq}

{docstring Fin.reduceRev}

{docstring Fin.reduceFinMk}

{docstring Fin.reduceXor}

{docstring Fin.reduceOp}

{docstring Fin.reduceAnd}

{docstring Fin.reduceOr}

{docstring Fin.reduceLast}

{docstring Fin.reduceShiftLeft}

{docstring Fin.reduceShiftRight}

{docstring Fin.reduceCastSucc}

{docstring Fin.reduceCastAdd}

{docstring Fin.reduceCastLT}

{docstring Fin.reduceCastLE}
