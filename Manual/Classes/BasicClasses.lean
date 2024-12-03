/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Manual
open Verso.Genre
open Verso.Genre.Manual

/-
#doc (Manual) "Basic Classes" =>
-/
#doc (Manual) "基本的なクラス（Basic Classes）" =>
%%%
tag := "basic-classes"
%%%

:::comment
Many Lean type classes exist in order to allow built-in notations such as addition or array indexing to be overloaded.

:::

Lean の型クラスの多くは、加算や配列インデックスのような組み込み記法をオーバーロードできるようにするために存在します。

:::comment
# Boolean Equality Tests

:::

# 真偽値上の等価性のテスト（Boolean Equality Tests）

{docstring BEq}

{docstring Hashable}

{docstring LawfulBEq}

:::comment
# Ordering

:::

# 順序（Ordering）

{docstring Ord}

{docstring Ordering}

{docstring LT}

{docstring LE}

:::comment
# Decidability
%%%
tag := "decidable-propositions"
%%%

:::

# 決定可能性（Decidability）

:::comment
A proposition is {deftech}_decidable_ if it can be checked algorithmically.{index}[decidable]{index subterm:="decidable"}[proposition]
The Law of the Excluded Middle means that every proposition is true or false, but it provides no way to check which of the two cases holds, which can often be useful.
By default, only algorithmic {lean}`Decidable` instances for which code can be generated are in scope; opening the `Classical` namespace makes every proposition decidable.

:::

アルゴリズム的にチェック可能である命題は {deftech}_決定可能_ （decidable）であると言います。 {index}[decidable]{index subterm:="decidable"}[proposition] 排中律は、すべての命題が真か偽であることを意味しますが、2つのケースのどちらが成り立つかをチェックする方法は提供しません。デフォルトでは、コードを生成できるアルゴリズム的な {lean}`Decidable` インスタンスのみがスコープに含まれます；`Classical` 名前空間を開くと、すべての命題が決定可能になります。

{docstring Decidable}

{docstring DecidableRel}

{docstring DecidableEq}

{docstring Decidable.decide}

{docstring Decidable.byCases}

:::::keepEnv
:::comment
::example "Excluded Middle and {lean}`Decidable`"
:::
::::example "排中律と {lean}`Decidable`"
:::comment
The equality of functions from {lean}`Nat` to {lean}`Nat` is not decidable:
:::

{lean}`Nat` から {lean}`Nat` への関数の等価性は決定不可能です：

```lean (error:=true) (name := NatFunNotDecEq)
example (f g : Nat → Nat) : Decidable (f = g) := inferInstance
```
```leanOutput NatFunNotDecEq
failed to synthesize
  Decidable (f = g)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

:::comment
Opening `Classical` makes every proposition decidable; however, declarations and examples that use this fact must be marked {keywordOf Lean.Parser.Command.declaration}`noncomputable` to indicate that code should not be generated for them.
:::

`Classical` を開くと、すえｂての命題が決定可能になります；しかし、この事実を使用する宣言と例には、コードを生成すべきでないことを示すために {keywordOf Lean.Parser.Command.declaration}`noncomputable` とマークしなければなりません。

```lean
open Classical
noncomputable example (f g : Nat → Nat) : Decidable (f = g) := inferInstance
```

::::
:::::


:::comment
# Inhabited Types

:::

# inhabited な型（Inhabited Types）

{docstring Inhabited}

{docstring Nonempty}

:::comment
# Visible Representations

:::

# 表現の可視化（Visible Representations）

:::planned 135

 * How to write a correct {name}`Repr` instance
 * {name}`ReprAtom`
 * Useful helpers, like {name}`Repr.addAppParen` and {name}`reprArg`
 * When to use {name}`Repr` vs {name}`ToString`
:::

{docstring Repr}

{docstring ToString}

:::comment
# Arithmetic and Bitwise Operators

:::

# 算術・ビット演算子（Arithmetic and Bitwise Operators）

{docstring Zero}

{docstring NeZero}

{docstring HAdd}

{docstring Add}

{docstring HSub}

{docstring Sub}

{docstring HMul}

{docstring Mul}

{docstring HDiv}

{docstring Div}

{docstring Dvd}

{docstring HMod}

{docstring Mod}

{docstring HPow}

{docstring Pow}

{docstring NatPow}

{docstring HomogeneousPow}

{docstring HShiftLeft}

{docstring ShiftLeft}

{docstring HShiftRight}

{docstring ShiftRight}

{docstring Neg}

{docstring HAnd}

{docstring HOr}

{docstring HXor}

:::comment
# Append

:::

# 結合（Append）

{docstring HAppend}

{docstring Append}

:::comment
# Data Lookups

:::

# データの検索（Data Lookups）

{docstring GetElem}

{docstring GetElem?}

{docstring LawfulGetElem}
