/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

/-
#doc (Manual) "The Empty Type" =>
-/
#doc (Manual) "空の型（The Empty Type）" =>
%%%
tag := "empty"
%%%

:::planned 170
 * What is {lean}`Empty`?
 * Contrast with {lean}`Unit` and {lean}`False`
 * Definitional equality
:::

:::comment
The empty type {name}`Empty` represents impossible values.
It is an inductive type with no constructors whatsoever.

:::

空の型 {name}`Empty` は不可能な値を表します。これはコンストラクタを一切持たない帰納型です。

:::comment
While the trivial type {name}`Unit`, which has a single constructor that takes no parameters, can be used to model computations where a result is unwanted or uninteresting, {name}`Empty` can be used in situations where no computation should be possible at all.
Instantiating a polymorphic type with {name}`Empty` can mark some of its constructors—those with a parameter of the corresponding type—as impossible; this can rule out certain code paths that are not desired.

:::

自明な型 {name}`Unit` はパラメータを取らないコンストラクタを1つ持ち、結果が不要であったり興味がないような計算をモデル化するために使用することができますが、 {name}`Empty` は計算が決して可能であってはならない状況で使用することができます。 {name}`Empty` で多相型をインスタンス化すると、そのコンストラクタの一部（対応する型のパラメータを持つコンストラクタ）を不可能なものとしてマークすることができます；これによってコード中の望ましくないパスを除外することができます。

:::comment
The presence of a term with type {name}`Empty` indicates that an impossible code path has been reached.
There will never be a value with this type, due to the lack of constructors.
On an impossible code path, there's no reason to write further code; the function {name}`Empty.elim` can be used to escape an impossible path.

:::

{name}`Empty` 型を持つ項が出現した場合、不可能なコードパスに到達したことを示します。コンストラクタがないため、この型の値が存在することはありません。不可能なコードパスでは、それ以降のコードを書くすべがありません； {name}`Empty.elim` 関数を使用することで、不可能なパスから抜け出すことができます。

:::comment
The universe-polymorphic equivalent of {name}`Empty` is {name}`PEmpty`.

:::

{name}`Empty` に相当する宇宙多相な型は {name}`PEmpty` です。

{docstring Empty}

{docstring PEmpty}


:::comment
::example "Impossible Code Paths"
:::
::::example "不可能なコードパス"

:::comment
The type signature of the function {lean}`f` indicates that it might throw exceptions, but allows the exception type to be anything:
:::

関数 {lean}`f` のシグネチャは例外を投げる可能性を示していますが、例外の型は何でも良いです：

```lean
def f (n : Nat) : Except ε Nat := pure n
```

:::comment
Instantiating {lean}`f`'s exception type with {lean}`Empty` exploits the fact that {lean}`f` never actually throws an exception to convert it to a function whose type indicates that no exceptions will be thrown.
In particular, it allows {lean}`Empty.elim` to be used to avoid handing the impossible exception value.

:::

{lean}`f` の例外の型を {lean}`Empty` でインスタンス化することで、 {lean}`f` が実際に決して例外を投げないことを利用して、例外が投げられないことを型が示す関数に変換します。特に、 {lean}`Empty.elim` を使用することで、不可能な例外の値を渡さないようにすることができます。

```lean
def g (n : Nat) : Nat :=
  match f (ε := Empty) n with
  | .error e =>
    Empty.elim e
  | .ok v => v
```
::::

:::comment
# API Reference
:::

# API リファレンス（API Reference）

{docstring Empty.elim}

{docstring PEmpty.elim}
