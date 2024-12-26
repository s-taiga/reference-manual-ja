/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

/-
#doc (Manual) "API Reference" =>
-/
#doc (Manual) "API リファレンス（API Reference）" =>

:::comment
In addition to the general functions described here, there are some functions that are conventionally defined as part of the API of in the namespace of each collection type:
 * `mapM` maps a monadic function.
 * `forM` maps a monadic function, throwing away the result.
 * `filterM` filters using a monadic predicate, returning the values that satisfy it.


:::

ここで説明する一般的な関数に加えて、各コレクション型の名前空間の API の一部として慣習的に定義されている関数がいくつかあります：
 * `mapM` はモナド関数をマップします。
 * `forM` はモナド関数をマップし、結果を捨てます。
 * `filterM` はモナド述語を使ってフィルタリングを行い、それを満たす値を返します。

:::comment
::example "Monadic Collection Operations"
:::
::::example "モナドのコレクションに対する操作"
:::comment
{name}`Array.filterM` can be used to write a filter that depends on a side effect.

:::

{name}`Array.filterM` を使用すると、副作用に依存したフィルタを書くことができます。

:::ioExample
```ioLean
def values := #[1, 2, 3, 5, 8]
def main : IO Unit := do
  let filtered ← values.filterM fun v => do
    repeat
      IO.println s!"Keep {v}? [y/n]"
      let answer := (← (← IO.getStdin).getLine).trim
      if answer == "y" then return true
      if answer == "n" then return false
    return false
  IO.println "These values were kept:"
  for v in filtered do
    IO.println s!" * {v}"
```
```stdin
y
n
oops
y
n
y
```
```stdout
Keep 1? [y/n]
Keep 2? [y/n]
Keep 3? [y/n]
Keep 3? [y/n]
Keep 5? [y/n]
Keep 8? [y/n]
These values were kept:
 * 1
 * 3
 * 8
```
:::
::::

:::comment
# Discarding Results
:::

# 結果の破棄（Discarding Results）


:::comment
The {name}`discard` function is especially useful when using an action that returns a value only for its side effects.

:::

{name}`discard` 関数は副作用のためだけに値を返すアクションを使うときに便利です。

{docstring discard}

:::comment
# Control Flow
:::

# フローの制御（Control Flow）


{docstring guard}

{docstring optional}

:::comment
# Lifting Boolean Operations
:::

# 真偽値演算子の持ち上げ（Lifting Boolean Operations）


{docstring andM}

{docstring orM}

{docstring notM}

:::comment
# Kleisli Composition
:::

# Kleisli 合成（Kleisli Composition）


:::comment
{deftech}_Kleisli composition_ is the composition of monadic functions, analogous to {name}`Function.comp` for ordinary functions.

:::

{deftech}_Kleisli 合成_ （Kleisli composition）はモナド関数の合成で、普通の関数の {name}`Function.comp` に似ています。

{docstring Bind.kleisliRight}

{docstring Bind.kleisliLeft}

:::comment
# Re-Ordered Operations
:::

# 並べ替え操作（Re-Ordered Operations）


:::comment
Sometimes, it can be convenient to partially apply a function to its second argument.
These functions reverse the order of arguments, making it this easier.

:::

関数の第2引数に関数を部分適用すると便利な場合があります。これらの関数は引数の順序を逆にすることでこれを簡単に行うことができます。

{docstring Functor.mapRev}

{docstring Bind.bindLeft}
