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
#doc (Manual) "Identity" =>
-/
#doc (Manual) "恒等モナド（Identity）" =>

:::comment
The identity monad {name}`Id` has no effects whatsoever.
Both {name}`Id` and the corresponding implementation of {name}`pure` are the identity function, and {name}`bind` is reversed function application.
The identity monad has two primary use cases:
 1. It can be the type of a {keywordOf Lean.Parser.Term.do}`do` block that implements a pure function with local effects.
 2. It can be placed at the bottom of a stack of monad transformers.

:::

恒等モナド {name}`Id` は何の作用も持ちません。 {name}`Id` と対応する {name}`pure` の実装はどちらも恒等関数であり、 {name}`bind` は関数適用を逆転させたものです。恒等モナドには主に2つの使用例があります：
 1. {keywordOf Lean.Parser.Term.do}`do` ブロックの型にして、局所的に作用を持つ純粋関数を実装することができます。
 2. モナド変換子のスタックの一番下に置くことができます。

```lean (show := false)
-- Verify claims
example : Id = id := rfl
example : Id.run (α := α) = id := rfl
example : (pure (f := Id)) = (id : α → α) := rfl
example : (bind (m := Id)) = (fun (x : α) (f : α → Id β) => f x) := rfl
```

{docstring Id}

{docstring Id.run}

:::comment
::example "Local Effects with the Identity Monad"
:::
::::example "恒等モナドによる局所的な作用"
:::comment
This code block implements a countdown procedure by using simulated local mutability in the identity monad.
:::

このコードブロックは恒等モナドのシミュレートされた局所的な可変性を使ってカウントダウン処理を実装しています。

```lean (name := idDo)
#eval Id.run do
  let mut xs := []
  for x in [0:10] do
    xs := x :: xs
  pure xs
```
```leanOutput idDo
[9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
```
::::

{docstring Id.hasBind}
