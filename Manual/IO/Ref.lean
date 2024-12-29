/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

/-
#doc (Manual) "Mutable References" =>
-/
#doc (Manual) "可変参照（Mutable References）" =>


:::comment
While ordinary {tech}[state monads] encode stateful computations with tuples that track the contents of the state along with the computation's value, Lean's runtime system also provides mutable references that are always backed by mutable memory cells.
Mutable references have a type {lean}`IO.Ref` that indicates that a cell is mutable, and reads and writes must be explicit.
{lean}`IO.Ref` is implemented using {lean}`ST.Ref`, so the entire {ref "mutable-st-references"}[{lean}`ST.Ref` API] may also be used with {lean}`IO.Ref`.

:::

通常の {tech}[状態モナド] は計算の値とともに状態の内容を追跡するタプルを使用して状態のある計算をエンコードしますが、Lean のランタイムシステムは、常に可変なメモリセルにバックアップされた可変参照も提供しています。可変参照は {lean}`IO.Ref` 型を持ちます。これによってセルが可変であることが示され、読み取りと書き込みは明示的に行う必要があります。 {lean}`IO.Ref` は {lean}`ST.Ref` を使って実装されているため、 {ref "mutable-st-references"}[{lean}`ST.Ref` API] をすべて {lean}`IO.Ref` と一緒に使うことができます。

{docstring IO.Ref}

{docstring IO.mkRef}



:::comment
# State Transformers
:::

# 状態変換（State Transformers）

%%%
tag := "mutable-st-references"
%%%


:::comment
Mutable references are often useful in contexts where arbitrary side effects are undesired.
They can give a significant speedup when Lean is unable to optimize pure operations into mutation, and some algorithms are more easily expressed using mutable references than with state monads.
Additionally, it has a property that other side effects do not have: if all of the mutable references used by a piece of code are created during its execution, and no mutable references from the code escape to other code, then the result of evaluation is deterministic.

:::

可変参照は恣意的な副作用が望ましくないコンテキストでしばしば有用です。こうした参照は Lean が純粋な演算をミューテーションに最適化できない場合に大幅なスピードアップをもたらすことが可能であり、状態モナドを使うよりも可変参照を使った方が簡単に表現できるアルゴリズムもあります。さらに可変参照には他の副作用にはない特性があります：コードの一部で使用されるすべての可変参照がその実行中に作成され、コードから他のコードに可変参照がエスケープされない場合、評価結果は決定論的です。

:::comment
The {lean}`ST` monad is a restricted version of {lean}`IO` in which mutable state is the only side effect, and mutable references cannot escape.{margin}[{lean}`ST` was first described by {citehere launchbury94}[].]
{lean}`ST` takes a type parameter that is never used to classify any terms.
The {lean}`runST` function, which allow escape from {lean}`ST`, requires that the {lean}`ST` action that is passed to it can instantiate this type parameter with _any_ type.
This unknown type does not exist except as a parameter to a function, which means that values whose types are “marked” by it cannot escape its scope.

:::

{lean}`ST` モナドは {lean}`IO` を副作用が可変状態だけにし、可変参照がエスケープしないように制限したバージョンです。 {margin}[{lean}`ST` は {citehere launchbury94}[] によって最初に記述されました。] {lean}`ST` は型パラメータを取りますが、その型パラメータはどの項の分類にも使用されません。 {lean}`ST` からのエスケープを可能にする {lean}`runST` 関数は、渡される {lean}`ST` アクションがこの型パラメータを _任意の_ 型でインスタンス化できることを要求します。この未知の型は関数のパラメータとして以外は存在しないため、この型によって「マーク」された値はそのスコープから逃れることができません。

{docstring ST}

{docstring runST}

:::comment
As with {lean}`IO` and {lean}`EIO`, there is also a variation of {lean}`ST` that takes a custom error type as a parameter.
Here, {lean}`ST` is analogous to {lean}`BaseIO` rather than {lean}`IO`, because {lean}`ST` cannot result in errors being thrown.

:::

{lean}`IO` や {lean}`EIO` と同様に、カスタムエラー型をパラメータとして受け取る {lean}`ST` のバリエーションも存在します。ここでは、 {lean}`ST` はエラーを投げることができないため、 {lean}`IO` より {lean}`BaseIO` に類似しています。

{docstring EST}

{docstring runEST}

{docstring ST.Ref}

{docstring ST.mkRef}

:::comment
## Reading and Writing
:::

## 読み込みと書き込み（Reading and Writing）


{docstring ST.Ref.get}

{docstring ST.Ref.set}

:::comment
::example "Data races with {name ST.Ref.get}`get` and {name ST.Ref.set}`set`"
:::
::::example "{name ST.Ref.get}`get` と {name ST.Ref.set}`set` のデータ競合"
:::ioExample
```ioLean
def main : IO Unit := do
  let balance ← IO.mkRef (100 : Int)

  let mut orders := #[]
  IO.println "Sending out orders..."
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      if cost < (← balance.get) then
        IO.sleep (← IO.rand 10 100).toUInt32
        balance.set ((← balance.get) - cost)
    orders := orders.push o

  -- Wait until all orders are completed
  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← balance.get) < 0 then
    IO.eprintln "Final balance is negative!"
  else
    IO.println "Final balance is zero or positive."
```
```stdout
Sending out orders...
```
```stderr
Final balance is negative!
```
:::
::::

{docstring ST.Ref.modify}

:::comment
::example "Avoiding data races with {name ST.Ref.modify}`modify`"
:::
::::example "{name ST.Ref.modify}`modify` によるデータ競合の回避"

:::comment
This program launches 100 threads.
Each thread simulates a purchase attempt: it generates a random price, and if the account balance is sufficient, it decrements it by the price.
The balance check and the computation of the new value occur in an atomic call to {name}`ST.Ref.modify`.

:::

このプログラムは100個のスレッドを起動します。各スレッドは購入をシミュレートします：ランダムな価格を生成し、口座の残高が十分であれば、その価格分だけ残高を減少させます。残高チェックと新しい値の計算は {name}`ST.Ref.modify` へのアトミックな呼び出しで行われます。

:::ioExample
```ioLean
def main : IO Unit := do
  let balance ← IO.mkRef (100 : Int)

  let mut orders := #[]
  IO.println "Sending out orders..."
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      balance.modify fun b =>
        if cost < b then
          b - cost
        else b
    orders := orders.push o

  -- Wait until all orders are completed
  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← balance.get) < 0 then
    IO.eprintln "Final balance negative!"
  else
    IO.println "Final balance is zero or positive."
```
```stdout
Sending out orders...
Final balance is zero or positive.
```
```stderr
```
:::
::::

{docstring ST.Ref.modifyGet}

:::comment
## Comparisons
:::

## 比較（Comparisons）


{docstring ST.Ref.ptrEq}

:::comment
## Concurrency
:::

## 並行性（Concurrency）


:::comment
Mutable references can be used as a locking mechanism.
_Taking_ the contents of the reference causes attempts to take it or to read from it to block until it is {name ST.Ref.set}`set` again.
This is a low-level feature that can be used to implement other synchronization mechanisms; it's usually better to rely on higher-level abstractions when possible.

:::

可変参照はロックメカニズムとして使用することができます。参照の内容を _取得_ すると、その参照を取得しようとしたり、そのリファレンスから読み込もうとしたりすると {name ST.Ref.set}`set` されるまでブロックされます。これは低レベルの機能であり、他の同期メカニズムを実装するために使用することができます；ただし可能であればより高度な抽象化に頼ったほうが良いです。

{docstring ST.Ref.take}

{docstring ST.Ref.swap}

{docstring ST.Ref.toMonadStateOf}


:::comment
::example "Reference Cells as Locks"
:::
:::::example "ロックとしての参照セル"
:::comment
This program launches 100 threads.
Each thread simulates a purchase attempt: it generates a random price, and if the account balance is sufficient, it decrements it by the price.
If the balance is not sufficient, then it is not decremented.
Because each thread {name ST.Ref.take}`take`s the balance cell prior to checking it and only returns it when it is finished, the cell acts as a lock.
Unlike using {name}`ST.Ref.modify`, which atomically modifies the contents of the cell using a pure function, other {name}`IO` actions may occur in the critical section
This program's `main` function is marked {keywordOf Lean.Parser.Command.declaration}`unsafe` because {name ST.Ref.take}`take` itself is unsafe.

:::

このプログラムは100個のスレッドを起動します。各スレッドは購入をシミュレートします：ランダムな価格を生成し、口座の残高が十分であれば、その価格分だけ残高を減少させます。もし残高が十分でなければ、残高を減らしません。各スレッドは残高を確認する前に残高セルを {name ST.Ref.take}`take` し、確認が終わるとそれを返すだけであるため、セルはロックとして機能します。 {name}`ST.Ref.modify` を使用して純粋関数を使用してアトミックにセルの内容を変更するのとは異なり、クリティカルなセクションで他の {name}`IO` アクションが発生する可能性があります。このプログラムの `main` 関数は {name ST.Ref.take}`take` 自体が安全ではないため、 {keywordOf Lean.Parser.Command.declaration}`unsafe` とマークされています。

::::ioExample
```ioLean
unsafe def main : IO Unit := do
  let balance ← IO.mkRef (100 : Int)
  let validationUsed ← IO.mkRef false

  let mut orders := #[]

  IO.println "Sending out orders..."
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      let b ← balance.take
      if cost ≤ b then
        balance.set (b - cost)
      else
        balance.set b
        validationUsed.set true
    orders := orders.push o

  -- Wait until all orders are completed
  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← validationUsed.get) then
    IO.println "Validation prevented a negative balance."

  if (← balance.get) < 0 then
    IO.eprintln "Final balance negative!"
  else
    IO.println "Final balance is zero or positive."
```

:::comment
The program's output is:
:::

このプログラムの出力は以下のようになります：

```stdout
Sending out orders...
Validation prevented a negative balance.
Final balance is zero or positive.
```
::::
:::::
