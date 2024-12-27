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
#doc (Manual) "Lifting Monads" =>
-/
#doc (Manual) "モナドの持ち上げ（Lifting Monads）" =>

:::::keepEnv

```lean (show := false)
variable {m m' n : Type u → Type v} [Monad m] [Monad m'] [Monad n] [MonadLift m n]
variable {α β : Type u}
```

:::comment
When one monad is at least as capable as another, then actions from the latter monad can be used in a context that expects actions from the former.
This is called {deftech (key := "lift")}_lifting_ the action from one monad to another.
Lean automatically inserts lifts when they are available; lifts are defined in the {name}`MonadLift` type class.
Automatic monad lifting is attempted before the general {tech}[coercion] mechanism.

:::

あるモナドが別のモナドに対して最低限同等の能力を持つとき、後者のモナドからのアクションは前者のモナドからのアクションを期待するコンテキストで使うことができます。これはあるモナドから別のモナドへのアクションの {deftech}_持ち上げ_ （lift）と呼ばれます。Lean は可能な場合は自動で持ち上げを挿入します；持ち上げは {name}`MonadLift` 型クラスで定義されます。モナドの自動持ち上げは一般的な {tech}[coercion] メカニズムの前に試行されます。

{docstring MonadLift}

:::comment
{tech key:="lift"}[Lifting] between monads is reflexive and transitive:
 * Any monad can run its own actions.
 * Lifts from {lean}`m` to {lean}`m'` and from {lean}`m'` to {lean}`n` can be composed to yield a lift from {lean}`m` to {lean}`n`.
The utility type class {name}`MonadLiftT` constructs lifts via the reflexive and transitive closure of {name}`MonadLift` instances.
Users should not define new instances of {name}`MonadLiftT`, but it is useful as an instance implicit parameter to a polymorphic function that needs to run actions from multiple monads in some user-provided monad.

:::

モナド間の {tech}[持ち上げ] は反射的かつ推移的です：
 * どのモナドもそれ自身のアクションを実行することができます。
 * {lean}`m` から {lean}`m'` への持ち上げ、および {lean}`m'` から {lean}`n` への持ち上げは {lean}`m`  {lean}`n` への持ち上げを生成するために合成することができます。
ユーティリティの型クラス {name}`MonadLiftT` は {name}`MonadLift` インスタンスの反射的かつ推移的な閉包によって持ち上げを構築します。ユーザは {name}`MonadLiftT` のインスタンスを新たに定義すべきではありませんが、ユーザが提供するモナドの複数のモナドからアクションを実行する必要がある多相関数のインスタンス暗黙パラメータとして便利です。

{docstring MonadLiftT}

:::comment
::example "Monad Lifts in Function Signatures"
:::
::::example "関数シグネチャ内のモナドの持ち上げ"
:::comment
The function {name}`IO.withStdin` has the following signature:
:::

関数 {name}`IO.withStdin` は以下のシグネチャを持ちます：

```signature
IO.withStdin.{u} {m : Type → Type u} {α : Type}
  [Monad m] [MonadFinally m] [MonadLiftT BaseIO m]
  (h : IO.FS.Stream) (x : m α) :
  m α
```
:::comment
Because it doesn't require its parameter to precisely be in {name}`IO`, it can be used in many monads, and the body does not need to restrict itself to {name}`IO`.
The instance implicit parameter {lean}`MonadLiftT BaseIO m` allows the reflexive transitive closure of {name}`MonadLift` to be used to assemble the lift.
:::

パラメータでは {name}`IO` であることを正確に要求していないため、その他の多くのモナドでも使用することができ、本体は {name}`IO` に制限する必要はありません。インスタンス暗黙パラメータ {lean}`MonadLiftT BaseIO m` により、 {name}`MonadLift` の反射的推移的閉包を使用して持ち上げを組み立てることができます。

::::


:::comment
When a term of type {lean}`n β` is expected, but the provided term has type {lean}`m α`, and the two types are not definitionally equal, Lean attempts to insert lifts and coercions before reporting an error.
There are the following possibilities:
:::

{lean}`n β` 型の項が期待されているが、提供された項が {lean}`m α` 型であり、2つの型が定義上等しくない場合、Lean はエラーを報告する前に持ち上げと強制の挿入を試みます。これには以下の可能性があります：

:::comment
 1. If {lean}`m` and {lean}`n` can be unified to the same monad, then {lean}`α` and {lean}`β` are not the same.
    In this case, no monad lifts are necessary, but the value in the monad must be {tech key:="coercion"}[coerced].
    If the appropriate coercion is found, then a call to {name}`Lean.Internal.coeM` is inserted, which has the following signature:
:::

 1. {lean}`m` と {lean}`n` が同じモナドに単一化できる場合、 {lean}`α` と {lean}`β` は同じではありません。この場合、モナドの持ち上げは必要ありませんが、モナド内の値は {tech key:="coercion"}[coerce] されなければなりません。適切な強制が見つかった場合、 {name}`Lean.Internal.coeM` の呼び出しが挿入されます：
    ```signature
    Lean.Internal.coeM.{u, v} {m : Type u → Type v} {α β : Type u}
      [(a : α) → CoeT α a β] [Monad m]
      (x : m α) :
      m β
    ```
:::comment
 2. If {lean}`α` and {lean}`β` can be unified, then the monads differ.
    In this case, a monad lift is necessary to transform an expression with type {lean}`m α` to {lean}`n α`.
    If {lean}`m` can be lifted to {lean}`n` (that is, there is an instance of {lean}`MonadLiftT m n`) then a call to {name}`liftM`, which is an alias for {name}`MonadLiftT.monadLift`, is inserted.
:::
 2. {lean}`α` と {lean}`β` が単一化できる場合、モナドが異なります。この場合、 {lean}`m α` 型の式を {lean}`n α` 型に変換するにはモナドの持ち上げが必要です。 {lean}`m` が {lean}`n` に持ち上げられる場合（つまり {lean}`MonadLiftT m n` のインスタンスがある場合）、 {name}`MonadLiftT.monadLift` のエイリアスである {name}`liftM` の呼び出しが挿入されます。
    ```signature
    liftM.{u, v, w}
      {m : Type u → Type v} {n : Type u → Type w}
      [self : MonadLiftT m n] {α : Type u} :
      m α → n α
    ```
:::comment
 3. If neither {lean}`m` and {lean}`n` nor {lean}`α` and {lean}`β` can be unified, but {lean}`m` can be lifted into {lean}`n` and {lean}`α` can be coerced to {lean}`β`, then a lift and a coercion can be combined.
    This is done by inserting a call to {name}`Lean.Internal.liftCoeM`:
:::
 3. {lean}`m` と {lean}`n` 、 {lean}`α` と {lean}`β` のどちらも単一化できないが、 {lean}`m` を {lean}`n` に持ち上げることができ、 {lean}`α` を {lean}`β` に強制できる場合、持ち上げと強制を組み合わせることができます。これは {name}`Lean.Internal.liftCoeM` の呼び出しを挿入することで行われます：
    ```signature
    Lean.Internal.liftCoeM.{u, v, w}
      {m : Type u → Type v} {n : Type u → Type w}
      {α β : Type u}
      [MonadLiftT m n] [(a : α) → CoeT α a β] [Monad n]
      (x : m α) :
      n β
    ```

:::comment
As their names suggest, {name}`Lean.Internal.coeM` and {name}`Lean.Internal.liftCoeM` are implementation details, not part of the public API.
In the resulting terms, occurrences of {name}`Lean.Internal.coeM`, {name}`Lean.Internal.liftCoeM`, and coercions are unfolded.

:::

その名前が示すように、 {name}`Lean.Internal.coeM` と {name}`Lean.Internal.liftCoeM` は実装の詳細であり、パブリックな API の一部ではありません。これらの結果の項では、 {name}`Lean.Internal.coeM` ・ {name}`Lean.Internal.liftCoeM` ・強制が展開されます。

:::::

:::::keepEnv
:::comment
::example "Lifting `IO` Monads"
:::
::::example "`IO` モナドの持ち上げ"
:::comment
There is an instance of {lean}`MonadLift BaseIO IO`, so any `BaseIO` action can be run in `IO` as well:
:::

{lean}`MonadLift BaseIO IO` のインスタンスがあるため、`IO` でも `BaseIO` アクションを実行することができます：

```lean
def fromBaseIO (act : BaseIO α) : IO α := act
```
:::comment
Behind the scenes, {name}`liftM` is inserted:
:::

裏側では、 {name}`liftM` が挿入されます：

```lean (name := fromBase)
#check fun {α} (act : BaseIO α) => (act : IO α)
```
```leanOutput fromBase
fun {α} act => liftM act : {α : Type} → BaseIO α → EIO IO.Error α
```
::::
:::::

:::::keepEnv
:::comment
::example "Lifting Transformed Monads"
:::
::::example "変換されたモナドの持ち上げ"
:::comment
There are also instances of {name}`MonadLift` for most of the standard library's {tech}[monad transformers], so base monad actions can be used in transformed monads without additional work.
For example, state monad actions can be lifted across reader and exception transformers, allowing compatible monads to be intermixed freely:
:::

また、標準ライブラリの {tech}[monad transformers] のほとんどに {name}`MonadLift` インスタンスがあるため、ベースとなるモナドアクションを追加作業無しに変換されたモナドで使用することができます。例えば、状態モナドアクションは、リーダと例外の変換を横断して持ち上げることができるため、互換性のあるモナドを自由に混在させることができます：

````lean (keep := false)
def incrBy (n : Nat) : StateM Nat Unit := modify (+ n)

def incrOrFail : ReaderT Nat (ExceptT String (StateM Nat)) Unit := do
  if (← read) > 5 then throw "Too much!"
  incrBy (← read)
````

:::comment
Disabling lifting causes the code to fail to work:
:::

持ち上げを無効にすると、このコードは機能しなくなります：

````lean (name := noLift)
set_option autoLift false

def incrBy (n : Nat) : StateM Nat Unit := modify (+ n)

def incrOrFail : ReaderT Nat (ExceptT String (StateM Nat)) Unit := do
  if (← read) > 5 then throw "Too much!"
  incrBy (← read)
````

::::
:::::


:::comment
Automatic lifting can be disabled by setting {option}`autoLift` to {lean}`false`.

:::

{option}`autoLift` を {lean}`false` に設定することで自動持ち上げを無効にすることができます。

{optionDocs autoLift}

:::comment
# Reversing Lifts
:::

# 持ち上げの引き下げ（Reversing Lifts）


```lean (show := false)
variable {m n : Type u → Type v} {α ε : Type u}
```

:::comment
Monad lifting is not always sufficient to combine monads.
Many operations provided by monads are higher order, taking an action _in the same monad_ as a parameter.
Even if these operations are lifted to some more powerful monad, their arguments are still restricted to the original monad.

:::

モナドの結合において、モナドの持ち上げだけでは必ずしも十分ではありません。モナドによって提供される多くの操作は高階であり、 _同じモナド内の_ アクションをパラメータとして取ります。これらの操作がより強力なモナドに持ち上げられたとしても、その引数はもとのモナドに制限されます。

:::comment
There are two type classes that support this kind of “reverse lifting”: {name}`MonadFunctor` and {name}`MonadControl`.
An instance of {lean}`MonadFunctor m n` explains how to interpret a fully-polymorphic function in {lean}`m` into {lean}`n`.
This polymorphic function must work for _all_ types {lean}`α`: it has type {lean}`{α : Type u} → m α → m α`.
Such a function can be thought of as one that may have effects, but can't do so based on specific values that are provided.
An instance of {lean}`MonadControl m n` explains how to interpret an arbitrary action from {lean}`m` into {lean}`n`, while at the same time providing a “reverse interpreter” that allows the {lean}`m` action to run {lean}`n` actions.

:::

このような「持ち上げの引き下げ」をサポートする型クラスが2つあります： {name}`MonadFunctor` と {name}`MonadControl` です。 {lean}`MonadFunctor m n` のインスタンスは、 {lean}`m` の完全な多相関数を {lean}`n` として解釈する方法を説明します。この多相関数は {lean}`α` として _すべて_ の型に対して機能しなければなりません：これは {lean}`{α : Type u} → m α → m α` という型を持ちます。このような関数は、作用を持つかもしれないが、与えられた特定の値に基づいて作用を持つことはできない関数として考えることができます。 {lean}`MonadControl m n` のインスタンスは {lean}`m` から {lean}`n` への任意のアクションを解釈する方法を説明すると同時に、 {lean}`m` アクションが {lean}`n` アクションを実行できるようにする「逆インタプリタ」を提供します。

:::comment
## Monad Functors
:::

## モナド関手（Monad Functors）


{docstring MonadFunctor}

{docstring MonadFunctorT}

:::comment
## Reversible Lifting with `MonadControl`
:::

## `MonadControl` による持ち上げの引き下げ（Reversible Lifting with `MonadControl`）


{docstring MonadControl}

{docstring MonadControlT}

{docstring control}

{docstring controlAt}


:::::keepEnv
:::comment
::example "Exceptions and Lifting"
:::
::::example "例外と持ち上げ"
:::comment
One example is {name}`Except.tryCatch`:
:::

一例として {name}`Except.tryCatch` を挙げます：

```signature
Except.tryCatch.{u, v} {ε : Type u} {α : Type v}
  (ma : Except ε α) (handle : ε → Except ε α) :
  Except ε α
```
:::comment
Both of its parameters are in {lean}`Except ε`.
{name}`MonadLift` can lift the entire application of the handler.
The function {lean}`getBytes`, which extracts the single bytes from an array of {lean}`Nat`s using state and exceptions, is written without {keywordOf Lean.Parser.Term.do}`do`-notation or automatic lifting in order to make its structure explicit.
:::

パラメータはどちらも {lean}`Except ε` です。 {name}`MonadLift` はハンドラの適用全体を持ち上げることができます。 {lean}`getBytes` 関数は、状態と例外を使用して {lean}`Nat` の配列からシングルバイトを抽出しますが、その構造を明示的にするために {keywordOf Lean.Parser.Term.do}`do` 記法や自動持ち上げなしで記述されています。

```lean
set_option autoLift false

def getByte (n : Nat) : Except String UInt8 :=
  if n < 256 then
    pure n.toUInt8
  else throw s!"Out of range: {n}"

def getBytes (input : Array Nat) : StateT (Array UInt8) (Except String) Unit := do
  input.forM fun i =>
    liftM (Except.tryCatch (some <$> getByte i) fun _ => pure none) >>=
      fun
        | some b => modify (·.push b)
        | none => pure ()
```

```lean (name := getBytesEval1)
#eval getBytes #[1, 58, 255, 300, 2, 1000000] |>.run #[] |>.map (·.2)
```
```leanOutput getBytesEval1
Except.ok #[1, 58, 255, 2]
```
:::comment
{name}`getBytes` uses an `Option` returned from the lifted action to signal the desired state updates.
This quickly becomes unwieldy if there are more possible ways to react to the inner action, such as saving handled exceptions.
Ideally, state updates would be performed within the {name}`tryCatch` call directly.


:::

{name}`getBytes` は、持ち上げられたアクションから返された `Option` を使用して必要な状態の更新を通知します。処理された例外を保存するなど、内側のアクションに反応する可能性がある場合、これはすぐに扱いにくくなります。理想的には、状態の更新は {name}`tryCatch` 呼び出しの中で直接実行されてほしいです。

:::comment
Attempting to save bytes and handled exceptions does not work, however, because the arguments to {name}`Except.tryCatch` have type {lean}`Except String Unit`:
:::

しかし、 {name}`Except.tryCatch` の引数の型は {lean}`Except String Unit` を持つため、バイトと処理された例外を保存しようとしてもうまくいきません：

```lean (error := true) (name := getBytesErr) (keep := false)
def getBytes' (input : Array Nat) : StateT (Array String) (StateT (Array UInt8) (Except String)) Unit := do
  input.forM fun i =>
    liftM
      (Except.tryCatch
        (getByte i >>= fun b =>
         modifyThe (Array UInt8) (·.push b))
        fun e =>
          modifyThe (Array String) (·.push e))
```
```leanOutput getBytesErr
failed to synthesize
  MonadStateOf (Array String) (Except String)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

:::comment
Because {name}`StateT` has a {name}`MonadControl` instance, {name}`control` can be used instead of {name}`liftM`.
It provides the inner action with an interpreter for the outer monad.
In the case of {name}`StateT`, this interpreter expects that the inner monad returns a tuple that includes the updated state, and takes care of providing the initial state and extracting the updated state from the tuple.

:::

{name}`StateT` は {name}`MonadControl` インスタンスを持つため、 {name}`liftM` の代わりに {name}`control` を使用することができます。これは内側のアクションに外側のモナドのインタプリタを提供します。 {name}`StateT` の場合、このインタプリタは内側のモナドが更新された状態を含むタプルを返すことを期待し、初期状態の提供とタプルからの更新された状態の抽出を行います。

```lean
def getBytes' (input : Array Nat) : StateT (Array String) (StateT (Array UInt8) (Except String)) Unit := do
  input.forM fun i =>
    control fun run =>
      (Except.tryCatch
        (getByte i >>= fun b =>
         run (modifyThe (Array UInt8) (·.push b))))
        fun e =>
          run (modifyThe (Array String) (·.push e))
```

```lean (name := getBytesEval2)
#eval
  getBytes' #[1, 58, 255, 300, 2, 1000000]
  |>.run #[] |>.run #[]
  |>.map (fun (((), bytes), errs) => (bytes, errs))
```
```leanOutput getBytesEval2
Except.ok (#["Out of range: 300", "Out of range: 1000000"], #[1, 58, 255, 2])
```
::::
:::::
