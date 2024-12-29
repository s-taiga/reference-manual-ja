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
-- set_option trace.SubVerso.Highlighting.Code true

/-
#doc (Manual) "Syntax" =>
-/
#doc (Manual) "構文（Syntax）" =>

:::comment
Lean supports programming with functors, applicative functors, and monads via special syntax:
 * Infix operators are provided for the most common operations.
 * An embedded language called {tech}[{keywordOf Lean.Parser.Term.do}`do`-notation] allows the use of imperative syntax when writing programs in a monad.

:::

Lean は関手・アプリカティブ関手・モナドを使ったプログラミングに対して特別な構文をサポートしています：
 * 最も一般的な操作には中置演算子が用意されています。
 * {tech}[{keywordOf Lean.Parser.Term.do}`do` 記法] と呼ばれる組み込み言語により、モナドでプログラムを記述する際に命令構文を使用することができます。

:::comment
# Infix Operators
:::

# 中置演算子（Infix Operators）


:::comment
Infix operators are primarily useful in smaller expressions, or when there is no {lean}`Monad` instance.

:::

中置演算子は主に小さい式や、 {lean}`Monad` インスタンスが無い場合に便利です。

:::comment
## Functors
:::

## 関手（Functors）


```lean (show := false)
section FOps
variable {f : Type u → Type v} [Functor f] {α β : Type u} {g : α → β} {x : f α}
```
:::comment
There are two infix operators for {name}`Functor.map`.

:::

{name}`Functor.map` には2つの中置演算子があります。

::::syntax term (title := "Functor Operators")
:::comment
{lean}`g <$> x` is short for {lean}`Functor.map g x`.
:::

{lean}`g <$> x` は {lean}`Functor.map g x` の省略形です。

```grammar
$_ <$> $_
```

:::comment
{lean}`x <&> g` is short for {lean}`Functor.map g x`.
:::

{lean}`x <&> g` は {lean}`Functor.map g x` の省略形です。

```grammar
$_ <&> $_
```
::::

```lean (show := false)
example : g <$> x = Functor.map g x := by rfl
example : x <&> g = Functor.map g x := by rfl
end FOps
```

:::comment
## Applicative Functors
:::

## アプリカティブ関手（Applicative Functors）


```lean (show := false)
section AOps
variable {f : Type u → Type v} [Applicative f] [Alternative f] {α β : Type u} {g : f (α → β)} {x e1 e e' : f α} {e2 : f β}
```

::::syntax term (title := "Applicative Operators")
:::comment
{lean}`g <*> x` is short for {lean}`Seq.seq g (fun () => x)`.
The function is inserted to delay evaluation because control might not reach the argument.
:::

{lean}`g <*> x` は {lean}`Seq.seq g (fun () => x)` の省略形です。この関数は制御が引数に到達しない可能性があるため、評価を遅らせるために挿入されます。

```grammar
$_ <*> $_
```

:::comment
{lean}`e1 *> e2` is short for {lean}`SeqRight.seqRight e1 (fun () => e2)`.
:::

{lean}`e1 *> e2` は {lean}`SeqRight.seqRight e1 (fun () => e2)` の省略形です。

```grammar
$_ *> $_
```

:::comment
{lean}`e1 <* e2` is short for {lean}`SeqLeft.seqLeft e1 (fun () => e2)`.
:::

{lean}`e1 <* e2` は {lean}`SeqLeft.seqLeft e1 (fun () => e2)` の省略形です。

```grammar
$_ <* $_
```
::::

:::comment
Many applicative functors also support failure and recovery via the {name}`Alternative` type class.
This class also has an infix operator.

:::

多くのアプリカティブ関手は {name}`Alternative` 型クラスによる失敗と回復もサポートしています。このクラスも中置演算子を持っています。

::::syntax term (title := "Alternative Operators")
:::comment
{lean}`e <|> e'` is short for {lean}`OrElse.orElse e (fun () => e')`.
The function is inserted to delay evaluation because control might not reach the argument.
:::

{lean}`e <|> e'` は {lean}`OrElse.orElse e (fun () => e')` の省略形です。この関数は制御が引数に到達しない可能性があるため、評価を遅らせるために挿入されます。

```grammar
$_ <|> $_
```
::::


```lean (show := false)
example : g <*> x = Seq.seq g (fun () => x) := by rfl
example : e1 *> e2 = SeqRight.seqRight e1 (fun () => e2) := by rfl
example : e1 <* e2 = SeqLeft.seqLeft e1 (fun () => e2) := by rfl
example : (e <|> e') = (OrElse.orElse e (fun () => e')) := by rfl
end AOps
```

::::::keepEnv
```lean
structure User where
  name : String
  favoriteNat : Nat
def main : IO Unit := pure ()
```
:::comment
::example "Infix `Functor` and `Applicative` Operators"
:::
:::::example "`Functor` と `Applicative` の中置演算子"
:::comment
A common functional programming idiom is to use a pure function in some context with effects by applying it via {name}`Functor.map` and {name}`Seq.seq`.
The function is applied to its sequence of arguments using `<$>`, and the arguments are separated by `<*>`.

:::

一般的な関数型プログラミングにおいて作用のあるコンテキストで純粋関数を使用するには {name}`Functor.map` と {name}`Seq.seq` を経由して関数を適用することが一般的です。関数への一連の引数は `<$>` を使って適用され、それぞれの引数は `<*>` で区切られます。

:::comment
In this example, the constructor {name}`User.mk` is applied via this idiom in the body of {lean}`main`.
:::

以下の例では、 {name}`User.mk` というコンストラクタが {lean}`main` の本体内でこのイディオムを使って適用されています。

::::ioExample
```ioLean
def getName : IO String := do
  IO.println "What is your name?"
  return (← (← IO.getStdin).getLine).trimRight

partial def getFavoriteNat : IO Nat := do
  IO.println "What is your favorite natural number?"
  let line ← (← IO.getStdin).getLine
  if let some n := line.trim.toNat? then
    return n
  else
    IO.println "Let's try again."
    getFavoriteNat

structure User where
  name : String
  favoriteNat : Nat
deriving Repr

def main : IO Unit := do
  let user ← User.mk <$> getName <*> getFavoriteNat
  IO.println (repr user)
```
:::comment
When run with this input:
:::

以下の入力で実行すると：

```stdin
A. Lean User
None
42
```
:::comment
it produces this output:
:::

以下を出力します：

```stdout
What is your name?
What is your favorite natural number?
Let's try again.
What is your favorite natural number?
{ name := "A. Lean User", favoriteNat := 42 }
```
::::

:::::
::::::

:::comment
## Monads
:::

## モナド（Monads）


:::comment
Monads are primarily used via {tech}[{keywordOf Lean.Parser.Term.do}`do`-notation].
However, it can sometimes be convenient to describe monadic computations via operators.

:::

モナドは主に {tech}[{keywordOf Lean.Parser.Term.do}`do` 記法] によって使用されます。しかし、演算子を使ってモナドの計算を記述する方が便利な場合もあります。

```lean (show := false)
section MOps
variable {m : Type u → Type v} [Monad m] {α β : Type u} {act : m α} {f : α → m β} {g : β → m γ}
```

::::syntax term (title := "Monad Operators")

:::comment
{lean}`act >>= f` is syntax for {lean}`Bind.bind act f`.
:::

{lean}`act >>= f` は {lean}`Bind.bind act f` の省略形です。

```grammar
$_ >>= $_
```

:::comment
Similarly, the reversed operator {lean}`f =<< act` is syntax for {lean}`Bind.bind act f`.
:::

同様に、逆向きの演算子 {lean}`f =<< act` は {lean}`Bind.bind act f` の省略形です。

```grammar
$_ =<< $_
```

:::comment
The Kleisli composition operators {name}`Bind.kleisliRight` and {name}`Bind.kleisliLeft` also have infix operators.
:::

Kleisli の合成演算子 {name}`Bind.kleisliRight` と {name}`Bind.kleisliLeft` にも中置演算子があります。

```grammar
$_ >=> $_
```
```grammar
$_ <=< $_
```

::::

```lean (show := false)
example : act >>= f = Bind.bind act f := by rfl
example : f =<< act = Bind.bind act f := rfl
example : f >=> g = Bind.kleisliRight f g := by rfl
example : g <=< f = Bind.kleisliLeft g f := by rfl
end MOps
```


:::comment
# `do`-Notation
:::

# `do` 記法（`do`-Notation）

%%%
tag := "do-notation"
%%%

:::comment
Monads are primarily used via {deftech}[{keywordOf Lean.Parser.Term.do}`do`-notation], which is an embedded language for programming in an imperative style.
It provides familiar syntax for sequencing effectful operations, early return, local mutable variables, loops, and exception handling.
All of these features are translated to the operations of the {lean}`Monad` type class, with a few of them requiring addition instances of classes such as {lean}`ForIn` that specify iteration over containers.
A {keywordOf Lean.Parser.Term.do}`do` term consists of the keyword {keywordOf Lean.Parser.Term.do}`do` followed by a sequence of {deftech}_{keywordOf Lean.Parser.Term.do}`do` items_.

:::

モナドは主に {deftech}[{keywordOf Lean.Parser.Term.do}`do` 記法] （ {keywordOf Lean.Parser.Term.do}`do`-notation ）によって使用されます。これは作用を持つ操作の列・早期リターン・ローカル変数・ループ・例外処理のためのおなじみの構文を提供します。これらの機能はすべて {lean}`Monad` 型クラスの操作に変換され、そのうちのいくつかは {lean}`ForIn` のようなコンテナに対する反復を指定するクラスのインスタンスを追加する必要があります。 {keywordOf Lean.Parser.Term.do}`do` 項は、キーワード {keywordOf Lean.Parser.Term.do}`do` に続く {deftech}_{keywordOf Lean.Parser.Term.do}`do` 要素_ （ {keywordOf Lean.Parser.Term.do}`do` item ）から構成されます。

::::syntax term
```grammar
do $stmt*
```
:::comment
The items in a {keywordOf Lean.Parser.Term.do}`do` may be separated by semicolons; otherwise, each should be on its own line and they should have equal indentation.
:::

{keywordOf Lean.Parser.Term.do}`do` の要素はセミコロンで区切ることができます；セミコロンを用いない場合は、それぞれの要素で行を分け、同じインデントにしなければなりません。

::::

```lean (show := false)
section
variable {m : Type → Type} [Monad m] {α β γ: Type} {e1 : m Unit} {e : β} {es : m α}
```

:::comment
## Sequential Computations
:::

## 逐次計算（Sequential Computations）


:::comment
One form of {tech}[{keywordOf Lean.Parser.Term.do}`do` item] is a term.

:::

{tech}[{keywordOf Lean.Parser.Term.do}`do` 要素] の1つの形式は項です。

:::syntax Lean.Parser.Term.doSeqItem
```grammar
$e:term
```
:::


:::comment
A term followed by a sequence of items is translated to a use {name}`bind`; in particular, {lean}`do e1; es` is translated to {lean}`e1 >>= fun () => do es`.


:::

要素の列に続く項は {name}`bind` の使用に変換されます；特に、 {lean}`do e1; es` は {lean}`e1 >>= fun () => do es` に変換されます。

::::comment
:::table (header := true)
* ignored
  * {keywordOf Lean.Parser.Term.do}`do` Item
  * Desugaring
* ignored
  * ```leanTerm
    do
    e1
    es
    ```
  * ```leanTerm
    e1 >>= fun () => do es
    ```
:::
::::
:::table (header := true)
* ignored
  * {keywordOf Lean.Parser.Term.do}`do` 要素
  * 脱糖後
* ignored
  * ```leanTerm
    do
    e1
    es
    ```
  * ```leanTerm
    e1 >>= fun () => do es
    ```
:::

```lean (show := false) (keep := false)
def ex1a := do e1; es
def ex1b := e1 >>= fun () => do es
example : @ex1a = @ex1b := by rfl
```

:::comment
The result of the term's computation may also be named, allowing it to be used in subsequent steps.
This is done using {keywordOf Lean.Parser.Term.doLet}`let`.

:::

項の計算結果には名前を付けることができ、後続のステップで使用することができます。これは {keywordOf Lean.Parser.Term.doLet}`let` を使って行います。

```lean (show := false)
section
variable {e1 : m β} {e1? : m (Option β)} {fallback : m α} {e2 : m γ} {f : β → γ → m Unit} {g : γ → α} {h : β → m γ}
```

::::syntax Lean.Parser.Term.doSeqItem
:::comment
There are two forms of monadic {keywordOf Lean.Parser.Term.doLet}`let`-binding in a {keywordOf Lean.Parser.Term.do}`do` block.
The first binds an identifier to the result, with an optional type annotation:
:::

{keywordOf Lean.Parser.Term.do}`do` ブロック内でのモナドによる {keywordOf Lean.Parser.Term.doLet}`let` 束縛には2つの形式があります。1つ目は識別子を結果に束縛するもので、オプションで型注釈をつけることができます：

```grammar
let $x:ident$[:$e]? ← $e:term
```
:::comment
The second binds a pattern to the result.
The fallback clause, beginning with `|`, specifies the behavior when the pattern does not match the result.
:::

2番目はパターンを結果に束縛します。 `|` で始まるフォールバック節は、パターンが結果にマッチしなかった場合の動作を指定します。

```grammar
let $x:term ← $e:term
  $[| $e]?
```
::::
:::comment
This syntax is also translated to a use of {name}`bind`.
{lean}`do let x ← e1; es` is translated to {lean}`e1 >>= fun x => do es`, and fallback clauses are translated to default pattern matches.
{keywordOf Lean.Parser.Term.doLet}`let` may also be used with the standard definition syntax `:=` instead of `←`.
This indicates a pure, rather than monadic, definition:
:::

この構文も {name}`bind` の使用に変換されます。 {lean}`do let x ← e1; es` は {lean}`e1 >>= fun x => do es` に変換され、フォールバック節はデフォルトのパターンマッチに変換されます。 {keywordOf Lean.Parser.Term.doLet}`let` は `←` の代わりに標準的な定義構文 `:=` によって使用することもできます。この場合はモナドではなく純粋な定義を示します：

:::syntax Lean.Parser.Term.doSeqItem
```grammar
let v := $e:term
```
:::
:::comment
{lean}`do let x := e; es` is translated to {lean}`let x := e; do es`.

:::

{lean}`do let x := e; es` は {lean}`let x := e; do es` に変換されます。

::::comment
:::table (header := true)
* ignored
  * {keywordOf Lean.Parser.Term.do}`do` Item
  * Desugaring
* ignored
  * ```leanTerm
    do
    let x ← e1
    es
    ```
  * ```leanTerm
    e1 >>= fun x =>
      do es
    ```
* ignored
  * ```leanTerm
    do
    let some x ← e1?
      | fallback
    es
    ```
  * ```leanTerm
    e1? >>= fun
      | some x => do
        es
      | _ => fallback
    ```
* ignored
  * ```leanTerm
    do
    let x := e
    es
    ```
  * ```leanTerm
    let x := e
    do es
    ```
:::
::::
:::table (header := true)
* ignored
  * {keywordOf Lean.Parser.Term.do}`do` 要素
  * 脱糖後
* ignored
  * ```leanTerm
    do
    let x ← e1
    es
    ```
  * ```leanTerm
    e1 >>= fun x =>
      do es
    ```
* ignored
  * ```leanTerm
    do
    let some x ← e1?
      | fallback
    es
    ```
  * ```leanTerm
    e1? >>= fun
      | some x => do
        es
      | _ => fallback
    ```
* ignored
  * ```leanTerm
    do
    let x := e
    es
    ```
  * ```leanTerm
    let x := e
    do es
    ```
:::

```lean (show := false) (keep := false)
-- Test desugarings
def ex1a := do
    let x ← e1
    es
def ex1b :=
    e1 >>= fun x =>
      do es
example : @ex1a = @ex1b := by rfl


def ex2a :=
    do
    let some x ← e1?
      | fallback
    es

def ex2b :=
    e1? >>= fun
      | some x => do
        es
      | _ => fallback
example : @ex2a = @ex2b := by rfl

def ex3a :=
    do
    let x := e
    es
def ex3b :=
    let x := e
    do es
example : @ex3a = @ex3b := by rfl
```
:::comment
Within a {keywordOf Lean.Parser.Term.do}`do` block, `←` may be used as a prefix operator.
The expression to which it is applied is replaced with a fresh variable, which is bound using {name}`bind` just before the current step.
This allows monadic effects to be used in positions that otherwise might expect a pure value, while still maintaining the distinction between _describing_ an effectful computation and actually _executing_ its effects.
Multiple occurrences of `←` are processed from left to right, inside to outside.

:::

{keywordOf Lean.Parser.Term.do}`do` ブロック内では、`←` を前置演算子として使用することができます。これが適用された式は新しい変数に置き換えられ、現在のステップの直前に {name}`bind` を使って束縛されます。これにより、作用のある計算を _記述する_ ことと、実際にその作用を _実行する_ ことの区別を維持したまま、純粋な値を期待する位置でモナドの作用も使用することができます。複数回出現する `←` は左から右へ、内側から外側の順に処理されます。

:::::figure "Example Nested Action Desugarings"
::::comment
:::table (header := true)
* ignored
  * {keywordOf Lean.Parser.Term.do}`do` Item
  * Desugaring
* ignored
  * ```leanTerm
    do
    f (← e1) (← e2)
    es
    ```
  * ```leanTerm
    do
    let x ← e1
    let y ← e2
    f x y
    es
    ```
* ignored
  * ```leanTerm
    do
    let x := g (← h (← e1))
    es
    ```
  * ```leanTerm
    do
    let y ← e1
    let z ← h y
    let x := g z
    es
    ```
:::
::::
:::table (header := true)
* ignored
  * {keywordOf Lean.Parser.Term.do}`do` 要素
  * 脱糖後
* ignored
  * ```leanTerm
    do
    f (← e1) (← e2)
    es
    ```
  * ```leanTerm
    do
    let x ← e1
    let y ← e2
    f x y
    es
    ```
* ignored
  * ```leanTerm
    do
    let x := g (← h (← e1))
    es
    ```
  * ```leanTerm
    do
    let y ← e1
    let z ← h y
    let x := g z
    es
    ```
:::
:::::

```lean (show := false) (keep := false)
-- Test desugarings
def ex1a := do
  f (← e1) (← e2)
  es
def ex1b := do
  let x ← e1
  let y ← e2
  f x y
  es
example : @ex1a = @ex1b := by rfl
def ex2a := do
  let x := g (← h (← e1))
  es
def ex2b := do
  let y ← e1
  let z ← h y
  let x := g z
  es
example : @ex2a = @ex2b := by rfl
```

:::comment
In addition to convenient support for sequential computations with data dependencies, {keywordOf Lean.Parser.Term.do}`do`-notation also supports the local addition of a variety of effects, including early return, local mutable state, and loops with early termination.
These effects are implemented via transformations of the entire {keywordOf Lean.Parser.Term.do}`do` block in a manner akin to {tech}[monad transformers], rather than via a local desugaring.

:::

{keywordOf Lean.Parser.Term.do}`do` 記法は、データに依存する逐次計算のサポートに加えて、早期リターン・ローカルの可変状態・早期終了のループなど、さまざまな作用におけるローカルでの追加作用もサポートしています。これらの作用は、ローカルの脱糖ではなく、 {tech}[モナド変換子] のような方法で {keywordOf Lean.Parser.Term.do}`do` ブロック全体の変換によって実装されています。

:::comment
## Early Return
:::

## 早期リターン（Early Return）


:::comment
Early return terminates a computation immediately with a given value.
The value is returned from the closest containing {keywordOf Lean.Parser.Term.do}`do` block; however, this may not be the closest `do` keyword.
The rules for determining the extent of a {keywordOf Lean.Parser.Term.do}`do` block are described {ref "closest-do-block"}[in their own section].

:::

早期リターンは与えられた値で直ちに計算を終了します。値は最も近い {keywordOf Lean.Parser.Term.do}`do` ブロックを含む {keywordOf Lean.Parser.Term.do}`do` ブロックから返されます；しかし、場合によっては最も近い `do` キーワードからではないこともあります。 {keywordOf Lean.Parser.Term.do}`do` ブロックの範囲を決定する規則は {ref "closest-do-block"}[専用の節] で説明されています。

:::syntax Lean.Parser.Term.doSeqItem
```grammar
return $e
```

```grammar
return
```
:::

:::comment
Not all monads include early return.
Thus, when a {keywordOf Lean.Parser.Term.do}`do` block contains {keywordOf Lean.Parser.Term.doReturn}`return`, the code needs to be rewritten to simulate the effect.
A program that uses early return to compute a value of type {lean}`α` in a monad {lean}`m` can be thought of as a program in the monad {lean}`ExceptT α m α`: early-returned values take the exception pathway, while ordinary returns do not.
Then, an outer handler can return the value from either code paths.
Internally, the {keywordOf Lean.Parser.Term.do}`do` elaborator performs a translation very much like this one.

:::

全てのモナドが早期リターンを含むわけではありません。したがって、 {keywordOf Lean.Parser.Term.do}`do` ブロックに {keywordOf Lean.Parser.Term.doReturn}`return` が含まれている場合、そのコードはその作用をシミュレートするために書き換えられる必要があります。モナド {lean}`m` の {lean}`α` 型の値を計算するために早期リターンを使用するプログラムは、 {lean}`ExceptT α m α` モナドのプログラムと考えることができます：早期リターンされる値は例外の経路を取り、通常の返却ではそちらを通りません。そして外部のハンドラはどちらのコードパスからも値を返すことができます。内部的には {keywordOf Lean.Parser.Term.do}`do` エラボレータはこのような変換を行います。

:::comment
On its own, {keywordOf Lean.Parser.Term.doReturn}`return` is short for {keywordOf Lean.Parser.Term.doReturn}`return`​` `​{lean}`()`.

:::

{keywordOf Lean.Parser.Term.doReturn}`return` だけ書かれた場合は、 {keywordOf Lean.Parser.Term.doReturn}`return`​` `​{lean}`()` の省略形です。

:::comment
## Local Mutable State
:::

## ローカルの可変状態（Local Mutable State）


:::comment
Local mutable state is mutable state that cannot escape the {keywordOf Lean.Parser.Term.do}`do` block in which it is defined.
The {keywordOf Lean.Parser.Term.doLet}`let mut` binder introduces a locally-mutable binding.
:::

ローカルの可変状態とは、それが定義されている {keywordOf Lean.Parser.Term.do}`do` ブロックからエスケープできないもののことです。 {keywordOf Lean.Parser.Term.doLet}`let mut` 束縛子はローカルの可変な束縛を導入します。

::::syntax Lean.Parser.Term.doSeqItem
:::comment
Mutable bindings may be initialized either with pure computations or with monadic computations:
:::

可変な束縛は、純粋な計算とモナドの計算のどちらでも初期化することができます：

```grammar
let mut $x := $e
```
```grammar
let mut $x ← $e
```

:::comment
Similarly, they can be mutated either with pure values or the results of monad computations:
:::

同様に、純粋な値とモナドの計算結果のどちらでもミューテーションさせることができます：

```grammar (of := Lean.Parser.Term.doReassign)
$x:ident$[: $_]?  := $e:term
```
```grammar (of := Lean.Parser.Term.doReassign)
$x:term$[: $_]? := $e:term
```
```grammar (of := Lean.Parser.Term.doReassignArrow)
$x:ident$[: $_]? ← $e:term
```
```grammar (of := Lean.Parser.Term.doReassignArrow)
$x:term ← $e:term
  $[| $e]?
```
::::

:::comment
These locally-mutable bindings are less powerful than a {tech}[state monad] because they are not mutable outside their lexical scope; this also makes them easier to reason about.
When {keywordOf Lean.Parser.Term.do}`do` blocks contain mutable bindings, the {keywordOf Lean.Parser.Term.do}`do` elaborator transforms the expression similarly to the way that {lean}`StateT` would, constructing a new monad and initializing it with the correct values.

:::

このようなローカルの可変な束縛は、そのレキシカルスコープの外では可変ではないため、 {tech}[状態モナド] よりも強力ではありません；この性質によって推論も簡単になります。 {keywordOf Lean.Parser.Term.do}`do` ブロックに可変な束縛が含まれている場合、 {keywordOf Lean.Parser.Term.do}`do` エラボレータは {lean}`StateT` と同じように式を変換し、新しいモナドを構築して正しい値で初期化します。

:::comment
## Control Structures
:::

## 制御構造（Control Structures）

%%%
tag := "do-control-structures"
%%%

:::comment
There are {keywordOf Lean.Parser.Term.do}`do` items that correspond to most of Lean's term-level control structures.
When they occur as a step in a {keywordOf Lean.Parser.Term.do}`do` block, they are interpreted as {keywordOf Lean.Parser.Term.do}`do` items rather than terms.
Each branch of the control structures is a sequence of {keywordOf Lean.Parser.Term.do}`do` items, rather than a term, and some of them are more syntactically flexible than their corresponding terms.

:::

{keywordOf Lean.Parser.Term.do}`do` 要素は Lean のほとんどの項レベルの制御構造に対応しています。これらは {keywordOf Lean.Parser.Term.do}`do` ブロックのステップとして出現する場合、項ではなく {keywordOf Lean.Parser.Term.do}`do` 要素として解釈されます。制御構造の各分岐は項ではなく {keywordOf Lean.Parser.Term.do}`do` 要素の列であり、それらのいくつかは対応する項よりも構文的に柔軟です。

::::syntax Lean.Parser.Term.doSeqItem
:::comment
In a {keywordOf Lean.Parser.Term.do}`do` block, {keywordOf Lean.Parser.Term.doIf}`if` statements may omit their {keywordOf Lean.Parser.Term.doIf}`else` branch.
Omitting an {keywordOf Lean.Parser.Term.doIf}`else` branch is equivalent to using {name}`pure`{lean}` ()` as the contents of the branch.
:::

{keywordOf Lean.Parser.Term.do}`do` ブロックでは、 {keywordOf Lean.Parser.Term.doIf}`if` 文は {keywordOf Lean.Parser.Term.doIf}`else` を省略することができます。 {keywordOf Lean.Parser.Term.doIf}`else` を省略することはその分岐の内容として {name}`pure`{lean}` ()` を使用することと同等です。

```grammar
if $[$h :]? $e then
  $e*
$[else
  $_*]?
```
::::

:::comment
Syntactically, the {keywordOf Lean.Parser.Term.doIf}`then` branch cannot be omitted.
For these cases, {keywordOf Lean.Parser.Term.doUnless}`unless` only executes its body when the condition is false.
The {keywordOf Lean.Parser.Term.do}`do` in {keywordOf Lean.Parser.Term.doUnless}`unless` is part of its syntax and does not induce a nested {keywordOf Lean.Parser.Term.do}`do` block.
:::

構文上、 {keywordOf Lean.Parser.Term.doIf}`then` 分岐を省略することはできません。このような場合、 {keywordOf Lean.Parser.Term.doUnless}`unless` は条件が偽の時にのみ本体を実行します。 {keywordOf Lean.Parser.Term.do}`do` 内の {keywordOf Lean.Parser.Term.doUnless}`unless` は構文の一部であり、 {keywordOf Lean.Parser.Term.do}`do` の入れ子を誘導しません。

:::syntax Lean.Parser.Term.doSeqItem
```grammar
unless $e do
  $e*
```
:::


:::comment
When {keywordOf Lean.Parser.Term.doMatch}`match` is used in a {keywordOf Lean.Parser.Term.do}`do` block, each branch is considered to be part of the same block.
Otherwise, it is equivalent to the {keywordOf Lean.Parser.Term.match}`match` term.
:::

{keywordOf Lean.Parser.Term.doMatch}`match` が {keywordOf Lean.Parser.Term.do}`do` ブロック内で使用されている場合、各分岐は同じブロックの一部と見なされます。そうでない場合。 {keywordOf Lean.Parser.Term.match}`match` 項と同等です。

:::syntax Lean.Parser.Term.doSeqItem
```grammar
match $[$[$h :]? $e],* with
  $[| $t,* => $e*]*
```
:::


:::comment
## Iteration
:::

## 反復処理（Iteration）


:::comment
Within a {keywordOf Lean.Parser.Term.do}`do` block, {keywordOf Lean.Parser.Term.doFor}`for`​`…`​{keywordOf Lean.Parser.Term.doFor}`in` loops allow iteration over a data structure.
The body of the loop is part of the containing {keywordOf Lean.Parser.Term.do}`do` block, so local effects such as early return and mutable variables may be used.

:::

{keywordOf Lean.Parser.Term.do}`do` ブロック内では、 {keywordOf Lean.Parser.Term.doFor}`for`​`…`​{keywordOf Lean.Parser.Term.doFor}`in` ループによってデータ構造に対する反復処理を可能にします。ループの本体は {keywordOf Lean.Parser.Term.do}`do` ブロックを含むため、早期リターンや可変変数などのローカルの作用を使用することができます。

:::syntax Lean.Parser.Term.doSeqItem
```grammar
for $[$[$h :]? $x in $y],* do
  $e*
```
:::

:::comment
A {keywordOf Lean.Parser.Term.doFor}`for`​`…`​{keywordOf Lean.Parser.Term.doFor}`in` loop requires at least one clause that specifies the iteration to be performed, which consists of an optional membership proof name followed by a colon (`:`), a pattern to bind, the keyword {keywordOf Lean.Parser.Term.doFor}`in`, and a collection term.
The pattern, which may just be an {tech}[identifier], must match any element of the collection; patterns in this position cannot be used as implicit filters.
Further clauses may be provided by separating them with commas.
Each collection is iterated over at the same time, and iteration stops when any of the collections runs out of elements.

:::

{keywordOf Lean.Parser.Term.doFor}`for`​`…`​{keywordOf Lean.Parser.Term.doFor}`in` ループでは、実行する反復処理を指定する節が少なくとも1つ必要です。この節は、コロン（`:`）が続くオプションのメンバシップ証明名・束縛パターン・キーワード {keywordOf Lean.Parser.Term.doFor}`in` ・コレクションの項から構成されます。パターンは {tech}[識別子] であり、コレクションの任意の要素と一致しなければなりません；この位置でのパターンは暗黙のフィルタとして使うことはできません。カンマで区切ることでさらに節を指定することができます。各コレクションは同時に反復され、いずれかのコレクションの要素がなくなると反復処理が停止します。

:::comment
::example "Iteration Over Multiple Collections"
:::
::::example "複数のコレクションに対する反復処理"
:::comment
When iterating over multiple collections, iteration stops when any of the collections runs out of elements.
:::

複数のコレクションに対して反復処理する場合、いずれかのコレクションの要素がなくなると反復処理が停止します。

```lean (name := earlyStop)
#eval Id.run do
  let mut v := #[]
  for x in [0:43], y in ['a', 'b'] do
    v := v.push (x, y)
  return v
```
```leanOutput earlyStop
#[(0, 'a'), (1, 'b')]
```
::::

:::::keepEnv
:::comment
::example "Iteration over Array Indices with {keywordOf Lean.Parser.Term.doFor}`for`"
:::
::::example "{keywordOf Lean.Parser.Term.doFor}`for` によるインデックスを用いた配列の繰り返し"

:::comment
When iterating over the valid indices for an array with {keywordOf Lean.Parser.Term.doFor}`for`, naming the membership proof allows the tactic that searches for proofs that array indices are in bounds to succeed.
:::

{keywordOf Lean.Parser.Term.doFor}`for` で配列の有効なインデックスを反復処理する場合、メンバシップ証明に名前を付けることで配列のインデックスが範囲内にあることの証明を検索するタクティクが成功するようになります。

```lean (keep := false)
def satisfyingIndices (p : α → Prop) [DecidablePred p] (xs : Array α) : Array Nat := Id.run do
  let mut out := #[]
  for h : i in [0:xs.size] do
    if p xs[i] then out := out.push i
  return out
```

:::comment
Omitting the hypothesis name causes the array lookup to fail, because no proof is available in the context that the iteration variable is within the specified range.

:::

仮定名を省略すると、反復変数が指定された範囲内にあることを証明するものがコンテキストにないため、配列の検索に失敗します。

```lean (keep := false) (show := false)
-- test it
/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
m : Type → Type
inst✝¹ : Monad m
α β γ : Type
e1✝ : m Unit
e : β
es : m α
e1 : m β
e1? : m (Option β)
fallback : m α
e2 : m γ
f : β → γ → m Unit
g : γ → α
h : β → m γ
p : α → Prop
inst✝ : DecidablePred p
xs : Array α
out✝ : Array Nat := #[]
col✝ : Std.Range := { start := 0, stop := xs.size, step := 1 }
i : Nat
r✝ : Array Nat
out : Array Nat := r✝
⊢ i < xs.size
-/
#guard_msgs in
def satisfyingIndices (p : α → Prop) [DecidablePred p] (xs : Array α) : Array Nat := Id.run do
  let mut out := #[]
  for i in [0:xs.size] do
    if p xs[i] then out := out.push i
  return out
```
::::
:::::

:::comment
The body of a {keywordOf Lean.doElemWhile_Do_}`while` loop is repeated while the condition remains true.
It is possible to write infinite loops using them in functions that are not marked {keywordOf Lean.Parser.Command.declaration}`partial`.
This is because the {keywordOf Lean.Parser.Command.declaration}`partial` modifier only applies to non-termination or infinite regress induced by the function being defined, and not by those that it calls.
The translation of {keywordOf Lean.doElemWhile_Do_}`while` loops relies on a separate helper.

:::

{keywordOf Lean.doElemWhile_Do_}`while` ループでは条件が真である限り本体が繰り返されます。 {keywordOf Lean.Parser.Command.declaration}`partial` とマークされていない関数の中で、このループを使って無限ループを書くことができます。これは {keywordOf Lean.Parser.Command.declaration}`partial` 修飾子が、定義されている関数によって引き起こされる非停止や無限後退にのみ適用され、その関数が呼び出す関数には適用されないためです。 {keywordOf Lean.doElemWhile_Do_}`while` ループの翻訳は別の補助関数に依存しています。

:::syntax Lean.Parser.Term.doSeqItem
```grammar
while $e do
  $e*
```
```grammar
while $h : $e do
  $e*
```
:::

:::comment
The body of a {keywordOf Lean.doElemRepeat_}`repeat` loop is repeated until a {keywordOf Lean.Parser.Term.doBreak}`break` statement is executed.
Just like {keywordOf Lean.doElemWhile_Do_}`while` loops, these loops can be used in functions that are not marked {keywordOf Lean.Parser.Command.declaration}`partial`.

:::

{keywordOf Lean.doElemRepeat_}`repeat` ループの本体は {keywordOf Lean.Parser.Term.doBreak}`break` 文が実行されるまで繰り返されます。 {keywordOf Lean.doElemWhile_Do_}`while` ループと同様に、これらのループは {keywordOf Lean.Parser.Command.declaration}`partial` とマークされていない関数で使用することができます。

:::syntax Lean.Parser.Term.doSeqItem
```grammar
repeat
  $e*
```
:::

:::comment
The {keywordOf Lean.Parser.Term.doContinue}`continue` statement skips the rest of the body of the closest enclosing {keywordOf Lean.doElemRepeat_}`repeat`, {keywordOf Lean.doElemWhile_Do_}`while`, or {keywordOf Lean.Parser.Term.doFor}`for` loop, moving on to the next iteration.
The {keywordOf Lean.Parser.Term.doBreak}`break` statement terminates the closest enclosing {keywordOf Lean.doElemRepeat_}`repeat`, {keywordOf Lean.doElemWhile_Do_}`while`, or {keywordOf Lean.Parser.Term.doFor}`for` loop, stopping iteration.

:::

{keywordOf Lean.Parser.Term.doContinue}`continue` 文は最も近い {keywordOf Lean.doElemRepeat_}`repeat` ・ {keywordOf Lean.doElemWhile_Do_}`while` ・ {keywordOf Lean.Parser.Term.doFor}`for` ループの本体の残りをスキップし、次の繰り返しに移ります。 {keywordOf Lean.Parser.Term.doBreak}`break` 文は最も近い {keywordOf Lean.doElemRepeat_}`repeat` ・ {keywordOf Lean.doElemWhile_Do_}`while` ・ {keywordOf Lean.Parser.Term.doFor}`for` ループを終了し、反復を停止します。

:::syntax Lean.Parser.Term.doSeqItem
```grammar
continue
```
```grammar
break
```
:::

:::comment
In addition to {keywordOf Lean.Parser.Term.doBreak}`break`, loops can always be terminated by effects in the current monad.
Throwing an exception from a loop terminates the loop.

:::

{keywordOf Lean.Parser.Term.doBreak}`break` に加えて、ループは常に現在のモナド内の作用によって終了させることができます。ループから例外を投げるとループが終了します。

:::comment
::example "Terminating Loops in the {lean}`Option` Monad"
:::
::::example "{lean}`Option` モナド内でのループの終了"
:::comment
The {name}`failure` method from the {name}`Alternative` class can be used to terminate an otherwise-infinite loop in the {name}`Option` monad.

:::

{name}`Alternative` クラスの {name}`failure` メソッドを使用すると、 {name}`Option` モナドの無限ループを終了させることができます。

```lean (name := natBreak)
#eval show Option Nat from do
  let mut i := 0
  repeat
    if i > 1000 then failure
    else i := 2 * (i + 1)
  return i
```
```leanOutput natBreak
none
```
::::

:::comment
## Identifying `do` Blocks
:::

## `do` ブロックの識別（Identifying `do` Blocks）

%%%
tag := "closest-do-block"
%%%

:::comment
Many features of {keywordOf Lean.Parser.Term.do}`do`-notation have an effect on the {deftech}[current {keywordOf Lean.Parser.Term.do}`do` block].
In particular, early return aborts the current block, causing it to evaluate to the returned value, and mutable bindings can only be mutated in the block in which they are defined.
Understanding these features requires a precise definition of what it means to be in the “same” block.

:::

{keywordOf Lean.Parser.Term.do}`do` 記法の多くの機能は {deftech}[現在の {keywordOf Lean.Parser.Term.do}`do` ブロック] （current {keywordOf Lean.Parser.Term.do}`do` block）に影響を与えます。特に、早期リターンは現在のブロックを中断させ、返却値で評価を行います。また可変な束縛はそれが定義されているブロックでのみミューテーションできます。これらの機能を理解するためには「同じ」ブロック内にあることの意味を正確に定義する必要があります。

:::comment
Empirically, this can be checked using the Lean language server.
When the cursor is on a {keywordOf Lean.Parser.Term.doReturn}`return` statement, the corresponding {keywordOf Lean.Parser.Term.do}`do` keyword is highlighted.
Attempting to mutate a mutable binding outside of the same {keywordOf Lean.Parser.Term.do}`do` block results in an error message.

:::

経験的に、これは Lean 言語サーバを使って確認することができます。カーソルが {keywordOf Lean.Parser.Term.doReturn}`return` 文の上にある場合、対応する {keywordOf Lean.Parser.Term.do}`do` キーワードがハイライトされます。同じ {keywordOf Lean.Parser.Term.do}`do` ブロックの外側で可変な束縛をミューテーションしようとするとエラーメッセージが表示されます。

:::figure "Highlighting {keywordOf Lean.Parser.Term.do}`do`"

![Highlighting do from return](/static/screenshots/do-return-hl-1.png)

![Highlighting do from return with errors](/static/screenshots/do-return-hl-2.png)
:::

:::comment
The rules are as follows:
 * Each item immediately nested under the {keywordOf Lean.Parser.Term.do}`do` keyword that begins a block belongs to that block.
 * Each item immediately nested under the {keywordOf Lean.Parser.Term.do}`do` keyword that is an item in a containing {keywordOf Lean.Parser.Term.do}`do` block belongs to the outer block.
 * Items in the branches of an {keywordOf Lean.Parser.Term.doIf}`if`, {keywordOf Lean.Parser.Term.doMatch}`match`, or {keywordOf Lean.Parser.Term.doUnless}`unless` item belong to the same {keywordOf Lean.Parser.Term.do}`do` block as the control structure that contains them. The {keywordOf Lean.Parser.Term.doUnless}`do` keyword that is part of the syntax of {keywordOf Lean.Parser.Term.doUnless}`unless` does not introduce a new {keywordOf Lean.Parser.Term.do}`do` block.
 * Items in the body of {keywordOf Lean.doElemRepeat_}`repeat`, {keywordOf Lean.doElemWhile_Do_}`while`, and {keywordOf Lean.Parser.Term.doFor}`for` belong to the same {keywordOf Lean.Parser.Term.do}`do` block as the loop  that contains them. The {keywordOf Lean.Parser.Term.doFor}`do` keyword that is part of the syntax of {keywordOf Lean.doElemWhile_Do_}`while` and {keywordOf Lean.Parser.Term.doFor}`for` does not introduce a new {keywordOf Lean.Parser.Term.do}`do` block.

:::

この規則は以下に従います：
 * あるブロックを開始する {keywordOf Lean.Parser.Term.do}`do` キーワードのすぐ下に入れ子になっている各要素は、そのブロックに属します。
 * ある {keywordOf Lean.Parser.Term.do}`do` ブロックの要素である {keywordOf Lean.Parser.Term.do}`do` キーワードのすぐ下に入れ子になっている各要素は。外側のブロックに属します。
 * {keywordOf Lean.Parser.Term.doIf}`if` ・ {keywordOf Lean.Parser.Term.doMatch}`match` ・ {keywordOf Lean.Parser.Term.doUnless}`unless` の分岐内の要素は、その要素を含んでいる制御構造と同じ {keywordOf Lean.Parser.Term.do}`do` ブロックに属します。 {keywordOf Lean.Parser.Term.doUnless}`unless` の構文の一部としての {keywordOf Lean.Parser.Term.doUnless}`do` キーワードは新しい {keywordOf Lean.Parser.Term.do}`do` ブロックを導入しません。
 * {keywordOf Lean.doElemRepeat_}`repeat` ・ {keywordOf Lean.doElemWhile_Do_}`while` ・ {keywordOf Lean.Parser.Term.doFor}`for` の本体内の要素は、それらを含むループと同じ {keywordOf Lean.Parser.Term.do}`do` ブロックに属します。 {keywordOf Lean.doElemWhile_Do_}`while` と {keywordOf Lean.Parser.Term.doFor}`for` の構文の一部としての {keywordOf Lean.Parser.Term.doFor}`do` キーワードは新しい {keywordOf Lean.Parser.Term.do}`do` ブロックを導入しません。

```lean (show := false)
-- Test nested `do` rules

/-- info: ((), 6) -/
#guard_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  do
    set 6
    return

/-- error: must be last element in a `do` sequence -/
#guard_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  do
    set 6
    return
  set 7
  return

/-- info: ((), 6) -/
#guard_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  if true then
    set 6
    do return
  set 7
  return
```

:::::keepEnv
:::comment
::example "Nested `do` and Branches"
:::
::::example "入れ子になった `do` と分岐"
:::comment
The following example outputs {lean}`6` rather than {lean}`7`:
:::

以下の例は {lean}`7` ではなく {lean}`6` を出力します：

```lean (name := nestedDo)
def test : StateM Nat Unit := do
  set 5
  if true then
    set 6
    do return
  set 7
  return

#eval test.run 0
```
```leanOutput nestedDo
((), 6)
```

:::comment
This is because the {keywordOf Lean.Parser.Term.doReturn}`return` statement under the {keywordOf Lean.Parser.Term.doIf}`if` belongs to the same {keywordOf Lean.Parser.Term.do}`do` as its immediate parent, which itself belongs to the same {keywordOf Lean.Parser.Term.do}`do` as the {keywordOf Lean.Parser.Term.doIf}`if`.
If {keywordOf Lean.Parser.Term.do}`do` blocks that occurred as items in other {keywordOf Lean.Parser.Term.do}`do` blocks instead created new blocks, then the example would output {lean}`7`.
:::

これは {keywordOf Lean.Parser.Term.doReturn}`return` 文が {keywordOf Lean.Parser.Term.doIf}`if` の直下の {keywordOf Lean.Parser.Term.do}`do` と同じ {keywordOf Lean.Parser.Term.doIf}`if` に属しているからです。この代わりに他の {keywordOf Lean.Parser.Term.do}`do` ブロックの要素として出現した {keywordOf Lean.Parser.Term.do}`do` ブロックによって新しいブロックを作成した場合、この例は {lean}`7` を出力します。

::::
:::::

```lean (show := false)
end
```

```lean (show := false)
-- tests for this section
set_option pp.all true

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) Unit α e1 fun (x : PUnit.{1}) => es : m α
-/
#guard_msgs in
#check do e1; es

section
variable {e1 : m β}
/-- info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (x : β) => es : m α -/
#guard_msgs in
#check do let x ← e1; es
end

/--
info: let x : β := e;
es : m α
-/
#guard_msgs in
#check do let x := e; es

variable {e1 : m β} {e2 : m γ} {f : β → γ → m Unit} {g : γ → α} {h : β → m γ}

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (__do_lift : β) =>
  @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) γ α e2 fun (__do_lift_1 : γ) =>
    @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) Unit α (f __do_lift __do_lift_1) fun (x : PUnit.{1}) => es : m α
-/
#guard_msgs in
#check do f (← e1) (← e2); es

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (__do_lift : β) =>
  @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) γ α (h __do_lift) fun (__do_lift : γ) =>
    let x : α := g __do_lift;
    es : m α
-/
#guard_msgs in
#check do let x := g (← h (← e1)); es

end


```

:::comment
## Type Classes for Iteration
:::

## 反復処理のための型クラス（Type Classes for Iteration）


:::comment
To be used with {keywordOf Lean.Parser.Term.doFor}`for` loops without membership proofs, collections must implement the {name}`ForIn` type class.
Implementing {lean}`ForIn'` additionally allows the use of {keywordOf Lean.Parser.Term.doFor}`for` loops with membership proofs.

:::

メンバシップ証明のない {keywordOf Lean.Parser.Term.doFor}`for` ループを使用するには、コレクションは {name}`ForIn` 型クラスを実装している必要があります。 {lean}`ForIn'` を実装することで、さらにメンバシップ証明付きの {keywordOf Lean.Parser.Term.doFor}`for` ループを使用することができます。

{docstring ForIn}

{docstring ForIn'}

{docstring ForInStep}

{docstring ForM}

{docstring ForM.forIn}
