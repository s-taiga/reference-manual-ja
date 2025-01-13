/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Manual.Monads.Zoo.State
import Manual.Monads.Zoo.Reader
import Manual.Monads.Zoo.Except
import Manual.Monads.Zoo.Combined
import Manual.Monads.Zoo.Id
import Manual.Monads.Zoo.Option

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
#doc (Manual) "Varieties of Monads" =>
-/
#doc (Manual) "さまざまなモナド（Varieties of Monads）" =>


:::comment
The {lean}`IO` monad has many, many effects, and is used for writing programs that need to interact with the world.
It is described in {ref "io"}[its own section].
Programs that use {lean}`IO` are essentially black boxes: they are typically not particularly amenable to verification.

:::

{lean}`IO` モナドは非常に多くの作用を持ち、世界と相互作用する必要のあるプログラムを書くために用いられます。これについては {ref "io"}[専用の節] で説明されています。 {lean}`IO` を使用するプログラムは本質的にブラックボックスです：これは大抵特に検証しやすいものではありません。

:::comment
Many algorithms are easiest to express with a much smaller set of effects.
These effects can often be simulated; for example, mutable state can be simulated by passing around a tuple that contains both the program's value and the state.
These simulated effects are easier to reason formally about, because they are defined using ordinary code rather than new language primitives.

:::

多くのアルゴリズムは、より小さな作用のセットで表現するほうが簡単です。例えば、可変状態はプログラムの値と状態の両方を含むタプルを渡すことでシミュレートできます。これらのシミュレートされた作用は言語のプリミティブではなく普通のコードを使って定義されるため、形式的に推論することが容易です。

:::comment
The standard library provides abstractions for working with commonly-used effects.
Many frequently-used effects fall into a small number of categories:

:::

標準ライブラリではよく使われる作用を扱うための抽象化が提供されています。よく使われる作用の多くはいくつかのカテゴリに分類されます：

:::comment
: {deftech}[State monads] have mutable state

  Computations that have access to some data that may be modified by other parts of the computation use _mutable state_.
  State can be implemented in a variety of ways, described in the section on {ref "state-monads"}[state monads] and captured in the {name}`MonadState` type class.

:::

: 可変状態を伴う {deftech}[状態モナド] （state monad）

  計算中に変更される可能性のあるデータにアクセスできる計算では _可変状態_ （mutable state）を使用します。 {ref "state-monads"}[状態モナド] の節で説明されているように、状態はさまざまな方法で実装することができ、 {name}`MonadState` 型クラスで捕捉されています。

:::comment
: {deftech}[Reader monads] are parameterized computations

  Computations that can read the value of some parameter provided by a context exist in most programming languages, but many languages that feature state and exceptions as first-class features do not have built-in facilities for defining new parameterized computations.
  Typically, these computations are provided with a parameter value when invoked, and sometimes they can locally override it.
  Parameter values have _dynamic extent_: the value provided most recently in the call stack is the one that is used.
  They can be simulated by passing a value unchanged through a sequence of function calls; however, this technique can make code harder to read and introduces a risk that the values may be passed incorrectly to further calls by mistake.
  They can also be simulated using mutable state with a careful discipline surrounding the modification of the state.
  Monads that maintain a parameter, potentially allowing it to be overridden in a section of the call stack, are called _reader monads_.
  Reader monads are captured in the {lean}`MonadReader` type class.
  Additionally, reader monads that allow the parameter value to be locally overridden are captured in the {lean}`MonadWithReader` type class.

:::

: パラメータ化された計算である {deftech}[リーダモナド] （reader monad）

  コンテキストから提供されたパラメータの値を読み取ることができる計算はほとんどのプログラミング言語に存在しますが、状態と例外を第一級の機能として備えている多くの言語には新しいパラメータ化された計算を定義するための組み込み機能がありません。一般的に、これらの計算は呼び出された時にパラメータ値が提供され、ローカルでオーバーライドできることもあります。パラメータ値は _動的範囲_ （dynamic extent）を持ちます：コールスタックで最も最近に提供された値が使用されます。パラメータ値は一連の関数呼び出しで変更されない値を渡すことでシミュレートできます；しかし、この技法はコードを読みにくくし、間違って次の呼び出しに間違った値を渡してしまう危険性があります。また状態の変更を慎重に規律することで可変状態を使ってパラメータ値をシミュレートすることもできます。パラメータを保持し、呼び出しスタックの位置でオーバーライドすることを可能にしたモナドは _リーダモナド_ と呼ばれます。リーダモナドは {lean}`MonadReader` 型クラスで捕捉されています。さらに、パラメータ値をローカルでオーバーライドできるモナドは {lean}`MonadWithReader` 型クラスで捕捉されます。

:::comment
: {deftech}[Exception monads] have exceptions

  Computations that may terminate early with an exceptional value use _exceptions_.
  They are typically modeled with a sum type that has a constructor for ordinary termination and a constructor for early termination with errors.
  Exception monads are described in the section on {ref "exception-monads"}[exception monads], and captured in the {name}`MonadExcept` type class.


:::

: 例外を持つ {deftech}[例外モナド] （exception monad）

  例外値で早期終了する可能性のある計算には _例外_ （exception）を使用します。これは通常、正常終了のためのコンストラクタとエラーによる早期終了のためのコンストラクタの直和型によってモデル化されます。例外モナドは {ref "exception-monads"}[例外モナド] の節で説明されており、 {name}`MonadExcept` 型クラスで捕捉されます。

:::comment
# Monad Type Classes
:::

# モナド型クラス（Monad Type Classes）


:::comment
Using type classes like {lean}`MonadState` and {lean}`MonadExcept` allow client code to be polymorphic with respect to monads.
Together with automatic lifting, this allows programs to be re-usable in many different monads and makes them more robust to refactoring.

:::

{lean}`MonadState` や {lean}`MonadExcept` のような型クラスを使うことでクライアントコードはモナドに対して多相的になります。自動持ち上げと合わせて、これはプログラムを多くの異なるモナドで再利用可能にし、リファクタリングに対してより堅牢にします。

:::comment
It's important to be aware that effects in a monad may not interact in only one way.
For example, a monad with state and exceptions may or may not roll back state changes when an exception is thrown.
If this matters for the correctness of a function, then it should use a more specific signature.

:::

モナド内の作用が1つの方法でしか相互作用しないとは限らない点に注意することが重要です。例えば、状態と例外を持つモナドは、例外が投げられた時に状態の変更をロールバックすることもあれば、しないこともあります。もしこれが関数の正しさにとって重要であれば、より特殊なシグネチャを使うべきです。

:::::keepEnv
:::comment
::example "Effect Ordering"
:::
::::example "作用の順序"
:::comment
The function {name}`sumNonFives` adds the contents of a list using a state monad, terminating early if it encounters a {lean}`5`.
:::

関数 {name}`sumNonFives` は状態モナドを使用してリストの内容の足し算を行い、 {lean}`5` に遭遇した場合、早期に終了します。

```lean
def sumNonFives {m}
    [Monad m] [MonadState Nat m] [MonadExcept String m]
    (xs : List Nat) :
    m Unit := do
  for x in xs do
    if x == 5 then
      throw "Five was encountered"
    else
      modify (· + x)
```

:::comment
Running it in one monad returns the state at the time that {lean}`5` was encountered:
:::

これを以下のモナドで実行すると {lean}`5` が発生した時点の状態が返されます：

```lean (name := exSt)
#eval
  sumNonFives (m := ExceptT String (StateM Nat))
    [1, 2, 3, 4, 5, 6] |>.run |>.run 0
```
```leanOutput exSt
(Except.error "Five was encountered", 10)
```

:::comment
In another, the state is discarded:
:::

別の以下のモナドでは、状態は破棄されます：

```lean (name := stEx)
#eval
  sumNonFives (m := StateT Nat (Except String))
    [1, 2, 3, 4, 5, 6] |>.run 0
```
```leanOutput stEx
Except.error "Five was encountered"
```

:::comment
In the second case, an exception handler would roll back the state to its value at the start of the {keywordOf Lean.Parser.Term.termTry}`try`.
The following function is thus incorrect:
:::

2つ目のケースでは、例外ハンドラは状態を {keywordOf Lean.Parser.Term.termTry}`try` の開始時の値にロールバックします。したがって以下の関数は正しくありません：

```lean
/-- Computes the sum of the non-5 prefix of a list. -/
def sumUntilFive {m}
    [Monad m] [MonadState Nat m] [MonadExcept String m]
    (xs : List Nat) :
    m Nat := do
  MonadState.set 0
  try
    sumNonFives xs
  catch _ =>
    pure ()
  get
```

:::comment
In one monad, the answer is correct:
:::

1つ目のモナドでは答えは正しくなります：

```lean (name := exSt2)
#eval
  sumUntilFive (m := ExceptT String (StateM Nat))
    [1, 2, 3, 4, 5, 6] |>.run |>.run' 0
```
```leanOutput exSt2
Except.ok 10
```

:::comment
In the other, it is not:
:::

もう一つでは正しくなりません：

```lean (name := stEx2)
#eval
  sumUntilFive (m := StateT Nat (Except String))
    [1, 2, 3, 4, 5, 6] |>.run' 0
```
```leanOutput stEx2
Except.ok 0
```
::::
:::::

:::comment
A single monad may support multiple version of the same effect.
For example, there might be a mutable {lean}`Nat` and a mutable {lean}`String` or two separate reader parameters.
As long as they have different types, it should be convenient to access both.
In typical use, some monadic operations that are overloaded in type classes have type information available for {tech key:="synthesis"}[instance synthesis], while others do not.
For example, the argument passed to {name MonadState.set}`set` determines the type of the state to be used, while {name MonadState.get}`get` takes no such argument.
The type information present in applications of {name MonadState.set}`set` can be used to pick the correct instance when multiple states are available, which suggests that the type of the mutable state should be an input parameter or {tech}[semi-output] parameter so that it can be used to select instances.
The lack of type information present in uses of {name MonadState.get}`get`, on the other hand, suggests that the type of the mutable state should be an {tech}[output parameter] in {lean}`MonadState`, so type class synthesis determines the state's type from the monad itself.

:::

1つのモナドが同じ作用の複数のバージョンをサポートすることがあります。例えば、可変な {lean}`Nat` と可変な {lean}`String` があったり、2つの別々のリーダのパラメータがあるかもしれません。それらの型が異なる限り、両方にアクセスできると便利でしょう。典型的な使用例では、型クラスでオーバーロードされるモナド演算の中には {tech key:="synthesis"}[instance synthesis] で型情報を利用できるものもあれば、そうでないものもあります。例えば、 {name MonadState.set}`set` に渡される引数は使用する状態の型を決定しますが、 {name MonadState.get}`get` ではそのような引数を取りません。 {name MonadState.set}`set` のアプリケーションに存在する型情報は、複数の状態が利用可能な場合に正しいインスタンスを選択するために使用することができます。これはインスタンスを選択するために使用できるように、可変状態の型を入力パラメータまたは {tech}[半出力パラメータ] にする必要があることを示唆しています。一方、 {name MonadState.get}`get` の使用には型情報がないことから、可変状態の型は {lean}`MonadState` の {tech}[出力パラメータ] であるべきであり、型クラス統合はモナド自体から状態の型を決定します。

:::comment
This dichotomy is solved by having two versions of many of the effect type classes.
The version with a semi-output parameter has the suffix `-Of`, and its operations take types explicitly as needed.
Examples include {name}`MonadStateOf`, {name}`MonadReaderOf`, and {name}`MonadExceptOf`.
The operations with explicit type parameters have names ending in `-The`, such as {name}`getThe`, {name}`readThe`, and {name}`tryCatchThe`.
The name of the version with an output parameter is undecorated.
The standard library exports a mix of operations from the `-Of` and undecorated versions of each type class, based on what has good inference behavior in typical use cases.

:::

この二律背反は、作用の型クラスの多くに2つのバージョンを持たせることで解決されます。半出力パラメータを持つバージョンの接尾辞は `-Of` で、その操作は必要に応じて明示的に型を取ります。例えば {name}`MonadStateOf` ・ {name}`MonadReaderOf` ・ {name}`MonadExceptOf` などです。明示的な型パラメータを持つ操作は {name}`getThe` ・ {name}`readThe` ・ {name}`tryCatchThe` などのように `-The` で終わる名前を持ちます。出力パラメータを持つバージョンの名前は装飾されません。標準ライブラリでは、典型的なユースケースで良い推論動作をするものに基づいて、各型クラスの `-Of` と装飾されていないバージョンの操作を混ぜてエクスポートしています。

::::comment
:::table (header := true)
  * ignored
   * Operation
   * From Class
   * Notes
  * ignored
   * {name}`get`
   * {name}`MonadState`
   * Output parameter improves type inference
  * ignored
   * {name}`set`
   * {name}`MonadStateOf`
   * Semi-output parameter uses type information from {name}`set`'s argument
  * ignored
   * {name}`modify`
   * {name}`MonadState`
   * Output parameter is needed to allow functions without annotations
  * ignored
   * {name}`modifyGet`
   * {name}`MonadState`
   * Output parameter is needed to allow functions without annotations
  * ignored
   * {name}`read`
   * {name}`MonadReader`
   * Output parameter is needed due to lack of type information from arguments
  * ignored
   * {name}`readThe`
   * {name}`MonadReaderOf`
   * Semi-output parameter uses the provided type to guide synthesis
  * ignored
   * {name}`withReader`
   * {name}`MonadWithReader`
   * Output parameter avoids the need for type annotations on the function
  * ignored
   * {name}`withTheReader`
   * {name}`MonadWithReaderOf`
   * Semi-output parameter uses provided type to guide synthesis
  * ignored
   * {name}`throw`
   * {name}`MonadExcept`
   * Output parameter enables the use of constructor dot notation for the exception
  * ignored
   * {name}`throwThe`
   * {name}`MonadExceptOf`
   * Semi-output parameter uses provided type to guide synthesis
  * ignored
   * {name}`tryCatch`
   * {name}`MonadExcept`
   * Output parameter enables the use of constructor dot notation for the exception
  * ignored
   * {name}`tryCatchThe`
   * {name}`MonadExceptOf`
   * Semi-output parameter uses provided type to guide synthesis
:::
::::
:::table (header := true)
  * ignored
   * 演算
   * 所有するクラス
   * 注記
  * ignored
   * {name}`get`
   * {name}`MonadState`
   * 出力パラメータによって型推論が改善します
  * ignored
   * {name}`set`
   * {name}`MonadStateOf`
   * 半出力パラメータは {name}`set` の引数の型情報を使用します
  * ignored
   * {name}`modify`
   * {name}`MonadState`
   * 注釈の無い関数を許可するには、出力パラメータが必要です
  * ignored
   * {name}`modifyGet`
   * {name}`MonadState`
   * 注釈の無い関数を許可するには、出力パラメータが必要です
  * ignored
   * {name}`read`
   * {name}`MonadReader`
   * 引数の型情報がないため、出力パラメータが必要です
  * ignored
   * {name}`readThe`
   * {name}`MonadReaderOf`
   * 半出力パラメータは提供された型を使用して統合を誘導します
  * ignored
   * {name}`withReader`
   * {name}`MonadWithReader`
   * 出力パラメータによって関数の型注釈の必要性を回避しています
  * ignored
   * {name}`withTheReader`
   * {name}`MonadWithReaderOf`
   * 半出力パラメータは提供された型を使用して統合を誘導します
  * ignored
   * {name}`throw`
   * {name}`MonadExcept`
   * 出力パラメータによってコンストラクタのドット記法を例外のために使用できます
  * ignored
   * {name}`throwThe`
   * {name}`MonadExceptOf`
   * 半出力パラメータは提供された型を使用して統合を誘導します
  * ignored
   * {name}`tryCatch`
   * {name}`MonadExcept`
   * 出力パラメータによってコンストラクタのドット記法を例外のために使用できます
  * ignored
   * {name}`tryCatchThe`
   * {name}`MonadExceptOf`
   * 半出力パラメータは提供された型を使用して統合を誘導します
:::

```lean (show := false)
example : @get = @MonadState.get := by rfl
example : @set = @MonadStateOf.set := by rfl
example (f : σ → σ) : @modify σ m inst f = @MonadState.modifyGet σ m inst PUnit fun (s : σ) => (PUnit.unit, f s) := by rfl
example : @modifyGet = @MonadState.modifyGet := by rfl
example : @read = @MonadReader.read := by rfl
example : @readThe = @MonadReaderOf.read := by rfl
example : @withReader = @MonadWithReader.withReader := by rfl
example : @withTheReader = @MonadWithReaderOf.withReader := by rfl
example : @throw = @MonadExcept.throw := by rfl
example : @throwThe = @MonadExceptOf.throw := by rfl
example : @tryCatch = @MonadExcept.tryCatch := by rfl
example : @tryCatchThe = @MonadExceptOf.tryCatch := by rfl
```

:::comment
::example "State Types"
:::
::::example "状態の型"
:::comment
The state monad {name}`M` has two separate states: a {lean}`Nat` and a {lean}`String`.
:::

以下の状態モナド {name}`M` は2つの別々の状態を持ちます： {lean}`Nat` と {lean}`String` です。

```lean
abbrev M := StateT Nat (StateM String)
```

:::comment
Because {name}`get` is an alias for {name}`MonadState.get`, the state type is an output parameter.
This means that Lean selects a state type automatically, in this case the one from the outermost monad transformer:
:::

{name}`get` は {name}`MonadState.get` のエイリアスであるため、状態の型は出力パラメータです。これは Lean が自動的に状態の型を選択することを意味し、この場合は一番外側のモナド変換子からのものとなります：

```lean (name := getM)
#check (get : M _)
```
```leanOutput getM
get : M Nat
```

:::comment
Only the outermost may be used, because the type of the state is an output parameter.
:::

状態の型は出力パラメータであるため、一番外側のみを使用することができます。

```lean (name := getMStr) (error := true)
#check (get : M String)
```
```leanOutput getMStr
failed to synthesize
  MonadState String M
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

:::comment
Providing the state type explicitly using {name}`getThe` from {name}`MonadStateOf` allows both states to be read.
:::

{name}`MonadStateOf` から {name}`getThe` を使用して明示的に状態の型を提供することで、両方の状態を読むことができます。

```lean (name := getTheM)
#check ((getThe String, getThe Nat) : M String × M Nat)
```
```leanOutput getTheM
(getThe String, getThe Nat) : M String × M Nat
```

:::comment
Setting a state works for either type, because the state type is a {tech}[semi-output parameter] on {name}`MonadStateOf`.
:::

状態の型は {name}`MonadStateOf` の {tech}[半出力パラメータ] であるため、状態のセットはどちらの型でも機能します。

```lean (name := setNat)
#check (set 4 : M Unit)
```
```leanOutput setNat
set 4 : M PUnit
```

```lean (name := setStr)
#check (set "Four" : M Unit)
```
```leanOutput setStr
set "Four" : M PUnit
```

::::


:::comment
# Monad Transformers
:::

# モナド変換子（Monad Transformers）

%%%
tag := "monad-transformers"
%%%

:::comment
A {deftech}_monad transformer_ is a function that, when provided with a monad, gives back a new monad.
Typically, this new monad has all the effects of the original monad along with some additional ones.

:::

{deftech}_モナド変換子_ （monad transformer）とは、モナドを与えると新しいモナドを返す関数のことです。通常、この新しいモナドは、もとのモナドのすべての作用といくつかの追加作用を持ちます。

```lean (show := false)
variable {α : Type u} (T : (Type u → Type v) → Type u → Type w) (m : Type u → Type v)

```
:::comment
A monad transformer consists of the following:
 * A function {lean}`T` that constructs the new monad's type from an existing monad
 * A `run` function that adapts a {lean}`T m α` into some variant of {lean}`m`, often requiring additional parameters and returning a more specific type under {lean}`m`
 * An instance of {lean}`[Monad m] → Monad (T m)` that allows the transformed monad to be used as a monad
 * An instance of {lean}`MonadLift` that allows the original monad's code to be used in the transformed monad
 * If possible, an instance of {lean}`MonadControl m (T m)` that allows actions from the transformed monad to be used in the original monad

:::

モナド変換子は以下から構成されます：
 * 関数 {lean}`T` 、既存のモナドから新しいモナドの型を構築します
 * {lean}`T m α` を {lean}`m` の変形に適応させる関数 `run`、これは多くの場合追加のパラメータを必要とし、 {lean}`m` の下でより特定の型を返します
 * {lean}`[Monad m] → Monad (T m)` のインスタンス、これにより変換されたモナドをモナドとして使用することができます
 * {lean}`MonadLift` のインスタンス、もとのモナドのコードを変換後のモナドで使用できるようにします
 * 可能であれば、変換後のモナドアクションをもとのモナドで使用できるようにする {lean}`MonadControl m (T m)` のインスタンス

:::comment
Typically, a monad transformer also provides instances of one or more type classes that describe the effects that it introduces.
The transformer's {name}`Monad` and {name}`MonadLift` instances make it practical to write code in the transformed monad, while the type class instances allow the transformed monad to be used with polymorphic functions.

:::

通常、モナド変換子はそれが導入する作用を記述する1つ以上の型クラスのインスタンスを提供します。変換子の {name}`Monad` と {name}`MonadLift` インスタンスは変換されたモナドでコードを書くことを実用的にし、型クラスのインスタンスは変換されたモナドを多相関数で使うことを可能にします。

:::::keepEnv
```lean (show := false)
universe u v
variable {m : Type u → Type v} {α : Type u}
```
:::comment
::example "The Identity Monad Transformer "
:::
::::example "恒等モナド変換子"
:::comment
The identity monad transformer neither adds nor removes capabilities to the transformed monad.
Its definition is the identity function, suitably specialized:
:::

恒等モナド変換子は、変換されたモナドへの機能の追加・削除を行いません。その定義は適切に特殊化された恒等関数です：

```lean
def IdT (m : Type u → Type v) : Type u → Type v := m
```
:::comment
Similarly, the {name IdT.run}`run` function requires no additional arguments and just returns an {lean}`m α`:
:::

同様に、 {name IdT.run}`run` 関数は追加の引数を必要とせず、 {lean}`m α` を返すだけです：

```lean
def IdT.run (act : IdT m α) : m α := act
```

:::comment
The monad instance relies on the monad instance for the transformed monad, selecting it via {tech}[type ascriptions]:
:::

モナドのインスタンスは {tech}[type ascriptions] を介して選択され、変換されたモナドのモナドインスタンスに依存します：

```lean
instance [Monad m] : Monad (IdT m) where
  pure x := (pure x : m _)
  bind x f := (x >>= f : m _)
```

:::comment
Because {lean}`IdT m` is definitionally equal to {lean}`m`, the {lean}`MonadLift m (IdT m)` instance doesn't need to modify the action being lifted:
:::

{lean}`IdT m` は {lean}`m` と definitionally equal であるため、 {lean}`MonadLift m (IdT m)` インスタンスはリフトされるアクションを変更する必要はありません：

```lean
instance : MonadLift m (IdT m) where
  monadLift x := x
```

:::comment
The {lean}`MonadControl` instance is similarly simple.
:::

{lean}`MonadControl` インスタンスも同様にシンプルです。

```lean
instance [Monad m] : MonadControl m (IdT m) where
  stM α := α
  liftWith f := f (fun x => Id.run <| pure x)
  restoreM v := v
```

::::
:::::

:::comment
The Lean standard library provides transformer versions of many different monads, including {name}`ReaderT`, {name}`ExceptT`, and {name}`StateT`, along with variants using other representations such as {name}`StateCpsT`, {name StateRefT'}`StateRefT`, and {name}`ExceptCpsT`.
Additionally, the {name}`EStateM` monad is equivalent to combining {name}`ExceptT` and {name}`StateT`, but it can use a more specialized representation to improve performance.

:::

Lean の標準ライブラリは {name}`ReaderT` ・ {name}`ExceptT` ・ {name}`StateT` などの多くの異なるモナドの変換子バージョンを提供しており、また {name}`StateCpsT` ・ {name StateRefT'}`StateRefT` ・ {name}`ExceptCpsT` などの他の表現を使用した変種も提供しています。さらに、 {name}`EStateM` モナドは {name}`ExceptT` と {name}`StateT` を組み合わせたものと同等ですが、パフォーマンスを向上させるためにより特化した表現を使用することができます。

{include 0 Monads.Zoo.Id}

{include 0 Monads.Zoo.State}

{include 0 Monads.Zoo.Reader}

{include 0 Monads.Zoo.Option}

{include 0 Monads.Zoo.Except}

{include 0 Monads.Zoo.Combined}
