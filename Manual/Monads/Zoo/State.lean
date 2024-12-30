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
#doc (Manual) "State" =>
-/
#doc (Manual) "状態（State）" =>
%%%
tag := "state-monads"
%%%

:::comment
{tech}[State monads] provide access to a mutable value.
The underlying implementation may a tuple to simulate mutability, or it may use something like {name}`ST.Ref` to ensure mutation.
Even those implementations that use a tuple may in fact use mutation at run-time due to Lean's use of mutation when there are unique references to values, but this requires a programming style that prefers {name}`modify` and {name}`modifyGet` over {name}`get` and {name}`set`.

:::

{tech}[状態モナド] は可変な値へのアクセスを提供します。基礎となる実装は、タプルを使用して可変性をシミュレートしたものとすることもでき、また {name}`ST.Ref` のようなものを使用してミューテーションを保証することもできます。タプルを使用する実装であっても、値への一意な参照がある場合には Lean がミューテーションを使用するため、実際には実行時にミューテーションを使用する可能性がありますが、これには {name}`get` や {name}`set` よりも {name}`modify` や {name}`modifyGet` を好むプログラミングスタイルが必要です。

:::comment
# General State API
:::

# 一般的な状態の API（General State API）


{docstring MonadState}

{docstring get}

{docstring modify}

{docstring modifyGet}

{docstring getModify}

{docstring MonadStateOf}

{docstring getThe}

{docstring modifyThe}

{docstring modifyGetThe}

:::comment
# Tuple-Based State Monads
:::

# タプルベースの状態モナド（Tuple-Based State Monads）


```lean (show := false)
variable {α σ : Type u}
```

:::comment
The tuple-based state monads represent a computation with states that have type {lean}`σ` yielding values of type {lean}`α` as functions that take a starting state and yield a value paired with a final state, e.g. {lean}`σ → α × σ`.
The {name}`Monad` operations thread the state correctly through the computation.

:::

タプルベースの状態モナドは {lean}`σ` 型の値をもたらす {lean}`α` 型の状態を持つ計算を、例えば {lean}`σ → α × σ` のように開始状態を受け取り、最終状態と対になった値をもたらす関数として表現します。 {name}`Monad` 演算は、計算を通して状態を正しくスレッド化します。

{docstring StateM}

{docstring StateT}

{docstring StateT.run}

{docstring StateT.get}

{docstring StateT.set}

{docstring StateT.orElse}

{docstring StateT.failure}

{docstring StateT.run'}

{docstring StateT.bind}

{docstring StateT.modifyGet}

{docstring StateT.lift}

{docstring StateT.map}

{docstring StateT.pure}

:::comment
# State Monads in Continuation Passing Style
:::

# 継続渡しスタイルの状態モナド（State Monads in Continuation Passing Style）


:::comment
Continuation-passing-style state monads represent stateful computations as functions that, for any type whatsoever, take an initial state and a continuation (modeled as a function) that accepts a value and an updated state.
An example of such a type is {lean}`(δ : Type u) → σ → (α → σ → δ) → δ`, though {lean}`StateCpsT` is a transformer that can be applied to any monad.
State monads in continuation passing style have different performance characteristics than tuple-based state monads; for some applications, it may be worth benchmarking them.


:::

継続渡しスタイルの状態モナドは、どのような型に対しても初期状態と、値・更新された状態を受け取る継続（関数としてモデル化されます）を受け取る関数として状態を持つ計算を表現します。このような型の例は {lean}`(δ : Type u) → σ → (α → σ → δ) → δ` ですが、 {lean}`StateCpsT` はどのモナドにも適用できる変換子です。継続渡しスタイルの状態モナドはタプルベースの状態モナドとは異なるパフォーマンス特性を持ちます；アプリケーションによってはベンチマークを取る価値があるかもしれません。

```lean (show := false)
/-- info: (δ : Type u) → σ → (α → σ → Id δ) → δ -/
#guard_msgs in
#reduce (types := true) StateCpsT σ Id α
```
{docstring StateCpsT}

{docstring StateCpsT.lift}

{docstring StateCpsT.runK}

{docstring StateCpsT.run'}

{docstring StateCpsT.run}

:::comment
# State Monads from Mutable References
:::

# 可変参照からの状態モナド（State Monads from Mutable References）


```lean (show := false)
variable {m : Type → Type} {σ ω : Type} [STWorld σ m]
```

:::comment
The monad {lean}`StateRefT σ m` is a specialized state monad transformer that can be used when {lean}`m` is a monad to which {name}`ST` computations can be lifted.
It implements the operations of {name}`MonadState` using an {name}`ST.Ref`, rather than pure functions.
This ensures that mutation is actually used at run time.

:::

モナド {lean}`StateRefT σ m` は {lean}`m` が {name}`ST` の計算を持ち上げることができるモナドである場合に使用できる、特殊な状態モナド変換子です。 {name}`MonadState` の演算は、純粋な関数ではなく {name}`ST.Ref` を使用して実装されます。これにより、ミューテーションが実行時に実際に使用されることが保証されます。

:::comment
{name}`ST` and {name}`EST` require a phantom type parameter that's used together with {name}`runST`'s polymorphic function argument to encapsulate mutability.
Rather than require this as a parameter to the transformer, an auxiliary type class {name}`STWorld` is used to propagate it directly from {lean}`m`.

:::

{name}`ST` と {name}`EST` は可変性をカプセル化するために {name}`runST` の多相関数引数と一緒に使用される幽霊型パラメータを必要とします。これを変換子のパラメータとして要求するのではなく、補助の型クラス {name}`STWorld` を使用して {lean}`m` から直接伝播させます。

:::comment
The transformer itself is defined as a {ref "syntax-ext"}[syntax extension] and an {ref "elaborators"}[elaborator], rather than an ordinary function.
This is because {name}`STWorld` has no methods: it exists only to propagate information from the inner monad to the transformed monad.
Nonetheless, its instances are terms; keeping them around could lead to unnecessarily large types.

:::

この変換子自体は普通の関数ではなく、 {ref "syntax-ext"}[構文拡張] と {ref "elaborators"}[エラボレータ] として定義されています。これは {name}`STWorld` がメソッドを持たないためです：これは内側のモナドから変換後のモナドに情報を伝播するためだけに存在します。それにもかかわたず、そのインスタンスは項です；これを保持すると不必要に大きい型になる可能性があります。

{docstring STWorld}

::::syntax term
:::comment
The syntax for {lean}`StateRefT σ m` accepts two arguments:

:::

{lean}`StateRefT σ m` の構文は2つの引数を取ります：

```grammar
StateRefT $_ $_
```

:::comment
Its elaborator synthesizes an instance of {lean}`STWorld ω m` to ensure that {lean}`m` supports mutable references.
Having discovered the value of {lean}`ω`, it then produces the term {lean}`StateRefT' ω σ m`, discarding the synthesized instance.
:::

そのエラボレータは {lean}`STWorld ω m` のインスタンスを統合し、 {lean}`m` が可変参照をサポートしていることを保証します。 {lean}`ω` の値を発見した後、 {lean}`StateRefT' ω σ m` の項を生成し、統合されたインスタンスを破棄します。

::::

{docstring StateRefT'}

{docstring StateRefT'.get}

{docstring StateRefT'.set}

{docstring StateRefT'.modifyGet}

{docstring StateRefT'.run}

{docstring StateRefT'.run'}

{docstring StateRefT'.lift}
