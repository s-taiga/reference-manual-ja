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
#doc (Manual) "Laws" =>
-/
#doc (Manual) "規則（Laws）" =>
%%%
tag := "monad-laws"
%%%

```lean (show := false)
section Laws
universe u u' v
axiom f : Type u → Type v
axiom m : Type u → Type v
variable [Functor f]
variable [Applicative f]
variable [Monad m]
axiom α : Type u'
axiom β : Type u'
axiom γ : Type u'
axiom x : f α
```

::::keepEnv
```lean (show := false)
section F
variable {f : Type u → Type v} [Functor f] {α β : Type u} {g : α → β} {h : β → γ} {x : f α}
```

:::comment
Having {name Functor.map}`map`, {name Pure.pure}`pure`, {name Seq.seq}`seq`, and {name Bind.bind}`bind` operators with the appropriate types is not really sufficient to have a functor, applicative functor, or monad.
These operators must additionally satisfy certain axioms, which are often called the {deftech}_laws_ of the type class.

:::

演算子 {name Functor.map}`map` ・ {name Pure.pure}`pure` ・ {name Seq.seq}`seq` ・ {name Bind.bind}`bind` が適切な型を持っているだけでは、関手・アプリカティブ関手・モナドを持つには十分ではありません。これらの演算子はさらに特定の公理を満たす必要があり、これはしばしば型クラスの {deftech}_規則_ （law）と呼ばれます。

:::comment
For a functor, the {name Functor.map}`map` operation must preserve identity and function composition. In other words, given a purported {name}`Functor` {lean}`f`, for all {lean}`x`​` : `​{lean}`f α`:
 * {lean}`id <$> x = x`, and
 * for all function {lean}`g` and {lean}`h`, {lean}`(h ∘ g) <$> x = h <$> g <$> x`.

:::

関手の場合、 {name Functor.map}`map` 演算は恒等関数と関数の合成を保持しなければなりません。言い換えると、 {name}`Functor` {lean}`f` が与えられた時、すべての {lean}`x`​` : `​{lean}`f α` に対して以下が成り立つことが必要です：
 * {lean}`id <$> x = x`
 * 全ての関数 {lean}`g` と {lean}`h` に対して、 {lean}`(h ∘ g) <$> x = h <$> g <$> x`

:::comment
Instances that violate these assumptions can be very surprising!
Additionally, because {lean}`Functor` includes {name Functor.mapConst}`mapConst` to enable instances to provide a more efficient implementation, a lawful functor's {name Functor.mapConst}`mapConst` should be equivalent to its default implementation.

:::

これらの仮定に反したインスタンスは非常に驚くようなものになりえます！さらに、 {lean}`Functor` には {name Functor.mapConst}`mapConst` が含まれており、インスタンスがより効率的な実装を提供できるようになっているため、合法的な関手の {name Functor.mapConst}`mapConst` はデフォルトの実装と同等であるべきです。

:::comment
The Lean standard library does not require profs of these properties in every instance of {name}`Functor`.
Nonetheless, if an instance violates them, then it should be considered a bug.
When proofs of these properties are necessary, an instance implicit parameter of type {lean}`LawfulFunctor f` can be used.
The {name}`LawfulFunctor` class includes the necessary proofs.

:::

Lean 標準ライブラリは {name}`Functor` のすべてのインスタンスにこれらの性質の証明を要求しているわけではありません。それにもかかわらず、インスタンスがそれらに違反する場合、それはバグとみなされるべきです。これらの性質の証明が必要な場合、 {lean}`LawfulFunctor f` 型のインスタンス暗黙パラメータを使用することができます。 {lean}`LawfulFunctor` クラスには必要な証明が含まれています。

{docstring LawfulFunctor}

```lean (show := false)
end F
```
::::

:::comment
In addition to proving that the potentially-optimized {name}`SeqLeft.seqLeft` and {name}`SeqRight.seqRight` operations are equivalent to their default implementations, Applicative functors {lean}`f` must satisfy four laws.

:::

最適化される可能性のある {name}`SeqLeft.seqLeft` と {name}`SeqRight.seqRight` の操作がデフォルト実装と同等であることを証明することに加え、アプリカティブ関手 {lean}`f` は4つの規則を満たさなければなりません。

{docstring LawfulApplicative}

:::comment
The {deftech}[monad laws] specify that {name}`pure` followed by {name}`bind` should be equivalent to function application (that is, {name}`pure` has no effects), that {name}`bind` followed by {name}`pure` around a function application is equivalent to {name Functor.map}`map`, and that {name}`bind` is associative.

:::

{deftech}[モナド則] （monad laws）では、 {name}`pure` の後に {name}`bind` が続いたものは関数適用と同等であること（つまり {name}`pure` は何の作用も持たない）、関数適用に対して {name}`bind` の後に {name}`pure` が続いたものは {name Functor.map}`map` と同等であること、 {name}`bind` が結合的であることを指定します。

{docstring LawfulMonad}

{docstring LawfulMonad.mk'}
