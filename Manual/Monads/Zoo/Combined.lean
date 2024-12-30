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
#doc (Manual) "Combined Error and State Monads" =>
-/
#doc (Manual) "エラーと状態モナドの結合（Combined Error and State Monads）" =>

```lean (show := false)
variable (ε : Type u) (σ σ' : Type u) (α : Type u)
```

:::comment
The {name}`EStateM` monad has both exceptions and mutable state.
{lean}`EStateM ε σ α` is logically equivalent to {lean}`ExceptT ε (StateM σ) α`.
While {lean}`ExceptT ε (StateM σ)` evaluates to the type {lean}`σ → Except ε α × σ`, the type {lean}`EStateM ε σ α` evaluates to {lean}`σ → EStateM.Result ε σ α`.
{name}`EStateM.Result` is an inductive type that's very similar to {name}`Except`, except both constructors have an additional field for the state.
In compiled code, this representation removes one level of indirection from each monadic bind.

:::

{name}`EStateM` モナドは例外と可変状態の両方を持ちます。 {lean}`EStateM ε σ α` は {lean}`ExceptT ε (StateM σ) α` と論理的に等価です。 {lean}`ExceptT ε (StateM σ)` が {lean}`σ → Except ε α × σ` 型に評価されるのに対して、 {lean}`EStateM ε σ α` は {lean}`σ → EStateM.Result ε σ α` 型に評価されます。 {name}`EStateM.Result` は {name}`Except` とよく似た帰納型ですが、どちらのコンストラクタにも状態を表すフィールドが追加されています。コンパイルされたコードでは、この表現は各モナドの bind から1段階インダイレクションを取り除きます。

```lean (show := false)
/-- info: σ → Except ε α × σ -/
#guard_msgs in
#reduce (types := true) ExceptT ε (StateM σ) α

/-- info: σ → EStateM.Result ε σ α -/
#guard_msgs in
#reduce (types := true) EStateM ε σ α
```

{docstring EStateM}

{docstring EStateM.Result}

{docstring EStateM.run}

{docstring EStateM.run'}

{docstring EStateM.adaptExcept}

{docstring EStateM.fromStateM}

:::comment
# State Rollback
:::

# 状態のロールバック（State Rollback）


:::comment
Composing {name}`StateT` and {name}`ExceptT` in different orders causes exceptions to interact differently with state.
In one ordering, state changes are rolled back when exceptions are caught; in the other, they persist.
The latter option matches the semantics of most imperative programming languages, but the former is very useful for search-based problems.
Often, some but not all state should be rolled back; this can be achieved by “sandwiching” {name}`ExceptT` between two separate uses of {name}`StateT`.

:::

{name}`StateT` と {name}`ExceptT` を異なる順序で合成すると例外と状態の相互作用は異なるものになります。片方の順序では、例外が捕捉された時に状態の変更がロールバックされ、もう一方では状態が持続します。後者のオプションはほとんどの命令型プログラミング言語のセマンティックスに一致しますが、前者は検索ベースの問題に対して非常に便利です。またしばしば、すべてではなく一部の状態だけがロールバックされるべき場合もあります；これは {name}`ExceptT` を2つの {name}`StateT` で「サンドイッチ」することで実現できます。

:::comment
To avoid yet another layer of indirection via the use of {lean}`StateT σ (EStateM ε σ') α`, {name}`EStateM` offers the {name}`EStateM.Backtrackable` {tech}[type class].
This class specifies some part of the state that can be saved and restored.
{name}`EStateM` then arranges for the saving and restoring to take place around error handling.

:::

{lean}`StateT σ (EStateM ε σ') α` の使用によるさらに別のレイヤーからのインダイレクトを避けるために、 {name}`EStateM` は {name}`EStateM.Backtrackable` {tech}[型クラス] を提供します。このクラスは保存と復元が可能な状態の一部を指定します。 {name}`EStateM` はエラー処理を中心に保存と復元が行われるよう調整します。

{docstring EStateM.Backtrackable}

:::comment
There is a universally-applicable instance of {name EStateM.Backtrackable}`Backtrackable` that neither saves nor restores anything.
Because instance synthesis chooses the most recent instance first, the universal instance is used only if no other instance has been defined.

:::

{name EStateM.Backtrackable}`Backtrackable` には普遍的に適用可能なインスタンスがありますが、これは何も保存も復元もしません。インスタンス統合は最新のインスタンスを最初に選択するため、他のインスタンスが定義されていない場合にのみこの普遍的なインスタンスが使用されます。

{docstring EStateM.nonBacktrackable}

:::comment
# Implementations
:::

# 実装（Implementations）


:::comment
These functions are typically not called directly, but rather are accessed through their corresponding type classes.

:::

これらの関数は通常、直接呼び出されることはなく、対応する型クラスを通じてアクセスされます。

{docstring EStateM.map}

{docstring EStateM.pure}

{docstring EStateM.bind}

{docstring EStateM.orElse}

{docstring EStateM.orElse'}

{docstring EStateM.seqRight}

{docstring EStateM.tryCatch}

{docstring EStateM.throw}

{docstring EStateM.get}

{docstring EStateM.set}

{docstring EStateM.modifyGet}
