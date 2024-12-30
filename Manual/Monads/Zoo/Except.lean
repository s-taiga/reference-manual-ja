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
#doc (Manual) "Exceptions" =>
-/
#doc (Manual) "例外（Exceptions）" =>
%%%
tag := "exception-monads"
%%%

:::comment
Exception monads describe computations that terminate early (fail).
Failing computations provide their caller with an _exception_ value that describes _why_ they failed.
In other words, computations either return a value or an exception.
The inductive type {name}`Except` captures this pattern, and is itself a monad.

:::

例外モナドは早期に終了（失敗）する計算を記述します。失敗した計算は、 _なぜ_ 失敗したかを示す _例外_ 値を呼び出し元に提供します。言い換えると、計算は値か例外を返します。帰納型 {name}`Except` はこのパターンを捕捉しており、それ自体がモナドです。

:::comment
# Exceptions
:::

# 例外（Exceptions）


{docstring Except}

{docstring Except.pure}

{docstring Except.bind}

{docstring Except.map}

{docstring Except.mapError}

{docstring Except.tryCatch}

{docstring Except.orElseLazy}

{docstring Except.isOk}

{docstring Except.toOption}

{docstring Except.toBool}


:::comment
# Type Class
:::

# 型クラス（Type Class）


{docstring MonadExcept}

{docstring MonadExcept.ofExcept}

{docstring MonadExcept.orElse}

{docstring MonadExcept.orelse'}

{docstring MonadExceptOf}

{docstring throwThe}

{docstring tryCatchThe}

:::comment
# “Finally” Computations
:::

# 「finally」の計算（“Finally” Computations）


{docstring MonadFinally}

:::comment
# Transformer
:::

# 変換子（Transformer）


{docstring ExceptT}

{docstring ExceptT.lift}

{docstring ExceptT.run}

{docstring ExceptT.pure}

{docstring ExceptT.bind}

{docstring ExceptT.bindCont}

{docstring ExceptT.tryCatch}

{docstring ExceptT.mk}

{docstring ExceptT.map}

{docstring ExceptT.adapt}


:::comment
# Exception Monads in Continuation Passing Style
:::

# 継続渡しスタイルの例外モナド（Exception Monads in Continuation Passing Style）


```lean (show := false)
universe u
variable (α : Type u)
variable (ε : Type u)
variable {m : Type u → Type v}
```

:::comment
Continuation-passing-style exception monads represent potentially-failing computations as functions that take success and failure continuations, both of which return the same type, returning that type.
They must work for _any_ return type.
An example of such a type is {lean}`(β : Type u) → (α → β) → (ε → β) → β`.
{lean}`ExceptCpsT` is a transformer that can be applied to any monad, so {lean}`ExceptCpsT ε m α` is actually defined as {lean}`(β : Type u) → (α → m β) → (ε → m β) → m β`.
Exception monads in continuation passing style have different performance characteristics than {name}`Except`-based state monads; for some applications, it may be worth benchmarking them.

:::

継続渡しスタイルの例外モナドは、失敗する可能性のある計算を、成功と失敗を取る関数として表します。この継続はどちらも同じ型を返し、この関数はその型を返します。例外モナドは _どのような_ 戻り値の型でも動作しなければなりません。このような型の例は {lean}`(β : Type u) → (α → β) → (ε → β) → β` です。 {lean}`ExceptCpsT` は任意のモナドに適用できる変換子であるため、 {lean}`ExceptCpsT ε m α` は実際には {lean}`(β : Type u) → (α → m β) → (ε → m β) → m β` と定義されています。継続渡しスタイルの例外モナドは、 {name}`Except` ベースの状態モナドとは異なるパフォーマンス特性を持ちます；アプリケーションによってはベンチマークを取る価値があるかもしれません。

```lean (show := false)
/-- info: (β : Type u) → (α → m β) → (ε → m β) → m β -/
#guard_msgs in
#reduce (types := true) ExceptCpsT ε m α
```

{docstring ExceptCpsT}

{docstring ExceptCpsT.runCatch}

{docstring ExceptCpsT.runK}

{docstring ExceptCpsT.run}

{docstring ExceptCpsT.lift}
