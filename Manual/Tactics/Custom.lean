/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

import Manual.Tactics.Reference
import Manual.Tactics.Conv

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean.Elab.Tactic

/-
#doc (Manual) "Custom Tactics" =>
-/
#doc (Manual) "カスタムタクティク（Custom Tactics）" =>
%%%
tag := "custom-tactics"
%%%


```lean (show := false)
open Lean
```

:::comment
Tactics are productions in the syntax category `tactic`. {TODO}[xref macro for syntax\_cats]
Given the syntax of a tactic, the tactic interpreter is responsible for carrying out actions in the tactic monad {name}`TacticM`, which is a wrapper around Lean's term elaborator that keeps track of the additional state needed to execute tactics.
A custom tactic consists of an extension to the `tactic` category along with either:
 * a {tech}[macro] that translates the new syntax into existing syntax, or
 * an elaborator that carries out {name}`TacticM` actions to implement the tactic.

:::

タクティクは構文カテゴリ `tactic` に含まれるプロダクションです。タクティクの構文が与えられると、タクティクのインタプリタはタクティクモナド {name}`TacticM` でアクションを実行します。これは Lean の項エラボレータのラッパーで、タクティクの実行にあたって追加で状態を追跡するものです。カスタムタクティクは `tactic` カテゴリの拡張と、以下のいずれかから構成されます：
 * 新しい構文を既存の構文に変換する {tech}[macro]
 * {name}`TacticM` アクションを実行してタクティクを実装するエラボレータ

:::comment
# Tactic Macros
:::

# タクティクマクロ（Tactic Macros）
%%%
tag := "tactic-macros"
%%%


:::comment
The easiest way to define a new tactic is as a {tech}[macro] that expands into already-existing tactics.
Macro expansion is interleaved with tactic execution.
The tactic interpreter first expands tactic macros just before they are to be interpreted.
Because tactic macros are not fully expanded prior to running a tactic script, they can use recursion; as long as the recursive occurrence of the macro syntax is beneath a tactic that can be executed, there will not be an infinite chain of expansion.

:::

新しいタクティクを定義する最も簡単な方法は、 {tech}[macro] として既存のタクティクに展開することです。マクロ展開はタクティクの実行と同時に行われます。タクティクのインタプリタは、まずタクティクマクロを解釈する直前に展開します。タクティクマクロはタクティクスクリプトを実行する前に完全には展開されないため、再帰を使用することができます；マクロ構文の再帰的な出現が実行可能なタクティクの下にある限り、マクロの展開は無限に連鎖しません。

:::::keepEnv
:::comment
::example "Recursive tactic macro"
:::
::::example "再帰的なタクティクマクロ"
:::comment
This recursive implementation of a tactic akin to {tactic}`repeat` is defined via macro expansion.
When the argument `$t` fails, the recursive occurrence of {tactic}`rep` is never invoked, and is thus never macro expanded.
:::

以下の {tactic}`repeat` に似たタクティクの再帰的な実装は、マクロ展開によって定義されます。引数 `$t` が失敗した時、 {tactic}`rep` の再帰的な発生は絶対に呼び出されず、したがってマクロ展開も決して行われません。

```lean
syntax "rep" tactic : tactic
macro_rules
  | `(tactic|rep $t) =>
  `(tactic|
    first
      | $t; rep $t
      | skip)

example : 0 ≤ 4 := by
  rep (apply Nat.le.step)
  apply Nat.le.refl
```
::::
:::::

:::comment
Like other Lean macros, tactic macros are {tech key:="hygiene"}[hygienic].
References to global names are resolved when the macro is defined, and names introduced by the tactic macro cannot capture names from its invocation site.

:::

他の Lean のマクロと同様に、タクティクマクロは {tech key:="hygiene"}[hygienic] です。グローバル名への参照はマクロが定義された時に解決され、タクティクマクロによって導入された名前はその呼び出しサイトから名前をキャプチャすることはできません。

:::comment
When defining a tactic macro, it's important to specify that the syntax being matched or constructed is for the syntax category `tactic`.
Otherwise, the syntax will be interpreted as that of a term, which will match against or construct an incorrect AST for tactics.

:::

タクティクマクロを定義するとき、パターンマッチと構成に用いられる構文が構文カテゴリ `tactic` のものであることを指定することが重要です。そうでない場合、構文は項の構文として解釈され、タクティクのための正しくない AST とマッチしたり構成されたりします。

:::comment
## Extensible Tactic Macros
:::

## 拡張可能なタクティクマクロ（Extensible Tactic Macros）
%%%
tag := "tactic-macro-extension"
%%%



:::comment
Because macro expansion can fail, {TODO}[xref] multiple macros can match the same syntax, allowing backtracking.
Tactic macros take this further: even if a tactic macro expands successfully, if the expansion fails when interpreted, the tactic interpreter will attempt the next expansion.
This is used to make a number of Lean's built-in tactics extensible—new behavior can be added to a tactic by adding a {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` declaration.

:::

マクロの展開は失敗することがあるため、複数のマクロが同じ構文にマッチすることができ、バックトラックが可能になります。タクティクマクロはこれをさらに推し進めます：タクティクマクロの展開が成功しても解釈時に展開に失敗すると、タクティクのインタプリタは次の展開を試みます。これは Lean の多くの組み込みタクティクを拡張可能にするためにしようされます。 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 宣言を追加することで新しい動作をタクティクに追加できます。

:::::keepEnv
:::comment
::example "Extending {tactic}`trivial`"
:::
::::example "{tactic}`trivial` の拡張"

:::comment
The {tactic}`trivial`, which is used by many other tactics to quickly dispatch subgoals that are not worth bothering the user with, is designed to be extended through new macro expansions.
Lean's default {lean}`trivial` can't solve {lean}`IsEmpty []` goals:
:::

{tactic}`trivial` はユーザを煩わせる価値のないサブゴールを素早くディスパッチするために、他の多くのタクティクから使用されますが、新しいマクロ展開によって拡張できるように設計されています。Lean のデフォルトの {lean}`trivial` は {lean}`IsEmpty []` ゴールを解決できません：

```lean (error := true)
def IsEmpty (xs : List α) : Prop :=
  ¬ xs ≠ []

example (α : Type u) : IsEmpty (α := α) [] := by trivial
```

:::comment
The error message is an artifact of {tactic}`trivial` trying {tactic}`assumption` last.
Adding another expansion allows {tactic}`trivial` to take care of these goals:
:::

このエラーメッセージは {tactic}`trivial` が最後に {tactic}`assumption` を試したことによるものです。ここで別の拡張を追加することで {tactic}`trivial` がこれらのゴールを対応するようにできます：

```lean
def emptyIsEmpty : IsEmpty (α := α) [] := by simp [IsEmpty]

macro_rules | `(tactic|trivial) => `(tactic|exact emptyIsEmpty)

example (α : Type u) : IsEmpty (α := α) [] := by
  trivial
```
::::
:::::

:::::keepEnv
:::comment
::example "Expansion Backtracking"
:::
::::example "展開のバックトラック"
:::comment
Macro expansion can induce backtracking when the failure arises from any part of the expanded syntax.
An infix version of {tactic}`first` can be defined by providing multiple expansions in separate {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` declarations:
:::

マクロ展開は、展開された構文のいずれかの部分で失敗した場合にバックトラックを引き起こす可能性があります。複数の展開を別々の {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 宣言で定義することで、 {tactic}`first` の中置バージョンを定義することができます：

```lean
syntax tactic "<|||>" tactic : tactic
macro_rules
  | `(tactic|$t1 <|||> $t2) => pure t1
macro_rules
  | `(tactic|$t1 <|||> $t2) => pure t2

example : 2 = 2 := by
  rfl <|||> apply And.intro

example : 2 = 2 := by
  apply And.intro <|||> rfl
```

:::comment
Multiple {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` declarations are needed because each defines a pattern-matching function that will always take the first matching alternative.
Backtracking is at the granularity of {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` declarations, not their individual cases.
:::

複数の {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 宣言は、それぞれがパターンマッチ関数を定義し、常に最初にマッチする選択肢を取ることができるようにするために必要です。バックトラックは {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 宣言の粒度であり、個々のケースではありません。

::::
:::::


:::comment
# The Tactic Monad
:::

# タクティクモナド（The Tactic Monad）
%%%
tag := "tactic-monad"
%%%


::: planned 67
 * Relationship to {name}`Lean.Elab.Term.TermElabM`, {name}`Lean.Meta.MetaM`
 * Overview of available effects
 * Checkpointing
:::

{docstring Lean.Elab.Tactic.Tactic}

{docstring Lean.Elab.Tactic.TacticM}

{docstring Lean.Elab.Tactic.run}

{docstring Lean.Elab.Tactic.runTermElab}

:::comment
## Control

:::

## 制御（Control）

{docstring Lean.Elab.Tactic.tryTactic}

{docstring Lean.Elab.Tactic.tryTactic?}

:::comment
## Expressions

:::

## 式（Expressions）

{docstring Lean.Elab.Tactic.ensureHasNoMVars}

{docstring Lean.Elab.Tactic.getFVarId}

{docstring Lean.Elab.Tactic.getFVarIds}

{docstring Lean.Elab.Tactic.sortMVarIdsByIndex}

{docstring Lean.Elab.Tactic.sortMVarIdArrayByIndex}

:::comment
## Source Locations

:::

## ソース位置（Source Locations）

{docstring Lean.Elab.Tactic.withLocation}

:::comment
## Goals

:::

## ゴール（Goals）

{docstring Lean.Elab.Tactic.getGoals}

{docstring Lean.Elab.Tactic.setGoals}

{docstring Lean.Elab.Tactic.getMainGoal}

{docstring Lean.Elab.Tactic.getMainTag}

{docstring Lean.Elab.Tactic.closeMainGoal}

{docstring Lean.Elab.Tactic.focus}

{docstring Lean.Elab.Tactic.tagUntaggedGoals}

{docstring Lean.Elab.Tactic.getUnsolvedGoals}

{docstring Lean.Elab.Tactic.pruneSolvedGoals}

{docstring Lean.Elab.Tactic.appendGoals}

{docstring Lean.Elab.Tactic.closeMainGoalUsing}

:::comment
## Term Elaboration

:::

## 項エラボレーション（Term Elaboration）

{docstring Lean.Elab.Tactic.elabTerm}

{docstring Lean.Elab.Tactic.elabTermEnsuringType}

{docstring Lean.Elab.Tactic.elabTermWithHoles}


:::comment
## Low-Level Operations

:::

## 低レベル操作（Low-Level Operations）

:::comment
These operations are primarily used as part of the implementation of {name}`TacticM` or of particular tactics.
It's rare that they are useful when implementing new tactics.

:::

これらの操作は主に {name}`TacticM` や特定のタクティクの実装の一部として使用されます。新しいタクティクを実装する際に役に立つことは稀です。

:::comment
### Monad Class Implementations

:::

### モナドクラスの実装（Monad Class Implementations）

:::comment
These operations are exposed through standard Lean monad type classes.

:::

これらの操作は標準的な Lean のモナド型クラスを通して公開されます。

{docstring Lean.Elab.Tactic.tryCatch}

{docstring Lean.Elab.Tactic.liftMetaMAtMain}

{docstring Lean.Elab.Tactic.getMainModule}

{docstring Lean.Elab.Tactic.orElse}

:::comment
### Macro Expansion

:::

### マクロ展開（Macro Expansion）

{docstring Lean.Elab.Tactic.getCurrMacroScope}

{docstring Lean.Elab.Tactic.adaptExpander}

:::comment
### Case Analysis

:::

### ケース分析（Case Analysis）

{docstring Lean.Elab.Tactic.elabCasesTargets}

:::comment
### Simplifier

:::

### 単純化器（Simplifier）

{docstring Lean.Elab.Tactic.elabSimpArgs}

{docstring Lean.Elab.Tactic.elabSimpConfig}

{docstring Lean.Elab.Tactic.elabSimpConfigCtxCore}

{docstring Lean.Elab.Tactic.dsimpLocation'}

{docstring Lean.Elab.Tactic.elabDSimpConfigCore}

:::comment
### Attributes

:::

### 属性（Attributes）

{docstring Lean.Elab.Tactic.tacticElabAttribute}

{docstring Lean.Elab.Tactic.mkTacticAttribute}
