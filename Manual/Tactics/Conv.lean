/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

/-
#doc (Manual) "Targeted Rewriting with {tactic}`conv`" =>
-/
#doc (Manual) "{tactic}`conv` によるターゲットの書き換え（Targeted Rewriting with {tactic}`conv` ）" =>
%%%
tag := "conv"
%%%


:::comment
The {tactic}`conv`, or conversion, tactic allows targeted rewriting within a goal.
The argument to {tactic}`conv` is written in a separate language that interoperates with the main tactic language; it features commands to navigate to specific subterms within the goal along with commands that allow these subterms to be rewritten.
{tactic}`conv` is useful when rewrites should only be applied in part of a goal (e.g. only on one side of an equality), rather than across the board, or when rewrites should be applied underneath a binder that prevents tactics like {tactic}`rw` from accessing the term.

:::

{tactic}`conv` 、もしくは変換タクティクはゴール内のターゲットを絞った書き換えを可能にします。 {tactic}`conv` の引数はメインのタクティク言語と相互に連携する別の言語で記述されます；これはゴール内の特定の部分項に移動するコマンドと、これらの部分項を書き換えるコマンドを備えています。 {tactic}`conv` は書き換えをゴール全体ではなく、ゴールの一部（例えば等式の片側のみ）にのみ適用する場合や、 {tactic}`rw` のようなタクティクが項にアクセスするのを防いでしまう束縛子の中の書き換えを適用する場合に便利です。

:::comment
The conversion tactic language is very similar to the main tactic language: it uses the same proof states, tactics work primarily on the main goal and may either fail or succeed with a sequence of new goals, and macro expansion is interleaved with tactic execution.
Unlike the main tactic language, in which tactics are intended to eventually solve goals, the {tactic}`conv` tactic is used to _change_ a goal so that it becomes amenable to further processing in the main tactic language.
Goals that are intended to be rewritten with {tactic}`conv` are shown with a vertical bar instead of a turnstile.

:::

変換タクティク言語はメインのタクティク言語に非常に似ています：同じ証明状態を使用し、タクティクは主にメインゴールに対して作用し、新しいゴールの列で失敗または成功する可能性があり、マクロ展開はタクティクの実行と交互に行われます。タクティクが最終的にゴールを解決するためのものであるメインのタクティク言語とは異なり、 {tactic}`conv` はゴールを _変更_ するために用いられます。これによってゴールはその後のメインのタクティク言語で容易に処理できるようになります。 {tactic}`conv` で書き換えることを意図しているゴールはターンスタイルの代わりに縦棒で表示されます。

:::tactic "conv"
:::

:::comment
::example "Navigation and Rewriting with {tactic}`conv`"
:::
::::example "{tactic}`conv` による移動と書き換え"

:::comment
In this example, there are multiple instances of addition, and {tactic}`rw` would by default rewrite the first instance that it encounters.
Using {tactic}`conv` to navigate to the specific subterm before rewriting leaves {tactic}`rw` no choice but to rewrite the correct term.

:::

この例では、加算のインスタンスが複数存在し、 {tactic}`rw` はデフォルトで最初に出会ったインスタンスを書き換えてしまいます。書き換える前に特定の部分項へ移動するために {tactic}`conv` を使用すると、 {tactic}`rw` は正しい項を書き換える以外に選択肢がなくなります。

```lean
example (x y z : Nat) : x + (y + z) = (x + z) + y := by
  conv =>
    lhs
    arg 2
    rw [Nat.add_comm]
  rw [Nat.add_assoc]
```

::::

:::comment
::example "Rewriting Under Binders with {tactic}`conv`"
:::
::::example "{tactic}`conv` による束縛子の中の書き換え"

:::comment
In this example, addition occurs under binders, so {tactic}`rw` can't be used.
However, after using {tactic}`conv` to navigate to the function body, it succeeds.
The nested use of {tactic}`conv` causes control to return to the current position in the term after performing further conversions on one of its subterms.
Because the goal is a reflexive equation after rewriting, {tactic}`conv` automatically closes it.

:::

この例では、加算は束縛子の中に存在するため、 {tactic}`rw` は使えません。しかし、 {tactic}`conv` を使用して関数本体に移動すると成功します。入れ子になった {tactic}`conv` の使用は、その部分項の1つに対してさらなる変換を実行したのち、制御を項の中の現在の位置に戻します。ゴールは書き換え後の反射性の等式であるため、 {tactic}`conv` は自動的にこれを閉じます。

```lean
example :
    (fun (x y z : Nat) =>
      x + (y + z))
    =
    (fun x y z =>
      (z + x) + y)
  := by
  conv =>
    lhs
    intro x y z
    conv =>
      arg 2
      rw [Nat.add_comm]
    rw [← Nat.add_assoc]
    arg 1
    rw [Nat.add_comm]
```

::::

:::comment
# Control Structures
%%%
tag := "conv-control"
%%%


:::

# 制御構造（Control Structures）

:::conv first show := "first"
:::

:::conv convTry_ show := "try"
:::

:::conv «conv_<;>_» show:="<;>"
:::

:::conv convRepeat_ show := "repeat"
:::

:::conv skip show:= "skip"
:::

:::conv nestedConv show:= "{ ... }"
:::

:::conv paren show:= "( ... )"
:::

:::conv convDone show:= "done"
:::

:::comment
# Goal Selection
%%%
tag := "conv-goals"
%%%


:::

# ゴールの選択（Goal Selection）

:::conv allGoals show:= "all_goals"
:::

:::conv anyGoals show:= "any_goals"
:::

:::conv case show:= "case ... => ..."
:::

:::conv case' show:= "case' ... => ..."
:::

:::conv «convNext__=>_» show:= "next ... => ..."
:::

:::conv focus show := "focus"
:::

:::conv «conv·._» show := ". ..."
:::

:::conv «conv·._» show := "· ..."
:::

:::conv failIfSuccess show := "fail_if_success"
:::


:::comment
# Navigation
%%%
tag := "conv-nav"
%%%


:::

# 移動（Navigation）

:::conv lhs show:= "lhs"
:::

:::conv rhs show:= "rhs"
:::

:::conv fun show:= "fun"
:::

:::conv congr show:= "congr"
:::

:::conv arg show:= "arg [@]i"
:::

:::syntax Lean.Parser.Tactic.Conv.enterArg
```grammar
$i:num
```
```grammar
@$i:num
```
```grammar
$x:ident
```
:::

:::conv enter show := "enter"
:::


:::conv pattern show:= "pattern"
:::

:::conv ext show:= "ext"
:::

:::conv convArgs show := "args"
:::

:::conv convLeft show := "left"
:::

:::conv convRight show := "right"
:::

:::conv convIntro___ show := "intro"
:::

:::comment
# Changing the Goal
:::

# ゴールの変更（Changing the Goal）
%%%
tag := "conv-change"
%%%


:::comment
## Reduction
%%%
tag := "conv-reduction"
%%%


:::

## 簡約（Reduction）

:::conv whnf show:= "whnf"
:::

:::conv reduce show:= "reduce"
:::

:::conv zeta show:= "zeta"
:::

:::conv delta show:= "delta"
:::

:::conv unfold show:= "unfold"
:::

:::comment
## Simplification
:::

## 単純化（Simplification）
%%%
tag := "conv-simp"
%%%

:::conv simp show:= "simp"
:::

:::conv dsimp show:= "dsimp"
:::

:::conv simpMatch show:= "simp_match"
:::

:::comment
## Rewriting
%%%
tag := "conv-rw"
%%%

:::

## 書き換え（Rewriting）

:::conv change show:= "change"
:::

:::conv rewrite show:= "rewrite"
:::

:::conv convRw__ show := "rw"
:::

:::conv convErw__ show := "erw"
:::

:::conv convApply_ show := "apply"
:::

:::comment
# Nested Tactics
%%%
tag := "conv-nested"
%%%


:::

# 入れ子のタクティク（Nested Tactics）

:::tactic Lean.Parser.Tactic.Conv.convTactic
:::

:::conv nestedTactic show:= "tactic"
:::

:::conv nestedTacticCore show:= "tactic'"
:::

:::tactic Lean.Parser.Tactic.Conv.convTactic show:= "conv'"
:::

:::conv convConvSeq show := "conv => ..."
:::


:::comment
# Debugging Utilities
%%%
tag := "conv-debug"
%%%

:::

# デバッグ用ユーティリティ（Debugging Utilities）

:::conv convTrace_state show:= "trace_state"
:::


:::comment
# Other
%%%
tag := "conv-other"
%%%

:::

# その他（Other）

:::conv convRfl show:= "rfl"
:::

:::conv normCast show := "norm_cast"
:::
