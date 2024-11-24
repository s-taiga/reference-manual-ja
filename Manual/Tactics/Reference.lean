/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.Papers
import Manual.Tactics.Reference.Simp


open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false



/-
#doc (Manual) "Tactic Reference" =>
-/
#doc (Manual) "タクティクリファレンス（Tactic Reference）" =>
%%%
tag := "tactic-ref"
%%%


:::comment
# Assumptions
:::

# 仮定（Assumptions）
%%%
tag := "tactic-ref-assumptions"
%%%


:::tactic Lean.Parser.Tactic.assumption
:::

:::tactic "apply_assumption"
:::

:::comment
# Quantifiers
:::

# 量化子（Quantifiers）
%%%
tag := "tactic-ref-quantifiers"
%%%


:::tactic "exists"
:::

:::tactic "intro"
:::


:::tactic "intros"
:::

:::tactic Lean.Parser.Tactic.introMatch (show := "intro | ... => ... | ... => ...")
:::

:::tactic "rintro"
:::


:::comment
# Relations
:::

# 関係（Relations）
%%%
tag := "tactic-ref-relations"
%%%


:::planned 47
 * Descriptions of the `symm` and `refl` and `trans` attributes
:::

:::tactic "rfl"
:::

:::tactic "rfl'"
:::


:::tactic Lean.Parser.Tactic.applyRfl
:::

:::tactic "symm"
:::

:::tactic "symm_saturate"
:::


:::tactic "calc"
:::


:::comment
## Equality
:::

## 等価性（Equality）
%%%
tag := "tactic-ref-equality"
%%%


:::tactic "subst"
:::

:::tactic "subst_eqs"
:::

:::tactic "subst_vars"
:::

:::tactic "congr"
:::

:::tactic "eq_refl"
:::

:::tactic "ac_rfl"
:::

:::comment
# Lemmas
:::

# 補題（Lemmas）
%%%
tag := "tactic-ref-lemmas"
%%%


:::tactic "exact"
:::

:::tactic "apply"
:::

:::tactic "refine"
:::

:::tactic "refine'"
:::

:::tactic "solve_by_elim"
:::


:::tactic "apply_rules"
:::

:::comment
# Falsehood
:::

# 偽（Falsehood）
%%%
tag := "tactic-ref-false"
%%%


:::tactic "exfalso"
:::

:::tactic "contradiction"
:::

:::tactic Lean.Parser.Tactic.falseOrByContra
:::


:::comment
# Goal Management
:::

# ゴールの管理（Goal Management）
%%%
tag := "tactic-ref-goals"
%%%


:::tactic "suffices"
:::

:::tactic "change"
:::

:::tactic Lean.Parser.Tactic.changeWith show:="change ... with ..."
:::

:::tactic "generalize"
:::

:::tactic "specialize"
:::

:::tactic "obtain"
:::

:::tactic "show"
:::

:::tactic Lean.Parser.Tactic.showTerm
:::


:::comment
# Cast Management
:::

# キャストの管理（Cast Management）
%%%
tag := "tactic-ref-casts"
%%%


:::comment
The tactics in this section make it easier avoid getting stuck on {deftech}_casts_, which are functions that coerce data from one type to another, such as converting a natural number to the corresponding integer.
They are described in more detail by {citet castPaper}[].

:::

本節のタクティクは {deftech}_キャスト_ （cast）に詰まってしまうことを回避します。キャストとはある型から別の型にデータを強制する関数であり、例えば自然数を対応する整数に変換するようなものです。これらは {citet castPaper}[] にて詳しく説明されています。

:::tactic Lean.Parser.Tactic.tacticNorm_cast_
:::

:::tactic Lean.Parser.Tactic.pushCast
:::

:::tactic Lean.Parser.Tactic.tacticExact_mod_cast_
:::

:::tactic Lean.Parser.Tactic.tacticApply_mod_cast_
:::

:::tactic Lean.Parser.Tactic.tacticRw_mod_cast___
:::

:::tactic Lean.Parser.Tactic.tacticAssumption_mod_cast
:::

:::comment
# Extensionality
:::

# 外延性（Extensionality）
%%%
tag := "tactic-ref-ext"
%%%


:::tactic "ext"
:::

:::tactic Lean.Elab.Tactic.Ext.tacticExt1___
:::

:::tactic Lean.Elab.Tactic.Ext.applyExtTheorem
:::

:::tactic "funext"
:::

{include 0 Manual.Tactics.Reference.Simp}


# 書き換え（Rewriting）
%%%
tag := "tactic-ref-rw"
%%%


:::comment
# Rewriting
:::
:::tactic "rw"
:::

:::tactic "rewrite"
:::

:::tactic "erw"
:::

:::tactic Lean.Parser.Tactic.tacticRwa__
:::

{docstring Lean.Meta.Rewrite.Config}

{docstring Lean.Meta.Occurrences}

{docstring Lean.Meta.TransparencyMode}

{docstring Lean.Meta.Rewrite.NewGoals}


:::tactic "unfold"

Implemented by {name}`Lean.Elab.Tactic.evalUnfold`.
:::

:::tactic "replace"
:::

:::tactic "delta"
:::


:::comment
# Inductive Types
:::

# 帰納型（Inductive Types）
%%%
tag := "tactic-ref-inductive"
%%%


:::comment
## Introduction
:::

## 帰納法（Introduction）
%%%
tag := "tactic-ref-inductive-intro"
%%%


:::tactic "constructor"
:::


:::tactic "injection"
:::

:::tactic "injections"
:::

:::tactic "left"
:::

:::tactic "right"
:::

:::comment
## Elimination
:::

## 除去（Elimination）
%%%
tag := "tactic-ref-inductive-elim"
%%%



:::planned 48

Description of the `@[induction_eliminator]` and `@[cases_eliminator]` attributes

:::

:::tactic "cases"
:::

:::tactic "rcases"
:::

:::tactic "induction"
:::

:::tactic "nofun"
:::

:::tactic "nomatch"
:::


:::comment
# Library Search
:::

# ライブラリ検索（Library Search）
%%%
tag := "tactic-ref-search"
%%%


:::comment
The library search tactics are intended for interactive use.
When run, they search the Lean library for lemmas or rewrite rules that could be applicable in the current situation, and suggests a new tactic.
These tactics should not be left in a proof; rather, their suggestions should be incorporated.

:::

ライブラリ検索タクティクは対話的な使用を目的としています。これらを実行すると、Lean ライブラリ内を検索し、現在の状況に適用できそうな補題や書き換え規則を探し、新しいタクティクを提案します。これらのタクティクは証明の中に放置されるべきではなく、むしろその提案を受け入れるべきです。

:::tactic "exact?"
:::

:::tactic "apply?"
:::




::::tacticExample
{goal show:=false}`∀ (i j k : Nat), i < j → j < k → i < k`
```setup
intro i j k h1 h2
```
:::comment
In this proof state:
:::

この証明状態において：

```pre
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < k
```

:::comment
invoking {tacticStep}`apply?` suggests:

:::

{tacticStep}`apply?` の実行結果は以下を提案します：

```tacticOutput
Try this: exact Nat.lt_trans h1 h2
```

```post (show := false)

```
::::


:::tactic "rw?"
:::

:::comment
# Case Analysis
:::

# ケース分析（Case Analysis）
%%%
tag := "tactic-ref-cases"
%%%



:::tactic "split"
:::

:::tactic "by_cases"
:::

:::comment
# Decision Procedures
:::

# 決定手続き（Decision Procedures）
%%%
tag := "tactic-ref-decision"
%%%



:::tactic Lean.Parser.Tactic.decide show:="decide"
:::

:::tactic Lean.Parser.Tactic.nativeDecide show:="native_decide"
:::

:::tactic "omega"
:::

:::tactic "bv_omega"
:::


:::comment
## SAT Solver Integration
:::

## SAT ソルバの統合（SAT Solver Integration）
%%%
tag := "tactic-ref-sat"
%%%


:::tactic "bv_decide"
:::

:::tactic "bv_normalize"
:::

:::tactic "bv_check"
:::

:::tactic Lean.Parser.Tactic.bvTrace
:::

:::comment
# Control Flow
:::

# フロー制御（Control Flow）
%%%
tag := "tactic-ref-control"
%%%



:::tactic "skip"
:::


:::tactic Lean.Parser.Tactic.guardHyp
:::

:::tactic Lean.Parser.Tactic.guardTarget
:::

:::tactic Lean.Parser.Tactic.guardExpr
:::

:::tactic "done"
:::

:::tactic "sleep"
:::


:::tactic "checkpoint"
:::

:::tactic "save"
:::

:::tactic "stop"
:::


:::comment
# Term Elaboration Backends
:::

# 項エラボレーションのバックエンド（Term Elaboration Backends）
%%%
tag := "tactic-ref-term-helpers"
%%%



:::comment
These tactics are used during elaboration of terms to satisfy obligations that arise.

:::

これらのタクティクは項のエラボレーション中において発生した義務を満たすために用いられます。

:::tactic "decreasing_tactic"
:::

:::tactic "decreasing_trivial"
:::

:::tactic "array_get_dec"
:::

:::tactic tacticDecreasing_with_
:::

:::tactic "get_elem_tactic"
:::

:::tactic "get_elem_tactic_trivial"
:::



:::comment
# Debugging Utilities
:::

# デバッグ用ユーティリティ（Debugging Utilities）
%%%
tag := "tactic-ref-debug"
%%%



:::tactic "sorry"
:::

:::tactic "admit"
:::

:::tactic "dbg_trace"
:::

:::tactic Lean.Parser.Tactic.traceState
:::

:::tactic Lean.Parser.Tactic.traceMessage
:::


:::comment
# Other
:::

# その他（Other）
%%%
tag := "tactic-ref-other"
%%%


:::tactic "trivial"
:::

:::tactic "solve"
:::

:::tactic "and_intros"
:::

:::tactic "infer_instance"
:::

:::tactic Lean.Parser.Tactic.tacticUnhygienic_
:::

:::tactic Lean.Parser.Tactic.runTac
:::
