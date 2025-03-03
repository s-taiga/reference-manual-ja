/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

/-
#doc (Manual) "Optional Values" =>
-/
#doc (Manual) "オプショナルの値" =>
%%%
tag := "option"
%%%

{docstring Option}


:::comment
# Coercions
:::
# 強制（Coercions）

```lean (show := false)
section
variable {α : Type u} (line : String)
```

:::comment
There is a {tech}[coercion] from {lean}`α` to {lean}`Option α` that wraps a value in {lean}`some`.
This allows {name}`Option` to be used in a style similar to nullable types in other languages, where values that are missing are indicated by {name}`none` and values that are present are not specially marked.

:::

{lean}`α` から {lean}`Option α` への {tech}[coercion] として値を {lean}`some` でラップするものがあります。これにより、 {name}`Option` を他の言語における nullable 型に似たスタイルで使用することができます。この場合、欠落している値は {name}`none` で示され、存在する値は特にマークされません。

:::comment
::example "Coercions and {name}`Option`"
:::
::::example "強制と {name}`Option`"
:::comment
In {lean}`getAlpha`, a line of input is read.
If the line consists only of letters (after removing whitespace from the beginning and end of it), then it is returned; otherwise, the function returns {name}`none`.

:::

{lean}`getAlpha` では1行の入力が読み込まれます。この行が（行頭と行末の空白を取り除いた後に）文字のみで構成されている場合、それ自体が返されます；そうでない場合、この関数は {name}`none` を返します。

```lean
def getAlpha : IO (Option String) := do
  let line := (← (← IO.getStdin).getLine).trim
  if line.length > 0 && line.all Char.isAlpha then
    return line
  else
    return none
```

:::comment
In the successful case, there is no explicit {name}`some` wrapped around {lean}`line`.
The {name}`some` is automatically inserted by the coercion.

:::

成功のケースにおいて、 {lean}`line` を囲む明示的な {name}`some` はありません。 {name}`some` は強制によって自動的に挿入されます。

::::

```lean (show := false)
end
```


:::comment
# API Reference
:::

# API リファレンス（API Reference）

:::comment
## Extracting Values
:::

## 値の抽出（Extracting Values）

{docstring Option.get}

{docstring Option.get!}

{docstring Option.getD}

{docstring Option.getDM}

{docstring Option.getM}

{docstring Option.elim}

{docstring Option.elimM}

{docstring Option.liftOrGet}

{docstring Option.merge}


:::comment
## Properties and Comparisons
:::

## 性質と比較（Properties and Comparisons）

{docstring Option.isNone}

{docstring Option.isSome}

{docstring Option.isEqSome}

{docstring Option.min}

{docstring Option.max}

{docstring Option.lt}

{docstring Option.decidable_eq_none}

:::comment
## Conversion
:::

## 変換（Conversion）

{docstring Option.toArray}

{docstring Option.toList}

{docstring Option.repr}

{docstring Option.format}

:::comment
## Control
:::

## 制御構造（Control）

:::comment
{name}`Option` can be thought of as describing a computation that may fail to return a value.
The {inst}`Monad Option` instance, along with {inst}`Alternative Option`, is based on this understanding.
Returning {name}`none` can also be thought of as throwing an exception that contains no interesting information, which is captured in the {inst}`MonadExcept Unit Option` instance.

:::

{name}`Option` は、値を返さない可能性のある計算を記述していると考えることができます。 {inst}`Monad Option` インスタンスは {inst}`Alternative Option` と共にこの考え方に基づいています。また {name}`none` の返却は特に興味深い情報を含まない例外を投げることとして考えることもでき、これは {inst}`MonadExcept Unit Option` インスタンスにキャプチャされています。

{docstring Option.guard}

{docstring Option.bind}

{docstring Option.bindM}

{docstring Option.join}

{docstring Option.sequence}

{docstring Option.tryCatch}

{docstring Option.or}

{docstring Option.orElse}


:::comment
## Iteration
:::

## 反復（Iteration）

:::comment
{name}`Option` can be thought of as a collection that contains at most one value.
From this perspective, iteration operators can be understood as performing some operation on the contained value, if present, or doing nothing if not.

:::

{name}`Option` は最大1つの値を含むコレクションと考えることができます。この観点において、反復演算子は含まれる値が存在する場合はその値に対して何らかの処理を行い、存在しない場合は何もしないものと理解することができます。

{docstring Option.all}

{docstring Option.any}

{docstring Option.filter}

{docstring Option.forM}

{docstring Option.map}

{docstring Option.mapA}

{docstring Option.mapM}

## Recursion Helpers

{docstring Option.attach}

{docstring Option.attachWith}

{docstring Option.unattach}

:::comment
## Reasoning
:::

## 推論（Reasoning）

{docstring Option.choice}

{docstring Option.pbind}

{docstring Option.pelim}

{docstring Option.pmap}
