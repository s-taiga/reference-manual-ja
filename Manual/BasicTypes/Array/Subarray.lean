/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true

/-
#doc (Manual) "Sub-Arrays" =>
-/
#doc (Manual) "部分配列（Sub-Arrays）" =>
%%%
tag := "subarray"
%%%

{docstring Subarray}

{docstring Subarray.toArray}

{docstring Subarray.empty}

:::comment
# Size
:::

# サイズ（Size）

{docstring Subarray.size}

:::comment
# Resizing
:::

# サイズ変更（Resizing）

{docstring Subarray.drop}

{docstring Subarray.take}

{docstring Subarray.popFront}

{docstring Subarray.split}

:::comment
# Lookups
:::

# 検索（Lookups）


{docstring Subarray.get}

{docstring Subarray.get!}

{docstring Subarray.getD}

:::comment
# Iteration
:::

# 反復（Iteration）


{docstring Subarray.foldl}

{docstring Subarray.foldlM}

{docstring Subarray.foldr}

{docstring Subarray.foldrM}

{docstring Subarray.forM}

{docstring Subarray.forRevM}

{docstring Subarray.forIn}

:::comment
# Element Predicates
:::

# 要素についての述語（Element Predicates）

{docstring Subarray.findRev?}

{docstring Subarray.findRevM?}

{docstring Subarray.findSomeRevM?}

{docstring Subarray.all}

{docstring Subarray.allM}

{docstring Subarray.any}

{docstring Subarray.anyM}
