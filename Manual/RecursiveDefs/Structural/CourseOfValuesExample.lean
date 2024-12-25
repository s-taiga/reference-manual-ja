/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Verso.Genre Manual
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

/-
#doc (Manual) "Recursion Example (for inclusion elsewhere)" =>
-/
#doc (Manual) "再帰の例（Recursion Example (for inclusion elsewhere)）" =>


:::comment
::example "Course-of-Values Tables"
:::
::::example "Course-of-Values Tables"
:::comment
This definition is equivalent to {name}`List.below`:
:::

以下の定義は {name}`List.below` と同等です：

```lean
def List.below' {α : Type u} {motive : List α → Sort u} :
    List α → Sort (max 1 u)
  | [] => PUnit
  | _ :: xs => motive xs ×' xs.below' (motive := motive)
```

```lean (show := false)
theorem List.below_eq_below' : @List.below = @List.below' := by
  funext α motive xs
  induction xs <;> simp [List.below, below']
  congr
```

:::comment
In other words, for a given {tech}[motive], {lean}`List.below'` is a type that contains a realization of the motive for all suffixes of the list.

:::

言い換えると、与えられた {tech}[動機] に対して、 {lean}`List.below'` はリストのすべての接尾辞に対する動機の実現を含む型です。

:::comment
More recursive arguments require further nested iterations of the product type.
For instance, binary trees have two recursive occurrences.
:::

より再帰的な引数は直積型の反復をさらに入れ子にする必要があります。例えば、二分木には2つの再帰が出現します。

```lean
inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)
```

:::comment
It's corresponding course-of-values table contains the realizations of the motive for all subtrees:
:::

対応する累積テーブルにはすべてのサブツリーに対する動機の実現が含まれています：

```lean
def Tree.below' {α : Type u} {motive : Tree α → Sort u} :
    Tree α → Sort (max 1 u)
  | .leaf => PUnit
  | .branch left _val right =>
    motive left ×' motive right ×'
    left.below' (motive := motive) ×'
    right.below' (motive := motive)
```

```lean (show := false)
theorem Tree.below_eq_below' : @Tree.below = @Tree.below' := by
  funext α motive t
  induction t <;> simp [Tree.below, below']
  congr
```

:::comment
For both lists and trees, the `brecOn` operator expects just a single case, rather than one per constructor.
This case accepts a list or tree along with a table of results for all smaller values; from this, it should satisfy the motive for the provided value.
Dependent case analysis of the provided value automatically refines the type of the memo table, providing everything needed.

:::

リストと木のどちらについても、`brecOn` 演算子はコンストラクタごとに1つではなく、1つのケースだけを想定しています。このエースはリストまたは木を、すべての小さい値に対する結果のテーブルと一緒に受け入れます；これにより、このケースは与えられた値に対する動機を満たすべきです。提供された値の依存ケース分析によって、メモテーブルの型が自動的に絞り込まれ、必要なものがすべて提供されます。

:::comment
The following definitions are equivalent to {name}`List.brecOn` and {name}`Tree.brecOn`, respectively.
The primitive recursive helpers {name}`List.brecOnTable`  and {name}`Tree.brecOnTable` compute the course-of-values tables along with the final results, and the actual definitions of the `brecOn` operators simply project out the result.
:::

以下の定義はそれぞれ {name}`List.brecOn` と {name}`Tree.brecOn` に同等です。プリミティブな再帰補助関数 {name}`List.brecOnTable` と {name}`Tree.brecOnTable` は最終結果と共に累積テーブルを計算し、実際の `brecOn` 演算子の定義は単に結果を射影します。

```lean
def List.brecOnTable {α : Type u}
    {motive : List α → Sort u}
    (xs : List α)
    (step :
      (ys : List α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive xs ×' xs.below' (motive := motive) :=
  match xs with
  | [] => ⟨step [] PUnit.unit, PUnit.unit⟩
  | x :: xs =>
    let res := xs.brecOnTable (motive := motive) step
    let val := step (x :: xs) res
    ⟨val, res⟩
```

```lean
def Tree.brecOnTable {α : Type u}
    {motive : Tree α → Sort u}
    (t : Tree α)
    (step :
      (ys : Tree α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive t ×' t.below' (motive := motive) :=
  match t with
  | .leaf => ⟨step .leaf PUnit.unit, PUnit.unit⟩
  | .branch left val right =>
    let resLeft := left.brecOnTable (motive := motive) step
    let resRight := right.brecOnTable (motive := motive) step
    let branchRes := ⟨resLeft.1, resRight.1, resLeft.2, resRight.2⟩
    let val := step (.branch left val right) branchRes
    ⟨val, branchRes⟩
```

```lean
def List.brecOn' {α : Type u}
    {motive : List α → Sort u}
    (xs : List α)
    (step :
      (ys : List α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive xs :=
  (xs.brecOnTable (motive := motive) step).1
```

```lean
def Tree.brecOn' {α : Type u}
    {motive : Tree α → Sort u}
    (t : Tree α)
    (step :
      (ys : Tree α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive t :=
  (t.brecOnTable (motive := motive) step).1
```

```lean (show := false)
-- Proving the above-claimed equivalence is too time consuming, but evaluating a few examples will at least catch silly mistakes!

/--
info: fun motive x y z step =>
  step [x, y, z]
    ⟨step [y, z] ⟨step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩,
      step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩
-/
#guard_msgs in
#reduce fun motive x y z step => List.brecOn' (motive := motive) [x, y, z] step

/--
info: fun motive x y z step =>
  step [x, y, z]
    ⟨step [y, z] ⟨step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩,
      step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩
-/
#guard_msgs in
#reduce fun motive x y z step => List.brecOn (motive := motive) [x, y, z] step

/--
info: fun motive x z step =>
  step ((Tree.leaf.branch x Tree.leaf).branch z Tree.leaf)
    ⟨step (Tree.leaf.branch x Tree.leaf) ⟨step Tree.leaf PUnit.unit, step Tree.leaf PUnit.unit, PUnit.unit, PUnit.unit⟩,
      step Tree.leaf PUnit.unit, ⟨step Tree.leaf PUnit.unit, step Tree.leaf PUnit.unit, PUnit.unit, PUnit.unit⟩,
      PUnit.unit⟩
-/
#guard_msgs in
#reduce fun motive x z step => Tree.brecOn' (motive := motive) (.branch (.branch .leaf x .leaf) z .leaf) step

/--
info: fun motive x z step =>
  step ((Tree.leaf.branch x Tree.leaf).branch z Tree.leaf)
    ⟨⟨step (Tree.leaf.branch x Tree.leaf)
          ⟨⟨step Tree.leaf PUnit.unit, PUnit.unit⟩, step Tree.leaf PUnit.unit, PUnit.unit⟩,
        ⟨step Tree.leaf PUnit.unit, PUnit.unit⟩, step Tree.leaf PUnit.unit, PUnit.unit⟩,
      step Tree.leaf PUnit.unit, PUnit.unit⟩
-/
#guard_msgs in
#reduce fun motive x z step => Tree.brecOn (motive := motive) (.branch (.branch .leaf x .leaf) z .leaf) step
```

::::
