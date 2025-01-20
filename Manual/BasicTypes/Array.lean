/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.BasicTypes.Array.Subarray
import Manual.BasicTypes.Array.FFI

open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true

example := Char

/-
#doc (Manual) "Arrays" =>
-/
#doc (Manual) "配列（Arrays）" =>
%%%
tag := "Array"
%%%

:::comment
The {lean}`Array` type represents sequences of elements, addressable by their position in the sequence.
Arrays are specially supported by Lean:
 * They have a _logical model_ that specifies their behavior in terms of lists of elements, which specifies the meaning of each operation on arrays.
 * They have an optimized run-time representation in compiled code as {tech}[dynamic arrays], and the Lean runtime specially optimizes array operations.
 * There is {ref "array-syntax"}[array literal syntax] for writing arrays.

:::

{lean}`Array` 型は要素のシーケンスを表し、シーケンス内の位置によってアクセスすることが可能です。配列は Lean で特別にサポートされています：
 * 配列には要素のリストという観点からその動作を指定する _論理モデル_ があり、配列に対する各操作の意味を指定します。
 * {tech}[動的配列] としてコンパイルされたコードに最適化されたランタイム表現があり、Lean のランタイムは配列操作を特別に最適化します。
 * 配列を記述するための {ref "array-syntax"}[配列リテラル構文] が存在します。

:::comment
Arrays can be vastly more efficient than lists or other sequences in compiled code.
In part, this is because they offer good locality: because all the elements of the sequence are next to each other in memory, the processor's caches can be used efficiently.
Even more importantly, if there is only a single reference to an array, operations that might otherwise copy or allocate a data structure can be implemented via mutation.
Lean code that uses an array in such a way that there's only ever one unique reference (that is, uses it {deftech}_linearly_) avoids the performance overhead of persistent data structures while still being as convenient to write, read, and prove things about as ordinary pure functional programs.

:::

配列はコンパイルされたコードにおいて、リストや他の配列よりも遥かに効率的です。これは配列が良い局所性を要求しているためです：配列のすべての要素がメモリ上で隣り合っているため、プロセッサのキャッシュを効率的に使うことができます。さらに重要なのは、配列への参照が1つだけであれば、データ構造をコピーしたり割り当てたりするような操作はミューテーションによって実装できるということです。一意な参照が1つしかないような配列を使用する（つまり、 {deftech}_linearly_ に使用する）Lean コードは、永続的なデータ構造のパフォーマンスオーバーヘッドを回避しつつ、通常の純粋関数型プログラムと同じように便利に書いたり読んだり証明したりすることができます。

:::comment
# Logical Model
:::

# 論理モデル（Logical Model）


{docstring Array}

:::comment
The logical model of arrays is a structure that contains a single field, which is a list of elements.
This is convenient when specifying and proving properties of array-processing functions at a low level.

:::

配列の論理モデルは、要素のリストである1つのフィールドを含む構造体です。これは配列処理関数の特性を低レベルで指定・証明する場合に便利です。

:::comment
# Run-Time Representation
:::

# ランタイム表現（Run-Time Representation）

%%%
tag := "array-runtime"
%%%

:::comment
Lean's arrays are {deftech}_dynamic arrays_, which are blocks of continuous memory with a defined capacity, not all of which is typically in use.
As long as the number of elements in the array is less than the capacity, new items can be added to the end without reallocating or moving the data.
Adding items to an array that has no extra space results in a reallocation that doubles the capacity.
The amortized overhead scales linearly with the size of the array.
The values in the array are represented as described in the {ref "inductive-types-ffi"}[section on the foreign function interface].

:::

Lean の配列は {deftech}_動的配列_ （dynamic array）であり、定義された容量（たいていすべて使われることはない）を持つ連続メモリのブロックです。配列の要素数が容量より少ない場合、データを再割り当てしたり、移動したりすることなく、新しい項目を末尾に追加できます。スペースに空きの無い配列に項目を追加すると、再割り当てで容量が2倍になります。償却されるオーバーヘッドは配列の大きさに応じて線形に増加します。配列内の値は {ref "inductive-types-ffi"}[外部関数インタフェースの節] で説明されているように表現されます。

:::figure "Memory layout of arrays" (name := "arrayffi")
![Memory layout of arrays](/static/figures/array.svg)
:::

:::comment
After the object header, an array contains:

:::

オブジェクトのヘッダに続き、配列は以下を保持します：

:::comment
: size

  The number of objects currently stored in the array

:::

: サイズ

  現在配列に格納されているオブジェクトの数

:::comment
: capacity

  The number of objects that fit in the memory allocated for the array

:::

: 容量

  配列に割り当てられたメモリに収まるオブジェクトの数

:::comment
: data

  The values in the array

:::

: データ

  配列に格納された値

:::comment
Many array functions in the Lean runtime check whether they have exclusive access to their argument by consulting the reference count in the object header.
If they do, and the array's capacity is sufficient, then the existing array can be mutated rather than allocating fresh memory.
Otherwise, a new array must be allocated.

:::

Lean のランタイムにて多くの配列関数は、オブジェクトヘッダの参照カウントを参照することで、引数に排他アクセスがあるかどうかをチェックします。もし排他アクセスがあり、配列の容量が十分であれば、新しいメモリを確保するのではなく、既存の配列を変更することができます。そうでない場合は、新しい配列を割り当てる必要があります。

:::comment
## Performance Notes
:::

## パフォーマンスについての注記（Performance Notes）

%%%
tag := "array-performance"
%%%


:::comment
Despite the fact that they appear to be an ordinary constructor and projection, {name}`Array.mk` and {name}`Array.data` take *time linear in the size of the array* in compiled code.
This is because they must implement the conversions between linked lists and packed arrays, which must necessarily visit each element.

:::

一見普通のコンストラクタと射影のように見えますが、 {name}`Array.mk` と {name}`Array.data` はコンパイルされたコードにおいて *配列のサイズに比例した時間* がかかります。これは連結リストと packed array の間の変換を実装する必要があるためで、各要素を訪問する必要があります。

:::comment
Mutable arrays can be used to write very efficient code.
However, they are a poor persistent data structure.
Updating a shared array rules out mutation, and requires time linear in the size of the array.
When using arrays in performance-critical code, it's important to ensure that they are used {tech}[linearly].

:::

可変配列は非常に効率的なコードを書くために使うことができます。しかし、これは永続性の低いデータ構造です。共有された配列の更新はミューテーションを排除し、配列のサイズに線形な時間を必要とします。パフォーマンスが重要なコードで配列を使用する場合、 {tech}[linearly] に使用されるようにすることが重要です。

:::comment
# Syntax
:::

# 構文（Syntax）

%%%
tag := "array-syntax"
%%%

:::comment
Array literals allow arrays to be written directly in code.
They may be used in expression or pattern contexts.

:::

配列リテラルによって、配列がコードで直接記述できるようになります。配列リテラルは式やパターンのコンテキストで使うことができます。

::::syntax term
:::comment
Array literals begin with `#[` and contain a comma-separated sequence of terms, terminating with `]`.

:::

配列リテラルは `#[` で始まり、カンマで区切られた一連の項を含み、`]` で終わります。

```grammar
#[$t,*]
```
::::

:::::keepEnv
:::comment
::example "Array Literals"
:::
::::example "配列リテラル"
:::comment
Array literals may be used as expressions or as patterns.

:::

配列リテラルは式としてもパターンとしても使用できます。

```lean
def oneTwoThree : Array Nat := #[1, 2, 3]

#eval
  match oneTwoThree with
  | #[x, y, z] => some ((x + z) / y)
  | _ => none
```
::::
:::::

:::comment
Additionally, {ref "subarray"}[sub-arrays] may be extracted using the following syntax:
:::

さらに、 {ref "subarray"}[部分配列] は以下の構文を使って取り出すことができます：

::::syntax term
:::comment
A start index followed by a colon constructs a sub-array that contains the values from the start index onwards (inclusive):
:::

開始インデックスの後にコロンを付けると、開始インデックス（を含み）以降の値を含む部分配列が構成されます：

```grammar
$t[$t:term :]
```

:::comment
Providing start and end indices  constructs a sub-array that contains the values from the start index (inclusive) to the end index (exclusive):
:::

開始インデックスと終了インデックスを指定すると、開始インデックス（含む）から終了インデックス（含まない）までの値を含む部分配列が構成されます：

```grammar
$t[$t:term : $_:term]
```
::::

:::::keepEnv
:::comment
::example "Sub-array Syntax"
:::
::::example "部分配列の構文"

:::comment
The array {lean}`ten` contains the first ten natural numbers.
:::

配列 {lean}`ten` は0から始まる10個の自然数を含みます。

```lean
def ten : Array Nat :=
  .range 10
```

:::comment
A sub-array that represents the second half of {lean}`ten` can be constructed using the sub-array syntax:
:::

{lean}`ten` の後半を表す部分配列は、部分配列構文を使って作ることができます：

```lean (name := subarr1)
#eval ten[5:]
```
```leanOutput subarr1
#[5, 6, 7, 8, 9].toSubarray
```

:::comment
Similarly, sub-array that contains two through five can be constructed by providing a stopping point:
:::

同様に、2番目から5番目までを含む部分配列は終了点を設けることで構築できます：

```lean (name := subarr2)
#eval ten[2:6]
```
```leanOutput subarr2
#[2, 3, 4, 5].toSubarray
```

:::comment
Because sub-arrays merely store the start and end indices of interest in the underlying array, the array itself can be recovered:
:::

部分配列は単にベースとなる配列の開始と終了のインデックスを格納するだけであるため、配列そのものを復元することができます：

```lean (name := subarr3)
#eval ten[2:6].array == ten
```
```leanOutput subarr3
true
```
::::
:::::

:::comment
# API Reference
:::

# API リファレンス（API Reference）

%%%
tag := "array-api"
%%%

:::comment
## Constructing Arrays
:::

## 配列の構成（Constructing Arrays）


{docstring Array.empty}

{docstring Array.singleton}

{docstring Array.range}

{docstring Array.ofFn}

{docstring Array.mkArray}

{docstring Array.append}

{docstring Array.appendList}

:::comment
## Size
:::

## サイズ（Size）


{docstring Array.size}

{docstring Array.usize}

{docstring Array.isEmpty}

:::comment
## Lookups
:::

## 検索（Lookups）


{docstring Array.extract}

{docstring Array.get}

{docstring Array.get?}

{docstring Array.getIdx?}

{docstring Array.getD}

{docstring Array.get!}

{docstring Array.uget}

{docstring Array.back?}

{docstring Array.back!}

{docstring Array.back}

{docstring Array.getMax?}

:::comment
## Conversions
:::

## 別の型への変換（Conversions）


{docstring Array.toList}

{docstring Array.toListRev}

{docstring Array.toListAppend}

{docstring Array.toSubarray}

{docstring Array.ofSubarray}

{docstring Array.toPArray'}

:::comment
## Modification
:::

## 配列の変更（Modification）


{docstring Array.push}

{docstring Array.pop}

{docstring Array.popWhile}

{docstring Array.erase}

{docstring Array.eraseIdx}

{docstring Array.eraseReps}

{docstring Array.swap}

{docstring Array.swap!}

{docstring Array.swapAt}

{docstring Array.swapAt!}

{docstring Array.set}

{docstring Array.set!}

{docstring Array.setD}

{docstring Array.uset}

{docstring Array.modify}

{docstring Array.modifyM}

{docstring Array.modifyOp}

{docstring Array.insertAt}

{docstring Array.insertAt!}

{docstring Array.reverse}

{docstring Array.binInsertM}

{docstring Array.take}

{docstring Array.takeWhile}

{docstring Array.flatten}

{docstring Array.getEvenElems}

:::comment
## Sorted Arrays
:::

## 配列のソート（Sorted Arrays）


{docstring Array.qsort}

{docstring Array.qsortOrd}

{docstring Array.insertionSort}

{docstring Array.binInsert}

{docstring Array.binSearch}

{docstring Array.binSearchContains}

:::comment
## Iteration
:::

## 反復（Iteration）


{docstring Array.foldr}

{docstring Array.foldrM}

{docstring Array.foldl}

{docstring Array.foldlM}

{docstring Array.forM}

{docstring Array.forRevM}

{docstring Array.forIn'}

:::comment
## Transformation
:::

## 要素の変換（Transformation）


{docstring Array.concatMap}

{docstring Array.concatMapM}

{docstring Array.zip}

{docstring Array.zipWith}

{docstring Array.zipWithIndex}

{docstring Array.unzip}

{docstring Array.map}

{docstring Array.mapMono}

{docstring Array.mapM}

{docstring Array.mapM'}

{docstring Array.mapMonoM}

{docstring Array.mapIdx}

{docstring Array.mapIdxM}

{docstring Array.mapFinIdx}

{docstring Array.mapIndexed}

{docstring Array.mapIndexedM}

{docstring Array.mapFinIdxM}

{docstring Array.flatMap}

{docstring Array.flatMapM}

{docstring Array.sequenceMap}

:::comment
## Filtering
:::

## フィルタ（Filtering）


{docstring Array.filterMap}

{docstring Array.filter}

{docstring Array.filterM}

{docstring Array.filterMapM}

{docstring Array.filterPairsM}

{docstring Array.filterSepElems}

{docstring Array.filterSepElemsM}

:::comment
## Partitioning
:::

## 分割（Partitioning）


{docstring Array.split}

{docstring Array.partition}

{docstring Array.groupByKey}


:::comment
## Element Predicates
:::

## 要素についての述語（Element Predicates）


{docstring Array.contains}

{docstring Array.elem}

{docstring Array.indexOf?}

{docstring Array.find?}

{docstring Array.findRev?}

{docstring Array.findIdx?}

{docstring Array.findM?}

{docstring Array.findRevM?}

{docstring Array.findIdxM?}

{docstring Array.findSomeM?}

{docstring Array.findSomeRev?}

{docstring Array.findSomeRevM?}

{docstring Array.all}

{docstring Array.allM}

{docstring Array.allDiff}

{docstring Array.any}

{docstring Array.anyM}

{docstring Array.isEqv}

{docstring Array.findSome?}

{docstring Array.findSome!}


:::comment
## Comparisons
:::

## 比較（Comparisons）


{docstring Array.isPrefixOf}

## Termination Helpers

{docstring Array.attach}

{docstring Array.attachWith}

{docstring Array.unattach}

:::comment
## Proof Automation
:::

## 証明の自動化（Proof Automation）


{docstring Array.reduceOption}

{docstring Array.reduceGetElem}

{docstring Array.reduceGetElem?}

{docstring Array.reduceGetElem!}

{include 1 Manual.BasicTypes.Array.Subarray}

{include 0 Manual.BasicTypes.Array.FFI}
