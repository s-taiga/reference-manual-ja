/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.BasicTypes.String.Logical
import Manual.BasicTypes.String.Literals
import Manual.BasicTypes.String.FFI

open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true

example := Char

/-
#doc (Manual) "Strings" =>
-/
#doc (Manual) "文字列（Strings）" =>
%%%
tag := "String"
%%%


:::comment
Strings represent Unicode text.
Strings are specially supported by Lean:
 * They have a _logical model_ that specifies their behavior in terms of lists of characters, which specifies the meaning of each operation on strings.
 * They have an optimized run-time representation in compiled code, as packed arrays of bytes that encode the string as UTF-8, and the Lean runtime specially optimizes string operations.
 * There is {ref "string-syntax"}[string literal syntax] for writing strings.

:::

文字列は Unicode テキストを表現しています。文字列は Lean で特別にサポートされています：
 * 文字のリストという観点から動作を指定する _論理モデル_ を持っており、文字列に対する各操作の意味を指定します。
 * コンパイルされたコードにおいて文字列を UTF-8 としてエンコードするバイトの packed array として最適化されたランタイム表現を持っており、Lean ランタイムは特別に文字列操作を最適化します。
 * 文字列を書くための {ref "string-syntax"}[文字列リテラルの構文] があります。

:::comment
The fact that strings are internally represented as UTF-8-encoded byte arrays is visible in the API:
 * There is no operation to project a particular character out of the string, as this would be a performance trap. {ref "string-iterators"}[Use a {name}`String.Iterator`] in a loop instead of a {name}`Nat`.
 * Strings are indexed by {name}`String.Pos`, which internally records _byte counts_ rather than _character counts_, and thus takes constant time. Aside from `0`, these should not be constructed directly, but rather updated using {name}`String.next` and {name}`String.prev`.

:::

文字列が内部的に UTF-8 エンコードされたバイト配列として表現されていることは API で確認できます：
 * 文字列から特定の文字を射影する操作はありません（仮にあった場合パフォーマンスの罠になりえます）。 {name}`Nat` の代わりに {ref "string-iterators"}[{name}`String.Iterator`] をループ内で使ってください。
 * 文字列は {name}`String.Pos` によってインデックス付けされ、内部的には _文字数_ ではなく _バイト数_ を記録するため、一定の時間がかかります。`0` は別として、これらは直接構成されるのではなく、 {name}`String.next` と {name}`String.prev` をつかって更新されます。

{include 0 Manual.BasicTypes.String.Logical}

# ランタイム表現（Run-Time Representation）
%%%
tag := "string-runtime"
%%%

:::comment
# Run-Time Representation
:::

:::figure "Memory layout of strings" (name := "stringffi")
![Memory layout of strings](/static/figures/string.svg)
:::

:::comment
Strings are represented as {tech}[dynamic arrays] of bytes, encoded in UTF-8.
After the object header, a string contains:

:::

文字列はバイトの {tech}[dynamic arrays] として表現され、UTF-8 でエンコードされます。オブジェクトヘッダの後、文字列は以下を含みます：

:::comment
: byte count

  The number of bytes that currently contain valid string data

:::

: バイト数

  現在有効な文字列データを含むバイト数

:::comment
: capacity

  The number of bytes presently allocated for the string

:::

: 容量

  現在文字列に割り当てられているバイト数

:::comment
: length

  The length of the encoded string, which may be shorter than the byte count due to UTF-8 multi-byte characters

:::

: 長さ

  エンコードされた文字列の長さ。UTF-8 のマルチバイト文字のため、バイト数よりも短くなる可能性があります。

:::comment
: data

  The actual character data in the string, null-terminated

:::

: データ

  ヌル文字で終端された文字列内の実際の文字データ

:::comment
Many string functions in the Lean runtime check whether they have exclusive access to their argument by consulting the reference count in the object header.
If they do, and the string's capacity is sufficient, then the existing string can be mutated rather than allocating fresh memory.
Otherwise, a new string must be allocated.


:::

Lean ランタイムの多くの文字列関数は、おぷじぇくとヘッダの参照カウントを参照することで引数に排他的アクセスがあるかどうかをチェックします。もしアクセスがあり、かつ文字列の容量が十分であれば、新しいメモリを確保するのではなく、既存の文字列を変更することができます。そうでない場合は新しい文字列を割り当てなければなりません。

:::comment
## Performance Notes
%%%
tag := "string-performance"
%%%


:::

## パフォーマンスについての注記（Performance Notes）

:::comment
Despite the fact that they appear to be an ordinary constructor and projection, {name}`String.mk` and {name}`String.data` take *time linear in the length of the string*.
This is because they must implement the conversions between lists of characters and packed arrays of bytes, which must necessarily visit each character.

:::

一見普通のコンストラクタと射影に見えますが、 {name}`String.mk` と {name}`String.data` は *文字列の長さに比例した時間* がかかります。これは文字のリストとバイトの packed array の間の変換を実装しなければならないためで、各文字を必ず訪問しなければなりません。

{include 0 Manual.BasicTypes.String.Literals}

# API リファレンス（API Reference）

:::comment
# API Reference
%%%
tag := "string-api"
%%%


:::
:::comment
## Constructing
%%%
tag := "string-api-build"
%%%


:::

## 構成（Constructing）

{docstring String.singleton}

{docstring String.append}

{docstring String.join}

{docstring String.intercalate}

:::comment
## Conversions
%%%
tag := "string-api-convert"
%%%


:::

## 変換（Conversions）

{docstring String.toList}

{docstring String.isNat}

{docstring String.toNat?}

{docstring String.toNat!}

{docstring String.isInt}

{docstring String.toInt?}

{docstring String.toInt!}

{docstring String.toFormat}

:::comment
## Properties
%%%
tag := "string-api-props"
%%%

:::

## プロパティ（Properties）

{docstring String.isEmpty}

{docstring String.length}

:::comment
## Positions
%%%
tag := "string-api-pos"
%%%

:::

## 位置（Positions）

{docstring String.Pos}

{docstring String.Pos.isValid}

{docstring String.atEnd}

{docstring String.endPos}

{docstring String.next}

{docstring String.next'}

{docstring String.nextWhile}

{docstring String.nextUntil}

{docstring String.prev}

{docstring String.Pos.min}

:::comment
## Lookups and Modifications
%%%
tag := "string-api-lookup"
%%%

:::

## 検索と変更（Lookups and Modifications）

{docstring String.get}

{docstring String.get?}

{docstring String.get!}

{docstring String.get'}

{docstring String.extract}

{docstring String.take}

{docstring String.takeWhile}

{docstring String.takeRight}

{docstring String.takeRightWhile}

{docstring String.drop}

{docstring String.dropWhile}

{docstring String.dropRight}

{docstring String.dropRightWhile}

{docstring String.trim}

{docstring String.trimLeft}

{docstring String.trimRight}

{docstring String.removeLeadingSpaces}

{docstring String.set}

{docstring String.modify}

{docstring String.front}

{docstring String.back}

{docstring String.posOf}

{docstring String.revPosOf}

{docstring String.contains}

{docstring String.offsetOfPos}

{docstring String.replace}

{docstring String.findLineStart}

{docstring String.find}

{docstring String.revFind}


:::comment
## Folds and Aggregation
%%%
tag := "string-api-fold"
%%%

:::

## 畳み込みと集約（Folds and Aggregation）

{docstring String.map}

{docstring String.foldl}

{docstring String.foldr}

{docstring String.all}

{docstring String.any}

:::comment
## Comparisons
%%%
tag := "string-api-compare"
%%%

:::

## 比較（Comparisons）

{docstring String.le}

{docstring String.firstDiffPos}

{docstring String.substrEq}

{docstring String.isPrefixOf}

{docstring String.startsWith}

{docstring String.endsWith}

{docstring String.decEq}

{docstring String.hash}

:::comment
## Manipulation
%%%
tag := "string-api-modify"
%%%

:::

## 操作（Manipulation）

{docstring String.split}

{docstring String.splitOn}

{docstring String.push}

{docstring String.pushn}

{docstring String.capitalize}

{docstring String.decapitalize}

{docstring String.toUpper}

{docstring String.toLower}

:::comment
## Iterators
:::

## イテレータ（Iterators）

%%%
tag := "string-iterators"
%%%

:::comment
Fundamentally, a {name}`String.Iterator` is a pair of a string and a valid position in the string.
Iterators provide functions for getting the current character ({name String.Iterator.curr}`curr`), replacing the current character ({name String.Iterator.setCurr}`setCurr`), checking whether the iterator can move to the left or the right ({name String.Iterator.hasPrev}`hasPrev` and {name String.Iterator.hasNext}`hasNext`, respectively), and moving the iterator ({name String.Iterator.prev}`prev` and {name String.Iterator.next}`next`, respectively).
Clients are responsible for checking whether they've reached the beginning or end of the string; otherwise, the iterator ensures that its position always points at a character.

:::

基本的に、 {name}`String.Iterator` は文字列と文字列内の有効な位置のペアです。イテレータは現在の文字を取得する関数（ {name String.Iterator.curr}`curr` ）・現在の文字を置き換える関数（ {name String.Iterator.setCurr}`setCurr` ）・イテレータが左または右に移動できるかどうかチェックする関数（それぞれ {name String.Iterator.hasPrev}`hasPrev` と {name String.Iterator.hasNext}`hasNext` ）・イテレータの移動（それぞれ {name String.Iterator.prev}`prev` と {name String.Iterator.next}`next` ）です。クライアントは文字列の先頭または末尾に到達したかどうかをチェックする責任があります；それ以外の場合、イテレータはその位置が常に文字を指すようにします。

{docstring String.Iterator}

{docstring String.iter}

{docstring String.mkIterator}

{docstring String.Iterator.curr}

{docstring String.Iterator.hasNext}

{docstring String.Iterator.next}

{docstring String.Iterator.forward}

{docstring String.Iterator.nextn}

{docstring String.Iterator.hasPrev}

{docstring String.Iterator.prev}

{docstring String.Iterator.prevn}

{docstring String.Iterator.atEnd}

{docstring String.Iterator.toEnd}

{docstring String.Iterator.setCurr}

{docstring String.Iterator.extract}

{docstring String.Iterator.remainingToString}

{docstring String.Iterator.remainingBytes}

{docstring String.Iterator.pos}

:::comment
## Substrings
%%%
tag := "string-api-substring"
%%%

:::

## 部分文字列（Substrings）

:::TODO
Substring API xref
:::

{docstring String.toSubstring}

{docstring String.toSubstring'}

:::comment
## Proof Automation
%%%
tag := "string-simp"
%%%


:::

## 証明自動化（Proof Automation）

{docstring String.reduceGT}

{docstring String.reduceGE}

{docstring String.reduceBinPred}

{docstring String.reduceLT}

{docstring String.reduceLE}

{docstring String.reduceBEq}

{docstring String.reduceEq}

{docstring String.reduceAppend}

{docstring String.reduceMk}

{docstring String.reduceBoolPred}

{docstring String.reduceBNe}

{docstring String.reduceNe}

:::comment
## Metaprogramming
%%%
tag := "string-api-meta"
%%%


:::

## メタプログラミング（Metaprogramming）

{docstring String.toName}

{docstring String.toFileMap}

{docstring String.quote}

{docstring String.fromExpr?}

:::comment
## Encodings
%%%
tag := "string-api-encoding"
%%%


:::

## エンコード（Encodings）

{docstring String.utf16PosToCodepointPos}

{docstring String.utf16PosToCodepointPosFrom}

{docstring String.codepointPosToUtf16Pos}

{docstring String.codepointPosToUtf16PosFrom}

{docstring String.getUtf8Byte}

{docstring String.utf8ByteSize}

{docstring String.utf8EncodeChar}

{docstring String.utf8DecodeChar?}

{docstring String.fromUTF8}

{docstring String.fromUTF8?}

{docstring String.fromUTF8!}

{docstring String.toUTF8}

{docstring String.validateUTF8}

{docstring String.utf16Length}

{docstring String.codepointPosToUtf8PosFrom}

{docstring String.crlfToLf}


{include 0 Manual.BasicTypes.String.FFI}
