/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Lean.MessageSeverity

open Verso.Genre Manual

set_option pp.rawOnError true

/-
#doc (Manual) "Introduction" =>
-/
#doc (Manual) "はじめに" =>
%%%
htmlSplit := .never
tag := "introduction"
%%%

:::comment
The _Lean Language Reference_ is intended as a comprehensive, precise description of Lean.
It is first and foremost a reference work in which Lean users can look up detailed information, rather than a tutorial for new users.
At the moment, this reference manual is a public preview.
Many sections are still to be written.
For tutorials and learning materials, please visit [the Lean documentation page](https://lean-lang.org/documentation/).
:::

_Lean 言語リファレンス_ は Lean の包括的で正確な説明を意図しています。本書は第一義的にリファレンスであり、新規ユーザ向けのチュートリアルではなく、Lean のユーザが詳細な情報を調べるためのマニュアルです。現時点では、このリファレンスマニュアルは高階プレビューです。多くの節は今なお執筆中です。チュートリアルや学習教材については [Lean のドキュメントのページ](https://lean-lang.org/documentation/) をご覧ください。

:::comment
This document describes version {versionString}[] of Lean.
:::

このドキュメントは Lean のバージョン {versionString}[] で記述されています。

# Lean
%%%
tag := "what-is-lean"
%%%


:::comment
Lean is an *interactive theorem prover* based on dependent type theory, designed for use both in cutting-edge mathematics and in software verification.
Lean's core type theory is expressive enough to capture very complicated mathematical objects, but simple enough to admit independent implementations, reducing the risk of bugs that affect soundness.
The core type theory is implemented in a minimal {tech}[kernel] that does nothing other than check proof terms.
This core theory and kernel are supported by advanced automation, realized in {ref "tactics"}[an expressive tactic language].
Each tactic produces a term in the core type theory that is checked by the kernel, so bugs in tactics do not threaten the soundness of Lean as a whole.
Along with many other parts of Lean, the tactic language is user-extensible, so it can be built up to meet the needs of a given formalization project.
Tactics are written in Lean itself, and can be used immediately upon definition; rebuilding the prover or loading external modules is not required.
:::

Lean は依存型理論に基づいた *対話型定理証明器* （interactive theorem prover）であり、最先端の数学とソフトウェア検証の両方で使用できるように設計されています。Lean の中核となる型理論は、非常に複雑な数学的対象を捉えるにあたって十分な表現力を持ちながら、独立した実装を認めるのに十分なシンプルさを持っており、健全性に影響を与えるバグのリスクを軽減しています。中核となる型理論は、証明項のチェック以外には何もしない最小限の {tech}[kernel] として実装されています。この中核理論とカーネルは {ref "tactics"}[表現力豊かなタクティク言語] で実現される高度な自動化によってサポートされています。各タクティクはカーネルによってチェックされる中核となる型理論の項を生成するため、タクティクにバグがあっても Lean 全体の健全性が脅かされることはありません。Lean の他の多くの部分と同様に、タクティク言語はユーザが拡張可能であるため、それぞれの形式化プロジェクトのニーズに合わせて構築することができます。タクティクは Lean 自体で記述されており、定義するとすぐに使用することができます：証明器の再ビルドや外部モジュールのロードなどは必要ありません。

:::comment
Lean is also a pure *functional programming language*, with features such as a run-time system based on reference counting that can efficiently work with packed array structures, multi-threading, and monadic {name}`IO`.
As befits a programming language, Lean is primarily implemented in itself, including the language server, build tool, {tech}[elaborator], and tactic system.
This very book is written in [Verso](https://github.com/leanprover/verso), a documentation authoring tool written in Lean.
:::

また、Lean は純粋 *関数型プログラミング言語* （functional programming language）でもあり、packed array 構造を効率的に扱うことができる参照カウントに基づくランタイムシステム・マルチスレッド・モナド {name}`IO` などの機能を備えています。プログラミング言語にふさわしく、Lean の言語サーバ・ビルドツール・ {tech}[elaborator] ・タクティクシステムなどはもっぱら Lean 自体で実装されています。本書もまさに [Verso](https://github.com/leanprover/verso) という Lean で書かれた文書作成ツールで書かれています。

:::comment
Familiarity with Lean's programming features is valuable even for users whose primary interest is in writing proofs, because Lean programs are used to implement new tactics and proof automation.
Thus, this reference manual does not draw a barrier between the two aspects, but rather describes them together so they can shed light on one another.
:::

Lean のプログラムは新しいタクティクや証明の自動化を実装するために使用されるため、Lean のプログラミング機能に精通することは証明を書くことに主な関心があるユーザにとっても価値があります。したがって、このリファレンスマニュアルでは2つの側面の間に壁を設けず、むしろ互いに光を当てることができるように両者を一緒に説明しています。

:::comment
## History
:::

## 歴史
%%%
tag := "history-of-lean"
%%%

:::comment
Leonardo de Moura launched the Lean project when he was at Microsoft Research in 2013, and Lean 0.1 was officially released on June 16, 2014.
The goal of the Lean project is to combine the high level of trust provided by a small, independently-implementable logical kernel with the convenience and automation of tools like SMT solvers, while scaling to large problems.
This vision still guides the development of Lean, as we invest in improved automation, improved performance, and user-friendliness; the trusted core proof checker is still minimal and independent implementations exist.
:::

Leonardo de Moura は2013年に Microsoft Research 在籍時に Lean プロジェクトを立ち上げ、2014年6月16日に Lean 0.1 が正式にリリースされました。Lean プロジェクトの目標は、独立に実装可能な小さな論理カーネル提供する高い信頼性と、SMTソルバのようなツールの利便性と自動化を組み合わせ、同時に大規模な問題にも対応できるようにすることです。このビジョンは現在も Lean の開発の指針となっており、自動化の改善・性能の向上・使いやすさの向上に投資されています；信頼されたコアな証明チェッカもまた最小限で、独立な実装が存在します。

:::comment
The initial versions of Lean were primarily configured as C++ libraries in which client code could carry out trustworthy proofs that were independently checkable.
In these early years, the design of Lean rapidly evolved towards traditional interactive provers, first with tactics written in Lua, and later with a dedicated front-end syntax.
January 20, 2017 saw the first release of the Lean 3.0 series.
Lean 3 achieved widespread adoption by mathematicians, and pioneered self-extensibility: tactics, notations, and top-level commands could all be defined in Lean itself.
The mathematics community built Mathlib, which at the end of Lean 3 had over one million lines of formalized mathematics, with all proofs mechanically checked.
The system itself, however, was still implemented in C++, which imposed limits on Lean's flexibility and made it more difficult to develop due to the diverse skills required.
:::

Lean の初期バージョンは主に C++ ライブラリとして構成され、クライアントコードが独立してチェック可能な信頼できる証明を実行できるようになっていました。この初期の数年間で Lean の設計は、最初は Lua で書かれたタクティクからのちに専用のフロントエンド構文へと、伝統的な対話型証明器へと急速に進化しました。2017年1月20日、Lean 3.0 シリーズの最初のリリースがありました。Lean 3 は数学者に広く採用され、自己拡張性を開拓しました：タクティク・記法・トップレベルコマンドはすべて Lean 自体で定義できます。数学コミュニティは Mathlib を構築し、Lean 3 の終わり頃には数学の形式化は100万行を超え、すべての証明が機械的にチェックされていました。しかしシステム自体はまだ C++ で実装されていたため、Lean の柔軟性には限界があり、必要とされるスキルが多岐にわたるため、開発はより困難になっていました。

:::comment
Development of Lean 4 began in 2018, culminating in the 4.0 release on September 8, 2023.
Lean 4 represents an important milestone: as of version 4, Lean is self-hosted - approximately 90% of the code that implements Lean is itself written in Lean.
Lean 4's rich extension API provides users with the ability to adapt it to their needs, rather than relying on the core developers to add necessary features.
Additionally, self-hosting makes the development process much faster, so features and performance can be delivered more quickly; Lean 4 is faster and scales to larger problems than Lean 3.
Mathlib was successfully ported to Lean 4 in 2023 through a community effort supported by the Lean developers, and it has now grown to over 1.5 million lines.
Even though Mathlib has grown by 50%, Lean 4 checks it faster than Lean 3 could check its smaller library.
The development process for Lean 4 was approximately as long as that of all prior versions combined, and we are now delighted with its design—no further rewrites are planned.
:::

Lean 4 の開発は2018年に始まり、2023年9月8日の4.0リリースで実を結びました。Lean 4 は重要なマイルストーンを体現しています：バージョン4の時点で、Lean はセルフホストされており、Lean を実装するコードの約90%は Lean で書かれています。Lean 4 の豊富な拡張 API は、必要な機能を追加するためにコアの開発者に依存するのではなく、ユーザに自分のニーズへ適応させる能力を提供します。さらに、セルフホスティングによって開発プロセスが大幅に高速化されたため、Lean の機能やパフォーマンスをより迅速に提供することができます；Lean 4 は Lean 3 よりも高速で、より大きな問題にも対応できるスケーラビリティを備えています。Mathlib は Lean の開発者がサポートするコミュニティの努力によって、2023年に Lean 4 への移植に成功し、現在では150万行を超えるまでに成長しました。Mathlib が50%増大したにも関わらず、Lean 4 は Lean 3 がその小さなライブラリをチェックするよりも早くチェックします。Lean 4 の開発プロセスは以前のすべてのバージョンを合わせたのと同じくらいの時間がかかりましたが、開発者たちはその設計に満足しています。これ以上の改修は予定されていません。

:::comment
Leonardo de Moura and his co-founder, Sebastian Ullrich, launched the Lean Focused Research Organization (FRO) nonprofit in July of 2023 within Convergent Research, with philanthropic support from the Simons Foundation International, the Alfred P. Sloan Foundation, and Richard Merkin.
The FRO currently has more than ten employees working to support the growth and scalability of Lean and the broader Lean community.
:::

Leonardo de Moura と彼の共同設立者である Sebastian Ullrich は2023年7月、Simons Foundation International・Alfred P. Sloan Foundation・Richard Merkin からの後援を受けて、非営利団体 Lean Focused Research Organization (FRO) を Convergent Research 内に立ち上げました。FRO は現在10人以上の従業員を擁し、Lean やより広範な Lean コミュニティの成長とスケーラビリティの支援に取り組んでいます。

:::comment
# Typographical Conventions
:::

# 表記ルール
%%%
tag := "typographical-conventions"
%%%

:::comment
This document makes use of a number of typographical and layout conventions to indicate various aspects of the information being presented.
:::

本書では提示される情報のさまざまな側面を示すために、多くの表記やレイアウトの慣例を用いています。

:::comment
## Lean Code

:::

## Lean のコード
%%%
tag := "code-samples"
%%%

:::comment
This document contains many Lean code examples.
They are formatted as follows:
:::

本書には多くの Lean コードの例が含まれています。これらは次のような形式になっています：

````lean
def hello : IO Unit := IO.println "Hello, world!"
````

:::comment
Compiler output (which may be errors, warnings, or just information) is shown both in the code and separately:
:::

コンパイラの出力（エラー・警告・単なる情報）は、コードの中と別に表示されます：

````lean (name := output) (error := true)
#eval s!"The answer is {2 + 2}"

theorem bogus : False := by sorry

example := Nat.succ "two"
````

:::comment
Informative output, such as the result of {keywordOf Lean.Parser.Command.eval}`#eval`, is shown like this:
:::

有益な出力、例えば {keywordOf Lean.Parser.Command.eval}`#eval` の結果などはこのように表示されます：

```leanOutput output (severity := information)
"The answer is 4"
```

:::comment
Warnings are shown like this:
:::

警告はこのように表示されます：

```leanOutput output (severity := warning)
declaration uses 'sorry'
```

:::comment
Error messages are shown like this:
:::

エラーメッセージはこのように表示されます：

```leanOutput output (severity := error)
application type mismatch
  Nat.succ "two"
argument
  "two"
has type
  String : Type
but is expected to have type
  Nat : Type
```


:::comment
The presence of tactic proof states is indicated by the presence of small lozenges that can be clicked to show the proof state, such as after {tactic}`rfl` below:
:::

タクティクによる証明状態の存在は、以下の {tactic}`rfl` の後のように、証明状態を表示するためにクリックできる小さな錠剤のようなマークの存在によって示されます：

```lean
example : 2 + 2 = 4 := by rfl
```

::::tacticExample
:::comment
Proof states may also be shown on their own.
When attempting to prove that {goal}`2 + 2 = 4`, the initial proof state is:
:::
証明状態は単独で示されることもあります。 {goal}`2 + 2 = 4` を証明しようとするとき、最初の証明状態は次のようになります：
```pre
⊢ 2 + 2 = 4
```
:::comment
After using {tacticStep}`rfl`, the resulting state is:
:::
{tacticStep}`rfl` を使ったのち、結果の状態は次のようになります：
```post

```

```setup
skip
```
::::

:::comment
Identifiers in code examples are hyperlinked to their documentation.
:::

コード例中の識別子はそれのドキュメントに対してハイパーリンクが張られます。

:::comment
Examples of code with syntax errors are shown with an indicator of where the parser stopped, along with the error message:
:::

構文エラーのあるコードの例は、エラーメッセージとともにパーサがどこで停止したかを示すインジケータを表示します：

```syntaxError intro
def f : Option Nat → Type
  | some 0 => Unit
  | => Option (f t)
  | none => Empty
```
```leanOutput intro
<example>:3:4: expected term
```

:::comment
## Examples
:::

## 例
%%%
tag := "example-boxes"
%%%

:::comment
Illustrative examples are in callout boxes, as below:
:::

具体例は以下のように吹き出しの中に置かれます：

:::::keepEnv
:::comment
::example "Even Numbers"
:::
::::example "偶数"
:::comment
This is an example of an example.
:::

これは具体例の例です。

:::comment
One way to define even numbers is via an inductive predicate:
:::

偶数を定義する1つの方法は、帰納的述語を使うことです：

```lean
inductive Even : Nat → Prop where
  | zero : Even 0
  | plusTwo : Even n → Even (n + 2)
```
::::
:::::

:::comment
## Technical Terminology

:::

## 専門用語
%%%
tag := "technical-terms"
%%%

:::comment
{deftech}_Technical terminology_ refers to terms used in a very specific sense when writing technical material, such as this reference.
Uses of {tech}[technical terminology] are frequently hyperlinked to their definition sites, using links like this one.
:::

{deftech}_専門用語_ とは、このようなリファレンスのような技術資料を書く際に、非常に特殊な意味で使われる用語を指します。 {tech}[専門用語] の使用はこのようなリンクを使ってその定義位置にハイパーリンクされることがよくあります。

:::comment
## Constant, Syntax, and Tactic References

:::

## 定数・構文・タクティクの参照
%%%
tag := "reference-boxes"
%%%

:::comment
Definitions, inductive types, syntax formers, and tactics have specific descriptions.
These descriptions are marked as follows:
:::

定義・帰納型・構文形成器・タクティクには具体的な記述があります。これらの記述は以下のように記されています。

::::keepEnv
:::comment
```lean
/--
Evenness: a number is even if it can be evenly divided by two.
-/
inductive Even : Nat → Prop where
  | /-- 0 is considered even here -/
    zero : Even 0
  | /-- If `n` is even, then so is `n + 2`. -/
    plusTwo : Even n → Even (n + 2)
```
:::
```lean
/--
偶：ある数が均等に2で割れるなら偶数である。
-/
inductive Even : Nat → Prop where
  | /-- ここでは0は遇だと見なす -/
    zero : Even 0
  | /-- もし `n` が遇ならば、`n + 2` も遇である。 -/
    plusTwo : Even n → Even (n + 2)
```

{docstring Even}

::::
