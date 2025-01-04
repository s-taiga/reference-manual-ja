/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Manual.NotationsMacros.Operators
import Manual.NotationsMacros.Precedence
import Manual.NotationsMacros.Notations
import Manual.NotationsMacros.SyntaxDef

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

/-
#doc (Manual) "Notations and Macros" =>
-/
#doc (Manual) "記法とマクロ（Notations and Macros）" =>
%%%
tag := "language-extension"
%%%

:::comment
Different mathematical fields have their own notational conventions, and many notations are re-used with differing meanings in different fields.
It is important that formal developments are able to use established notations: formalizing mathematics is already difficult, and the mental overhead of translating between syntaxes can be substantial.
At the same time, it's important to be able to control the scope of notational extensions.
Many fields use related notations with very different meanings, and it should be possible to combine developments from these separate fields in a way where both readers and the system know which convention is in force in any given region of a file.

:::

数学では分野ごとに固有の記法の慣習を持っており、多くの記法が複数の分野で異なる意味として再利用されています。形式化の開発では確立された記法を使えることが重要です：数学の形式化はすでに難しいものになっており、構文間の変換による精神的オーバーヘッドは相当なものになります。同時に、記法の拡張範囲をコントロールできることも重要です。多くの分野では、全く異なる意味を持つ似た表記が使われており、読者とシステムの両方が、ファイルの任意の領域でどの記法が有効であるかを知ることができるような方法でこれらの別々の分野からの開発を組み合わせることが可能でなければならない。

:::comment
Lean addresses the problem of notational extensibility with a variety of mechanisms, each of which solves a different aspect of the problem.
They can be combined flexibly to achieve the necessary results:

:::

Lean はさまざまなメカニズムで記法の拡張性の問題に取り組んでおり、それぞれが問題の異なる側面を解決しています。必要な結果を得るために、それらを柔軟に組み合わせることができます：

:::comment
 * The {ref "parser"}_extensible parser_ {index}[parser] allows a great variety of notational conventions to be implemented declaratively, and combined flexibly.
 * {ref "macro-and-elab"}[Macros] allow new syntax to be easily mapped to existing syntax, which is a simple way to provide meaning to new constructs.
  Due to {tech}[hygiene] and automatic propagation of source positions, this process doesn't interfere with Lean's interactive features.
 * {ref "macro-and-elab"}[Elaborators] provide new syntax with the same tools available to Lean's own syntax in cases where a macro is insufficiently expressive.
 * {ref "notations"}[Notations] allow the simultaneous definition of a parser extension, a macro, and a pretty printer.
   When defining infix, prefix, or postfix operators, {ref "operators"}[custom operators] automatically take care of precedence and associativity.
 * Low-level parser extensions allow the parser to be extended in ways that modify its rules for tokens and whitespace, or that even completely replace Lean's syntax. This is an advanced topic that requires familiarity with Lean internals; nevertheless, the possibility of doing this without modifying the compiler is important. This reference manual is written using a language extension that replaces Lean's concrete syntax with a Markdown-like language for writing documents, but the source files are still Lean files.

:::

 * {ref "parser"}_拡張可能なパーサ_ {index}[parser] は非常に多様な記法規則を宣言的に実装し、柔軟に組み合わせることができます。
 * {ref "macro-and-elab"}[マクロ] により、新しい構成に意味を与えるシンプルな方法によって新しい構文を既存の構文に簡単にマッピングすることができます。 {tech}[hygiene] とソース位置の自動伝播によって、このプロセスは Lean の対話的機能を妨げません。
 * {ref "macro-and-elab"}[エラボレータ] はマクロの表現力が不十分な場合に Lean 独自の構文と同じツールを使って新しい構文を提供します。
 * {ref "notations"}[記法] はパーサ拡張・マクロ・プリティプリンタを同時に定義できます。中置・前置・後置演算子を定義する場合、 {ref "operators"}[カスタム演算子] が自動的に優先順位と結合性を考慮します。
 * 低レベルのパーサ拡張は、トークンや空白に対するルールを変更したり、Lean の構文を完全に置き換えたりするような方法でパーサを拡張することを可能にします。これは高度なトピックであり、Lean の内部構造に精通している必要があります；とはいえ、コンパイラを修正することなくこれを行える可能性があることは重要です。このリファレンスマニュアルは Lean の具体的な構文を Markdown のような言語で置き換えた言語拡張を使って書かれていますが、ソースファイルは Lean のままです。

{include 0 Manual.NotationsMacros.Operators}

{include 0 Manual.NotationsMacros.Precedence}

{include 0 Manual.NotationsMacros.Notations}

{include 0 Manual.NotationsMacros.SyntaxDef}


# マクロ（Macros）

%%%
tag := "macros"
%%%

:::comment
# Macros
-- 別ファイル内容importのために上下入れ替え
:::

:::comment
{deftech}_Macros_ are transformations from {name Lean.Syntax}`Syntax` to {name Lean.Syntax}`Syntax` that occur during {tech key:="elaborator"}[elaboration] and during {ref "tactic-macros"}[tactic execution].
Replacing syntax with the result of transforming it with a macro is called {deftech}_macro expansion_.
Multiple macros may be associated with a single {tech}[syntax kind], and they are attempted in order of definition.
Macros are run in a {tech}[monad] that has access to some compile-time metadata and has the ability to either emit an error message or to delegate to subsequent macros, but the macro monad is much less powerful than the elaboration monads.

:::

{deftech}_マクロ_ （macro）は {tech key:="エラボレータ"}[エラボレーション] および {ref "tactic-macros"}[タクティクの実行] 中に出現する {name Lean.Syntax}`Syntax` から {name Lean.Syntax}`Syntax` への変換処理のことです。構文をマクロで変換した結果で置き換えることを {deftech}_マクロ展開_ （macro expansion）と呼びます。複数のマクロを1つの {tech}[構文種別] に関連付けることができ、定義順に試行されます。マクロは {tech}[monad] の中で実行され、コンパイル時のメタデータにアクセスし、エラーメッセージを出すかマクロ展開を後続のマクロに委譲するする機能を持ちますが、マクロモナドはエラボレーションモナドにくらべてはるかに非力です。

```lean (show := false)
section
open Lean (Syntax MacroM)
```

:::comment
Macros are associated with {tech}[syntax kinds].
An internal table maps syntax kinds to macros of type {lean}`Syntax → MacroM Syntax`.
Macros delegate to the next entry in the table by throwing the {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` exception.
A given {name}`Syntax` value _is a macro_ when there is a macro associated with its syntax kind that does not throw {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax`.
If a macro throws any other exception, an error is reported to the user.
{tech}[Syntax categories] are irrelevant to macro expansion; however, because each syntax kind is typically associated with a single syntax category, they do not interfere in practice.

:::

マクロは {tech}[構文種別] に関連付けられます。内部テーブルは構文種別を {lean}`Syntax → MacroM Syntax` 型のマクロにマッピングします。マクロは {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 例外を投げることで次のエントリに委譲します。与えられた {name}`Syntax` の値は {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` を投げない構文種別に関連付けられたマクロが存在する場合、 _マクロとなります_ 。マクロがそれ以外の例外を投げる場合、ユーザにエラーが報告されます。 {tech}[構文カテゴリ] はマクロ展開には関係ありません；ただし、各構文種別は通常1つの構文カテゴリに関連付けられているため実際には干渉しません。

:::::keepEnv
:::comment
::example "Macro Error Reporting"
:::
::::example "マクロからのエラー報告"
:::comment
The following macro reports an error when its parameter is the literal numeral five.
It expands to its argument in all other cases.
:::

次のマクロはパラメータがリテラル数値 5 である場合にエラーを報告します。それ以外の場合は引数に展開されます。

```lean
syntax &"notFive" term:arg : term
open Lean in
macro_rules
  | `(term|notFive 5) =>
    Macro.throwError "'5' is not allowed here"
  | `(term|notFive $e) =>
    pure e
```

:::comment
When applied to terms that are not syntactically the numeral five, elaboration succeeds:
:::

構文的に数値の 5 でない項に適用するとエラボレーションが成功します：

```lean (name := notFiveAdd)
#eval notFive (2 + 3)
```
```leanOutput notFiveAdd
5
```

:::comment
When the error case is triggered, the user receives an error message:
:::

エラーのケースがトリガーされると、ユーザはエラーメッセージを受け取ります：

```lean (name := notFiveFive) (error := true)
#eval notFive 5
```
```leanOutput notFiveFive
'5' is not allowed here
```
::::
:::::

:::comment
Before elaborating a piece of syntax, the elaborator checks whether its {tech}[syntax kind] has macros associated with it.
These are attempted in order.
If a macro succeeds, potentially returning syntax with a different kind, the check is repeated and macros are expanded again until the outermost layer of syntax is no longer a macro.
Elaboration or tactic execution can then proceed.
Only the outermost layer of syntax (typically a {name Lean.Syntax.node}`node`) is expanded, and the output of macro expansion may contain nested syntax that is a macro.
These nested macros are expanded in turn when the elaborator reaches them.

:::

構文の一部をエラボレートする前に、エラボレータはその {tech}[構文種別] にマクロが関連付けられているかどうかをチェックします。これらは順番に試行されます。マクロが成功し、異なる種類の構文を返す可能性がある場合、チェックが繰り返され、構文の一番外側がマクロでなくなるまでマクロが繰り返し展開されます。その後、エラボレーションやタクティクの実行が可能になります。構文の一番外側（通常は {name Lean.Syntax.node}`node` ）だけが展開されます。このマクロ展開の出力にはマクロの構文が含まれる場合があります。これらの入れ子になったマクロはエラボレータがそこに到達した時に順番に展開されます。

:::comment
In particular, macro expansion occurs in three situations in Lean:

:::

特に、Lean では3つの状況でマクロ展開が発生します：

:::comment
 1. During term elaboration, macros in the outermost layer of the syntax to be elaborated are expanded prior to invoking the {ref "elaborators"}[syntax's term elaborator].

:::

 1. 項のエラボレーションの際において、 {ref "elaborators"}[構文の項エラボレータ] を呼び出す前にエラボレートされる構文の一番外側のマクロが展開されます。

:::comment
 2. During command elaboration, macros in the outermost layer of the syntax to be elaborated are expanded prior to invoking the {ref "elaborators"}[syntax's command elaborator].

:::

 2. コマンドのエラボレーションの際において、 {ref "elaborators"}[構文のコマンドエラボレータ] を呼び出す前にエラボレートされる一番外側のマクロが展開されます。

:::comment
 3. During tactic execution, macros in the outermost layer of the syntax to be elaborated are expanded {ref "tactic-macros"}[prior to executing the syntax as a tactic].


:::

 3. タクティクの実行の際において、 {ref "tactic-macros"}[その構文をタクティクとして実行する前に] エラボレートされる一番外側のマクロが展開されます。

```lean (keep := false) (show := false)
-- Test claim in preceding paragraph that it's OK for macros to give up prior to elab
syntax "doubled " term:arg : term

macro_rules
  | `(term|doubled $n:num) => `($n * 2)
  | `(term|doubled $_) => Lean.Macro.throwUnsupported

/-- info: 10 -/
#guard_msgs in
#eval doubled 5

/--
error: elaboration function for 'termDoubled_' has not been implemented
  doubled (5 + 2)
-/
#guard_msgs in
#eval doubled (5 + 2)

elab_rules : term
  | `(term|doubled $e:term) => Lean.Elab.Term.elabTerm e none

/-- info: 7 -/
#guard_msgs in
#eval doubled (5 + 2)
```

:::comment
## Hygiene
:::

## 健全性（Hygiene）

%%%
tag := "macro-hygiene"
%%%

:::comment
A macro is {deftech (key:="hygiene")}_hygienic_ if its expansion cannot result in identifier capture.
{deftech}[Identifier capture] is when an identifier ends up referring to a binding site other than that which is in scope where the identifier occurs in the source code.
There are two types of identifier capture:
 * If a macro's expansion introduces binders, then identifiers that are parameters to the macro may end up referring to the introduced binders if their names happen to match.
 * If a macro's expansion is intended to refer to a name, but the macro is used in a context that either locally binds this name or in which a new global name has been introduced, it may end up referring to the wrong name.

:::

マクロが {deftech (key:="hygiene")}_健全である_ （hygienic）であるとは、その展開によって識別子のキャプチャが生じないようなマクロを指します。 {deftech}[識別子のキャプチャ] （identifier capture）とは、識別子がソースコード内で発生するスコープ以外の束縛位置を参照してしまうことです。識別子のキャプチャには2つのタイプがあります：
 * マクロ展開で束縛子が導入される場合、マクロのパラメータである識別子はその名前が一致すると導入された束縛子を参照してしまう可能性があります。
 * マクロ展開が名前を参照することを意図している場合において、その名前がローカルに束縛されているか、新しいグローバル名として導入されているコンテキストにおいてマクロが使用されると、間違った名前を参照してしまう可能性があります。

:::comment
The first kind of variable capture can be avoided by ensuring that every binding introduced by a macro uses a freshly generated, globally-unique name, while the second can be avoided by always using fully-qualified names to refer to constants.
The fresh names must be generated again at each invocation of the macro to avoid variable capture in recursive macros.
These techniques are error-prone.
Variable capture issues are difficult to test for because they rely on coincidences of name choices, and consistently applying these techniques results in noisy code.

:::

1つ目の変数キャプチャは、マクロによって導入されるすべての束縛子が新しく生成されたもので、かつグローバルで一意な名前を使用することで、2つ目は定数の参照に常に完全修飾名を使用することでそれぞれ回避できます。1つ目の対策での新しい名前は、再帰的なマクロでの変数キャプチャを回避するためにマクロの呼び出しのたびに生成する必要があります。これらのテクニックはエラーを起こしやすいです。変数キャプチャの問題は、名前の選択の一致に依存するためテストが難しく、これらのテクニックを一貫して適用すると読みづらいコードになります。

:::comment
Lean features automatic hygiene: in almost all cases, macros are automatically hygienic.
Capture by introduced bindings is avoided by annotating identifiers introduced by a macro with {deftech}_macro scopes_, which uniquely identify each invocation of macro expansion.
If the binding and the use of the identifier have the same macro scopes, then they were introduced by the same step of macro expansion and should refer to one another.
Similarly, uses of global names in code generated by a macro are not captured by local bindings in the context in which they are expanded because these use sites have macro scopes that are not present in the binding occurrence.
Capture by newly-introduced global names is prevented by annotating potential global name references with the set of global names that match at quotation time in code produced in the macro's body.
Identifiers annotated with potential referents are called {deftech}_pre-resolved identifiers_, and the {lean}`Syntax.Preresolved` field on the {name}`Syntax.ident` constructor is used to store the potential referents.
During elaboration, if an identifier has pre-resolved global names associated with it, then other global names are not considered as valid reference targets.

:::

Lean は自動的な健全性の機構を持ちます：ほとんどすべての場合において、マクロは自動的に健全です。導入された束縛子によるキャプチャは、マクロによって導入された識別子を {deftech}_マクロスコープ_ （macro scope）で注釈することで回避できます。マクロスコープはマクロ展開のそれぞれの呼び出しごとに一意に識別されます。束縛子と識別子の使用が同じマクロスコープを持つ場合、それらはマクロ展開の同じステップで導入されたものであり、お互いを参照する必要があります。同様に、マクロによって生成されたコードでのグローバル名の使用は、それが展開されたコンテキストではローカルの束縛子によってキャプチャされません。なぜなら、そのグローバル名の使用位置には束縛子の出現には存在しないマクロスコープがあるからです。新しく導入されたグローバル名によるキャプチャは、潜在的なグローバル名参照に対してマクロの本体で生成されるコードで quotation 時に一致するグローバル名のセットをアノテーションすることで防がれます。潜在的な参照による注釈された識別子は {deftech}_事前解決された識別子_ （pre-resolved identifier）と呼ばれ、 {name}`Syntax.ident` コンストラクタの {lean}`Syntax.Preresolved` フィールドは潜在的な参照先を格納するために使用されます。エラボレーションの際に、識別子が事前解決されたグローバル名に関連付けられている場合、他のグローバル名は有効な参照対象として考慮されません。

:::comment
The introduction of macro scopes and pre-resolved identifiers to generated syntax occurs during {tech}[quotation].
Macros that construct syntax by other means than quotation should also ensure hygiene by some other means.
For more details on Lean's hygiene algorithm, please consult {citet beyondNotations ullrich23}[].

:::

生成された構文へのマクロスコープと事前解決された識別子の導入は {tech}[quotation] の間に行われます。quotation 以外の方法で構文を構築するマクロであっても、他の何らかの方法で健全性を確保する必要があります。Lean の健全性アルゴリズムの詳細については {citet beyondNotations ullrich23}[] を参照してください。

:::comment
## The Macro Monad
:::

## マクロモナド（The Macro Monad）

%%%
tag := "macro-monad"
%%%

:::comment
The macro monad {name Lean.MacroM}`MacroM` is sufficiently powerful to implement hygiene and report errors.
Macro expansion does not have the ability to modify the environment directly, to carry out unification, to examine the current local context, or to do anything else that only makes sense in one particular context.
This allows the same macro mechanism to be used throughout Lean, and it makes macros much easier to write than {tech}[elaborators].

:::

マクロモナド {name Lean.MacroM}`MacroM` は健全性を実装し、エラーを報告するのに十分な機能を有しています。マクロ展開には環境を直接変更したり、単一化を実行したり現在のローカルコンテキストを調べたり、ある特定のコンテキストのみで意味を持つようなことはできません。これにより、Lean 全体で同じマクロ機構を使用することができ、マクロは {tech}[エラボレータ] よりもはるかに書きやすくなります。

{docstring Lean.MacroM}

{docstring Lean.Macro.expandMacro?}

{docstring Lean.Macro.trace}

:::comment
### Exceptions and Errors
:::

### 例外とエラー（Exceptions and Errors）

%%%
tag := "macro-exceptions"
%%%

:::comment
The {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` exception is used for control flow during macro expansion.
It indicates that the current macro is incapable of expanding the received syntax, but that an error has not occurred.
The exceptions thrown by {name Lean.Macro.throwError}`throwError` and {name Lean.Macro.throwErrorAt}`throwErrorAt` terminate macro expansion, reporting the error to the user.

:::

{name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 例外は、マクロ展開時の制御フローに使用されます。これは現在のマクロが受け取った構文を展開できないが、エラーが発生したわけではないことを示します。 {name Lean.Macro.throwError}`throwError` と {name Lean.Macro.throwErrorAt}`throwErrorAt` が投げる例外はマクロ展開を終了し、ユーザにエラーを報告します。

{docstring Lean.Macro.throwUnsupported}

{docstring Lean.Macro.Exception.unsupportedSyntax}

{docstring Lean.Macro.throwError}

{docstring Lean.Macro.throwErrorAt}

:::comment
### Hygiene-Related Operations
:::

### 健全性関連の操作（Hygiene-Related Operations）

%%%
tag := "macro-monad-hygiene"
%%%

:::comment
{tech}[Hygiene] is implemented by adding {tech}[macro scopes] to the identifiers that occur in syntax.
Ordinarily, the process of {tech}[quotation] adds all necessary scopes, but macros that construct syntax directly must add macro scopes to the identifiers that they introduce.

:::

{tech}[Hygiene] は構文中に出現する識別子に {tech}[マクロスコープ] を追加することで実装されます。通常、 {tech}[quotation] の処理は必要なスコープをすべて追加しますが、構文を直接構成するマクロは、導入する識別子にマクロスコープを追加しなければなりません。

{docstring Lean.Macro.withFreshMacroScope}

{docstring Lean.Macro.addMacroScope}

:::comment
### Querying the Environment
:::

### 環境への問い合わせ（Querying the Environment）

%%%
tag := "macro-environment"
%%%

:::comment
Macros have only limited support for querying the environment.
They can check whether a constant exists and resolve names, but further introspection is unavailable.

:::

マクロの環境への問い合わせは限られた機能しかサポートされていません。定数が存在するかどうかをチェックし、名前を解決することはできますが、それ以上の考慮・吟味はできません。

{docstring Lean.Macro.hasDecl}

{docstring Lean.Macro.getCurrNamespace}

{docstring Lean.Macro.resolveNamespace}

{docstring Lean.Macro.resolveGlobalName}

## Quotation
%%%
tag := "quotation"
%%%

:::comment
{deftech}_Quotation_ marks code for representation as data of type {name}`Syntax`.
Quoted code is parsed, but not elaborated—while it must be syntactically correct, it need not make sense.
Quotation makes it much easier to programmatically generate code: rather than reverse-engineering the specific nesting of {name Lean.Syntax.node}`node` values that Lean's parser would produce, the parser can be directly invoked to create them.
This is also more robust in the face of refactoring of the grammar that may change the internals of the parse tree without affecting the user-visible concrete syntax.
Quotation in Lean is surrounded by `` `( `` and `)`.

:::

{deftech}_Quotation_ は {name}`Syntax` 型のデータとして表現するためにコードをマークします。quote されたコードはパースされますが、エラボレートはされません。つまり構文的に正しくなければなりませんが、意味を為している必要はありません。quotation はコードをプログラム的に生成することをとても簡単にします：Lean のパーサが生成する {name Lean.Syntax.node}`node` 値の特定の入れ子をリバースエンジニアリングするのではなく、パーサを直接呼び出して生成することができます。これはまた、文法のリファクタリングが、ユーザから見える具体的な構文に影響を与えることなくパースされた木の内部を変更する可能性がある場合により堅牢です。Lean の quotation は ``​`(`` と `)` で囲まれます。

:::comment
The syntactic category or parser being quoted may be indicated by placing its name after the opening backtick and parenthesis, followed by a vertical bar (`|`).
As a special case, the name `tactic` may be used to parse either tactics or sequences of tactics.
If no syntactic category or parser is provided, Lean attempts to parse the quotation both as a term and as a non-empty sequence of commands.
Term quotations have higher priority than command quotations, so in cases of ambiguity, the interpretation as a term is chosen; this can be overridden by explicitly indicating that the quotation is of a command sequence.

:::

quote される構文カテゴリやパーサは、その名前を先頭のバックティックと括弧の後に置き、その後に縦棒（`|`）を置くことで示すことができます。特殊なケースとして、`tactic` という名前はタクティクやタクティクの列をパースするために使用することができます。構文カテゴリやパーサが提供されていない場合、Lean は quotation を項と空でない一連のコマンドの両方としてパースしようとします。項の quotation はコマンドの quotation よりも優先順位が高いため、あいまいな場合は項として解釈されます；これはコマンド列の quotation であることを明示することで上書きできます。

:::::keepEnv
:::comment
::example "Term vs Command Quotation Syntax"
:::
::::example "項 vs コマンドの quotation 構文"
```lean (show := false)
open Lean
```

:::comment
In the following example, the contents of the quotation could either be a function application or a sequence of commands.
Both match the same region of the file, so the {tech}[local longest-match rule] is not relevant.
Term quotation has a higher priority than command quotation, so the quotation is interpreted as a term.
Terms expect their {tech}[antiquotations] to have type {lean}``TSyntax `term`` rather than {lean}``TSyntax `command``.
:::

以下の例では、quotation の中身は関数適用かコマンド列のどちらかです。どちらもファイルの同じ領域でマッチするため、 {tech}[ローカル最長一致規則] は関係しません。項の quotation はコマンドの quotation よりも優先順位が高いため、quotation は項として解釈されます。項は {lean}``TSyntax `command`` 型よりも {lean}``TSyntax `term`` 型を持つ {tech}[antiquotations] を期待します。

```lean (error := true) (name := cmdQuot)
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) := `($cmd1 $cmd2)
```
:::comment
The result is two type errors like the following:
:::

これにより、以下のような2つの型エラーが発生します：

```leanOutput cmdQuot
application type mismatch
  cmd1.raw
argument
  cmd1
has type
  TSyntax `command : Type
but is expected to have type
  TSyntax `term : Type
```

:::comment
The type of the quotation ({lean}``MacroM (TSyntax `command)``) is not used to select a result because syntax priorities are applied prior to elaboration.
In this case, specifying that the antiquotations are commands resolves the ambiguity because function application would require terms in these positions:
:::

構文の優先順位はエラボレーションの前に適用されるため、quotation の型（ {lean}``MacroM (TSyntax `command)`` ）は結果の選択に使用されません。この場合、antiquotation がコマンドであることを指定すると、関数の適用がこれらの位置に項を必要とするため、あいまいさが解決されます：

```lean
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) := `($cmd1:command $cmd2:command)
```
:::comment
Similarly, inserting a command into the quotation eliminates the possibility that it could be a term:
:::

同様に、コマンドを quotation の中に挿入することができ、それが項である可能性を排除することができます：

```lean
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) := `($cmd1 $cmd2 #eval "hello!")
```
::::
:::::

```lean (show := false)
-- There is no way to extract parser priorities (they're only saved in the Pratt tables next to
-- compiled Parser code), so this test of priorities checks the observable relative priorities of the
-- quote parsers.

/--
info: do
  let _ ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.getMainModule
  pure { raw := { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `term)
-/
#guard_msgs in
#check (`($(⟨.missing⟩)) : MacroM _)
/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.getMainModule
  pure
      {
        raw :=
          Syntax.node2 info `Lean.Parser.Term.app { raw := Syntax.missing }.raw
            (Syntax.node1 info `null { raw := Syntax.missing }.raw) } : MacroM (Lean.TSyntax `term)
-/
#guard_msgs in
#check (`($(⟨.missing⟩) $(⟨.missing⟩)) : MacroM _)
/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.getMainModule
  pure
      {
        raw :=
          Syntax.node2 info `null { raw := Syntax.missing }.raw
            { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `command)
-/
#guard_msgs in
#check (`($(⟨.missing⟩):command $(⟨.missing⟩)) : MacroM _)

/--
info: do
  let _ ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.getMainModule
  pure { raw := { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `tactic)
-/
#guard_msgs in
#check (`(tactic| $(⟨.missing⟩):tactic) : MacroM _)

/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.getMainModule
  pure
      {
        raw :=
          Syntax.node1 info `Lean.Parser.Tactic.seq1
            (Syntax.node3 info `null { raw := Syntax.missing }.raw (Syntax.atom info ";")
              { raw := Syntax.missing }.raw) } : MacroM (Lean.TSyntax `tactic.seq)
-/
#guard_msgs in
#check (`(tactic|
          $(⟨.missing⟩):tactic; $(⟨.missing⟩)) : MacroM _)
```

::::freeSyntax term (open := false)

:::comment
Lean's syntax includes quotations for terms, commands, tactics, and sequences of tactics, as well as a general quotation syntax that allows any input that Lean can parse to be quoted.
Term quotations have the highest priority, followed by tactic quotations, general quotations, and finally command quotations.

:::

Lean の構文には、項・コマンド・タクティク・タクティク列の quotation と、Lean がパースできるすべての入力を quote できる一般的な quotation 構文があります。項の quotation が最も優先順位が高く、次いでタクティクの quotation・一般的な quotation・コマンドの quotation と続きます。

```grammar
`(term|`($_:term))
*******
"`("$_:command+")"
*******
`(term|`(tactic| $_:tactic))
*******
`(term|`(tactic| $_:tactic;*))
*******
"`("p:ident"|"/-- Parse a {p} here -/")"
```
::::

```lean (show := false)
section M
variable {m : Type → Type}
open Lean (MonadRef MonadQuotation)
open Lean.Elab.Term (TermElabM)
open Lean.Elab.Command (CommandElabM)
open Lean.Elab.Tactic (TacticM)
```

:::comment
Rather than having type {name}`Syntax`, quotations are monadic actions with type {lean}`m Syntax`.
Quotation is monadic because it implements {tech}[hygiene] by adding {tech}[macro scopes] and pre-resolving identifiers, as described in {ref "macro-hygiene"}[the section on hygiene].
The specific monad to be used is an implicit parameter to the quotation, and any monad for which there is an instance of the {name}`MonadQuotation` type class is suitable.
{name}`MonadQuotation` extends {name}`MonadRef`, which gives the quotation access to the source location of the syntax that the macro expander or elaborator is currently processing. {name}`MonadQuotation` additionally includes the ability to add {tech}[macro scopes] to identifiers and use a fresh macro scope for a sub-task.
Monads that support quotation include {name}`MacroM`, {name}`TermElabM`, {name}`CommandElabM`, and {name}`TacticM`.

:::

quotation は {name}`Syntax` 型ではなく、 {lean}`m Syntax` 型を持ったモナドアクションです。 {ref "macro-hygiene"}[健全性の節] で説明されているように、 {tech}[マクロスコープ] と事前解決された識別子を追加することで {tech}[hygiene] を実装しているため、quotation はモナドです。使用する特定のモナドは quotation の暗黙のパラメータであり、 {name}`MonadQuotation` 型クラスのインスタンスを持つ任意のモナドが適しています。 {name}`MonadQuotation` は {name}`MonadRef` を継承しており、マクロ展開またはエラボレータが現在処理している構文のソース位置にアクセスすることができます。 {name}`MonadQuotation` はさらに識別子に {tech}[マクロスコープ] を追加し、サブタスクに新しいマクロスコープを使用する機能を含んでいます。quotation をサポートするモナドは、 {name}`MacroM` ・ {name}`TermElabM` ・ {name}`CommandElabM` ・ {name}`TacticM` です。

```lean (show := false)
end M
```


```lean (show := false)
-- Verify claim about monads above
open Lean in
example [Monad m] [MonadQuotation m] : m Syntax := `(term|2 + 2)
```

### Quasiquotation
%%%
tag := "quasiquotation"
%%%

:::comment
{deftech}_Quasiquotation_ is a form of quotation that may contain {deftech}_antiquotations_, which are regions of the quotation that are not quoted, but instead are expressions that are evaluated to yield syntax.
A quasiquotation is essentially a template; the outer quoted region provides a fixed framework that always yields the same outer syntax, while the antiquotations yield the parts of the final syntax that vary.
All quotations in Lean are quasiquotations, so no special syntax is needed to distinguish quasiquotations from other quotations.
The quotation process does not add macro scopes to identifiers that are inserted via antiquotations, because these identifiers either come from another quotation (in which case they already have macro scopes) or from the macro's input (in which case they should not have macro scopes, because they are not introduced by the macro).

:::

{deftech}_Quasiquotation_ は {deftech}_antiquotations_ を含むことができる quotation の形式です。antiquotation は、quote されていない代わりに評価すると構文を生成する式である quotation の領域を指します。quasiquotation は本質的にはテンプレートです；外側の quote された領域は、常に同じ外側の構文を生成する固定されたフレームワークを提供します。Lean の quotation はすべて quasiquotation であるため、quasiquotation を他の quotation と区別するための特別な構文は必要ありません。quotation 処理は antiquotation を通じて挿入された識別子にマクロスコープを追加しません。なぜなら、これらの識別子は別の quotation から来るか（その場合すでにマクロスコープを持っています）、マクロの入力から来るか（その場合、マクロによって導入されたものではないためマクロスコープを持つべきではありません）のいずれかであるからです。

:::comment
Basic antiquotations consist of a dollar sign (`$`) immediately followed by an identifier.
This means that the value of the corresponding variable, which should be a syntax tree, is to be substituted into this position of the quoted syntax.
Entire expressions may be used as antiquotations by wrapping them in parentheses.

:::

基本的な antiquotation はドル記号（`$`）の直後に識別子が続くものです。これは構文木であるべき対応する変数の値が、quote された構文のこの位置に代入されることを意味します。式全体を括弧でくくることで、 antiquotation として使用することができます。

```lean (show := false)
section
open Lean
example (e : Term) : MacroM Syntax := `(term| $e)

example (e : Term) : MacroM Syntax := `(term| $(e))

--example (e : Term) : MacroM Syntax := `(term| $ (e))

end
```



```lean (show := false)
section
open Lean (TSyntax SyntaxNodeKinds)
variable {c : SyntaxNodeKinds}
```

:::comment
Lean's parser assigns every antiquotation a syntax category based on what the parser expects at the given position.
If the parser expects syntax category {lean}`c`, then the antiquotation's type is {lean}`TSyntax c`.


:::

Lean のパーサは、パーサが指定された位置で何を期待するかに基づいて、すべての antiquotation に構文カテゴリを割り当てます。パーサが構文カテゴリ {lean}`c` を期待する場合、antiquotation の型は {lean}`TSyntax c` になります。

:::comment
Some syntax categories can be matched by elements of other categories.
For example, numeric and string literals are valid terms in addition to being their own syntax categories.
Antiquotations may be annotated with the expected category by suffixing them with a colon and the category name, which causes the parser to validate that the annotated category is acceptable in the given position and construct any intermediate layers that are required in the parse tree.

:::

構文カテゴリの中には、他のカテゴリの要素とマッチするものがあります。例えば、数値リテラルと文字列リテラルは、それ自身の構文カテゴリであることに加えて、有効な項です。antiquotation はコロンとカテゴリ名を接尾辞として付けることで、期待されるカテゴリを注釈することができます。これにより、パーサは注釈されたカテゴリが指定された位置で受け入れられるかどうか検証し、パースされた木で必要とされる中間層を構築します。

::::freeSyntax antiquot title:="Antiquotations" open := false
```grammar
"$"ident(":"ident)?
*******
"$("term")"(":"ident)?
```
:::comment
Whitespace is not permitted between the dollar sign ('$') that initiates an antiquotation and the identifier or parenthesized term that follows.
Similarly, no whitespace is permitted around the colon that annotates the syntax category of the antiquotation.
:::

antiquotation を開始するドル記号（`$`）と、それに続く識別子または括弧で囲まれた項の間に空白を入れることはできません。同様に、antiquotation の構文カテゴリを示すコロンの周りには空白を入れられません。

::::

::::example "Quasiquotation"

:::comment
Both forms of antiquotation are used in this example.
Because natural numbers are not syntax, {name Lean.quote}`quote` is used to transform a number into syntax that represents it.

:::

この例では antiquotation の両方の形式が使われています。自然数は構文ではないため、 {name Lean.quote}`quote` は数値を表す構文に変換するために使用されます。

```lean
open Lean in
example [Monad m] [MonadQuotation m] (x : Term) (n : Nat) : m Syntax :=
  `($x + $(quote (n + 2)))
```
::::

:::::keepEnv
:::comment
::example "Antiquotation Annotations"
:::
::::example "Antiquotation 注釈"
```lean (show := false)
open Lean
```

:::comment
This example requires that {lean}`m` is a monad that can perform quotation.
:::

この例では {lean}`m` が quotation を行えるモナドであることを求めています。

```lean
variable {m : Type → Type} [Monad m] [MonadQuotation m]
```

:::comment
By default, the antiquotation `$e` is expected to be a term, because that's the syntactic category that's immediately expected as the second argument to addition.
:::

デフォルトでは、antiquotation `$e` は項であることが期待されます。なぜなら、それが加算の第2引数としてすぐに期待される構文カテゴリであるからです。

```lean (name := ex1)
def ex1 (e) := show m _ from `(2 + $e)
#check ex1
```
```leanOutput ex1
ex1 {m : Type → Type} [Monad m] [MonadQuotation m] (e : TSyntax `term) : m (TSyntax `term)
```

:::comment
Annotating `$e` as a numeric literal succeeds, because numeric literals are also valid terms.
The expected type of the parameter `e` changes to ``TSyntax `num``.
:::

数値リテラルも有効な項であるため、`$e` の数値リテラルとして注釈は成功します。パラメータ `e` に期待される型は ``TSyntax `num`` に変更されます。

```lean (name := ex2)
def ex2 (e) := show m _ from `(2 + $e:num)
#check ex2
```
```leanOutput ex2
ex2 {m : Type → Type} [Monad m] [MonadQuotation m] (e : TSyntax `num) : m (TSyntax `term)
```

:::comment
Spaces are not allowed between the dollar sign and the identifier.
:::

ドル記号と識別子の間にスペースを入れてはいけません。

```syntaxError ex2err1
def ex2 (e) := show m _ from `(2 + $ e:num)
```
```leanOutput ex2err1
<example>:1:35: expected '`(tactic|' or no space before spliced term
```

:::comment
Spaces are also not allowed before the colon:
:::

また、コロンの前にスペースを入れることもできません：

```syntaxError ex2err2
def ex2 (e) := show m _ from `(2 + $e :num)
```
```leanOutput ex2err2
<example>:1:38: expected ')'
```
::::
:::::

```lean (show := false)
end
```

:::::keepEnv
:::comment
::example "Expanding Quasiquotation"
:::
::::example "Quasiquotation の展開"
:::comment
Printing the definition of {name}`f` demonstrates the expansion of a quasiquotation.
:::

{name}`f` の定義を表示することで、quasiquotation の展開が示されます。

```lean (name := expansion)
open Lean in
def f [Monad m] [MonadQuotation m] (x : Term) (n : Nat) : m Syntax :=
  `(fun k => $x + $(quote (n + 2)) + k)
#print f
```
```leanOutput expansion
def f : {m : Type → Type} → [inst : Monad m] → [inst : Lean.MonadQuotation m] → Lean.Term → Nat → m Syntax :=
fun {m} [Monad m] [Lean.MonadQuotation m] x n => do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let scp ← Lean.getCurrMacroScope
  let mainModule ← Lean.getMainModule
  pure
      {
          raw :=
            Syntax.node2 info `Lean.Parser.Term.fun (Syntax.atom info "fun")
              (Syntax.node4 info `Lean.Parser.Term.basicFun
                (Syntax.node1 info `null (Syntax.ident info "k".toSubstring' (Lean.addMacroScope mainModule `k scp) []))
                (Syntax.node info `null #[]) (Syntax.atom info "=>")
                (Syntax.node3 info `«term_+_»
                  (Syntax.node3 info `«term_+_» x.raw (Syntax.atom info "+") (Lean.quote `term (n + 2)).raw)
                  (Syntax.atom info "+")
                  (Syntax.ident info "k".toSubstring' (Lean.addMacroScope mainModule `k scp) []))) }.raw
```

```lean (show := false)
section
variable {x : Term} {n : Nat}
```

:::comment
In this output, the quotation is a {keywordOf Lean.Parser.Term.do}`do` block.
It begins by constructing the source information for the resulting syntax, obtained by querying the compiler about the current user syntax being processed.
It then obtains the current macro scope and the name of the module being processed, because macro scopes are added with respect to a module to enable independent compilation and avoid the need for a global counter.
It then constructs a node using helpers such as {name}`Syntax.node1` and {name}`Syntax.node2`, which create a {name}`Syntax.node` with the indicated number of children.
The macro scope is added to each identifier, and {name Lean.TSyntax.raw}`TSyntax.raw` is used to extract the contents of typed syntax wrappers.
The antiquotations of {lean}`x` and {lean}`quote (n + 2)` occur directly in the expansion, as parameters to {name}`Syntax.node3`.

:::

この出力では、quotation は {keywordOf Lean.Parser.Term.do}`do` ブロックです。これは、処理中の現在のユーザ構文についてコンパイラに問い合わせることで得られる結果の構文のソース情報を構築することから始まります。次に、現在のマクロスコープと処理対象のモジュール名を取得します。これはマクロスコープはモジュールに対して追加されるため、独立したコンパイルが可能になり、グローバルカウンタが不要になるからです。次に、 {name}`Syntax.node1` や {name}`Syntax.node2` などの補助関数を使用してノードを構築します。これらの補助関数は指定された数の子を持つ {name}`Syntax.node` を作成します。マクロスコープは各識別子に追加され、 {name Lean.TSyntax.raw}`TSyntax.raw` は型付き構文ラッパーの内容を抽出するために使用されます。 {lean}`x` と {lean}`quote (n + 2)` の antiquotation は {name}`Syntax.node3` のパラメータとして展開の中で直接発生します。

```lean (show := false)
end
```
::::
:::::


:::comment
### Splices
:::

### スプライス（Splices）

%%%
tag := "splices"
%%%

:::comment
In addition to including other syntax via antiquotations, quasiquotations can include {deftech}_splices_.
Splices indicate that the elements of an array are to be inserted in order.
The repeated elements may include separators, such as the commas between list or array elements.
Splices may consist of an ordinary antiquotation with a {deftech}_splice suffix_, or they may be {deftech}_extended splices_ that provide additional repeated structure.

:::

quasiquotation には antiquotation による他の構文に加えて、 {deftech}_スプライス_ （splice）を含めることができます。スプライスは配列の要素を順番に挿入することを示します。繰り返される要素には、リストや配列の要素間のカンマのような区切り文字を含めることができます。スプライスは {deftech}_スプライス接尾辞_ （splice suffix）を持つ通常の antiquotation から構成されることもあれば、追加の繰り返し構造を提供する {deftech}_拡張スプライス_ （extended splice）であることもあります。

:::comment
Splice suffixes consist of either an asterisk or a valid atom followed by an asterisk (`*`).
Suffixes may follow any identifier or term antiquotation.
An antiquotation with the splice suffix `*` corresponds to a use of `many` or `many1`; both the `*` and `+` suffixes in syntax rules correspond to the `*` splice suffix.
An antiquotation with a splice suffix that includes an atom prior to the asterisk corresponds to a use of `sepBy` or `sepBy1`.
The splice suffix `?` corresponds to a use of `optional` or the `?` suffix in a syntax rule.
Because `?` is a valid identifier character, identifiers must be parenthesized to use it as a suffix.

:::

スプライス接尾辞は、アスタリスクまたは有効なアトムの後にアスタリスク（`*`）を付けたものです。接尾辞は任意の識別子または項の antiquotation の後につけることができます。スプライス接尾辞 `*` を持つ antiquotation は `many` または `many1` に対応します；構文規則の `*` と `+` 接尾辞のどちらも `*` スプライス接尾辞に対応します。アスタリスクの前にアトムを含むスプライス接尾辞を持つ antiquotation は `sepBy` または `sepBy1` に対応します。スプライス接尾辞 `?` は構文規則の `optional` または `?` 接尾辞の使用に対応します。`?` は有効な識別子文字であるため、これを接尾辞として使用するには括弧でくくらなければなりません。

:::comment
While there is overlap between repetition specifiers for syntax and antiquotation suffixes, they have distinct syntaxes.
When defining syntax, the suffixes `*`, `+`, `,*`, `,+`, `,*,?`, and `,+,?` are built in to Lean.
There is no shorter way to specify separators other than `,`.
Antiquotation suffixes are either just `*` or whatever atom was provided to `sepBy` or `sepBy1` followed by `*`.
The syntax repetitions `+` and `*` correspond to the splice suffix `*`; the repetitions `,*`, `,+`, `,*,?`, and `,+,?` correspond to `,*`.
The optional suffix `?` in syntax and splices correspond with each other.


:::

構文の繰り返し指定子と antiquotation の接尾辞は重複していますが、それぞれ別の構文を持っています。構文を定義する際、接尾辞 `*` ・ `+` ・ `,*` ・ `,+` ・ `,*,?` ・ `,+,?` は Lean に組み込まれています。区切り文字を `,` 以外に短く指定する方法はありません。antiquotation の接尾辞は `*` だけか、`sepBy` または `sepBy1` に指定されたアトムの後に `*` が続くものです。構文の繰り返し `+` と `*` はスプライス接尾辞 `*` に対応し、繰り返し `,*` ・ `,+` ・ `,*,?` ・ `,+,?` は `,*` に対応します。構文とスプライスのオプションの接尾辞 `?` はどちらも同じものに対応します。

:::table (header := true)
 * ignore
   - Syntax Repetition
   - Splice Suffix
 * ignore
   - `+` `*`
   - `*`
 * ignore
   - `,*` `,+` `,*,?` `,+,?`
   - `,*`
 * ignore
   - `sepBy(_, "S")` `sepBy1(_, "S")`
   - `S*`
 * ignore
   - `?`
   - `?`
:::


:::::keepEnv
:::comment
::example "Suffixed Splices"
:::
::::example "接尾辞のついたスプライス"
```lean (show := false)
open Lean
open Lean.Elab.Command (CommandElabM)
```

:::comment
This example requires that {lean}`m` is a monad that can perform quotation.
:::

この例では、 {lean}`m` が quotation を実行できるモナドであることを要求しています。

```lean
variable {m : Type → Type} [Monad m] [MonadQuotation m]
```

:::comment
By default, the antiquotation `$e` is expected to be an array of terms separated by commas, as is expected in the body of a list:
:::

デフォルトでは、`$e` はリストの本体で期待されるように、カンマで区切られた項の配列であると期待されます：

```lean (name := ex1)
def ex1 (xs) := show m _ from `(#[$xs,*])
#check ex1
```
```leanOutput ex1
ex1 {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Syntax.TSepArray `term ",") : m (TSyntax `term)
```

:::comment
However, Lean includes a collection of coercions between various representations of arrays that will automatically insert or remove separators, so an ordinary array of terms is also acceptable:
:::

しかし、Lean には配列の様々な表現の間に自動的に区切り文字を挿入したり削除したりする強制のコレクションが含まれているため、普通の項の配列でも構いません：

```lean (name := ex2)
def ex2 (xs : Array (TSyntax `term)) := show m _ from `(#[$xs,*])
#check ex2
```
```leanOutput ex2
ex2 {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Array (TSyntax `term)) : m (TSyntax `term)
```

:::comment
Repetition annotations may also be used with term antiquotations and syntax category annotations.
This example is in {name Lean.Elab.Command.CommandElabM}`CommandElabM` so the result can be conveniently logged.
:::

繰り返しの注釈は項の antiquotation や構文カテゴリの注釈と一緒に使用することもできます。この例は {name Lean.Elab.Command.CommandElabM}`CommandElabM` で記述されているため、結果を便利にログに残すことができます。

```lean (name := ex3)
def ex3 (size : Nat) := show CommandElabM _ from do
  let mut nums : Array Nat := #[]
  for i in [0:size] do
    nums := nums.push i
  let stx ← `(#[$(nums.map (Syntax.mkNumLit ∘ toString)):num,*])
  -- Using logInfo here causes the syntax to be rendered via the pretty printer.
  logInfo stx

#eval ex3 4
```
```leanOutput ex3
#[0, 1, 2, 3]
```
::::
:::::

:::::keepEnv
:::comment
::example "Non-Comma Separators"
:::
::::example "カンマではない区切り文字"
:::comment
The following unconventional syntax for lists separates numeric elements by either em dashes or double asterisks, rather than by commas.
:::

以下のリスト用の型破りな構文は、数値要素をカンマで区切るのではなく、em ダッシュまたは2つのアスタリスクで区切ります。

```lean
syntax "⟦" sepBy1(num, " — ") "⟧": term
syntax "⟦" sepBy1(num, " ** ") "⟧": term
```
:::comment
This means that `—*` and `***` are valid splice suffixes between the `⟦` and `⟧` atoms.
In the case of `***`, the first two asterisks are the atom in the syntax rule, while the third is the repetition suffix.
:::

これは `—*` と `***` がアトム `⟦` と `⟧` の間の有効なスプライス接尾辞であることを意味します。`***` の場合、最初の2つのアスタリスクは構文規則のアトムで、3つ目は反復の接尾辞になります。

```lean
macro_rules
  | `(⟦$n:num—*⟧) => `(⟦$n***⟧)
  | `(⟦$n:num***⟧) => `([$n,*])
```
```lean (name := nonComma)
#eval ⟦1 — 2 — 3⟧
```
```leanOutput nonComma
[1, 2, 3]
```
::::
:::::

:::::keepEnv
:::comment
::example "Optional Splices"
:::
::::example "オプショナルなスプライス"
:::comment
The following syntax declaration optionally matches a term between two tokens.
The parentheses around the nested `term` are needed because `term?` is a valid identifier.
:::

以下の構文宣言は、2つのトークンの間にある項にオプション的にマッチします。入れ子になった `term` を括弧で囲む必要があるのは、 `term?` が有効な識別子だからです。

```lean (show := false)
open Lean
```
```lean
syntax "⟨| " (term)? " |⟩": term
```

:::comment
The `?` splice suffix for a term expects an {lean}`Option Term`:
:::

項のスプライス接尾辞 `?` は {lean}`Option Term` を期待します：

```lean
def mkStx [Monad m] [MonadQuotation m] (e) : m Term :=
  `(⟨| $(e)? |⟩)
```
```lean (name := checkMkStx)
#check mkStx
```
```leanOutput checkMkStx
mkStx {m : Type → Type} [Monad m] [MonadQuotation m] (e : Option (TSyntax `term)) : m Term
```

:::comment
Supplying {name}`some` results in the optional term being present.
:::

{name}`some` を指定すると、オプショナルな項が存在することになります。

```lean (name := someMkStx)
#eval do logInfo (← mkStx (some (quote 5)))
```
```leanOutput someMkStx
⟨| 5 |⟩
```

:::comment
Supplying {name}`none` results in the optional term being absent.
:::

{name}`none` を指定すると、オプショナルな項が存在s内ことになります。

```lean (name := noneMkStx)
#eval do logInfo (← mkStx none))
```
```leanOutput noneMkStx
⟨| |⟩
```

::::
:::::

```lean (show := false)
section
open Lean Syntax
variable {k k' : SyntaxNodeKinds} {sep : String} [Coe (TSyntax k) (TSyntax k')]
-- Demonstrate the coercions between different kinds of repeated syntax

/-- info: instCoeHTCTOfCoeHTC -/
#guard_msgs in
#synth CoeHTCT (TSyntaxArray k) (TSepArray k sep)

/-- info: instCoeHTCTOfCoeHTC -/
#guard_msgs in
#synth CoeHTCT (TSyntaxArray k) (TSepArray k' sep)

/-- info: instCoeHTCTOfCoeHTC -/
#guard_msgs in
#synth CoeHTCT (Array (TSyntax k)) (TSepArray k sep)

/-- info: instCoeHTCTOfCoeHTC -/
#guard_msgs in
#synth CoeHTCT (TSepArray k sep) (TSyntaxArray k)

end
```

:::comment
### Token Antiquotations
:::

### トークンの antiquotation（Token Antiquotations）

%%%
tag := "token-antiquotations"
%%%

:::comment
In addition to antiquotations of complete syntax, Lean features {deftech}_token antiquotations_ which allow the source information of an atom to be replaced with the source information from some other syntax.
This is primarily useful to control the placement of error messages or other information that Lean reports to users.
A token antiquotation does not allow an arbitrary atom to be inserted via evaluation.
A token antiquotation consists of an atom (that is, a keyword)

:::

完全な構文の antiquotation に加えて、Lean は {deftech}_トークンの antiquotation_ （token antiquotation）を備えています。これはアトムのソース情報を他の構文のソース情報に置き換えることができます。これは主に、Lean がユーザに報告するエラーメッセージやその他の情報の配置を制御するのに便利です。トークンの antiquotation では、評価によって任意のアトムを挿入することはできません。トークンの antiquotation はアトム（つまりキーワード）から構成されます。

::::freeSyntax antiquot (open := true) (title := "Token Antiquotations")
:::comment
Token antiquotations replace the source information (of type {name Lean.SourceInfo}`SourceInfo`) on a token with the source information from some other syntax.

:::

トークンの antiquotation はトークンのソース情報（ {name Lean.SourceInfo}`SourceInfo` 型）を他の構文のソース情報に置き換えます。

```grammar
atom"%$"ident
```
::::


::: TODO

More complex splices with brackets

:::

:::comment
## Matching Syntax
:::

## 構文のマッチ（Matching Syntax）

%%%
tag := "quote-patterns"
%%%

:::comment
Quasiquotations can be used in pattern matching to recognize syntax that matches a template.
Just as antiquotations in a quotation that's used as a term are regions that are treated as ordinary non-quoted expressions, antiquotations in patterns are regions that are treated as ordinary Lean patterns.
Quote patterns are compiled differently from other patterns, so they can't be intermixed with non-quote patterns in a single {keywordOf Lean.Parser.Term.match}`match` expression.
Like ordinary quotations, quote patterns are first processed by Lean's parser.
The parser's output is then compiled into code that determines whether there is a match.
Syntax matching assumes that the syntax being matched was produced by Lean's parser, either via quotation or directly in user code, and uses this to omit some checks.
For example, if nothing but a particular keyword can be present in a given position, the check may be omitted.

:::

quasiquotation はテンプレートにマッチする構文を認識するためのパターンマッチで使用することができます。項として使用される quotation の中の antiquotation が通常の非 quote 式として扱われる領域であるのと同じように、パターンの中の antiquotation の領域は通常の Lean のパターンとして扱われます。quote パターンは他のパターンとは異なる方法でコンパイルされるため、1つの {keywordOf Lean.Parser.Term.match}`match` 式の中に quote パターン以外のパターンを混在させることはできません。通常の quotation と同様に、quote パターンはまず Lean のパーサによって処理されます。そしてパーサの出力はマッチするかどうかを判断するコードにコンパイルされます。構文マッチは、マッチする構文が Lean のパーサによって quotation を経由・または直接ユーザコードで生成されたものであると仮定し、いくつかのチェックを省略するためにこれを使用します。例えば、ある位置に特定のキーワード以外が存在しない場合、そのチェックは省略されます。

:::comment
Syntax matches a quote pattern in the following cases:


:::

構文は以下の場合に quote パターンにマッチします：

:::comment
 : Atoms

  Keyword atoms (such as {keywordOf termIfThenElse}`if` or {keywordOf Lean.Parser.Term.match}`match`) result in singleton nodes whose kind is `token.` followed by the atom.
  In many cases, it is not necessary to check for specific atom values because the grammar allows only a single keyword, and no checking will be performed.
  If the syntax of the term being matched requires the check, then the node kind is compared.

  Literals, such as string or numeric literals, are compared via their underlying string representation.
  The pattern `` `(0x15) `` and the quotation `` `(21) `` do not match.

:::

 : アトム

  キーワードアトム（ {keywordOf termIfThenElse}`if` や {keywordOf Lean.Parser.Term.match}`match` など）は `token.` の後にアトムが続く、子を1つだけ持つノードとなります。多くの場合、文法は単一のキーワードしか許さないため、特定のアトムの値をチェックする必要はなく、チェックは行われません。マッチする語の構文がチェックを必要とする場合は、ノードの種別を比較します。

  文字列や数値リテラルなどのリテラルは、その文字列表現によって比較されます。パターン ``​`(0x15)`` と quotation ``​`(21)`` はマッチしません。

:::comment
 : Nodes

  If both the pattern and the value being matched represent {name}`Syntax.node`, there is a match when both have the same syntax kind, the same number of children, and each child pattern matches the corresponding child value.

:::

 : ノード

  マッチするパターンと値の両方が {name}`Syntax.node` を表す場合、両方が同じ構文種別・同じ数の子を持ち、それぞれの子のパターンが対応する子の値にマッチする時にマッチします。

:::comment
 : Identifiers

  If both the pattern and the value being matched are identifiers, then their literal {name Lean.Name}`Name` values are compared for equality modulo macro scopes.
  Identifiers that “look” the same match, and it does not matter if they refer to the same binding.
  This design choice allows quote pattern matching to be used in contexts that don't have access to a compile-time environment in which names can be compared by reference.


:::

 : 識別子

  パターンとマッチする値の両方が識別子の場合、そのリテラル {name Lean.Name}`Name` の値はマクロスコープで等しいかどうか比較されます。同じように「見える」識別子はマッチし、それらが同じ束縛子を参照しているかどうかは問題になりません。この設計上の選択により、名前を参照で比較できるコンパイル時の環境に対してアクセスできないコンテキストでも quote パターンマッチを使用できるようになります。

:::comment
Because quotation pattern matching is based on the node kinds emitted by the parser, quotations that look identical may not match if they come from different syntax categories.
If in doubt, including the syntax category in the quotation can help.

:::

quotation のパターンマッチはパーサが出力するノードの種別に基づいて行われるため、同じように見える quotation でも構文カテゴリが異なるとマッチしないことがあります。疑わしい場合は、quotation に構文カテゴリを含めると良いでしょう。

:::comment
## Defining Macros
:::

## マクロの定義（Defining Macros）

%%%
tag := "defining-macros"
%%%


:::comment
There are two primary ways to define macros: the {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command and the {keywordOf Lean.Parser.Command.macro}`macro` command.
The {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command associates a macro with existing syntax, while the {keywordOf Lean.Parser.Command.macro}`macro` command simultaneously defines new syntax and a macro that translates it to existing syntax.
The {keywordOf Lean.Parser.Command.macro}`macro` command can be seen as a generalization of {keywordOf Lean.Parser.Command.notation}`notation` that allows the expansion to be generated programmatically, rather than simply by substitution.

:::

マクロを定義するには主に2つの方法があります： {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` コマンドと {keywordOf Lean.Parser.Command.macro}`macro` コマンドです。 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` コマンドは既存の構文にマクロを関連付けますが、 {keywordOf Lean.Parser.Command.macro}`macro` コマンドは新しい構文とそれを既存の構文に変換するマクロを同時に定義します。 {keywordOf Lean.Parser.Command.macro}`macro` コマンドは {keywordOf Lean.Parser.Command.notation}`notation` を一般化したものと見なすことができます。これは単純に置換するのではなく、プログラム的に生成された展開を許可するものです。

:::comment
### The `macro_rules` Command
:::

### `macro_rules` コマンド（The `macro_rules` Command）

%%%
tag := "macro_rules"
%%%

::::syntax command

:::comment
The {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command takes a sequence of rewrite rules, specified as syntax pattern matches, and adds each as a macro.
The rules are attempted in order, before previously-defined macros, and later macro definitions may add further macro rules.

:::

{keywordOf Lean.Parser.Command.macro_rules}`macro_rules` コマンドは、構文のパターンマッチとして指定された一連の書き換えルールを受け取り、それぞれをマクロとして追加します。ルールは以前に定義されたマクロの前に順番に試行され、後のマクロ定義でさらにマクロルールを追加することができます。

```grammar
$[$d:docComment]?
$[@[$attrs,*]]?
$_:attrKind macro_rules $[(kind := $k)]?
  $[| `(free{(p:ident"|")?/-- Suitable syntax for {p} -/}) => $e]*
```
::::

:::comment
The patterns in the macros must be quotation patterns.
They may match syntax from any syntax category, but a given pattern can only ever match a single syntax kind.
If no category or parser is specified for the quotation, then it may match terms or (sequences of) commands, but never both.
In case of ambiguity, the term parser is chosen.

:::

マクロのパターンは quotation パターンでなければなりません。これらはどの構文カテゴリの構文にもマッチしますが、1つのパターンがマッチするのは1つの構文種別だけです。quotation にカテゴリやパーサが指定されていない場合、それは項かコマンド（の列）にマッチしますが、両方にマッチすることはありません。あいまいな場合は、項のパーサが選択されます。

:::comment
Internally, macros are tracked in a table that maps each {tech}[syntax kind] to its macros.
The {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command may be explicitly annotated with a syntax kind.

:::

内部的には、マクロは各 {tech}[構文種別] をそのマクロに対応付けるテーブルで追跡されます。 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` コマンドは構文種別を明示的に注釈することができます。

:::comment
If a syntax kind is explicitly provided, the macro definition checks that each quotation pattern has that kind.
If the parse result for the quotation was a {tech}[choice node] (that is, if the parse was ambiguous), then the pattern is duplicated once for each alternative with the specified kind.
It is an error if none of the alternatives have the specified kind.

:::

構文種別が明示的に指定されている場合、マクロ定義は各 quotation パターンがその種別を持つかどうかをチェックします。quotation のパース結果が {tech}[choice node] であった場合（つまりパースが曖昧であった場合）、指定された種別を持つ各選択肢に対してパターンが1回複製されます。指定された種別を持つ選択肢が1つも無い場合はエラーとなります。

:::comment
If no kind is provided explicitly, then the kind determined by the parser is used for each pattern.
The patterns are not required to all have the same syntax kind; macros are defined for each syntax kind used by at least one of the patterns.
It is an error if the parse result for a quotation pattern was a {tech}[choice node] (that is, if the parse was ambiguous).

:::

種別を明示的に指定しない場合、パーサが決定した種別が各パターンに使用されます。パターンがすべて同じ構文種別を持つ必要はありません；少なくとも1つのパターンで使用される構文種別ごとにマクロが定義されます。quotation パターンのパース結果が {tech}[choice node] であった場合（つまりパース結果が曖昧であった場合）はエラーとなります。

:::comment
The documentation comment associated with {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` is displayed to users if the syntax itself has no documentation comment.
Otherwise, the documentation comment for the syntax itself is shown.

:::

構文自体にドキュメントコメントが無い場合、 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` に関連付けられたドキュメントコメントがユーザに表示されます。そうでない場合は、構文自体のドキュメントコメントが表示されます。

:::comment
As with {ref "notations"}[notations] and {ref "operators"}[operators], macro rules may be declared `scoped` or `local`.
Scoped macros are only active when the current namespace is open, and local macro rules are only active in the current {tech}[section scope].

:::

{ref "notations"}[notations] と {ref "operators"}[operators] と同様に、マクロ規則も `scoped` や `local` として宣言することができます。スコープ付きマクロは現在の名前空間が開いているときにのみ有効であり、ローカルなマクロ規則は現在の {tech}[セクションスコープ] においてのみ有効です。

:::::keepEnv
::::example "Idiom Brackets"
:::comment
Idiom brackets are an alternative syntax for working with applicative functors.
If the idiom brackets contain a function application, then the function is wrapped in {name}`pure` and applied to each argument using `<*>`. {TODO}[Operator hyperlinking to docs]
Lean does not support idiom brackets by default, but they can be defined using a macro.
:::

idiom bracket はアプリカティブ関手を扱うための代替構文です。idiom bracket に関数適用が含まれている場合、関数は {name}`pure` でラップされ、`<*>` を使って各引数に適用されます。Lean はデフォルトでは idiom bracket をサポートしていませんが、マクロを使って定義することができます。

```lean
syntax (name := idiom) "⟦" (term:arg)+ "⟧" : term

macro_rules
  | `(⟦$f $args*⟧) => do
    let mut out ← `(pure $f)
    for arg in args do
      out ← `($out <*> $arg)
    return out
```

:::comment
This new syntax can be used immediately.
:::

この新しい構文は直ちに使うことができます。

```lean
def addFirstThird [Add α] (xs : List α) : Option α :=
  ⟦Add.add xs[0]? xs[2]?⟧
```
```lean (name := idiom1)
#eval addFirstThird (α := Nat) []
```
```leanOutput idiom1
none
```
```lean (name := idiom2)
#eval addFirstThird [1]
```
```leanOutput idiom2
none
```
```lean (name := idiom3)
#eval addFirstThird [1,2,3,4]
```
```leanOutput idiom3
some 4
```
::::
:::::

:::::keepEnv
:::comment
::example "Scoped Macros"
:::
::::example "スコープ付きマクロ"
:::comment
Scoped macro rules are active only in their namespace.
When the namespace `ConfusingNumbers` is open, numeric literals will be assigned an incorrect meaning.
:::

スコープ付きマクロ規則はその名前空間でのみ有効です。名前空間 `ConfusingNumbers` が開いている場合、数値リテラルは正しくない意味になります。

````lean
namespace ConfusingNumbers
````

:::comment
The following macro recognizes terms that are odd numeric literals, and replaces them with double their value.
If it unconditionally replaced them with double their value, then macro expansion would become an infinite loop because the same rule would always match the output.

:::

以下のマクロは奇数の数値リテラルである項を認識し、その値を2倍したものに置き換えます。もし無条件に2倍に置き換えてしまうと、同じ規則が必ず出力にマッチしてしまうため、マクロ展開は無限ループになってしまいます。

```lean
scoped macro_rules
  | `($n:num) => do
    if n.getNat % 2 = 0 then Lean.Macro.throwUnsupported
    let n' := (n.getNat * 2)
    `($(Syntax.mkNumLit (info := n.raw.getHeadInfo) (toString n')))
```

:::comment
Once the namespace ends, the macro is no longer used.
:::

名前空間が閉じられると、このマクロはもはや使うことができません。

````lean
end ConfusingNumbers
````

:::comment
Without opening the namespace, numeric literals function in the usual way.
:::

名前空間を開かない場合、数値リテラルは通常通り機能します。

```lean (name := nums1)
#eval (3, 4)
```
```leanOutput nums1
(3, 4)
```

:::comment
When the namespace is open, the macro replaces {lean}`3` with {lean}`6`.
:::

名前空間が開かれると、マクロは {lean}`3` を {lean}`6` に置き換えます。

```lean (name := nums2)
open ConfusingNumbers

#eval (3, 4)
```
```leanOutput nums2
(6, 4)
```

:::comment
It is not typically useful to change the interpretation of numeric or other literals in macros.
However, scoped macros can be very useful when adding new rules to extensible tactics such as {tactic}`trivial` that work well with the contents of the namespaces but should not always be used.
:::

数値リテラルやその他のリテラルの解釈をマクロで変更することは通常は有用ではありません。しかし、スコープ付きマクロは、 {tactic}`trivial` のような拡張可能なタクティクに新しい規則を追加する時に非常に便利です。

::::
:::::

:::comment
Behind the scenes, a {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command generates one macro function for each syntax kind that is matched in its quote patterns.
This function has a default case that throws the {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` exception, so further macros may be attempted.


:::

裏側では、 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` コマンドが quote パターンでマッチした構文種別ごとに1つのマクロ関数を生成します。この関数にはデフォルトケースとして {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 例外を投げるケースを持つため、追加のマクロを試行することが可能です。

:::comment
A single {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command with two rules is not always equivalent to two separate single-match commands.
First, the rules in a {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` are tried from top to bottom, but recently-declared macros are attempted first, so the order would need to be reversed.
Additionally, if an earlier rule in the macro throws the {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` exception, then the later rules are not tried; if they were instead in separate {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` commands, then they would be attempted.

:::

2つの規則を持つ単一の {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` コマンドは、必ずしも2つの単一ケースにマッチするコマンドと同じとは限りません。まず、 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` の規則は上から下に試行されますが、直近で宣言されたマクロが最初に試行されるため、同じ挙動にするには順序を逆にする必要があります。さらに、マクロ内の以前の規則が {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 例外を投げた場合、それ以降の規則は試されません；規則が別々の {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` コマンドであった場合は試行されます。

:::comment
::example "One vs. Two Sets of Macro Rules"
:::
:::::example "1つ vs 2つのマクロ規則"

```lean (show := false)
open Lean.Macro
```

:::comment
The `arbitrary!` macro is intended to expand to some arbitrarily-determined value of a given type.

:::

`arbitrary!` マクロは与えられた型に対して任意に決定される値を展開することを意図しています。

```lean
syntax (name := arbitrary!) "arbitrary!" term:arg : term
```

::::keepEnv
```lean
macro_rules
  | `(arbitrary! ()) => `(())
  | `(arbitrary! Nat) => `(42)
  | `(arbitrary! ($t1 × $t2)) => `((arbitrary! $t1, arbitrary! $t2))
  | `(arbitrary! Nat) => `(0)
```

:::comment
Users may extend it by defining further sets of macro rules, such as this rule for {lean}`Empty` that fails:
:::

ユーザはさらにマクロ規則を定義することでこれを拡張できます。例えばこの {lean}`Empty` に対する規則は失敗します：

```lean
macro_rules
  | `(arbitrary! Empty) => throwUnsupported
```

```lean (name := arb1)
#eval arbitrary! (Nat × Nat)
```
```leanOutput arb1
(42, 42)
```
::::

::::keepEnv
:::comment
If all of the macro rules had been defined as individual cases, then the result would have instead used the later case for {lean}`Nat`.
This is because the rules in a single {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command are checked from top to bottom, but more recently-defined {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` commands take precedence over earlier ones.

:::

すべてのマクロ規則が個別のケースとして定義されていた場合、上記は {lean}`Nat` の後に定義されたケースを使用したことでしょう。これは1つの {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` コマンドの規則は上から下にチェックされますが、より最近定義された {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` コマンドがより前のものより優先されるためです。

```lean
macro_rules
  | `(arbitrary! ()) => `(())
macro_rules
  | `(arbitrary! Nat) => `(42)
macro_rules
  | `(arbitrary! ($t1 × $t2)) => `((arbitrary! $t1, arbitrary! $t2))
macro_rules
  | `(arbitrary! Nat) => `(0)
macro_rules
  | `(arbitrary! Empty) => throwUnsupported
```

```lean (name := arb2)
#eval arbitrary! (Nat × Nat)
```
```leanOutput arb2
(0, 0)
```
::::

:::comment
Additionally, if any rule throws the {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` exception, no further rules in that command are checked.
:::

さらに、いずれかの規則が {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 例外を投げた場合、そのコマンド内のそれ以降の規則はチェックされません。

```lean
macro_rules
  | `(arbitrary! Nat) => throwUnsupported
  | `(arbitrary! Nat) => `(42)

macro_rules
  | `(arbitrary! Int) => `(42)
macro_rules
  | `(arbitrary! Int) => throwUnsupported
```

:::comment
The case for {lean}`Nat` fails to elaborate, because macro expansion did not translate the {keywordOf arbitrary!}`arbitrary!` syntax into something supported by the elaborator.
:::

{lean}`Nat` のケースはマクロ展開が {keywordOf arbitrary!}`arbitrary!` 構文をエラボレータにサポートされるものに変換しないため、エラボレートに失敗します。

```lean (name := arb3) (error := true)
#eval arbitrary! Nat
```
```leanOutput arb3
elaboration function for 'arbitrary!' has not been implemented
  arbitrary! Nat
```

:::comment
The case for {lean}`Int` succeeds, because the first set of macro rules are attempted after the second throws the exception.
:::

{lean}`Int` のケースでは、2番目の例外を投げるものが試行された後に1番目のマクロ規則が試行されるため成功します。

```lean (name := arb4)
#eval arbitrary! Int
```
```leanOutput arb4
42
```
:::::


:::comment
### The `macro` Command
:::

### `macro` コマンド（The `macro` Command）

%%%
tag := "macro-command"
%%%

```lean (show := false)
section
open Lean
```

:::comment
The {keywordOf Lean.Parser.Command.macro}`macro` command simultaneously defines a new {tech}[syntax rule] and associates it with a {tech}[macro].
Unlike {keywordOf Lean.Parser.Command.notation}`notation`, which can define only new term syntax and in which the expansion is a term into which the parameters are to be substituted, the {keywordOf Lean.Parser.Command.macro}`macro` command may define syntax in any {tech}[syntax category] and it may use arbitrary code in the {name}`MacroM` monad to generate the expansion.
Because macros are so much more flexible than notations, Lean cannot automatically generate an unexpander; this means that new syntax implemented via the {keywordOf Lean.Parser.Command.macro}`macro` command is available for use in _input_ to Lean, but Lean's output does not use it without further work.

:::

{keywordOf Lean.Parser.Command.macro}`macro` コマンドは新しい {tech}[構文規則] の定義とそれを {tech}[マクロ] に関連付けることを同時に行います。 {keywordOf Lean.Parser.Command.notation}`notation` コマンドが新しい項の構文のみを定義でき、展開がパラメータを代入する項であるのとは異なり、 {keywordOf Lean.Parser.Command.macro}`macro` コマンドは任意の {tech}[構文カテゴリ] の構文を定義でき、展開の生成に {name}`MacroM` モナドの任意のコードを使用できます。マクロは記法よりはるかに柔軟であるため、Lean は自動的に unexpander を生成することができません；つまり、 {keywordOf Lean.Parser.Command.macro}`macro` コマンドで実装された新しい構文は、Lean への _入力_ で使用できますが、Lean の出力で用いるにはさらなる作業を行わないといけません。

:::syntax command
```grammar
$[$_:docComment]?
$[@[$attrs,*]]?
$_:attrKind macro$[:$p]? $[(name := $_)]? $[(priority := $_)]? $xs:macroArg* : $k:ident =>
  $tm
```
:::

::::syntax Lean.Parser.Command.macroArg (open := false)
:::comment
A macro's arguments are either syntax items (as used in the {keywordOf Lean.Parser.Command.syntax}`syntax` command) or syntax items with attached names.
:::

マクロの引数は構文アイテム（ {keywordOf Lean.Parser.Command.syntax}`syntax` コマンドで使われるもの）か、名前が付加された構文アイテムです。

```grammar
$s:stx
```
```grammar
$x:ident:$stx
```
::::

:::comment
In the expansion, the names that are attached to syntax items are bound; they have type {name Lean.TSyntax}`TSyntax` for the appropriate syntax kinds.
If the syntax matched by the parser does not have a defined kind (e.g. because the name is applied to a complex specification), then the type is {lean}`TSyntax Name.anonymous`.

:::

展開では、構文アイテムに付けられる名前は束縛されます；これは適切な構文種別に対して {name Lean.TSyntax}`TSyntax` 型を持ちます。パーサによってマッチされた構文が定義された種別を持たない場合（例えば名前が複雑な仕様に適用されるためなど）、型は {lean}`TSyntax Name.anonymous` となります。

```lean (show := false) (keep := false)
-- Check the typing rules
open Lean Elab Term Macro Meta

elab "dbg_type " e:term ";" body:term : term => do
  let e' ← elabTerm e none
  let t ← inferType e'
  logInfoAt e t
  elabTerm body none

/--
info: TSyntax `str
---
info: TSyntax Name.anonymous
---
info: Syntax.TSepArray `num ","
-/
#guard_msgs in
macro "gah!" thing:str other:(str <|> num) arg:num,* : term => do
  dbg_type thing; pure ()
  dbg_type other; pure ()
  dbg_type arg; pure ()
  return quote s!"{thing.raw} ||| {other.raw} ||| {arg.getElems}"

/-- info: "(str \"\\\"one\\\"\") ||| (num \"44\") ||| #[(num \"2\"), (num \"3\")]" : String -/
#guard_msgs in
#check gah! "one" 44 2,3

```

:::comment
The documentation comment is associated with the new syntax, and the attribute kind (none, `local`, or `scoped`) governs the visibility of the macro just as it does for notations: `scoped` macros are available in the namespace in which they are defined or in any {tech}[section scope] that opens that namespace, while `local` macros are available only in the local section scope.

:::

ドキュメントコメントは新しい構文に関連付けられ、属性の種類（無し・`local`・`scoped`）は記法の場合と同じようにマクロの可視性を制御します：`scoped` なマクロは定義されている名前空間か、その名前空間を開いている {tech}[セクションスコープ] で、`local` マクロはローカルのセクションスコープでのみ利用可能です。

:::comment
Behind the scenes, the {keywordOf Lean.Parser.Command.macro}`macro` command is itself implemented by a macro that expands it to a {keywordOf Lean.Parser.Command.syntax}`syntax` command and a {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command.
Any attributes applied to the macro command are applied to the syntax definition, but not to the {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command.

:::

裏側では、 {keywordOf Lean.Parser.Command.macro}`macro` コマンドは、 {keywordOf Lean.Parser.Command.syntax}`syntax` コマンドと {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` コマンドに展開するようなマクロとして実装されています。マクロコマンドに展開される属性は構文定義に適用されますが、 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` コマンドには適用されません。

```lean (show := false)
end
```

:::comment
### The Macro Attribute
:::

### マクロ属性（The Macro Attribute）

%%%
tag := "macro-attribute"
%%%

:::comment
{tech}[Macros] can be manually added to a syntax kind using the {keywordOf Lean.Parser.Attr.macro}`macro` attribute.
This low-level means of specifying macros is typically not useful, except as a result of code generation by macros that themselves generate macro definitions.

:::

{tech}[マクロ] は {keywordOf Lean.Parser.Attr.macro}`macro` 属性を使用して構文種別に手動で追加を行うことができます。マクロを指定するこの低レベルな手段は、それ自身がマクロ定義を生成するマクロによるコード生成の結果である場合を除いて通常は有用ではありません。

::::syntax attr label:="attribute"
:::comment
The {keywordOf Lean.Parser.Attr.macro}`macro` attribute specifies that a function is to be considered a {tech}[macro] for the specified syntax kind.
:::

{keywordOf Lean.Parser.Attr.macro}`macro` 属性は指定された構文種別に対して {tech}[マクロ] と見なされる関数を指定します。

```grammar
macro $_:ident
```
::::

:::::keepEnv
:::comment
::example "The Macro Attribute"
:::
::::example "マクロ属性"
```lean (show := false)
open Lean Macro
```
```lean
/-- Generate a list based on N syntactic copies of a term -/
syntax (name := rep) "[" num " !!! " term "]" : term

@[macro rep]
def expandRep : Macro
  | `([ $n:num !!! $e:term]) =>
    let e' := Array.mkArray n.getNat e
    `([$e',*])
  | _ =>
    throwUnsupported
```

:::comment
Evaluating this new expression demonstrates that the macro is present.
:::

この新しい式を評価すると、マクロが存在することがわかります。

```lean (name := attrEx1)
#eval [3 !!! "hello"]
```
```leanOutput attrEx1
["hello", "hello", "hello"]
```
::::
:::::


# Elaborators
%%%
tag := "elaborators"
%%%

:::planned 72
For now, a quick overview of term and command elaborators, with a detailed description to be written in a later revision.
:::
