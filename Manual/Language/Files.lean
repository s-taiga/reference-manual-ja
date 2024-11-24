/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

/-
#doc (Manual) "Files" =>
-/
#doc (Manual) "ファイル（Files）" =>
%%%
tag := "files"
%%%

:::comment
The smallest unit of compilation in Lean is a single {deftech}[module].
Modules correspond to source files, and are imported into other modules based on their filenames.
In other words, the names and folder structures of files are significant in Lean code.
:::

Lean におけるコンパイルの最小単位は1つの {deftech key:="module"}[モジュール] （module）です。モジュールはソースファイルに対応し、ファイル名に基づいて他のモジュールにインポートされます。言い換えれば、Lean コードではファイルの名前とフォルダ構造が重要です。

:::comment
# Modules
:::

# モジュール（Modules）
%%%
tag := "modules"
%%%

:::comment
Every Lean file defines a module.
A module's name is derived from a combination of its filename and the way in which Lean was invoked: Lean has a _root directory_ in which it expects to find code, and the module's name is the names of the directories from the root to the filename, with dots (`.`) interspersed and `.lean` removed.
For example, if Lean is invoked with `Projects/MyLib/src` as its root, the file `Projects/MyLib/src/Literature/Novel/SciFi.lean` would contain a module named `Literature.Novel.SciFi`.
:::

すべての Lean ファイルはモジュールを定義します。モジュールの名前はファイル名と Lean の起動方法の組み合わせで決まります：Lean はコードを見つけることを期待する _ルートディレクトリ_ （root directory）を持っており、モジュールの名前はルートからファイル名までのディレクトリの名前にドット（`.`）を散りばめ、`.lean` を取り除いたものです。例えば、Lean が `Projects/MyLib/src` をルートとして起動された場合、`Projects/MyLib/src/Literature/Novel/SciFi.lean` というファイルには `Literature.Novel.SciFi` という名前のモジュールが含まれます。

::: TODO
Describe case sensitivity/preservation for filenames here
:::

:::comment
## Encoding and Representation
:::

## エンコードと表現（Encoding and Representation）
%%%
tag := "module-encoding"
%%%

:::comment
Lean modules are Unicode text files encoded in UTF-8. {TODO}[Figure out the status of BOM and Lean]
Lines may end either with newline characters (`"\n"`, Unicode `'LINE FEED (LF)' (U+000A)`) or with a form feed and newline sequence (`"\r\n"`, Unicode `'CARRIAGE RETURN (CR)' (U+000D)` followed by `'LINE FEED (LF)' (U+000A)`).
However, Lean normalizes line endings when parsing or comparing files, so all files are compared as if all their line endings are `"\n"`.
:::

Lean モジュールは UTF-8 でエンコードされた Unicode テキストファイルです。行の終わりは改行文字（`"\n"`、Unicode `'LINE FEED (LF)' (U+000A)`）か、改ページと改行の連なり（`"\r\n"`、Unicode `'CARRIAGE RETURN (CR)' (U+000D)` followed by `'LINE FEED (LF)' (U+000A)`）のどちらかです。しかし、Lean はファイルを解析したり比較したりするときに行末を正規化するため、すべてのファイルはあたかもすべての行末が `"\n"` であるかのように比較されます。

::: TODO
Marginal note: this is to make cached files and `#guard_msgs` and the like work even when git changes line endings. Also keeps offsets stored in parsed syntax objects consistent.
:::

:::comment
## Concrete Syntax

:::

## 具体的な構文（Concrete Syntax）
%%%
tag := "module-syntax"
%%%

:::comment
Lean's concrete syntax is extensible.
In a language like Lean, it's not possible to completely describe the syntax once and for all, because libraries may define syntax in addition to new constants or {tech}[inductive types].
Rather than completely describing the language here, the overall framework is described, while the syntax of each language construct is documented in the section to which it belongs.
:::

Lean の具体的な構文は拡張可能です。Lean のような言語では、新しい定数やデータ型に加えて、ライブラリが構文を定義する可能性があるため、構文を完全に記述することはできません。ここでは言語を完全に説明するのではなく、全体的な枠組みを説明し、言語を構成するそれぞれの構文は、それが属する節で説明します。

:::comment
### Whitespace

:::

### 空白（Whitespace）
%%%
tag := "whitespace"
%%%

:::comment
Tokens in Lean may be separated by any number of {deftech}[_whitespace_] character sequences.
Whitespace may be a space (`" "`, Unicode `'SPACE (SP)' (U+0020)`), a valid newline sequence, or a comment. {TODO}[xref]
Neither tab characters nor carriage returns not followed by newlines are valid whitespace sequences.
:::

Lean における字句は {deftech}[_空白_] （whitespace）文字の列でいくつでも区切ることができます。空白はスペース（`" "`、Unicode `'SPACE (SP)' (U+0020)`）・有効な改行の列・もしくはコメントです。タブ文字と改行が続かない CR はどちらも有効な空白列ではありません。

:::comment
### Comments

:::

### コメント（Comments）
%%%
tag := "comments"
%%%

:::comment
Comments are stretches of the file that, despite not being whitespace, are treated as such.
Lean has two syntaxes for comments:
:::

コメントは空白でないにもかかわらず、そのように扱われるのはファイルの伸縮性です。Lean には2つのコメントについての構文があります：

:::comment
: Line comments

  A `--` that does not occur as part of a token begins a _line comment_. All characters from the initial `-` to the newline are treated as whitespace.{index (subterm := "line")}[comment]
:::

: 行コメント

  字句の一部として出現しない `--` は _行コメント_ を開始します。最初の `-` から改行までのすべての文字は空白として扱われます。 {index (subterm := "line")}[comment]

:::comment
: Block comments

  A `/-` that does not occur as part of a token and is not immediately followed by a `-` character begins a _block comment_.{index (subterm := "block")}[comment]
  The block comment continues until a terminating `-/` is found.
  Block comments may be nested; a `-/` only terminates the comment if prior nested block comment openers `/-` have been terminated by a matching `-/`.

:::

: ブロックコメント

  直後に `-` が続かず、字句の一部として出現しない `/-` は _ブロックコメント_ を開始します。 {index (subterm := "block")}[comment] ブロックコメントは終了する `-/` が見つかるまで続きます。ブロックコメントは入れ子にすることができます；`-/` はそれ以前に入れ子になっていたブロックコメントを開く `/-` がマッチする `-/` によって終了していた場合にのみコメントを終了します。

:::comment
`/--` and `/-!` begin {deftech}_documentation_ {TODO}[xref] rather than comments, which are also terminated with `-/` and may contain nested block comments.
Even though documentation resembles comments, they are their own syntactic category; their valid placement is determined by Lean's grammar.


:::

`/--` と `/-!` はコメントではなく {deftech}_ドキュメント_ （documentation）を開始します。これらも `-/` で終了し、入れ子のブロックコメントを含むことができます。ドキュメントはコメントに似ていますが、それ自体が構文のカテゴリです；これらの有効な配置は Lean の文法によって決定されます。

:::comment
### Keywords and Identifiers
:::

### キーワードと識別子（Keywords and Identifiers）
%%%
tag := "keywords-and-identifiers"
%%%

:::comment
An {tech}[identifier] consists of one or more identifier components, separated by `'.'`.{index}[identifier]
:::

{tech}[identifier] は `'.'` 区切りで1つ以上の識別子要素から構成されます。 {index}[identifier]

:::comment
{deftech}[Identifier components] consist of a letter or letter-like character or an underscore (`'_'`), followed by zero or more identifier continuation characters.
Letters are English letters, upper- or lowercase, and the letter-like characters include a range of non-English alphabetic scripts, including the Greek script which is widely used in Lean, as well as the members of the Unicode letter-like symbol block, which contains a number of double-struck characters (including `ℕ` and `ℤ`) and abbreviations.
Identifier continuation characters consist of letters, letter-like characters, underscores (`'_'`), exclamation marks (`!`), question marks (`?`), subscripts, and single quotes (`'`).
As an exception, underscore alone is not a valid identifier.
:::

{deftech}[識別子要素] （Identifier component）は、文字・文字様文字・アンダースコア（`'_'`）とそれに続く0個以上の識別子継続文字から構築されます。文字は大文字または小文字の英語アルファベット、文字様文字には Lean で広く使用されているギリシャ文字や重ね打ち体（`ℕ` や `ℤ` を含む）や省略形を含む Unicode の文字様記号ブロックの要素など英語以外のアルファベット文字が含まれます。識別子継続文字は文字・文字様文字・アンダースコア（`'_'`）・感嘆符（`'!'`）・疑問符（`'?'`）・下付き文字・シングルクォート（`'`）から構成されます。例外として、アンダースコアのみは有効な識別子ではありません。

````lean (show := false)
def validIdentifier (str : String) : IO String :=
  Lean.Parser.identFn.test str

/-- info: "Success! Final stack:\n  `ℕ\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "ℕ"

/-- info: "Failure @0 (⟨1, 0⟩): expected identifier\nFinal stack:\n  <missing>\nRemaining: \"?\"" -/
#guard_msgs in
#eval validIdentifier "?"

/-- info: "Success! Final stack:\n  `ℕ?\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "ℕ?"

/-- info: "Failure @0 (⟨1, 0⟩): expected identifier\nFinal stack:\n  <missing>\nRemaining: \"_\"" -/
#guard_msgs in
#eval validIdentifier "_"

/-- info: "Success! Final stack:\n  `_3\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "_3"

/-- info: "Success! Final stack:\n  `_.a\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "_.a"

/-- info: "Success! Final stack:\n  `αποδεικνύοντας\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "αποδεικνύοντας"


/- Here's some things that probably should be identifiers but aren't at the time of writing -/

/-- info: "Success! Final stack:\n  `κύκ\nRemaining:\n\"λος\"" -/
#guard_msgs in
#eval validIdentifier "κύκλος"

/-- info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"øvelse\"" -/
#guard_msgs in
#eval validIdentifier "øvelse"

/--
info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"Übersetzung\""
-/
#guard_msgs in
#eval validIdentifier "Übersetzung"

/--
info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"переклад\""
-/
#guard_msgs in
#eval validIdentifier "переклад"

````

:::comment
Identifiers components may also be surrounded by double guillemets (`'«'` and `'»'`).
Such identifier components may contain any character at all aside from `'»'`, even `'«'`, `'.'`, and newlines.
The guillemets are not part of the resulting identifier component, so `«x»` and `x` denote the same identifier.
`«Nat.add»`, on the other hand, is an identifier with a single component, while `Nat.add` has two.


:::

識別子要素は二重ギュメ（`'«'` と `'»'`）で囲むこともできます。このような識別子要素には `'»'` 以外であれば `'«'` や `'.'` 、改行文字でさえも含めたどのような文字でも含めることができます。ギュメは識別子コンポーネントの一部ではないため、`«x»` と `x` は同じ識別子を表します。一方で、`«Nat.add»` は1つのコンポーネントからなる識別子であるのに対し、`Nat.add` は2つからなります。


```lean (show := false)
/-- info: "Success! Final stack:\n  `«\n  »\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "«\n»"

/-- info: "Success! Final stack:\n  `««one line\n  and another»\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "««one line\nand another»"

/-- info: "Success! Final stack:\n  `«one line\x00and another»\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "«one line\x00and another»"

/-- info: "Success! Final stack:\n  `«one line\x0band another»\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "«one line\x0Band another»"
```

:::comment
Some potential identifier components may be reserved keywords.
The specific set of reserved keywords depends on the set of active syntax extensions, which may depend on the set of imported modules and the currently-opened {TODO}[xref/deftech for namespace] namespaces; it is impossible to enumerate for Lean as a whole.
These keywords must also be quoted with guillemets to be used as identifier components in most syntactic contexts.
Contexts in which keywords may be used as identifiers without guillemets, such as constructor names in inductive types, are {deftech}_raw identifier_ contexts.{index (subterm:="raw")}[identifier]
:::

識別子要素として予約キーワードを使うことがあるかもしれません。予約キーワードの特定のセットは、アクティブな構文拡張のセットに依存し、またそれらはインポートされたモジュールと現在開いている名前空間のセットに依存するかもしれません；Lean はこれを列挙することができません。これらのキーワードはほとんどの構文で識別子の構成要素として使用するために、ギュメでクォートする必要があります。帰納型のコンストラクタ名など、キーワードをギュメなしで識別子として使用できるコンテキストは {deftech}_生識別子_ （raw identifier）コンテキストです。 {index (subterm:="raw")}[identifier]

:::comment
Identifiers that contain one or more `'.'` characters, and thus consist of more than one identifier component, are called {deftech}[hierarchical identifiers].
Hierarchical identifiers are used to represent both module names and names in a namespace.
:::

1つ以上の `'.'` 文字を含み、複数の識別子要素から構成される識別子を {deftech}[階層的識別子] （hierarchical identifier）と呼ばれます。階層的識別子はモジュールの名前と名前空間の名前の両方を表現するために用いられます。

:::comment
## Structure
:::

## 構造体（Structure）
%%%
tag := "module-structure"
%%%

::::syntax Lean.Parser.Module.module (open := false)
```grammar
$hdr:header $cmd:command*
```

:::comment
A module consists of a {deftech}_module header_ followed by a sequence of {deftech}_commands_.
:::

モジュールは {deftech}_モジュールヘッダ_ （module header）とそれに続く {deftech}_コマンド_ （command）の列から構成されます。

::::

:::comment
### Module Headers

:::

### モジュールヘッダ（Module Headers）
%%%
tag := "module-headers"
%%%

:::comment
The module header consists of a sequence of {deftech}[`import` statements].
:::

モジュールヘッダは {deftech}[`import` 文] の列から構成されます。

::::syntax Lean.Parser.Module.header (open := false)
```grammar
$i:import*
```

:::comment
An optional keyword `prelude`, for use in Lean's implementation, is also allowed:
:::

Lean の実装で使用するために、オプションのキーワードとして `prelude` も使用することができます：

```grammar
prelude $«import»*
```
::::


::::syntax Lean.Parser.Module.prelude (open := false)
```grammar
prelude
```

:::comment
The `prelude` keyword indicates that the module is part of the implementation of the Lean {deftech}_prelude_, which is the code that is available without explicitly importing any modules—it should not be used outside of Lean's implementation.
:::

`prelude` キーワードは、そのモジュールが Lean の {deftech}_prelude_ の実装の一部となることを示しています。prelude は明示的にモジュールのインポートをしなくても利用可能なコードです。このキーワードは Lean の実装外では使うべきではありません。

::::

::::syntax Lean.Parser.Module.import
```grammar
import $mod:ident
```

:::comment
Imports the module.
Importing a module makes its contents available in the current module, as well as those from modules transitively imported by its imports.
:::

モジュールのインポートについて。モジュールのインポートによってその内容を現在のモジュールで利用できるようになり、またそのインポート先がインポートしているモジュールからも遷移的に利用可能です。

:::comment
Modules do not necessarily correspond to namespaces.
Modules may add names to any namespace, and importing a module has no effect on the set of currently open namespaces.
:::

モジュールは必ずしも名前空間に対応するとは限りません。モジュールはどの名前空間にも名前を追加することができ、モジュールをインポートしても現在開いている名前空間のセットには影響しません。

:::comment
The imported module name is translated to a filename by replacing dots (`'.'`) in its name with directory separators and appending `.lean` or `.olean`.
Lean searches its include path for the corresponding intermediate build product or importable module file.
:::

インポートされたモジュール名は、その名前のドット（`'.'`）をディレクトリの区切り文字に置き換え、`.lean` または `.olean` を付加することでファイル名に変換されます。Lean は対応する中間ビルド生成物またはインポート可能なモジュールファイルをインクルードパスから検索します。

::::

:::comment
### Commands
:::

### コマンド（Commands）
%%%
tag := "commands"
%%%

:::comment
{tech}[Commands] are top-level statements in Lean.
Some examples are inductive type declarations, theorems, function definitions, namespace modifiers like `open` or `variable`, and interactive queries such as `#check`.
The syntax of commands is user-extensible.
Specific Lean commands are documented in the corresponding chapters of this manual, rather than being listed here.
:::

{tech}[コマンド] （command）は Lean においてトップレベルの文です。例えば、帰納型の宣言・定理・関数定義・`open` や `variable` などの名前空間修飾子・`#check` のような対話的クエリなどです。コマンドの構文はユーザが拡張可能です。特定の Lean コマンドについてはここに列挙するのではなく、このマニュアルの対応する章で説明しています。

::: TODO
Make the index include links to all commands, then xref from here
:::

:::comment
## Contents
:::

## 内容（Contents）
%%%
tag := "module-contents"
%%%

:::comment
A module includes an {TODO}[def and xref] environment, which includes both the inductive type and constant definitions from an environment and any data stored in {TODO}[xref] its environment extensions.
As the module is processed by Lean, commands add content to the environment.
A module's environment can be serialized to a {deftech (key:="olean")}[`.olean` file], which contains both the environment and a compacted heap region with the run-time objects needed by the environment.
This means that an imported module can be loaded without re-executing all of its commands.
:::

モジュールには環境が含まれます。これには環境からの帰納型と定数定義、環境拡張に格納されたデータの両方が含まれます。Lean によってモジュールが処理されると、コマンドは環境に内容を追加します。モジュールの環境は {deftech (key:="olean")}[`.olean` ファイル] にシリアライズすることができ、これには環境と環境によって必要とされるランタイムオブジェクトを含むコンパクト化されたヒープ領域の両方を含みます。これはインポートされたモジュールが、そのコマンドをすべて再実行することなくロードできることを意味します。

:::comment
# Packages, Libraries, and Targets

:::

# パッケージ・ライブラリ・ターゲット（Packages, Libraries, and Targets）
%%%
tag := "code-distribution"
%%%

:::comment
Lean code is organized into {deftech}_packages_, which are units of code distribution.
A {tech}[package] may contain multiple libraries or executables.
:::

Lean のコードはコード配布の単位である {deftech}_パッケージ_ （package）へと編成されます。 {tech}[パッケージ] には複数のライブラリや実行ファイルが含まれることがあります。

:::comment
Code in a package that is intended for use by other Lean packages is organized into {deftech (key:="library")}[libraries].
Code that is intended to be compiled and run as independent programs is organized into {deftech (key:="executable")}[executables].
Together, libraries and executables are referred to as {deftech}_targets_ in Lake, the standard Lean build tool. {TODO}[section xref]
:::

他の Lean パッケージで使用することを意図したパッケージ内のコードは {deftech (key:="library")}[ライブラリ] に編成されます。独立したプログラムとしてコンパイルされ実行されることを意図したコードは {deftech (key:="executable")}[実行ファイル] に編成されます。Lean の標準的なビルドツールである Lake では、ライブラリと実行ファイルを合わせて {deftech}_ターゲット_ と呼んでいます。

:::TODO
Write Lake section, coordinate this content with it
:::
