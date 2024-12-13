/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

/-
#doc (Manual) "Defining New Syntax" =>
-/
#doc (Manual) "新しい構文の定義（Defining New Syntax）" =>
%%%
tag := "syntax-ext"
%%%

:::comment
Lean's uniform representation of syntax is very general and flexible.
This means that extensions to Lean's parser do not require extensions to the representation of parsed syntax.

:::

Lean の統一された構文表現は非常に汎用的で柔軟です。これは Lean のパーサを拡張しても、パースされた構文の表現を拡張する必要はないことを意味します。

:::comment
# Syntax Model
:::

# 構文モデル（Syntax Model）

:::comment
Lean's parser produces a concrete syntax tree, of type {name}`Lean.Syntax`.
{name}`Lean.Syntax` is an inductive type that represents all of Lean's syntax, including commands, terms, tactics, and any custom extensions.
All of these are represented by a few basic building blocks:

:::

Lean のパーサは {name}`Lean.Syntax` 型の解析木を生成します。 {name}`Lean.Syntax` はコマンド・項・タクティク・カスタム拡張を含む Lean のすべての構文を表す帰納型です。これらは全て、いくつかの基本的なビルディングブロックで表されます。

:::comment
: {deftech}[Atoms]

  Atoms are the fundamental terminals of the grammar, including literals (such as those for characters and numbers), parentheses, operators, and keywords.

:::

: {deftech}[アトム] （atom）

  アトムは文法の基本的な終端で、リテラル（文字や数値）・括弧・演算子・キーワードを含みます。

::::comment
: {deftech}[Identifiers]

  :::keepEnv
  ```lean (show := false)
  variable {α : Type u}
  variable {x : α}
  ```
  Identifiers represent names, such as {lean}`x`, {lean}`Nat`, or {lean}`Nat.add`.
  Identifier syntax includes a list of pre-resolved names that the identifier might refer to.
  :::

::::

: {deftech}[識別子] （identifier）

  :::keepEnv
  ```lean (show := false)
  variable {α : Type u}
  variable {x : α}
  ```
  識別子は {lean}`x` ・ {lean}`Nat` ・ {lean}`Nat.add` などのような名前を表します。識別子の構文には、識別子が参照する可能性のある事前解決された名前のリストが含まれています。
  :::

:::comment
: {deftech}[Nodes]

  Nodes represent the parsing of nonterminals.
  Nodes contain a {deftech}_syntax kind_, which identifies the syntax rule that the node results from, along with an array of child {name Lean.Syntax}`Syntax` values.

:::

: {deftech}[ノード] （node）

  ノードは非終端のパースを表します。ノードは {deftech}_構文種別_ （syntax kind）と子として {name Lean.Syntax}`Syntax` 値の配列を含みます。構文種別はノードの結果となる構文規則を識別します。

:::comment
: Missing Syntax

  When the parser encounters an error, it returns a partial result, so Lean can provide some feedback about partially-written programs or programs that contain mistakes.
  Partial results contain one or more instances of missing syntax.

:::

: 欠落した構文

  パーサがエラーに遭遇すると、パーサは部分的な結果を返すため、Lean は部分的に書かれたプログラムや間違いを含むプログラムについて何らかのフィードバックを提供することができます。部分的な結果には、1つ以上の構文の欠落が含まれます。

:::comment
Atoms and identifiers are collectively referred to as {deftech}_tokens_.

:::

アトムと識別子をまとめて {deftech}_トークン_ （token）と呼びます。

{docstring Lean.Syntax}

{docstring Lean.Syntax.Preresolved}

:::comment
# Syntax Node Kinds
:::

# 構文ノード種別（Syntax Node Kinds）

:::comment
Syntax node kinds typically identify the parser that produced the node.
This is one place where the names given to operators or notations (or their automatically-generated internal names) occur.
While only nodes contain a field that identifies their kind, identifiers have the kind {name Lean.identKind}`identKind` by convention, while atoms have their internal string as their kind by convention.
Lean's parser wraps each keyword atom `KW` in a singleton node whose kind is `` `token.KW ``.
The kind of a syntax value can be extracted using {name Lean.Syntax.getKind}`Syntax.getKind`.

:::

構文ノード種別は通常、そのノードを生成したパーサを識別します。これは演算子や記法に与えられた名前（または自動的に生成された内部的な名前）が出現する場所の1つです。ノードだけが種別を識別するフィールドを持ちますが、識別子は規約により {name Lean.identKind}`identKind` 種別を、アトムは規約により内部文字列を種別として持ちます。Lean のパーサは各キーワードアトム `KW` を ``​`token.KW`` という種類を持つ子を1つだけ持つノードにラップします。構文の値は {name Lean.Syntax.getKind}`Syntax.getKind` を使って取り出すことができます。

{docstring Lean.SyntaxNodeKind}

{docstring Lean.Syntax.isOfKind}

{docstring Lean.Syntax.getKind}

{docstring Lean.Syntax.setKind}

:::comment
# Token and Literal Kinds
:::

# トークンとリテラル種別（Token and Literal Kinds）

:::comment
A number of named kinds are associated with the basic tokens produced by the parser.
Typically, single-token syntax productions consist of a {name Lean.Syntax.node}`node` that contains a single {name Lean.Syntax.atom}`atom`; the kind saved in the node allows the value to be recognized.
Atoms for literals are not interpreted by the parser: string atoms include their leading and trailing double-quote characters along with any escape sequences contained within, and hexadecimal numerals are saved as a string that begins with {lean}`"0x"`.
{ref "typed-syntax-helpers"}[Helpers] such as {name}`Lean.TSyntax.getString` are provided to perform this decoding on demand.

:::

パーサによって生成される基本的なトークンには多くの名前付き種別が関連付けられます。通常、単一トークンの構文生成物は {name Lean.Syntax.atom}`atom` を1つ含む {name Lean.Syntax.node}`node` で構成されます；ノードに保存された種別によって値を判別できるようになります。リテラル用のアトムはパーサによって解釈されません：文字列アトムはその先頭と末尾のダブルクォート文字とその中に含まれるエスケープシーケンスを含み、16進数は {lean}`"0x"` から始まる文字列として保存されます。 {name}`Lean.TSyntax.getString` のような {ref "typed-syntax-helpers"}[補助関数] は要求に応じてこうしたデコードを行うために提供されています。

```lean (show := false) (keep := false)
-- Verify claims about atoms and nodes
open Lean in
partial def noInfo : Syntax → Syntax
  | .node _ k children => .node .none k (children.map noInfo)
  | .ident _ s x pre => .ident .none s x pre
  | .atom _ s => .atom .none s
  | .missing => .missing
/--
info: Lean.Syntax.node (Lean.SourceInfo.none) `num #[Lean.Syntax.atom (Lean.SourceInfo.none) "0xabc123"]
-/
#guard_msgs in
#eval noInfo <$> `(term|0xabc123)

/--
info: Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"ab\\tc\""]
-/
#guard_msgs in
#eval noInfo <$> `(term|"ab\tc")
```

{docstring Lean.identKind}

{docstring Lean.strLitKind}

{docstring Lean.interpolatedStrKind}

{docstring Lean.interpolatedStrLitKind}

{docstring Lean.charLitKind}

{docstring Lean.numLitKind}

{docstring Lean.scientificLitKind}

{docstring Lean.nameLitKind}

{docstring Lean.fieldIdxKind}

:::comment
# Internal Kinds
:::

# 内部的な種別（Internal Kinds）

{docstring Lean.groupKind}

{docstring Lean.nullKind}

{docstring Lean.choiceKind}

{docstring Lean.hygieneInfoKind}

:::comment
# Source Positions
:::

# ソース位置（Source Positions）

%%%
tag := "source-info"
%%%

:::comment
Atoms, identifiers, and nodes optionally contain {deftech}[source information] that tracks their correspondence with the original file.
The parser saves source information for all tokens, but not for nodes; position information for parsed nodes is reconstructed from their first and last tokens.
Not all {name Lean.Syntax}`Syntax` data results from the parser: it may be the result of {tech}[マクロ展開]macro expansion, in which case it typically contains a mix of generated and parsed syntax, or it may be the result of {tech key:="delaborate"}[delaborating] an internal term to display it to a user.
In these use cases, nodes may themselves contain source information.

:::

アトム・識別子・ノードは元のファイルとの対応を追跡する {deftech}[ソース情報] （source information）をオプションで含みます。パーサはすべてのトークンのソース情報を保存しますが、ノードのソース情報は保存しません；パースされたノードの位置情報は最初と最後のトークンから再構築されます。すべての {name Lean.Syntax}`Syntax` データがパーサから得られるわけではありません： {tech}[マクロ展開] の結果である場合もあり、その場合は通常、生成された構文と解析された構文が混在しています。また内部的な項をユーザに表示するために {tech key:="delaborate"}[delaborating] した結果である場合もあります。これらの使用例では、ノード自体にソース情報が含まれることがあります。

:::comment
Source information comes in two varieties:

:::

ソース情報には2種類存在します：

:::comment
: {deftech}[Original]

  Original source information comes from the parser.
  In addition to the original source location, it also contains leading and trailing whitespace that was skipped by the parser, which allows the original string to be reconstructed.
  This whitespace is saved as offsets into the string representation of the original source code (that is, as {name}`Substring`) to avoid having to allocate copies of substrings.

:::

: {deftech}[オリジナル] （original）

  もとのソース情報はパーサから得られます。もとのソース位置に加えて、パーサによってスキップされた先頭と末尾の空白も含まれるため、元の文字列を再構築することができます。この空白は、部分文字列のコピーを割り当てる必要が内容に、もとのソースコードの文字列表現のオフセットとして（つまり {name}`Substring` として）保存されます。

:::comment
: {deftech}[Synthetic]

  Synthetic source information comes from metaprograms (including macros) or from Lean's internals.
  Because there is no original string to be reconstructed, it does not save leading and trailing whitespace.
  Synthetic source positions are used to provide accurate feedback even when terms have been automatically transformed, as well as to track the correspondence between elaborated expressions and their presentation in Lean's output.
  A synthetic position may be marked {deftech}_canonical_, in which case some operations that would ordinarily ignore synthetic positions will treat it as if it were not.

:::

: {deftech}[統合的] （synthetic）

  統合されたソース情報はメタプログラム（マクロを含む）または Lean の内部から得られます。再構築されるもとの文字列がないため、先頭と末尾の空白は保存されません。統合されたソース位置は、項が自動的に変換された場合でも正確なフィードバックを提供し、エラボレートされた式と Lean の出力における表現の対応を追跡するために使用されます。統合された位置には {deftech}_標準的_ （canonical）というマークが付けられることがありますが、この場合、通常は統合された位置を無視する操作があたかもそうではないかのように扱われます。

{docstring Lean.SourceInfo}

:::comment
# Inspecting Syntax
:::

# 構文の検査（Inspecting Syntax）

```lean (show := false)
section Inspecting
open Lean
```

:::comment
There are three primary ways to inspect {lean}`Syntax` values:

:::

{lean}`Syntax` 値の検査には3つの方法があります：

:::comment
 : The {lean}`Repr` Instance

  The {lean}`Repr Syntax` instance produces a very detailed representation of syntax in terms of the constructors of the {lean}`Syntax` type.

:::

 : {lean}`Repr` インスタンス

  {lean}`Repr Syntax` インスタンスは {lean}`Syntax` 型のコンストラクタを用いて、構文の非常に詳細な表現を生成します。

:::comment
 : The {lean}`ToString` Instance

  The {lean}`ToString Syntax` instance produces a compact view, representing certain syntax kinds with particular conventions that can make it easier to read at a glance.
  This instance suppresses source position information.

:::

 : {lean}`ToString` インスタンス

  {lean}`ToString` インスタンスはコンパクトな可視化を行い、特定の構文の種類を特定の規則で表現し、ひと目で読みやすくします。このインスタンスはソースの位置情報を抑制します。

:::comment
 : The Pretty Printer

  Lean's pretty printer attempts to render the syntax as it would look in a source file, but fails if the nesting structure of the syntax doesn't match the expected shape.

:::

 : プリティプリンタ

  Lean のプリティプリンタは、構文をソースファイルで表示されるようにレンダリングしようとします。ただし、構文の入れ子構造が期待される形と一致しない場合は失敗します。

:::::keepEnv
:::comment
::example "Representing Syntax as Constructors"
:::
::::example "コンストラクタによる構文表現"
:::comment
The {name}`Repr` instance's representation of syntax can be inspected by quoting it in the context of {keywordOf Lean.Parser.Command.eval}`#eval`, which can run actions in the command elaboration monad {name Lean.Elab.Command.CommandElabM}`CommandElabM`.
To reduce the size of the example output, the helper {lean}`removeSourceInfo` is used to remove source information prior to display.
:::

{keywordOf Lean.Parser.Command.eval}`#eval` のコンテキストにて quote することで、 {name}`Repr` インスタンスの構文表現を検査することができます。これはコマンドエラボレーションモナド {name Lean.Elab.Command.CommandElabM}`CommandElabM` でアクションが実行されます。出力例のサイズを小さくするために、補助関数 {lean}`removeSourceInfo` を使用して、表示前にソース情報を削除しています。

```lean
partial def removeSourceInfo : Syntax → Syntax
  | .atom _ str => .atom .none str
  | .ident _ str x pre => .ident .none str x pre
  | .node _ k children => .node .none k (children.map removeSourceInfo)
  | .missing => .missing
```

```lean (name := reprStx1)
#eval do
  let stx ← `(2 + $(⟨.missing⟩))
  logInfo (repr (removeSourceInfo stx.raw))
```
```leanOutput reprStx1
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `«term_+_»
  #[Lean.Syntax.node (Lean.SourceInfo.none) `num #[Lean.Syntax.atom (Lean.SourceInfo.none) "2"],
    Lean.Syntax.atom (Lean.SourceInfo.none) "+", Lean.Syntax.missing]
```

:::comment
In the second example, {tech}[macro scopes] inserted by quotation are visible on the call to {name}`List.length`.
:::

2つ目の例では、quotation で囲まれた {tech}[マクロスコープ] が {name}`List.length` の呼び出しで見えるようになっています。

```lean (name := reprStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  logInfo (repr (removeSourceInfo stx.raw))
```
:::comment
The contents of the {tech}[pre-resolved identifier] {name}`List.length` are visible here:
:::

{tech}[事前解決された識別子] {name}`List.length` の内容は以下のように表示されます：

```leanOutput reprStx2
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `Lean.Parser.Term.app
  #[Lean.Syntax.ident
      (Lean.SourceInfo.none)
      "List.length".toSubstring
      (Lean.Name.mkNum `List.length._@.Manual.NotationsMacros.SyntaxDef._hyg 2)
      [Lean.Syntax.Preresolved.decl `List.length [], Lean.Syntax.Preresolved.namespace `List.length],
    Lean.Syntax.node
      (Lean.SourceInfo.none)
      `null
      #[Lean.Syntax.node
          (Lean.SourceInfo.none)
          `«term[_]»
          #[Lean.Syntax.atom (Lean.SourceInfo.none) "[",
            Lean.Syntax.node
              (Lean.SourceInfo.none)
              `null
              #[Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Rose\""],
                Lean.Syntax.atom (Lean.SourceInfo.none) ",",
                Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Daffodil\""],
                Lean.Syntax.atom (Lean.SourceInfo.none) ",",
                Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Lily\""]],
            Lean.Syntax.atom (Lean.SourceInfo.none) "]"]]]
```
::::
:::::

:::comment
The {name}`ToString` instance represents the constructors of {name}`Syntax` as follows:

:::

{name}`ToString` インスタンスは {name}`Syntax` のコンストラクタを以下のように表現します：

:::comment
 * The {name Syntax.ident}`ident` constructor is represented as the underlying name. Source information and pre-resolved names are not shown.
 * The {name Syntax.atom}`atom` constructor is represented as a string.
 * The {name Syntax.missing}`missing` constructor is represented by `<missing>`.
 * The representation of the {name Syntax.node}`node` constructor depends on the kind.
   If the kind is {lean}`` `null ``, then the node is represented by its child nodes order in square brackets.
   Otherwise, the node is represented by its kind followed by its child nodes, both surrounded by parentheses.

:::

 * {name Syntax.ident}`ident` コンストラクタはベースになっている名前として表現されます。ソース情報と事前解決された名前は表示されません。
 * {name Syntax.atom}`atom` コンストラクタは文字列として表現されます。
 * {name Syntax.missing}`missing` コンストラクタは `<missing>` で表現されます。
 * {name Syntax.node}`node` コンストラクタの表現は種別に依存します。もし種別が ``​`null`` の場合、ノードは角括弧で囲まれた子ノードで表現されます。そうでない場合、ノードはその種別とその子ノードで表現され、どちらも括弧で囲まれます。

:::comment
::example "Syntax as Strings"
:::
::::example "文字列による構文"
:::comment
The string representation of syntax can be inspected by quoting it in the context of {keywordOf Lean.Parser.Command.eval}`#eval`, which can run actions in the command elaboration monad {name Lean.Elab.Command.CommandElabM}`CommandElabM`.

:::

{keywordOf Lean.Parser.Command.eval}`#eval` のコンテキストにて quote することで、文字列による構文表現を検査することができます。これはコマンドエラボレーションモナド {name Lean.Elab.Command.CommandElabM}`CommandElabM` でアクションが実行されます。

```lean (name := toStringStx1)
#eval do
  let stx ← `(2 + $(⟨.missing⟩))
  logInfo (toString stx)
```
```leanOutput toStringStx1
(«term_+_» (num "2") "+" <missing>)
```

:::comment
In the second example, {tech}[macro scopes] inserted by quotation are visible on the call to {name}`List.length`.
:::

2つ目の例では、quotation で囲まれた {tech}[マクロスコープ] が {name}`List.length` の呼び出しで見えるようになっています。

```lean (name := toStringStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  logInfo (toString stx)
```
```leanOutput toStringStx2
(Term.app
 `List.length._@.Manual.NotationsMacros.SyntaxDef._hyg.2
 [(«term[_]» "[" [(str "\"Rose\"") "," (str "\"Daffodil\"") "," (str "\"Lily\"")] "]")])
```
::::

:::comment
Pretty printing syntax is typically most useful when including it in a message to a user.
Normally, Lean automatically invokes the pretty printer when necessary.
However, {name}`ppTerm` can be explicitly invoked if needed.

:::

構文のプリティプリントは通常、ユーザへのメッセージに含める場合に最も便利です。通常、Lean は必要に応じて自動的にプリティプリンタを起動します。しかし、必要に応じて {name}`ppTerm` を明示的に呼び出すことができます。

:::::keepEnv
:::comment
::example "Pretty-Printed Syntax"
:::
::::example "プリティプリントされた構文"
```lean (show := false)
open Lean Elab Command
```

:::comment
The string representation of syntax can be inspected by quoting it in the context of {keywordOf Lean.Parser.Command.eval}`#eval`, which can run actions in the command elaboration monad {name Lean.Elab.Command.CommandElabM}`CommandElabM`.
Because new syntax declarations also equip the pretty printer with instructions for displaying them, the pretty printer requires a configuration object.
This context can be constructed with a helper:
:::

{keywordOf Lean.Parser.Command.eval}`#eval` のコンテキストにて quote することで、文字列による構文表現を検査することができます。これはコマンドエラボレーションモナド {name Lean.Elab.Command.CommandElabM}`CommandElabM` でアクションが実行されます。新しい構文宣言は、それらを表示させるための命令をプリティプリンタに備えさせるため、プリティプリンタは設定オブジェクトを必要とします。このオブジェクトは補助関数で構築できます：

```lean
def getPPContext : CommandElabM PPContext := do
  return {
    env := (← getEnv),
    opts := (← getOptions),
    currNamespace := (← getCurrNamespace),
    openDecls := (← getOpenDecls)
  }
```

```lean (name := ppStx1)
#eval show CommandElabM Unit from do
  let stx ← `(2 + 5)
  let fmt ← ppTerm (← getPPContext) stx
  logInfo fmt
```
```leanOutput ppStx1
2 + 5
```

:::comment
In the second example, the {tech}[macro scopes] inserted on {name}`List.length` by quotation cause it to be displayed with a dagger (`✝`).
:::

2つ目の例では、quotation によって {name}`List.length` に挿入された {tech}[マクロスコープ] がダガー（`✝`）付きで表示されます。

```lean (name := ppStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  let fmt ← ppTerm (← getPPContext) stx
  logInfo fmt
```
```leanOutput ppStx2
List.length✝ ["Rose", "Daffodil", "Lily"]
```

:::comment
Pretty printing wraps lines and inserts indentation automatically.
A {tech}[coercion] typically converts the pretty printer's output to the type expected by {name}`logInfo`, using a default layout width.
The width can be controlled by explicitly calling {name Std.Format.pretty}`pretty` with a named argument.
:::

プリティプリントは行を折り返し、自動的にインデントを挿入します。 {tech}[coercion] は通常、デフォルトのレイアウト幅を使用して、プリティプリンタの出力を {name}`logInfo` が期待する型に変換します。この幅は {name Std.Format.pretty}`pretty` を名前付き引数で明示的に呼び出すことで制御できます。

```lean (name := ppStx3)
#eval do
  let flowers := #["Rose", "Daffodil", "Lily"]
  let manyFlowers := flowers ++ flowers ++ flowers
  let stx ← `(List.length [$(manyFlowers.map (quote (k := `term))),*])
  let fmt ← ppTerm (← getPPContext) stx
  logInfo (fmt.pretty (width := 40))
```
```leanOutput ppStx3
List.length✝
  ["Rose", "Daffodil", "Lily", "Rose",
    "Daffodil", "Lily", "Rose",
    "Daffodil", "Lily"]
```
::::


:::::

```lean (show := false)
end Inspecting
```

:::comment
# Typed Syntax
:::

# 型付き構文（Typed Syntax）

:::comment
Syntax may additionally be annotated with a type that specifies which {tech}[syntax category] it belongs to.
{TODO}[Describe the problem here - complicated invisible internal invariants leading to weird error msgs]
The {name Lean.TSyntax}`TSyntax` structure contains a type-level list of syntax categories along with a syntax tree.
The list of syntax categories typically contains precisely one element, in which case the list structure itself is not shown.

:::

構文は追加でどの {tech}[構文カテゴリ] に属するかを指定する型を注釈することができます。 {name Lean.TSyntax}`TSyntax` 構造体には、構文木とともに、構文カテゴリの型レベルのリストが含まれます。構文カテゴリのリストは通常、ちょうど1つの要素を含み、その場合リスト構造自体は表示されません。

{docstring Lean.TSyntax}

:::comment
{tech}[Quasiquotations] prevent the substitution of typed syntax that does not come from the correct syntactic category.
For many of Lean's built-in syntactic categories, there is a set of {tech}[coercions] that appropriately wrap one kind of syntax for another category, such as a coercion from the syntax of string literals to the syntax of terms.
Additionally, many helper functions that are only valid on some syntactic categories are defined for the appropriate typed syntax only.

:::

{tech}[Quasiquotations] は正しい構文カテゴリに由来しない型付き構文の置換を防ぎます。Lean の組み込み構文カテゴリの多くには、ある種別の構文を別のカテゴリに適切にラップする {tech}[coercions] のセットがあります。これには例えば文字列リテラルの構文から項の構文への強制などが含まれます。さらに、ある構文カテゴリに対してのみ有効な補助関数の多くは、適切な型付き構文に対してのみ定義されています。

```lean (show := false)
/-- info: instCoeHTCTOfCoeHTC -/
#guard_msgs in
open Lean in
#synth CoeHTCT (TSyntax `str) (TSyntax `term)
```

:::comment
The constructor of {name Lean.TSyntax}`TSyntax` is public, and nothing prevents users from constructing values that break internal invariants.
The use of {name Lean.TSyntax}`TSyntax` should be seen as a way to reduce common mistakes, rather than rule them out entirely.


:::

{name Lean.TSyntax}`TSyntax` のコンストラクタはパブリックであり、ユーザが内部制約を破る値を構築することを妨げるものはありません。 {name Lean.TSyntax}`TSyntax` の使用はよくあるミスを完全に排除するためではなく、減らすための方法と考えるべきです。

:::comment
In addition to {name Lean.TSyntax}`TSyntax`, there are types that represent arrays of syntax, with or without separators.
These correspond to {TODO}[xref] repeated elements in syntax declarations or antiquotations.

:::

{name Lean.TSyntax}`TSyntax` の他に、セパレータの有無に関わらず、構文の配列を表す型があります。これらは構文宣言、または antiquotation の繰り返し要素に対応します。

{docstring Lean.TSyntaxArray}

{docstring Lean.Syntax.TSepArray}

:::comment
# Aliases
:::

# エイリアス（Aliases）

:::comment
A number of aliases are provided for commonly-used typed syntax varieties.
These aliases allow code to be written at a higher level of abstraction.

:::

よく使われる型付き構文のために、多くのエイリアスが用意されています。これらのエイリアスによって、より抽象度の高いコードを書くことができます。

{docstring Lean.Term}

{docstring Lean.Command}

{docstring Lean.Syntax.Level}

{docstring Lean.Syntax.Tactic}

{docstring Lean.Prec}

{docstring Lean.Prio}

{docstring Lean.Ident}

{docstring Lean.StrLit}

{docstring Lean.CharLit}

{docstring Lean.NameLit}

{docstring Lean.NumLit}

{docstring Lean.ScientificLit}

{docstring Lean.HygieneInfo}

:::comment
# Helpers for Typed Syntax
:::

# 型付き構文のための補助関数（Helpers for Typed Syntax）

%%%
tag := "typed-syntax-helpers"
%%%

:::comment
For literals, Lean's parser produces a singleton node that contains an {name Lean.Syntax.atom}`atom`.
The inner atom contains a string with source information, while the node's kind specifies how the atom is to be interpreted.
This may involve decoding string escape sequences or interpreting base-16 numeric literals.
The helpers in this section perform the correct interpretation.

:::

リテラルの場合、Lean のパーサは {name Lean.Syntax.atom}`atom` を1つ含むノードを生成します。内部のアトムは、ソース情報を持つ文字列を含み、ノードの種別はアトムがどのように解釈されるかを指定します。これには文字列のエスケープシーケンスのデコードや、16進数リテラルの解釈などがふくまれます。本節の補助案数は正しい解釈を行います。

{docstring Lean.TSyntax.getId}

{docstring Lean.TSyntax.getName}

{docstring Lean.TSyntax.getNat}

{docstring Lean.TSyntax.getScientific}

{docstring Lean.TSyntax.getString}

{docstring Lean.TSyntax.getChar}

{docstring Lean.TSyntax.getHygieneInfo}

:::comment
# Syntax Categories
:::

# 構文カテゴリ（Syntax Categories）

%%%
tag := "syntax-categories"
%%%

:::comment
Lean's parser contains a table of {deftech}_syntax categories_, which correspond to nonterminals in a context-free grammar.
Some of the most important categories are terms, commands, universe levels, priorities, precedences, and the categories that represent tokens such as literals.
Typically, each {tech}[syntax kind] corresponds to a category.
New categories can be declared using {keywordOf Lean.Parser.Command.syntaxCat}`declare_syntax_cat`.

:::

Lean のパーサは {deftech}_構文カテゴリ_ （syntax category）のテーブルを保持しています。構文カテゴリはコンテキストに依存しない文法における非終端に対応します。最も重要なカテゴリは項・コマンド・宇宙レベル・優先度 {margin}[訳注：インスタンスの優先度（priority）のこと] ・優先順位 {margin}[訳注：構文解析においての優先順位のこと（precedence）] ・リテラルなどのトークンを表すカテゴリです。通常、各 {tech}[構文種別] はカテゴリに対応します。新しいカテゴリは {keywordOf Lean.Parser.Command.syntaxCat}`declare_syntax_cat` を使って宣言できます。

::::syntax command
:::comment
Declares a new syntactic category.

:::

新しい構文カテゴリを宣言します。

```grammar
$[$_:docComment]?
declare_syntax_cat $_ $[(behavior := $_)]?
```
::::

:::comment
The leading identifier behavior is an advanced feature that usually does not need to be modified.
It controls the behavior of the parser when it encounters an identifier, and can sometimes cause the identifier to be treated as a non-reserved keyword instead.
This is used to avoid turning the name of every {ref "tactics"}[tactic] into a reserved keyword.

:::

識別子の後ろの動作指定は高度な機能で、通常は変更する必要はありません。これはパーサが識別子に遭遇した時の動作を制御し、時には識別子を非予約キーワードとして代わりに扱うようにすることができます。これはすべての {ref "tactics"}[tactic] の名前が予約キーワードになるのを避けるために使用されています。

{docstring Lean.Parser.LeadingIdentBehavior}

:::comment
# Syntax Rules
:::

# 構文規則（Syntax Rules）

%%%
tag := "syntax-rules"
%%%

:::comment
Each {tech}[syntax category] is associated with a set of {deftech}_syntax rules_, which correspond to productions in a context-free grammar.
Syntax rules can be defined using the {keywordOf Lean.Parser.Command.syntax}`syntax` command.

:::

各 {tech}[構文カテゴリ] は {deftech}_構文規則_ （syntax rule）のセットに関連づけられています。構文規則はコンテキストに依存しない文法の生成物に対応します。構文規則は {keywordOf Lean.Parser.Command.syntax}`syntax` コマンドで定義できます。

:::syntax command
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind
syntax$[:$p]? $[(name := $x)]? $[(priority := $p)]? $_* : $c
```
:::

:::comment
As with operator and notation declarations, the contents of the documentation comments are shown to users while they interact with the new syntax.
Attributes may be added to invoke compile-time metaprograms on the resulting definition.

:::

演算子や記法宣言と同様に、ドキュメントコメントの内容はユーザが新しい構文を操作している間に表示されます。コンパイル時にメタプログラムを呼び出すために、結果の定義に属性を追加することができます。

:::comment
Syntax rules interact with {tech}[section scopes] in the same manner as attributes, operators, and notations.
By default, syntax rules are available to the parser in any module that transitively imports the one in which they are established, but they may be declared `scoped` or `local` to restrict their availability either to contexts in which the current namespace has been opened or to the current {tech}[section scope], respectively.

:::

構文属性は属性・演算子・記法と同じように {tech}[section scopes] と相互作用します。デフォルトでは、構文規則はそれが確立されたパーサをインポートした任意のモジュールで遷移的に利用可能です。しかし、`scoped` または `local` と宣言することで、それぞれ現在の名前空間が開かれているコンテキストか、現在の {tech}[section scope] に限定することができます。

:::comment
When multiple syntax rules for a category can match the current input, the {tech}[local longest-match rule] is used to select one of them.
Like notations and operators, if there is a tie for the longest match then the declared priorities are used to determine which parse result applies.
If this still does not resolve the ambiguity, then all the results that tied are saved.
The elaborator is expected to attempt all of them, succeeding when exactly one can be elaborated.

:::

あるカテゴリの複数の構文規則が現在の入力にマッチする場合、 {tech}[ローカル最長一致規則] が使用され、そのうちの1つが選択されます。記法や演算子と同様に、最長一致が複数ある場合は、宣言された優先度が使用され、どちらの構文解析結果が適用されるかが決定されます。それでもあいまいさが解消されない場合、同店の結果はすべて保存されます。エラボレータはそれらすべての試行し、1つだけがエラボレートできたときに成功することが期待されます。

:::comment
The syntax rule's precedence, written immediately after the {keywordOf Lean.Parser.Command.syntax}`syntax` keyword, restricts the parser to use this new syntax only when the precedence context is at least the provided value.
{TODO}[Default precedence]
Just as with operators and notations, syntax rules may be manually provided with a name; if they are not, an otherwise-unused name is generated.
Whether provided or generated, this name is used as the syntax kind in the resulting {name Lean.Syntax.node}`node`.

:::

{keywordOf Lean.Parser.Command.syntax}`syntax` キーワードの直後に記述された構文規則の優先順位は、優先順位コンテキストが指定された値以上の場合にのみ、この新しい構文を使用するようにパーサを制限します。演算子や記法と同様に、構文規則も手動で名前を指定することができます；指定されない場合、他では使われない名前が生成されます。名前が指定された場合でも生成された場合でも、この名前は結果の {name Lean.Syntax.node}`node` の構文種別として使用されます。

:::comment
The body of a syntax declaration is even more flexible than that of a notation.
String literals specify atoms to match.
Subterms may be drawn from any syntax category, rather than just terms, and they may be optional or repeated, with or without interleaved comma separators.
Identifiers in syntax rules indicate syntax categories, rather than naming subterms as they do in notations.


:::

構文宣言の本体は記法よりもさらに柔軟です。文字列リテラルはマッチするアトムを指定します。部分項は項だけでなく、任意の構文カテゴリから引き出すことができ、それらはカンマの有無に関わらずオプション的であったり繰り返されたりします。構文規則における識別子は、記法の場合のように部分項を指定するのではなく、構文カテゴリを示します。

:::comment
Finally, the syntax rule specifies which syntax category it extends.
It is an error to declare a syntax rule in a nonexistent category.

:::

最後に、構文規則はどのカテゴリを拡張するかを指定します。存在しないカテゴリで構文規則を宣言するのはエラーになります。

```lean (show := false)
-- verify preceding para
/-- error: unknown category 'nuhUh' -/
#guard_msgs in
syntax "blah" : nuhUh
```


::::syntax stx (open := false)
:::comment
The syntactic category `stx` is the grammar of specifiers that may occur in the body of a {keywordOf Lean.Parser.Command.syntax}`syntax` command.

:::

構文カテゴリ `stx` は {keywordOf Lean.Parser.Command.syntax}`syntax` コマンドのボディに出現する可能性のある指定子についての文法です。

:::comment
String literals are parsed as {tech}[atoms] (including both keywords such as `if`, `#eval`, or `where`):
:::

文字列リテラルは {tech}[アトム] （`if`・`#eval`・`where`などのキーワードを含む）としてパースされます：

```grammar
$s:str
```
:::comment
Leading and trailing spaces in the strings do not affect parsing, but they cause Lean to insert spaces in the corresponding position when displaying the syntax in {tech}[proof states] and error messages.
Ordinarily, valid identifiers occurring as atoms in syntax rules become reserved keywords.
Preceding a string literal with an ampersand (`&`) suppresses this behavior:
:::

文字列の先頭と末尾の空白はパースに影響しませんが、空白を入れた場合 {tech}[証明状態] やエラーメッセージで構文を表示する時に Lean が対応する位置に空白が挿入されます。通常、構文規則のアトムとして出現する有効な識別子は予約キーワードになります。文字列リテラルの前にアンパサンド（`&`）を置くとこの動作が抑制されます：

```grammar
&$s:str
```

:::comment
Identifiers specify the syntactic category expected in a given position, and may optionally provide a precedence:{TODO}[Default prec here?]
:::

識別子は、指定された位置で期待される構文カテゴリを指定し、オプションで優先順位を指定できます：

```grammar
$x:ident$[:$p]?
```

:::comment
The `*` modifier is the Kleene star, matching zero or more repetitions of the preceding syntax.
It can also be written using `many`.
:::

修飾子 `*` はクリーネスターで、直前の構文の0回以上の繰り返しにマッチします。これは `many` と書くこともできます。

```grammar
$s:stx *
```
:::comment
The `+` modifier matches one or more repetitions of the preceding syntax.
It can also be written using `many1`.
:::

修飾子 `+` は直前の構文の1回以上の繰り返しにマッチします。これは `many1` と書くこともできます。

```grammar
$s:stx +
```
:::comment
The `?` modifier makes a subterm optional, and matches zero or one, but not more, repetitions of the preceding syntax.
It can also be written as `optional`.
:::

修飾性 `?` は部分項をオプショナルにし、直前の構文の繰り返しに0回または1回（それ以上は繰り返さない）にマッチします。これは `optional` と書くこともできます。

```grammar
$s:stx ?
```
```grammar
optional($s:stx)
```

:::comment
The `,*` modifier matches zero or more repetitions of the preceding syntax with interleaved commas.
It can also be written using `sepBy`.
:::

修飾子 `,*` はカンマで区切られた直前の構文の0回以上の繰り返しにマッチします。これは `sepBy` と書くこともできます。

```grammar
$_:stx ,*
```

:::comment
The `,+` modifier matches one or more repetitions of the preceding syntax with interleaved commas.
It can also be written using `sepBy1`.
:::

修飾子 `,+` はカンマで区切られた直前の構文の1回以上の繰り返しにマッチします。これは `sepBy1` と書くこともできます。

```grammar
$_:stx ,+
```

:::comment
The `,*,?` modifier matches zero or more repetitions of the preceding syntax with interleaved commas, allowing an optional trailing comma after the final repetition.
It can also be written using `sepBy` with the `allowTrailingSep` modifier.
:::

修飾子 `,*,?` はカンマで区切られた直前の構文の0回以上の繰り返しにマッチし、繰り返しの最後のカンマを任意にすることができます。これは `allowTrailingSep` を伴った `sepBy` と書くこともできます。

```grammar
$_:stx ,*,?
```

:::comment
The `,+,?` modifier matches one or more repetitions of the preceding syntax with interleaved commas, allowing an optional trailing comma after the final repetition.
It can also be written using `sepBy1` with the `allowTrailingSep` modifier.
:::

修飾子 `,+,?` はカンマで区切られた直前の構文の1回以上の繰り返しにマッチし、繰り返しの最後のカンマを任意にすることができます。これは `allowTrailingSep` を伴った `sepBy1` と書くこともできます。

```grammar
$_:stx ,+,?
```

:::comment
The `<|>` operator, which can be written `orelse`, matches either syntax.
However, if the first branch consumes any tokens, then it is committed to, and failures will not be backtracked:
:::

演算子 `<|>` は `orelse` と書くこともでき、どちらかの構文にマッチします。しかし、最初の分岐で何らかのトークンが消費された場合、その分岐がコミットされ、失敗はバックトラックされません：

```grammar
$_:stx <|> $_:stx
```
```grammar
orelse($_:stx, $_:stx)
```

:::comment
The `!` operator matches the complement of its argument.
If its argument fails, then it succeeds, resetting the parsing state.
:::

演算子 `!` は引数の補集合にマッチします。引数が失敗した場合に成功し、パース状態がリセットされます。

```grammar
! $_:stx
```

:::comment
Syntax specifiers may be grouped using parentheses.
:::

構文指定子は括弧を使ってグループ化することができます。

```grammar
($_:stx)
```

:::comment
Repetitions may be defined using `many` and `many1`.
The latter requires at least one instance of the repeated syntax.
:::

繰り返しは `many` と `many1` を使って定義することができます。後者は繰り返される構文のインスタンスが少なくとも1つ必要です。

```grammar
many($_:stx)
```
```grammar
many1($_:stx)
```

:::comment
Repetitions with separators may be defined using `sepBy` and `sepBy1`, which respectively match zero or more occurrences and one or more occurrences, separated by some other syntax.
They come in three varieties:
 * The two-parameter version uses the atom provided in the string literal to parse the separators, and does not allow trailing separators.
 * The three-parameter version uses the third parameter to parse the separators, using the atom for pretty-printing.
 * The four-parameter version optionally allows the separator to occur an extra time at the end of the sequence.
    The fourth argument must always literally be the keyword `allowTrailingSep`.

:::

区切り文字を使った繰り返しは `sepBy` と `sepBy1` を使って定義することができ、それぞれ0個以上・1個以上の出現にマッチし、他の構文で区切られます。使い方は3種類あります：
 * パラメータが2つの場合は、文字列リテラルで指定されたアトムを使用して区切り文字をパースし、末尾の区切り文字を許容しません。
 * パラメータが3つの場合は、3番目のパラメータを使用して区切り文字をパースし、プリティプリンタのためにアトムを使用します。
 * パラメータが4つの場合、オプションとしてシーケンスの最後にセパレータを追加することができます。第4引数は常にキーワード `allowTrailingSep` を指定しなければなりません。

```grammar
sepBy($_:stx, $_:str)
```
```grammar
sepBy($_:stx, $_:str, $_:stx)
```
```grammar
sepBy($_:stx, $_:str, $_:stx, allowTrailingSep)
```
```grammar
sepBy1($_:stx, $_:str)
```
```grammar
sepBy1($_:stx, $_:str, $_:stx)
```
```grammar
sepBy1($_:stx, $_:str, $_:stx, allowTrailingSep)
```
::::

:::::keepEnv
:::comment
::example "Parsing Matched Parentheses and Brackets"
:::
::::example "一致した丸括弧と角括弧のパース"

:::comment
A language that consists of matched parentheses and brackets can be defined using syntax rules.
The first step is to declare a new {tech}[syntax category]:
:::

一致する丸括弧と角括弧で構成される言語は、構文規則を使って定義することができます。最初のステップは新しい {tech}[構文カテゴリ] を宣言することです：

```lean
declare_syntax_cat balanced
```
:::comment
Next, rules can be added for parentheses and square brackets.
To rule out empty strings, the base cases consist of empty pairs.
:::

次に、丸括弧と角括弧の規則を追加することができます。空の文字列を除外するために、基本ケースは空のペアで構成されます。

```lean
syntax "(" ")" : balanced
syntax "[" "]" : balanced
syntax "(" balanced ")" : balanced
syntax "[" balanced "]" : balanced
syntax balanced balanced : balanced
```

:::comment
In order to invoke Lean's parser on these rules, there must also be an embedding from the new syntax category into one that may already be parsed:
:::

これらの規則に対して Lean のパーサを呼び出すには、新しい構文カテゴリから、すでにパースされている構文カテゴリへの埋め込みも必要です：

```lean
syntax (name := termBalanced) "balanced " balanced : term
```

:::comment
These terms cannot be elaborated, but reaching an elaboration error indicates that parsing succeeded:
:::

これらの項はエラボレートできませんが、エラボレートエラーになったということは、パースが成功したということです：

```lean
/--
error: elaboration function for 'termBalanced' has not been implemented
  balanced ()
-/
#guard_msgs in
example := balanced ()

/--
error: elaboration function for 'termBalanced' has not been implemented
  balanced []
-/
#guard_msgs in
example := balanced []

/--
error: elaboration function for 'termBalanced' has not been implemented
  balanced [[]()([])]
-/
#guard_msgs in
example := balanced [[] () ([])]
```

:::comment
Similarly, parsing fails when they are mismatched:
:::

同様に、括弧が一致しない場合はパースに失敗します：

```syntaxError mismatch
example := balanced [() (]]
```
```leanOutput mismatch
<example>:1:25: expected ')' or balanced
```
::::
:::::

:::::keepEnv
:::comment
::example "Parsing Comma-Separated Repetitions"
:::
::::example "カンマ区切りの繰り返しのパース"
:::comment
A variant of list literals that requires double square brackets and allows a trailing comma can be added with the following syntax:
:::

二重の角括弧を必要とし、末尾のカンマを許容するリストリテラルの亜種は、以下の構文で追加できます：

```lean
syntax "[[" term,*,? "]]" : term
```

:::comment
Adding a {deftech}[macro] that describes how to translate it into an ordinary list literal allows it to be used in tests.
:::

{deftech}[マクロ] （macro）を追加して、通常のリストリテラルに変換する方法を記述することで、テストで使用できるようになります。

```lean
macro_rules
  | `(term|[[$e:term,*]]) => `([$e,*])
```

```lean (name := evFunnyList)
#eval [["Dandelion", "Thistle",]]
```
```leanOutput evFunnyList
["Dandelion", "Thistle"]
```

::::
:::::

:::comment
# Indentation
:::

# インデント（Indentation）

%%%
tag := "syntax-indentation"
%%%

:::comment
Internally, the parser maintains a saved source position.
Syntax rules may include instructions that interact with these saved positions, causing parsing to fail when a condition is not met.
Indentation-sensitive constructs, such as {keywordOf Lean.Parser.Term.do}`do`, save a source position, parse their constituent parts while taking this saved position into account, and then restore the original position.

:::

内部的に、パーサは保存されたソース位置を保持します。構文規則には、これらの保存された位置と相互作用し、条件が満たされない場合にパースを失敗させる命令を含めることができます。 {keywordOf Lean.Parser.Term.do}`do` のようなインデントに依存する構文はソース位置を保存し、この保存された位置を考慮しながら一連の部分をパースし、もとの位置に戻します。

:::comment
In particular, Indentation-sensitvity is specified by combining {name Lean.Parser.withPosition}`withPosition` or {name Lean.Parser.withPositionAfterLinebreak}`withPositionAfterLinebreak`, which save the source position at the start of parsing some other syntax, with {name Lean.Parser.checkColGt}`colGt`, {name Lean.Parser.checkColGe}`colGe`, and {name Lean.Parser.checkColEq}`colEq`, which compare the current column with the column from the most recently-saved position.
{name Lean.Parser.checkLineEq}`lineEq` can also be used to ensure that two positions are on the same line in the source file.

:::

特に、インデントへの依存は {name Lean.Parser.withPosition}`withPosition` または {name Lean.Parser.withPositionAfterLinebreak}`withPositionAfterLinebreak` と {name Lean.Parser.checkColGt}`colGt` ・ {name Lean.Parser.checkColGe}`colGe` ・ {name Lean.Parser.checkColEq}`colEq` を組み合わせることで指定します。最初の2つは他の構文をパースし始める際のソース位置を保存します。後ろの3つは現在の列と最近保存された位置の列を比較します。また、 {name Lean.Parser.checkLineEq}`lineEq` は2つの位置がソースファイルの同じ行にあることを確認するために使用できます。

:::parserAlias withPosition
:::

:::parserAlias withoutPosition
:::

:::parserAlias withPositionAfterLinebreak
:::

:::parserAlias colGt
:::

:::parserAlias colGe
:::

:::parserAlias colEq
:::

:::parserAlias lineEq
:::


:::::keepEnv
:::comment
::example "Aligned Columns"
:::
::::example "列をそろえる"
:::comment
This syntax for saving notes takes a bulleted list of items, each of which must be aligned at the same column.
:::

箇条書きの項目リストを取るメモ保存のための以下の構文では、各項目は同じ列にそろえなければなりません。

```lean
syntax "note " ppLine withPosition((colEq "• " str ppLine)+) : term
```

:::comment
There is no elaborator or macro associated with this syntax, but the following example is accepted by the parser:
:::

この構文に関連するエラボレータやマクロはありませんが、以下の例はパーサに受け入れられます：

```lean (error := true) (name := noteEx1)
#check
  note
    • "One"
    • "Two"
```
```leanOutput noteEx1
elaboration function for '«termNote__•__»' has not been implemented
  note
    • "One"
    • "Two"
```

:::comment
The syntax does not require that the list is indented with respect to the opening token, which would require an extra `withPosition` and a `colGt`.
:::

この構文では、リストが開始トークンに対してインデントされている必要はありません。それを達成するには追加で `withPosition` と `colGt` が必要です。

```lean (error := true) (name := noteEx15)
#check
  note
• "One"
• "Two"
```
```leanOutput noteEx15
elaboration function for '«termNote__•__»' has not been implemented
  note
    • "One"
    • "Two"
```


:::comment
The following examples are not syntactically valid because the columns of the bullet points do not match.
:::

以下の例は、箇条書きの列が一致していないために、構文的に妥当ではありません。

```syntaxError noteEx2
#check
  note
    • "One"
   • "Two"
```
```leanOutput noteEx2
<example>:4:3: expected end of input
```

```syntaxError noteEx2
#check
  note
   • "One"
     • "Two"
```
```leanOutput noteEx2
<example>:4:5: expected end of input
```
::::
:::::
