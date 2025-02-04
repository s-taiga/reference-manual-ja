/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Language.Files

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option pp.rawOnError true
set_option maxRecDepth 3000

set_option linter.unusedVariables false

/-
#doc (Manual) "Source Files" =>
-/
#doc (Manual) "ソースファイル（Source Files）" =>

{include 0 Manual.Language.Files}


# モジュールの内容（Module Contents）

:::comment
# Module Contents

:::

:::comment
As described {ref "module-structure"}[in the section on the syntax of files], a Lean module consists of a header followed by a sequence of commands.

:::

{ref "module-structure"}[ファイルの構文に関する節] で説明したように、Lean のモジュールはヘッダとそれに続く一連のコマンドで構成されます。

:::comment
## Commands and Declarations

:::

## コマンドと宣言（Commands and Declaration）

:::comment
After the header, every top-level phrase of a Lean module is a command.
Commands may add new types, define new constants, or query Lean for information.
Commands may even {ref "language-extension"}[change the syntax used to parse subsequent commands].

:::

ヘッダの後にある、Lean モジュールのトップレベルのフレーズはすべてコマンドです。コマンドは新しい型を追加したり、新しい定数を定義したり、Lean に情報を問い合わせたりします。コマンドは {ref "language-extension"}[後続のコマンドをパースするために使用される構文を変更する] ことさえもできます。

::: planned 100
 * Describe the various families of available commands (definition-like, `#eval`-like, etc).
 * Refer to specific chapters that describe major commands, such as `inductive`.
:::

:::comment
### Definition-Like Commands

:::

### 定義に類するコマンド（Definition-Like Commands）

::: planned 101
 * Precise descriptions of these commands and their syntax
 * Comparison of each kind of definition-like command to the others
:::

:::comment
The following commands in Lean are definition-like: {TODO}[Render commands as their name (a la tactic index)]
:::

以下の Lean のコマンドは定義に類するものです：

 * {syntaxKind}`def`
 * {syntaxKind}`abbrev`
 * {syntaxKind}`example`
 * {syntaxKind}`theorem`

:::comment
All of these commands cause Lean to {tech key:="elaborator"}[elaborate] a term based on a signature.
With the exception of {syntaxKind}`example`, which discards the result, the resulting expression in Lean's core language is saved for future use in the environment.
The {keywordOf Lean.Parser.Command.declaration}`instance` command is described in the {ref "instance-declarations"}[section on instance declarations].

:::

これらのコマンドはすべて Lean によってシグネチャに応じた項へ {tech key:="エラボレータ"}[エラボレート] されます。結果を破棄する {syntaxKind}`example` を除き、Lean のコア言語での結果の式は将来の環境で使用するために保存されます。 {keywordOf Lean.Parser.Command.declaration}`instance` コマンドについては {ref "instance-declarations"}[インスタンス宣言の節] で記述します。

:::syntax Lean.Parser.Command.declaration
```grammar
$_:declModifiers
$_:definition
```
:::

:::syntax Lean.Parser.Command.definition
```grammar
def $_ $_ := $_
```

```grammar
def $_ $_
  $[| $_ => $_]*
```

```grammar
def $_ $_ where
  $_*
```
:::

:::syntax Lean.Parser.Command.theorem
```grammar
theorem $_ $_ := $_
```

```grammar
theorem $_ $_
  $[| $_ => $_]*
```

```grammar
theorem $_ $_ where
  $_*
```
:::

:::syntax Lean.Parser.Command.abbrev
```grammar
abbrev $_ $_ := $_
```

```grammar
abbrev $_ $_
  $[| $_ => $_]*
```

```grammar
abbrev $_ $_ where
  $_*
```
:::



:::syntax Lean.Parser.Command.example
```grammar
example $_ $_ := $_
```

```grammar
example $_ $_
  $[| $_ => $_]*
```

```grammar
example $_ $_ where
  $_*
```
:::

:::comment
{deftech}_Opaque constants_ are defined constants that cannot be reduced to their definition.

:::

{deftech}_不透明な定数_ はそれらの定義へ簡約されない定義された定数です。

:::syntax Lean.Parser.Command.opaque
```grammar
opaque $_ $_
```
:::

:::syntax Lean.Parser.Command.axiom
```grammar
axiom $_ $_
```
:::


### Modifiers
%%%
tag := "declaration-modifiers"
%%%

::: planned 52

A description of each modifier allowed in the production `declModifiers`, including {deftech}[documentation comments].

:::

:::syntax declModifiers alias:=Lean.Parser.Command.declModifiers

```grammar
$_
$_
$_
$_
$_
$_
```

:::

### Signatures

:::planned 53

Describe signatures, including the following topics:
 * Explicit, implicit, instance-implicit, and strict implicit parameter binders
 * {deftech key := "optional parameter"}[Optional] and {deftech}[automatic parameters]
 * {deftech}_Automatic implicit_ parameters
 * Argument names and by-name syntax
 * Which parts can be omitted where? Why?

:::

:::comment
### Headers

:::

### ヘッダ（Headers）

:::comment
The {deftech}[_header_] of a definition or declaration specifies the signature of the new constant that is defined.

:::

定義または宣言の {deftech}[_ヘッダ_] （header）は定義される新しい定数のシグネチャを指定します。

::: TODO
* Precision and examples; list all of them here
* Mention interaction with autoimplicits
:::

## Namespaces
%%%
tag := "namespaces"
%%%

:::planned 210

Describe {deftech}[namespaces], aliases, and the semantics of `export` and `open`.
Which language features are controlled by the currently open namespaces?

:::

:::comment
## Section Scopes
:::

## セクションスコープ（Section Scopes）

%%%
tag := "scopes"
%%%

:::comment
Many commands have an effect for the current {deftech}[_section scope_] (sometimes just called "scope" when clear).
Every Lean module has a section scope.
Nested scopes are created via the {keywordOf Lean.Parser.Command.namespace}`namespace` and {keywordOf Lean.Parser.Command.section}`section` commands, as well as the {keywordOf Lean.Parser.Command.in}`in` command combinator.

:::

多くのコマンドは現在の {deftech}[_セクションスコープ_] （section scope）（明確な場合は単位「スコープ」と呼ばれることもあります）に対して効果を持ちます。Lean のすべてのモジュールはセクションスコープを持ちます。スコープを入れ子にするには {keywordOf Lean.Parser.Command.namespace}`namespace` と {keywordOf Lean.Parser.Command.section}`section` コマンド、および {keywordOf Lean.Parser.Command.in}`in` コマンドコンビネータによって作成されます。

:::comment
The following data are tracked in section scopes:

:::

セクションスコープでは、以下のデータが追跡されます：

:::comment
: The Current Namespace

  The {deftech}_current namespace_ is the namespace into which new declarations will be defined.
  Additionally, {tech (key:="resolve")}[name resolution] includes all prefixes of the current namespace in the scope for global names.

:::

: 現在の名前空間

  {deftech}_現在の名前空間_ （current namespace）は新しく宣言されたものが定義される名前空間です。さらに、 {tech (key:="解決")}[名前解決] はグローバル名のスコープに現在の名前空間のすべての接頭辞を含めます。

:::comment
: Opened Namespaces

  When a namespace is {deftech}_opened_, its names become available without an explicit prefix in the current scope.
  Additionally, scoped attributes and {ref "syntax-rules"}[scoped syntax extensions] in namespaces that have been opened are active in the current section scope.

:::

: 開かれた名前空間

  名前空間が {deftech}_開かれる_ （opened）と、その名前は現在のスコープで明示的な接頭辞なしで利用可能になります。さらに、開かれた名前空間に対してのスコープ属性と {ref "syntax-rules"}[スコープ構文拡張] は、現在のセクションスコープで有効になります。

:::comment
: Options

  Compiler options are reverted to their original values at the end of the scope in which they were modified.

:::

: オプション

  コンパイラオプションの変更は、その変更が行われたスコープの終了時にもとの値に戻されます。

:::comment
: Section Variables

  {tech}[Section variables] are names (or {tech}[instance implicit] parameters) that are automatically added as parameters to definitions.
  They are also added as universally-quantified assumptions to theorems when they occur in the theorem's statement.


:::

: セクション変数

  {tech}[セクション変数] は、定義のパラメータとして自動的に追加される名前（もしくは {tech}[インスタンス暗黙] のパラメータ）です。また、定理の文中に登場する場合は、全称量化された仮定として定理に追加されます。

:::comment
### Controlling Section Scopes
:::

### セクションスコープの制御（Controlling Section Scopes）

%%%
tag := "scope-commands"
%%%

:::comment
The {keywordOf Lean.Parser.Command.section}`section` command creates a new section scope, but does not modify the current namespace, opened namespaces, or section variables.
Changes made to the section scope are reverted when the section ends.
Sections may optionally be named; the {keywordOf Lean.Parser.Command.end}`end` command that closes a named section must use the same name.
If section names have multiple components (that is, if they contain `.`-separated names), then multiple nested sections are introduced.
Section names have no other effect, and are a readability aid.

:::

{keywordOf Lean.Parser.Command.section}`section` コマンドは新しいセクションスコープを作成しますが、現在の名前空間・開かれた名前空間・セクション変数は変更しません。セクションスコープに加えられた変更は、そのセクションが終了するともとに戻ります。セクションにはオプションとして名前を付けることができます；名前付きセクションを閉じる {keywordOf Lean.Parser.Command.end}`end` コマンドでは、同じ名前を使用する必要があります。セクション名が複数のコンポーネントから構成される（つまり `.` で区切られた名前で構成される場合）、複数の入れ子になったセクションが導入されます。セクション名には可読性の目的以外の効果はありません。

::::syntax command
:::comment
The {keywordOf Lean.Parser.Command.section}`section` command creates a section scope that lasts either until an `end` command or the end of the file.
:::

{keywordOf Lean.Parser.Command.section}`section` コマンドは `end` コマンドかファイルの終わりまで続くセクションスコープを作成します。

```grammar
section $[$id:ident]?
```
::::

:::comment
::example "Named Section"
:::
::::example "名前付きスコープ"

:::comment
The name {name Greetings.english}`english` is defined in the `Greetings` namespace.

:::

名前 {name Greetings.english}`english` は `Greetings` 名前空間で定義されています。

```lean
def Greetings.english := "Hello"
```

:::comment
Outside its namespace, it cannot be evaluated.

:::

名前空間の外からは評価することができません。

```lean (error := true) (name := english1)
#eval english
```
```leanOutput english1
unknown identifier 'english'
```

:::comment
Opening a section allows modifications to the global scope to be contained.
This section is named `Greetings`.
:::

セクションを開くことで、グローバルスコープへの変更を含めることができます。このセクションの名前は `Greetings` です。

```lean
section Greetings
```

:::comment
Even though the section name matches the definition's namespace, the name is not in scope because section names are purely for readability and ease of refactoring.

:::

セクション名が定義の名前空間と一致していても、その名前はスコープに含まれません。なぜなら、セクション名は純粋に可読性を上げ、リファクタリングを容易にするためのものだからです。

```lean (error := true)  (name := english2)
#eval english
```
```leanOutput english2
unknown identifier 'english'
```

:::comment
Opening the namespace `Greetings` brings {name}`Greetings.english` as {name Greetings.english}`english`:


:::

名前空間 `Greetings` を開くと、 {name}`Greetings.english` は {name Greetings.english}`english` になります：

```lean  (name := english3)
open Greetings

#eval english
```
```leanOutput english3
"Hello"
```

:::comment
The section's name must be used to close it.

:::

このセクションを閉じるにはセクション名を使わなければなりません。

```lean (error := true) (name := english4)
end
```
```leanOutput english4
invalid 'end', name is missing (expected Greetings)
```

```lean
end Greetings
```

:::comment
When the section is closed, the effects of the {keywordOf Lean.Parser.Command.open}`open` command are reverted.
:::

セクションが閉じられると、 {keywordOf Lean.Parser.Command.open}`open` コマンドの効果は元に戻ります。

```lean (error := true)  (name := english5)
#eval english
```
```leanOutput english5
unknown identifier 'english'
```
::::

:::comment
The {keywordOf Lean.Parser.Command.namespace}`namespace` command creates a new section scope.
Within this section scope, the current namespace is the name provided in the command, interpreted relative to the current namespace in the surrounding section scope.
Like sections, changes made to the section scope are reverted when the namespace's scope ends.

:::

{keywordOf Lean.Parser.Command.namespace}`namespace` コマンドは新しいセクションスコープを作成します。このセクションスコープ内では、現在の名前空間はコマンドで指定された名前となり、周囲のセクションスコープ内において現在の名前空間から相対的に解釈されます。セクションと同様に、セクションスコープに加えられた変更は、名前空間のスコープが終了するともとに戻ります。

:::comment
To close a namespace, the {keywordOf Lean.Parser.Command.end}`end` command requires a suffix of the current namespace, which is removed.
All section scopes introduced by the {keywordOf Lean.Parser.Command.namespace}`namespace` command that introduced part of that suffix are closed.

:::

名前空間を閉じるには、 {keywordOf Lean.Parser.Command.end}`end` コマンドで、削除する現在の名前空間の接尾辞を指定します。その接尾辞に含まれる {keywordOf Lean.Parser.Command.namespace}`namespace` コマンドで導入されたセクションスコープは全て閉じられます。

::::syntax command
:::comment
The `namespace` command modifies the current namespace by appending the provided identifier.

:::

`namespace` コマンドは、指定された識別子を追加して現在の名前空間を変更します。

:::comment
creates a section scope that lasts either until an {keywordOf Lean.Parser.Command.end}`end` command or the end of the file.
:::

{keywordOf Lean.Parser.Command.end}`end` コマンドかファイルの終わりまで続くセクションスコープを作成します。

```grammar
namespace $id:ident
```
::::


::::syntax command
:::comment
Without an identifier, {keywordOf Lean.Parser.Command.end}`end` closes the most recently opened section, which must be anonymous.
:::

識別子が無い場合、 {keywordOf Lean.Parser.Command.end}`end` は最近開いたセクションを閉じます。このセクションは無名でなければなりません。

```grammar
end
```

:::comment
With an identifier, it closes the most recently opened section section or namespace.
If it is a section, the identifier be a suffix of the concatenated names of the sections opened since the most recent {keywordOf Lean.Parser.Command.namespace}`namespace` command.
If it is a namespace, then the identifier must be a suffix of the current namespace's extensions since the most recent {keywordOf Lean.Parser.Command.section}`section` that is still open; afterwards, the current namespace will have had this suffix removed.
:::

識別子を指定すると、最も最近に開かれたセクションまたは名前空間を閉じます。セクションの場合、この識別子は、直近の {keywordOf Lean.Parser.Command.namespace}`namespace` コマンド以降にオープンされたセクション名を連結した接尾辞でなければなりません。名前空間の場合、この識別子は、まだ開いている直近の {keywordOf Lean.Parser.Command.section}`section` 以降の現在の名前空間の拡張子の接尾辞でなければなりません；その後、現在の名前空間ではこの接尾辞は削除されます。

```grammar
end $id:ident
```
::::

:::comment
The {keywordOf Lean.Parser.Command.mutual}`end` that closes a {keywordOf Lean.Parser.Command.mutual}`mutual` block is part of the syntax of {keywordOf Lean.Parser.Command.mutual}`mutual`, rather than the {keywordOf Lean.Parser.Command.end}`end` command.

:::

{keywordOf Lean.Parser.Command.mutual}`mutual` ブロックを閉じる {keywordOf Lean.Parser.Command.mutual}`end` は、 {keywordOf Lean.Parser.Command.end}`end` コマンドではなく、 {keywordOf Lean.Parser.Command.mutual}`mutual` の構文の一部です。

:::comment
::example "Nesting Namespaces and Sections"
:::
::::example "名前空間とセクションの入れ子"
:::comment
Namespaces and sections may be nested.
A single {keywordOf Lean.Parser.Command.end}`end` command may close one or more namespaces or one or more sections, but not a mix of the two.

:::

名前空間とセクションは入れ子にすることができます。1つの {keywordOf Lean.Parser.Command.end}`end` コマンドで1つ以上の名前空間、または1つ以上のセクションを閉じることができますが、両者を混ぜたものを閉じることはできません。

:::comment
After setting the current namespace to `A.B.C` with two separate commands, `B.C` may be removed with a single {keywordOf Lean.Parser.Command.end}`end`:
:::

2つの別々のコマンドで現在の名前空間を `A.B.C` に設定した後、1つの {keywordOf Lean.Parser.Command.end}`end` で `B.C` を削除することができます：

```lean
namespace A.B
namespace C
end B.C
```
:::comment
At this point, the current namespace is `A`.

:::

この時点で、現在の名前空間は `A` です。

:::comment
Next, an anonymous section and the namespace `D.E` are opened:
:::

次に、匿名のセクションと名前空間 `D.E` が開かれます：

```lean
section
namespace D.E
```
:::comment
At this point, the current namespace is `A.D.E`.
An {keywordOf Lean.Parser.Command.end}`end` command cannot close all three due to the intervening section:
:::

この時点で、現在の名前空間は `A.D.E` です。1つの {keywordOf Lean.Parser.Command.end}`end` コマンドでは、間にセクションがあるため、3つすべてを閉じることはできません：

```lean (error := true) (name := endADE) (keep := false)
end A.D.E
```
```leanOutput endADE
invalid 'end', name mismatch (expected «».D.E)
```
:::comment
Instead, namespaces and sections must be ended separately.
:::

その代わり、名前空間とセクションは別々に終了しなければなりません。

```lean
end D.E
end
end A
```
::::

:::comment
Rather than opening a section for a single command, the {keywordOf Lean.Parser.Command.in}`in` combinator can be used to create single-command section scope.
The {keywordOf Lean.Parser.Command.in}`in` combinator is right-associative, allowing multiple scope modifications to be stacked.

:::

単一のコマンドのためにセクションを開くのではなく、 {keywordOf Lean.Parser.Command.in}`in` コンビネータを使用して単一のコマンド用のセクションスコープを作成することができます。 {keywordOf Lean.Parser.Command.in}`in` は右結合であるため、複数のスコープの変更を重ねることができます。

::::syntax command
:::comment
The `in` command combinator introduces a section scope for a single command.
:::

`in` コマンドコンビネータは単一のコマンドにセクションスコープを導入します。

```grammar
$c:command in
$c:command
```
::::

:::comment
::example "Using {keywordOf Lean.Parser.Command.in}`in` for Local Scopes"
:::
::::example "ローカルスコープのための {keywordOf Lean.Parser.Command.in}`in` の使用"
:::comment
The contents of a namespace can be made available for a single command using {keywordOf Lean.Parser.Command.in}`in`.
:::

名前空間の内容は {keywordOf Lean.Parser.Command.in}`in` を使用して単一のコマンドで使用できるようにすることができます。

```lean
def Dessert.cupcake := "delicious"

open Dessert in
#eval cupcake
```

:::comment
After the single command, the effects of {keywordOf Lean.Parser.Command.open}`open` are reverted.

:::

単一のコマンドの後では、 {keywordOf Lean.Parser.Command.open}`open` の効果はもとに戻ります。

```lean (error := true) (name := noCake)
#eval cupcake
```
```leanOutput noCake
unknown identifier 'cupcake'
```
::::

:::comment
### Section Variables
:::

### セクション変数（Section Variables）

:::comment
{deftech}_Section variables_ are parameters that are automatically added to declarations that mention them.
This occurs whether or not the option {option}`autoImplicit` is {lean}`true`.
Section variables may be implicit, strict implicit, or explicit; instance implicit section variables are treated specially.

:::

{deftech}_セクション変数_ （section variable）はそれを言及する宣言に対して自動的に追加されるパラメータです。これは {option}`autoImplicit` オプションが {lean}`true` であってもなくても発生します。セクション変数は暗黙・厳密な暗黙・明示的のいずれでもかまいません；インスタンス暗黙のセクション変数は特別に扱われます。

:::comment
When the name of a section variable is encountered in a non-theorem declaration, it is added as a parameter.
Any instance implicit section variables that mention the variable are also added.
If any of the variables that were added depend on other variables, then those variables are added as well; this process is iterated until no more dependencies remain.
All section variables are added in the order in which they are declared, before all other parameters.
Section variables are added only when they occur in the _statement_ of a theorem.
Otherwise, modifying the proof of a theorem could change its statement if the proof term made use of a section variable.

:::

定理以外の宣言でセクション変数名が出現すると、パラメータとして追加されます。その変数に言及しているインスタンス暗黙のセクション変数も追加されます。追加された変数が他の変数に依存している場合は、それらの変数も追加されます；このプロセスは依存が無くなるまで繰り返されます。すべてのセクション変数は、宣言された順に他のすべてのパラメータよりも前に追加されます。セクション変数が追加されるのは、それが定理の _文_ の中に現れる時だけです。そうでなければ、証明項がセクション変数を使用している場合、定理の証明を変更によってその文が変更されてしまう可能性があります。

:::comment
Variables are declared using the {keywordOf Lean.Parser.Command.variable}`variable` command.


:::

変数は {keywordOf Lean.Parser.Command.variable}`variable` コマンドを使って宣言します。

:::syntax command
```grammar
variable $b:bracketedBinder $b:bracketedBinder*
```
:::

::::syntax bracketedBinder (open := false)
:::comment
The bracketed binders allowed after `variable` match the syntax used in definition headers.
:::

`variable` の後ろに許可される括弧付きの束縛子は、定義でのヘッダで使用される構文と一致します。

```grammar
($x $x* : $t $[:= $e]?)
```
```grammar
{$x $x* : $t}
```
```grammar
⦃$x $x* : $t⦄
```
```grammar
[$[$x :]? $t]
```
::::




:::comment
::example "Section Variables"
:::
::::example "セクション変数"
:::comment
In this section, automatic implicit parameters are disabled, but a number of section variables are defined.

:::

このセクションでは、自動的な暗黙のパラメータは無効になっていますが、多くのセクション変数が定義されています。

```lean
section
set_option autoImplicit false
universe u
variable {α : Type u} (xs : List α) [Zero α] [Add α]
```

:::comment
Because automatic implicit parameters are disabled, the following definition fails:
:::

自動的な暗黙パラメータが無効になっているため、以下の定義は失敗します：

```lean (error := true) (name := secvars) (keep := false)
def addAll (lst : List β) : β :=
  lst.foldr (init := 0) (· + ·)
```
```leanOutput secvars
unknown identifier 'β'
```

:::comment
On the other hand, not even {lean}`xs` needs to be written directly in the definition:

:::

一方で、以下の定義では {lean}`xs` さえも直接書く必要はありません：

```lean
def addAll :=
  xs.foldr (init := 0) (· + ·)
```

::::

:::comment
To add a section variable to a theorem even if it is not explicitly mentioned in the statement, mark the variable with the {keywordOf Lean.Parser.Command.include}`include` command.
All variables marked for inclusion are added to all theorems.
The {keywordOf Lean.Parser.Command.omit}`omit` command removes the inclusion mark from a variable; it's typically a good idea to use it with {keywordOf Lean.Parser.Command.in}`in`.


:::

セクション変数が文の中で明示的に言及されていなくても定理に追加するには、 {keywordOf Lean.Parser.Command.include}`include` コマンドでその変数をマークします。include としてマークされた変数はすべての定理に追加されます。 {keywordOf Lean.Parser.Command.omit}`omit` コマンドは変数から include マークを削除します；通常、これは {keywordOf Lean.Parser.Command.in}`in` と一緒に使用すると良いでしょう。

```lean (show := false)
section
variable {p : Nat → Prop}
variable (pFifteen : p 15)
```
:::comment
::example "Included and Omitted Section Variables"
:::
:::::example "セクション変数の include と omit"

:::comment
This section's variables include a predicate as well as everything needed to prove that it holds universally, along with a useless extra assumption.

:::

このセクションの変数には述語と、それが普遍的に成立するために必要なすべての情報、役に立たない余分な仮定が含まれています。

```lean
section
variable {p : Nat → Prop}
variable (pZero : p 0) (pStep : ∀ n, p n → p (n + 1))
variable (pFifteen : p 15)
```

:::comment
However, only {lean}`p` is added to this theorem's assumptions, so it cannot be proved.
:::

しかし、以下の定理には {lean}`p` しか追加されないため、証明することができません。

```lean (error := true) (keep := false)
theorem p_all : ∀ n, p n := by
  intro n
  induction n
```

:::comment
The {keywordOf Lean.Parser.Command.include}`include` command causes the additional assumptions to be added unconditionally:
:::

{keywordOf Lean.Parser.Command.include}`include` コマンドは無条件に仮定の追加を行います：

```lean (keep := false) (name := lint)
include pZero pStep pFifteen

theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```
:::comment
Because the spurious assumption {lean}`pFifteen` was inserted, Lean issues a warning:
:::

{lean}`pFifteen` という偽の仮定が挿入されたため、Lean は警告を発します：

```leanOutput lint
automatically included section variable(s) unused in theorem 'p_all':
  pFifteen
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit pFifteen in theorem ...
note: this linter can be disabled with `set_option linter.unusedSectionVars false`
```

:::comment
This can be avoided by using {keywordOf Lean.Parser.Command.omit}`omit`to remove {lean}`pFifteen`:
:::

これは {keywordOf Lean.Parser.Command.omit}`omit` を使って {lean}`pFifteen` を削除することで回避できます：

```lean (keep := false)
include pZero pStep pFifteen

omit pFifteen in
theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```

```lean
end
```

:::::
```lean (show := false)
end
```

:::comment
### Scoped Attributes
:::

### スコープ属性（Scoped Attributes）

:::comment
Many attributes can be applied in a particular scope.
This determines whether the attribute's effect is visible only in the current section scope, in namespaces that open the current namespace, or everywhere.
These scope indications are also used to control {ref "syntax-rules"}[syntax extensions] and {ref "instance-attribute"}[type class instances].

:::

多くの属性は、適用するスコープを特定のものにすることができます。これによって属性の効果が、現在のセクションスコープでのみ・現在の名前空間を開いている名前空間のみ・どこからでも見ることができるかを決定します。これらのスコープ指定は {ref "syntax-rules"}[構文拡張] や {ref "instance-attribute"}[型クラスインスタンス] を制御するためにも使用されます。

::::syntax attrKind (open := false)
:::comment
Globally-scoped declarations (the default) are in effect whenever the {tech}[module] in which they're established is transitively imported.
They are indicated by the absence of another scope modifier.
:::

グローバルスコープ宣言（デフォルト）は、その宣言が確立された {tech}[module] が遷移的にインポートされた場所ならどこででも有効です。この宣言は他のスコープ修飾子がないことで指示されます。

```grammar
```

:::comment
Locally-scoped declarations are in effect only for the extent of the {tech}[section scope] in which they are established.
:::

ローカルスコープの宣言は、それが確立された {tech}[セクションスコープ] の範囲でのみ有効です。

```grammar
local
```

:::comment
Scoped declarations are in effect whenever the {tech key:="current namespace"}[namespace] in which they are established is opened.
:::

スコープ宣言は、その宣言が確立されている {tech key:="現在の名前空間"}[名前空間] が開かれるたびに有効になります。

```grammar
scoped
```
::::

# Axioms

:::planned 78
Describe {deftech}_axioms_ in detail
:::

# Attributes
%%%
tag := "attributes"
%%%

:::planned 144
 * Concrete syntax of {deftech}[attributes]
 * Use cases
 * Scope
 * When can they be added?
:::

# Dynamic Typing

{docstring TypeName}

{docstring Dynamic}

{docstring Dynamic.mk}

{docstring Dynamic.get?}

# Coercions
%%%
tag := "coercions"
%%%

:::planned 146
 * {deftech}[Coercions]
 * When they are inserted
 * Varieties of coercions
 * When should each be used?
:::
