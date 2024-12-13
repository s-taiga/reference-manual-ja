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
#doc (Manual) "Notations" =>
-/
#doc (Manual) "記法（Notations）" =>
%%%
tag := "notations"
%%%

:::comment
The term {deftech}_notation_ is used in two ways in Lean: it can refer to the general concept of concise ways of writing down ideas, and it is the name of a language feature that allows notations to be conveniently implemented with little code.
Like custom operators, Lean notations allow the grammar of terms to be extended with new forms.
However, notations are more general: the new syntax may freely intermix required keywords or operators with subterms, and they provide more precise control over precedence levels.
Notations may also rearrange their parameters in the resulting subterms, while infix operators provide them to the function term in a fixed order.
Because notations may define operators that use a mix of prefix, infix, and postfix components, they can be called {deftech}_mixfix_ operators.

:::

{deftech}_記法_ （notation）という用語は Lean では2つの意味で用いられます：アイデアを簡潔に書き記すという一般的な概念を指す場合と、少ないコードで便利に記法を実装できる言語機能の名前です。カスタム演算子のように、Lean の記法は項の文法を新しい形で拡張することができます。しかし、記法はより汎用的です：新しい構文では、必要なキーワードや演算子と下位の項を自由に混在させることができ、優先順位レベルをより正確に制御することができます。記法はまた、結果として得られる部分項のパラメータを並べ替えることができますが、その一方で中置演算子は固定された順序でパラメータを関数項に与えます。記法は前置・中置・後置を混在して使用する演算子を定義することができるため、それらを {deftech}_mixfix_ 演算子と呼ぶことができます。

::::syntax command
:::comment
Notations are defined using the {keywordOf Lean.Parser.Command.notation}`notation` command.

:::

記法は {keywordOf Lean.Parser.Command.notation}`notation` コマンドを使って定義します。

```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind notation$[:$_:prec]? $[(name := $_:ident)]? $[(priority := $_:prio)]? $[$_:notationItem]* => $_:term
```
::::

::::syntax Lean.Parser.Command.notationItem (open := false)
:::comment
The body of a notation definition consists of a sequence of {deftech}_notation items_, which may be either string literals or identifiers with optional precedences.
:::

記法定義の本体は {deftech}_記法アイテム_ （notation item）の列からなり、文字列リテラルか、オプションの優先順位を持つ識別子のどちらかです。

```grammar
$s:str
```
```grammar
$x:ident$[:$_:prec]?
```
::::

:::comment
As with operator declarations, the contents of the documentation comments are shown to users while they interact with the new syntax.
Adding the {attr}`inherit_doc` attribute causes the documentation comment of the function at the head of the term into which the notation expands to be copied to the new syntax.
Other attributes may be added to invoke other compile-time metaprograms on the resulting definition.

:::

演算子の宣言と同様に、新しい構文を操作している間はドキュメントコメントの内容がユーザに表示されます。 {attr}`inherit_doc` 属性を追加すると、記法が展開される項の先頭にある関数のドキュメントコメントが新しい構文にコピーされます。他の属性を追加して、結果の定義に他のコンパイル時のメタプログラムを呼び出すことができます。

:::comment
Notations interact with {tech}[section scopes] in the same manner as attributes and operators.
By default, notations are available in any module that transitively imports the one in which they are established, but they may be declared `scoped` or `local` to restrict their availability either to contexts in which the current namespace has been opened or to the current {tech}[section scope], respectively.

:::

記法は {tech}[section scopes] と属性や演算子と同様に相互作用します。デフォルトでは、記法はそれが確立されたモジュールをインポートした任意のモジュールで遷移的に利用可能です。しかし、`scoped` または `local` と宣言することで、それぞれ現在の名前空間が開かれているコンテキストか、現在の {tech}[section scope] に限定することができます。

:::comment
Like operators, the {tech}[local longest-match rule] is used while parsing notations.
If more than one notation ties for the longest match, the declared priorities are used to determine which parse result applies.
If this still does not resolve the ambiguity, then all are saved, and the elaborator is expected to attempt all of them, succeeding when exactly one can be elaborated.

:::

演算子と同様に、 {tech}[ローカル最長一致規則] が記法をパースする際に使用されます。もし複数の記法が最長一致で並んだ場合、宣言された優先順位によってどのパース結果が適用されるかが決定されます。それでもあいまいさが解消されない場合、すべてが保存され、エラボレータはそれらすべてを試行し、ちょうど1つがエラボレートできたときに成功することが期待されます。

:::comment
Rather than a single operator with its fixity and token, the body of a notation declaration consists of a sequence of {deftech}_notation items_, which may be either new {tech}[atoms] (including both keywords such as `if`, `#eval`, or `where` and symbols such as `=>`, `+`, `↗`, `⟦`, or `⋉`) or positions for terms.
Just as they do in operators, string literals identify the placement of atoms.
Leading and trailing spaces in the strings do not affect parsing, but they cause Lean to insert spaces in the corresponding position when displaying the syntax in {tech}[proof states] and error messages.
Identifiers indicate positions where terms are expected, and name the corresponding term so it can be inserted in the notation's expansion.

:::

単一の演算子についてその配置と字句を示す代わりに、記法の本体の宣言は {deftech}_記法アイテム_ （notation item）の列から構成されます。これは新しい {tech}[アトム] （`if` や `#eval` などのキーワードと `=>` ・ `+` ・ `↗` ・ `⟦` ・ `⋉` などの記号の両方を含む）、または項の位置です。演算子と同様に、文字列リテラルはアトムの配置を指定します。文字列の先頭と末尾の空白はパースに影響しませんが、空白を入れた場合 {tech}[証明状態] やエラーメッセージで構文を表示する時に Lean が対応する位置に空白が挿入されます。識別子は項が予想される位置を示し、対応する項を記法の展開に挿入できるように名前を付けます。

:::comment
While custom operators have a single notion of precedence, there are many involved in a notation.
The notation itself has a precedence, as does each term to be parsed.
The notation's precedence determines which contexts it may be parsed in: the parser only attempts to parse productions whose precedence is at least as high as the current context.
For example, because multiplication has higher precedence than addition, the parser will attempt to parse an infix multiplication term while parsing the arguments to addition, but not vice versa.
The precedence of each term to be parsed determines which other productions may occur in them.

:::

カスタム演算子には単一の優先順位の表記がありますが、記法には多くの優先順位の表記があります。パースされる各項と同様に、記法自体にも優先順位があります。記法の優先順位はどのコンテキストでパースされるかを決定します：パーサは少なくとも現在のコンテキストと同程度の優先順位を持つプロダクションのパースを試みます。例えば、乗算は加算よりも優先順位が高いため、パーサは加算の引数をパースしている間に乗算の中置項のパースを試みますが、その逆は行いません。パースされる各項の優先順位は、その中でどの他のプロダクションが出現するかを決定します。

:::comment
If no precedence is supplied for the notation itself, the default value depends on the form of the notation.
If the notation both begins and ends with an atom (represented by string literals), then the default precedence is `max`.{TODO}[keywordOf]
This applies both to notations that consist only of a single atom and to notations with multiple items, in which the first and last items are both atoms.
Otherwise, the default precedence of the whole notation is `lead`.
If no precedence is provided for notation items that are terms, then they default to precedence `min`.

:::

記法自体に優先順位が与えられていない場合、デフォルト値は記法の形式によって異なります。記法がアトム（文字列リテラルで表される）出は自杏里、アトムで終わる場合、デフォルトの優先順位は `max` となります。これは1つのアトムだけで構成される記法と、最初と最後のアイテムが両方ともアトムである複数のアイテムを持つ記法にも適用されます。それ以外の場合、記法全体のデフォルトの優先順位は `lead` となります。項である記法アイテムに対して優先順位が与えられない場合、デフォルトの優先順位は `min` になります。

```lean (keep := false) (show := false)

-- Test for default precedences for notations

/-- Parser max -/
notation "takesMax " e:max => e
/-- Parser lead -/
notation "takesLead " e:lead => e
/-- Parser min -/
notation "takesMin " e:min => e

/-- Take the first one -/
notation e1 " <# " e2 => e1

/-- Take the first one in brackets! -/
notation "<<<<<" e1 " <<# " e2 ">>>>>" => e1

elab "#parse_test " "[" e:term "]"  : command => do
  Lean.logInfoAt e (toString e)
  pure ()

-- Here, takesMax vs takesLead distinguishes the notations

/-- info: («term_<#_» (termTakesMax_ "takesMax" (num "1")) "<#" (num "2")) -/
#guard_msgs in
#parse_test [ takesMax 1 <# 2 ]

/-- info: (termTakesLead_ "takesLead" («term_<#_» (num "1") "<#" (num "2"))) -/
#guard_msgs in
#parse_test [ takesLead 1 <# 2 ]


-- Here, takesMax vs takesLead does not distinguish the notations because both have precedence `max`

/--
info: (termTakesMax_ "takesMax" («term<<<<<_<<#_>>>>>» "<<<<<" (num "1") "<<#" (num "2") ">>>>>"))
-/
#guard_msgs in
#parse_test [ takesMax <<<<< 1 <<# 2 >>>>> ]

/--
info: (termTakesLead_ "takesLead" («term<<<<<_<<#_>>>>>» "<<<<<" (num "1") "<<#" (num "2") ">>>>>"))
-/
#guard_msgs in
#parse_test [ takesLead <<<<< 1 <<# 2 >>>>> ]
```

:::comment
After the required double arrow ({keywordOf Lean.Parser.Command.notation}`=>`), the notation is provided with an expansion.
While operators are always expanded by applying their function to the operator's arguments in order, notations may place their term items in any position in the expansion.
The terms are referred to by name.
Term items may occur any number of times in the expansion.
Because notation expansion is a purely syntactic process that occurs prior to elaboration or code generation, duplicating terms in the expansion may lead to duplicated computation when the resulting term is evaluated, or even duplicated side effects when working in a monad.

:::

必須の二重矢印（ {keywordOf Lean.Parser.Command.notation}`=>` ）に続いて記法がその展開される内容と共に提供されます。演算子は常にその関数を演算子の引数に順番に適用することで展開されますが、記法はその項アイテムを展開内の任意の位置に置くことができます。項は名前によって参照されます。項アイテムは展開の中で何度も出現することができます。記法の展開はエラボレーションやコード生成の前に行われる純粋に構文的な処理であるため、展開で項が複製されると、結果の項が評価される時に計算が重複したり、モナドで作業する際には副作用が重複したりする可能性があります。

:::::keepEnv
:::comment
::example "Ignored Terms in Notation Expansion"
:::
::::example "記法展開で無視された項"
:::comment
This notation ignores its first parameter:
:::

この記法は最初のパラメータを無視しています：

```lean
notation (name := ignore) "ignore " _ign:arg e:arg => e
```

:::comment
The term in the ignored position is discarded, and Lean never attempts to elaborate it, so terms that would otherwise result in errors can be used here:
:::

無視された位置にある項は破棄され、Lean はそれを決してエラボレートしません。そのためエラーになるような項をここで用いることができます：

```lean (name := ignore)
#eval ignore (2 + "whatever") 5
```
```leanOutput ignore
5
```

:::comment
However, the ignored term must still be syntactically valid:
:::

しかし、無視される項は構文的に有効でなければなりません：

```syntaxError ignore' (category := command)
#eval ignore (2 +) 5
```
```leanOutput ignore'
<example>:1:17: expected term
```
::::
:::::

:::::keepEnv
:::comment
::example "Duplicated Terms in Notation Expansion"
:::
::::example "記法展開で複製された項"

:::comment
The {keywordOf dup}`dup!` notation duplicates its sub-term.

:::

{keywordOf dup}`dup!` 記法はその部分項を複製しています。

```lean
notation (name := dup) "dup!" t:arg => (t, t)
```

:::comment
Because the term is duplicated, it can be elaborated separately with different types:
:::

この項は複製されているため、異なる型で別々にエラボレートされることができます：

```lean
def e : Nat × Int := dup! (2 + 2)
```

:::comment
Printing the resulting definition demonstrates that the work of addition will be performed twice:
:::

この定義を表示すると、加算が2回行われていることがわかります：

```lean (name := dup)
#print e
```
```leanOutput dup
def e : Nat × Int :=
(2 + 2, 2 + 2)
```
::::
:::::


:::comment
When the expansion consists of the application of a function defined in the global environment and each term in the notation occurs exactly once, an {tech}[unexpander] is generated.
The new notation will be displayed in {tech}[proof states], error messages, and other output from Lean when matching function application terms otherwise would have been displayed.
As with custom operators, Lean does not track whether the notation was used in the original term; it is used at every opportunity in Lean's output.

:::

展開がグローバル環境で定義された関数の適用で構成され、記法の各項がちょうど1回出現する場合、 {tech}[unexpander] が生成されます。この新しい記法は {tech}[証明状態] ・エラーメッセージ・その他の Lean からの出力にて、マッチする関数適用項が表示される場合に表示されます。カスタム演算子と同様に、Lean はもとの項がその記法で使われていたかどうかを追跡しません；これは Lean の出力にていたるところで用いられます。

:::comment
# Operators and Notations
:::

# 演算子と記法（Operators and Notations）

%%%
tag := "operators-and-notations"
%%%

:::comment
Internally, operator declarations are translated into notation declarations.
Term notation items are inserted where the operator would expect arguments, and in the corresponding positions in the expansion.
For prefix and postfix operators, the notation's precedence as well as the precedences of its term items is the operator's declared precedence.
For non-associative infix operators, the notation's precedence is the declared precedence, but both arguments are parsed at a precedence level that is one higher, which prevents successive uses of the notation without parentheses.
Associative infix operators use the operator's precedence for the notation and for one argument, while a precedence that is one level higher is used for the other argument; this prevents successive applications in one direction only.
Left-associative operators use the higher precedence for their right argument, while right-associative operators use the higher precedence for their left argument.

:::

内部的には、演算子宣言は記法宣言に変換されます。項の記法アイテムは、演算子が引数を予見する場所と展開の対応する位置に挿入されます。前置演算子や後置演算子の場合、記法の優先順位や項アイテムの優先順位は演算子の宣言された優先順位となります。非結合的な中置演算子の場合、記法の優先順位は宣言された優先順位ですが、両方の引数は1つ上の優先順位としてパースされるため、括弧無しで連続して記法を使用することはできません。結合的な中置演算子は、記法と一方の引数には演算子の優先順位を使用し、もう一方の引数には1つ高い優先順位を使用します。左結合の演算子には右の引数に高い優先順位を、右結合の演算子には左の引数に高い優先順位を使用します。
