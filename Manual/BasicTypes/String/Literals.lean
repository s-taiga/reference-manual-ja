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
#doc (Manual) "Syntax" =>
-/
#doc (Manual) "構文（Syntax）" =>
%%%
tag := "string-syntax"
%%%

:::comment
Lean has three kinds of string literals: ordinary string literals, interpolated string literals, and raw string literals.

:::

Lean には3種類の文字列リテラルがあります：通常の文字列リテラル・補間文字列リテラル・生文字列リテラル

:::comment
# String Literals
%%%
tag := "string-literals"
%%%

:::

# 文字列リテラル（String Literals）

:::comment
String literals begin and end with a double-quote character `"`. {index subterm:="string"}[literal]
Between these characters, they may contain any other character, including newlines, which are included literally (with the caveat that all newlines in a Lean source file are interpreted as `'\n'`, regardless of file encoding and platform).
Special characters that cannot otherwise be written in string literals may be escaped with a backslash, so `"\"Quotes\""` is a string literal that begins and ends with double quotes.
The following forms of escape sequences are accepted:

:::

文字列リテラルはダブルクォート文字 `"` で開始・終了します。 {index subterm:="string"}[literal] これらの文字の間には、改行文字を（文字通り）含む他の任意の文字を含めることができます（ただし、Lean ソースファイル内のすべての改行文字はファイルのエンコーディングやプラットフォームに関係なく `'\n'` として解釈されます）。文字列リテラルにかけない特殊文字はバックスラッシュでエスケープすることができるため、 `"\"Quotes\""` は二重引用符で開始・終了する文字列リテラルです。以下の形式のエスケープシーケンスが利用できます：

:::comment
: `\r`, `\n`, `\t`, `\\`, `\"`, `\'`

  These escape sequences have the usual meaning, mapping to `CR`, `LF`, tab, backslash, double quote, and single quote, respectively.

:::

: `\r`・`\n`・`\t`・`\\`・`\"`・`\'`

  これらのエスケープシーケンスは通常の意味を持ち、それぞれ `CR`・`LF`・タブ・バックスラッシュ・二重引用符・引用符に対応します。

:::comment
: `\xNN`

  When `NN` is a sequence of two hexadecimal digits, this escape denotes the character whose Unicode code point is indicated by the two-digit hexadecimal code.

:::

: `\xNN`

  `NN` が2桁の16進数である時、このエスケープは2桁の16進数で示される Unicode コードポイントを持つ文字を表します。

:::comment
: `\uNNNN`

  When `NN` is a sequence of two hexadecimal digits, this escape denotes the character whose Unicode code point is indicated by the four-digit hexadecimal code.


:::

: `\uNNNN`

  `NN` が2桁の16進数である時、このエスケープは4桁の16進数コードで示される Unicode コードポイントを持つ文字を表します。

:::comment
String literals may contain {deftech}[_gaps_].
A gap is indicated by an escaped newline, with no intervening characters between the escaping backslash and the newline.
In this case, the string denoted by the literal is missing the newline and all leading whitespace from the next line.
String gaps may not precede lines that contain only whitespace.

:::

文字列リテラルは {deftech}[_ギャップ_] （gap）を含むことができます。ギャップはエスケープされた開業で示され、エスケープされたバックスラッシュと改行の間には文字が介在しません。この場合、リテラルで示される文字列には、改行と次の行の先頭の空白がすべて含まれません。文字列のギャップは空白のみを含む行の前にあってはなりません。

:::comment
Here, `str1` and `str2` are the same string:
:::



```lean
def str1 := "String with \
             a gap"
def str2 := "String with a gap"

example : str1 = str2 := rfl
```

:::comment
If the line following the gap is empty, the string is rejected:

:::

ギャップに続く行が空の場合、その文字列は拒否されます：

```syntaxError foo
def str3 := "String with \

             a gap"
```
:::comment
The parser error is:
:::

パーサは以下のエラーを返します：

```leanOutput foo
<example>:2:0: unexpected additional newline in string gap
```

:::comment
# Interpolated Strings
%%%
tag := "string-interpolation"
%%%

:::

# 補間文字列（Interpolated Strings）

:::comment
Preceding a string literal with `s!` causes it to be processed as an {deftech}[_interpolated string_], in which regions of the string surrounded by `{` and `}` characters are parsed and interpreted as Lean expressions.
Interpolated strings are interpreted by appending the string that precedes the interpolation, the expression (with an added call to {name ToString.toString}`toString` surrounding it), and the string that follows the interpolation.

:::

文字列の前に `s!` を置くと、 {deftech}[_補間文字列_] （interpolated string）として処理されます。この文字列内の `{` と `}` で囲まれた領域がパースされ、Lean の式として解釈されます。補間文字列は、補間の前の文字列・式（それを囲む {name ToString.toString}`toString` の呼び出しが追加されたもの）・補間後の文字列が連結されたものとして解釈されます。

:::comment
For example:
:::

例えば：

```lean
example : s!"1 + 1 = {1 + 1}\n" = "1 + 1 = " ++ toString (1 + 1) ++ "\n" := rfl
```

:::comment
Preceding a literal with `m!` causes the interpolation to result in an instance of {name Lean.MessageData}`MessageData`, the compiler's internal data structure for messages to be shown to users.

:::

リテラルの前に `m!` を置くと、 {name Lean.MessageData}`MessageData` のインスタンスとなります。これはコンパイラの内部からユーザ向けに使用されるメッセージのデータ構造です。

:::comment
# Raw String Literals
%%%
tag := "raw-string-literals"
%%%

:::

# 生文字列リテラル

:::comment
In {deftech}[raw string literals], {index subterm:="raw string"}[literal] there are no escape sequences or gaps, and each character denotes itself exactly.
Raw string literals are preceded by `r`, followed by zero or more hash characters (`#`) and a double quote `"`.
The string literal is completed at a double quote that is followed by _the same number_ of hash characters.
For example, they can be used to avoid the need to double-escape certain characters:
:::

{deftech}[生文字列リテラル] {index subterm:="raw string"}[literal] （raw string literal）では、エスケープシーケンスやギャップはなく、各文字はそれ自身を正確に表します。生文字列リテラルは `r` で始まり、0個以上のハッシュ文字（`#`）と二重引用符 `"` が続きます。文字列リテラルは _同じ数_ のハッシュ文字が続く二重引用符で補完されます。例えば、特定の文字をダブルエスケープする必要を避けるために使用することができます：

```lean (name := evalStr)
example : r"\t" = "\\t" := rfl
#eval r"Write backslash in a string using '\\\\'"
```
:::comment
The `#eval` yields:
:::

この `#eval` は以下を出力します：

```leanOutput evalStr
"Write backslash in a string using '\\\\\\\\'"
```

:::comment
Including hash marks allows the strings to contain unescaped quotes:

:::

ハッシュ記号を含めると、文字列にエスケープされていない引用符を含めることができます。

```lean
example : r#"This is "literally" quoted"# = "This is \"literally\" quoted" := rfl
```

:::comment
Adding sufficiently many hash marks allows any raw literal to be written literally:

:::

十分な数のハッシュ記号を追加することで、どんな生リテラルでも文字通りに書くことができます：

```lean
example : r##"This is r#"literally"# quoted"## = "This is r#\"literally\"# quoted" := rfl
```
