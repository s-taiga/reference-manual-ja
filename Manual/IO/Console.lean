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
#doc (Manual) "Console Output" =>
-/
#doc (Manual) "コンソール出力（Console Output）" =>

:::comment
Lean includes convenience functions for writing to {tech}[standard output] and {tech}[standard error].
All make use of {lean}`ToString` instances, and the varieties whose names end in `-ln` add a newline after the output.
These convenience functions only expose a part of the functionality available {ref "stdio"}[using the standard I/O streams].
In particular, to read a line from standard input, use a combination of {lean}`IO.getStdin` and {lean}`IO.FS.Stream.getLine`.

:::

Lean は {tech}[標準出力] と {tech}[標準エラー] に書き出すための便利な関数を有しています。それらは全て {lean}`ToString` インスタンスを使用し、そのうち名前が `-ln` で終わるものは出力の後に改行を追加します。これらの便利な関数は {ref "stdio"}[標準 I/O ストリームを使用する] 機能の一部しか公開していません。特に、標準入力から行を読むには、 {lean}`IO.getStdin` と {lean}`IO.FS.Stream.getLine` を組み合わせて使用します。

{docstring IO.print}

{docstring IO.println}

{docstring IO.eprint}

{docstring IO.eprintln}

:::comment
::example "Printing"
:::
:::::example "表示"
:::comment
This program demonstrates all four convenience functions for console I/O.

:::

このプログラムはコンソール I/O のための4つの便利な関数をすべて示しています。

::::ioExample
```ioLean
def main : IO Unit := do
  IO.print "This is the "
  IO.print "Lean"
  IO.println " language reference."
  IO.println "Thank you for reading it!"
  IO.eprint "Please report any "
  IO.eprint "errors"
  IO.eprintln " so they can be corrected."
```

:::comment
It outputs the following to the standard output:

:::

これは以下を標準出力に書き出します：

```stdout
This is the Lean language reference.
Thank you for reading it!
```

:::comment
and the following to the standard error:

:::

また以下を標準エラーに書き出します：

```stderr
Please report any errors so they can be corrected.
```
::::
:::::
