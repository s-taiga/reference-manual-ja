/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta

/-!
This is extracted into its own file because line numbers show up in the error message, and we don't
want to update it over and over again as we edit the large file.
-/

open Verso.Genre Manual
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Termination failure (for inclusion elsewhere)" =>

:::comment
::example "Termination failure"
:::
::::example "停止の失敗"

:::comment
If there is no {keywordOf Lean.Parser.Command.declaration}`termination_by` clause, Lean attempts to infer a measure for well-founded recursion.
If it fails, then it prints the table mentioned above.
In this example, the {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause simply prevents Lean from also attempting structural recursion; this keeps the error message specific.

:::

{keywordOf Lean.Parser.Command.declaration}`termination_by` 句が無い場合、Lean は整礎再帰のための測度を推測しようとします。失敗した場合、前述の表を出力します。この例では {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 句によって Lean の構造的再帰の推測が阻害されます；これによってエラーメッセージが特定されます。

```lean (error := true) (keep := false) (name := badwf)
def f : (n m l : Nat) → Nat
  | n+1, m+1, l+1 => [
      f (n+1) (m+1) (l+1),
      f (n+1) (m-1) (l),
      f (n)   (m+1) (l) ].sum
  | _, _, _ => 0
decreasing_by all_goals decreasing_tactic
```
```leanOutput badwf (whitespace := lax)
Could not find a decreasing measure.
The arguments relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
           n m l
1) 38:6-25 = = =
2) 39:6-23 = < _
3) 40:6-23 < _ _
Please use `termination_by` to specify a decreasing measure.
```
:::comment
```leanOutput badwf (whitespace := lax)
Could not find a decreasing measure.
The arguments relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
           n m l
1) 30:6-25 = = =
2) 31:6-23 = < _
3) 32:6-23 < _ _
Please use `termination_by` to specify a decreasing measure.
```
:::

:::comment
The three recursive calls are identified by their source positions.
This message conveys the following facts:

:::

この3つの再帰呼び出しは、呼び出し元の位置によって識別されます。このメッセージは以下の事実を伝えています：

:::comment
* In the first recursive call, all arguments are (provably) equal to the parameters
* In the second recursive call, the first argument is equal to the first parameter and the second argument is provably smaller than the second parameter.
  The third parameter was not checked for this recursive call, because it was not necessary to determine that no suitable termination argument exists.
* In the third recursive call, the first argument decreases strictly, and the other arguments were not checked.

:::

* 最初の再帰呼び出しでは、すべての引数はパラメータと（証明的に）等価です。
* 2回目の再帰呼び出しでは、第1引数は第1パラメータに等しく、第2引数は第2パラメータよりも証明的に小さいです。第3パラメータはこの再帰呼び出しではチェックされません。なぜなら適切な停止引数が存在しないことを判断する必要がないためです。
* 3回目の再帰呼び出しでは、第1引数は厳密に減少し、他の引数はチェックされませんでした。

:::comment
When termination proofs fail in this manner, a good technique to discover the problem is to explicitly indicate the expected termination argument using {keywordOf Lean.Parser.Command.declaration}`termination_by`.
This will surface the messages from the failing tactic.

:::

このように停止証明に失敗した場合、問題を発見するための良いテクニックは {keywordOf Lean.Parser.Command.declaration}`termination_by` を使って予想される停止引数を明示的に示すことです。これにより、失敗したタクティクからのメッセージが表示されます。

::::
