/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.RecursiveDefs.Structural
import Manual.RecursiveDefs.WF

open Verso.Genre Manual
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option maxRecDepth 1500

/-
#doc (Manual) "Recursive Definitions" =>
-/
#doc (Manual) "再帰定義（Recursive Definitions）" =>
%%%
tag := "recursive-definitions"
%%%

:::comment
Allowing arbitrary recursive function definitions would make Lean's logic inconsistent.
General recursion makes it possible to write circular proofs: "{tech}[proposition] $`P` is true because proposition $`P` is true".
Outside of proofs, an infinite loop could be assigned the type {name}`Empty`, which can be used with {keywordOf Lean.Parser.Term.nomatch}`nomatch` or {name Empty.rec}`Empty.rec` to prove any theorem.

:::

任意の再帰関数定義を許してしまうと、Lean の論理は矛盾してしまいます。一般的な再帰は循環証明を書くことを可能にします：「 {tech}[命題] $`P` は真である、なぜなら命題 $`P` は真だからである」証明以外では、無限ループには {name}`Empty` 型を割り当てることが可能です。これは {keywordOf Lean.Parser.Term.nomatch}`nomatch` や {name Empty.rec}`Empty.rec` などと一緒に使うことで任意の定理を証明することができます。

:::comment
Banning recursive function definitions outright would render Lean far less useful: {tech}[inductive] types are key to defining both predicates and data, and they have a recursive structure.
Furthermore, most useful recursive functions do not threaten soundness, and infinite loops usually indicate mistakes in definitions rather than intentional behavior.
Instead of banning recursive functions, Lean requires that each recursive function is defined safely.
While elaborating recursive definitions, the Lean elaborator also produces a justification that the function being defined is safe.{margin}[The section on {ref "elaboration-results"}[the elaborator's output] in the overview of elaboration contextualizes the elaboration of recursive definitions in the overall context of the elaborator.]

:::

再帰関数定義を全面的に禁止した場合、Lean の有用性ははるかに低下してしまうでしょう： {tech}[帰納型] は述語とデータの両方を定義する鍵となる概念であり、再帰的な構造を持っています。さらに、ほとんどの有用な再帰関数は健全性を脅かすものではなく、無限ループは通常、意図的な動作ではなく定義の間違いを示しています。Lean では、再帰関数を禁止する代わりに、各再帰関数を安全に定義することを要求しています。再帰定義をエラボレートする際に、Lean のエラボレータはその関数が安全に定義されていることを示す正当性も提供します。 {margin}[エラボレーションの概要にある {ref "elaboration-results"}[エラボレータの出力] の節は、エラボレータの全体的な文脈の中で再帰定義のエラボレーションを説明しています。]

:::comment
There are four main kinds of recursive functions that can be defined:

:::

定義できる再帰関数には主に4種類あります：

:::comment
: Structurally recursive functions

  Structurally recursive functions take an argument such that the function makes recursive calls only on strict sub-components of said argument.{margin}[Strictly speaking, arguments whose types are {tech}[indexed families] are grouped together with their indices, with the whole collection considered as a unit.]
  The elaborator translates the recursion into uses of the argument's {tech}[recursor].
  Because every type-correct use of a recursor is guaranteed to avoid infinite regress, this translation is evidence that the function terminates.
  Applications of functions defined via recursors are definitionally equal to the result of the recursion, and are typically relatively efficient inside the kernel.

:::

: 構造的再帰関数

  構造的再帰関数は、関数が当該引数の厳密な部分コンポーネントに対してのみ再帰呼び出しを行うように引数を取ります。 {margin}[厳密に言えば、型が {tech}[添字族] である引数は、それらの添字と共にグループ化され、コレクション全体が1つの単位とみなされます。] エラボレータは再帰を引数の {tech}[再帰子] の使用に変換します。型が正しい再帰子の使用は、すべての無限後退を回避することが保証されているため、この変換は関数が停止する根拠となります。再帰子を介して定義された関数の適用は定義上は再帰の結果と等しく、カーネル内部において通常は比較的効率的です。

:::comment
: Recursion over well-founded relations

  Many functions are also difficult to convert to structural recursion; for instance, a function may terminate because the difference between an array index and the size of the array decreases as the index increases, but {name}`Nat.rec` isn't applicable because the index that increases is the function's argument.
  Here, there is a {tech}[measure] of termination that decreases at each recursive call, but the measure is not itself an argument to the function.
  In these cases, {tech}[well-founded recursion] can be used to define the function.
  Well-founded recursion is a technique for systematically transforming recursive functions with a decreasing measure into recursive functions over proofs that every sequence of reductions to the measure eventually terminates at a minimum.
  Applications of functions defined via well-founded recursion are not necessarily definitionally equal to their return values, but this equality can be proved as a proposition.
  Even when definitional equalities exist, these functions are frequently slow to compute with because they require reducing proof terms that are often very large.

:::

: 整礎関係上の再帰

  多くの関数は構造的再帰へと変換することも難しいです；例えば、ある関数について引数の配列のインデックスと配列のサイズの差がインデックスが増加するにつれて減少するような場合、この関数は停止できますが、 {name}`Nat.rec` は、増加するインデックスが関数の引数であるため適用することができません。ここでは、再帰呼び出しのたびに減少する停止のための {tech}[測度] がありますが、この測度自体は関数の引数ではありません。このような場合、 {tech}[well-founded recursion] を使って関数を定義することができます。整礎再帰は、何かしらの測度が減少する再帰関数を、測度の簡約のすべての列が最終的に最小値で終了する証明上に定義される再帰関数へと体系的に変換する技術です。整礎再帰によって定義された関数適用とその戻り値と必ずしも定義上等しいとは限りませんが、この等しさは命題として証明することができます。定義上等しい場合であっても、これらの関数はしばしば非常に大きい証明項を簡約する必要があるため、計算に時間がかかることが多いです。

:::comment
: Partial functions with nonempty ranges

  For many applications, it's not important to reason about the implementation of certain functions.
  A recursive function might be used only as part of the implementation of proof automation steps, or it might be an ordinary program that will never be formally proved correct.
  In these cases, the Lean kernel does not need either definitional or propositional equalities to hold for the definition; it suffices that soundness is maintained.
  Functions marked {keywordOf Lean.Parser.Command.declaration}`partial` are treated as opaque constants by the kernel and are neither unfolded nor reduced.
  All that is required for soundness is that their return type is inhabited.
  Partial functions may still be used in compiled code as usual, and they may appear in propositions and proofs; their equational theory in Lean's logic is simply very weak.

:::

: 空でない値域での部分関数

  多くのアプリケーションでは、特定の関数の実装を推論することは重要ではありません。ある再帰関数は、証明の自動化ステップの実装の一部としてのみ使用されるかもしれず、形式的に正しいことが証明されることのない普通のプログラムかもしれません。このような場合、Lean のカーネルは定義や命題上の等価性の成立を必要としません；健全性が維持されていれば十分とします。 {keywordOf Lean.Parser.Command.declaration}`partial` とマークされた関数は、カーネルによって不透明な定数として扱われ、展開も簡約もされません。健全性を保つために必要なことはその戻り値が存在することです。部分関数は通常通りコンパイルされたコードで使用することができ、命題や証明に出現させることができます；これらの Lean の論理における等価性の理論は非常に弱いものになります。

:::comment
: Unsafe recursive definitions

  Unsafe definitions have none of the restrictions of partial definitions.
  They may freely make use of general recursion, and they may use features of Lean that break assumptions about its equational theory, such as primitives for casting ({name}`unsafeCast`), checking pointer equality ({name}`ptrAddrUnsafe`), and observing {tech}[reference counts] ({name}`isExclusiveUnsafe`).
  However, any declaration that refers to an unsafe definition must itself be marked {keywordOf Lean.Parser.Command.declaration}`unsafe`, making it clear when logical soundness is not guaranteed.
  Unsafe operations can be used to replace the implementations of other functions with more efficient variants in compiled code, while the kernel still uses the original definition.
  The replaced function may be opaque, which results in the function name having a trivial equational theory in the logic, or it may be an ordinary function, in which case the function is used in the logic.
  Use this feature with care: logical soundness is not at risk, but the behavior of programs written in Lean may diverge from their verified logical models if the unsafe implementation is incorrect.


:::

: 安全ではない再帰定義

  安全ではない定義には部分定義のような制限はありません。一般的な再帰を自由に使用することができ、キャストのためのプリミティブ（ {name}`unsafeCast` ）・ポインタの等価性のチェック（ {name}`ptrAddrUnsafe` ）・ {tech}[reference counts] の観察（ {name}`isExclusiveUnsafe` ）など、Lean の等価理論の仮定を破る機能を使用することができます。しかし、安全ではない定義を参照する任意の宣言は、それ自身が {keywordOf Lean.Parser.Command.declaration}`unsafe` とマークされなければならず、これによってその定義は論理的な健全性が保証されていないことが明確になります。安全ではない操作は、カーネルがもとの定義を使用したまま、コンパイルされたコードで他の関数の実装をより効率的な変種に置き換えるために使用できます。置換された関数は、その関数名が論理内で自明な等価の理論を持つ不透明なものになるか、その関数がその論理内で使われる場合には普通の関数となります。この機能を使用する際には注意が必要です：論理的な健全性は損なわれませんが、安全でない実装が正しくない場合、Lean で記述されたプログラムの動作が検証済みの論理モデルと乖離する可能性があります。

:::comment
As described in the {ref "elaboration-results"}[overview of the elaborator's output], elaboration of recursive functions proceeds in two phases:
:::

{ref "elaboration-results"}[エラボレータの出力の概要] で説明したように、再帰関数のエラボレーションは2つのフェーズで進行します：

:::comment
 1. The definition is elaborated as if Lean's core type theory had recursive definitions.
    Aside from using recursion, this provisional definition is fully elaborated.
    The compiler generates code from these provisional definitions.

:::

 1. 定義は Lean のコア型理論に再帰定義があるかのようにエラボレートされます。再帰の使用とは別に、この仮定義は完全にエラボレートされます。コンパイラはこの仮定義からコードを生成します。

:::comment
 2. A termination analysis attempts to use the four techniques to justify the function to Lean's kernel.
    If the definition is marked {keywordOf Lean.Parser.Command.declaration}`unsafe` or {keywordOf Lean.Parser.Command.declaration}`partial`, then that technique is used.
    If an explicit {keywordOf Lean.Parser.Command.declaration}`termination_by` clause is present, then the indicated technique is the only one attempted.
    If there is no such clause, then the elaborator performs a search, testing each parameter to the function as a candidate for structural recursion, and attempting to find a measure with a well-founded relation that decreases at each recursive call.

:::

 2. 停止性の分析では、4つの技法を使って Lean のカーネルに関数を正当化しようとします。定義が {keywordOf Lean.Parser.Command.declaration}`unsafe` または {keywordOf Lean.Parser.Command.declaration}`partial` とマークされている場合、この技法が使用されます。明示的な {keywordOf Lean.Parser.Command.declaration}`termination_by` 節が存在する場合、指定された技法のみが試みられます。この節がない場合、エラボレータは探索を実行し、構造的再帰の候補として関数への各パラメータをテストし、各再帰呼び出しで減少する整礎関係を持つ測度を見つけようとします。

:::comment
This section describes the rules that govern recursive functions.
After a description of mutual recursion, each of the four kinds of recursive definitions is specified, along with the tradeoffs between reasoning power and flexibility that go along with each.
:::

本節では再帰関数を支配する規則について説明します。相互再帰についての記述の後に、4種類の再帰定義それぞれについて、推論の機能性と柔軟性のトレードオフについて説明します。

# Mutual Recursion
%%%
tag := "mutual-syntax"
%%%

Just as a recursive definition is one that mentions the name being defined in the body of the definition, {deftech}_mutually recursive_ definitions are definitions that may be recursive or mention one another.
To use mutual recursion between multiple declarations, they must be placed in a {deftech}[mutual block].

:::syntax command (title := "Mutual Declaration Blocks")
The general syntax for mutual recursion is:

```grammar
mutual
  $[$declaration:declaration]*
end
```
where the declarations must be definitions or theorems.
:::

The declarations in a mutual block are not in scope in each others' signatures, but they are in scope in each others' bodies.
Even though the names are not in scope in signatures, they will not be inserted as auto-bound implicit parameters.

:::example "Mutual Block Scope"
Names defined in a mutual block are not in scope in each others' signatures.

```lean (error := true) (name := mutScope) (keep := false)
mutual
  abbrev NaturalNum : Type := Nat
  def n : NaturalNum := 5
end
```
```leanOutput mutScope
unknown identifier 'NaturalNum'
```

Without the mutual block, the definition succeeds:
```lean
abbrev NaturalNum : Type := Nat
def n : NaturalNum := 5
```
:::

:::example "Mutual Block Scope and Automatic Implicit Parameters"
Names defined in a mutual block are not in scope in each others' signatures.
Nonetheless, they cannot be used as automatic implicit parameters:

```lean (error := true) (name := mutScopeTwo) (keep := false)
mutual
  abbrev α : Type := Nat
  def identity (x : α) : α := x
end
```
```leanOutput mutScopeTwo
unknown identifier 'α'
```

With a different name, the implicit parameter is automatically added:
```lean
mutual
  abbrev α : Type := Nat
  def identity (x : β) : β := x
end
```
:::

Elaborating recursive definitions always occurs at the granularity of mutual blocks, as if there were a singleton mutual block around every declaration that is not itself part of such a block.
Local definitions introduced via {keywordOf Lean.Parser.Term.letrec}`let rec` and
 {keywordOf Lean.Parser.Command.declaration}`where` are lifted out of their context, introducing parameters for captured free variables as necessary, and treated as if they were separate definitions within the {keywordOf Lean.Parser.Command.mutual}`mutual` block as well. {TODO}[Explain this mechanism in more detail, here or in the term section.]
Thus, helpers defined in a {keywordOf Lean.Parser.Command.declaration}`where` block may use mutual recursion both with one another and with the definition in which they occur, but they may not mention each other in their type signatures.

After the first step of elaboration, in which definitions are still recursive, and before translating recursion using the techniques above, Lean identifies the actually (mutually) recursive cliques{TODO}[define this term, it's useful]  among the definitions in the mutual block and processes them separately and in dependency order.

{include 0 Manual.RecursiveDefs.Structural}

{include 0 Manual.RecursiveDefs.WF}

# Partial and Unsafe Recursive Definitions
%%%
tag := "partial-unsafe"
%%%

:::planned 59
This section will describe `partial` and `unsafe` definitions:


 * Interaction with the kernel and elaborator
 * What guarantees are there, and what aren't there?
 * How to bridge from unsafe to safe code?

:::

# Controlling Reduction

:::planned 58
This section will describe {deftech}_reducibility_: {deftech}[reducible], {deftech}[semi-reducible], and {deftech}[irreducible] definitions.
:::
