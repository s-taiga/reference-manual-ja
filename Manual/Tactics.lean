/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

import Manual.Tactics.Reference
import Manual.Tactics.Conv
import Manual.Tactics.Custom

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean.Elab.Tactic

/-
#doc (Manual) "Tactic Proofs" =>
-/
#doc (Manual) "タクティクによる証明（Tactic Proofs）" =>
%%%
tag := "tactics"
%%%

:::comment
The tactic language is a special-purpose programming language for constructing proofs.
In Lean, {tech}[propositions] are represented by types, and proofs are terms that inhabit these types.
{margin}[The {ref "propositions"}[section on propositions] describes propositions in more detail.]
While terms are designed to make it convenient to indicate a specific inhabitant of a type, tactics are designed to make it convenient to demonstrate that a type is inhabited.
This distinction exists because it's important that definitions pick out the precise objects of interest and that programs return the intended results, but proof irrelevance means that there's no _technical_ reason to prefer one proof term over another.
For example, given two assumptions of a given type, a program must be carefully written to use the correct one, while a proof may use either without consequence.

:::

タクティク言語は証明を構築するための特別な目的のプログラミング言語です。Lean では、 {tech}[命題] は型によって表現され、証明はこれらの型に住んでいる項です。 {margin}[命題については {ref "propositions"}[命題の節] で詳しく説明しています] 項が型の特定の住人を示すのに便利なように設計されているのに対して、タクティクは型に住人がいることを示すのに便利なように設計されています。この区別が存在するのは、定義では関心のある対象を正確に選び出してプログラムが意図した結果を返すことが重要ですが、証明の irrelevance によってある証明を別の証明の中から選りすぐる _技術的な_ 理由は無いからです。例えば、ある型の2つの仮定が与えられた時、プログラムは正しい方を使うように注意深く書かなければならない一方で、証明はどちらを使っても構いません。

:::comment
Tactics are imperative programs that modify a {deftech}_proof state_.{index}[proof state]
A proof state consists of an ordered sequence of {deftech}_goals_, which are contexts of local assumptions together with types to be inhabited; a tactic may either _succeed_ with a possibly-empty sequence of further goals (called {deftech}_subgoals_) or _fail_ if it cannot make progress.
If tactic succeeds with no subgoals, then the proof is complete.
If it succeeds with one or more subgoals, then its goal or goals will be proved when those subgoals have been proved.
The first goal in the proof state is called the {deftech}_main goal_.{index subterm:="main"}[goal]{index}[main goal]
While most tactics affect only the main goal, operators such as {tactic}`<;>` and {tactic}`all_goals` can be used to apply a tactic to many goals, and operators such as bullets, {tactic}`next` or {tactic}`case` can narrow the focus of subsequent tactics to only a single goal in the proof state.

:::

タクティクは {deftech}_証明状態_ （proof state）を修正する命令型プログラムです。証明状態は {deftech}_ゴール_ （goal）の順序付けられた列から構成されます。これは住人がいるべき型と一緒になった局所的な仮定のコンテキストです；タクティクはさらなるゴール（ {deftech}_サブゴール_ 、subgoal と呼ばれます）の空である可能性のある列によって _成功_ するか、処理が進まない場合は _失敗_ します。タクティクがサブゴールが無い状態で成功すれば証明は完了です。1つ以上のサブゴールで成功した場合、それらのサブゴールが証明された時にそのゴールが証明されます。証明状態における最初のゴールを {deftech}_メインゴール_ （main goal）と呼びます。 {index subterm:="main"}[goal]{index}[main goal] ほとんどのタクティクはメインゴールだけに影響しますが、 {tactic}`<;>` や {tactic}`all_goals` などの演算子は、タクティクを多くのゴールに適用するために使用することができ、ブレット・ {tactic}`next` ・ {tactic}`case` などの演算子は後続のタクティクの焦点を証明状態の単一のゴールだけに絞ることができます。

:::comment
Behind the scenes, tactics construct {deftech}[proof terms].
Proof terms are independently checkable evidence of a theorem's truth, written in Lean's type theory.
Each proof is checked in the {tech}[kernel], and can be verified with independently-implemented external checkers, so the worst outcome from a bug in a tactic is a confusing error message, rather than an incorrect proof.
Each goal in a tactic proof corresponds to an incomplete portion of a proof term.

:::

裏では、タクティクは {deftech}[証明項] を構築します。証明項とは、Lean の型理論で書かれた定理の真理について独立にチェック可能な根拠です。各証明は {tech}[カーネル] でチェックされ、独立に実装された外部チェッカで検証できるため、タクティクのバグによる最悪の結果は間違った照明ではなく混乱したエラーメッセージです。タクティク証明の各ゴールは証明項の不完全な部分に対応します。

:::comment
# Running Tactics
%%%
tag := "by"
%%%

:::

# タクティクの実行（Running Tactics）

:::TODO
The syntax of `by` is showing with commas instead of semicolons below
:::

::::syntax Lean.Parser.Term.byTactic
:::comment
Tactics are included in terms using {keywordOf Lean.Parser.Term.byTactic}`by`, which is followed by a sequence of tactics in which each has the same indentation:
:::

タクティクは {keywordOf Lean.Parser.Term.byTactic}`by` を使用して項に含まれ、その後に同じインデントを持つタクティクの列が続きます：

```grammar
by
$t
```

:::comment
Alternatively, explicit braces and semicolons may be used:
:::

あるいは、波括弧とセミコロンを明示的に使用することもできます：

```grammar
by { $t* }
```
::::

:::comment
Tactics are invoked using the {keywordOf Lean.Parser.Term.byTactic}`by` term.
When the elaborator encounters {keywordOf Lean.Parser.Term.byTactic}`by`, it invokes the tactic interpreter to construct the resulting term.
Tactic proofs may be embedded via {keywordOf Lean.Parser.Term.byTactic}`by` in any context in which a term can occur.

:::

タクティクは {keywordOf Lean.Parser.Term.byTactic}`by` 項を使って呼び出されます。エラボレータが {keywordOf Lean.Parser.Term.byTactic}`by` に遭遇すると、タクティクインタプリタを呼び出して結果の項を構築します。タクティクの証明は、項が出現しうる任意のコンテキストで {keywordOf Lean.Parser.Term.byTactic}`by` によって埋め込むことができます。

:::comment
# Reading Proof States
%%%
tag := "proof-states"
%%%

:::

# 証明状態の読み方（Reading Proof States）

:::comment
The goals in a proof state are displayed in order, with the main goal on top.
Goals may be either named or anonymous.
Named goals are indicated with `case` at the top (called a {deftech}_case label_), while anonymous goals have no such indicator.
Tactics assign goal names, typically on the basis of constructor names, parameter names, structure field names, or the nature of the reasoning step implemented by the tactic.

:::

証明状態にあるゴールはメインゴールを上にして順番に表示されます。ゴールには名前付きのものと匿名のものがあります。名前付きゴールは先頭に `case` と表示され（ {deftech}_ケースラベル_ 、case label と呼ばれます）、一方で匿名のゴールにはそのような表示はありません。タクティクは通常、コンストラクタ名・パラメータ名・構造体フィールド名・タクティクなどによって実装される推論ステップの性質に基づいて、ゴール名を割り当てます。

:::comment
::example "Named goals"
:::
:::::example "名前付きゴール"
```CSS
#lawful-option-cases .goal-name { background-color: var(--lean-compl-yellow); }
```

:::comment
This proof state contains four goals, all of which are named.
This is part of a proof that the {lean}`Monad Option` instance is lawful (that is, to provide the {lean}`LawfulMonad Option` instance), and the case names (highlighted below) come from the names of the fields of {name}`LawfulMonad`.

:::

この証明状態には4つのゴールが含まれ、そのすべてに名前が付けられています。これは {lean}`Monad Option` インスタンスが合法であること（つまり {lean}`LawfulMonad Option` インスタンスを提供すること）の証明の一部であり、ケース名（以下でハイライトしているもの）は {name}`LawfulMonad` のフィールド名に由来します。

```proofState tag:="lawful-option-cases"
LawfulMonad Option := by
constructor
intro α β f x
rotate_right
intro α β γ x f g
rotate_right
intro α β x f
rotate_right
intro α β f x
rotate_right
```
:::::


:::comment
::example "Anonymous Goals"
:::
:::::example "匿名のゴール"
:::comment
This proof state contains a single anonymous goal.

:::

この証明状態には1つの匿名ゴールが含まれています。

```proofState
∀ (n k : Nat), n + k = k + n := by
intro n k
```
:::::

:::comment
The {tactic}`case` and {tactic}`case'` tactics can be used to select a new main goal using the desired goal's name.
When names are assigned in the context of a goal which itself has a name, the new goals' names are appended to the main goal's name with a dot (`'.', Unicode FULL STOP (0x2e)`) between them.

:::

{tactic}`case` と {tactic}`case'` タクティクを使用すると、希望するゴール名を使用して新しいメインゴールを選択することができます。名前付きのゴールのコンテキストにて名前が割り当てられると、新しいゴールの名前はメインゴールの名前との間にドット（`'.'、Unicode FULL STOP (0x2e)`）を挟んだものとして追加されます。

:::comment
::example "Hierarchical Goal Names"
:::
:::::example "階層的なゴールの名前"

::::tacticExample
```setup
intro n k
induction n
```


:::comment
In the course of an attempt to prove {goal}`∀ (n k : Nat), n + k = k + n`, this proof state can occur:
:::

{goal}`∀ (n k : Nat), n + k = k + n` を証明しようとしている過程において、以下のような証明状態が起こりえます：

```pre
case zero
k : Nat
⊢ 0 + k = k + 0

case succ
k n✝ : Nat
a✝ : n✝ + k = k + n✝
⊢ n✝ + 1 + k = k + (n✝ + 1)
```

:::comment
After {tacticStep}`induction k`, the two new cases' names have `zero` as a prefix, because they were created in a goal named `zero`:

:::

{tacticStep}`induction k` の後、2つの新しいケースの名前は接頭辞として `zero` を持ちます。これはその名前のゴール内で作られたためです：

```CSS
#hierarchical-case-names .goal:not(:last-child) .goal-name { background-color: var(--lean-compl-yellow); }
```

```post tag:="hierarchical-case-names"
case zero.zero
⊢ 0 + 0 = 0 + 0

case zero.succ
n✝ : Nat
a✝ : 0 + n✝ = n✝ + 0
⊢ 0 + (n✝ + 1) = n✝ + 1 + 0

case succ
k n✝ : Nat
a✝ : n✝ + k = k + n✝
⊢ n✝ + 1 + k = k + (n✝ + 1)
```
::::
:::::


:::comment
Each goal consists of a sequence of assumptions and a desired conclusion.
Each assumption has a name and a type; the conclusion is a type.
Assumptions are either arbitrary elements of some type or statements that are presumed true.

:::

各ゴールは一連の仮定と期待される結論から構成されます。それぞれの仮定には名前と型があります；結論は型です。仮定はある型の任意の要素か、真であると推定される文のどちらかです。

:::comment
::example "Assumption Names and Conclusion"
:::
:::::example "仮定の名前と結論"

```CSS
#ex-assumption-names .hypothesis .name { background-color: var(--lean-compl-yellow); }
```

:::comment
This goal has four assumptions:

:::

このゴールは4つの仮定を持ちます：

```proofState tag:="ex-assumption-names"
∀ (α) (xs : List α), xs ++ [] = xs := by
intro α xs
induction xs
sorry
rename_i x xs ih
```

::::keepEnv
```lean show:=false
axiom α : Type
axiom x : α
axiom xs : List α
axiom ih : xs ++ [] = xs
```

:::comment
They are:

:::

これらはそれぞれ：

:::comment
 * {lean}`α`, an arbitrary type
 * {lean}`x`, an arbitrary {lean}`α`
 * {lean}`xs`, an arbitrary {lean}`List α`
 * {lean}`ih`, an induction hypothesis that asserts that appending the empty list to {lean}`xs` is equal to {lean}`xs`.

:::

 * {lean}`α` 、任意の型
 * {lean}`x` 、 {lean}`α` 型の任意の値
 * {lean}`xs` 、 {lean}`List α` 型の任意の値
 * {lean}`ih` 、帰納法の仮定で、これは空のリストを {lean}`xs` に追加したものが {lean}`xs` と等しいことを主張します。

:::comment
The conclusion is the statement that prepending `x` to both sides of the equality in the induction hypothesis results in equal lists.
:::

結論は、帰納法の仮定の等号の両辺に `x` を先頭に追加すると等しいリストになるという文です。

::::

:::::

:::comment
Some assumptions are {deftech}_inaccessible_, {index}[inaccessible] {index subterm:="inaccessible"}[assumption] which means that they cannot be referred to explicitly by name.
Inaccessible assumptions occur when an assumption is created without a specified name or when the assumption's name is shadowed by a later assumption.
Inaccessible assumptions should be regarded as anonymous; they are presented as if they had names because they may be referred to in later assumptions or in the conclusion, and displaying a name allows these references to be distinguished from one another.
In particular, inaccessible assumptions are presented with daggers (`†`) after their names.


:::

いくつかの仮定は {deftech}_アクセス不能_ {index}[inaccessible] {index subterm:="inaccessible"}[assumption] （inaccessible）です。これは名前によって明示的に参照できないことを意味します。アクセス不能な仮定は、仮定が指定された名前なしで作成された時、または仮定の名前がそれより後に作られた仮定によってシャドーイングされた時に発生します。アクセス不能な仮定は匿名とみなされるべきです；それらが名前を持っているかのように表示されるのは、それらが後の仮定または結論で参照される可能性があり、名前を表示することでこれらの参照を互いに区別することができるからです。特に、アクセス不能な仮定には、その名前の後に短剣（`†`）が表示されます。

:::comment
::example "Accessible Assumption Names"
:::
::::example "アクセス可能な仮定の名前"
```CSS
#option-cases-accessible .hypothesis .name { background-color: var(--lean-compl-yellow); }
```

:::comment
In this proof state, all assumptions are accessible.

:::

この証明状態では、すべての仮定がアクセス可能です。

```proofState tag:="option-cases-accessible"
LawfulMonad Option := by
constructor
intro α β f x
rotate_right
sorry
rotate_right
sorry
rotate_right
sorry
rotate_right
```
::::


:::comment
::example "Inaccessible Assumption Names"
:::
:::::example "アクセス不能な仮定の名前"
```CSS
#option-cases-inaccessible .hypotheses .hypothesis:nth-child(even) .name { background-color: var(--lean-compl-yellow); }
```

:::comment
In this proof state, only the first and third assumptions are accessible.
The second and fourth are inaccessible, and their names include a dagger to indicate that they cannot be referenced.

:::

この証明状態では1つ目と3つ目の仮定だけがアクセス可能です。2番目と4番目はアクセス不能であり、その名前には参照できないことを示す短剣が含まれています。

```proofState tag:="option-cases-inaccessible"
LawfulMonad Option := by
constructor
intro α _ f _
rotate_right
sorry
rotate_right
sorry
rotate_right
sorry
rotate_right
```
:::::


:::comment
Inaccessible assumptions can still be used.
Tactics such as {tactic}`assumption` or {tactic}`simp` can scan the entire list of assumptions, finding one that is useful, and {tactic}`contradiction` can eliminate the current goal by finding an impossible assumption without naming it.
Other tactics, such as {tactic}`rename_i` and {tactic}`next`, can be used to name inaccessible assumptions, making them accessible.
Additionally, assumptions can be referred to by their type, by writing the type in single guillemets.

:::

アクセス不能な仮定はそれでもなお使用することができます。 {tactic}`assumption` や {tactic}`simp` などのタクティクは、仮定のリスト全体をスキャンし、有用なものを見つけることができ、 {tactic}`contradiction` は名前を付けずに不可能な仮定を見つけることで現在のゴールを除去することができます。その他のタクティク、例えば {tactic}`rename_i` と {tactic}`next` はアクセス不能な仮定に名前を付け、アクセス可能にするために使用できます。さらに、仮定はその型を単一のギュメで書くことによって、その型から参照することができます。

:::::syntax term
:::comment
Single guillemets around a term represent a reference to some term in scope with that type.

:::

項を囲む単一のキュメはその型を持つスコープ内の項への参照を表します。

```grammar
‹$t›
```

:::comment
This can be used to refer to local lemmas by their theorem statement rather than by name, or to refer to assumptions regardless of whether they have explicit names.
:::

これは名前ではなく定理文によってローカルの補題を参照したり、明示的な名前の有無に関係なく仮定を参照したりするのに使うことができます。

:::::

:::comment
::example "Assumptions by Type"
:::
:::::example "型による仮定"

::::keepEnv
```lean
variable (n : Nat)
```
:::comment
In the following proof, {tactic}`cases` is repeatedly used to analyze a number.
At the beginning of the proof, the number is named `x`, but {tactic}`cases` generates an inaccessible name for subsequent numbers.
Rather than providing names, the proof takes advantage of the fact that there is a single assumption of type {lean}`Nat` at any given time and uses {lean}`‹Nat›` to refer to it.
After the iteration, there is an assumption that `n + 3 < 3`, which {tactic}`contradiction` can use to remove the goal from consideration.
:::


以下の証明において、 {tactic}`cases` は数を解析するために繰り返し使用されています。証明の最初では、数は `x` という名前ですが、 {tactic}`cases` はそれ以降の数に対してアクセス不能な名前を生成します。名前を提供する代わりに、証明は任意の時点で {lean}`Nat` 型の仮定が1つ存在するという事実を利用し、それを参照するために {lean}`‹Nat›` を使用します。繰り返しののち、`n + 3 < 3` という仮定が残り、これは {tactic}`contradiction` を使うことでゴールを考慮から除くことができます。
::::

```lean
example : x < 3 → x ∈ [0, 1, 2] := by
  intros
  iterate 3
    cases ‹Nat›
    . decide
  contradiction
```
:::::

:::comment
::example "Assumptions by Type, Outside Proofs"
:::
:::::example "型による仮定（証明以外）"

:::comment
Single-guillemet syntax also works outside of proofs:

:::

単一のギュメ構文は証明以外でも帰納します：

```lean name:=evalGuillemets
#eval
  let x := 1
  let y := 2
  ‹Nat›
```
```leanOutput evalGuillemets
2
```

:::comment
This is generally not a good idea for non-propositions, however—when it matters _which_ element of a type is selected, it's better to select it explicitly.
:::

しかし、これは非命題に対しては一般的に良いアイデアではありません。ある型の _どの_ 要素が選択されるかが重要な場合は明示的に選択する方が良いでしょう。

:::::

:::comment
## Hiding Proofs and Large Terms
%%%
tag := "hiding-terms-in-proof-states"
%%%

:::

## 証明と大きな項の非表示（Hiding Proofs and Large Terms）

:::comment
Terms in proof states can be quite big, and there may be many assumptions.
Because of definitional proof irrelevance, proof terms typically give little useful information.
By default, they are not shown in goals in proof states unless they are {deftech}_atomic_, meaning that they contain no subterms.
Hiding proofs is controlled by two options: {option}`pp.proofs` turns the feature on and off, while {option}`pp.proofs.threshold` determines a size threshold for proof hiding.

:::

証明状態の項は非常に大きくなることがあり、多くの仮定が存在することもあります。定義上の証明の irrelevance により通常、証明項はほとんど有用な情報を与えません。デフォルトでは、 {deftech}_アトミック_ でない限り、証明状態のゴールには表示されません。アトミックとは部分項を持たないことを意味します。証明の非表示は2つのオプションで制御できます： {option}`pp.proofs` はこの機能のオン・オフを切り替え、 {option}`pp.proofs.threshold` は証明の非表示のサイズ閾値を決定します。

:::comment
::example "Hiding Proof Terms"
:::
::::example "証明項の非表示"
:::comment
In this proof state, the proof that `0 < n` is hidden.

:::

この証明状態において、`0 < n` の証明は非表示になっています。

```proofState
∀ (n : Nat) (i : Fin n), i.val > 5 → (⟨0, by cases i; omega⟩ : Fin n) < i := by
  intro n i gt
/--
n : Nat
i : Fin n
gt : ↑i > 5
⊢ ⟨0, ⋯⟩ < i
-/

```
::::



{optionDocs pp.proofs}

{optionDocs pp.proofs.threshold}


:::comment
Additionally, non-proof terms may be hidden when they are too large.
In particular, Lean will hide terms that are below a configurable depth threshold, and it will hide the remainder of a term once a certain amount in total has been printed.
Showing deep terms can enabled or disabled with the option {option}`pp.deepTerms`, and the depth threshold can be configured with the option {option}`pp.deepTerms.threshold`.
The maximum number of pretty printer steps can be configured with the option {option}`pp.maxSteps`.
Printing very large terms can lead to slowdowns or even stack overflows in tooling; please be conservative when adjusting these options' values.

:::

さらに、非証明項が大きすぎる場合は非表示にすることができます。特に、Lean は一定の深さの閾値（設定可能）以下の項を非表示にし、合計が一定量表示されると残りの項を非表示にします。深い項の表示の有効・無効はオプション {option}`pp.deepTerms` で、深さの閾値はオプション {option}`pp.deepTerms.threshold` で設定できます。プリティプリンタの最大ステップ数はオプション {option}`pp.maxSteps` で設定できます。非常に大きな項の表示はツールの速度低下を招き、スタックオーバーフローになることもあります；これらのオプションの値を調整する時は控えめになるようにしましょう。

{optionDocs pp.deepTerms}

{optionDocs pp.deepTerms.threshold}

{optionDocs pp.maxSteps}

:::comment
## Metavariables
%%%
tag := "metavariables-in-proofs"
%%%

:::

## メタ変数（Metavariables）

:::comment
Terms that begin with a question mark are _metavariables_ that correspond to an unknown value.
They may stand for either {tech}[universe] levels or for terms.
Some metavariables arise as part of Lean's elaboration process, when not enough information is yet available to determine a value.
These metavariables' names have a numeric component at the end, such as `?m.392` or `?u.498`.
Other metavariables come into existence as a result of tactics or {tech}[synthetic holes].
These metavariables' names do not have a numeric component.
Metavariables that result from tactics frequently appear as goals whose {tech}[case labels] match the name of the metavariable.


:::

疑問符で始まる項は未知の値に対応する _メタ変数_ （metavariable）です。これらは {tech}[宇宙] レベルか項のいずれかを表すこともあります。メタ変数の中には、Lean のエラボレーションプロセスの一環として、値を決定するのに十分な情報が得られていないときに生じるものがあります。このようなメタ変数の名前の最後には `?m.392` や `?u.498` のように数字が付きます。その他のメタ変数はタクティクや {tech}[named holes] の結果として存在するようになります。これらのメタ変数の名前には数字の要素はありません。タクティクの結果として生じるメタ変数は {tech}[ケースラベル] がメタ変数の名前と一致するゴールとして現れることが多いです。

:::comment
::example "Universe Level Metavariables"
:::
:::::example "宇宙レベルのメタ変数"
:::comment
In this proof state, the universe level of `α` is unknown:
:::

この証明状態において、宇宙レベル `α` は不明です：

```proofState
∀ (α : _) (x : α) (xs : List α), x ∈ xs → xs.length > 0 := by
  intros α x xs elem
/--
α : Type ?u.891
x : α
xs : List α
elem : x ∈ xs
⊢ xs.length > 0
-/

```
:::::

:::comment
::example "Type Metavariables"
:::
:::::example "型メタ変数"
:::comment
In this proof state, the type of list elements is unknown.
The metavariable is repeated because the unknown type must be the same in both positions.
:::

この証明状態において、リスト要素の型は不明です。このメタ変数は繰り返し出現しています。これはこの不明な型が両方の位置で同じ出なければならないからです。

```proofState
∀ (x : _) (xs : List _), x ∈ xs → xs.length > 0 := by
  intros x xs elem
/--
x : ?m.1035
xs : List ?m.1035
elem : x ∈ xs
⊢ xs.length > 0
-/



```
:::::


:::comment
::example "Metavariables in Proofs"
:::
:::::example "証明におけるメタ変数"

::::tacticExample

{goal show:=false}`∀ (i j k  : Nat), i < j → j < k → i < k`

```setup
  intros i j k h1 h2
```

:::comment
In this proof state,
:::

この証明状態において、

```pre
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < k
```
:::comment
applying the tactic {tacticStep}`apply Nat.lt_trans` results in the following proof state, in which the middle value of the transitivity step `?m` is unknown:
:::

タクティク {tacticStep}`apply Nat.lt_trans` を適用すると、以下のような証明状態になり、推移性ステップの中間値 `?m` が不明となります：

```post
case h₁
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < ?m

case a
i j k : Nat
h1 : i < j
h2 : j < k
⊢ ?m < k

case m
i j k : Nat
h1 : i < j
h2 : j < k
⊢ Nat
```
::::
:::::

:::comment
::example "Explicitly-Created Metavariables"
:::
:::::example "明示的に作成されたメタ変数"
::::tacticExample
{goal show:=false}`∀ (i j k  : Nat), i < j → j < k → i < k`

```setup
  intros i j k h1 h2
```

:::comment
Explicit named holes are represented by metavariables, and additionally give rise to proof goals.
In this proof state,
:::

明示的な名前付きホールはメタ変数で表現され、さらに証明ゴールを生みます。この証明状態において、

```pre
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < k
```
:::comment
applying the tactic {tacticStep}`apply @Nat.lt_trans i ?middle k ?p1 ?p2` results in the following proof state, in which the middle value of the transitivity step `?middle` is unknown and goals have been created for each of the named holes in the term:
:::

ここでタクティク {tacticStep}`apply @Nat.lt_trans i ?middle k ?p1 ?p2` を適用すると、以下のような証明状態になります。このとき、推移性ステップの中間値 `?middle` は不明であり、項内の名前付きホールのそれぞれに対してゴールが作成されています。

```post
case middle
i j k : Nat
h1 : i < j
h2 : j < k
⊢ Nat

case p1
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < ?middle

case p2
i j k : Nat
h1 : i < j
h2 : j < k
⊢ ?middle < k
```
::::
:::::

:::comment
The display of metavariable numbers can be disabled using the {option}`pp.mvars`.
This can be useful when using features such as {keywordOf Lean.guardMsgsCmd}`#guard_msgs` that match Lean's output against a desired string, which is very useful when writing tests for custom tactics.

:::

メタ変数の番号の表示はオプション {option}`pp.mvars` を使うことで無効にできます。これは {keywordOf Lean.guardMsgsCmd}`#guard_msgs` のような Lean の出力と希望する文字列をマッチさせる機能を使うときに便利です。さらにカスタムのタクティクに対するテストを書くときに非常に便利です。

{optionDocs pp.mvars}


:::planned 68
Demonstrate and explain diff labels that show the difference between the steps of a proof state.
:::

:::comment
# The Tactic Language
%%%
tag := "tactic-language"
%%%

:::

# タクティク言語（The Tactic Language）

:::comment
A tactic script consists of a sequence of tactics, separated either by semicolons or newlines.
When separated by newlines, tactics must be indented to the same level.
Explicit curly braces and semicolons may be used instead of indentation.
Tactic sequences may be grouped by parentheses.
This allows a sequence of tactics to be used in a position where a single tactic would otherwise be grammatically expected.

:::

タクティクのスクリプトはセミコロンか改行で区切られた一連のタクティクで構成されます。改行で区切る場合、タクティクは同じレベルにインデントされなければなりません。インデントの代わりに波括弧とセミコロンを使っても良いです。タクティクの列は括弧でグループ化することができます。こうすることで文法的には1つのタクティクが期待される位置で一連のタクティクを使うことができます。

:::comment
Generally, execution proceeds from top to bottom, with each tactic running in the proof state left behind by the prior tactic.
The tactic language contains a number of control structures that can modify this flow.

:::

一般的に、実行は上から下へと進み、各タクティクは前のタクティクが残した証明状態にて実行されます。タクティク言語には、このフローを変更できる制御構造が数多く含まれています。

:::comment
Each tactic is a syntax extension in the `tactic` category.
This means that tactics are free to define their own concrete syntax and parsing rules.
However, with a few exceptions, the majority of tactics can be identified by a leading keyword; the exceptions are typically frequently-used built-in control structures such as {tactic}`<;>`.

:::

各タクティクは `tactic` カテゴリの構文拡張です。つまり、タクティクは独自の具体的な構文やパース規則を自由に定義することができます。しかし、いくつかの例外を除いて、大部分のタクティクは先頭のキーワードで識別することができます；例外は典型的には {tactic}`<;>` のようなよく使われる組み込みの制御構造です。

:::comment
## Control Structures
%%%
tag := "tactic-language-control"
%%%

:::

## 制御構造（Control Structures）

:::comment
Strictly speaking, there is no fundamental distinction between control structures and other tactics.
Any tactic is free to take others as arguments and arrange for their execution in any context that it sees fit.
Even if a distinction is arbitrary, however, it can still be useful.
The tactics in this section are those that resemble traditional control structures from programming, or those that _only_ recombine other tactics rather than making progress themselves.

:::

厳密に言えば、制御構造と他のタクティクの間に基礎的な区別はありません。どのようなタクティクであれ、他のものを引数として受け取り、適切と思われる文脈で実行できるようにアレンジすることは自由です。しかし、たとえこの区別が恣意的であったとしても、有用であることには変わりありません。この節のタクティクはプログラミングの伝統的な制御構造に似ているものや、それ自身が証明をすすめるのではなく、他のタクティクを再結合させる _だけ_ などです。

:::comment
### Success and Failure
%%%
tag := "tactic-language-success-failure"
%%%

:::

### 成功と失敗（Success and Failure）

:::comment
When run in a proof state, every tactic either succeeds or fails.
Tactic failure is akin to exceptions: failures typically "bubble up" until handled.
Unlike exceptions, there is no operator to distinguish between reasons for failure; {tactic}`first` simply takes the first branch that succeeds.

:::

証明状態で実行すると、すべてのタクティクは成功するか失敗するかのどちらかです。タクティクの失敗は例外に似ています；失敗は通常、処理されるまで「沸き立ちます」。例外とは異なり、失敗の理由を区別する演算子はありません； {tactic}`first` は単に成功した最初の分岐を取ります。

::: tactic "fail"
:::

:::tactic "fail_if_success"
:::

:::tactic "try"
:::

:::tactic "first"
:::


:::comment
### Branching
%%%
tag := "tactic-language-branching"
%%%

:::

### 分岐（Branching）

:::comment
Tactic proofs may use pattern matching and conditionals.
However, their meaning is not quite the same as it is in terms.
While terms are expected to be executed once the values of their variables are known, proofs are executed with their variables left abstract and should consider _all_ cases simultaneously.
Thus, when `if` and `match` are used in tactics, their meaning is reasoning by cases rather than selection of a concrete branch.
All of their branches are executed, and the condition or pattern match is used to refine the main goal with more information in each branch, rather than to select a single branch.

:::

タクティクの証明では、パターンマッチや条件式を使うことがあります。しかし、その意味は項においてのものと全く同じではありません。項では変数の値が分かってから実行されるのに対し、証明は変数が抽象的なまま実行され、同時に _すべての_ ケースを考慮しなければなりません。したがって、`if` や `match` がタクティクで使われる場合、その意味は具体的な分岐の選択ではなく、ケースによる推論です。それらの分岐はすべて実行され、条件やパターンマッチは単一の分岐を選択するためではなく、各分岐でより多くの情報を使ってメインゴールを絞り込むために使われます。

:::tactic Lean.Parser.Tactic.tacIfThenElse show := "if ... then ... else ..."

:::

:::tactic Lean.Parser.Tactic.tacDepIfThenElse show:= "if h : ... then ... else ..."
:::

:::comment
::example "Reasoning by cases with `if`"
:::
::::example "`if` による場合分けの推論"
:::comment
In each branch of the {keywordOf Lean.Parser.Tactic.tacIfThenElse}`if`, an assumption is added that reflects whether `n = 0`.

:::

{keywordOf Lean.Parser.Tactic.tacIfThenElse}`if` の各分岐では、`n = 0` かどうかを反映する仮定が追加されます。

```lean
example (n : Nat) : if n = 0 then n < 1 else n > 0 := by
  if n = 0 then
    simp [*]
  else
    simp only [↓reduceIte, gt_iff_lt, *]
    omega
```
::::

::::tactic Lean.Parser.Tactic.match show := "match"

:::comment
When pattern matching, instances of the scrutinee in the goal are replaced with the patterns that match them in each branch.
Each branch must then prove the refined goal.
Compared to the `cases` tactic, using `match` can allow a greater degree of flexibility in the cases analysis being performed, but the requirement that each branch solve its goal completely makes it more difficult to incorporate into larger automation scripts.
:::

パターンマッチの場合、ゴールの中の被検査対象のインスタンスは各ブランチでそれにマッチするパターンに置き換えられます。その後、各ブランチは絞り込まれたゴールを証明しなければなりません。`cases` タクティクと比較すると、`match` を使用することで、実行するケース分析に柔軟性を持たせることができますが、各ブランチがゴールを完全に解決する必要があるため、大規模な自動化スクリプトに組み込むことが難しくなります。

::::

:::comment
::example "Reasoning by cases with `match`"
:::
::::example "`match` による場合分けの推論"
:::comment
In each branch of the {keywordOf Lean.Parser.Tactic.match}`match`, the scrutinee `n` has been replaced by either `0` or `k + 1`.
:::

{keywordOf Lean.Parser.Tactic.match}`match` の各ブランチでは、被検査対象 `n` が `0` または `k + 1` に置き換えられています。

```lean
example (n : Nat) : if n = 0 then n < 1 else n > 0 := by
  match n with
  | 0 =>
    simp
  | k + 1 =>
    simp
```
::::

:::comment
### Goal Selection
%%%
tag := "tactic-language-goal-selection"
%%%


:::

### ゴールの選択（Goal Selection）

:::comment
Most tactics affect the {tech}[main goal].
Goal selection tactics provide a way to treat a different goal as the main one, rearranging the sequence of goals in the proof state.


:::

ほとんどのタクティクは {tech}[メインゴール] に影響を与えます。ゴール選択タクティクは異なるゴールをメインゴールとして扱う方法を提供し、証明状態のゴールの順序を並べ替えます。

:::tactic "case"
:::

:::tactic "case'"
:::


:::tactic "rotate_left"
:::

:::tactic "rotate_right"
:::

:::comment
#### Sequencing
%%%
tag := "tactic-language-sequencing"
%%%

:::

#### 順序実行（Sequencing）

:::comment
In addition to running tactics one after the other, each being used to solve the main goal, the tactic language supports sequencing tactics according to the way in which goals are produced.
The {tactic}`<;>` tactic combinator allows a tactic to be applied to _every_ {tech}[subgoal] produced by some other tactic.
If no new goals are produced, then the second tactic is not run.

:::

タクティク言語では、タクティクを次々に実行し、それぞれがメインゴールを解決するために使用されることに加え、目標の生成方法に従ってタクティクを順番に実行することもサポートしています。 {tactic}`<;>` タクティクコンビネータは、他のタクティクによって生成された _すべての_ {tech}[サブゴール] ごとにタクティクを適用することを可能にします。新しいゴールが生成されなければ、2番目のタクティクは実行されません。

::::tactic "<;>"

:::comment
If the tactic fails on any of the {tech}[subgoals], then the whole {tactic}`<;>` tactic fails.
:::

タクティクが {tech}[サブゴール] のいずれかで失敗した場合、 {tactic}`<;>` タクティク全体が失敗します。

::::

:::comment
::example "Subgoal Sequencing"
:::
:::::example "サブゴールの順序実行"
::::tacticExample

```setup
  intro x h
```


{goal show := false}`∀x, x = 1 ∨ x = 2 → x < 3`

:::comment
In a this proof state:
:::

この証明状態において：

```pre
x : Nat
h : x = 1 ∨ x = 2
⊢ x < 3
```
:::comment
the tactic {tacticStep}`cases h` yields the following two goals:
:::

タクティク {tacticStep}`cases h` は以下の2つのゴールを生成します：

```post
case inl
x : Nat
h✝ : x = 1
⊢ x < 3

case inr
x : Nat
h✝ : x = 2
⊢ x < 3
```

::::
::::tacticExample

```setup
  intro x h
```

{goal show := false}`∀x, x = 1 ∨ x = 2 → x < 3`

```pre (show := false)
x : Nat
h : x = 1 ∨ x = 2
⊢ x < 3
```

:::comment
Running {tacticStep}`cases h ; simp [*]` causes {tactic}`simp` to solve the first goal, leaving the second behind:
:::

{tacticStep}`cases h ; simp [*]` を実行することで、 {tactic}`simp` が最初のゴールを解決し、2つ目が残ります：

```post
case inr
x : Nat
h✝ : x = 2
⊢ x < 3
```

::::

::::tacticExample

```setup
  intro x h
```

{goal show := false}`∀x, x = 1 ∨ x = 2 → x < 3`

```pre (show := false)
x : Nat
h : x = 1 ∨ x = 2
⊢ x < 3
```

:::comment
Replacing the `;` with {tactic}`<;>` and running {tacticStep}`cases h <;> simp [*]` solves *both* of the new goals with {tactic}`simp`:

:::

`;` を {tactic}`<;>` で置き換え、 {tacticStep}`cases h <;> simp [*]` を実行すると {tactic}`simp` によって新しいゴールが *両方とも* 解決されます：

```post

```

::::

:::::

:::comment
#### Working on Multiple Goals
%%%
tag := "tactic-language-multiple-goals"
%%%

:::

#### 複数のゴールに作用する（Working on Multiple Goals）

:::comment
The tactics {tactic}`all_goals` and {tactic}`any_goals` allow a tactic to be applied to every goal in the proof state.
The difference between them is that if the tactic fails for in any of the goals, {tactic}`all_goals` itself fails, while {tactic}`any_goals` fails only if the tactic fails in all of the goals.

:::

タクティク {tactic}`all_goals` と {tactic}`any_goals` は証明状態のすべてのゴールにタクティクを適用できます。両者の違いは、タクティクがいずれかのゴールで失敗した場合、 {tactic}`all_goals` はそれ自体が失敗する一方、 {tactic}`any_goals` はタクティクがすべてのゴールで失敗した場合のみに失敗します。

:::tactic "all_goals"
:::

:::tactic "any_goals"
:::


:::comment
### Focusing
%%%
tag := "tactic-language-focusing"
%%%

:::

### 焦点をあてる（Focusing）

:::comment
Focusing tactics remove some subset of the proof goals (typically leaving only the main goal) from the consideration of some further tactics.
In addition to the tactics described here, the {tactic}`case` and {tactic}`case'` tactics focus on the selected goal.

:::

焦点をあてるタクティクは証明ゴールのサブセット（通常はメインゴールのみを残します）をそれ以降のタクティクの検討対象から外します。ここで説明するタクティクに加えて、 {tactic}`case` と {tactic}`case'` は選択されたゴールに焦点を当てます。

::::tactic Lean.cdot show:="·"

:::comment
It is generally considered good Lean style to use bullets whenever a tactic line results in more than one new subgoal.
This makes it easier to read and maintain proofs, because the connections between steps of reasoning are more clear and any change in the number of subgoals while editing the proof will have a localized effect.
:::

一般に、1つのタクティク行から複数の新しいサブゴールが生成される場合、ブレットを使用することが良い Lean 流と考えられています。こうすることで、推論のステップ間の繋がりがより明確になり、証明の編集中にサブゴールの数を変更しても局所的な効果しかないため、証明を読みやすく、維持しやすくなります。

::::

:::tactic "next"
:::


:::tactic "focus"
:::

:::comment
### Repetition and Iteration
%%%
tag := "tactic-language-iteration"
%%%

:::

### 繰り返しと反復（Repetition and Iteration）

:::tactic "iterate"
:::

:::tactic "repeat"
:::

:::tactic "repeat'"
:::

:::tactic "repeat1'"
:::


:::comment
## Names and Hygiene
%%%
tag := "tactic-language-hygiene"
%%%

:::

## 名前と健全性（Names and Hygiene）

:::comment
Behind the scenes, tactics generate proof terms.
These proof terms exist in a local context, because assumptions in proof states correspond to local binders in terms.
Uses of assumptions correspond to variable references.
It is very important that the naming of assumptions be predictable; otherwise, small changes to the internal implementation of a tactic could either lead to variable capture or to a broken reference if they cause different names to be selected.

:::

裏側では、タクティクは証明項を生成しています。これらの証明項はローカルコンテキストに存在します。なぜなら証明状態の仮定は項のローカルの束縛子に対応するからです。仮定の使用は変数の参照に対応します。仮定の名前付けは予測可能であることが非常に重要です；そうでなければ、タクティクの内部実装に小さな変更を加えると、変数がキャプチャされたり、異なる名前が選択されると参照が壊れたりする可能性があります。

:::comment
Lean's tactic language is _hygienic_. {index subterm := "in tactics"}[hygiene]
This means that the tactic language respects lexical scope: names that occur in a tactic refer to the enclosing binding in the source code, rather than being determined by the generated code, and the tactic framework is responsible for maintaining this property.
Variable references in tactic scripts refer either to names that were in scope at the beginning of the script or to bindings that were explicitly introduced as part of the tactics, rather than to the names chosen for use in the proof term behind the scenes.

:::

Lean のタクティク言語は _健全_ {index subterm := "in tactics"}[hygiene] （hygienic）です。これはタクティク言語が字句スコープを尊重することを意味します：タクティク内で出現する名前は生成されたコードによって決定されるのではなく、ソースコードの束縛を参照しており、タクティクフレームワークはこのプロパティを維持する責任があります。タクティクスクリプトの変数参照は裏側で証明項で使うために選ばれた名前ではなく、スクリプトの最初にスコープにあった名前か、タクティクの一部として明示的に導入された束縛を参照します。

:::comment
A consequence of hygienic tactics is that the only way to refer to an assumption is to explicitly name it.
Tactics cannot assign assumption names themselves, but must rather accept names from users; users are correspondingly obligated to provide names for assumptions that they wish to refer to.
When an assumption does not have a user-provided name, it is shown in the proof state with a dagger (`'†', DAGGER	0x2020`).
The dagger indicates that the name is _inaccessible_ and cannot be explicitly referred to.

:::

健全なタクティクの結果として、仮定を参照する唯一の方法は、その仮定に明示的に名前をつけることです。タクティクは自分で仮定に名前を付けることができず、むしろユーザからの名前を受け入れなければなりません；これに応じてユーザは参照したい仮定の名前を提供する義務があります。ユーザが仮定に名前を提供しない場合、その仮定は短剣（`'†'、DAGGER	0x2020`）と共に証明状態に表示されます。この短剣はその名前が _アクセス不能_ （inaccessible）であり、明示的に参照できないことを示します。

:::comment
Hygiene can be disabled by setting the option {option}`tactic.hygienic` to `false`.
This is not recommended, as many tactics rely on the hygiene system to prevent capture and thus do not incur the overhead of careful manual name selection.

:::

オプション {option}`tactic.hygienic` を `false` に設定することで、健全性を無効にすることができます。多くのタクティクはキャプチャを防ぐために健全性システムに依存しており、注意深く手動で名前を選択するオーバーヘッドが発生しないため、これは推奨されません。

{optionDocs tactic.hygienic}

:::comment
::example "Tactic hygiene: inaccessible assumptions"
:::
:::::example "タクティクの健全さ：アクセス不能な仮定"
::::tacticExample

```setup
skip
```
:::comment
When proving that {goal}`∀ (n : Nat), 0 + n = n`, the initial proof state is:

:::

{goal}`∀ (n : Nat), 0 + n = n` を証明する場合、最初の証明状態は次のようになります：

```pre
⊢ ∀ (n : Nat), 0 + n = n
```

:::comment
The tactic {tacticStep}`intro` results in a proof state with an inaccessible assumption:

:::

タクティク {tacticStep}`intro` によってアクセス不能な仮定を持つ証明状態になります：

```post
n✝ : Nat
⊢ 0 + n✝ = n✝
```
::::
:::::

:::comment
::example "Tactic hygiene: accessible assumptions"
:::
:::::example "タクティクの健全さ：アクセス可能な仮定"
::::tacticExample

```setup
skip
```
:::comment
When proving that {goal}`∀ (n : Nat), 0 + n = n`, the initial proof state is:

:::

{goal}`∀ (n : Nat), 0 + n = n` を証明する場合、最初の証明状態は次のようになります：

```pre
⊢ ∀ (n : Nat), 0 + n = n
```

:::comment
The tactic {tacticStep}`intro n`, with the explicit name `n`, results in a proof state with an accessibly-named assumption:

:::

明示的な名前 `n` を伴ったタクティク {tacticStep}`intro n` はアクセス可能な名前の仮定を持つ証明状態になります：

```post
n : Nat
⊢ 0 + n = n
```
::::
:::::

:::comment
### Accessing Assumptions
%%%
tag := "tactic-language-assumptions"
%%%

:::

### 仮定へのアクセス（Accessing Assumptions）

:::comment
Many tactics provide a means of specifying names for the assumptions that they introduce.
For example, {tactic}`intro` and {tactic}`intros` take assumption names as arguments, and {tactic}`induction`'s {keywordOf Lean.Parser.Tactic.induction}`with`-form allows simultaneous case selection, assumption naming, and focusing.
When an assumption does not have a name, one can be assigned using {tactic}`next`, {tactic}`case`, or {tactic}`rename_i`.

:::

多くのタクティクは、導入する仮定の名前を指定する手段を提供します。例えば、 {tactic}`intro` と {tactic}`intros` は引数として仮定の名前を取り、 {tactic}`induction` の {keywordOf Lean.Parser.Tactic.induction}`with` による形式はケース選択・仮定の名前付け・焦点当てを同時に行うことができます。仮定に名前がない場合、 {tactic}`next` ・ {tactic}`case` ・ {tactic}`rename_i` などを使用して名前を割り当てることができます。

:::tactic "rename_i"
:::

:::comment
## Assumption Management
%%%
tag := "tactic-language-assumption-management"
%%%

:::

## 仮定の管理（Assumption Management）

:::comment
Larger proofs can benefit from management of proof states, removing irrelevant assumptions and making their names easier to understand.
Along with these operators, {tactic}`rename_i` allows inaccessible assumptions to be renamed, and {tactic}`intro`, {tactic}`intros` and {tactic}`rintro` convert goals that are implications or universal quantification into goals with additional assumptions.

:::

より大きな証明では証明状態の管理による恩恵が大きく、無関係な仮定を削除し、それらの名前を理解しやすくします。ここまでの演算子に加え、 {tactic}`rename_i` はアクセス不能な仮定の名前を付けなおし、 {tactic}`intro` ・ {tactic}`intros` ・ {tactic}`rintro` は含意または全称量化されたゴールを追加の仮定を持つゴールに変換します。

:::tactic "rename"
:::

:::tactic "revert"
:::

:::tactic "clear"
:::


:::comment
## Local Definitions and Proofs
%%%
tag := "tactic-language-local-defs"
%%%

:::

## ローカル定義と証明（Local Definitions and Proofs）

:::comment
{tactic}`have` and {tactic}`let` both create local assumptions.
Generally speaking, {tactic}`have` should be used when proving an intermediate lemma; {tactic}`let` should be reserved for local definitions.

:::

{tactic}`have` と {tactic}`let` はどちらもローカルの仮定を作ります。一般的に言って、中間的な補題を証明する時には {tactic}`have` を使うべきです； {tactic}`let` はローカル定義の保存に使うべきです。

:::tactic "have"
:::

:::tactic Lean.Parser.Tactic.tacticHaveI_
:::

:::tactic Lean.Parser.Tactic.tacticHave'_
:::

:::tactic Lean.Parser.Tactic.tacticLet_ show:="let"
:::

:::tactic Lean.Parser.Tactic.letrec show:="let rec"
:::

:::tactic Lean.Parser.Tactic.tacticLetI_
:::

:::tactic Lean.Parser.Tactic.tacticLet'_
:::

## Configuration
%%%
tag := "tactic-config"
%%%

Many tactics are configurable.{index subterm:="of tactics"}[configuration]
By convention, tactics share a configuration syntax, described using {syntaxKind}`optConfig`.
The specific options available to each tactic are described in the tactic's documentation.

:::syntax Lean.Parser.Tactic.optConfig (open := false)
A tactic configuration consists of zero or more {deftech}[configuration items]:
```grammar
$x:configItem*
```
:::

:::syntax Lean.Parser.Tactic.configItem (open := false)
Each configuration item has a name that corresponds to an underlying tactic option.
Boolean options may be enabled or disabled using prefix `+` and `-`:
```grammar
+$x
```
```grammar
-$x
```

Options may be assigned specific values using a syntax similar to that for named function arguments:
```grammar
($x:ident := $t)
```

Finally, the name `config` is reserved; it is used to pass an entire set of options as a data structure.
The specific type expected depends on the tactic.
```grammar
(config := $t)
```

:::

:::comment
## Namespace and Option Management
%%%
tag := "tactic-language-namespaces-options"
%%%

:::

## 名前空間とオプション管理（Namespace and Option Management）

:::comment
Namespaces and options can be adjusted in tactic scripts using the same syntax as in terms.

:::

名前空間とオプションは項と同じ構文を使ってタクティクスクリプトで調整できます。

:::tactic Lean.Parser.Tactic.set_option show:="set_option"
:::

:::tactic Lean.Parser.Tactic.open show:="open"
:::

:::comment
### Controlling Unfolding
%%%
tag := "tactic-language-unfolding"
%%%

:::

### 展開のコントロール（Controlling Unfolding）

:::comment
By default, only definitions marked reducible are unfolded, except when checking definitional equality.
These operators allow this default to be adjusted for some part of a tactic script.

:::

デフォルトでは、定義上の等価性をチェックする時を除いて、reducible とマークされた定義だけが展開されます。これらの演算子により、タクティクスクリプトの一部でこのデフォルトを調整することができます。

:::tactic Lean.Parser.Tactic.withReducibleAndInstances
:::

:::tactic Lean.Parser.Tactic.withReducible
:::

:::tactic Lean.Parser.Tactic.withUnfoldingAll
:::


:::comment
# Options
%%%
tag := "tactic-language-options"
%%%

:::

# オプション

:::comment
These options affect the meaning of tactics.

:::

これらのオプションはタクティクの意味に影響します。

{optionDocs tactic.dbg_cache}

{optionDocs tactic.customEliminators}

{optionDocs tactic.skipAssignedInstances}

{optionDocs tactic.simp.trace}


{include 0 Manual.Tactics.Reference}

{include 0 Manual.Tactics.Conv}

{include 0 Manual.Tactics.Custom}
