/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

/-
#doc (Manual) "The Simplifier" =>
-/
#doc (Manual) "単純化器（The Simplifier）" =>
%%%
tag := "the-simplifier"
%%%

:::comment
The simplifier is one of the most-used features of Lean.
It performs inside-out rewriting of terms based on a database of simplification rules.
The simplifier is highly configurable, and a number of tactics use it in different ways.

:::

単純化器は Lean で最もよく使われる機能の1つです。これは単純化規則のデータベースに基づいて、項を隅から隅まで書き換えます。単純化器は高度に設定可能であり、多くのタクティクが様々な方法で単純化器を使用しています。

:::comment
# Invoking the Simplifier
:::

# 単純化器の呼び出し（Invoking the Simplifier）
%%%
tag := "simp-tactic-naming"
%%%



:::comment
Lean's simplifier can be invoked in a variety of ways.
The most common patterns are captured in a set of tactics.
The {ref "simp-tactics"}[tactic reference] contains a complete list of simplification tactics.

:::

Lean の単純化器はさまざまな方法で呼び出すことができます。最も一般的なパターンはタクティクのセットに含まれています。 {ref "simp-tactics"}[タクティクのリファレンス] には、単純化タクティクの完全なリストが含まれています。

:::comment
Simplification tactics all contain `simp` in their name.
Aside from that, they are named according to a system of prefixes and suffixes that describe their functionality:

:::

単純化器のタクティクはすべて名前に `simp` を含んでいます。それはともかく、それらはその機能を表す接頭辞と接尾辞のシステムに従って命名されます：

:::comment
: `-!` suffix

  Sets the {name Lean.Meta.Simp.Config.autoUnfold}`autoUnfold` configuration option to `true`, causing the simplifier unfold all definitions

:::

: `-!` 接尾辞

  {name Lean.Meta.Simp.Config.autoUnfold}`autoUnfold` 設定オプションを `true` にし、これにより単純化器はすべての定義を展開します

:::comment
: `-?` suffix

  Causes the simplifier to keep track of which rules it employed during simplification and suggest a minimal {tech}[simp set] as an edit to the tactic script

:::

: `-?` 接尾辞

  単純化スクリプトが単純化中にどの規則を採用したかを追跡し、単純化スクリプトを記述する上で最小の {tech}[simp セット] を提案するようにします

:::comment
: `-_arith` suffix

  Enables the use of linear arithmetic simplification rules

:::

: `-_arith` 接尾辞

  線形算術の単純化規則の使用を可能にします

:::comment
: `d-` prefix

  Causes the simplifier to simplify only with rewrites that hold definitionally

:::

: `d-` 接頭辞

  定義上成立する書き換えのみを単純化します

:::comment
: `-_all` suffix

  Causes the simplifier to repeatedly simplify all assumptions and the conclusion of the goal, taking as many hypotheses into account as possible, until no further simplification is possible

:::

: `-_all` 接尾辞

  これ以上の単純化が不可能になるまで、可能な限り多くの仮定を考慮に入れながら単純化器にすべての仮定とゴールの結論を繰り返し単純化させます

:::comment
There are two further simplification tactics, {tactic}`simpa` and {tactic}`simpa!`, which are used to simultaneously simplify a goal and either a proof term or an assumption before discharging the goal.
This simultaneous simplification makes proofs more robust to changes in the {tech}[simp set].

:::

これらに加えて2つの単純化タクティク {tactic}`simpa` と {tactic}`simpa!` があります。これらはゴールを終了する前に、ゴールと証明項・仮定を同時に単純化するために用いられます。この同時単純化により、 {tech}[simp セット] の変更に対して証明がより頑強になります。

:::comment
## Parameters
%%%
tag := "simp-tactic-params"
%%%

:::

## パラメータ（Parameters）

:::comment
The simplification tactics have the following grammar:

:::

単純化タクティクは以下のような文法を持ちます：

:::syntax tactic
```grammar
simp $_:optConfig $[only]? $[ [ $[$e],* ] ]? $[at $[$h]*]?
```
:::

:::comment
In other words, an invocation of a simplification tactic takes the following modifiers, in order, all of which are optional:
 * A {ref "tactic-config"}[configuration options], which should the fields of {name}`Lean.Meta.Simp.Config` or {name}`Lean.Meta.DSimp.Config`, depending on whether the simplifier being invoked is a version of {tactic}`simp` or a version of {tactic}`dsimp`.
 * The {keywordOf Lean.Parser.Tactic.simp}`only` modifier excludes the default simp set, instead beginning with an empty{margin}[Technically, the simp set always includes {name}`eq_self` and {name}`iff_self` in order to discharge reflexive cases.] simp set.
 * The lemma list adds or removes lemmas from the simp set. There are three ways to specify lemmas in the lemma list:
   * `*`, which adds all assumptions in the proof state to the simp set
   * `-` followed by a lemma, which removes the lemma from the simp set
   * A lemma specifier, consisting of the following in sequence:
      * An optional `↓` or `↑`, which respectively cause the lemma to be applied before or after entering a subterm (`↑` is the default). The simplifier typically simplifies subterms before attempting to simplify parent terms, as simplified arguments often make more rules applicable; `↓` causes the parent term to be simplified with the rule prior to the simplification of subterms.
      * An optional `←`, which causes equational lemmas to be used from right to left rather than from left to right.
      * A mandatory lemma, which can be a simp set name, a lemma name, or a term. Terms are treated as if they were named lemmas with fresh names.
 * A location specifier, preceded by {keywordOf Lean.Parser.Tactic.simp}`at`, which consists of a sequence of locations. Locations may be:

:::

言い換えれば、単純化タクティクの呼び出しは以下の修飾子を順番に取ります。またこれらはすべて任意です：
 * {ref "tactic-config"}[設定オプション] 、呼び出される単純化器が {tactic}`simp` のバージョンか {tactic}`dsimp` のバージョンであるかに応じて、 {name}`Lean.Meta.Simp.Config` か {name}`Lean.Meta.DSimp.Config` のフィールドでなければなりません。
 * {keywordOf Lean.Parser.Tactic.simp}`only` 修飾子はデフォルトの simp セットを除外し、代わりに空の {margin}[厳密には、再帰的なケースを除外するために、simp セットは常に {name}`eq_self` と {name}`iff_self` を含みます。] simp セットから開始します。
 * 補題リストは simp セットに補題を追加したり削除したりします。補題リストで補題を指定する方法は3つあります：
   * `*`、これは証明状態にあるすべての仮定を simp セットに追加します
   * `-` に続く補題はその simp セットから取り除かれます
   * 補題指定子、これは以下の順番で構成されます：
     * 任意の `↓` または `↑` はそれぞれ部分項を入力する前後に補題を適用します（`↑` がデフォルト）。単純化された引数はより多くの規則を適用できることが多いため、単純化器は通常、親の項を単純化する前に部分項を単純化します；`↓` によって親の項が部分項の単純化よりも優先的に単純化されます。
     * 任意の `←` は等式の補題を左から右へではなく、右から左へ使うようにします。
     * 必須の補題で、simp セット名・補題名・項のいずれでも良いです。項はあたかも新しい名前の補題であるかのように扱われます。
 * {keywordOf Lean.Parser.Tactic.simp}`at` で始まる位置指定子で、これは位置の列から構成されます。位置は次のいずれかになります：

:::comment
   - The name of an assumption, indicating that its type should be simplified
   - An asterisk `*`, indicating that all assumptions and the conclusion should be simplified
   - A turnstile `⊢`, indicating that the conclusion should be simplified

:::

   - 仮定の名前、これはその型が単純化されるべきであることを示します
   - アスタリスク `*`、すべての仮定と結論が単純化されることを示します
   - ターンスタイル `⊢`、結論を単純化する必要があることを示します

:::comment
  By default, only the conclusion is simplified.

:::

  デフォルトでは結論だけが単純化されます。

:::comment
::example "Location specifiers for {tactic}`simp`"
:::
:::::example "{tactic}`simp` のための位置指定子"
::::tacticExample
{goal show:=false}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```

:::comment
In this proof state,
:::

この証明状態において、

```pre
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

:::comment
the tactic {tacticStep}`simp_arith` simplifies only the goal:

:::

タクティク {tacticStep}`simp_arith` はゴールのみを単純化します：

```post
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (x + 7)
```
::::

::::tacticExample
{goal show:=false}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```
```pre (show := false)
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

:::comment
Invoking {tacticStep}`simp_arith at h` yields a goal in which the hypothesis `h` has been simplified:

:::

{tacticStep}`simp_arith at h` の呼び出しは仮定 `h` が単純化されたゴールを生成します：

```post
p : Nat → Prop
x : Nat
h' : p (3 + x + 9)
h : p (x + 7)
⊢ p (6 + x + 1)
```
::::

::::tacticExample
{goal show:=false}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```
```pre (show := false)
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

:::comment
The conclusion can be additionally simplified by adding `⊢`, that is, {tacticStep}`simp_arith at h ⊢`:

:::

さらに結論を単純化するには `⊢` を追加して {tacticStep}`simp_arith at h ⊢` とすることで可能です：

```post
p : Nat → Prop
x : Nat
h' : p (3 + x + 9)
h : p (x + 7)
⊢ p (x + 7)
```
::::

::::tacticExample
{goal show:=false}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```
```pre (show := false)
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

:::comment
Using {tacticStep}`simp_arith at *` simplifies all assumptions together with the conclusion:

:::

{tacticStep}`simp_arith at *` を使うことで結論を含めすべての仮定が単純化されます：

```post
p : Nat → Prop
x : Nat
h : p (x + 7)
h' : p (x + 12)
⊢ p (x + 7)
```
::::
:::::


:::comment
# Rewrite Rules
:::

# 書き換え規則（Rewrite Rules）
%%%
tag := "simp-rewrites"
%%%


:::comment
The simplifier has three kinds of rewrite rules:

:::

単純化器には3種類の書き換え規則があります：

:::comment
: Declarations to unfold

  The simplifier will only unfold {tech}[reducible] definitions by default. However, a rewrite rule can be added for any {tech}[semi-reducible] or {tech}[irreducible] definition that causes the simplifier to unfold it as well. When the simplifier is running in definitional mode ({tactic}`dsimp` and its variants), definition unfolding only replaces the defined name with its value; otherwise, it also uses the equational lemmas produced by the equation compiler.

:::

: 定義の展開

  単純化器はデフォルトで {tech}[reducible] な定義のみを展開します。しかし、任意の {tech}[semi-reducible] または {tech}[irreducible] な定義用に書き換え規則を追加して、単純化器が同様にそれらを展開するようにできます。単純化器が定義上モード（ {tactic}`dsimp` とその亜種）で動作している場合、定義の展開は定義された名前をその値で置き換えるだけです；それ以外では、等式のコンパイラから提供された等式の補題も使用します。

:::comment
: Equational lemmas

  The simplifier can treat equality proofs as rewrite rules, in which case the left side of the equality will be replaced with the right. These equational lemmas may have any number of parameters. The simplifier instantiates parameters to make the left side of the equality match the goal, and it performs a proof search to instantiate any additional parameters.

:::

: 等式の補題

  単純化器は等式の証明を書き換え規則として扱うことができ、この場合等式の左辺は右辺に置き換えられます。これらの等式の補題は任意の数のパラメータを持つことができます。単純化器は等式の左辺がゴールに一致するようにパラメータをインスタンス化し、追加のパラメータをインスタンス化するために証明探索を実行します。

:::comment
: Simplification procedures

  The simplifier supports simplification procedures, known as {deftech}_simprocs_, that use Lean metaprogramming to perform rewrites that can't be efficiently specified using equations. Lean includes simprocs for the most important operations on built-in types.

:::

: 単純化手続き

  単純化器は {deftech}_simprocs_ として知られている単純化手続きをサポートしており、Lean メタプログラミングを使用して、等式では効率的に指定できない書き換えを実行します。Lean には組み込み型に対する最も重要な操作のための simproc が含まれています。

:::keepEnv
```lean (show := false)
-- Validate the above description of reducibility

@[irreducible]
def foo (x : α) := x

set_option allowUnsafeReducibility true in
@[semireducible]
def foo' (x : α) := x

@[reducible]
def foo'' (x : α) := x

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#guard_msgs in
example : foo (x, y) = (y, x) := by
  simp [foo]

/-- error: simp made no progress -/
#guard_msgs in
example : foo (x, y) = (y, x) := by
  simp

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#guard_msgs in
example : foo' (x, y) = (y, x) := by
  simp [foo']

/-- error: simp made no progress -/
#guard_msgs in
example : foo' (x, y) = (y, x) := by
  simp

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#guard_msgs in
example : foo'' (x, y) = (y, x) := by
  simp [foo'']

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#guard_msgs in
example : foo'' (x, y) = (y, x) := by
  simp

```
:::

:::comment
Due to {tech}[propositional extensionality], equational lemmas can rewrite propositions to simpler, logically equivalent propositions.
When the simplifier rewrites a proof goal to {lean}`True`, it automatically closes it.
As a special case of equational lemmas, propositions other than equality can be tagged as rewrite rules
They are preprocessed into rules that rewrite the proposition to {lean}`True`.

:::

{tech}[propositional extensionality] により、等式の補題は命題をより単純で論理的に等価な補題に書き換えることができます。単純化器が証明のゴールを {lean}`True` に書き換えると、ゴールが自動的に閉じられます。等式の補題の特別なケースとして、等式以外の命題を書き換え規則としてタグ付けすることができます。それらは命題を {lean}`True` に書き換える規則へと前処理されます。

:::comment
::example "Rewriting Propositions"
:::
:::::example "書き換えの命題"
::::tacticExample

{goal show:=false}`∀(α β : Type) (w y : α) (x z : β), (w, x) = (y, z)`
```setup
intro α β w y x z
```

:::comment
When asked to simplify an equality of pairs:
:::

ペアについての等式を単純化することが求められている場合：

```pre
α β : Type
w y : α
x z : β
⊢ (w, x) = (y, z)
```

:::comment
{tacticStep}`simp` yields a conjunction of equalities:

:::

{tacticStep}`simp` は連言の等式を生成します：

```post
α β : Type
w y : α
x z : β
⊢ w = y ∧ x = z
```

:::comment
The default simp set contains {lean}`Prod.mk.injEq`, which shows the equivalence of the two statements:

:::

デフォルトの simp セットには {lean}`Prod.mk.injEq` が含まれており、2つの文の同値性を示しています：

```signature
Prod.mk.injEq.{u, v} {α : Type u} {β : Type v} (fst : α) (snd : β) :
  ∀ (fst_1 : α) (snd_1 : β),
    ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
```
::::
:::::

:::comment
In addition to rewrite rules, {tactic}`simp` has a number of built-in reduction rules, {ref "simp-config"}[controlled by the `config` parameter].
Even when the simp set is empty, {tactic}`simp` can replace `let`-bound variables with their values, reduce {keywordOf Lean.Parser.Term.match}`match` expressions whose scrutinees are constructor applications, reduce structure projections applied to constructors, or apply lambdas to their arguments.

:::

書き換え規則に加え、 {tactic}`simp` は {ref "simp-config"}[`config` パラメータによって制御される] いくつかの組み込みの簡約規則を持っています。simp セットが空の場合でも、 {tactic}`simp` は `let` 束縛変数のその値へに置き換え・場合分け対象がコンストラクタ適用である {keywordOf Lean.Parser.Term.match}`match` 式の簡約・コンストラクタに適用される構造体の射影の簡約・ラムダ式の引数への適用などを行うことができます。

:::comment
# Simp sets
:::

# simp セット（Simp sets）
%%%
tag := "simp-sets"
%%%


:::comment
A collection of rules used by the simplifier is called a {deftech}_simp set_.
A simp set is specified in terms of modifications from a _default simp set_.
These modifications can include adding rules, removing rules, or adding a set of rules.
The `only` modifier to the {tactic}`simp` tactic causes it to start with an empty simp set, rather than the default one.
Rules are added to the default simp set using the {attr}`simp` attribute.


:::

単純化器が使用する規則のセットを {deftech}_simp セット_ （simp set）と呼びます。simp セットは、_デフォルト simp セット_ （default simp set）への修正の観点において指定が行われます。これらの修正には規則の追加・削除・セットの追加が含まれます。 {tactic}`simp` タクティクに `only` 修飾子を付けると、デフォルト simp セットではなく、空の simp セットから開始します。規則は {attr}`simp` 属性を使ってデフォルト simp セットに追加されます。

::::syntax attr alias := Lean.Meta.simpExtension label:="attribute"
:::comment
The {attr}`simp` attribute adds a declaration to the default simp set.
If the declaration is a definition, the definition is marked for unfolding; if it is a theorem, then the theorem is registered as a rewrite rule.

:::

{attr}`simp` 属性はデフォルト simp セットに宣言を追加します。宣言が定義である場合、その定義は展開用としてマークされます；宣言が定理である場合、その定理は書き換え規則として登録されます。

```grammar
simp
```


```grammar
simp ↑ $p?
```

```grammar
simp ↓ $p?
```

```grammar
simp $p:prio
```

```lean (show := false)
-- Check above claim about default priority
/-- info: 1000 -/
#guard_msgs in
#eval eval_prio default
```
::::

:::comment
Custom simp sets are created with {name Lean.Meta.registerSimpAttr}`registerSimpAttr`, which must be run during {tech}[initialization] by placing it in an {keywordOf Lean.Parser.Command.initialize}`initialize` block.
As a side effect, it creates a new attribute with the same interface as {attr}`simp` that adds rules to the custom simp set.
The returned value is a {name Lean.Meta.SimpExtension}`SimpExtension`, which can be used to programmatically access the contents of the custom simp set.
The {tactic}`simp` tactics can be instructed to use the new simp set by including its attribute name in the rule list.

:::

カスタム simp セットは {name Lean.Meta.registerSimpAttr}`registerSimpAttr` で作成します。これは {tech}[初期化] 中における {keywordOf Lean.Parser.Command.initialize}`initialize` ブロック内でのみ実行可能です。副次効果として、カスタム simp セットに規則を追加する {attr}`simp` と同じインタフェースを持つ新しい属性を作成します。戻り値は {name Lean.Meta.SimpExtension}`SimpExtension` で、プログラムにてカスタム simp セットの内容にアクセスするために使用できます。 {tactic}`simp` タクティクは規則のリストにその属性名を含めることで新しい simp セットを使用するとうに指示できます。

{docstring Lean.Meta.registerSimpAttr}

{docstring Lean.Meta.SimpExtension}



:::comment
# Simp Normal Forms
:::

# simp 正規形（Simp Normal Forms）
%%%
tag := "simp-normal-forms"
%%%



:::comment
The default {tech}[simp set] contains all the theorems and simplification procedures marked with the {attr}`simp` attribute.
The {deftech}_simp normal form_ of an expression is the result of applying the default simp set via the {tactic}`simp` tactic until no more rules can be applied.
When an expression is in simp normal form, it is as reduced as possible according to the default simp set, often making it easier to work with in proofs.

:::

デフォルト {tech}[simp セット] には {attr}`simp` でマークされたすべての定理と単純化手続きが含まれます。式の {deftech}_simp 正規形_ （simp normal form）は、 {tactic}`simp` タクティクによってデフォルトの simp セットを適用できる規則がなくなるまで適用した結果です。式が simp 正規形であると、デフォルト simp セットに従って可能な限り簡約されているため、多くの場合証明で作業しやすくなります。

:::comment
The {tactic}`simp` tactic *does not guarantee confluence*, which means that the simp normal form of an expression may depend on the order in which the elements of the default simp set are applied.
The order in which the rules are applied can be changed by assigning priorities when setting the {attr}`simp` attribute.

:::

{tactic}`simp` タクティクは *合流性を保証しません* 。つまり式の simp 正規形はデフォルト simp セットの要素が適用される順番に依存する可能性があります。 {attr}`simp` 属性を設定する際に優先度を割り当てることで規則の適用順序を変更することができます。

:::comment
When designing a Lean library, it's important to think about what the appropriate simp normal form for the various combinations of the library's operators is.
This can serve as a guide when selecting which rules the library should add to the default simp set.
In particular, the right-hand side of simp lemmas should be in simp normal form; this helps ensure that simplification terminates.
Additionally, each concept in the library should be expressed through one simp normal form, even if there are multiple equivalent ways to state it.
If a concept is stated in two different ways in different simp lemmas, then some desired simplifications may not occur because the simplifier does not connect them.

:::

Lean ライブラリを設計する際には、ライブラリの演算子の様々な組み合わせに対して適切な simp 正規形とは何かを考えることが重要です。これはライブラリがデフォルト simp セットに追加するべき規則を選択する際の指針になります。特に、simp の補題の右辺は simp 正規形であるべきです；これによって単純化が停止することの保証が促進されます。さらに、ライブラリの各概念はたとえ等価な表現方法が複数あったとしても、1つの simp 正規形を通して表現されるべきです。ある概念が異なる simp の補題で2つの異なる方法で記述されている場合、単純化器がそれらを結び付けずに望ましい単純化が行われないことがあります。

:::comment
Even though simplification doesn't need to be confluent, striving for confluence is helpful because it makes the library more predictable and tends to reveal missing or poorly chosen simp lemmas.
The default simp set is as much a part of a library's interface as the type signatures of the constants that it exports.

:::

単純化では必ずしも合流性を満たす必要はありませんが、合流性に近づけようとすることはライブラリをより予測しやすくし、simp の補題の欠落や不適切な選択を明らかにする傾向があるため有益です。デフォルト simp セットはライブラリがエクスポートする定数の型シグネチャと同様に、ライブラリのインタフェースの一部です。

:::comment
Libraries should not add rules to the default simp set that don't mention at least one constant defined in the library.
Otherwise, importing a library could change the behavior of {tactic}`simp` for some unrelated library.
If a library relies on additional simplification rules for definitions or declarations from other libraries, please create a custom simp set and either instruct users to use it or provide a dedicated tactic.


:::

ライブラリは、そのライブラリで定義されている少なくとも1つの定数に言及しない規則をデフォルト simp セットに追加すべきではありません。そうでなければ、ライブラリをインポートすることで無関係なライブラリの {tactic}`simp` の挙動が変わってしまう可能性があります。ライブラリが他のライブラリからの定義や宣言に対する追加の単純化規則に依存している場合、カスタム simp セットを作成し、それを使用するようにユーザに指示するか、専用のタクティクを提供してください。

:::comment
# Terminal vs Non-Terminal Positions
:::

# 終端・非終端位置（Terminal vs Non-Terminal Positions）
%%%
tag := "terminal-simp"
%%%


:::comment
To write maintainable proofs, avoid using {tactic}`simp` without {keywordOf Lean.Parser.Tactic.simp}`only` unless it closes the goal.
Such uses of {tactic}`simp` that do not close a goal are referred to as {deftech}_non-terminal simps_.
This is because additions to the default simp set may make {tactic}`simp` more powerful or just cause it to select a different sequence of rewrites and arrive at a different simp normal form.
When {keywordOf Lean.Parser.Tactic.simp}`only` is specified, additional lemmas will not affect that invocation of the tactic.
In practice, terminal uses of {tactic}`simp` are not nearly as likely to be broken by the addition of new simp lemmas, and when they are, it's easier to understand the issue and fix it.

:::

メンテナンス可能な証明を書くためには、 {keywordOf Lean.Parser.Tactic.simp}`only` を伴わない {tactic}`simp` の使用はゴールを閉じない限り避けてください。ゴールを閉じない {tactic}`simp` のこのような使用は {deftech}_非終端 simp_ （non-terminal simp）と呼ばれます。これはデフォルト simp セットに追加することで、 {tactic}`simp` がより強力になったり、単に異なる書き換えシーケンスを選択し、異なる simp 正規形に到達する可能性があるからです。 {keywordOf Lean.Parser.Tactic.simp}`only` が指定されている場合、追加の補題はタクティクのその呼び出しに影響しません。実際には {tactic}`simp` の終端位置での使用は、新しい simp の補題の追加によって壊れる可能性はほとんどなく、壊れた場合も問題の理解と修正は容易です。

:::comment
When working in non-terminal positions, {tactic}`simp?` (or one of the other simplification tactics with `?` in their names) can be used to generate an appropriate invocation with{keywordOf Lean.Parser.Tactic.simp}`only`.
Just as {tactic}`apply?` or {tactic}`rw?` suggest the use of relevant lemmas, {tactic}`simp?` suggests an invocation of {tactic}`simp` with a minimal simp set that was used to reach the normal form.

:::

非終端位置で作業する場合、 {tactic}`simp?` （または名前に `?` を持つ他の単純化タクティクのいずれか）を使用して、 {keywordOf Lean.Parser.Tactic.simp}`only` で適切な呼び出しを生成することができます。ちょうど {tactic}`apply?` や {tactic}`rw?` が関連する補題の使用を提案するように、 {tactic}`simp?` は正規形に到達するために使用された最小の simp セットでの {tactic}`simp` の呼び出しを提案します。

:::comment
::example "Using {tactic}`simp?`"
:::
::::example "{tactic}`simp?` の使用"

:::comment
The non-terminal {tactic}`simp?` in this proof suggests a smaller {tactic}`simp` with {keywordOf Lean.Parser.Tactic.simp}`only`:
:::

この証明における非終端位置での {tactic}`simp?` は {keywordOf Lean.Parser.Tactic.simp}`only` を伴ったより小さい {tactic}`simp` を示唆します：

```lean (name:=simpHuhDemo)
example (xs : Array Unit) : xs.size = 2 → xs = #[(), ()] := by
  intros
  ext
  simp?
  assumption
```
:::comment
The suggested rewrite is:
:::



```leanOutput simpHuhDemo
Try this: simp only [Array.size_toArray, List.length_cons, List.length_singleton, Nat.reduceAdd]
```
:::comment
which results in the more maintainable proof:
:::

これはよりメンテナンス可能な証明になります：

```lean
example (xs : Array Unit) : xs.size = 2 → xs = #[(), ()] := by
  intros
  ext
  simp only [Array.size_toArray, List.length_cons, List.length_singleton, Nat.reduceAdd]
  assumption
```

::::


:::comment
# Configuring Simplification
:::

# 単純化の設定（Configuring Simplification）

%%%
tag := "simp-config"
%%%

:::comment
{tactic}`simp` is primarily configured via a configuration parameter, passed as a named argument called `config`.

:::

{tactic}`simp` は主に `config` という名前対の引数として渡される設定パラメータによって設定されます。

{docstring Lean.Meta.Simp.Config}

{docstring Lean.Meta.Simp.neutralConfig}

{docstring Lean.Meta.DSimp.Config}

:::comment
## Options
:::

## オプション（Options）
%%%
tag := "simp-options"
%%%


:::comment
Some global options affect {tactic}`simp`:

:::

いくつかのグローバルオプションが {tactic}`simp` に影響します：

{optionDocs simprocs}

{optionDocs tactic.simp.trace}

{optionDocs linter.unnecessarySimpa}

{optionDocs trace.Meta.Tactic.simp.rewrite}

{optionDocs trace.Meta.Tactic.simp.discharge}

:::comment
# Simplification vs Rewriting
:::

# 単純化と書き換え（Simplification vs Rewriting）
%%%
tag := "simp-vs-rw"
%%%



:::comment
Both {tactic}`simp` and {tactic}`rw`/{tactic}`rewrite` use equational lemmas to replace parts of terms with equivalent alternatives.
Their intended uses and their rewriting strategies differ, however.
Tactics in the {tactic}`simp` family are primarily used to reformulate a problem in a standardized way, making it more amenable to both human understanding and further automation.
In particular, simplification should never render an otherwise-provable goal impossible.
Tactics in the {tactic}`rw` family are primarily used to apply hand-selected transformations that do not always preserve provability nor place terms in standardized forms.
These different emphases are reflected in the differences of behavior between the two families of tactics.

:::

{tactic}`simp` と {tactic}`rw` ・ {tactic}`rewrite` はどちらも等式の補題を使用して、項の一部を同値な代替の項に置き換えます。しかし、それらの意図された用途と書き換え戦略は異なります。 {tactic}`simp` の族のタクティクは、主に標準化された方法で問題を再定式化するために使用され、人間の理解とさらなる自動化の両方に供します。特に、単純化することで、他に証明可能なゴールが不可能になるようなことがあってはなりません。 {tactic}`rw` の族のタクティクは主に手作業で選択された変換を適用するために使用されます。これは証明可能性を常に保持したり、項を標準化された形式に配置したりしません。これらの異なる強調点は、2つのタクティクの族の動作の違いに反映されています。

:::comment
The {tactic}`simp` tactics primarily rewrite from the inside out.
The smallest possible expressions are simplified first so that they can unlock further simplification opportunities for the surrounding expressions.
The {tactic}`rw` tactics select the leftmost outermost subterm that matches the pattern, rewriting it a single time.
Both tactics allow their strategy to be overridden: when adding a lemma to a simp set, the `↓` modifier causes it to be applied prior to the simplification of subterms, and the {name Lean.Meta.Rewrite.Config.occs}`occs` field of {tactic}`rw`'s configuration parameter allows a different occurrence to be selected, either via a whitelist or a blacklist.
:::

{tactic}`simp` タクティクは主に内側から外側へ書き換えます。可能な限り小さい式が最初に単純化され、周囲の式のさらなる単純化の機会を解放します。 {tactic}`rw` タクティクは、パターンにマッチする最も左の外側の部分項を選択し、それを1回だけ書き換えます。どちらのタクティクもその戦略を上書きすることができます：simp セットに補題を追加するとき、`↓` 修飾子は部分項の単純化の前に適用されるようにし、 {tactic}`rw` の設定パラメータの {name Lean.Meta.Rewrite.Config.occs}`occs` フィールドは複数の出現に対してホワイトリストかブラックリストのいずれかの選択を可能にします。
