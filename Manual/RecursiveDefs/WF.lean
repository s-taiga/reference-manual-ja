/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta
import Manual.Papers
import Manual.RecursiveDefs.WF.GuessLexExample

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

/-
#doc (Manual) "Well-Founded Recursion" =>
-/
#doc (Manual) "整礎再帰（Well-Founded Recursion）" =>
%%%
tag := "well-founded-recursion"
%%%

:::comment
Functions defined by {deftech}_well-founded recursion_ are those in which each recursive call has arguments that are _smaller_ (in a {ref "wf-rel"}[suitable sense]) than the functions' parameters.
In contrast to {ref "structural-recursion"}[structural recursion], in which recursive definitions must satisfy particular _syntactic_ requirements, definitions that use well-founded recursion employ _semantic_ arguments.
This allows a larger class of recursive definitions to be accepted.
Furthermore, when Lean's automation fails to construct a termination proof, it is possible to specify one manually.

:::

{deftech}_整礎再帰_ （well-founded recursion）によって定義される関数とは、各再帰呼び出しがその関数のパラメータよりも（ {ref "wf-rel"}[適切な意味] において） _小さい_ 引数を持つものを差します。 {ref "structural-recursion"}[構造的再帰] では再帰定義は特定の _構文的_ 要件を満たさなければならないことと対照的に、整礎再帰を使用する定義は _意味的_ な引数を使用します。これにより、より多くのクラスの再帰定義を受け入れることができます。さらに、Lean の自動化が停止証明を構築できない場合、手動で停止証明を指定することができます。

:::comment
All definitions are treated identically by the Lean compiler.
In Lean's logic, definitions that use well-founded recursion typically do not reduce {tech key:="definitional equality"}[definitionally].
The reductions do hold as propositional equalities, however, and Lean automatically proves them.
This does not typically make it more difficult to prove properties of definitions that use well-founded recursion, because the propositional reductions can be used to reason about the behavior of the function.
It does mean, however, that using these functions in types typically does not work well.
Even when the reduction behavior happens to hold definitionally, it is often much slower than structurally recursive definitions in the kernel, which must unfold the termination proof along with the definition.
When possible, recursive function that are intended for use in types or in other situations where definitional equality is important should be defined with structural recursion.

:::

すべての定義は Lean のコンパイラによって同じように扱われます。Lean の論理において、整礎再帰を使用した定義は通常、 {tech key:="definitional equality"}[definitionally] に簡約されません。しかしこの簡約は propositional equality として成立しており、Lean は自動的にこれを証明します。このため、整礎再帰を使用した定義の性質を証明することが難しくなることは通常ありません。なぜなら propositional の簡約は関数の挙動を推論するために使用できるからです。しかし、これらの関数を型で使用することは一般的にうまく行かないことを意味します。仮に簡約の挙動が definitionally に成立する場合であっても、カーネル内での構造的再帰に比べると、定義と共に停止の証明を展開しなければならないため、かなり遅くなることが多いです。可能であれば、型や definitional equality が重要な状況での使用を意図した再帰関数は、構造的再帰で定義されるべきです。

:::comment
To explicitly use well-founded recursion recursion, a function or theorem definition can be annotated with a {keywordOf Lean.Parser.Command.declaration}`termination_by` clause that specifies the {deftech}_measure_ by which the function terminates.
The measure should be a term that decreases at each recursive call; it may be one of the function's parameters or a tuple of the parameters, but it may also be any other term.
The measure's type must be equipped with a {tech}[well-founded relation], which determines what it means for the measure to decrease.

:::

整礎再帰を明示的に使用するには、関数または定理の定義に {keywordOf Lean.Parser.Command.declaration}`termination_by` 句を注釈して、関数の停止のための {deftech}_測度_ （measure）を指定します。この測度は、再帰呼び出しのたびに減少する項でなければなりません；これは関数のパラメータのうちのどれか1つ、またはパラメータのタプルである場合もありますが、それ以外の項である場合もあります。測度の型には {tech}[整礎関係] を指定する必要があります。これは測度の減少の意味を決定します。

::::syntax Lean.Parser.Termination.terminationBy (title := "Explicit Well-Founded Recursion")

:::comment
The {keywordOf Lean.Parser.Command.declaration}`termination_by` clause introduces the termination argument.

:::

{keywordOf Lean.Parser.Command.declaration}`termination_by` 句は停止引数を導入します。

```grammar
termination_by $[$_:ident* =>]? $term
```

:::comment
The identifiers before the optional `=>` can bring function parameters into scope that are not
already bound in the declaration header, and the mandatory term must indicate one of the function's parameters, whether introduced in the header or locally in the clause.
:::

オプションの `=>` の前の識別子には、宣言ヘッダでまだ束縛されていない関数のパラメータをスコープに入れることができます。必須の項には関数のパラメータの1つを指定しなければなりません。これにはヘッダもしくは句の中で局所的に導入されたもののどちらでも利用できます。

::::

:::comment
::example "Division by Iterated Subtraction"
:::
::::example "引き算の繰り返しによる割り算"
:::comment
Division can be specified as the number of times the divisor can be subtracted from the dividend.
This operation cannot be elaborated using structural recursion because subtraction is not pattern matching.
The value of `n` does decrease with each recursive call, so well-founded recursion can be used to justify the definition of division by iterated subtraction.

:::

割り算は被除数から除数を引く回数として指定できます。引き算はパターンマッチではないため、この演算を構造的再帰を使用してエラボレートすることはできません。`n` の値は再帰呼び出しのたびに減少するので、引き算の繰り返しによる除算の定義を正当化するために、整礎再帰を使用することができます。

```lean
def div (n k : Nat) : Nat :=
  if k = 0 then 0
  else if k > n then 0
  else 1 + div (n - k) k
termination_by n
```
::::

:::comment
# Well-Founded Relations
:::

# 整礎関係（Well-Founded Relations）

%%%
tag := "wf-rel"
%%%

:::comment
A relation `≺` is a {deftech}_well-founded relation_ if there exists no infinitely descending chain

:::

関係 `≺` が {deftech}_整礎関係_ （well-founded relation）であるとは、無限降鎖が存在しないことを指します。

$$`` x_0 ≻ x_1 ≻ \cdots``

:::comment
In Lean, types that are equipped with a canonical well-founded relation are instances of the {name}`WellFoundedRelation` type class.

:::

Lean では、標準的な整礎関係を持つ型は {name}`WellFoundedRelation` 型クラスのインスタンスです。

{docstring WellFoundedRelation}

```lean (show := false)
section
variable {α : Type u} {β : Type v} (a₁ a₂ : α) (b₁ b₂ : β) [WellFoundedRelation α] [WellFoundedRelation β]
variable {γ : Type u} (x₁ x₂ : γ) [SizeOf γ]
local notation x " ≺ " y => WellFoundedRelation.rel x y
```

:::comment
The most important instances are:

:::

最も重要なインスタンスは以下です：

:::comment
* {name}[`Nat`], ordered by {lean type:="Nat → Nat → Prop"}`(· < ·)`.

:::

* {name}[`Nat`] 、これは {lean type:="Nat → Nat → Prop"}`(· < ·)` で順序付けられます。

:::comment
* {name}[`Prod`], ordered lexicographically: {lean}`(a₁, b₁) ≺ (a₂, b₂)` if and only if {lean}`a₁ ≺ a₂` or {lean}`a₁ = a₂` and {lean}`b₁ ≺ b₂`.

:::

* {name}[`Prod`] 、辞書式順序で順序付けられます： {lean}`(a₁, b₁) ≺ (a₂, b₂)` であるのは {lean}`a₁ ≺ a₂` もしくは {lean}`a₁ = a₂` かつ {lean}`b₁ ≺ b₂` である場合に限ります。

:::comment
* Every type that is an instance of the {name}`SizeOf` type class, which provides a method {name}`SizeOf.sizeOf`, has a well-founded relation.
  For these types, {lean}`x₁ ≺ x₂` if and only if {lean}`sizeOf x₁ < sizeOf x₂`. For {tech}[inductive types], a {lean}`SizeOf` instance is automatically derived by Lean.

:::

* {name}`SizeOf` 型クラスのインスタンスであり、 {name}`SizeOf.sizeOf` メソッドを提供するすべての型は整礎関係を持ちます。これらの型では、 {lean}`x₁ ≺ x₂` であるのは {lean}`sizeOf x₁ < sizeOf x₂` である場合に限ります。 {tech}[帰納型] では、 {lean}`SizeOf` インスタンスは Lean によって自動的に導出されます。

```lean (show := false)
end
```

:::comment
Note that there exists a low-priority instance {name}`instSizeOfDefault` that provides a {lean}`SizeOf` instance for any type, and always returns {lean}`0`.
This instance cannot be used to prove that a function terminates using well-founded recursion because {lean}`0 < 0` is false.

:::

{lean}`SizeOf` インスタンスとして任意の型に対して低い優先度で {name}`instSizeOfDefault` インスタンスが提供されており、これは常に {lean}`0` を返すことに注意してください。 {lean}`0 < 0` が偽であるため、このインスタンスによる整礎関係を使用して関数が終了することを証明するために使用することができません。

```lean (show := false)

-- Check claims about instSizeOfDefault

example {α} (x : α) : sizeOf x = 0 := by rfl

/-- info: instSizeOfDefault.{u} (α : Sort u) : SizeOf α -/
#guard_msgs in
#check instSizeOfDefault

```

:::comment
::example "Default Size Instance"
:::
::::example "デフォルトの Size インスタンス"

:::comment
Function types in general do not have a well-founded relation that's useful for termination proofs.
{ref "instance-synth"}[Instance synthesis] thus selects {name}`instSizeOfDefault` and the corresponding well-founded relation.
If the measure is a function, the default {name}`SizeOf` instance is selected and the proof cannot succeed.

:::

一般的な関数型は、停止証明に有用な整礎関係を持ちません。このため、 {ref "instance-synth"}[インスタンス統合] は {name}`instSizeOfDefault` と対応する整礎関係を選択します。測度が関数の場合、デフォルトの {name}`SizeOf` インスタンスが選択されるため以下の証明は成功しません。

```lean (keep := false)
def fooInst (b : Bool → Bool) : Unit := fooInst (b ∘ b)
termination_by b
decreasing_by
  guard_target =
    @sizeOf (Bool → Bool) (instSizeOfDefault _) (b ∘ b) < sizeOf b
  simp only [sizeOf, default.sizeOf]
  guard_target = 0 < 0
  simp
  guard_target = False
  sorry
```
::::

:::comment
# Termination proofs
:::

# 停止証明（Termination proofs）


:::comment
Once a {tech}[measure] is specified and its {tech}[well-founded relation] is determined, Lean determines the termination proof obligation for every recursive call.

:::

{tech}[測度] が指定され、その {tech}[整礎関係] が決定されると、Lean はすべての再帰呼び出しの停止証明義務を決定します。

```lean (show := false)
section
variable {α : Type u} {β : α → Type v} {β' : Type v} (more : β') (g : (x : α) → (y : β x) → β' → γ) [WellFoundedRelation γ] (a₁ p₁ : α) (a₂ : β a₁) (p₂ : β p₁)

local notation (name := decRelStx) x " ≺ " y => WellFoundedRelation.rel x y
local notation "…" => more

```

:::comment
The proof obligation for each recursive call is of the form {lean}`g a₁ a₂ … ≺ g p₁ p₂ …`, where:
 * {lean}`g` is the measure as a function of the parameters,
 * {name WellFoundedRelation.rel}`≺` is the inferred well-founded relation,
 * {lean}`a₁` {lean}`a₂` {lean}`…` are the arguments of the recursive call and
 * {lean}`p₁` {lean}`p₂` {lean}`…` are the parameters of the function definition.

:::

各再帰呼び出しの証明義務は {lean}`g a₁ a₂ … ≺ g p₁ p₂ …` の形式となります：
 * {lean}`g` はこれらのパラメータの関数としての測度です。
 * {name WellFoundedRelation.rel}`≺` は推論される整礎関係です。
 * {lean}`a₁` {lean}`a₂` {lean}`…` は再帰呼び出しの引数であり、
 * {lean}`p₁` {lean}`p₂` {lean}`…` は関数定義のパラメータです。

:::comment
The context of the proof obligation is the local context of the recursive call.
In particular, local assumptions (such as those introduced by `if h : _`, `match h : _ with ` or `have`) are available.
If a function parameter is the {tech key:="match discriminant"}[discriminant] of a pattern match (e.g. by a {keywordOf Lean.Parser.Term.match}`match` expression), then this parameter is refined to the matched pattern in the proof obligation.

:::

この証明義務のコンテキストは、再帰呼び出しのローカルコンテキストです。具体的には、ローカルの仮定（`if h : _`・`match h : _ with `・`have` などで導入されるものなど）が利用できます。関数のパラメータが（例えば {keywordOf Lean.Parser.Term.match}`match` 式による）パターンマッチの {tech key:="マッチ判別子"}[判別子] である場合、このパラメータは証明義務の中でマッチしたパターンに絞り込まれます。

```lean (show := false)
end
```

:::comment
The overall termination proof obligation consists of one goal for each recursive call.
By default, the tactic {tactic}`decreasing_trivial` is used to prove each proof obligation.
A custom tactic script can be provided using the optional {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause, which comes after the {keywordOf Lean.Parser.Command.declaration}`termination_by` clause.
This tactic script is run once, with one goal for each proof obligation, rather than separately on each proof obligation.

:::

停止の証明義務の全体は、各再帰呼び出しに対する1つのゴールで構成されます。デフォルトでは、タクティク {tactic}`decreasing_trivial` が各証明義務の証明に使用されます。オプションの {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 句を使用することでカスタムのタクティクスクリプトを提供することができます。この句は {keywordOf Lean.Parser.Command.declaration}`termination_by` 句の後に来ます。このタクティクスクリプトは証明義務ごとに個別に実行されるのではなく、証明義務ごとに1つのゴールで1回実行されます。

```lean (show := false)
section
variable {n : Nat}
```

:::comment
::example "Termination Proof Obligations"
:::
::::example "停止の証明義務"

:::comment
The following recursive definition of the Fibonacci numbers has two recursive calls, which results in two goals in the termination proof.

:::

以下のフィボナッチ数の再帰的定義には2つの再帰的呼び出しがあり、これにより停止の証明には2つのゴールがあります。

```lean (error := true) (keep := false) (name := fibGoals)
def fib (n : Nat) :=
  if h : n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  skip
```

```leanOutput fibGoals (whitespace := lax) (show := false)
unsolved goals
   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 2 < n
```

```proofState
∀ (n : Nat), (h : ¬ n ≤ 1) → n - 1 < n ∧ n - 2 < n := by
  intro n h
  apply And.intro ?_ ?_
/--
n : Nat
h : ¬n ≤ 1
⊢ n - 1 < n

n : Nat
h : ¬n ≤ 1
⊢ n - 2 < n
-/

```



:::comment
Here, the {tech}[measure] is simply the parameter itself, and the well-founded order is the less-than relation on natural numbers.
The first proof goal requires the user to prove that the argument of the first recursive call, namely {lean}`n - 1`, is strictly smaller than the function's parameter, {lean}`n`.

:::

ここで、 {tech}[測度] は単にパラメータそのものであり、整礎順序は自然数の小なりの関係です。最初の証明のゴールでは、最初の再帰呼び出しの引数、すなわち {lean}`n - 1` が関数のパラメータ {lean}`n` より狭義に小さいことを証明することを要求します。

:::comment
Both termination proofs can be easily discharged using the {tactic}`omega` tactic.

:::

どちらの停止の証明も、 {tactic}`omega` タクティクを使って簡単に解消することができます。

```lean (keep := false)
def fib (n : Nat) :=
  if h : n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  · omega
  · omega
```
::::
```lean (show := false)
end
```

:::comment
::example "Refined Parameters"
:::
::::example "パラメータの絞り込み"

:::comment
If a parameter of the function is the {tech key:="match discriminant"}[discriminant] of a pattern match, then the proof obligations mention the refined parameter.

:::

関数のパラメータがパターンマッチの {tech key:="マッチ判別子"}[判別子] である場合、証明義務は絞り込まれたパラメータに言及します。

```lean (error := true) (keep := false) (name := fibGoals2)
def fib : Nat → Nat
  | 0 | 1 => 1
  | .succ (.succ n) => fib (n + 1) + fib n
termination_by n => n
decreasing_by
  skip
```
```leanOutput fibGoals2 (whitespace := lax) (show := false)
unsolved goals
n : Nat
⊢ n + 1 < n.succ.succ

n : Nat
⊢ n < n.succ.succ
```

```proofState
∀ (n : Nat), n + 1 < n.succ.succ ∧ n < n.succ.succ := by
  intro n
  apply And.intro ?_ ?_
/--
n : Nat
⊢ n + 1 < n.succ.succ

n : Nat
⊢ n < n.succ.succ
-/

```

::::

:::comment
Additionally, in the branches of {ref "if-then-else"}[if-then-else] expressions, a hypothesis asserting the current branch's condition is brought into scope, much as if the dependent if-then-else syntax had been used.


:::

さらに、 {ref "if-then-else"}[if-then-else] 式の分岐では、依存 if-then-else 構文を使用した場合と同様に、現在の分岐の条件を主張する仮定がスコープに入ります。

:::comment
::example "Local Assumptions and Conditionals"
:::
::::example "ローカルの仮定と条件"

:::comment
Here, the {keywordOf termIfThenElse}`if` does not bring a local assumption about the condition into scope. Nevertheless, it is available in the context of the termination proof.

:::

ここで、 {keywordOf termIfThenElse}`if` は条件についてのローカルの仮定をスコープに入れません。とはいえ、停止証明のコンテキストでは利用可能です。

```lean (error := true) (keep := false) (name := fibGoals3)
def fib (n : Nat) :=
  if n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  skip
```

```leanOutput fibGoals3 (whitespace := lax) (show := false)
unsolved goals
   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 2 < n
```

```proofState
∀ (n : Nat), («h✝» : ¬ n ≤ 1) → n - 1 < n ∧ n - 2 < n := by
  intro n «h✝»
  apply And.intro ?_ ?_
/--
n : Nat
h✝ : ¬n ≤ 1
⊢ n - 1 < n

n : Nat
h✝ : ¬n ≤ 1
⊢ n - 2 < n
-/

```



::::

```lean (show := false)
section
```

:::comment
::example "Nested Recursion in Higher-order Functions"
:::
::::example "高階関数の入れ子の再帰"

:::comment
When recursive calls are nested in higher-order functions, sometimes the function definition has to be adjusted so that the termination proof obligations can be discharged.
This often happens when defining functions recursively over {ref "nested-inductive-types"}[nested inductive types], such as the following tree structure:

:::

再帰呼び出しが高階関数に入れ子になっている場合、停止の証明義務が果たせるように関数定義を調整しなければならないことがあります。これは以下の木構造のように {ref "nested-inductive-types"}[入れ子の帰納型] 上で再帰的に関数を定義する際によく発生します：

```lean
structure Tree where
  children : List Tree
```

:::comment
A naïve attempt to define a recursive function over this data structure will fail:
:::

素朴にこのデータ構造に対して再帰関数を定義しようとすると失敗します：

```lean (keep := false) (name := nestedBad) (error := true)
def Tree.depth (t : Tree) : Nat :=
  let depths := t.children.map (fun c => Tree.depth c)
  match depths.max? with
  | some d => d+1
  | none => 0
termination_by t
```
```leanOutput nestedBad
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
t c : Tree
⊢ sizeOf c < sizeOf t
```

```lean (show := false)
variable (t : Tree) (c : Tree)
```


:::comment
The termination proof obligation is not provable, because there is no connection between the local variable {lean}`c` and the parameter {lean}`t`.
However, {name}`List.map` applies its function argument only to elements of the given list; thus, {lean}`c` is always an element of {lean}`t.children`.

:::

ローカル変数 {lean}`c` とパラメータ {lean}`t` の間に関連がないため、この停止の証明義務は証明できません。ただし、 {name}`List.map` は与えられたリストの要素にのみ関数の引数を適用します；そのため {lean}`c` は常に {lean}`t.children` の要素です。

:::comment
Because the termination proof goal provides access to the local context of the recursive call, it helps to bring facts into scope in the function definition that indicate that {lean}`c` is indeed an element of the list {lean}`t.children`.
This can be achieved by “attaching” a proof of membership in {lean}`t.children` to each of its elements using the function {name}`List.attach` and then bringing this proof into scope in the function passed to {name}`List.map`:

:::

停止証明のゴールは再帰呼び出しのローカルコンテキストへのアクセスを提供するため、 {lean}`c` が確かにリスト {lean}`t.children` の要素であることを示す事実を関数定義のスコープに入れることに役立ちます。これは、関数 {name}`List.attach` を使って {lean}`t.children` の各要素にメンバシップの証明を「アタッチ」し、 {name}`List.map` に渡された関数のスコープにこの証明を取り込むことで実現できます：

```lean (keep := false)
def Tree.depth (t : Tree) : Nat :=
  let depths := t.children.attach.map (fun ⟨c, hc⟩ => Tree.depth c)
  match depths.max? with
  | some d => d+1
  | none => 0
termination_by t
decreasing_by
  decreasing_tactic
```

:::comment
Note that the proof goal after {keywordOf Lean.Parser.Command.declaration}`decreasing_by` now includes the assumption {lean}`c ∈ t.children`, which suffices for {tactic}`decreasing_tactic` to succeed.

:::

{keywordOf Lean.Parser.Command.declaration}`decreasing_by` の後の証明ゴールには {lean}`c ∈ t.children` という仮定が含まれるようになり、 {tactic}`decreasing_tactic` が成功すれば十分であることに注意してください。

::::

```lean (show := false)
end
```


::::TODO

:::example "Nested recursive calls and subtypes"

I (Joachim) wanted to include a good example where recursive calls are nested inside each other, and one likely needs to introduce a subtype in the result to make it go through. But can't think of something nice and natural right now.

:::

::::

:::comment
# Default Termination Proof Tactic
:::

# デフォルトの停止証明タクティク（Default Termination Proof Tactic）


:::comment
If no {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause is given, then the {tactic}`decreasing_tactic` is used implicitly, and applied to each proof obligation separately.


:::

{keywordOf Lean.Parser.Command.declaration}`decreasing_by` 句が与えられない場合、 {tactic}`decreasing_tactic` が暗黙的に使用され、各証明義務に個別に適用されます。

::::tactic "decreasing_tactic" (replace := true)

:::comment
The tactic {tactic}`decreasing_tactic` mainly deals with lexicographic ordering of tuples, applying {name}`Prod.Lex.right` if the left components of the product are {tech (key := "definitional equality")}[definitionally equal], and {name}`Prod.Lex.left` otherwise.
After preprocessing tuples this way, it calls the {tactic}`decreasing_trivial` tactic.

:::

タクティク {tactic}`decreasing_tactic` は主にタプルの辞書式順序を扱い、直積の左成分が {tech (key := "definitional equality")}[definitionally equal] である場合には {name}`Prod.Lex.right` を、そうでない場合は {name}`Prod.Lex.left` を適用します。このようにタプルを前処理した後、 {tactic}`decreasing_trivial` タクティクを呼び出します。

::::


::::tactic "decreasing_trivial"

:::comment
The tactic {tactic}`decreasing_trivial` is an extensible tactic that applies a few common heuristics to solve a termination goal.
In particular, it tries the following tactics and theorems:

:::

タクティク {tactic}`decreasing_trivial` は拡張可能なタクティクであり、いくつかの一般的なヒューリスティックスを適用して停止ゴールを解きます。特に、以下のタクティクと定理を試行します：

:::comment
* {tactic}`simp_arith`
* {tactic}`assumption`
* theorems {name}`Nat.sub_succ_lt_self`, {name}`Nat.pred_lt'`, {name}`Nat.pred_lt`, which handle common arithmetic goals
* {tactic}`omega`
* {tactic}`array_get_dec` and {tactic}`array_mem_dec`, which prove that the size of array elements is less than the size of the array
* {tactic}`sizeOf_list_dec` that the size of list elements is less than the size of the list
* {name}`String.Iterator.sizeOf_next_lt_of_hasNext` and {name}`String.Iterator.sizeOf_next_lt_of_atEnd`, to handle iteration through a string using  {keywordOf Lean.Parser.Term.doFor}`for`

:::

* {tactic}`simp_arith`
* {tactic}`assumption`
* 定理 {name}`Nat.sub_succ_lt_self` ・ {name}`Nat.pred_lt'` ・ {name}`Nat.pred_lt` 、これらは共通の算術的ゴールを扱います
* {tactic}`omega`
* {tactic}`array_get_dec` と {tactic}`array_mem_dec` 、これは配列の要素のサイズが配列のサイズより小さいことを証明するものです
* {tactic}`sizeOf_list_dec` 、リストの要素のサイズがリストのサイズ未満であること
* {name}`String.Iterator.sizeOf_next_lt_of_hasNext` と {name}`String.Iterator.sizeOf_next_lt_of_atEnd` 、これは {keywordOf Lean.Parser.Term.doFor}`for` を用いた文字列に対する繰り返しを扱います

:::comment
This tactic is intended to be extended with further heuristics using {keywordOf Lean.Parser.Command.macro_rules}`macro_rules`.

:::

このタクティクは {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` を使用してヒューリスティックスをさらに拡張することを意図しています。

::::


:::comment
::example "No Backtracking of Lexicographic Order"
:::
::::example "辞書式順序のバックトラック無し"

:::comment
A classic example of a recursive function that needs a more complex {tech}[measure] is the Ackermann function:

:::

より複雑な {tech}[測度] を必要とする再帰関数の典型的な例としてアッカーマン関数が挙げられます：

```lean (keep := false)
def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)
```

:::comment
The measure is a tuple, so every recursive call has to be on arguments that are lexicographically smaller than the parameters.
The default {tactic}`decreasing_tactic` can handle this.

:::

ここでの測度はタプルであるため、すべての再帰呼び出しはパラメータよりも辞書式に小さい引数でなければなりません。これはデフォルトの {tactic}`decreasing_tactic` で扱うことができます。

:::comment
In particular, note that the third recursive call has a second argument that is smaller than the second parameter and a first argument that is definitionally equal to the first parameter.
This allowed  {tactic}`decreasing_tactic` to apply {name}`Prod.Lex.right`.

:::

特に、3番目の再帰呼び出しは2番目のパラメータよりも小さい2番目の引数と、1番目のパラメータに definitionally equal な1番目の引数を持つ点に注意してください。これにより、 {tactic}`decreasing_tactic` は {name}`Prod.Lex.right` を適用することが可能になっています。

```signature
Prod.Lex.right {α β} {ra : α → α → Prop} {rb : β → β → Prop}
  (a : α) {b₁ b₂ : β}
  (h : rb b₁ b₂) :
  Prod.Lex ra rb (a, b₁) (a, b₂)
```

:::comment
It fails, however, with the following modified function definition, where the third recursive call's first argument is provably smaller or equal to the first parameter, but not syntactically equal:

:::

しかし、3番目の再帰呼び出しの第1引数が1番目のパラメータ以下であることが証明できるものの構文的には等しくないように修正された次の関数定義では失敗します：

```lean (keep := false) (error := true) (name := synack)
def synack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => synack m 1
  | m + 1, n + 1 => synack m (synack (m / 2 + 1) n)
termination_by m n => (m, n)
```
```leanOutput synack (whitespace := lax)
failed to prove termination, possible solutions:
     - Use `have`-expressions to prove the remaining goals
     - Use `termination_by` to specify a different well-founded relation
     - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
case h
m n : Nat
⊢ m / 2 + 1 < m + 1
```

:::comment
Because {name}`Prod.Lex.right` is not applicable, the tactic used {name}`Prod.Lex.left`, which resulted in the unprovable goal above.

:::

{name}`Prod.Lex.right` が適用できないため、タクティクは {name}`Prod.Lex.left` を使用し、その結果上記の証明不可能なゴールが生まれています。

:::comment
This function definition may require a manual proof that uses the more general theorem {name}`Prod.Lex.right'`, which allows the first component of the tuple (which must be of type {name}`Nat`) to be less or equal instead of strictly equal:
:::

この関数定義では、より一般的な定理 {name}`Prod.Lex.right'` を使用した手作業による証明が必要になる場合があります。この定理では、タプルの最初のコンポーネント（これは {name}`Nat` 型でなければなりません）が狭義な等しさではなく未満であることを許容します：

```signature
Prod.Lex.right' {β} (rb : β → β → Prop)
  {a₂ : Nat} {b₂ : β} {a₁ : Nat} {b₁ : β}
  (h₁ : a₁ ≤ a₂) (h₂ : rb b₁ b₂) :
  Prod.Lex Nat.lt rb (a₁, b₁) (a₂, b₂)
```

```lean (keep := false)
def synack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => synack m 1
  | m + 1, n + 1 => synack m (synack (m / 2 + 1) n)
termination_by m n => (m, n)
decreasing_by
  · apply Prod.Lex.left
    omega
  -- the next goal corresponds to the third recursive call
  · apply Prod.Lex.right'
    · omega
    · omega
  · apply Prod.Lex.left
    omega
```

:::comment
The {tactic}`decreasing_tactic` tactic does not use the stronger {name}`Prod.Lex.right'` because it would require backtracking on failure.

:::

{tactic}`decreasing_tactic` タクティクは失敗時にバックトラックが必要になるため、より強力な {name}`Prod.Lex.right'` を使用しません。

::::

:::comment
# Inferring Well-Founded Recursion
:::

# 整礎再帰の推測（Inferring Well-Founded Recursion）

%%%
tag := "inferring-well-founded-recursion"
%%%

:::comment
If a recursive function definition does not indicate a termination {tech}[measure], Lean will attempt to discover one automatically.
If neither {keywordOf Lean.Parser.Command.declaration}`termination_by` nor {keywordOf Lean.Parser.Command.declaration}`decreasing_by` is provided, Lean will try to {ref "inferring-structural-recursion"}[infer structural recursion] before attempting well-founded recursion.
If a {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause is present, only well-founded recursion is attempted.

:::

再帰関数の定義で停止のための {tech}[測度] を指定しない場合、Lean は自動的に停止性を発見しようとします。 {keywordOf Lean.Parser.Command.declaration}`termination_by` と {keywordOf Lean.Parser.Command.declaration}`decreasing_by` のどちらも指定されていない場合、Lean は整礎再帰を試みる前に {ref "inferring-structural-recursion"}[構造的再帰の推測] を試みます。 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 句がある場合、整礎再帰のみが試みられます。

:::comment
To infer a suitable termination {tech}[measure], Lean considers multiple {deftech}_basic termination measures_, which are termination measures of type {name}`Nat`, and then tries all tuples of these measures.

:::

適切な停止のための {tech}[測度] を推論するために、Lean は {deftech}_基本停止測度_ （basic termination measure）を複数考慮します。これは {name}`Nat` 型の停止のための測度です。Lean はこれらの測度のすべてのタプルを試します。

:::comment
The basic termination measures considered are:

:::

基本停止測度としては以下が考慮されます：

:::comment
* all parameters whose type have a non-trivial {name}`SizeOf` instance
* the expression `e₂ - e₁` whenever the local context of a recursive call has an assumption of type `e₁ < e₂` or `e₁ ≤ e₂`, where `e₁` and `e₂` are of type {name}`Nat` and depend only on the function's parameters. {margin}[This approach is based on work by {citehere manolios2006}[].]
* in a mutual group, an additional basic measure is used to distinguish between recursive calls to other functions in the group and recursive calls to the function being defined (for details, see {ref "mutual-well-founded-recursion"}[the section on mutual well-founded recursion])

:::

* 非自明な {name}`SizeOf` インスタンスを持つすべてのパラメータ
* 再帰呼び出しのローカルコンテキストにおいて `e₁ < e₂` または `e₁ ≤ e₂` 型の仮定を持つ場合は式 `e₂ - e₁` 。ここで `e₁` と `e₂` は {name}`Nat` 型であり、関数のパラメータのみに依存します。 {margin}[このアプローチは {citehere manolios2006}[] の成果に基づいています。]
* 相互グループにおいて、グループ内の他の関数への再帰呼び出しと、定義されている関数自身への再帰呼び出しを区別するために、追加の基本測度が使用されます。（詳細については {ref "mutual-well-founded-recursion"}[相互整礎再帰の節] を参照してください）。

:::comment
{deftech}_Candidate measures_ are basic measures or tuples of basic measures.
If any of the candidate measures allow all proof obligations to be discharged by the termination proof tactic (that is, the tactic specified by {keywordOf Lean.Parser.Command.declaration}`decreasing_by`, or {tactic}`decreasing_trivial` if there is no {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause), then an arbitrary such candidate measure is selected as the automatic termination measure.

:::

{deftech}_測度候補_ （candidate measure）は基本測度または基本測度のタプルです。測度候補のいずれかが停止証明タクティク（つまり {keywordOf Lean.Parser.Command.declaration}`decreasing_by` で指定されるタクティク、もしくは {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 句が無い場合は {tactic}`decreasing_trivial` で指定されるタクティク）によってすべての証明義務を解消できる場合、そのような任意の測度候補が自動停止測度として選択されます。

:::comment
A {keyword}`termination_by?` clause causes the inferred termination annotation to be shown.
It can be automatically added to the source file using the offered suggestion or code action.

:::

{keyword}`termination_by?` 句を指定すると、推論された停止の注釈が表示されます。これは提案に対するサジェスト、またはコードアクションを使用してソースファイルに自動的に追加することができます。

:::comment
To avoid the combinatorial explosion of trying all tuples of measures, Lean first tabulates all {tech}[basic termination measures], determining whether the basic measure is decreasing, strictly decreasing, or non-decreasing.
A decreasing measure is smaller for at least one recursive call and never increases at any recursive call, while a strictly decreasing measure is smaller at all recursive calls.
A non-decreasing measure is one that the termination tactic could not show to be decreasing or strictly decreasing.
A suitable tuple is chosen based on the table.{margin}[This approach is based on {citehere bulwahn2007}[].]
This table shows up in the error message when no automatic measure could be found.

:::

測度についてすべてのタプルを試行することによる組み合わせ爆発を避けるために、Lean はまず {tech}[基本停止測度] を集計し、基本測度が減少的・狭義に減少的・非減少的のどれであるかを決定します。減少的な測度とは少なくとも1つの再帰呼び出しに対して小さくなり、任意の再帰呼び出しにおいて決して増加しないものを指します。一方、狭義に減少的な測度はすべての再帰呼び出しに対して小さくなります。非減少的な測度は停止タクティクが減少または狭義に減少することを示せないような測度です。こうして得られたテーブルに基づいて適切なタプルが選択されます。 {margin}[このアプローチは {citehere bulwahn2007}[] に基づいています。] このテーブルは、測度が自動的に見つからなかった時のエラーメッセージに表示されます。

{spliceContents Manual.RecursiveDefs.WF.GuessLexExample}

```lean (show := false)
section
variable {e₁ e₂ i j : Nat}
```
:::comment
::example "Array Indexing"
:::
::::example "配列のインデキシング"

:::comment
The purpose of considering expressions of the form {lean}`e₂ - e₁` as measures is to support the common idiom of counting up to some upper bound, in particular when traversing arrays in possibly interesting ways.
In the following function, which performs binary search on a sorted array, this heuristic helps Lean to find the {lean}`j - i` measure.

:::

{lean}`e₂ - e₁` の形式の式を測度と見なす目的は、ある上限までカウントするという一般的なイディオムをサポートすることであり、これは特に興味深い方法で配列を走査するような場合が該当します。ソート済みの配列に対して二分木探索を実行する以下の関数では、このヒューリスティックスは Lean が測度として {lean}`j - i` を見つけるのに役立ちます。

```lean (name := binarySearch)
def binarySearch (x : Int) (xs : Array Int) : Option Nat :=
  go 0 xs.size
where
  go (i j : Nat) (hj : j ≤ xs.size := by omega) :=
    if h : i < j then
      let mid := (i + j) / 2
      let y := xs[mid]
      if x = y then
        some mid
      else if x < y then
        go i mid
      else
        go (mid + 1) j
    else
      none
  termination_by?
```

:::comment
The fact that the inferred termination argument uses some arbitrary measure, rather than an optimal or minimal one, is visible in the inferred measure, which contains a redundant `j`:
:::

この推測された停止引数が、最適または最小の測度ではなく、複数の任意の測度を使用しているという事実は、冗長な `j` を含む推測された測度を見ることでわかります：

```leanOutput binarySearch
Try this: termination_by (j, j - i)
```

::::

```lean (show := false)
end
```

:::comment
::example "Termination Proof Tactics During Inference"
:::
::::example "推測中における停止証明のタクティク"

:::comment
The tactic indicated by {keywordOf Lean.Parser.Command.declaration}`decreasing_by` is used slightly differently when inferring the termination {tech}[measure] than it is in the actual termination proof.

:::

{keywordOf Lean.Parser.Command.declaration}`decreasing_by` で示されるタクティクは、停止 {tech}[測度] を推論する際において、実際の停止証明のときとは少し違った使われ方をします。

:::comment
* During inference, it is applied to a _single_ goal, attempting to prove {name LT.lt}`<` or {name LE.le}`≤` on {name}`Nat`.
* During the termination proof, it is applied to many simultaneous goals (one per recursive call), and the goals may involve the lexicographic ordering of pairs.

:::

* 推論中において、このタクティクは {name}`Nat` 上の {name LT.lt}`<` または {name LE.le}`≤` を証明しようとする _単一の_ ゴールに適用されます。
* 停止証明において、このタクティクは多くの同時ゴール（再帰呼び出しごとに1つ）に適用されます。これらのゴールはペアの辞書式順序を含む可能性があります。

:::comment
A consequence is that a {keywordOf Lean.Parser.Command.declaration}`decreasing_by` block that addresses goals individually and which works successfully with an explicit termination argument can cause inference of the termination measure to fail:

:::

その結果、ゴールに個別にアクセスし、明示的な停止引数で正常に動作するような {keywordOf Lean.Parser.Command.declaration}`decreasing_by` ブロックが停止測度の推論に失敗することがあります：

```lean (keep := false) (error := true)
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
decreasing_by
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    omega
  · apply Prod.Lex.left
    omega
```

:::comment
It is advisable to always include a {keywordOf Lean.Parser.Command.declaration}`termination_by` clause whenever an explicit {keywordOf Lean.Parser.Command.declaration}`decreasing_by` proof is given.

:::

明示的な {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 証明が与えられた場合は、常に {keywordOf Lean.Parser.Command.declaration}`termination_by` 句を含めることをお勧めします。

::::

:::comment
::example "Inference too powerful"
:::
::::example "強力すぎる推論"

:::comment
Because {tactic}`decreasing_tactic` avoids the need to backtrack by being incomplete with regard to lexicographic ordering, Lean may infer a termination {tech}[measure] that leads to goals that the tactic cannot prove.
In this case, the error message is the one that results from the failing tactic rather than the one that results from being unable to find a measure.
This is what happens in {lean}`notAck`:

:::

{tactic}`decreasing_tactic` は辞書式順序に対して不完全であることによってバックトラックの必要性を回避するため、Lean はタクティクが証明できないゴールを導く停止 {tech}[測度] を推論する場合があります。この場合、エラーメッセージは測度を見つけることができなかったことによるものではなく、タクティクが失敗したことによるものです。これは以下の {lean}`notAck` で見ることができます：

```lean (error := true) (name := badInfer)
def notAck : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => notAck m 1
  | m + 1, n + 1 => notAck m (notAck (m / 2 + 1) n)
decreasing_by all_goals decreasing_tactic
```
```leanOutput badInfer
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
case h
m n : Nat
⊢ m / 2 + 1 < m + 1
```

:::comment
In this case, explicitly stating the termination {tech}[measure] helps.

:::

この場合、停止 {tech}[測度] を明示することが有効です。

::::

:::comment
# Mutual Well-Founded Recursion
:::

# 相互整礎再帰（Mutual Well-Founded Recursion）

%%%
tag := "mutual-well-founded-recursion"
%%%

:::comment
Lean supports the definition of {tech}[mutually recursive] functions using {tech}[well-founded recursion].
Mutual recursion may be introduced using a {tech}[mutual block], but it also results from {keywordOf Lean.Parser.Term.letrec}`let rec` expressions and {keywordOf Lean.Parser.Command.declaration}`where` blocks.
The rules for mutual well-founded recursion are applied to a group of actually mutually recursive, lifted definitions, that results from the {ref "mutual-syntax"}[elaboration steps] for mutual groups.

:::

Lean は {tech}[整礎再帰] を使った {tech}[相互再帰] 関数の定義をサポートしています。相互再帰は {tech}[相互ブロック] を使って導入することができますが、 {keywordOf Lean.Parser.Term.letrec}`let rec` 式と {keywordOf Lean.Parser.Command.declaration}`where` ブロックによっても得ることができます。相互整礎再帰の規則は {ref "mutual-syntax"}[エラボレーションのステップ] の相互グループの結果である、実際に相互再帰的で持ち上げられた定義のグループに適用されます。

:::comment
If any function in the mutual group has a {keywordOf Lean.Parser.Command.declaration}`termination_by` or {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause, well-founded recursion is attempted.
If a termination {tech}[measure] is specified using {keywordOf Lean.Parser.Command.declaration}`termination_by` for _any_ function in the mutual group, then _all_ functions in the group must specify a termination measure, and they have to have the same type.

:::

相互グループ内の関数が {keywordOf Lean.Parser.Command.declaration}`termination_by` または {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 句を持つ場合、整礎再帰が試みられます。もし相互グループ内の _任意の_ 関数に対して {keywordOf Lean.Parser.Command.declaration}`termination_by` を使用して停止 {tech}[測度] を指定した場合、グループ内の _全ての_ 関数は停止測度を指定する必要があり、それらは同じ型でなければなりません。

:::comment
If no termination argument is specified, the termination argument is {ref "inferring-well-founded-recursion"}[inferred, as described above]. In the case of mutual recursion, a third class of basic measures is considered during inference, namely for each function in the mutual group the measure that is `1` for that function and `0` for the others. This allows Lean to order the functions so that some calls from one function to another are allowed even if the parameters do not decrease.

:::

停止引数が指定されていない場合、停止引数は {ref "inferring-well-founded-recursion"}[上述したように推論されます] 。相互再帰の場合、推論において基本測度の低級な、すなわち、相互グループ内の各関数に対してその関数に対しては `1`、他の関数に対して `0` である測度が考慮されます。これによって Lean はパラメータが減少しなくても、ある関数から別の関数への呼び出しが許可されるように関数を並べることができます。

:::comment
::example "Mutual recursion without parameter decrease"
:::
::::example "パラメータが減少しない相互再帰"

:::comment
In the following mutual function definitions, the parameter does not decrease in the call from {lean}`g` to {lean}`f`.
Nonetheless, the definition is accepted due to the ordering imposed on the functions themselves by the additional basic measure.

:::

以下の相互関数定義では、 {lean}`g` から {lean}`f` への呼び出しにおいてパラメータは減少しません。それにもかかわらず、この定義は、追加の基本測度によって関数自体に課される順序によって許容されます。

```lean (name := fg)
mutual
  def f : (n : Nat) → Nat
    | 0 => 0
    | n+1 => g n
  termination_by?

  def g (n : Nat) : Nat := (f n) + 1
  termination_by?
end
```

:::comment
The inferred termination argument for {lean}`f` is:
:::

{lean}`f` の推測された停止引数は以下です：

```leanOutput fg
Try this: termination_by n => (n, 0)
```

:::comment
The inferred termination argument for {lean}`g` is:
:::

{lean}`g` の推測された停止引数は以下です：

```leanOutput fg
Try this: termination_by (n, 1)
```

::::

:::comment
# Theory and Construction
:::

# 理論と構成（Theory and Construction）


```lean (show := false)
section
variable {α : Type u}
```

:::comment
This section gives a very brief glimpse into the mathematical constructions that underlie termination proofs via {tech}[well-founded recursion], which may surface occasionally.
The elaboration of functions defined by well-founded recursion is based on the {name}`WellFounded.fix` operator.

:::

本節では、 {tech}[整礎再帰] による停止証明の根底にある数学的構造をごく簡単に紹介します。整礎再帰で定義された関数のエラボレーションは {name}`WellFounded.fix` 演算子に基づいています。

{docstring WellFounded.fix}

:::comment
The type {lean}`α` is instantiated with the function's (varying) parameters, packed into one type using {name}`PSigma`.
The {name}`WellFounded` relation is constructed from the termination {tech}[measure] via {name}`invImage`.

:::

型 {lean}`α` は関数の（変換する）パラメータによってインスタンス化され、 {name}`PSigma` を用いて1つの型にまとめられます。 {name}`WellFounded` 関係は {name}`invImage` を介して停止 {tech}[測度] から構築されます。

{docstring invImage}

:::comment
The function's body is passed to {name}`WellFounded.fix`, with parameters suitably packed and unpacked, and recursive calls are replaced with a call to the value provided by {name}`WellFounded.fix`.
The termination proofs generated by the {keywordOf Lean.Parser.Command.declaration}`decreasing_by` tactics are inserted in the right place.

:::

関数の本体は {name}`WellFounded.fix` に渡され、パラメータは適切にパックおよびアンパックされ、再帰呼び出しは {name}`WellFounded.fix` が提供する値への呼び出しに置き換えられます。 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` タクティクによって生成された停止証明は適切な位置に挿入されます。

:::comment
Finally, the equational and unfolding theorems for the recursive function are proved from {name}`WellFounded.fix_eq`.
These theorems hide the details of packing and unpacking arguments and describe the function's behavior in terms of the original definition.

:::

最後に、 {name}`WellFounded.fix_eq` から再帰関数の等式定理と展開の定理が証明されます。これらの定理は引数のパッキングとアンパッキングの詳細を隠蔽し、もとの定義の観点から関数の動作を記述します。

:::comment
In the case of mutual recursion, an equivalent non-mutual function is constructed by combining the function's arguments using {name}`PSum`, and pattern-matching on that sum type in the result type and the body.

:::

相互再帰の場合、 {name}`PSum` を使って関数の引数を組み合わせ、その直和型をパターンマッチすることで同等の非相互関数が構築されます。

:::comment
The definition of {name}`WellFounded` builds on the notion of _accessible elements_ of the relation:

:::

{name}`WellFounded` の定義は、その関係の _アクセス可能な要素_ （accessible element）という概念に基づいています。

{docstring WellFounded}

{docstring Acc}

:::comment
:: example "Division by Iterated Subtraction: Termination Proof"
:::
:::: example "引き算の繰り返しによる割り算：停止証明"

:::comment
The definition of division by iterated subtraction can be written explicitly using well-founded recursion.
:::

引き算の繰り返しによる割り算の定義は、整礎再帰を使って明示的に描くことができます。

```lean
noncomputable def div (n k : Nat) : Nat :=
  (inferInstanceAs (WellFoundedRelation Nat)).wf.fix
    (fun n r =>
      if h : k = 0 then 0
      else if h : k > n then 0
      else 1 + (r (n - k) <| by
        show (n - k) < n
        omega))
    n
```
:::comment
The definition must be marked {keywordOf Lean.Parser.Command.declaration}`noncomputable` because well-founded recursion is not supported by the compiler.
Like {tech}[recursors], it is part of Lean's logic.

:::

整礎再帰はコンパイラにサポートされていないため、この定義は {keywordOf Lean.Parser.Command.declaration}`noncomputable` をマークしなければなりません。 {tech}[再帰子] と同様に、これは Lean の論理の一部です。

:::comment
The definition of division should satisfy the following equations:

:::

割り算の定義は以下の式を満たす必要があります：
 * {lean}`∀{n k : Nat}, (k = 0) → div n k = 0`
 * {lean}`∀{n k : Nat}, (k > n) → div n k = 0`
 * {lean}`∀{n k : Nat}, (k ≠ 0) → (¬ k > n) → div n k = div (n - k) k`

:::comment
This reduction behavior does not hold {tech key:="definitional equality"}[definitionally]:
:::

この簡約の挙動は {tech key:="definitional equality"}[definitionally] に保持されません：

```lean (error := true) (name := nonDef) (keep := false)
theorem div.eq0 : div n 0 = 0 := by rfl
```
```leanOutput nonDef
tactic 'rfl' failed, the left-hand side
  div n 0
is not definitionally equal to the right-hand side
  0
n : Nat
⊢ div n 0 = 0
```
:::comment
However, using `WellFounded.fix_eq` to unfold the well-founded recursion, the three equations can be proved to hold:
:::

しかし、 `WellFounded.fix_eq` を使って整礎再帰を展開すれば、3つの等式が成り立つことが証明できます：

```lean
theorem div.eq0 : div n 0 = 0 := by
  unfold div
  apply WellFounded.fix_eq

theorem div.eq1 : k > n → div n k = 0 := by
  intro h
  unfold div
  rw [WellFounded.fix_eq]
  simp only [gt_iff_lt, dite_eq_ite, ite_eq_left_iff, Nat.not_lt]
  intros; omega

theorem div.eq2 :
    ¬ k = 0 → ¬ (k > n) →
    div n k = 1 + div (n - k) k := by
  intros
  unfold div
  rw [WellFounded.fix_eq]
  simp_all only [
    gt_iff_lt, Nat.not_lt,
    dite_false, dite_eq_ite,
    ite_false, ite_eq_right_iff
  ]
  omega
```
::::
