/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.Language.Functions
import Manual.Language.InductiveTypes

open Verso.Genre Manual

set_option maxRecDepth 800

/-
#doc (Manual) "The Type System" =>
-/
#doc (Manual) "型システム（The Type System）" =>
%%%
tag := "type-system"
%%%

:::comment
{deftech}_Terms_, also known as {deftech}_expressions_, are the fundamental units of meaning in Lean's core language.
They are produced from user-written syntax by the {tech}[elaborator].
Lean's type system relates terms to their _types_, which are also themselves terms.
Types can be thought of as denoting sets, while terms denote individual elements of these sets.
A term is {deftech}_well-typed_ if it has a type under the rules of Lean's type theory.
Only well-typed terms have a meaning.

:::

{deftech}_項_ （term）は {deftech}_式_ （expression）としても知られ、Lean のコア言語における意味の基本単位です。これらは {tech}[エラボレータ] によってユーザが書いた構文から生成されます。Lean の型システムは項をその _型_ （type）に関連付けます。型は集合を表し、項は集合の個々の要素を表すと考えることができます。Lean の型理論のルールに従った型を持つ項は {deftech}_well-typed_ と言います。well-typed である項のみが意味を持ちます。

:::comment
Terms are a dependently typed λ-calculus: they include function abstraction, application, variables, and `let`-bindings.
In addition to bound variables, variables in the term language may refer to {tech}[constructors], {tech}[type constructors], {tech}[recursors], {deftech}[defined constants], or opaque constants.
Constructors, type constructors, recursors, and opaque constants are not subject to substitution, while defined constants may be replaced with their definitions.

:::

項は依存型付きラムダ計算です；関数抽象・適用・変数・`let` 束縛を含みます。束縛変数に加えて、項言語の変数は {tech}[コンストラクタ] ・ {tech}[型コンストラクタ] ・ {tech}[再帰子] ・ {deftech}[defined constants] ・不透明な定数を参照することができます。コンストラクタ・型コンストラクタ・再帰子・不透明な定数は置換の対象にはなりませんが、定義された定数はその定義に置き換えることができます。

:::comment
A {deftech}_derivation_ demonstrates the well-typedness of a term by explicitly indicating the precise inference rules that are used.
Implicitly, well-typed terms can stand in for the derivations that demonstrate their well-typedness.
Lean's type theory is explicit enough that derivations can be reconstructed from well-typed terms, which greatly reduces the overhead that would be incurred from storing a complete derivation, while still being expressive enough to represent modern research mathematics.
This means that proof terms are sufficient evidence of the truth of a theorem and are amenable to independent verification.

:::

{deftech}_導出_ （derivation）は使用される正確な推論規則を明示的に示すことで項の well-typed さを示します。暗黙的に、well-typed な項は、その well-typed であることを示す導出の代わりにすることができます。Lean の型理論は十分に明示的であるため、well-typed な項から導出を再構築することができ、完全な導出を保存することで発生するオーバーヘッドを大幅に削減することができるにもかかわらず、この理論は現代の研究数学を表現するに足る表現力を保ちます。これは、証明項が定理の真理の十分な根拠となり、独立した検証が可能であることを意味します。

:::comment
In addition to having types, terms are also related by {deftech}_definitional equality_.
This is the mechanically-checkable relation that equates terms modulo their computational behavior.
Definitional equality includes the following forms of {deftech}[reduction]:

:::

型を持つことに加えて、項は {deftech}_定義上の等価性_ （definitional equality）によっても関連付けられます。これは機械的にチェック可能な関係であり、計算動作に応じて項を等しくします。定義上の等価性には {deftech}[簡約] （reduction）の以下の形式が含まれます：

:::comment
 : {deftech}[β] (beta)

    Applying a function abstraction to an argument by substitution for the bound variable

:::

 : {deftech}[β] (beta)

    束縛された変数への置換によって、引数に関数抽象を適用する

:::comment
 : {deftech}[δ] (delta)

    Replacing occurrences of {tech}[defined constants] by the definition's value

:::

 : {deftech}[δ] (delta)

    {tech}[defined constant] の出現箇所を定義の値で置き換える

:::comment
 : {deftech}[ι] (iota)

    Reduction of recursors whose targets are constructors (primitive recursion)

:::

 : {deftech}[ι] (iota)

    コンストラクタをターゲットとする再帰子の簡約（原始再帰）

:::comment
 : {deftech}[ζ] (zeta)

     Replacement of let-bound variables by their defined values

:::

 : {deftech}[ζ] (zeta)

    let 束縛変数を定義された値に置き換える

:::comment
Terms in which all possible reductions have been carried out are in {deftech}_normal form_.

:::

すべての可能な簡約が行われた項は {deftech}_正規形_ （normal form）となります。

::::keepEnv
```lean (show := false)
axiom α : Type
axiom β : Type
axiom f : α → β

structure S where
  f1 : α
  f2 : β

axiom x : S

-- test claims in next para

example : (fun x => f x) = f := by rfl
example : S.mk x.f1 x.f2 = x := by rfl

export S (f1 f2)
```

:::comment
Definitional equality includes η-equivalence of functions and single-constructor inductive types.
That is, {lean}`fun x => f x` is definitionally equal to {lean}`f`, and {lean}`S.mk x.f1 x.f2` is definitionally equal to {lean}`x`, if {lean}`S` is a structure with fields {lean}`f1` and {lean}`f2`.
It also features proof irrelevance, so any two proofs of the same proposition are definitionally equal.
It is reflexive, symmetric, and a congruence.
:::

定義上の等価性には関数と単一コンストラクタの帰納型についてのη同値が含まれます。つまり、 {lean}`fun x => f x` は {lean}`f` に定義上等しく、 {lean}`S` がフィールド {lean}`f1` と {lean}`f2` を持つ構造体である時には {lean}`S.mk x.f1 x.f2` は {lean}`x` と定義上等価です。また証明の irrelevance も特徴づけ、同じ命題の2つの証明は定義上等価です。これは反射的・対称的・合同です。

::::

:::comment
Definitional equality is used by conversion: if two terms are definitionally equal, and a given term has one of them as its type, then it also has the other as its type.
Because definitional equality includes reduction, types can result from computations over data.

:::

定義上の等価性は変換にも用いられます：2つの項が定義上等しく、ある項がその一方を型として持つ場合、その項ももう一方を型として持ちます。定義上の等価性は簡約を含むため、データに対する計算から型が生じることがあります。

:::::keepEnv
:::comment
::Manual.example "Computing types"
:::
::::Manual.example "型の計算"

:::comment
When passed a natural number, the function {lean}`LengthList` computes a type that corresponds to a list with precisely that many entries in it:

:::

自然数を渡すと、関数 {lean}`LengthList` は正確にその数のエントリを持つリストに対応する型を計算します：

```lean
def LengthList (α : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => α × LengthList α n
```

:::comment
Because Lean's tuples nest to the right, multiple nested parentheses are not needed:
:::

Lean のタプルは右側にネストしているため、複数のネストした括弧は必要ありません：

````lean
example : LengthList Int 0 := ()

example : LengthList String 2 :=
  ("Hello", "there", ())
````

:::comment
If the length does not match the number of entries, then the computed type will not match the term:
:::

長さが項目数と一致しない場合、計算された型はその項と一致しません：

```lean error:=true name:=wrongNum
example : LengthList String 5 :=
  ("Wrong", "number", ())
```
```leanOutput wrongNum
application type mismatch
  ("number", ())
argument
  ()
has type
  Unit : Type
but is expected to have type
  LengthList String 3 : Type
```
::::
:::::

:::comment
The basic types in Lean are {tech}[universes], {tech}[function] types, and {tech}[type constructors] of {tech}[inductive types].
{tech}[Defined constants], applications of {tech}[recursors], function application, {tech}[axioms] or {tech}[opaque constants] may additionally give types, just as they can give rise to terms in any other type.


:::

Lean の基本型は {tech}[宇宙] ・ {tech}[関数] 型・ {tech}[帰納型] の {tech}[型コンストラクタ] です。 {tech}[Defined constants] ・ {tech}[再帰子] の適用・関数適用・ {tech}[axioms] ・ {tech}[不透明な定数] のいずれかは他の型の項を生じさせることができるのと同様に、さらに型を与えることができます。

{include Manual.Language.Functions}

# 命題（Propositions）
%%%
tag := "propositions"
%%%

:::comment
-- エラーが出るため章タイトルの上下を入れ替えている
# Propositions
:::

:::comment
{deftech}[Propositions] are meaningful statements that admit proof. {index}[proposition]
Nonsensical statements are not propositions, but false statements are.
All propositions are classified by {lean}`Prop`.

:::

{deftech}[命題] （propositioin）は証明を認める意味のある文です。 {index}[proposition] 無意味な文は命題ではありませんが、偽の文は命題です。すべての命題は {lean}`Prop` によって分類されます。

:::comment
Propositions have the following properties:

:::

命題は以下の性質を持ちます：

:::comment
: Definitional proof irrelevance

  Any two proofs of the same proposition are completely interchangeable.

:::

: 定義上の証明の irrelevance

  同じ命題の2つの証明は完全に交換可能です。

:::comment
: Run-time irrelevance

  Propositions are erased from compiled code.

:::

: ランタイムにおける irrelevance

  命題はコンパイルされたコードからは消去されます。

:::comment
: Impredicativity

  Propositions may quantify over types from any universe whatsoever.

:::

: 非可述性

  命題はあらゆる宇宙からの型に対して量化することができます。

:::comment
: Restricted Elimination

  With the exception of {tech}[subsingletons], propositions cannot be eliminated into non-proposition types.

:::

: 制限された除去

  {tech}[subsingletons] を除いて、命題は非命題型に除去することができません。

:::comment
: {deftech key:="propositional extensionality"}[Extensionality] {index subterm:="of propositions"}[extensionality]

  Any two logically equivalent propositions can be proven to be equal with the {lean}`propext` axiom.

:::

: {deftech key:="propositional extensionality"}[外延性] {index subterm:="of propositions"}[extensionality]

  論理的に同等な2つの命題は、 {lean}`propext` 公理によって等しいことが証明できます。

{docstring propext}

:::comment
# Universes

:::

:::comment
Types are classified by {deftech}_universes_. {index}[universe]
Each universe has a {deftech (key:="universe level")}_level_, {index subterm := "of universe"}[level] which is a natural number.
The {lean}`Sort` operator constructs a universe from a given level. {index}[`Sort`]
If the level of a universe is smaller than that of another, the universe itself is said to be smaller.
With the exception of propositions (described later in this chapter), types in a given universe may only quantify over types in smaller universes.
{lean}`Sort 0` is the type of propositions, while each `Sort (u + 1)` is a type that describes data.

:::

型は {deftech}_宇宙_ （universe）によって分類されます。 {index}[universe] 各宇宙には {deftech (key:="universe level")}_レベル_ （level）があり、これは自然数です。 {lean}`Sort` 演算子は与えられたレベルから宇宙を構築します。 {index}[`Sort`] ある宇宙レベルが他の宇宙レベルよりも小さい場合、その宇宙自体も小さいと言います。命題を除いて（この章で後述）、与えられた宇宙内の型はより小さい宇宙内の型に対してのみ量化することができます。 {lean}`Sort 0` は命題の型であり、各 `Sort (u + 1)` はデータを記述する型です。

:::comment
Every universe is an element of every strictly larger universe, so {lean}`Sort 5` includes {lean}`Sort 4`.
This means that the following examples are accepted:
:::

すべての宇宙はすべての狭義に大きな宇宙の要素なので、 {lean}`Sort 5` は {lean}`Sort 4` を含みます。つまり、以下の例が認められます：

```lean
example : Sort 5 := Sort 4
example : Sort 2 := Sort 1
```

:::comment
On the other hand, {lean}`Sort 3` is not an element of {lean}`Sort 5`:
:::

一方で、 {lean}`Sort 3` は {lean}`Sort 5` の要素ではありません：

```lean (error := true) (name := sort3)
example : Sort 5 := Sort 3
```

```leanOutput sort3
type mismatch
  Type 2
has type
  Type 3 : Type 4
but is expected to have type
  Type 4 : Type 5
```

:::comment
Similarly, because {lean}`Unit` is in {lean}`Sort 1`, it is not in {lean}`Sort 2`:
:::

同様に、 {lean}`Unit` は {lean}`Sort 1` に存在するため、 {lean}`Sort 2` には存在しません：

```lean
example : Sort 1 := Unit
```
```lean error := true name := unit1
example : Sort 2 := Unit
```

```leanOutput unit1
type mismatch
  Unit
has type
  Type : Type 1
but is expected to have type
  Type 1 : Type 2
```

:::comment
Because propositions and data are used differently and are governed by different rules, the abbreviations {lean}`Type` and {lean}`Prop` are provided to make the distinction more convenient.  {index}[`Type`] {index}[`Prop`]
`Type u` is an abbreviation for `Sort (u + 1)`, so {lean}`Type 0` is {lean}`Sort 1` and {lean}`Type 3` is {lean}`Sort 4`.
{lean}`Type 0` can also be abbreviated {lean}`Type`, so `Unit : Type` and `Type : Type 1`.
{lean}`Prop` is an abbreviation for {lean}`Sort 0`.

:::

命題とデータは異なる使われ方をし、異なる規則に支配されるため、より便利に区別するために {lean}`Type` と {lean}`Prop` という省略形が用意されています。 {index}[`Type`] {index}[`Prop`] `Type u` は `Sort (u + 1)` の省略形であるため、 {lean}`Type 0` は {lean}`Sort 1` で {lean}`Type 3` は {lean}`Sort 4` です。 {lean}`Type 0` は {lean}`Type` と省略することもできるため、 `Unit : Type` および `Type : Type 1` です。 {lean}`Prop` は {lean}`Sort 0` の省略形です。

:::comment
## Predicativity
:::

## 可述性（Predicativity）

:::comment
Each universe contains dependent function types, which additionally represent universal quantification and implication.
A function type's universe is determined by the universes of its argument and return types.
The specific rules depend on whether the return type of the function is a proposition.

:::

各宇宙は依存関数型を含んでおり、それはさらに全称量化子と含意を表します。関数型の宇宙は、引数の型と戻り値の型の宇宙によって決定されます。具体的な規則は、関数の戻り値が命題かどうかに依存します。

:::comment
Predicates, which are functions that return propositions (that is, where the result of the function is some type in `Prop`) may have argument types in any universe whatsoever, but the function type itself remains in `Prop`.
In other words, propositions feature {deftech}[_impredicative_] {index}[impredicative]{index subterm := "impredicative"}[quantification] quantification, because propositions can themselves be statements about all propositions (and all other types).

:::

命題を返す関数である述語（つまり、関数の結果が `Prop` にある型である場合）は引数の型がどのような宇宙に会っても構いませんが、関数の型自体は `Prop` に留まります。言い換えると、命題は {deftech}[_非可述_] {index}[impredicative]{index subterm := "impredicative"}[quantification] な量化子を特徴づけます。というのも、命題はそれ自体、すべての命題（および他のすべての命題）についての文になりうるからです。

:::comment
::Manual.example "Impredicativity"
:::
::::Manual.example "非可述性"
:::comment
Proof irrelevance can be written as a proposition that quantifies over all propositions:
:::

証明の irrelevance はすべての命題を量化する命題として書くことができます：

```lean
example : Prop := ∀ (P : Prop) (p1 p2 : P), p1 = p2
```

:::comment
A proposition may also quantify over all types, at any given level:
:::

命題はまた任意のレベルにおいてすべての型を量化することもできます：

```lean
example : Prop := ∀ (α : Type), ∀ (x : α), x = x
example : Prop := ∀ (α : Type 5), ∀ (x : α), x = x
```
::::

:::comment
For universes at {tech key:="universe level"}[level] `1` and higher (that is, the `Type u` hierarchy), quantification is {deftech}[_predicative_]. {index}[predicative]{index subterm := "predicative"}[quantification]
For these universes, the universe of a function type is the least upper bound of the argument and return types' universes.

:::

{tech key:="universe level"}[レベル] `1` 以上の宇宙（つまり、`Type u` の階層）では、量化子は {deftech}[_可述_] です。 {index}[predicative]{index subterm := "predicative"}[quantification] これらの宇宙では、関数型の宇宙は引数の型と戻り値の型の宇宙の最小上界となります。

:::comment
::Manual.example "Universe levels of function types"
:::
::::Manual.example "関数型の宇宙レベル"
:::comment
Both of these types are in {lean}`Type 2`:
:::

これらの型はどちらも {lean}`Type 2` に存在します：

```lean
example (α : Type 1) (β : Type 2) : Type 2 := α → β
example (α : Type 2) (β : Type 1) : Type 2 := α → β
```
::::

:::comment
::Manual.example "Predicativity of {lean}`Type`"
:::
::::Manual.example "{lean}`Type` の Predicativity"
:::comment
This example is not accepted, because `α`'s level is greater than `1`. In other words, the annotated universe is smaller than the function type's universe:
:::

`α` のレベルは `1` より大きいため、この例は許可されません。言い換えると、注釈された宇宙は実際の関数型の宇宙よりも小さいです：

```lean error := true name:=toosmall
example (α : Type 2) (β : Type 1) : Type 1 := α → β
```
```leanOutput toosmall
type mismatch
  α → β
has type
  Type 2 : Type 3
but is expected to have type
  Type 1 : Type 2
```
::::

:::comment
Lean's universes are not {deftech}[cumulative];{index}[cumulativity] a type in `Type u` is not automatically also in `Type (u + 1)`.
Each type inhabits precisely one universe.

:::

Lean の宇宙は {deftech}[cumulative] ではありません； {index}[cumulativity] これは `Type u` の型が自動的に `Type (u + 1)` にも存在するようにならないことを意味します。

:::comment
::Manual.example "No cumulativity"
:::
::::Manual.example "cumulativity ではない"
:::comment
This example is not accepted because the annotated universe is larger than the function type's universe:
:::

この例は注釈された宇宙が関数型の宇宙よりも大きいため、許可されません：

```lean error := true name:=toobig
example (α : Type 2) (β : Type 1) : Type 3 := α → β
```
```leanOutput toobig
type mismatch
  α → β
has type
  Type 2 : Type 3
but is expected to have type
  Type 3 : Type 4
```
::::

:::comment

## Polymorphism

:::

## 多相性（Polymorphism）

:::comment
Lean supports {deftech}_universe polymorphism_, {index subterm:="universe"}[polymorphism] {index}[universe polymorphism] which means that constants defined in the Lean environment can take {deftech}[universe parameters].
These parameters can then be instantiated with universe levels when the constant is used.
Universe parameters are written in curly braces following a dot after a constant name.

:::

Lean は {deftech}_宇宙多相_ {index subterm:="universe"}[polymorphism] {index}[universe polymorphism] （universe polymorphism）をサポートしており、Lean 環境で定義された定数は {deftech}[宇宙パラメータ] を取ることができます。これらのパラメータは定数が使用されるときに宇宙レベルでインスタンス化されます。宇宙パラメータは定数名の後のドットに続く波括弧で記述します。

:::comment
::Manual.example "Universe-polymorphic identity function"
:::
::::Manual.example "宇宙多相恒等関数"
:::comment
When fully explicit, the identity function takes a universe parameter `u`. Its signature is:
:::

完全に明示的な場合、恒等関数は宇宙パラメータ `u` を取ります。このシグネチャは以下になります：

```signature
id.{u} {α : Sort u} (x : α) : α
```
::::

:::comment
Universe variables may additionally occur in {ref "level-expressions"}[universe level expressions], which provide specific universe levels in definitions.
When the polymorphic definition is instantiated with concrete levels, these universe level expressions are also evaluated to yield concrete levels.

:::

宇宙変数はさらに、定義の中で特定の宇宙レベルを提供する {ref "level-expressions"}[宇宙レベル式] の中で現れるかもしれません。多相定義が具体的なレベルでインスタンス化されるとき、これらの宇宙レベル式も具体的なレベルをもたらすために評価されます。

:::::keepEnv
:::comment
::Manual.example "Universe level expressions"
:::
::::Manual.example "宇宙レベル式"

:::comment
In this example, {lean}`Codec` is in a universe that is one greater than the universe of the type it contains:
:::

この例では、 {lean}`Codec` はそれが含む型の宇宙より1つ大きい宇宙に存在します：

```lean
structure Codec.{u} : Type (u + 1) where
  type : Type u
  encode : Array UInt32 → type → Array UInt32
  decode : Array UInt32 → Nat → Option (type × Nat)
```

:::comment
Lean automatically infers most level parameters.
In the following example, it is not necessary to annotate the type as {lean}`Codec.{0}`, because {lean}`Char`'s type is {lean}`Type 0`, so `u` must be `0`:
:::

Lean はほとんどのレベルパラメータを自動的に推論します。以下の例では、 {lean}`Char` の型は {lean}`Type 0` であるため、`u` は `0` でなければならないことから、 {lean}`Codec.{0}` と注釈する必要はありません。

```lean (keep := true)
def Codec.char : Codec where
  type := Char
  encode buf ch := buf.push ch.val
  decode buf i := do
    let v ← buf[i]?
    if h : v.isValidChar then
      let ch : Char := ⟨v, h⟩
      return (ch, i + 1)
    else
      failure
```
::::
:::::

:::comment
Universe-polymorphic definitions in fact create a _schematic definition_ that can be instantiated at a variety of levels, and different instantiations of universes create incompatible values.

:::

宇宙多相な定義は、実際には様々なレベルでインスタンス可能な _スキーマ的定義_ （schematic definition）を作り出し、宇宙レベルの異なるインスタンス化は互換性のない値を作ります。

:::comment
::Manual.example "Universe polymorphism and definitional equality"
:::
:::::keepEnv
::::Manual.example "宇宙多相と定義上の等価性"

:::comment
This can be seen in the following example, in which {lean}`T` is a gratuitously-universe-polymorphic function that always returns {lean}`true`.
Because it is marked {keywordOf Lean.Parser.Command.declaration}`opaque`, Lean can't check equality by unfolding the definitions.
Both instantiations of {lean}`T` have the parameters and the same type, but their differing universe instantiations make them incompatible.
:::

これは次の例で見ることができます。 {lean}`T` は不要な宇宙多相定義で、常に {lean}`true` を返します。 {keywordOf Lean.Parser.Command.declaration}`opaque` とマークされているため、Lean は {lean}`T` の定義を展開して等価性をチェックすることができません。 {lean}`T` のインスタンスはどれもパラメータと同じ型を持ちますが、宇宙のインスタンス化が異なるため互換性がありません：

```lean (error := true) (name := uniIncomp)
opaque T.{u} (_ : Nat) : Bool := (fun (α : Sort u) => true) PUnit.{u}

set_option pp.universes true

def test.{u, v} : T.{u} 0 = T.{v} 0 := rfl
```
```leanOutput uniIncomp
type mismatch
  rfl.{?u.27}
has type
  Eq.{?u.27} ?m.29 ?m.29 : Prop
but is expected to have type
  Eq.{1} (T.{u} 0) (T.{v} 0) : Prop
```
::::
:::::

:::comment
Auto-bound implicit arguments are as universe-polymorphic as possible.
Defining the identity function as follows:
:::

自動的に束縛される暗黙の引数は可能な限り宇宙多相となります。恒等関数を次のように定義します：

```lean
def id' (x : α) := x
```
:::comment
results in the signature:
:::

これは以下のシグネチャになります：

```signature
id'.{u} {α : Sort u} (x : α) : α
```

:::comment
::Manual.example "Universe monomorphism in auto-bound implicit parameters"
:::
::::Manual.example "自動的に束縛された暗黙のパラメータを持つ宇宙のモノ射"
:::comment
On the other hand, because {name}`Nat` is in universe {lean}`Type 0`, this function automatically ends up with a concrete universe level for `α`, because `m` is applied to both {name}`Nat` and `α`, so both must have the same type and thus be in the same universe:
:::

一方、 {name}`Nat` は {lean}`Type 0` に存在するため、この関数は自動的に `α` の具体的な宇宙レベルを求めます。`m` は {name}`Nat` と `α` の両方に適用されるため、どちらも同じ型を持たなければならず、結果として同じ宇宙となります：

```lean
partial def count [Monad m] (p : α → Bool) (act : m α) : m Nat := do
  if p (← act) then
    return 1 + (← count p act)
  else
    return 0
```

```lean (show := false)
/-- info: Nat : Type -/
#guard_msgs in
#check Nat

/--
info: count.{u_1} {m : Type → Type u_1} {α : Type} [Monad m] (p : α → Bool) (act : m α) : m Nat
-/
#guard_msgs in
#check count
```
::::

:::comment
### Level Expressions
:::
### レベル式（Level Expressions）
%%%
tag := "level-expressions"
%%%

:::comment
Levels that occur in a definition are not restricted to just variables and addition of constants.
More complex relationships between universes can be defined using level expressions.

:::

定義に現れるレベルは変数と定数の和だけに限定されません。より複雑な宇宙間の関係もレベルの表現を使って定義できます。

:::comment
````
Level ::= 0 | 1 | 2 | ...  -- Concrete levels
        | u, v             -- Variables
        | Level + n        -- Addition of constants
        | max Level Level  -- Least upper bound
        | imax Level Level -- Impredicative LUB
````
:::
````
Level ::= 0 | 1 | 2 | ...  -- 具体的なレベル
        | u, v             -- 変数
        | Level + n        -- 定数の和
        | max Level Level  -- 最小上界
        | imax Level Level -- 非可述な最小上界
````

:::comment
Given an assignment of level variables to concrete numbers, evaluating these expressions follows the usual rules of arithmetic.
The `imax` operation is defined as follows:

:::

レベル変数が具体的な数値に割り当てられている場合、これらの式の評価は通常の算術の規則に従います。`imax` 演算は以下のように定義されます：

$$``\mathtt{imax}\ u\ v = \begin{cases}0 & \mathrm{when\ }v = 0\\\mathtt{max}\ u\ v&\mathrm{otherwise}\end{cases}``

:::comment
`imax` is used to implement {tech}[impredicative] quantification for {lean}`Prop`.
In particular, if `A : Sort u` and `B : Sort v`, then `(x : A) → B : Sort (imax u v)`.
If `B : Prop`, then the function type is itself a {lean}`Prop`; otherwise, the function type's level is the maximum of `u` and `v`.

:::

`imax` は {lean}`Prop` の {tech}[非可述] な量化子を実装するために使用されます。特に、`A : Sort u` かつ `B : Sort v` である場合、`(x : A) → B : Sort (imax u v)` となります。もし `B : Prop` ならば、その関数型は {lean}`Prop` であり、それ以外ではその関数型のレベルは `u` と `v` の最大値になります。

:::comment
### Universe Variable Bindings

:::

### 宇宙変数の束縛（Universe Variable Bindings）

:::comment
Universe-polymorphic definitions bind universe variables.
These bindings may be either explicit or implicit.
Explicit universe variable binding and instantiation occurs as a suffix to the definition's name.
Universe parameters are defined or provided by suffixing the name of a constant with a period (`.`) followed by a comma-separated sequence of universe variables between curly braces.

:::

宇宙多相定義は宇宙変数を束縛します。これらの束縛は明示的・暗黙的のどちらも可能です。明示的な宇宙変数の束縛とインスタンス化は定義の名前の接尾辞として行われます。宇宙パラメータは定数名にピリオド（`.`）を接尾辞として付け、その後に波括弧の間にカンマで区切られた一連の宇宙変数を付けることで定義・提供されます。

:::::keepEnv
:::comment
::Manual.example "Universe-polymorphic `map`"
:::
::::Manual.example "宇宙多相な `map`"
:::comment
The following declaration of {lean}`map` declares two universe parameters (`u` and `v`) and instantiates the polymorphic {name}`List` with each in turn:
:::

以下{lean}`map` の宣言では、2つの宇宙パラメータ（`u` と `v`）を宣言し、多相型の {name}`List` を順番にインスタンス化しています：

```lean
def map.{u, v} {α : Type u} {β : Type v}
    (f : α → β) :
    List.{u} α → List.{v} β
  | [] => []
  | x :: xs => f x :: map f xs
```
::::
:::::

:::comment
Just as Lean automatically instantiates implicit parameters, it also automatically instantiates universe parameters.
When the {TODO}[describe this option and add xref] `autoImplicit` option is set to {lean}`true` (the default), it is not necessary to explicitly bind universe variables.
When it is set to {lean}`false`, then they must be added explicitly or declared using the `universe` command. {TODO}[xref]

:::

Lean が暗黙のパラメータを自動的にインスタンス化するように、宇宙パラメータも自動的にインスタンス化されます。`autoImplicit` オプションが {lean}`true` に設定されている場合（これがデフォルトです）、宇宙変数を明示的に束縛する必要はありません。 {lean}`false` に設定すると、明示的に追加するか `universe` コマンドを使って宣言する必要があります。

:::comment
::Manual.example "Auto-implicits and universe polymorphism"
:::
::::Manual.example "自動的な暗黙さと宇宙多相"
:::comment
When `autoImplicit` is {lean}`true` (which is the default setting), this definition is accepted even though it does not bind its universe parameters:
:::

`autoImplicit` が {lean}`true` （デフォルト値）の場合、この定義は宇宙パラメータを束縛していなくても許可されます：

```lean (keep := false)
set_option autoImplicit true
def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

:::comment
When `autoImplicit` is {lean}`false`, the definition is rejected because `u` and `v` are not in scope:
:::

`autoImplicit` が {lean}`false` の場合、`u` と `v` がスコープにないためこの定義は却下されます：

```lean (error := true) (name := uv)
set_option autoImplicit false
def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs
```
```leanOutput uv
unknown universe level 'u'
```
```leanOutput uv
unknown universe level 'v'
```
::::

:::comment
In addition to using `autoImplicit`, particular identifiers can be declared as universe variables in a particular {tech}[section scope] using the `universe` command.

:::

`autoImplicit` を使うことに加えて、`universe` コマンドを使って特定の識別子を特定の {tech}[section scope] 内の宇宙変数として宣言することができます。

::::syntax Lean.Parser.Command.universe
```grammar
universe $x:ident $xs:ident*
```

:::comment
Declares one or more universe variables for the extent of the current scope.

:::

現在のスコープの範囲において1つ以上の宇宙変数を宣言します。

:::comment
Just as the `variable` command causes a particular identifier to be treated as a parameter with a particular type, the `universe` command causes the subsequent identifiers to be implicitly quantified as as universe parameters in declarations that mention them, even if the option `autoImplicit` is {lean}`false`.
:::

`variable` コマンドが特定の識別子を特定の型のパラメータとして扱うように、`universe` コマンドは `autoImplicit` オプションが {lean}`false` であっても、それに続く識別子を宇宙パラメータとして暗黙的に量化します。

::::

:::comment
::Manual.example "The `universe` command when `autoImplicit` is `false`"
:::
:::Manual.example "`autoImplicit` が `false` の際の `universe` コマンド"
```lean (keep := false)
set_option autoImplicit false
universe u
def id₃ (α : Type u) (a : α) := a
```
:::

:::comment
Because the automatic implicit parameter feature only insert parameters that are used in the declaration's {tech}[header], universe variables that occur only on the right-hand side of a definition are not inserted as arguments unless they have been declared with `universe` even when `autoImplicit` is `true`.

:::

自動的な暗黙のパラメータ機能は宣言の {tech}[ヘッダ] で使用されるパラメータのみを挿入するため、定義の右側にのみ現れる宇宙変数は `autoImplicit` が `true` の場合でも `universe` で宣言されていない限り引数として挿入されません。

:::comment
::Manual.example "Automatic universe parameters and the `universe` command"
:::
::::Manual.example "自動的な宇宙パラメータと `universe` コマンド"

:::comment
This definition with an explicit universe parameter is accepted:
:::

明示的な宇宙パラメータを伴ったこの定義は許可されます：

```lean (keep := false)
def L.{u} := List (Type u)
```
:::comment
Even with automatic implicit parameters, this definition is rejected, because `u` is not mentioned in the header, which precedes the `:=`:
:::

`u` が `:=` の前にあるヘッダで言及されていないため、自動的な暗黙のパラメータでもこの定義は却下されます：

```lean (error := true) (name := unknownUni) (keep := false)
set_option autoImplicit true
def L := List (Type u)
```
```leanOutput unknownUni
unknown universe level 'u'
```
:::comment
With a universe declaration, `u` is accepted as a parameter even on the right-hand side:
:::

宇宙宣言では、`u` は右辺でもパラメータとして許可されます：

```lean (keep := false)
universe u
def L := List (Type u)
```
:::comment
The resulting definition of `L` is universe-polymorphic, with `u` inserted as a universe parameter.

:::

その結果、`L` の定義は宇宙パラメータとして `u` が挿入された宇宙多相となります。

:::comment
Declarations in the scope of a `universe` command are not made polymorphic if the universe variables do not occur in them or in other automatically-inserted arguments.
:::

`universe` コマンドのスコープにある宣言は、その中に宇宙変数が無い場合、または自動的に挿入される他の引数の中に宇宙変数が無い場合、多相にはなりません。

```lean
universe u
def L := List (Type 0)
#check L
```
::::

### Universe Unification

:::planned 99
 * Rules for unification, properties of algorithm
 * Lack of injectivity
 * Universe inference for unannotated inductive types
:::

### Universe Lifting

:::planned 174
 * When to use universe lifting?
:::

{docstring PLift}

{docstring ULift}

{include 0 Language.InductiveTypes}


# Quotients
%%%
tag := "quotients"
%%%

:::planned 51
 * Define {deftech}[quotient] type
 * Show the computation rule
:::
