/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Meta

open Verso.Genre Manual

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

set_option maxRecDepth 800

/-
#doc (Manual) "Logical Model" =>
-/
#doc (Manual) "論理 モデル" =>
%%%
tag := "inductive-types-logical-model"
%%%


:::comment
# Recursors
%%%
tag := "recursors"
%%%

:::

# 再帰子

:::comment
Every inductive type is equipped with a {tech}[recursors].
The recursor is completely determined by the signatures of the type constructor and the constructors.
Recursors have function types, but they are primitive and are not definable using `fun`.

:::

全ての帰納型は {tech}[再帰子] を備えています。再帰子は型コンストラクタとコンストラクタのシグネチャによって完全に決定されます。再帰子は関数型を持ちますが、それはプリミティブであり、`fun` を使って定義することはできません。

:::comment
## Recursor Types
%%%
tag := "recursor-types"
%%%


:::

## 再帰子の型

:::comment
The recursor takes the following parameters:
:::

再帰子は以下のパラメータを取ります：

:::comment
: The inductive type's {tech}[parameters]

  Because parameters are consistent, they can be abstracted over the entire recursor

:::

: 帰納型の {tech}[パラメータ]

  パラメータは一貫しているため、これらは再帰性全体を通して抽象化できます

:::comment
: The {deftech}_motive_

  The motive determines the type of an application of the recursor. The motive is a function whose arguments are the type's indices and an instance of the type with these indices instantiated. The specific universe for the type that the motive determines depends on the inductive type's universe and the specific constructors—see the section on {ref "subsingleton-elimination"}[{tech}[subsingleton] elimination] for details.

:::

: {deftech}_動機_ （motive）

  動機は再帰子の適用の型を決定します。動機は型の添字とこれらの添字をインスタンス化した型のインスタンスを引数とする関数です。動機が決定する型の特定の宇宙は帰納型の宇宙とその特定のコンストラクタに依存します。詳細は {ref "subsingleton-elimination"}[{tech}[subsingleton] 除去] の節を参照してください。

:::comment
: A case for each constructor

  For each constructor, the recursor expects a function that satisfies the motive for an arbitrary application of the constructor. Each case abstracts over all of the constructor's parameters. If the constructor's parameter's type is the inductive type itself, then the case additionally takes a parameter whose type is the motive applied to that parameter's value—this will receive the result of recursively processing the recursive parameter.

:::

: 各コンストラクタのケース

  それぞれのコンストラクタに対して、再帰子はコンストラクタの任意の適用の動機を満たす関数を期待します。各ケースはコンストラクタのすべてのパラメータを抽象します。コンストラクタのパラメータの型が帰納型そのものである場合、ケースはさらにそのパラメータの値に適用される動機を型とするパラメータを取ります。これは再帰的なパラメータの再帰的な処理結果を受け取ります。

:::comment
: The target

  Finally, the recursor takes an instance of the type as an argument, along with any index values.

:::

: ターゲット

  最後に、再帰子は型のインスタンスと添字の値を引数に取ります。

:::comment
The result type of the recursor is the motive applied to these indices and the target.

:::

再帰子の結果の型は、これらの添字とターゲットに適用される動機です。

:::comment
::example "The recursor for {lean}`Bool`"
:::
::::example "{lean}`Bool` の再帰子"
:::comment
{lean}`Bool`'s recursor {name}`Bool.rec` has the following parameters:

:::

{lean}`Bool` の再帰子 {name}`Bool.rec` は以下のパラメータを持ちます：

:::comment
 * The motive computes a type in any universe, given a {lean}`Bool`.
 * There are cases for both constructors, in which the motive is satisfied for both {lean}`false` and {lean}`true`.
 * The target is some {lean}`Bool`.

:::

 * 動機は Bool から任意の宇宙における型を計算します。
 * {lean}`false` と {lean}`true` の両方で動機が満たされる両方のコンストラクタのケースが存在します。
 * ターゲットはなんらかの {lean}`Bool` です。

:::comment
The return type is the motive applied to the target.

:::

戻りの型はターゲットに適用される動機です。

```signature
Bool.rec.{u} {motive : Bool → Sort u}
  (false : motive false)
  (true : motive true)
  (t : Bool) : motive t
```
::::

:::comment
::example "The recursor for {lean}`List`"
:::
:::::example "{lean}`List` の再帰子"
:::comment
{lean}`List`'s recursor {name}`List.rec` has the following parameters:

:::

{lean}`List` の再帰子 {name}`List.rec` は以下のパラメータを持ちます：

::::keepEnv
```lean (show := false)
axiom α.{u} : Type u
```

:::comment
 * The parameter {lean}`α` comes first, because the parameter and the cases need to refer to it
 * The motive computes a type in any universe, given a {lean}`List α`. There is no connection between the universe levels `u` and `v`.
 * There are cases for both constructors:
    - The motive is satisfied for {name}`List.nil`
    - The motive should be satisfiable for any application of {name}`List.cons`, given that it is satisfiable for the tail. The extra parameter `motive tail` is because `tail`'s type is a recursive occurrence of {name}`List`.
 * The target is some {lean}`List α`.
:::

 * パラメータとケースで参照されるため、パラメータ {lean}`α` が最初に来ます。
 * 動機は {lean}`List α` から任意の宇宙における型を計算します。宇宙レベル `u` と `v` の間には何の関連もありません。
 * それぞれのコンストラクタのためのケースがあります：
    - この動機は {name}`List.nil` を満たします。
    - この動機は後続のリストが満たされているならば {name}`List.cons` のどの適用でも満たすことができるはずです。追加のパラメータ `motive tail` は `tail` の型が {name}`List` の再帰的な出現であるためです。
 * ターゲットはなんらかの {lean}`List` です。

::::

:::comment
Once again, the return type is the motive applied to the target.

:::

繰り返しになりますが、戻りの型はターゲットに適用される動機です。

```signature
List.rec.{u, v} {α : Type v} {motive : List α → Sort u}
  (nil : motive [])
  (cons : (head : α) → (tail : List α) → motive tail →
    motive (head :: tail))
  (t : List α) : motive t
```
:::::

::::::keepEnv
:::comment
::example "Recursor with parameters and indices"
:::
:::::example "パラメータと添字を持つ再帰子"
:::comment
Given the definition of {name}`EvenOddList`:
:::

定義 {name}`EvenOddList` に対して：

```lean
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
```


:::comment
The recursor {name}`EvenOddList.rec` is very similar to that for `List`.
The difference comes from the presence of the index:
 * The motive now abstracts over any arbitrary choice of index.
 * The case for {name EvenOddList.nil}`nil` applies the motive to {name EvenOddList.nil}`nil`'s index value `true`.
 * The case for {name EvenOddList.cons}`cons` abstracts over the index value used in its recursive occurrence, and instantiates the motive with its negation.
 * The target additionally abstracts over an arbitrary choice of index.

:::

再帰子 {name}`EvenOddList.rec` は `List` のものと非常に似たものになります。違う箇所は添字の存在に由来します：
 * ここでは動機は任意の添字の選択を抽象化します。
 * {name EvenOddList.nil}`nil` のケースでは、 {name EvenOddList.nil}`nil` の添字の値 `true` に動機を適用しています。
 * {name EvenOddList.cons}`cons` のケースでは、再帰的な出現で使用される添字の値を抽象化し、その否定で動機をインスタンス化しています。
 * ターゲットでは追加で任意の添字の選択を抽象化しています。

```signature
EvenOddList.rec.{u, v} {α : Type v}
  {motive : (isEven : Bool) → EvenOddList α isEven → Sort u}
  (nil : motive true EvenOddList.nil)
  (cons : {isEven : Bool} →
    (head : α) →
    (tail : EvenOddList α isEven) → motive isEven tail →
    motive (!isEven) (EvenOddList.cons head tail)) :
  {isEven : Bool} → (t : EvenOddList α isEven) → motive isEven t
```
:::::
::::::

:::comment
When using a predicate (that is, a function that returns a {lean}`Prop`) for the motive, recursors express induction.
The cases for non-recursive constructors are the base cases, and the additional arguments supplied to constructors with recursive arguments are the induction hypotheses.

:::

動機に述語（つまり {lean}`Prop` を返す関数）を使用する場合、再帰子は帰納法を表現します。非再帰コンストラクタのケースは基本ケースであり、再帰引数を持つコンストラクタに供給される追加の引数は帰納法の仮定

:::comment
### Subsingleton Elimination
:::

### Subsingleton 除去

%%%
tag := "subsingleton-elimination"
%%%

:::comment
Proofs in Lean are computationally irrelevant.
In other words, having been provided with *some* proof of a proposition, it should be impossible for a program to check *which* proof it has received.
This is reflected in the types of recursors for inductively defined propositions or predicates.
For these types, if there's more than one potential proof of the theorem then the motive may only return another {lean}`Prop`.
If the type is structured such that there's only at most one proof anyway, then the motive may return a type in any universe.
A proposition that has at most one inhabitant is called a {deftech}_subsingleton_.
Rather than obligating users to _prove_ that there's only one possible proof, a conservative syntactic approximation is used to check whether a proposition is a subsingleton.
Propositions that fulfill both of the following requirements are considered to be subsingletons:
 * There is at most one constructor.
 * Each of the constructor's parameter types is either a {lean}`Prop`, a parameter, or an index.

:::

Lean において証明は計算上 irrelevant です。言い換えると、ある命題の *ある* 証明が提供されたとき、プログラムが *どの* 証明を受け取ったかをチェックすることは不可能でなければなりません。これは帰納的に定義された命題や述語の再帰子の型に反映されています。これらの型では、定理の証明に複数の可能性がある場合、動機は別の {lean}`Prop` を返すだけです。型が高々1つの証明しかないような構造になっている場合、動機はどの宇宙でも型を返すことができます。高々1つしか存在しない命題を {deftech}_subsingleton_ と呼びます。可能な証明が1つしかないことをユーザに _証明_ することを義務付ける代わりに、命題が subsingleton であるかどうかをチェックするための保守的な構文的近似が使われます。
 * コンストラクタを高々1つ持つ
 * 各コンストラクタのパラメータの型は {lean}`Prop` ・パラメータ・添字のいずれかである

:::comment
::example "{lean}`True` is a subsingleton"
:::
::::example "{lean}`True` は subsingleton"
:::comment
{lean}`True` is a subsingleton because it has one constructor, and this constructor has no parameters.
Its recursor has the following signature:
:::

{lean}`True` はコンストラクタを1つ持ち、そのコンストラクタにパラメータが無いため subsingleton です。この再帰子は以下のシグネチャを持ちます：

```signature
True.rec.{u} {motive : True → Sort u}
  (intro : motive True.intro)
  (t : True) : motive t
```
::::

:::comment
::example "{lean}`False` is a subsingleton"
:::
::::example "{lean}`False` は subsingleton"
:::comment
{lean}`False` is a subsingleton because it has no constructors.
Its recursor has the following signature:
:::

{lean}`False` はコンストラクタが無いため subsingleton です。この再帰子は以下のシグネチャを持ちます：

```signature
False.rec.{u} (motive : False → Sort u) (t : False) : motive t
```
:::comment
Note that the motive is an explicit parameter.
This is because it is not mentioned in any further parameters' types, so it could not be solved by unification.
:::

動機は明示的なパラメータであることに注意してください。これは動機がそれ以降のパラメータの型において言及されていないため、単一化では解決できなかったからです。

::::


:::comment
::example "{name}`And` is a subsingleton"
:::
::::example "{name}`And` は subsingleton"
:::comment
{lean}`And` is a subsingleton because it has one constructor, and both of the constructor's parameters' types are propositions.
Its recursor has the following signature:
:::

{lean}`True` はコンストラクタを1つ持ち、コンストラクタのパラメータの型は両方とも命題であるため subsingleton です。この再帰子は以下のシグネチャを持ちます：

```signature
And.rec.{u} {a b : Prop} {motive : a ∧ b → Sort u}
  (intro : (left : a) → (right : b) → motive (And.intro left right))
  (t : a ∧ b) : motive t
```
::::

:::comment
::example "{name}`Or` is not a subsingleton"
:::
::::example "{name}`Or` は subsingleton ではない"
:::comment
{lean}`Or` is not a subsingleton because it has more than one constructor.
Its recursor has the following signature:
:::

{lean}`Or` は複数のコンストラクタを持つため、subsingleton ではありません。この再帰子は以下のシグネチャを持ちます：

```signature
Or.rec {a b : Prop} {motive : a ∨ b → Prop}
  (inl : ∀ (h : a), motive (.inl h))
  (inr : ∀ (h : b), motive (.inr h))
  (t : a ∨ b) : motive t
```
:::comment
The motive's type indicates that {name}`Or.rec` can only be used to produce proofs.
A proof of a disjunction can be used to prove something else, but there's no way for a program to inspect _which_ of the two disjuncts was true and used for the proof.
:::

動機の型は、 {name}`Or.rec` が証明を作成するためにのみ使用できることを示しています。。選言の証明は何かしらを用いることで証明できますが、2つの選言のうち、どちらが真で証明に使われたかをプログラムが推察する方法はありません。

::::

:::comment
::example "{name}`Eq` is a subsingleton"
:::
::::example "{name}`Eq` は subsingleton"
:::comment
{lean}`Eq` is a subsingleton because it has just one constructor, {name}`Eq.refl`.
This constructor instantiates {lean}`Eq`'s index with a parameter value, so all arguments are parameters:
:::

{lean}`Eq` はコンストラクタ {lean}`Eq.refl` を1つだけ持つため、subsingleton です。このコンストラクタは {lean}`Eq` の添字をパラメータの値でインスタンス化するため、すべての引数はパラメータです：

```signature
Eq.refl.{u} {α : Sort u} (x : α) : Eq x x
```

:::comment
Its recursor has the following signature:
:::

この再帰子は以下のシグネチャを持ちます：

```signature
Eq.rec.{u, v} {α : Sort v} {x : α}
  {motive : (y : α) → x = y → Sort u}
  (refl : motive x (.refl x))
  {y : α} (t : x = y) : motive y t
```
:::comment
This means that proofs of equality can be used to rewrite the types of non-propositions.
:::

つまり、等号の証明は命題以外の型を書き換えるために使うことができます。

::::

:::comment
## Reduction
%%%
tag := "iota-reduction"
%%%

:::

## 簡約

:::comment
In addition to adding new constants to the logic, inductive type declarations also add new reduction rules.
These rules govern the interaction between recursors and constructors; specifically recursors that have constructors as their targets.
This form of reduction is called {deftech}_ι-reduction_ (iota reduction){index}[ι-reduction]{index (subterm:="ι (iota)")}[reduction].

:::

論理に新しい定数が追加されるだけでなく、帰納型宣言には新しい簡約規則も追加されます。これらの規則は再帰子とコンストラクタ、特にコンストラクタをターゲットとする再帰子の相互作用を支配します。この簡約の形式は {deftech}_ι簡約_ {index}[ι-reduction]{index (subterm:="ι (iota)")}[reduction] （iota reduction）と呼ばれます。

:::comment
When the recursor's target is a constructor with no recursive parameters, the recursor application reduces to an application of the constructor's case to the constructor's arguments.
If there are recursive parameters, then these arguments to the case are found by applying the recursor to the recursive occurrence.

:::

再帰子のターゲットが再帰パラメータを持たないコンストラクタである場合、再帰子の適用はコンストラクタの引数へのコンストラクタのケースの適用に簡約されます。再帰パラメータがある場合は、再帰の出現に対して再帰を適用することでケースに対するこれらの引数を見つけることができます。

:::comment
# Well-Formedness Requirements
:::

# 適格要件


%%%
tag := "well-formed-inductives"
%%%

:::comment
Inductive type declarations are subject to a number of well-formedness requirements.
These requirements ensure that Lean remains consistent as a logic when it is extended with the inductive type's new rules.
They are conservative: there exist potential inductive types that do not undermine consistency, but that these requirements nonetheless reject.

:::

帰納型の宣言は、多くの適格要件に従います。これらの要件は、Lean が帰納的データ型の新しい規則で拡張された時に、論理としての一貫性が保たれることを保証します。これらの要件は保守的です：一貫性を損なわない帰納型だったとしてもこれらの要件はその帰納型を拒否する可能性があります。

:::comment
## Universe Levels

:::

## 宇宙レベル

:::comment
Type constructors of inductive types must either inhabit a {tech}[universe] or a function type whose return type is a universe.
Each constructor must inhabit a function type that returns a saturated application of the inductive type.
If the inductive type's universe is {lean}`Prop`, then there are no further restrictions on universes, because {lean}`Prop` is {tech}[impredicative].
If the universe is not {lean}`Prop`, then the following must hold for each parameter to the constructor:
 * If the constructor's parameter is a parameter (in the sense of parameters vs indices) of the inductive type, then this parameter's type may be no larger than the type constructor's universe.
 * All other constructor parameters must be smaller than the type constructor's universe.

:::

帰納型の型コンストラクタは {tech}[universe] か戻り値が宇宙である関数型のどちらかに属さなければなりません。各コンストラクタは帰納型の完全な適用を返す関数型に属さなければなりません。もし帰納型の宇宙が {lean}`Prop` であれば、 {lean}`Prop` は {tech}[impredicative] であるため宇宙にはそれ以上の制限はありません。もし宇宙が {lean}`Prop` でない場合、コンストラクタの各パラメータについて以下が成り立つ必要があります：
 * コンストラクタのパラメータが（パラメータか添字かの意味で）帰納型のパラメータである場合、このパラメータの型は型コンストラクタの宇宙より大きくはできません。
 * その他のすべてのコンストラクタのパラメータは型コンストラクタの宇宙より小さくなければなりません。

::::::keepEnv
:::comment
::example "Universes, constructors, and parameters"
:::
:::::example "宇宙・コンストラクタ・パラメータ"
:::comment
{lean}`Either` is in the greater of its arguments' universes, because both are parameters to the inductive type:
:::

{lean}`Either` はその引数の宇宙がどちらも帰納型のパラメータであるため、それらのうち大きい方の宇宙に存在します：

```lean
inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Either α β
  | inr : β → Either α β
```

:::comment
{lean}`CanRepr` is in a larger universe than the constructor parameter `α`, because `α` is not one of the inductive type's parameters:
:::

{lean}`CanRepr` は `α` が帰納型のパラメータのいずれでもないため、コンストラクタのパラメータ `α` よりも大きな宇宙に存在します：

```lean
inductive CanRepr : Type (u + 1) where
  | mk : (α : Type u) → [Repr α] → CanRepr
```

:::comment
Constructorless inductive types may be in universes smaller than their parameters:
:::

コンストラクタの無い帰納型はそのパラメータよりも小さな宇宙に存在することができます：

```lean
inductive Spurious (α : Type 5) : Type 0 where
```
:::comment
It would, however, be impossible to add a constructor to {name}`Spurious` without changing its levels.
:::

しかし、 {name}`Spurious` のレベルを変えずにコンストラクタを追加することは不可能です。

:::::
::::::

## Strict Positivity
%%%
tag := "strict-positivity"
%%%


:::comment
All occurrences of the type being defined in the types of the parameters of the constructors must be in {deftech}_strictly positive_ positions.
A position is strictly positive if it is not in a function's argument type (no matter how many function types are nested around it) and it is not an argument of any expression other than type constructors of inductive types.
This restriction rules out unsound inductive type definitions, at the cost of also ruling out some unproblematic ones.

:::

定義される型がコンストラクタの引数の型に出現する場合は、すべて {deftech}_strictly positive_ な位置になければなりません。ある位置が strictly positive であるとは、それが関数の引数型になく（その周囲にいくつの関数型がネストしていても同様です）、帰納型の型コンストラクタ以外の式の引数でない場合です。この制限により不健全な帰納型の定義は除外されますが、問題のないものも除外されます。

:::comment
::example "Non-strictly-positive inductive types"
:::
::::::example "非 strictly-positive な帰納型"
:::::keepEnv
:::comment
The type `Bad` would make Lean inconsistent if it were not rejected:
:::

`Bad` 型はもし不許可でなければ Lean を矛盾した存在にしてしまいます：

```lean (name := Bad) (error := true)
inductive Bad where
  | bad : (Bad → Bad) → Bad
```
```leanOutput Bad
(kernel) arg #1 of 'Bad.bad' has a non positive occurrence of the datatypes being declared
```

::::keepEnv
```lean (show := false)
axiom Bad : Type
axiom Bad.bad : (Bad → Bad) → Bad
```
:::comment
This is because it would be possible to write a circular argument that proves {lean}`False` under the assumption {lean}`Bad`.
{lean}`Bad.bad` is rejected because the constructor's parameter has type {lean}`Bad → Bad`, which is a function type in which {lean}`Bad` occurs as an argument type.
:::

これは {lean}`Bad` という仮定の下で {lean}`False` を証明する循環論法を書くことが可能だからです。 {lean}`Bad.bad` はコンストラクタの引数の型が {lean}`Bad → Bad` であり、 {lean}`Bad` が引数の型として出現する関数型であるため却下されます。

::::

:::comment
This declaration of a fixed point operator is rejected, because `Fix` occurs as an argument to `f`:
:::

`Fix` は `f` の引数として出現するため、この不動点演算子の宣言は却下されます：

```lean (name := Fix) (error := true)
inductive Fix (f : Type u → Type u) where
  | fix : f (Fix f) → Fix f
```
```leanOutput Fix
(kernel) arg #2 of 'Fix.fix' contains a non valid occurrence of the datatypes being declared
```

:::comment
`Fix.fix` is rejected because `f` is not a type constructor of an inductive type, but `Fix` itself occurs as an argument to it.
In this case, `Fix` is also sufficient to construct a type equivalent to `Bad`:
:::

`Fix.fix` は `f` が帰納型の型コンストラクタではなく、`Fix` 自身がその引数として出現するため却下されます。この場合、`Fix` も `Bad` と同等な型を構成するのに十分です：

```lean (show := false)
axiom Fix : (Type → Type) → Type
```
```lean
def Bad : Type := Fix fun t => t → t
```
:::::
::::::


## Prop vs Type
%%%
tag := "prop-vs-type"
%%%

:::comment
Lean rejects universe-polymorphic types that could not, in practice, be used polymorphically.
This could arise if certain instantiations of the universe parameters would cause the type itself to be a {lean}`Prop`.
If this type is not a {tech}[subsingleton], then is recursor can only target propositions (that is, the {tech}[motive] must return a {lean}`Prop`).
These types only really make sense as {lean}`Prop`s themselves, so the universe polymorphism is probably a mistake.
Because they are largely useless, Lean's inductive type elaborator has not been designed to support these types.

:::

Lean は実用上多相的に使うことができない宇宙多相型を拒否します。これは宇宙パラメータの特定のインスタンス化によって型自体が {lean}`Prop` になる場合に発生する可能性があります。この型が {tech}[subsingleton] でない場合、再帰子は命題のみを対象とすることができます（つまり、 {tech}[動機] は {lean}`Prop` を返さなければなりません）。このような型は {lean}`Prop` そのものとしてしか意味をなさないため、宇宙多相としたことは間違いだと考えられます。これらの型はほとんど役に立たないため、Lean のデータ型エラボレータはこれらの型をサポートするように設計されていません。

:::comment
When such universe-polymorphic inductive types are indeed subsingletons, it can make sense to define them.
Lean's standard library defines {name}`PUnit` and {name}`PEmpty`.
To define a subsingleton that can inhabit {lean}`Prop` or a {lean}`Type`, set the option {option}`bootstrap.inductiveCheckResultingUniverse` to {lean}`false`.

:::

このような宇宙多相な帰納型が本当に subsingleton である場合、それらを定義することは意味があります。Lean の標準ライブラリは {name}`PUnit` と {name}`PEmpty` を定義しています。 {lean}`Prop` または {lean}`Type` に属することのできる subsingleton を定義するには、オプション {option}`bootstrap.inductiveCheckResultingUniverse` を {lean}`false` に設定します。

{optionDocs bootstrap.inductiveCheckResultingUniverse}

:::::keepEnv
:::comment
::example "Overly-universe-polymorphic {lean}`Bool`"
:::
::::example "過剰に宇宙多相な {lean}`Bool`"
:::comment
Defining a version of {lean}`Bool` that can be in any universe is not allowed:
:::

任意の宇宙に存在できるバージョンの {lean}`Bool` の定義は許可されません：

```lean (error := true) (name := PBool)
inductive PBool : Sort u where
  | true
  | false
```


```leanOutput PBool
invalid universe polymorphic resulting type, the resulting universe is not 'Prop', but it may be 'Prop' for some parameter values:
  Sort u
Possible solution: use levels of the form 'max 1 _' or '_ + 1' to ensure the universe is of the form 'Type _'.
```
::::
:::::



:::comment
# Constructions for Termination Checking
:::

# 停止性チェックのための構成

%%%
tag := "recursor-elaboration-helpers"
%%%

:::comment
In addition to the type constructor, constructors, and recursors that Lean's core type theory prescribes for inductive types, Lean constructs a number of useful helpers.
First, the equation compiler (which translates recursive functions with pattern matching in to applications of recursors) makes use of these additional constructs:
 * `recOn` is a version of the recursor in which the target is prior to the cases for each constructor.
 * `casesOn` is a version of the recursor in which the target is prior to the cases for each constructor, and recursive arguments do not yield induction hypotheses. It expresses case analysis rather than primitive recursion.
 * `below` computes a type that, for some motive, expresses that _all_ inhabitants of the inductive type that are subtrees of the target satisfy the motive. It transforms a motive for induction or primitive recursion into a motive for strong recursion or strong induction.
 * `brecOn` is a version of the recursor in which `below` is used to provide access to all subtrees, rather than just immediate recursive parameters. It represents strong induction.
 * `noConfusion` is a general statement from which injectivity and disjointness of constructors can be derived.
 * `noConfusionType` is the motive used for `noConfusion` that determines what the consequences of two constructors being equal would be. For separate constructors, this is {lean}`False`; if both constructors are the same, then the consequence is the equality of their respective parameters.


:::

Lean のコア型理論が帰納型に対して規定している型コンストラクタ・コンストラクタ・再帰子に加えて、Lean は多くの補助構成を構築しています。まず、等式のコンパイラ（パターンマッチによる再帰関数を再帰子の適用に変換する）はこれらの追加のコンストラクタを使用します：
 * `recOn` は各コンストラクタのケースよりもターゲットが優先される再帰子のバージョンです。
 * `casesOn` は再帰子のバージョンであり、ターゲットが各コンストラクタのケースより前にあり、再帰的な引数は帰納法の仮定を生成しません。これはプリミティブな再帰ではなく、ケース分析を表現しています。
 * `below` はある動機に対して、ターゲットの部分木である帰納型の _すべての_ 住人がその動機を満たすことを表現する型を計算します。これは、帰納法やプリミティブな再帰の動機を強再帰や強帰納法の動機に変換します。
 * `brecOn` は `below` を使用して、直前の再帰パラメータだけでなく、すべての部分木へのアクセスを提供する再帰子のバージョンです。これは強帰納法を表現しています。
 * `noConfusion` は一般的な文であり、そこからコンストラクタの単射性と不連結性を導き出すことができます。
 * `noConfusionType` は `noConfusion` に対して用いられ、2つのコンストラクタが等しい場合どうなるかを決定する動機です。別々のコンストラクタの場合、これは {lean}`False` です；両方のコンストラクタが同じであれば、それぞれのパラメータが等しいという結果になります。

:::comment
For {tech}[well-founded] recursion, it is frequently useful to have a generic notion of size available.
This is captured in the {name}`SizeOf` class.

:::

{tech}[整礎再帰] では、サイズの一般的な概念があると便利なことがよくあります。これは {name}`SizeOf` クラスに含まれています。

{docstring SizeOf}
