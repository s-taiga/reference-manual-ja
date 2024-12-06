/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers


open Manual
open Verso.Genre
open Verso.Genre.Manual



/-
#doc (Manual) "Instance Synthesis" =>
-/
#doc (Manual) "インスタンス統合（Instance Synthesis）" =>
%%%
tag := "instance-synth"
%%%


:::comment
Instance synthesis is a recursive search procedure that either finds an instance for a given type class or fails.
In other words, given a type that is registered as a type class, instance synthesis attempts constructs a term with said type.
It respects {tech}[reducibility]: {tech}[semi-reducible] or {tech}[irreducible] definitions are not unfolded, so instances for a definition are not automatically treated as instances for its unfolding unless it is {tech}[reducible].
There may be multiple possible instances for a given class; in this case, declared priorities and order of declaration are used as tiebreakers, in that order, with more recent instances taking precedence over earlier ones with the same priority.

:::

インスタンス統合は与えられた型クラスのインスタンスを見つけるか失敗するかのどちらかの結果となる再帰的な検索手順です。言い換えると、型クラスとして登録されている型が与えられたとき、インスタンス統合はその型を持つ項の構築を試みます。これは {tech}[reducibility] を尊重します： {tech}[semi-reducible] や {tech}[irreducible] の定義は展開されないため、 {tech}[reducible] でない限り、定義に対するインスタンスは自動的にその定義の展開に対するインスタンスとして扱われることはありません。与えられたクラスに対して、インスタンスは複数ある可能性があります；この場合、宣言された優先度と宣言の順番がタイブレーカとして使用されます。順番として、同じ優先度のインスタンス同士ではより新しいインスタンスがそれより古いものより優先されます。

:::comment
This search procedure is efficient in the presence of diamonds and does not loop indefinitely when there are cycles.
{deftech}_Diamonds_ occur when there is more than one route to a given goal, and {deftech}_cycles_ are situations when two instances each could be solved if the other were solved.
Diamonds occur regularly in practice when encoding mathematical concepts using type classes, and Lean's coercion feature {TODO}[link] naturally leads to cycles, e.g. between finite sets and finite multisets.

:::

この検索手続きはダイアモンドがあっても効率的であり、巡回があっても無限にループすることはありません。 {deftech}_ダイアモンド_ （diamond）は与えられたゴールへのルートが1つ以上ある場合に発生し、 {deftech}_巡回_ （cycle）は2つのインスタンスがそれぞれもう1つを解決すれば解決できる状況です。ダイアモンドは実際に、型クラスを使用して数学的概念をエンコードする際に定期的に発生します。また Lean の強制機能は有限集合と有限多集合の間などで巡回を自然に導きます。

:::comment
Instance synthesis can be tested using the {keywordOf Lean.Parser.Command.synth}`#synth` command.
:::

インスタンス統合は {keywordOf Lean.Parser.Command.synth}`#synth` コマンドを使ってテストすることができます。

::::syntax command
:::comment
The {keywordOf Lean.Parser.Command.synth}`#synth` command attempts to synthesize an instance for the provided class.
If it succeeds, then the resulting term is output.
:::

{keywordOf Lean.Parser.Command.synth}`#synth` コマンドは指定されたクラスのインスタンスの統合を試みます。成功した場合、結果の項が出力されます。

```grammar
#synth $t
```
::::

:::comment
Additionally, {name}`inferInstance` and {name}`inferInstanceAs` can be used to synthesize an instance in a position where the instance itself is needed.

:::

さらに、 {name}`inferInstance` と {name}`inferInstanceAs` を使うことで、インスタンス自体が必要である位置においてインスタンスを統合することができます。

{docstring inferInstance}

{docstring inferInstanceAs}

:::comment
# Instance Search Summary
:::

# インスタンス検索の概要（Instance Search Summary）

:::comment
Generally speaking, instance synthesis is a recursive search procedure that may, in general, backtrack arbitrarily.
Synthesis may _succeed_ with an instance term, _fail_ if no such term can be found, or get _stuck_ if there is insufficient information.
A detailed description of the instance synthesis algorithm is available in {citet tabledRes}[].
An instance search problem is given by a type class applied to concrete arguments; these argument values may or may not be known.
Instance search attempts every locally-bound variable whose type is a class, as well as each registered instance, in order of priority and definition.
When candidate instances themselves have instance-implicit parameters, they impose further synthesis tasks.

:::

一般的に言うと、インスタンス統合は再帰的な検索手順であり、一般的には任意にバックトラックすることができます。統合はインスタンスの項で _成功_ することもあれば、そのような項が見つからなければ _失敗_ することもあり、情報が不十分であれば _行き詰る_ こともあります。インスタンス統合アルゴリズムの詳細な説明は {citet tabledRes}[] にあります。インスタンス検索問題は、具体的な引数に適用される型クラスによって与えられます；これらの引数の値は既知と未知の場合のどちらもあります。インスタンス検索は、登録された各インスタンスと同様に、型がクラスであるすべてのローカル束縛変数を優先度と定義の順に試行します。候補のインスタンス自体がインスタンスの暗黙のパラメータを持つ場合、統合のタスクが追加で課されます。

:::comment
A problem is only attempted when all of the input parameters to the type class are known.
When a problem cannot yet be attempted, then that branch is stuck; progress in other subproblems may result in the problem becoming solvable.
Output or semi-output parameters may be either known or unknown at the start of instance search.
Output parameters are ignored when checking whether an instance matches the problem, while semi-output parameters are considered.

:::

問題は型クラスへの入力パラメータがすべてわかっているときのみに試行されます。ある問題がまだ試行できない場合、その分岐は行き詰っています；他の部分問題の進行によってこの問題が解けるようになる場合があります。出力または半出力パラメータはインスタンス検索の開始時において既知と未知のどちらでもよいです。出力パラメータはインスタンスが問題にマッチするかどうかをチェックする際には無視されますが、半出力パラメータは考慮されます。

:::comment
Every candidate solution for a given problem is saved in a table; this prevents infinite regress in case of cycles as well as exponential search overheads in the presence of diamonds (that is, multiple paths by which the same goal can be achieved).
A branch of the search fails when any of the following occur:
 * All potential instances have been attempted, and the search space is exhausted.
 * The instance size limit specified by the option {option}`synthInstance.maxSize` is reached.
 * The synthesized value of an output parameter does not match the specified value in the search problem.
Failed branches are not retried.

:::

与えられた問題の解の各候補はテーブルに保存されます；これにより、巡回が存在する場合の無限後退やダイアモンド（つまり、同じゴールを達成できる複数の経路）が存在する場合の指数関数的な検索のオーバーヘッドを防ぐことができます。探索の分岐は以下のいずれが発生したときに失敗します：
 * すべてのインスタンス候補が試行され、検索空間が空になった場合。
 * オプション {option}`synthInstance.maxSize` で指定されたインスタンスサイズの上限に達した場合。
 * 出力パラメータの統合結果の値が検索問題で指定された値と一致しない場合。
失敗した分岐は再試行されません。

:::comment
If search would otherwise fail or get stuck, the search process attempts to use matching {tech}[default instances] in order of priority.
For default instances, the input parameters do not need to be fully known, and may be instantiated by the instances parameter values.
Default instances may take instance-implicit parameters, which induce further recursive search.

:::

検索が失敗か行き詰った場合、検索プロセスは優先度の高い順に一致する {tech}[デフォルトインスタンス] の使用を試みます。デフォルトインスタンスでは、入力パラメータを完全に知っている必要はなく、インスタンスパラメータの値によってインスタンス化することができます。デフォルトインスタンスはインスタンス暗黙のパラメータを取ることがあり、これによってさらなる再帰的な検索が引き起こされます。

:::comment
Successful branches in which the problem is fully known (that is, in which there are no unsolved metavariables) are pruned, and further potentially-successful instances are not attempted, because no later instance could cause the previously-succeeding branch to fail.

:::

成功した問題が完全に分かっている（つまり未解決のメタ変数がない）成功したブランチは刈り込まれ、それ以上成功する可能性のあるインスタンスは試みられません。なぜなら先に成功した分岐を失敗させる可能性のあるインスタンスはこの後には存在しないからです。

:::comment
# Instance Search Problems
:::

# インスタンス検索問題（Instance Search Problems）

:::comment
Instance search occurs during the elaboration of (potentially nullary) function applications.
Some of the implicit parameters' values are forced by others; for instance, an implicit type parameter may be solved using the type of a later value argument that is explicitly provided.
Implicit parameters may also be solved using information from the expected type at that point in the program.
The search for instance implicit arguments may make use of the implicit argument values that have been found, and may additionally solve others.

:::

インスタンス検索は、（潜在的に引数が0個の可能性もあります）関数適用の作成中に発生します。暗黙のパラメータの値のうちいくつかはそれ以外から強制されます；例えば、暗黙の型パラメータは、それより後に明示的に提供された値引数の型を使用して解決されるかもしれません。暗黙のパラメータはプログラム中のその時点で期待される型の情報を使って解決することもできます。インスタンス暗黙の引数の検索は見つかった暗黙の引数の値を使用し、さらに他の値を解決することができます。

:::comment
Instance synthesis begins with the type of the instance-implicit parameter.
This type must be the application of a type class to zero or more arguments; these argument values may be known or unknown when search begins.
If an argument to a class is unknown, the search process will not instantiate it unless the corresponding parameter is {ref "class-output-parameters"}[marked as an output parameter], explicitly making it an output of the instance synthesis routine.

:::

インスタンス統合はインスタンス暗黙のパラメータの型から始めます。この型は0個以上の引数に対する型クラスの適用でなければなりません；検索開始時にはこれらの引数の値は既知と未知の場合のどちらもあります。クラスの引数が未知の場合、対応するパラメータが {ref "class-output-parameters"}[出力パラメータとしてマーク] され、明示的にインスタンス統合のルーチンの出力にならない限り、検索プロセスはそれをインスタンス化しません。

:::comment
Search may succeed, fail, or get stuck; a stuck search may occur when an unknown argument value becoming known might enable progress to be made.
Stuck searches may be re-invoked when the elaborator has discovered one of the previously-unknown implicit arguments.
If this does not occur, stuck searches become failures.


:::
検索は成功することもあれば、失敗することも行き詰ることもあります；行き詰った検索は未知の引数の値がわかることで前進できるかもしれないような場合に発生する可能性があります。行き詰った検索はエラボレータがそこまでに未知だった暗黙の引数の1つを発見した場合に再度呼び出される場合があります。これが発生しない場合、行き詰った検索は失敗します。


:::comment
# Candidate Instances
:::

# 候補のインスタンス（Candidate Instances）

:::comment
Instance synthesis uses both local and global instances in its search.
{deftech}_Local instances_ are those available in the local context; they may be either parameters to a function or locally defined with `let`. {TODO}[xref to docs for `let`]
Local instances do not need to be indicated specially; any local variable whose type is a type class is a candidate for instance synthesis.
{deftech}_Global instances_ are those available in the global environment; every global instance is a defined name with the {attr}`instance` attribute applied.{margin}[{keywordOf Lean.Parser.Command.declaration}`instance` declarations automatically apply the {attr}`instance` attribute.]

:::

インスタンス統合では、ローカルインスタンスとグローバルインスタンスの両方を検索に使用します。 {deftech}_ローカルインスタンス_ （local instance）とは、ローカルコンテキストで利用可能なインスタンスのことです；これらは関数のパラメータであったり、`let` でローカルに定義されたりします。ローカルインスタンスは特別に示す必要はありません；型が型クラスである任意のローカル変数はインスタンス統合の候補となります。 {deftech}_グローバルインスタンス_ （global instance）はグローバル環境で利用可能なインスタンスです；すべてのグローバルインスタンスは {attr}`instance` 属性が適用された定義名です。 {margin}[{keywordOf Lean.Parser.Command.declaration}`instance` 宣言は自動的に {attr}`instance` 属性を適用します。]

:::::keepEnv
:::comment
::example "Local Instances"
:::
::::example "ローカルインスタンス"
:::comment
In this example, {lean}`addPairs` contains a locally-defined instance of {lean}`Add NatPair`:
:::

この例では、 {lean}`addPairs` はローカルに定義された {lean}`Add NatPair` インスタンスを含みます：

```lean
structure NatPair where
  x : Nat
  y : Nat

def addPairs (p1 p2 : NatPair) : NatPair :=
  let _ : Add NatPair :=
    ⟨fun ⟨x1, y1⟩ ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩⟩
  p1 + p2
```
:::comment
The local instance is used for the addition, having been found by instance synthesis.
:::

このローカルインスタンスはインスタンス統合によって発見され、加法に用いられます。

::::
:::::

:::::keepEnv
:::comment
::example "Local Instances Have Priority"
:::
::::example "優先度を持つローカルインスタンス"
:::comment
Here, {lean}`addPairs` contains a locally-defined instance of {lean}`Add NatPair`, even though there is a global instance:
:::

ここで、 {lean}`addPairs` はグローバルインスタンスがあるにもかかわらず、ローカルで定義された {lean}`Add NatPair` インスタンスを含みます：

```lean
structure NatPair where
  x : Nat
  y : Nat

instance : Add NatPair where
  add
    | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩

def addPairs (p1 p2 : NatPair) : NatPair :=
  let _ : Add NatPair :=
    ⟨fun _ _ => ⟨0, 0⟩⟩
  p1 + p2
```
:::comment
The local instance is selected instead of the global one:
:::

このローカルインスタンスはグローバルのものの代わりに選択されます：

```lean (name:=addPairsOut)
#eval addPairs ⟨1, 2⟩ ⟨5, 2⟩
```
```leanOutput addPairsOut
{ x := 0, y := 0 }
```
::::
:::::

:::comment
# Instance Parameters and Synthesis
:::

# インスタンスパラメータと統合（Instance Parameters and Synthesis）

%%%
tag := "instance-synth-parameters"
%%%

:::comment
The search process for instances is largely governed by class parameters.
Type classes take a certain number of parameters, and instances are tried during the search when their choice of parameters is _compatible_ with those in the class type for which the instance is being synthesized.

:::

インスタンスの検索プロセスはクラスのパラメータに大きく支配されています。型クラスは一定数のパラメータを取り、インスタンスはそのパラメータの選択がインスタンス統合を試みるクラスの型のパラメータと _互換性がある_ 場合において、検索が試行されます。

:::comment
Instances themselves may also take parameters, but the role of instances' parameters in instance synthesis is very different.
Instances' parameters represent either variables that may be instantiated by instance synthesis or further synthesis work to be done before the instance can be used.
In particular, parameters to instances may be explicit, implicit, or instance-implicit.
If they are instance implicit, then they induce further recursive instance searching, while explicit or implicit parameters must be solved by unification.

:::

インスタンス自体もパラメータを取ることがありますが、インスタンス統合におけるインスタンスのパラメータの役割は大きく異なります。インスタンスのパラメータは、インスタンス統合によってインスタンス化される可能性のある変数か、インスタンスを使用する前に行うべきさらなる統合作用のいずれかを表します。特に、インスタンスに対するパラメータは明示的・暗黙的・インスタンス暗黙のいずれかです。インスタンス暗黙であれば、さらに再帰的なインスタンス検索を引き起こしますが、明示的・暗黙的なパラメータは単一化によって解決されなければなりません。

:::::keepEnv
:::comment
::example "Implicit and Explicit Parameters to Instances"
:::
::::example "インスタンスの暗黙的・明示的なパラメータ"
:::comment
While instances typically take parameters either implicitly or instance-implicitly, explicit parameters may be filled out as if they were implicit during instance synthesis.
In this example, {name}`aNonemptySumInstance` is found by synthesis, applied explicitly to {lean}`Nat`, which is needed to make it type-correct.
:::

インスタンスは通常、暗黙的またはインスタンス暗黙のパラメータを取りますが、明示的なパラメータはインスタンス統合時に暗黙的であるかのように埋めることができます。この例では、 {name}`aNonemptySumInstance` が統合によって見つかり、正しい型となるために必要な {lean}`Nat` に明示的に適用されます。

```lean
instance aNonemptySumInstance (α : Type) {β : Type} [inst : Nonempty α] : Nonempty (α ⊕ β) :=
  let ⟨x⟩ := inst
  ⟨.inl x⟩
```

```lean (name := instSearch)
set_option pp.explicit true in
#synth Nonempty (Nat ⊕ Empty)
```
:::comment
In the output, both the explicit argument {lean}`Nat` and the implicit argument {lean}`Empty` were found by unification with the search goal, while the {lean}`Nonempty Nat` instance was found via recursive instance synthesis.
:::

出力では、明示的な引数 {lean}`Nat` と暗黙的な引数 {lean}`Empty` の両方が検索ゴールによる単一化によって見つかり、 {lean}`Nonempty Nat` インスタンスは再帰的なインスタンス統合によって見つかっています。

```leanOutput instSearch
@aNonemptySumInstance Nat Empty (@instNonemptyOfInhabited Nat instInhabitedNat)
```
::::
:::::

:::comment
# Output Parameters
:::

# 出力パラメータ（Output Parameters）

%%%
tag := "class-output-parameters"
%%%

:::comment
By default, the parameters of a type class are considered to be _inputs_ to the search process.
If the parameters are not known, then the search process gets stuck, because choosing an instance would require the parameters to have values that match those in the instance, which cannot be determined on the basis of incomplete information.
In most cases, guessing instances would make instance synthesis unpredictable.

:::

デフォルトでは、型クラスのパラメータは検索プロセスへの _入力_ とみなされます。パラメータが未知の場合、検索プロセスは行き詰ります。なぜならインスタンスを選択するにはパラメータがインスタンスの値と一致する必要がありますが、不完全な情報に基づいて決定することはできないからです。ほとんどの場合、インスタンスを推測することはインスタンスの統合を予測不可能にします。

:::comment
In some cases, however, the choice of one parameter should cause an automatic choice of another.
For example, the overloaded membership predicate type class {name}`Membership` treats the type of elements of a data structure as an output, so that the type of element can be determined by the type of data structure at a use site, instead of requiring that there be sufficient type annotations to determine _both_ types prior to starting instance synthesis.
An element of a {lean}`List Nat` can be concluded to be a {lean}`Nat` simply on the basis of its membership in the list.

:::

しかし、あるパラメータを選択すると自動的に別のパラメータが選択されるような場合もあります。例えば、オーバーロードされたメンバシップ述語の型クラス {name}`Membership` はデータ構造の要素の型を出力として扱うため、インスタンス統合を開始する前に _両方_ の型を決定するのに十分な型注釈があることを要求する代わりに、要素の型は使用する側でデータ構造の型によって決定することができます。 {lean}`List Nat` の要素は単純にリスト内のメンバシップに基づいて {lean}`Nat` であると結論付けることができます。

```signature (show := false)
-- Test the above claim
Membership.{u, v} (α : outParam (Type u)) (γ : Type v) : Type (max u v)
```

:::comment
Type class parameters can be declared as outputs by wrapping their types in the {name}`outParam` {tech}[gadget].
When a class parameter is an {deftech}_output parameter_, instance synthesis will not require that it be known; in fact, any existing value is ignored completely.
The first instance that matches the input parameters is selected, and that instance's assignment of the output parameter becomes its value.
If there was a pre-existing value, then it is compared with the assignment after synthesis is complete, and it is an error if they do not match.

:::

型クラスのパラメータは {name}`outParam` {tech}[ガジェット] でそれらの型をラップすることで出力として宣言することができます。クラスのパラメータが {deftech}_出力パラメータ_ （output parameter）である場合、インスタンス統合はそれが既知であることを要求しません；実際、どんな値を渡しても完全に無視されます。入力パラメータがマッチする最初のインスタンスが選択され、そのインスタンスの出力パラメータの値には利用箇所で使用される値が割り当てられます。そのインスタンスの出力パラメータに値が存在していた場合、統合が完了した後にその値と割り当てられた値が比較され、一致しない場合はエラーとなります。

{docstring outParam}

:::comment
::example "Output Parameters and Stuck Search"
:::
:::::example "出力パラメータと行き詰った検索"
::::keepEnv
:::comment
This serialization framework provides a way to convert values to some underlying storage type:
:::

このシリアライズ化のフレームワークは、値を基礎となるストレージ型に変換する方法を提供します：

```lean
class Serialize (input output : Type) where
  ser : input → output
export Serialize (ser)

instance : Serialize Nat String where
  ser n := toString n

instance [Serialize α γ] [Serialize β γ] [Append γ] :
    Serialize (α × β) γ where
  ser
    | (x, y) => ser x ++ ser y
```

:::comment
In this example, the output type is unknown.
:::

この例では出力パラメータは不明です：

```lean (error := true) (name := noOutputType)
example := ser (2, 3)
```
:::comment
Instance synthesis can't select the {lean}`Serialize Nat String` instance, and thus the {lean}`Append String` instance, because that would require instantiating the output type as {lean}`String`, so the search gets stuck:
:::

インスタンス統合は {lean}`Serialize Nat String` インスタンスを選択することができず、したがって {lean}`Append String` インスタンスも選択することができません。なぜならこれは出力の型が {lean}`String` とインスタンス化されることを要求するからです。そのためこの検索は行き詰ります：

```leanOutput noOutputType
typeclass instance problem is stuck, it is often due to metavariables
  Serialize (Nat × Nat) ?m.16
```
:::comment
One way to fix the problem is to supply an expected type:
:::

この問題を解決する1つの方法は期待される型を与えることです：

```lean
example : String := ser (2, 3)
```
::::
::::keepEnv
:::comment
The other is to make the output type into an output parameter:
:::

もう1つの方法は出力の型を出力パラメータにすることです：

```lean
class Serialize (input : Type) (output : outParam Type) where
  ser : input → output
export Serialize (ser)

instance : Serialize Nat String where
  ser n := toString n

instance [Serialize α γ] [Serialize β γ] [Append γ] :
    Serialize (α × β) γ where
  ser
    | (x, y) => ser x ++ ser y
```
:::comment
Now, instance synthesis is free to select the {lean}`Serialize Nat String` instance, which solves the unknown implicit `output` parameter of {name}`ser`:
:::

これでインスタンス統合は {lean}`Serialize Nat String` インスタンスを自由に選択できるようになり、これによって {name}`ser` の未知の暗黙の `output` パラメータを解決できるようになります：

```lean
example := ser (2, 3)
```
::::
:::::

:::::keepEnv
:::comment
::example "Output Parameters with Pre-Existing Values"
:::
::::example "値がすでに与えられている出力パラメータ"
:::comment
The class {name}`OneSmaller` represents a way to transform non-maximal elements of a type into elements of a type that has one fewer elements.
There are two separate instances that can match an input type {lean}`Option Bool`, with different outputs:
:::

クラス {name}`OneSmaller` は、ある型の最大でない要素を要素が1つ少ない型に変換する方法を表現します。入力型 {lean}`Option Bool` にマッチするインスタンスが2つあり、出力が異なります：

```lean
class OneSmaller (α : Type) (β : outParam Type) where
  biggest : α
  shrink : (x : α) → x ≠ biggest → β

instance : OneSmaller (Option α) α where
  biggest := none
  shrink
    | some x, _ => x

instance : OneSmaller (Option Bool) (Option Unit) where
  biggest := some true
  shrink
    | none, _ => none
    | some false, _ => some ()

instance : OneSmaller Bool Unit where
  biggest := true
  shrink
    | false, _ => ()
```
:::comment
Because instance synthesis selects the most recently defined instance, the following code is an error:
:::

インスタンス統合は最後に定義されたインスタンスを選択するため以下のコードはエラーになります：

```lean (error := true) (name := nosmaller)
#check OneSmaller.shrink (β := Bool) (some false) sorry
```
```leanOutput nosmaller
failed to synthesize
  OneSmaller (Option Bool) Bool
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
:::comment
The {lean}`OneSmaller (Option Bool) (Option Unit)` instance was selected during instance synthesis, without regard to the supplied value of `β`.
:::

与えられた `β` の値を考慮することなく、インスタンス統合によって {lean}`OneSmaller (Option Bool) (Option Unit)` インスタンスが選択されています。

::::
:::::

:::comment
{deftech}_Semi-output parameters_ are like output parameters in that they are not required to be known prior to synthesis commencing; unlike output parameters, their values are taken into account when selecting instances.

:::

{deftech}_半出力パラメータ_ （semi-output parameter）は統合を開始する前に知っている必要がないという点では出力パラメータと同じです；出力パラメータとは異なり、インスタンスを選択する際にその値が考慮されます。

{docstring semiOutParam}

:::comment
Semi-output parameters impose a requirement on instances: each instance of a class with semi-output parameters should determine the values of its semi-output parameters.
:::

半出力パラメータはインスタンスに要件を課します：半出力パラメータを持つ各インスタンスは、その半出力パラメータの値を決定しなければなりません。

:::TODO
What goes wrong if they can't?
:::

:::::keepEnv
:::comment
::example "Semi-Output Parameters with Pre-Existing Values"
:::
::::example "値がすでに与えられている半出力パラメータ"
:::comment
The class {name}`OneSmaller` represents a way to transform non-maximal elements of a type into elements of a type that one fewer elements.
It has two separate instances that can match an input type {lean}`Option Bool`, with different outputs:
:::

クラス {name}`OneSmaller` は、ある型の最大でない要素を要素が1つ少ない型に変換する方法を表現します。これは {lean}`Option Bool` という入力型にマッチする2つの別々のインスタンスを持っており、異なる出力をもちます：

```lean
class OneSmaller (α : Type) (β : semiOutParam Type) where
  biggest : α
  shrink : (x : α) → x ≠ biggest → β

instance : OneSmaller (Option α) α where
  biggest := none
  shrink
    | some x, _ => x

instance : OneSmaller (Option Bool) (Option Unit) where
  biggest := some true
  shrink
    | none, _ => none
    | some false, _ => some ()

instance : OneSmaller Bool Unit where
  biggest := true
  shrink
    | false, _ => ()
```

:::comment
Because instance synthesis takes semi-output parameters into account when selecting instances, the {lean}`OneSmaller (Option Bool) (Option Unit)` instance is passed over due to the supplied value for `β`:
:::

インスタンス統合は、インスタンスを選択する時に半出力パラメータを考慮するため、`β` として提供された値によって {lean}`OneSmaller (Option Bool) (Option Unit)` インスタンスが渡されます：

```lean (name := nosmaller2)
#check OneSmaller.shrink (β := Bool) (some false) sorry
```
```leanOutput nosmaller2
OneSmaller.shrink (some false) ⋯ : Bool
```
::::
:::::

:::comment
# Default Instances
:::

# デフォルトインスタンス（Default Instances）

%%%
tag := "default-instance-synth"
%%%

:::comment
When instance synthesis would otherwise fail, having not selected an instance, the {deftech}_default instances_ specified using the {attr}`default_instance` attribute are attempted in order of priority.
When priorities are equal, more recently-defined default instances are chosen before earlier ones.
The first default instance that causes the search to succeed is chosen.

:::

インスタンスを選ばずにインスタンス統合が失敗した場合、 {attr}`default_instance` 属性を使用して指定された {deftech}_デフォルトインスタンス_ （default instance）が優先度の高い順に試行されます。優先度が等しい場合、より最近定義されたデフォルトインスタンスがそれ以前のものよりも先に選択されます。検索が成功した最初のデフォルトインスタンスが選択されます。

:::comment
Default instances may induce further recursive instance search if the default instances themselves have instance-implicit parameters.
If the recursive search fails, the search process backtracks and the next default instance is tried.

:::

デフォルトインスタンスはデフォルトインスタンス自体がインスタンス暗黙のパラメータを持つ場合、さらに再帰的なインスタンス検索を引き起こす可能性があります。再帰検索が失敗した場合、検索プロセスはバックトラックし、次のデフォルトインスタンスが試行されます。

:::comment
# “Morally Canonical” Instances
:::

# 「道徳的に標準的な」インスタンス（“Morally Canonical” Instances）

:::comment
During instance synthesis, if a goal is fully known (that is, contains no metavariables) and search succeeds, no further instances will be attempted for that same goal.
In other words, when search succeeds for a goal in a way that can't be refuted by a subsequent increase in information, the goal will not be attempted again, even if there are other instances that could potentially have been used.
This optimization can prevent a failure in a later branch of an instance synthesis search from causing spurious backtracking that replaces a fast solution from an earlier branch with a slow exploration of a large state space.

:::

インスタンス統合中、ゴールが完全に既知（つまりメタ変数を含まない）であり、検索が成功した場合、同じゴールに対してそれ以上インスタンス検索が試行されることはありません。言い換えると、あるゴールに対して、その後の情報の増加によって反論できないような方法で検索が成功した場合、たとえ使用できた可能性のある他のインスタンスがあったとしてもそのゴールは再度試行されません。この最適化により、インスタンス統合の検索の後の分岐で失敗した場合に誤ったバックトラックが発生し、それより前の分岐で解が早く得られるはずだったことが、大規模な状態空間の低速な検索に置き換わってしまうことを防ぐことができます。

:::comment
The optimization relies on the assumption that instances are {deftech}_morally canonical_.
Even if there is more than one potential implementation of a given type class's overloaded operations, or more than one way to synthesize an instance due to diamonds, _any discovered instance should be considered as good as any other_.
In other words, there's no need to consider _all_ potential instances so long as one of them has been guaranteed to work.
The optimization may be disabled with the backwards-compatibility option {option}`backward.synthInstance.canonInstances`, which may be removed in a future version of Lean.

:::

この最適化は、インスタンスが {deftech}_道徳的に標準的_ （morally canonical）であるという仮定に依存しています。与えられた型クラスのオーバーロードされた演算の潜在的な実装が1つ以上あったり、ダイアモンドによってインスタンスを統合する方法が1つ以上あったりしても、 _発見されたインスタンスは他のインスタンスと同じように良いものである_ と考えるべきです。言い換えれば、そのうちの1つが動作することが保証されている限り、 _すべての_ 潜在的なインスタンスを考慮する必要はありません。この最適化は後方互換なオプション {option}`backward.synthInstance.canonInstances` で無効にすることができますが、これは今後の Lean で削除される可能性があります。

:::comment
Code that uses instance-implicit parameters should be prepared to consider all instances as equivalent.
In other words, it should be robust in the face of differences in synthesized instances.
When the code relies on instances _in fact_ being equivalent, it should either explicitly manipulate instances (e.g. via local definitions, by saving them in structure fields, or having a structure inherit from the appropriate class) or it should make this dependency explicit in the type, so that different choices of instance lead to incompatible types.

:::

インスタンス暗黙のパラメータを使用するコードは、すべてのインスタンスを同等のものとみなすように準備すべきです。言い換えれば、統合されたインスタンスの違いにあたってもロバストでなければなりません。そのコードが _実際に_ インスタンスが同等である事実に依存する場合、インスタンスを明示的に操作するか（例えば、ローカル定義を介して構造体フィールドに保存するか、構造体を適切なクラスから継承させる）、インスタンスの異なる選択が互換性のない型につながるように型の中でこの依存関係を明示的にする必要があります。

:::comment
# Options
:::

# オプション（Options）

{optionDocs backward.synthInstance.canonInstances}

{optionDocs synthInstance.maxHeartbeats}

{optionDocs synthInstance.maxSize}
