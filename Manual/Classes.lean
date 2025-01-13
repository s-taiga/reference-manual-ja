/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Language.Functions
import Manual.Language.Files
import Manual.Language.InductiveTypes
import Manual.Classes.InstanceDecls
import Manual.Classes.InstanceSynth
import Manual.Classes.DerivingHandlers
import Manual.Classes.BasicClasses

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Lean.Parser.Command (declModifiers)

set_option pp.rawOnError true

set_option linter.unusedVariables false

def wadlerBlott89 : InProceedings where
  title := .concat (inlines!"How to make ad-hoc polymorphism less ad hoc")
  authors := #[.concat (inlines!"Philip Wadler"), .concat (inlines!"Stephen Blott")]
  year := 1980
  booktitle := .concat (inlines!"Proceedings of the 16th Symposium on Principles of Programming Languages")

set_option maxRecDepth 100000
/-
#doc (Manual) "Type Classes" =>
-/
#doc (Manual) "型クラス（Type Classes）" =>
%%%
tag := "type-classes"
%%%

:::comment
An operation is _polymorphic_ if it can be used with multiple types.
In Lean, polymorphism comes in three varieties:

:::

ある演算が _多相_ （polymorphic）であるとは、それが複数の型で使用できることを指します。Lean では、多相性には3種類あります：

:::comment
 1. {tech}[universe polymorphism], where the sorts in a definition can be instantiated in various ways,
 2. functions that take types as (potentially implicit) parameters, allowing a single body of code to work with any type, and
 3. {deftech}_ad-hoc polymorphism_, implemented with type classes, in which operations to be overloaded may have different implementations for different types.

:::

 1. {tech}[宇宙多相] 、これは定義中のソートを様々な方法でインスタンス化できることを指し、
 2. 型を（暗黙の可能性もある）パラメータとして受け取る関数、これによって1つのコードで任意の型に働きかけることができ、
 3. {deftech}_アドホック多相性_ （ad-hoc polymorphism）、これは型クラスによって実装されるもので、オーバーロードされる演算は型によって異なる演算を持つことができます。

:::comment
Because Lean does not allow case analysis of types, polymorphic functions implement operations that are uniform for any choice of type argument; for example, {name}`List.map` does not suddenly compute differently depending on whether the input list contains {name}`String`s or {name}`Nat`s.
Ad-hoc polymorphic operations are useful when there is no “uniform” way to implement an operation; the canonical use case is for overloading arithmetic operators so that they work with {name}`Nat`, {name}`Int`, {name}`Float`, and any other type that has a sensible notion of addition.
Ad-hoc polymorphism may also involve multiple types; looking up a value at a given index in a collection involves the collection type, the index type, and the type of member elements to be extracted.
A {deftech}_type class_{margin}[Type classes were first described in {citehere wadlerBlott89}[]] describes a collection of overloaded operations (called {deftech}_methods_) together with the involved types.

:::

Lean は型のケース分析を許容していないため、多相関数は任意に選んだ型引数に対して一様な演算を実装します；例えば、 {name}`List.map` は、入力リストに {name}`String` か {name}`Nat` のどちらが含まれていようとも突然異なる計算をすることはありません。アドホック多相な演算は演算を実装するにあたって「一様な」方法がない場合に有益です；典型的な使用例としては、 {name}`Nat` ・ {name}`Int` ・ {name}`Float` やその他加算の概念を持つ任意の型で動作するように算術演算子をオーバーロードすることです。アドホック多相は複数の型を含むこともあります；コレクション内の指定されたインデックスの値を検索するには、コレクション型・インデックス型・抽出されるメンバ要素の型が関係します。 {deftech}_型クラス_{margin}[型クラスが最初に記述されたのは {citehere wadlerBlott89}[] です] （type class）はオーバーロードされる演算（ {deftech}_メソッド_ 、method と呼ばれます）のコレクションを関連する型とともに記述します。

:::comment
Type classes are very flexible.
Overloading may involve multiple types; operations like indexing into a data structure can be overloaded for a specific choice of data structure, index type, element type, and even a predicate that asserts the presence of the key in the structure.
Due to Lean's expressive type system, overloading operations is not restricted only to types; type classes may be parameterized by ordinary values, by families of types, and even by predicates or propositions.
All of these possibilities are used in practice:

:::

型クラスは非常に柔軟です。オーバーロードは複数の型に関係させることが可能です；データ構造へのインデックス付けのような操作は、データ構造・インデックス型・要素型・さらには構造体内のキーの存在を保証する述語の具体的な選択に対してまでもオーバーロードすることができます。Lean の表現力豊かな型システムにより、演算のオーバーロードは型だけに限定されません；型クラスは通常の値・型族・さらには述語や命題によってパラメータ化することができます。これらの可能性はすべて実際に使用されています：

:::comment
: Natural number literals

  The {name}`OfNat` type class is used to interpret natural number literals.
  Instances may depend not only on the type being instantiated, but also on the number literal itself.

:::

: 自然数リテラル

  {name}`OfNat` 型クラスは自然数リテラルを解釈するために使用されます。インスタンスはインスタンス化される型だけでなく、数値リテラル自体にも依存します。

:::comment
: Computational effects

  Type classes such as {name}`Monad`, whose parameter is a function from one type to another, are used to provide {ref "monads-and-do"}[special syntax for programs with side effects.]
  The “type” for which operations are overloaded is actually a type-level function, such as {name}`Option`, {name}`IO`, or {name}`Except`.

:::

: 計算の作用

  {name}`Monad` のような型クラスはパラメータとしてある型から別の型の関数を取り、 {ref "monads-and-do"}[副作用を持つプログラムのための特別な構文] を提供するために使用されます。具体的には、操作がオーバーロードされる「型」は {name}`Option` ・ {name}`IO` ・ {name}`Except` などの型レベルの関数です。

:::comment
: Predicates and propositions

  The {name}`Decidable` type class allows a decision procedure for a proposition to be found automatically by Lean.
  This is used as the basis for {keywordOf termIfThenElse}`if`-expressions, which may branch on any decidable proposition.

:::

: 述語と命題

  {name}`Decidable` 型クラスによって Lean が命題の決定手続きを自動的に見つけることができるようにします。これは決定可能な任意の命題への分岐を可能にする {keywordOf termIfThenElse}`if` 式の基礎として使われています。

:::comment
While ordinary polymorphic definitions simply expect instantiation with arbitrary parameters, the operators overloaded with type classes are to be instantiated with {deftech}_instances_ that define the overloaded operation for some specific set of parameters.
These {deftech}[instance-implicit] parameters are indicated in square brackets.
At invocation sites, Lean either {deftech key:="synthesis"}_synthesizes_ {index}[instance synthesis] {index subterm:="of type class instances"}[synthesis] a suitable instance from the available candidates or signals an error.
Because instances may themselves have instance parameters, this search process may be recursive and result in a final composite instance value that combines code from a variety of instances.
Thus, type class instance synthesis is also a means of constructing programs in a type-directed manner.

:::

通常の多相定義は単に任意のパラメータでインスタンス化されることを想定していますが、型クラスでオーバーロードされる演算子は特定のパラメータセットに対してオーバーロードされる演算を定義する {deftech}_インスタンス_ （instance）としてインスタンス化されます。これらの {deftech}[インスタンス暗黙] （instance-implicit）パラメータは大括弧で示されます。呼び出しの際において、Lean は利用可能な候補から適切なインスタンスを {deftech key:="synthesis"}_統合_ {index}[instance synthesis] {index subterm:="of type class instances"}[synthesis] （synthesize）するかエラーを通知します。インスタンスはそれ自身がインスタンスパラメータを持つことがあるため、この検索プロセスは再帰的であり、様々なインスタンスからのコードを組み合わせた最終的な合成インスタンス値になる可能性があります。このように型クラスのインスタンス統合は型指向の流儀によるプログラムを構築する手段でもあります。

:::comment
Here are some typical use cases for type classes:
 * Type classes may represent overloaded operators, such as arithmetic that can be used with a variety of types of numbers or a membership predicate that can be used for a variety of data structures. There is often a single canonical choice of operator for a given type—after all, there is no sensible alternative definition of addition for {lean}`Nat`—but this is not an essential property, and libraries may provide alternative instances if needed.
 * Type classes can represent an algebraic structure, providing both the extra structure and the axioms required by the structure. For example, a type class that represents an Abelian group may contain methods for a binary operator, a unary inverse operator, an identity element, as well as proofs that the binary operator is associative and commutative, that the identity is an identity, and that the inverse operator yields the identity element on both sides of the operator. Here, there may not be a canonical choice of structure, and a library may provide many ways to instantiate a given set of axioms; there are two equally canonical monoid structures over the integers.
 * A type class can represent a relation between two types that allows them to be used together in some novel way by a library.
   The {lean}`Coe` class represents automatically-inserted coercions from one type to another, and {lean}`MonadLift` represents a way to run operations with one kind of effect in a context that expects another kind.
 * Type classes can represent a framework of type-driven code generation, where instances for polymorphic types each contribute some portion of a final program.
    The {name}`Repr` class defines a canonical pretty printer for a type, and polymorphic types end up with polymorphic {name}`Repr` instances.
    When pretty printing is finally invoked on an expression with a known concrete type, such as {lean}`List (Nat × (String ⊕ Int))`, the resulting pretty printer contains code assembled from the {name}`Repr` instances for {name}`List`, {name}`Prod`, {name}`Nat`, {name}`Sum`, {name}`String`, and {name}`Int`.

:::

ここでいくつか型クラスの一般的な使用例を挙げましょう：
 * 型クラスはオーバーロードされた演算子を表すことができ、それは例えば様々な型の数値に使用できる算術演算や、様々なデータ構造に使用できるメンバシップ述語などです。演算子はそれぞれの型に対して標準的なものが1つだけ存在することがしばしばあります。結局のところ、 {lean}`Nat` の加算に対して感覚的な代替定義は存在しないものの、これは本質的な性質ではないため、必要であればライブラリは別のインスタンスを提供することが可能です。
 * 型クラスは代数的構造を表現することができ、その構造で必要とされる追加の構造と公理の両方を提供します。例えば、アーベル群を表す型クラスには二項演算子・単項逆演算子・単位元のメソッドと、二項演算子が結合的かつ可換であること・この単位元が実際に単位であること・逆演算子を演算子の左右どちらにおいても単位元をもたらすことの証明を含ませることができます。ここで、こうした構造に対する標準的な選択は存在しないかもしれず、ライブラリはある公理のセットに対してインスタンス化する方法を多数提供するかもしれません；例えば整数上には2つの標準的なモノイド構造があります。
 * 型クラスは2つの型の間の関係を表すことができ、ライブラリによって2つの型を一緒に使うことができます。 {lean}`Coe` クラスはある型から別の型へ自動的に挿入される強制子を表し、 {lean}`MonadLift` はある種の作用を持つ操作を別の種類の作用を期待するコンテキストで実行する方法を表します。
 * 型クラスは型駆動コード生成のフレームワークを表すことができ、多相型のインスタンスはそれぞれ最終的なプログラムの一部に貢献します。 {name}`Repr` クラスは型のための標準的なプリティプリンタを定義し、多相型の場合は多相型用の {name}`Repr` インスタンスに行きつきます。最終的にプリティプリンタが {lean}`List (Nat × (String ⊕ Int))` のような既知の具体的な型を持つ式に対して呼び出されると、結果として得られるプリティプリンタには {name}`List` ・ {name}`Prod` ・ {name}`Nat` ・ {name}`Sum` ・ {name}`String` ・ {name}`Int` の {name}`Repr` インスタンスから組み立てられたコードが含まれます。

:::comment
# Class Declarations
:::

# クラス定義（Class Declarations）

%%%
tag := "class"
%%%

:::comment
Type classes are declared with the {keywordOf Lean.Parser.Command.declaration}`class` keyword.

:::

型クラスは {keywordOf Lean.Parser.Command.declaration}`class` キーワードを用いて宣言されます。

::::syntax command
```grammar
$_:declModifiers
class $d:declId $_:bracketedBinder*
    $[extends $_,*]? $[: $_]? where
  $[$_:declModifiers $_ ::]?
  $_
$[deriving $[$x:ident],*]?
```

:::comment
Declares a new type class.
:::

新しい型クラスを宣言します。

::::

:::keepEnv
```lean (show := false)
-- Just make sure that the `deriving` clause is legit
class A (n : Nat) where
  k : Nat
  eq : n = k
deriving DecidableEq
```
:::


:::comment
The {keywordOf Lean.Parser.Command.declaration}`class` declaration creates a new single-constructor inductive type, just as if the {keywordOf Lean.Parser.Command.declaration}`structure` command had been used instead.
In fact, the results of the {keywordOf Lean.Parser.Command.declaration}`class` and {keywordOf Lean.Parser.Command.declaration}`structure` commands are almost identical, and features such as default values may be used the same way in both.
Please refer to {ref "structures"}[the documentation for structures] for more information about default values, inheritance, and other features of structures.
The differences between structure and class declarations are:

:::

{keywordOf Lean.Parser.Command.declaration}`class` 宣言は {keywordOf Lean.Parser.Command.declaration}`structure` コマンドを使用した場合と同様に、新しい単一のコンストラクタの帰納型を作成します。実は、 {keywordOf Lean.Parser.Command.declaration}`class` コマンドと {keywordOf Lean.Parser.Command.declaration}`structure` コマンドの結果はほとんど同じであり、デフォルト値のような機能はどちらも同じように使うことができます。構造体のデフォルト値や継承、その他の機能については {ref "structures"}[構造体についてのドキュメント] を参照してください。構造体選言とクラス宣言の違いは以下の通りです：

:::comment
: Methods instead of fields

  Instead of creating field projections that take a value of the structure type as an explicit parameter, {tech}[methods] are created. Each method takes the corresponding instance as an instance-implicit parameter.

:::

: フィールドの代わりにメソッド

  構造体型の値を明示的なパラメータとして受け取るフィールドの射影を作成する代わりに {tech}[メソッド] が作成されます。各メソッドは対応するインスタンスをインスタンス暗黙のパラメータとして取ります。

:::comment
: Instance-implicit parent classes

  The constructor of a class that extends other classes takes its class parents' instances as instance-implicit parameters, rather than explicit parameters.
  When instances of this class are defined, instance synthesis is used to find the values of inherited fields.
  Parents that are not classes are still explicit parameters to the underlying constructor.

:::

: インスタンス暗黙としての親クラス

  他のクラスを継承するクラスのコンストラクタは、明示的なパラメータではなくそのクラスの親のインスタンスをインスタンス暗黙のパラメータとして受け取ります。このクラスのインスタンスが定義されると、継承されたフィールドの値を見つけるためにインスタンス統合が使用されます。クラスでない親は依然として基礎となるコンストラクタの明示的なパラメータになります。

:::comment
: Parent projections via instance synthesis

  Structure field projections make use of {ref "structure-inheritance"}[inheritance information] to project parent structure fields from child structure values.
  Classes instead use instance synthesis: given a child class instance, synthesis will construct the parent; thus, methods are not added to child classes in the same way that projections are added to child structures.

:::

: インスタンス統合経由の親の射影

  構造体のフィールドの射影では {ref "structure-inheritance"}[継承情報] を使用して、子の構造体の値から親の構造体フィールドを射影します。クラスでは代わりにインスタンス統合を使用します：子のクラスのインスタンスに対して、統合によって親が構成されます；したがって、子の構造体に射影が追加されるのに対して、子クラスにメソッドが追加されることはありません。

:::comment
: Registered as class

  The resulting inductive type is registered as a type class, for which instances may be defined and that may be used as the type of instance-implicit arguments.

:::

: クラスとして登録される

  宣言の結果出来る帰納型は型クラスとして登録され、インスタンスの定義およびインスタンス暗黙の引数の型のために使用されます。

:::comment
: Out and semi-out parameters are considered

  The {name}`outParam` and {name}`semiOutParam` {tech}[gadgets] have no meaning in structure definitions, but they are used in class definitions to control instance search.

:::

: out と semi-out パラメータの考慮

  {name}`outParam` と {name}`semiOutParam` {tech}[ガジェット] は構造体定義では意味を持ちませんが、クラス定義ではインスタンス検索を制御するために使用されます。

:::comment
While {keywordOf Lean.Parser.Command.declaration}`deriving` clauses are allowed for class definitions to maintain the parallel between class and structure elaboration, they are not frequently used and should be considered an advanced feature.

:::

{keywordOf Lean.Parser.Command.declaration}`deriving` 句は、クラスと構造体のエラボレーションの間の並列性を維持するためにクラス定義で許可されていますが、頻繁に使用されるものではなく、高度な機能と見なされるべきです。

:::comment
::example "No Instances of Non-Classes"
:::
::::example "クラス以外ではインスタンスは存在しない"

:::comment
Lean rejects instance-implicit parameters of types that are not classes:
:::

Lean はクラスでない型のインスタンス暗黙のパラメータを拒否します：

```lean (error := true) (name := notClass)
def f [n : Nat] : n = n := rfl
```

```leanOutput notClass
invalid binder annotation, type is not a class instance
  Nat
use the command `set_option checkBinderAnnotations false` to disable the check
```

::::

:::comment
::example "Class vs Structure Constructors"
:::
::::example "クラスと構造体のコンストラクタ"
:::comment
A very small algebraic hierarchy can be represented either as structures ({name}`S.Magma`, {name}`S.Semigroup`, and {name}`S.Monoid` below), a mix of structures and classes ({name}`C1.Monoid`), or only using classes ({name}`C2.Magma`, {name}`C2.Semigroup`, and {name}`C2.Monoid`):
:::

非常に簡単な代数階層は、構造体（下記の {name}`S.Magma` ・ {name}`S.Semigroup` ・ {name}`S.Monoid` ）、構造体とクラスの混合（ {name}`C1.Monoid` ）、クラスのみ（ {name}`C2.Magma` ・ {name}`C2.Semigroup` ・ {name}`C2.Monoid` ）のいずれかで表現することができます：

````lean
namespace S
structure Magma (α : Type u) where
  op : α → α → α

structure Semigroup (α : Type u) extends Magma α where
  op_assoc : ∀ x y z, op (op x y) z = op x (op y z)

structure Monoid (α : Type u) extends Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end S

namespace C1
class Monoid (α : Type u) extends S.Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end C1

namespace C2
class Magma (α : Type u) where
  op : α → α → α

class Semigroup (α : Type u) extends Magma α where
  op_assoc : ∀ x y z, op (op x y) z = op x (op y z)

class Monoid (α : Type u) extends Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end C2
````


:::comment
{name}`S.Monoid.mk` and {name}`C1.Monoid.mk` have identical signatures, because the parent of the class {name}`C1.Monoid` is not itself a class:
:::

{name}`S.Monoid.mk` と {name}`C1.Monoid.mk` は同じシグネチャを持ちますが、これはクラス {name}`C1.Monoid` の親がそれ自身クラスではないからです：

```signature
S.Monoid.mk.{u} {α : Type u}
  (toSemigroup : S.Semigroup α)
  (ident : α)
  (ident_left : ∀ (x : α), toSemigroup.op ident x = x)
  (ident_right : ∀ (x : α), toSemigroup.op x ident = x) :
  S.Monoid α
```
```signature
C1.Monoid.mk.{u} {α : Type u}
  (toSemigroup : S.Semigroup α)
  (ident : α)
  (ident_left : ∀ (x : α), toSemigroup.op ident x = x)
  (ident_right : ∀ (x : α), toSemigroup.op x ident = x) :
  C1.Monoid α
```

:::comment
Similarly, because neither `S.Magma` nor `C2.Magma` inherits from another structure or class, their constructors are identical:
:::

同様に、`S.Magma` と `C2.Magma` のどちらも他の構造体やクラスを継承していないため、これらのコンストラクタは同一です：

```signature
S.Magma.mk.{u} {α : Type u} (op : α → α → α) : S.Magma α
```
```signature
C2.Magma.mk.{u} {α : Type u} (op : α → α → α) : C2.Magma α
```

:::comment
{name}`S.Semigroup.mk`, however, takes its parent as an ordinary parameter, while {name}`C2.Semigroup.mk` takes its parent as an instance implicit parameter:
:::

しかし、 {name}`S.Semigroup.mk` はその親を通常のパラメータとして受け取る一方で、 {name}`C2.Semigroup.mk` は親をインスタンス暗黙のパラメータとして受け取ります：

```signature
S.Semigroup.mk.{u} {α : Type u}
  (toMagma : S.Magma α)
  (op_assoc : ∀ (x y z : α),
    toMagma.op (toMagma.op x y) z = toMagma.op x (toMagma.op y z)) :
  S.Semigroup α
```
```signature
C2.Semigroup.mk.{u} {α : Type u} [toMagma : C2.Magma α]
  (op_assoc : ∀ (x y z : α),
    toMagma.op (toMagma.op x y) z = toMagma.op x (toMagma.op y z)) :
  C2.Semigroup α
```

:::comment
Finally, {name}`C2.Monoid.mk` takes its semigroup parent as an instance implicit parameter.
The references to `op` become references to the method {name}`C2.Magma.op`, relying on instance synthesis to recover the implementation from the {name}`C2.Semigroup` instance-implicit parameter via its parent projection:
:::

最後に、 {name}`C2.Monoid.mk` はインスタンス暗黙のパラメータとして半群の親を取ります。`op` への参照はメソッド {name}`C2.Magma.op` への参照になります。これは {name}`C2.Semigroup` のインスタンス暗黙のパラメータから親の射影を経由して実装を復元するインスタンス統合に依存しています：

```signature
C2.Monoid.mk.{u} {α : Type u}
  [toSemigroup : C2.Semigroup α]
  (ident : α)
  (ident_left : ∀ (x : α), C2.Magma.op ident x = x)
  (ident_right : ∀ (x : α), C2.Magma.op x ident = x) :
  C2.Monoid α
```
::::

:::comment
Parameters to type classes may be marked with {deftech}_gadgets_, which are special versions of the identity function that cause the elaborator to treat a value differently.
Gadgets never change the _meaning_ of a term, but they may cause it to be treated differently in elaboration-time search procedures.
The gadgets {name}`outParam` and {name}`semiOutParam` affect {ref "instance-synth"}[instance synthesis], so they are documented in that section.

:::

型クラスへ渡すパラメータは {deftech}_ガジェット_ （gadget）としてマークすることができます。ガジェットはエラボレータに値を異なるように扱わせる恒等関数の特別なバージョンです。ガジェットは項の _意味_ を変更することはありませんが、エラボレーション時の検索手続きで異なる扱いをさせることができます。ガジェット {name}`outParam` と {name}`semiOutParam` については {ref "instance-synth"}[インスタンス統合] に影響するため、その節で記述されています。

:::comment
Whether a type is a class or not has no effect on definitional equality.
Two instances of the same class with the same parameters are not necessarily identical and may in fact be very different.

:::

型がクラスであるかどうかは definitional equality には影響しません。同じパラメータを持つ同じクラスの2つのインスタンスは必ずしも同一ではなく、実際には大きく異なる可能性があります。

:::comment
::example "Instances are Not Unique"
:::
::::example "インスタンスは一意ではない"

:::comment
This implementation of binary heap insertion is buggy:
:::

この二分ヒープへの挿入の実装にはバグがあります：

````lean
structure Heap (α : Type u) where
  contents : Array α
deriving Repr

def Heap.bubbleUp [Ord α] (i : Nat) (xs : Heap α) : Heap α :=
  if h : i = 0 then xs
  else if h : i ≥ xs.contents.size then xs
  else
    let j := i / 2
    if Ord.compare xs.contents[i] xs.contents[j] == .lt then
      Heap.bubbleUp j {xs with contents := xs.contents.swap ⟨i, by omega⟩ ⟨j, by omega⟩}
    else xs

def Heap.insert [Ord α] (x : α) (xs : Heap α) : Heap α :=
  let i := xs.contents.size
  {xs with contents := xs.contents.push x}.bubbleUp i
````

:::comment
The problem is that a heap constructed with one {name}`Ord` instance may later be used with another, leading to the breaking of the heap invariant.

:::

問題は、ある {name}`Ord` インスタンスで構成されたヒープが後で別のインスタンスで使用される可能性があり、これによってヒープの不変性が破られることです。

:::comment
One way to correct this is to making the heap type depend on the selected `Ord` instance:
:::

これを修正する方法の1つとして、ヒープの型を選択された `Ord` インスタンスに依存させることです：

```lean
structure Heap' (α : Type u) [Ord α] where
  contents : Array α

def Heap'.bubbleUp [inst : Ord α] (i : Nat) (xs : @Heap' α inst) : @Heap' α inst :=
  if h : i = 0 then xs
  else if h : i ≥ xs.contents.size then xs
  else
    let j := i / 2
    if inst.compare xs.contents[i] xs.contents[j] == .lt then
      Heap'.bubbleUp j {xs with contents := xs.contents.swap ⟨i, by omega⟩ ⟨j, by omega⟩}
    else xs

def Heap'.insert [Ord α] (x : α) (xs : Heap' α) : Heap' α :=
  let i := xs.contents.size
  {xs with contents := xs.contents.push x}.bubbleUp i
end A
```

:::comment
In the improved definitions, {name}`Heap'.bubbleUp` is needlessly explicit; the instance does not need to be explicitly named here because Lean would select the indicated instances nonetheless, but it does bring the correctness invariant front and center for readers.
:::

改良された定義では、 {name}`Heap'.bubbleUp` は不必要に明示的です；Lean はどうであれ指示されたインスタンスを選択するため、ここで明示的にインスタンスを名付ける必要はありませんが、これによってコードを読む人に前と中間で不変性が保たれていることが提示されます。

::::

:::comment
## Sum Types as Classes
:::

## クラスとしての直和型（Sum Types as Classes）

%%%
tag := "class inductive"
%%%

:::comment
Most type classes follow the paradigm of a set of overloaded methods from which clients may choose freely.
This is naturally modeled by a product type, from which the overloaded methods are projections.
Some classes, however, are sum types: they require that the recipient of the synthesized instance first check _which_ of the available instance constructors was provided.
To account for these classes, a class declaration may consist of an arbitrary {tech}[inductive type], not just an extended form of structure declaration.

:::

ほとんどの型クラスはオーバーロードされたメソッドのセットからクライアントが自由に選択できるというパラダイムに従っています。これは自然に直積型によってモデル化され、そこからオーバーロードされたメソッドが射影されます。しかし、いくつかのクラスは直和型です：これらのクラスの統合されたインスタンスを受け取る方は利用可能なインスタンスのコンストラクタとして _どれが_ 提供されたかを最初にチェックする必要があります。このようなクラスを考慮するために、クラス宣言は構造体選言の拡張形だけでなく、任意の {tech}[帰納型] で構成することができます。

:::syntax Lean.Parser.Command.declaration
```grammar
$_:declModifiers
class inductive $d:declId $_:optDeclSig where
  $[| $_ $c:ident $_]*
$[deriving $[$x:ident],*]?
```
:::

:::comment
Class inductive types are just like other inductive types, except they may participate in instance synthesis.
The paradigmatic example of a class inductive is {name}`Decidable`: synthesizing an instance in a context with free variables amounts to synthesizing the decision procedure, but if there are no free variables, then the truth of the proposition can be established by instance synthesis alone (as is done by the {tactic (show:="decide")}`Lean.Parser.Tactic.decide` tactic).

:::

クラス帰納型はインスタンス統合に参加できることを除けば他の帰納型と同じです。クラス帰納型の典型的な例は {name}`Decidable` です：自由変数を持つコンテキストでインスタンスを統合することは決定手続きを統合することに等しいですが、自由変数が無い場合命題の真理は（ {tactic (show:="decide")}`Lean.Parser.Tactic.decide` タクティクでできるように）インスタンス統合だけで確立することができます。

:::comment
## Class Abbreviations
:::

## 省略クラス（Class Abbreviations）

%%%
tag := "class-abbrev"
%%%

:::comment
In some cases, many related type classes may co-occur throughout a codebase.
Rather than writing all the names repeatedly, it would be possible to define a class that extends all the classes in question, contributing no new methods itself.
However, this new class has a disadvantage: its instances must be declared explicitly.

:::

いくつかのケースでは、関連する型クラスがコードベース全体に同時に出現することがあります。それらのクラス名を繰り返し記述するよりも、該当するすべてのクラスを継承するクラスを定義した方が新しいメソッドを追加せずに済みます。しかし、この新しいクラスには欠点があります：そのインスタンスは明示的に宣言しなければなりません。

:::comment
The {keywordOf Lean.Parser.Command.classAbbrev}`class abbrev` command allows the creation of {deftech}_class abbreviations_ in which one name is short for a number of other class parameters.
Behind the scenes, a class abbreviation is represented by a class that extends all the others.
Its constructor is additionally declared to be an instance so the new class can be constructed by instance synthesis alone.

:::

{keywordOf Lean.Parser.Command.classAbbrev}`class abbrev` コマンドを使うと、 {deftech}_省略クラス_ （class abbreviation）を作成することができます。裏側では、省略クラスは他のすべてのクラスを継承するクラスとして表されます。そのコンストラクタはさらにインスタンスであることが宣言されているため、新しいクラスはインスタンス統合だけで構成できます。

:::::keepEnv

:::comment
::example "Class Abbreviations"
:::
::::example "省略クラス"
:::comment
Both {name}`plusTimes1` and {name}`plusTimes2` require that their parameters' type have {name}`Add` and {name}`Mul` instances:

:::

{name}`plusTimes1` と {name}`plusTimes2` はどちらもパラメータの型が {name}`Add` と {name}`Mul` のインスタンスを持っている必要があります：

```lean
class abbrev AddMul (α : Type u) := Add α, Mul α

def plusTimes1 [AddMul α] (x y z : α) := x + y * z

class AddMul' (α : Type u) extends Add α, Mul α

def plusTimes2 [AddMul' α] (x y z : α) := x + y * z
```

:::comment
Because {name}`AddMul` is a {keywordOf Lean.Parser.Command.classAbbrev}`class abbrev`, no additional declarations are necessary to use {name}`plusTimes1` with {lean}`Nat`:

:::

{name}`AddMul` は {keywordOf Lean.Parser.Command.classAbbrev}`class abbrev` であるため、 {lean}`Nat` で {name}`plusTimes1` を使用するために追加の宣言は必要ありません：

```lean (name := plusTimes1)
#eval plusTimes1 2 5 7
```
```leanOutput plusTimes1
37
```

:::comment
However, {name}`plusTimes2` fails, because there is no {lean}`AddMul' Nat` instance—no instances whatsoever have yet been declared:
:::

しかし、 {name}`plusTimes2` では {lean}`AddMul' Nat` インスタンスが無い（インスタンスがまだ何も宣言されていない）ため失敗します：

```lean (name := plusTimes2a) (error := true)
#eval plusTimes2 2 5 7
```
```leanOutput plusTimes2a
failed to synthesize
  AddMul' ?m.22
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
:::comment
Declaring an very general instance takes care of the problem for {lean}`Nat` and every other type:
:::

この場合は非常に一般的なインスタンスを宣言することで {lean}`Nat` や他のすべての型の問題を解決できます：

```lean (name := plusTimes2b)
instance [Add α] [Mul α] : AddMul' α where

#eval plusTimes2 2 5 7
```
```leanOutput plusTimes2b
37
```
::::
:::::

{include 0 Manual.Classes.InstanceDecls}

{include 0 Manual.Classes.InstanceSynth}

# インスタンス導出（Deriving Instances）
%%%
tag := "deriving-instances"
%%%
:::comment
# Deriving Instances
:::

:::comment
Lean can automatically generate instances for many classes, a process known as {deftech}_deriving_ instances.
Instance deriving can be invoked either when defining a type or as a stand-alone command.

:::

Lean は多くのクラスに対して自動的にインスタンスを生成することができます。これはインスタンスの {deftech}_導出_ （deriving）と呼ばれる処理です。インスタンスの導出は型を定義する時に呼び出すことも、独立したコマンドとして呼び出すこともできます。

::::syntax Lean.Parser.Command.optDeriving (open := false)
:::comment
As part of a command that creates a new inductive type, a {keywordOf Lean.Parser.Command.declaration}`deriving` clause specifies a comma-separated list of class names for which instances should be generated:
:::

新しい帰納型を作成するコマンドの一部としての {keywordOf Lean.Parser.Command.declaration}`deriving` 句には、その型からインスタンスが生成されるべきクラス名のカンマ区切りのリストを指定します：

```grammar
$[deriving $[$_],*]?
```
::::

::::syntax Lean.Parser.Command.deriving
:::comment
The stand-alone {keywordOf Lean.Parser.Command.deriving}`deriving` command specifies a number of class names and subject names.
Each of the specified classes are derived for each of the specified subjects.
:::

独立した {keywordOf Lean.Parser.Command.deriving}`deriving` コマンドには複数のクラスと対象の名前を指定します。指定された各クラスは指定された各対象に対して導出されます。

```grammar
deriving instance $[$_],* for $_,*
```
::::

:::::keepEnv
:::comment
::example "Deriving Multiple Classes"
:::
::::example "複数クラスの導出"
:::comment
After specifying multiple classes to derive for multiple types, as in this code:
:::

このコードのように、複数の型に対して導出する複数のクラスを指定した場合：

```lean
structure A where
structure B where

deriving instance BEq, Repr for A, B
```
:::comment
all the instances exist for all the types, so all four {keywordOf Lean.Parser.Command.synth}`#synth` commands succeed:
:::

すべての型にすべてのインスタンスが存在するため、4つの {keywordOf Lean.Parser.Command.synth}`#synth` コマンドはすべて成功します：

```lean
#synth BEq A
#synth BEq B
#synth Repr A
#synth Repr B
```
::::
:::::

{include 2 Manual.Classes.DerivingHandlers}

{include 0 Manual.Classes.BasicClasses}
