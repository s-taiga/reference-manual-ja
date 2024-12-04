/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Manual
open Verso.Genre
open Verso.Genre.Manual

/-
#doc (Manual) "Instance Declarations" =>
-/
#doc (Manual) "インスタンスの宣言（Instance Declarations）" =>
%%%
tag := "instance-declarations"
%%%


:::comment
The syntax of instance declarations is almost identical to that of definitions.
The only syntactic differences are that the keyword {keywordOf Lean.Parser.Command.declaration}`def` is replaced by {keywordOf Lean.Parser.Command.declaration}`instance` and the name is optional:

:::

インスタンス宣言の構文は定義とほとんど同じです。唯一の構文の違いは、キーワード {keywordOf Lean.Parser.Command.declaration}`def` が {keywordOf Lean.Parser.Command.declaration}`instance` に置き換えられていることと、名前が省略可能であることです：

::::syntax Lean.Parser.Command.instance

:::comment
Most instances define each method using {keywordOf Lean.Parser.Command.declaration}`where` syntax:

:::

ほとんどのインスタンスでは {keywordOf Lean.Parser.Command.declaration}`where` 構文を使って各メソッドを定義します：

```grammar
instance $[(priority := $p:prio)]? $name? $_ where
  $_*
```

:::comment
However, type classes are inductive types, so instances can be constructed using any expression with an appropriate type:

:::

しかし、型クラスは帰納型であるため、インスタンスは適切な型を持つ任意の式を使って構築できます：

```grammar
instance $[(priority := $p:prio)]? $_? $_ :=
  $_
```

:::comment
Instances may also be defined by cases; however, this feature is rarely used outside of {name}`Decidable` instances:

:::

インスタンスはケースによって定義することもできます；しかし、 {name}`Decidable` のインスタンス以外でこの機能が使われることはほとんどありません：

```grammar
instance $[(priority := $p:prio)]? $_? $_
  $[| $_ => $_]*
```

::::

:::comment
Instances defined with explicit terms often consist of either anonymous constructors ({keywordOf Lean.Parser.Term.anonymousCtor}`⟨...⟩`) wrapping method implementations or of invocations of {name}`inferInstanceAs` on definitionally equal types.

:::

明示的な条件で定義されたインスタンスは多くの場合、メソッドの実装をラップする匿名コンストラクタ（ {keywordOf Lean.Parser.Term.anonymousCtor}`⟨...⟩` ）か、定義が等しい型に対する {name}`inferInstanceAs` の呼び出しで構成されます。

:::comment
Elaboration of instances is almost identical to the elaboration of ordinary definitions, with the exception of the caveats documented below.
If no name is provided, then one is created automatically.
It is possible to refer to this generated name directly, but the algorithm used to generate the names has changed in the past and may change in the future.
It's better to explicitly name instances that will be referred to directly.
After elaboration, the new instance is registered as a candidate for instance search.
Adding the attribute {attr}`instance` to a name can be used to mark any other defined name as a candidate.

:::

インスタンスのエラボレーションは以下に示す注意点を除いて通常の定義の作成とほとんど同じです。名前が提供されない場合は、自動的に名前が生成されます。この生成された名前を直接参照することは可能ですが、名前の生成に使用されるアルゴリズムは過去に変更されたことがあり、将来的にも変更される可能性があります。直接参照されるインスタンスには明示的に名前を付ける方が良いです。エラボレーションの後、新しいインスタンスはインスタンス検索の候補として登録されます。名前に {attr}`instance` 属性を追加することで、他の定義された名前を候補としてマークすることができます。

:::::keepEnv
:::comment
::example "Instance Name Generation"
:::
::::example "インスタンス名の生成"
:::comment
Following these declarations:
:::

以下のこれらの定義について：

```lean
structure NatWrapper where
  val : Nat

instance : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y
```

:::comment
the name {lean}`instBEqNatWrapper` refers to the new instance.
:::

新しいインスタンスの名前は {lean}`instBEqNatWrapper` となります。

::::
:::::

:::::keepEnv
:::comment
::example "Variations in Instance Definitions"
:::
::::example "インスタンス定義のバリエーション"

:::comment
Given this structure type:
:::

この構造体型に対して：

```lean
structure NatWrapper where
  val : Nat
```
:::comment
all of the following ways of defining a {name}`BEq` instance are equivalent:
:::

{name}`BEq` インスタンスの定義である以下のすべては同等です：

```lean
instance : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y

instance : BEq NatWrapper :=
  ⟨fun x y => x.val == y.val⟩

instance : BEq NatWrapper :=
  ⟨fun ⟨x⟩ ⟨y⟩ => x == y⟩
```

:::comment
Aside from introducing different names into the environment, the following are also equivalent:
:::

環境に異なる名前を導入することを除けば、以下の同等です：

```lean
@[instance]
def instBeqNatWrapper : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y

instance : BEq NatWrapper :=
  ⟨fun x y => x.val == y.val⟩

instance : BEq NatWrapper :=
  ⟨fun ⟨x⟩ ⟨y⟩ => x == y⟩
```
::::
:::::

:::comment
# Recursive Instances
:::

# 再帰的なインスタンス（Recursive Instances）

%%%
tag := "recursive-instances"
%%%

:::comment
Functions defined in {keywordOf Lean.Parser.Command.declaration}`where` structure definition syntax are not recursive.
Because instance declaration is a version of structure definition, type class methods are also not recursive by default.
Instances for recursive inductive types are common, however.
There is a standard idiom to work around this limitation: define a recursive function independently of the instance, and then refer to it in the instance definition.
By convention, these recursive functions have the name of the corresponding method, but are defined in the type's namespace.

:::

{keywordOf Lean.Parser.Command.declaration}`where` による構造体定義構文で定義された関数は再帰的ではありません。インスタンス宣言は構造体定義の亜種であるため、型クラスのメソッドもデフォルトでは再帰的ではありません。しかし、再帰的帰納型のインスタンスは一般的です。この制限を回避するための標準的なパターンがあります：インスタンスとは独立に再帰関数を定義し、インスタンス定義でそれを参照するというものです。慣例として、これらの再帰関数は対応するメソッドの名前を持ちますが、型の名前空間で定義されます。

:::comment
:: example "Instances are not recursive"
:::
:::: example "インスタンスは再帰的ではない"
:::comment
Given this definition of {lean}`NatTree`:
:::

以下の {lean}`NatTree` の定義に対して：

```lean
inductive NatTree where
  | leaf
  | branch (left : NatTree) (val : Nat) (right : NatTree)
```
:::comment
the following {name}`BEq` instance fails:
:::

以下の {name}`BEq` インスタンスは失敗します：

```lean (error := true) (name := beqNatTreeFail)
instance : BEq NatTree where
  beq
    | .leaf, .leaf => true
    | .branch l1 v1 r1, .branch l2 v2 r2 => l1 == l2 && v1 == v2 && r1 == r2
    | _, _ => false
```
:::comment
with errors in both the left and right recursive calls that read:
:::

これは左右両方の再帰呼び出しでエラーが発生しています：

```leanOutput beqNatTreeFail
failed to synthesize
  BEq NatTree
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
:::comment
Given a suitable recursive function, such as {lean}`NatTree.beq`:
:::

{lean}`NatTree.beq` のような適切な再帰関数を与え：

```lean
def NatTree.beq : NatTree → NatTree → Bool
  | .leaf, .leaf => true
  | .branch l1 v1 r1, .branch l2 v2 r2 => l1 == l2 && v1 == v2 && r1 == r2
  | _, _ => false
```
:::comment
the instance can be created in a second step:
:::

次のステップでインスタンスを作成できます：

```lean
instance : BEq NatTree where
  beq := NatTree.beq
```
:::comment
or, equivalently, using anonymous constructor syntax:
:::

もしくは同等ですが、匿名コンストラクタ構文を使うことでも作成できます：

```lean
instance : BEq NatTree := ⟨NatTree.beq⟩
```
::::

:::comment
Furthermore, instances are not available for instance synthesis during their own definitions.
They are first marked as being available for instance synthesis after they are defined.
Nested inductive types, in which the recursive occurrence of the type occurs as a parameter to some other inductive type, may require an instance to be available to write even the recursive function.
The standard idiom to work around this limitation is to create a local instance in a recursively-defined function that includes a reference to the function being defined, taking advantage of the fact that instance synthesis may use every binding in the local context with the right type.


:::

さらに、インスタンスはそれ自身の定義中はインスタンス統合のために利用できません。インスタンスは定義された後、はじめてインスタンス統合のために利用可能であるとマークされます。型の再帰的な出現が他の帰納型のパラメータとして出現している入れ子になった帰納型ではインスタンスは再帰関数としても書けることを要求する場合があります。この制限を回避する標準的なイディオムは、定義されている関数への参照を含む再帰的に定義された関数内にてローカルインスタンスを作成することです。これにはローカルコンテキストのすべての束縛においてインスタンス統合が正しい型で使える利点があります。

:::comment
:: example "Instances for nested types"
:::
:::: example "入れ子の型のインスタンス"
:::comment
In this definition of {lean}`NatRoseTree`, the type being defined occurs nested under another inductive type constructor ({name}`Array`):
:::

この {lean}`NatRoseTree` の定義では、定義されている型は別の帰納型コンストラクタ（ {name}`Array` ）の下に入れ子になっています：

```lean
inductive NatRoseTree where
  | node (val : Nat) (children : Array NatRoseTree)

```
:::comment
Checking the equality of rose trees requires checking equality of arrays.
However, instances are not typically available for instance synthesis during their own definitions, so the following definition fails, even though {lean}`NatRoseTree.beq` is a recursive function and is in scope in its own definition.
:::

バラの木の等価性をチェックするには、配列の等価性をチェックする必要があります。しかし、インスタンスは通常それ自身の定義中にインスタンス統合のために利用できないため、たとえ {lean}`NatRoseTree.beq` が再帰関数であり、それ自身の定義のスコープ内にあるにもかかわらず以下の定義は失敗します。

```lean (error := true) (name := natRoseTreeBEqFail) (keep := false)
def NatRoseTree.beq : (tree1 tree2 : NatRoseTree) → Bool
  | .node val1 children1, .node val2 children2 =>
    val1 == val2 &&
    children1 == children2
```
```leanOutput natRoseTreeBEqFail
failed to synthesize
  BEq (Array NatRoseTree)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

:::comment
To solve this, a local {lean}`BEq NatRoseTree` instance may be `let`-bound:

:::

これを解決するために、`let` 束縛されたローカルの {lean}`BEq NatRoseTree` インスタンスを作成します：

```lean
partial def NatRoseTree.beq : (tree1 tree2 : NatRoseTree) → Bool
  | .node val1 children1, .node val2 children2 =>
    let _ : BEq NatRoseTree := ⟨NatRoseTree.beq⟩
    val1 == val2 &&
    children1 == children2
```
:::comment
The use of array equality on the children finds the let-bound instance during instance synthesis.
:::

インスタンス統合時に、子に対して配列の等価性を使用することで let 束縛されたインスタンスが発見されて使用されます。

::::

:::comment
# Instances of `class inductive`s
:::

# `class inductive` のインスタンス（Instances of `class inductive`s）

%%%
tag := "class-inductive-instances"
%%%

:::comment
Many instances have function types: any instance that itself recursively invokes instance search is a function, as is any instance with implicit parameters.
While most instances only project method implementations from their own instance parameters, instances of class inductive types typically pattern-match one or more of their arguments, allowing the instance to select the appropriate constructor.
This is done using ordinary Lean function syntax.
Just as with other instances, the function in question is not available for instance synthesis in its own definition.
:::

多くのインスタンスは関数型を持っています：それ自身がインスタンス検索を再帰的に呼び出す任意のインスタンスは関数であり、暗黙のパラメータを持つインスタンスも同様です。ほとんどのインスタンスは自身のインスタンスパラメータからメソッドの実装を射影するだけですが、帰納的なクラスの型のインスタンスは通常、1つ以上の引数をパターンマッチさせ、インスタンスが適切なコンストラクタを選択できるようにします。これは通常の Lean の関数の構文を使って行われます。他のインスタンスと同様に、問題の関数はそれ自身の定義ではインスタンス統合のために利用できません。

:::::keepEnv
:::comment
::example "An instance for a sum class"
:::
::::example "直和クラスのためのインスタンス"
```lean (show := false)
axiom α : Type
```
:::comment
Because {lean}`DecidableEq α` is an abbreviation for {lean}`(a b : α) → Decidable (Eq a b)`, its arguments can be used directly, as in this example:

:::

{lean}`DecidableEq α` は {lean}`(a b : α) → Decidable (Eq a b)` の省略形であるため、この例のように直接引数を使うことができます：

```lean
inductive ThreeChoices where
  | yes | no | maybe

instance : DecidableEq ThreeChoices
  | .yes,   .yes   =>
    .isTrue rfl
  | .no,    .no    =>
    .isTrue rfl
  | .maybe, .maybe =>
    .isTrue rfl
  | .yes,   .maybe | .yes,   .no
  | .maybe, .yes   | .maybe, .no
  | .no,    .yes   | .no,    .maybe =>
    .isFalse nofun

```

::::
:::::

:::::keepEnv
:::comment
::example "A recursive instance for a sum class"
:::
::::example "直和クラスのための再帰的なインスタンス"
:::comment
The type {lean}`StringList` represents monomorphic lists of strings:
:::

型 {lean}`StringList` はモノ射な文字列リストを表します：

```lean
inductive StringList where
  | nil
  | cons (hd : String) (tl : StringList)
```
:::comment
In the following attempt at defining a {name}`DecidableEq` instance, instance synthesis invoked while elaborating the inner {keywordOf termIfThenElse}`if` fails because the instance is not available for instance synthesis in its own definition:
:::

以下の {name}`DecidableEq` インスタンスを定義しようとすると、内部の {keywordOf termIfThenElse}`if` をエラボレートする際にインスタンス統合が呼び出されますが、インスタンスがそれ自身の定義でインスタンス統合に利用できないため失敗します：

```lean (error := true) (name := stringListNoRec) (keep := false)
instance : DecidableEq StringList
  | .nil, .nil => .isTrue rfl
  | .cons h1 t1, .cons h2 t2 =>
    if h : h1 = h2 then
      if h' : t1 = t2 then
        .isTrue (by simp [*])
      else
        .isFalse (by intro hEq; cases hEq; trivial)
    else
      .isFalse (by intro hEq; cases hEq; trivial)
  | .nil, .cons _ _ | .cons _ _, .nil => .isFalse nofun
```
```leanOutput stringListNoRec
failed to synthesize
  Decidable (t1 = t2)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
:::comment
However, because it is an ordinary Lean function, it can recursively refer to its own explicitly-provided name:
:::

しかし、これは通常の Lean の関数であるため、明示的に与えられた名前を再帰的に参照することができます：

```lean
instance instDecidableEqStringList : DecidableEq StringList
  | .nil, .nil => .isTrue rfl
  | .cons h1 t1, .cons h2 t2 =>
    if h : h1 = h2 then
      if h' : instDecidableEqStringList t1 t2 then
        .isTrue (by simp [*])
      else
        .isFalse (by intro hEq; cases hEq; trivial)
    else
      .isFalse (by intro hEq; cases hEq; trivial)
  | .nil, .cons _ _ | .cons _ _, .nil => .isFalse nofun
```
::::
:::::


:::comment
# Instance Priorities
:::

# インスタンスの優先度（Instance Priorities）

%%%
tag := "instance-priorities"
%%%

:::comment
Instances may be assigned {deftech}_priorities_.
During instance synthesis, higher-priority instances are preferred; see {ref "instance-synth"}[the section on instance synthesis] for details of instance synthesis.

:::

インスタンスには {deftech}_優先度_ （priority）を割り当てることができます。インスタンス統合において、高い優先度のインスタンスが優先されます：インスタンス統合の詳細については {ref "instance-synth"}[インスタンス統合の節] を参照してください。

::::syntax prio open:=false
:::comment
Priorities may be numeric:
:::

優先度は数値を指定できます：

```grammar
$n:num
```

:::comment
If no priority is specified, the default priority that corresponds to {evalPrio}`default` is used:
:::

優先度が指定されていない場合、 {evalPrio}`default` に対応するデフォルトの優先度が使用されます：

```grammar
default
```

:::comment
Three named priorities are available when numeric values are too fine-grained, corresponding to {evalPrio}`low`, {evalPrio}`mid`, and {evalPrio}`high` respectively.
The {keywordOf prioMid}`mid` priority is lower than {keywordOf prioDefault}`default`.
:::

数値による指定が細かすぎるケースのために、 {evalPrio}`low` ・ {evalPrio}`mid` ・ {evalPrio}`high` の名前付きの優先度を利用することができます。 {keywordOf prioMid}`mid` 優先度は {keywordOf prioDefault}`default` よりも低くなります。

```grammar
low
```
```grammar
mid
```
```grammar
high
```

:::comment
Finally, priorities can be added and subtracted, so `default + 2` is a valid priority, corresponding to {evalPrio}`default + 2`:
:::

最後に、優先度は足し引きが可能であるため、`default + 2` は有効な優先度であり、 {evalPrio}`default + 2` に対応します：

```grammar
($_)
```
```grammar
$_ + $_
```
```grammar
$_ - $_
```

::::

:::comment
# Default Instances
:::

# デフォルトインスタンス（Default Instances）

%%%
tag := "default-instances"
%%%

:::comment
The {attr}`default_instance` attribute specifies that an instance {ref "default-instance-synth"}[should be used as a fallback in situations where there is not enough information to select it otherwise].
If no priority is specified, then the default priority `default` is used.

:::

{attr}`default_instance` 属性は、そのインスタンスが {ref "default-instance-synth"}[他に選択するのに十分な情報がない場合にフォールバックとして使用する] ことを指定します。優先度が指定されていない場合、デフォルトの優先度 `default` が使用されます。

:::syntax attr
```grammar
default_instance $p?
```
:::

:::::keepEnv
:::comment
::example "Default Instances"
:::
::::example "デフォルトインスタンス"
:::comment
A default instance of {lean}`OfNat Nat` is used to select {lean}`Nat` for natural number literals in the absence of other type information.
It is declared in the Lean standard library with priority 100.
Given this representation of even numbers, in which an even number is represented by half of it:
:::

{lean}`OfNat Nat` のデフォルトインスタンスは、他の型情報がない場合に自然数リテラルに対して {lean}`Nat` を選択するために使用されます。これは Lean の標準ライブラリで優先度 100 で宣言されています。この偶数の表現では、偶数はその半分の値で表現されています：

```lean
structure Even where
  half : Nat
```

:::comment
the following instances allow numeric literals to be used for small {lean}`Even` values (a limit on the depth of type class instance search prevents them from being used for arbitrarily large literals):
:::

以下のインスタンスでは、数値リテラルを小さな {lean}`Even` に使用することができます（型クラスインスタンス検索の深さの制限により、任意の大きさのリテラルに使用することはできません）：

```lean (name := insts)
instance ofNatEven0 : OfNat Even 0 where
  ofNat := ⟨0⟩

instance ofNatEvenPlusTwo [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := ⟨(OfNat.ofNat n : Even).half + 1⟩

#eval (0 : Even)
#eval (34 : Even)
#eval (254 : Even)
```
```leanOutput insts
{ half := 0 }
```
```leanOutput insts
{ half := 17 }
```
```leanOutput insts
{ half := 127 }
```

:::comment
Specifying them as default instances with a priority greater than or equal to 100 causes them to be used instead of {lean}`Nat`:
:::

これらを優先度が 100 以上のデフォルトインスタンスとして指定すると、 {lean}`Nat` の代わりに使用されます：

```lean
attribute [default_instance 100] ofNatEven0
attribute [default_instance 100] ofNatEvenPlusTwo
```
```lean (name := withDefaults)
#eval 0
#eval 34
```
```leanOutput withDefaults
{ half := 0 }
```
```leanOutput withDefaults
{ half := 17 }
```

:::comment
Non-even numerals still use the {lean}`OfNat Nat` instance:
:::

偶数でない数字では依然として {lean}`OfNat Nat` インスタンスが使用されます：

```lean (name := stillNat)
#eval 5
```
```leanOutput stillNat
5
```
::::
:::::

:::comment
# The Instance Attribute
:::

# インスタンス属性（The Instance Attribute）

%%%
tag := "instance-attribute"
%%%

:::comment
The {attr}`instance` attribute declares a name to be an instance, with the specified priority.
Like other attributes, {attr}`instance` can be applied globally, locally, or only when the current namespace is opened.
The {keywordOf Lean.Parser.Command.declaration}`instance` declaration is a form of definition that automatically applies the {attr}`instance` attribute.

:::

{attr}`instance` 属性は指定された優先度で名前をインスタンスであると宣言します。他の属性と同様に、 {attr}`instance` 属性はグローバル・ローカル・現在の名前空間がオープンされた時にのみに適用できます。 {keywordOf Lean.Parser.Command.declaration}`instance` 宣言は {attr}`instance` 属性を自動的に適用する定義の形式です。

::::syntax attr

:::comment
Declares the definition to which it is applied to be an instance.
If no priority is provided, then the default priority `default` is used.

:::

適用される定義がインスタンスであることを宣言します。優先度を指定しない場合は、デフォルトの優先度 `default` が使用されます。

```grammar
instance $p?
```


::::
