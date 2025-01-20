/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

/-
#doc (Manual) "Structure Declarations" =>
-/
#doc (Manual) "構造体宣言（Structure Declarations）" =>
%%%
tag := "structures"
%%%

::::syntax command
```grammar
$_:declModifiers
structure $d:declId $_:bracketedBinder*
    $[extends $_,*]? $[: $_]? where
  $[$_:declModifiers $_ ::]?
  $_
$[deriving $[$_],*]?
```

:::comment
Declares a new structure type.
:::

新しい構造体の型を宣言します。

::::

:::comment
{deftech}[Structures] are inductive types that have only a single constructor and no indices.
In exchange for these restrictions, Lean generates code for structures that offers a number of conveniences: projection functions are generated for each field, an additional constructor syntax based on field names rather than positional arguments is available, a similar syntax may be used to replace the values of certain named fields, and structures may extend other structures.
Just like other inductive types, structures may be recursive; they are subject to the same restrictions regarding strict positivity.
Structures do not add any expressive power to Lean; all of their features are implemented in terms of code generation.

:::

{deftech}[構造体] （structure）は単一のコンストラクタを持ち、添字を持たない帰納型です。これらの制限と引き換えに、Lean は構造体のための数々の便利なコードを生成します：各フィールドに対して生成される射影関数・位置引数ではなくフィールド名に基づく追加のコンストラクタ構文が利用できる・同様の構文を使用して特定の名前付きフィールドの値を書き換えることができる・構造体は他の構造体を拡張することができる。他の帰納型と同様に、構造体も再帰的にすることができます；また strict positivity に関しても同じ制約を受けます。構造体は Lean の表現力を増すものではありません；構造体のすべての機能はコード生成によって実装されています。

```lean (show := false)
-- Test claim about recursive above

/--
error: (kernel) arg #1 of 'RecStruct.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
structure RecStruct where
  next : RecStruct → RecStruct

```

:::comment
# Structure Parameters
:::

# 構造体のパラメータ（Structure Parameters）
%%%
tag := "structure-params"
%%%


:::comment
Just like ordinary inductive type declarations, the header of the structure declaration contains a signature that may specify both parameters and a resulting universe.
Structures may not define {tech}[indexed families].

:::

通常の帰納型宣言と同様に、構造体宣言のヘッダにはパラメータと結果の宇宙の両方を指定できるシグネチャが含まれます。構造体は {tech}[添字付けられた型の族] を定義することはできません。

:::comment
# Fields
:::

# フィールド（Fields）
%%%
tag := "structure-fields"
%%%


:::comment
Each field of a structure declaration corresponds to a parameter of the constructor.
Auto-implicit arguments are inserted in each field separately, even if their names coincide, and the fields become constructor parameters that quantify over types.

:::

構造体宣言の各フィールドは、コンストラクタのパラメータに対応します。自動的な暗黙引数はたとえ名前が一致していても各フィールドに別々に挿入され、フィールドは型を量化するコンストラクタのパラメータになります。

:::comment
:: example "Auto-implicit parameters in structure fields"
:::
::::: example "構造体のフィールドの自動的な暗黙のパラメータ"

:::comment
The structure {lean}`MyStructure` contains a field whose type is an auto-implicit parameter:

:::

構造体 {lean}`MyStructure` は型が自動的な暗黙のパラメータであるフィールドを含んでいます：

```lean
structure MyStructure where
  field1 : α
  field2 : α
```
:::comment
The type constructor {name}`MyStructure` takes two universe parameters:
:::

型コンストラクタ {name}`MyStructure` は2つの宇宙パラメータを取ります：

```signature
MyStructure.{u, v} : Type (max u v)
```
:::comment
The resulting type is in `Type` rather than `Sort` because the constructor fields quantify over types in `Sort`. In particular, both fields in its constructor {name}`MyStructure.mk` take an implicit type parameter:
:::

コンストラクタのフィールドは `Sort` の型に対して量化されるため、結果の型は `Type` ではなく `Sort` になります。具体的には、コンストラクタ {name}`MyStructure.mk` の両方のフィールドは暗黙の型パラメータを取ります：

```signature
MyStructure.mk.{u, v}
  (field1 : {α : Sort u} → α)
  (field2 : {α : Sort v} → α)
  : MyStructure.{u,v}
```

:::::


:::comment
For each field, a {deftech}[projection function] is generated that extracts the field's value from the underlying type's constructor.
This function is in the structure's name's namespace.
Structure field projections are handled specially by the elaborator (as described in the {ref "structure-inheritance"}[section on structure inheritance]), which performs extra steps beyond looking up a namespace.
When field types depend on prior fields, the types of the dependent projection functions are written in terms of earlier projections, rather than explicit pattern matching.


:::

各フィールドに対してベースとなる型のコンストラクタからフィールドの値を抽出する {deftech}[射影関数] （projection function）が生成されます。この関数は構造体の名前の名前空間に存在します。構造体のフィールドの射影はエラボレータによって特別に処理され（ {ref "structure-inheritance"}[構造体の継承についての節] で説明します）、名前空間を検索する以上の余分なステップが実行されます。フィールドの型が先行するフィールドに依存する場合、依存する射影関数の型は、明示的なパターンマッチではなく、先行する射影によって記述されます。

:::comment
:: example "Dependent projection types"
:::
::::: example "依存射影型"

:::comment
The structure {lean}`ArraySized` contains a field whose type depends on both a structure parameter and an earlier field:
:::

構造体 {lean}`ArraySized` は型が構造体のパラメータとそれより前のフィールドの両方に依存するフィールドを含んでいます：

```lean
structure ArraySized (α : Type u) (length : Nat)  where
  array : Array α
  size_eq_length : array.size = length
```

:::comment
The signature of the projection function {name ArraySized.size_eq_length}`size_eq_length` takes the structure type's parameter as an implicit parameter and refers to the earlier field using the corresponding projection:
:::

射影関数 {name ArraySized.size_eq_length}`size_eq_length` のシグネチャは構造体の型のパラメータを暗黙のパラメータとして受け取り、対応する射影を使ってそれより前のフィールドを参照します：

```signature
ArraySized.size_eq_length.{u}
  {α : Type u} {length : Nat}
  (self : ArraySized α length)
  : self.array.size = length
```

:::::

:::comment
Structure fields may have default values, specified with `:=`.
These values are used if no explicit value is provided.


:::

構造体のフィールドは `:=` で指定されたデフォルト値を持つことができます。明示的な値が提供されない場合、これらの値が使用されます。

:::comment
:: example "Default values"
:::
:::: example "デフォルト値"

:::comment
An adjacency list representation of a graph can be represented as an array of lists of {lean}`Nat`.
The size of the array indicates the number of vertices, and the outgoing edges from each vertex are stored in the array at the vertex's index.
Because the default value {lean}`#[]` is provided for the field {name Graph.adjacency}`adjacency`, the empty graph {lean}`Graph.empty` can be constructed without providing any field values.
:::

グラフの隣接リスト表現は {lean}`Nat` のリストの配列として表すことができます。配列のサイズは頂点の数を表し、各頂点から出る辺は頂点のインデックスで配列に格納されます。フィールド {name Graph.adjacency}`adjacency` にはデフォルト値 {lean}`#[]` が指定されているため、フィールドの値を指定しなくても空のグラフ {lean}`Graph.empty` を作成することができます。

```lean
structure Graph where
  adjacency : Array (List Nat) := #[]

def Graph.empty : Graph := {}
```
::::


:::comment
Structure fields may additionally be accessed via their index, using dot notation.
Fields are numbered beginning with `1`.


:::

構造体のフィールドはさらに、ドット記法を使ってインデックスからアクセスすることもできます。フィールドの番号は `1` から始まります。

:::comment
# Structure Constructors
:::

# 構造体のコンストラクタ（Structure Constructors）
%%%
tag := "structure-constructors"
%%%



:::comment
Structure constructors may be explicitly named by providing the constructor name and `::` prior to the fields.
If no name is explicitly provided, then the constructor is named `mk` in the structure type's namespace.
{ref "declaration-modifiers"}[Declaration modifiers] may additionally be provided along with an explicit constructor name.

:::

構造体のコンストラクタは、フィールドの前にコンストラクタ名と `::` を指定することで明示的に名前を付けることができます。名前が明示的に与えられない場合、コンストラクタ名は構造体型の名前空間の `mk` という名前になります。また、明示的なコンストラクタ名と共に、 {ref "declaration-modifiers"}[宣言修飾子] を指定することもできます。

:::comment
:: example "Non-default constructor name"
:::
:::: example "デフォルトではないコンストラクタ名"
:::comment
The structure  {lean}`Palindrome` contains a string and a proof that the string is the same when reversed:

:::

構造体 {lean}`Palindrome` は文字列と、その文字列が反転しても同じであることの証明を含みます：

```lean
structure Palindrome where
  ofString ::
  text : String
  is_palindrome : text.data.reverse = text.data
```

:::comment
Its constructor is named {name}`Palindrome.ofString`, rather than `Palindrome.mk`.

:::

そのコンストラクタ名は `Palindrome.mk` ではなく {name}`Palindrome.ofString` です。

::::

:::comment
:: example "Modifiers on structure constructor"
:::
:::: example "構造体のコンストラクタの修飾子"
:::comment
The structure {lean}`NatStringBimap` maintains a finite bijection between natural numbers and strings.
It consists of a pair of maps, such that the keys each occur as values exactly once in the other map.
Because the constructor is private, code outside the defining module can't construct new instances and must use the provided API, which maintains the invariants of the type.
Additionally, providing the default constructor name explicitly is an opportunity to attach a {tech}[documentation comment] to the constructor.

:::

構造体 {lean}`NatStringBimap` は自然数と文字列の間の有限な全単射を保持します。これはマップのペアで構成され、それぞれのキーがもう一方の写像の値として一度だけ出現するようになっています。コンストラクタはプライベートであるため、これを定義したモジュールの外のコードでは新しいインスタンスを作成できず、提供されたAPIを使用しなければなりません。このAPIでは型の不変量を保持します。さらに、デフォルトのコンストラクタ名を明示的に指定することで、コンストラクタに {tech}[documentation comment] を付けることができます。

```lean
structure NatStringBimap where
  /--
  Build a finite bijection between some
  natural numbers and strings
  -/
  private mk ::
  natToString : Std.HashMap Nat String
  stringToNat : Std.HashMap String Nat

def NatStringBimap.empty : NatStringBimap := ⟨{}, {}⟩

def NatStringBimap.insert
    (nat : Nat) (string : String)
    (map : NatStringBimap) :
    Option NatStringBimap :=
  if map.natToString.contains nat ||
      map.stringToNat.contains string then
    none
  else
    some (NatStringBimap.mk (map.natToString.insert nat string) (map.stringToNat.insert string nat))
```
::::

:::comment
Because structures are represented by single-constructor inductive types, their constructors can be invoked or matched against using {tech}[anonymous constructor syntax].
Additionally, structures may be constructed or matched against using {deftech}_structure instance_ notation, which includes the names of the fields together with values for them.

:::

構造体は単一コンストラクタの帰納型として表現されるため、そのコンストラクタは {tech}[匿名コンストラクタ構文] を使用して呼び出したり、マッチしたりすることができます。さらに、構造体は {deftech}_構造体インスタンス_ （structure instance）の記法を用いて構築したり、マッチすることができます。構造体インスタンスの記法ではフィールド名とそれに紐づく値を含みます。

::::syntax term (title := "Structure Instances")

```grammar
{ $_,*
  $[: $ty:term]? }
```

:::comment
Constructs a value of a constructor type given values for named fields.
Field specifiers may take two forms:
:::

指定されたフィールドの値が与えられたコンストラクタの型の値を構築します。フィールド指定子には2つの形式があります：

```grammar (of := Lean.Parser.Term.structInstField)
$x := $y
```

```grammar (of := Lean.Parser.Term.structInstField)
$f:ident
```

:::comment
A {syntaxKind}`structInstLVal` is a field name (an identifier), a field index (a natural number), or a term in square brackets, followed by a sequence of zero or more subfields.
Subfields are either a field name or index preceded by a dot, or a term in square brackets.

:::

{syntaxKind}`structInstLVal` はフィールド名（識別子）・フィールドインデックス（自然数）・大括弧内の項のいずれかで、その後に0個以上のサブフィールドが続きます。サブフィールドはドットで始まるフィールド名・インデックス、もしくは大括弧で囲まれた項のどちらかです。

:::comment
This syntax is elaborated to applications of structure constructors.
The values provided for fields are by name, and they may be provided in any order.
The values provided for subfields are used to initialize fields of constructors of structures that are themselves found in fields.
Terms in square brackets are not allowed when constructing a structure; they are used in structure updates.

:::

この構文は、構造体コンストラクタの適用にエラボレートされます。フィールドに提供される値は名前であり、どのような順序で提供されても構いません。サブフィールドに指定された値は、それ自体がフィールドに含まれる構造体のコンストラクタのフィールドを初期化するために使用されます。大括弧内の項は構造体を構築する際には使用できません；これらは構造体の更新で用いられます。

:::comment
Field specifiers that do not contain `:=` are field abbreviations.
In this context, the identifier `f` is an abbreviation for `f := f`; that is, the value of `f` in the current scope is used to initialize the field `f`.

:::

`:=` を含まないフィールド指定子はフィールドの省略形です。この文脈においては、識別子 `f` は `f := f` の省略形です；つまり、現在のスコープにおける `f` の値がフィールド `f` の初期化に使われます。

:::comment
Every field that does not have a default value must be provided.
If a tactic is specified as the default argument, then it is run at elaboration time to construct the argument's value.

:::

デフォルト値を持たないすべてのフィールドには値を提供されなければなりません。デフォルトの引数としてタクティクが指定された場合、そのタクティクは引数の値を構築するためにエラボレーション時に実行されます。

:::comment
In a pattern context, field names are mapped to patterns that match the corresponding projection, and field abbreviations bind a pattern variable that is the field's name.
Default arguments are still present in patterns; if a pattern does not specify a value for a field with a default value, then the pattern only matches the default.

:::

パターンの文脈では、フィールド名は対応する射影にマッチするパターンにマップされ、フィールドの省略形はそのフィールド名を持つパターン変数を束縛します。デフォルト引数はパターンでも出現します；デフォルト値を持つフィールドに対してパターンが値を指定しない場合、パターンはデフォルト値のみにマッチします。

:::comment
The optional type annotation allows the structure type to be specified in contexts where it is not otherwise determined.
:::

オプションで型注釈することによって、構造体型が他に決定されないコンテキストにおいて構造体型を指定することを可能にします。

::::

:::::keepEnv

:::comment
::example "Patterns and default values"
:::
::::example "パターンとデフォルト値"
:::comment
The structure {name}`AugmentedIntList` contains a list together with some extra information, which is empty if omitted:
:::

構造体 {name}`AugmentedIntList` にはリストといくつかの追加情報がふくまれています。追加情報が省かれた時は空になります：

```lean
structure AugmentedIntList where
  list : List Int
  augmentation : String := ""
```

:::comment
When testing whether the list is empty, the function {name AugmentedIntList.isEmpty}`isEmpty` is also testing whether the {name AugmentedIntList.augmentation}`augmentation` field is empty, because the omitted field's default value is also used in pattern contexts:
:::

リストが空かどうかをテストするとき、関数 {name AugmentedIntList.isEmpty}`isEmpty` は {name AugmentedIntList.augmentation}`augmentation` フィールドが空かどうかもテストしています。これは省略されたフィールドのデフォルト値もパターンの文脈で使用されるからです：

```lean (name := isEmptyDefaults)
def AugmentedIntList.isEmpty : AugmentedIntList → Bool
  | {list := []} => true
  | _ => false

#eval {list := [], augmentation := "extra" : AugmentedIntList}.isEmpty
```
```leanOutput isEmptyDefaults
false
```
::::
:::::


::::syntax term
```grammar
{$e:term with
  $_,*
  $[: $ty:term]?}
```
:::comment
Updates a value of a constructor type.
The term that precedes the {keywordOf Lean.Parser.Term.structInst}`with` clause is expected to have a structure type; it is the value that is being updated.
A new instance of the structure is created in which every field not specified is copied from the value that is being updated, and the specified fields are replaced with their new values.
When updating a structure, array values may also be replaced by including the index to be updated in square brackets.
This updating does not require that the index expression be in bounds for the array, and out-of-bounds updates are discarded.
:::

コンストラクタの型の値を更新します。 {keywordOf Lean.Parser.Term.structInst}`with` 句の前にある項は構造体型を持つことが期待されます；これがこれから更新される値です。構造体の新しいインスタンスが作成され、指定されていないすべてのフィールドが更新される値からコピーされ、指定されたフィールドは新しい値に置き換えられます。構造体を更新する時、更新するインデックスを大括弧で囲むことで配列の値を置き換えることもできます。この更新では、インデックスの式が配列の範囲内にある必要はなく、範囲外の更新は破棄されます。

::::

:::comment
::example "Updating arrays"
:::
:::::example "配列の更新"
::::keepEnv
:::comment
Updating structures may use array indices as well as projection names.
Updates at indices that are out of bounds are ignored:

:::

構造体の更新には、射影名だけでなく、配列インデックスも指定できます。範囲外のインデックスでの更新は無視されます：

```lean name:=arrayUpdate
structure AugmentedIntArray where
  array : Array Int
  augmentation : String := ""
deriving Repr

def one : AugmentedIntArray := {array := #[1]}
def two : AugmentedIntArray := {one with array := #[1, 2]}
def two' : AugmentedIntArray := {two with array[0] := 2}
def two'' : AugmentedIntArray := {two with array[99] := 3}
#eval (one, two, two', two'')
```
```leanOutput arrayUpdate
({ array := #[1], augmentation := "" },
 { array := #[1, 2], augmentation := "" },
 { array := #[2, 2], augmentation := "" },
 { array := #[1, 2], augmentation := "" })
```
::::
:::::

:::comment
Values of structure types may also be declared using {keywordOf Lean.Parser.Command.declaration (parser:=declValEqns)}`where`, followed by definitions for each field.
This may only be used as part of a definition, not in an expression context.

:::

構造体型の値は、 {keywordOf Lean.Parser.Command.declaration (parser:=declValEqns)}`where` とそれに続く各フィールドの定義を使用して宣言することもできます。これは定義の一部としてのみ使用でき、式の文脈では使用できません。

:::comment
::example "`where` for structures"
:::
:::::example "構造体での `where`"
::::keepEnv
:::comment
The product type in Lean is a structure named {name}`Prod`.
Products can be defined using their projections:
:::

Lean の直積型は {name}`Prod` という構造体です。直積は射影を使って定義できます：

```lean
def location : Float × Float where
  fst := 22.807
  snd := -13.923
```
::::
:::::

:::comment
# Structure Inheritance
:::

# 構造体の継承（Structure Inheritance）

%%%
tag := "structure-inheritance"
%%%

:::comment
Structures may be declared as extending other structures using the optional {keywordOf Lean.Parser.Command.declaration (parser:=«structure»)}`extends` clause.
The resulting structure type has all of the fields of all of the parent structure types.
If the parent structure types have overlapping field names, then all overlapping field names must have the same type.
If the overlapping fields have different default values, then the default value from the last parent structure that includes the field is used.
New default values in the child structure take precedence over default values from the parent structures.

:::

構造体はオプションの {keywordOf Lean.Parser.Command.declaration (parser:=«structure»)}`extends` 句を使用することで複数の他の構造体を拡張することを宣言できます。結果として得られる構造体型は、すべての親構造体型のすべてのフィールドを持ちます。親構造体型が重複するフィールド名を持つ場合、重複するフィールド名はすべて同じ型を持たなければなりません。重複するフィールド名が異なるデフォルト値を持つ場合、そのフィールドを含む最後の親構造体のデフォルト値が使用されます。子構造体の新しいデフォルト値は、親構造体のデフォルト値よりも優先されます。

```lean (show := false) (keep := false)
-- If the overlapping fields have different default values, then the default value from the last parent structure that includes the field is used.
structure Q where
  x : Nat := 0
deriving Repr
structure Q' where
  x : Nat := 3
deriving Repr
structure Q'' extends Q, Q'
deriving Repr
structure Q''' extends Q', Q
deriving Repr

/-- info: 3 -/
#guard_msgs in
#eval ({} : Q'').x
/-- info: 0 -/
#guard_msgs in
#eval ({} : Q''').x
```

:::comment
When the new structure extends existing structures, the new structure's constructor takes the existing structure's information as additional arguments.
Typically, this is in the form of a constructor parameter for each parent structure type.
This parent value contains all of the parent's fields.
If the parents' fields overlap, however, then the subset of non-overlapping fields from one or more of the parents is included instead of an entire value of the parent structure to prevent duplicating field information.


:::

新しい構造体が既存の構造体を拡張する場合、新しい構造体のコンストラクタは既存の構造体の情報を追加引数として受け取ります。通常、これは親構造体の型ごとにコンストラクタのパラメータを指定する形になります。この親の値はすべての親のフィールドを含みます。しかし、親のフィールドが重複している場合は、フィールド情報の重複を防ぐために、親の構造体全体の値の代わりに、親の1つ以上のフィールドから重複していないフィールドのサブセットを含みます。

:::comment
There is no subtyping relation between a parent structure type and its children.
Even if structure `B` extends structure `A`, a function expecting an `A` will not accept a `B`.
However, conversion functions are generated that convert a structure into each of its parents.
These conversion functions are in the child structure's namespace, and their name is the parent structure's name preceded by `to`.

:::

親構造体とその子構造体の間には部分型の関係はありません。構造体 `B` が構造体 `A` を継承していても、`A` を期待する関数は `B` を受け付けません。しかし、構造体をそれぞれの親に変換する変換関数が生成されます。これらの変換関数は子構造体の名前空間に存在し、その名前は親構造体の名前の前に `to` が付いたものになります。

:::comment
:: example "Structure type inheritance with overlapping fields"
:::
:::: example "重複したフィールドを含む構造体型の継承"
:::comment
In this example, a {lean}`Textbook` is a {lean}`Book` that is also an {lean}`AcademicWork`:

:::

この例では、 {lean}`Textbook` は {lean}`Book` であり、 {lean}`AcademicWork` でもあります：

```lean
structure Book where
  title : String
  author : String

structure AcademicWork where
  author : String
  discipline : String

structure Textbook extends Book, AcademicWork

#check Textbook.toBook
```

:::comment
Because the field `author` occurs in both {lean}`Book` and {lean}`AcademicWork`, the constructor {name}`Textbook.mk` does not take both parents as arguments.
Its signature is:
:::

フィールド `author` は {lean}`Book` と {lean}`AcademicWork` の両方に存在するため、コンストラクタ {name}`Textbook.mk` は両方の親を引数に取りません。そのシグネチャは以下のようになります：

```signature
Textbook.mk (toBook : Book) (discipline : String) : Textbook
```

:::comment
The conversion functions are:
:::

変換関数は以下です：

```signature
Textbook.toBook (self : Textbook) : Book
```
```signature
Textbook.toAcademicWork (self : Textbook) : AcademicWork
```

:::comment
The latter combines the `author` field of the included {lean}`Book` with the unbundled `Discipline` field, and is equivalent to:
:::

後者は含まれる {lean}`Book` の `author` フィールドとバンドルされていない `discipline` フィールドを組み合わせたもので、次のものと等価です：

```lean
def toAcademicWork (self : Textbook) : AcademicWork :=
  let .mk book discipline := self
  let .mk _title author := book
  .mk author discipline
```
```lean (show := false)
-- check claim of equivalence
example : toAcademicWork = Textbook.toAcademicWork := by
  funext b
  cases b
  dsimp [toAcademicWork]
```

::::

:::comment
The resulting structure's projections can be used as if its fields are simply the union of the parents' fields.
The Lean elaborator automatically generates an appropriate projection when fields are used.
Likewise, the field-based initialization and structure update notations hide the details of the encoding of inheritance.
The encoding is, however, visible when using the constructor's name, when using {tech}[anonymous constructor syntax], or when referring to fields by their index rather than their name.

:::

結果として得られる構造体の射影はそのフィールドが単に親のフィールドの合併であるかのように使うことができます。Lean のエラボレータは射影に遭遇すると、自動的に適切な射影を生成します。同様に、フィールドベースの初期化と構造体の更新の記法は、継承のエンコーディングの詳細を隠します。しかし、このエンコーディングはコンストラクタの名前の使用時・ {tech}[匿名コンストラクタ構文] の使用時・名前ではなくインデックスでフィールドを参照する時には表示されます。

:::comment
:: example "Field Indices and Structure Inheritance"
:::
::::: example "フィールドのインデックスと構造体の継承"

```lean
structure Pair (α : Type u) where
  fst : α
  snd : α
deriving Repr

structure Triple (α : Type u) extends Pair α where
  thd : α
deriving Repr

def coords : Triple Nat := {fst := 17, snd := 2, thd := 95}
```

:::comment
Evaluating the first field index of {name}`coords` yields the underlying {name}`Pair`, rather than the contents of the field `fst`:
:::

{name}`coords` の最初のフィールドインデックスを評価すると、フィールド `fst` の内容ではなく、そのベースである {name}`Pair` が得られます：

```lean name:=coords1
#eval coords.1
```
```leanOutput coords1
{ fst := 17, snd := 2 }
```

:::comment
The elaborator translates {lean}`coords.fst` into {lean}`coords.toPair.fst`.

:::

エラボレータは {lean}`coords.fst` を {lean}`coords.toPair.fst` に変換します。

````lean (show := false) (keep := false)
example (t : Triple α) : t.fst = t.toPair.fst := rfl
````
:::::

:::comment
:: example "No structure subtyping"
:::
::::: example "構造体に部分型が無いこと"
::::keepEnv
:::comment
Given these definitions of even numbers, even prime numbers, and a concrete even prime:
:::

偶数・偶素数・具体的な偶数素数の定義が与えられている時：

```lean
structure EvenNumber where
  val : Nat
  isEven : 2 ∣ val := by decide

structure EvenPrime extends EvenNumber where
  notOne : val ≠ 1 := by decide
  isPrime : ∀ n, n ≤ val → n ∣ val  → n = 1 ∨ n = val

def two : EvenPrime where
  val := 2
  isPrime := by
    intros
    dsimp only at *
    repeat' (cases ‹Nat.le _ _›)
    all_goals omega

def printEven (num : EvenNumber) : IO Unit :=
  IO.print num.val
```
:::comment
it is a type error to apply {name}`printEven` directly to {name}`two`:
:::

{name}`printEven` を {name}`two` に直接適用すると型エラーになります：

```lean (error := true) (name := printTwo)
#check printEven two
```
```leanOutput printTwo
application type mismatch
  printEven two
argument
  two
has type
  EvenPrime : Type
but is expected to have type
  EvenNumber : Type
```
:::comment
because values of type {name}`EvenPrime` are not also values of type {name}`EvenNumber`.
:::

なぜなら {name}`EvenPrime` 型の値は {name}`EvenNumber` 型の値でもないからです。

::::
:::::


```lean (show := false) (keep := false)
structure A where
  x : Nat
  y : Int
structure A' where
  x : Int
structure B where
  foo : Nat
structure C extends A where
  z : String
/-- info: C.mk (toA : A) (z : String) : C -/
#guard_msgs in
#check C.mk

def someC : C where
  x := 1
  y := 2
  z := ""

/--
error: type mismatch
  someC
has type
  C : Type
but is expected to have type
  A : Type
-/
#guard_msgs in
#check (someC : A)

structure D extends A, B where
  z : String
/-- info: D.mk (toA : A) (toB : B) (z : String) : D -/
#guard_msgs in
#check D.mk
structure E extends A, B where
  x := 44
  z : String
/-- info: E.mk (toA : A) (toB : B) (z : String) : E -/
#guard_msgs in
#check E.mk
/--
error: parent field type mismatch, field 'x' from parent 'A'' has type
  Int : Type
but is expected to have type
  Nat : Type
-/
#guard_msgs in
structure F extends A, A' where



```
