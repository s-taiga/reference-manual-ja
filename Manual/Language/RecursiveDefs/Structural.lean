/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Language.RecursiveDefs.Structural.RecursorExample
import Manual.Language.RecursiveDefs.Structural.CourseOfValuesExample

import Manual.Meta


open Verso.Genre Manual
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

/-
#doc (Manual) "Structural Recursion" =>
-/
#doc (Manual) "構造的再帰（Structural Recursion）" =>
%%%
tag := "structural-recursion"
%%%

:::comment
Structurally recursive functions are those in which each recursive call is on a structurally smaller term than the argument.
Structural recursion is stronger than the primitive recursion that recursors provide, because the recursive call can use an _arbitrary_ sub-term of the argument, rather than only an immediate sub-term.
The constructions used to implement structural recursion are, however, implemented using the recursor; these helper constructions are described in the {ref "recursor-elaboration-helpers"}[section on inductive types].

:::

構造的再帰関数とは、各再帰呼び出しが引数よりも構造的に小さい項に対して行われる関数のことです。構造的再帰は、再帰子が提供する原始再帰よりも強力です。なぜなら、再帰呼び出しが引数の直前の部分項だけでなく、任意の部分項を使用できるからです。しかし、構造的再帰を実装するために使用される構成は再帰子を使用して実装されます；これらの補助構成は {ref "recursor-elaboration-helpers"}[帰納型の節] で説明されています。

{spliceContents Manual.Language.RecursiveDefs.Structural.RecursorExample}

:::comment
Recognizing structural recursion involves the following steps:
 1. The function's parameters are divided into a _fixed prefix_ of parameters that do not vary in any recursive calls, and ordinary parameters that do.
 2. The ordinary parameters are split into groups of parameters that, together, may constitute a structurally decreasing parameter. In this step, indices are grouped with the arguments whose types depend on them.


:::

構造的再帰を認識するには、次のようなステップがあります：
 1. 関数のパラメータは再帰呼び出しで変化しない _固定パラメータ_ と変化する通常のパラメータに分けられます。
 2. 通常のパラメータは、一緒になって構造的に減少する可能性のあるパラメータのグループに分割されます。このステップでは、添字はその型が依存する引数とともにグループ化されます。

:::comment
The structural recursion analysis attempts to translate the recursive pre-definition into a use of the appropriate structural recursion constructions.
At this step, pattern matching has already been translated into the use of matcher functions; these are treated specially by the termination checker.
Next, for each group of parameters, a translation using `brecOn` is attempted.

:::

構造的再帰分析は再帰的な事前定義を適切な構造的再帰の構成の利用に変換しようと試みます。このステップでは、パターンマッチはすでにマッチ関数の使用に変換されています；これらの関数は停止チェッカによって特別に扱われます。次に、各パラメータのグループに対して `brecOn` を使った変換が試みられます。

{spliceContents Manual.Language.RecursiveDefs.Structural.CourseOfValuesExample}

:::comment
The `below` construction is a mapping from each value of a type to the results of some function call on _all_ smaller values; it can be understood as a memoization table that already contains the results for all smaller values.
Recursors expect an argument for each of the inductive type's constructors; these arguments are called with the constructor's arguments (and the result of recursion on recursive parameters) during {tech}[ι-reduction].
The course-of-values recursion operator `brecOn`, on the other hand, expects just a single case that covers all constructors at once.
This case is provided with a value and a `below` table that contains the results of recursion on all values smaller than the given value; it should use the contents of the table to satisfy the motive for the provided value.
If the function is structurally recursive over a given parameter (or parameter group), then the results of all recursive calls will be present in this table already.

:::

`below` 構成は型の各値から _すべての_ 小さい値に対する関数呼び出しの結果へのマッピングです；これはすべての小さい値の結果をすでの格納したメモ化テーブルとして理解することができます。再帰子は帰納型のコンストラクタの各引数を期待します；これらの引数は {tech}[ι簡約] の間にコンストラクタの引数（および再帰パラメータに対する再帰の結果）とともに呼び出されます。一方、累積再帰の演算子 `brecOn` は一度にすべてのコンストラクタをカバーする単一のケースだけを期待します。このケースには値と、与えられた値よりも小さいすべての値に対する再帰の結果を含む `below` テーブルが提供されます；これは与えられた値に対する動機を満たすテーブルの内容を使用するべきです。関数が与えられたパラメータ（もしくはパラメータグループ）に対して構造的再帰である場合、すべての再帰呼び出しの結果はすでにこのテーブルに存在することになります。

:::comment
When the body of the recursive function is transformed into an invocation of `brecOn` on one of the function's parameters, the parameter and its course-of-values table are in scope.
The analysis traverses the body of the function, looking for recursive calls.
If the parameter is matched against, then its occurrences in the local context are {ref "match-generalization"}[generalized] and then instantiated with the pattern; this is also true for the type of the course-of-values table.
Typically, this pattern matching results in the type of the course-of-values table becoming more specific, which gives access to the recursive results for smaller values.
When an recursive occurrence of the function is detected, the course-of-values table is consulted to see whether it contains a result for the argument being checked.
If so, the recursive call can be replaced with a projection from the table.
If not, then the parameter in question doesn't support structural recursion.

:::

再帰関数の本体が関数のパラメータの1つに対する `brecOn` の呼び出しに変換されると、そのパラメータと値の累積テーブルがスコープに入ります。この解析は関数本体を走査し、再帰的な呼び出しを探します。パラメータがマッチした場合、ローカルコンテキストに出現するパラメータは {ref "match-generalization"}[一般化] され、そのパターンでインスタンス化されます；これは累積テーブルの型についても真です。通常、このパターンマッチの結果、累積テーブルの型はより具体的になり、より小さな値の再帰結果にアクセスできるようになります。関数の再帰的な出現が検出されると、累積テーブルが参照され、チェックされている引数の結果が含まれているかどうかが確認されます。もし含まれていれば、再帰呼び出しはテーブルからの射影で置き換えることができます。含まれていない場合は、当該パラメータは構造的再帰をサポートしていません。

```lean (show := false)
section
```

:::comment
::example "Elaboration Walkthrough"
:::
::::example "エラボレーションの一連の流れ"
:::comment
The first step in walking through the elaboration of {name}`half` is to manually desugar it to a simpler form.
This doesn't match the way Lean works, but its output is much easier to read when there are fewer {name}`OfNat` instances present.
This readable definition:
:::

{name}`half` のエラボレーションを進める最初のステップは、手作業でより単純な形に脱糖することです。これは Lean の動作方法とは一致しませんが、 {name}`OfNat` インスタンスの数が少なければその出力はずっと読みやすくなります。この読みやすい定義：

```lean (keep := false)
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
```
:::comment
can be rewritten to this somewhat lower-level version:
:::

は、以下のやや低レベルのバージョンに書き換えることができます：

```lean (keep := false)
def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```

:::comment
The elaborator begins by elaborating a pre-definition in which recursion is still present but the definition is otherwise in Lean's core type theory.
Turning on the compiler's tracing of pre-definitions, as well as making the pretty printer more explicit, makes the resulting pre-definition visible:
:::

エラボレータは、再帰はまだ存在するものの、それ以外は Lean のコア型理論に沿った事前定義をエラボレートすることから始めます。コンパイラの事前定義の追跡をオンにすると、プリティプリンタがより明示的になり、その結果事前定義が見えるようになります：

```lean (keep := false) (show := false)
-- Test of next block - visually check correspondence when updating!
set_option trace.Elab.definition.body true in
set_option pp.all true in

/--
info: [Elab.definition.body] half : Nat → Nat :=
    fun (x : Nat) =>
      half.match_1.{1} (fun (x : Nat) => Nat) x (fun (_ : Unit) => Nat.zero) (fun (_ : Unit) => Nat.zero)
        fun (n : Nat) => Nat.succ (half n)
-/
#guard_msgs in
def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```
```lean (name := tracedHalf)
set_option trace.Elab.definition.body true in
set_option pp.all true in

def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```
:::comment
The returned trace message is:{TODO}[Trace not showing up in serialized info - figure out why so this test can work better, or better yet, add proper trace rendering to Verso]
:::

返される追跡メッセージは以下です：

```
[Elab.definition.body] half : Nat → Nat :=
    fun (x : Nat) =>
      half.match_1.{1} (fun (x : Nat) => Nat) x
        (fun (_ : Unit) => Nat.zero)
        (fun (_ : Unit) => Nat.zero)
        fun (n : Nat) => Nat.succ (half n)
```
:::comment
The auxiliary match function's definition is:
:::

この補助マッチ関数の定義は以下です：

```lean (name := halfmatch)
#print half.match_1
```
```leanOutput halfmatch (whitespace := lax)
def half.match_1.{u_1} :
    (motive : Nat → Sort u_1) → (x : Nat) →
    (Unit → motive Nat.zero) → (Unit → motive 1) →
    ((n : Nat) → motive n.succ.succ) →
    motive x :=
  fun motive x h_1 h_2 h_3 =>
    Nat.casesOn x (h_1 ()) fun n =>
      Nat.casesOn n (h_2 ()) fun n =>
        h_3 n
```
:::comment
Formatted more readably, this definition is:
:::

より読みやすくフォーマットすると、この定義は以下のようになります：

```lean
def half.match_1'.{u} :
    (motive : Nat → Sort u) → (x : Nat) →
    (Unit → motive Nat.zero) → (Unit → motive 1) →
    ((n : Nat) → motive n.succ.succ) →
    motive x :=
  fun motive x h_1 h_2 h_3 =>
    Nat.casesOn x (h_1 ()) fun n =>
      Nat.casesOn n (h_2 ()) fun n =>
        h_3 n
```
:::comment
In other words, the specific configuration of patterns used in {name}`half` are captured in {name}`half.match_1`.

:::

つまり、 {name}`half` で使用されるパターンの特定の構成は {name}`half.match_1` に取り込まれます。

:::comment
This definition is a more readable version of {name}`half`'s pre-definition:
:::

以下の定義は {name}`half` の事前定義をより読みやすくしたものです：

```lean
def half' : Nat → Nat :=
  fun (x : Nat) =>
    half.match_1 (motive := fun _ => Nat) x
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
```

:::comment
To elaborate it as a structurally recursive function, the first step is to establish the `bRec` invocation.
The definition must be marked {keywordOf Lean.Parser.Command.declaration}`noncomputable` because Lean does not support code generation for recursors such as {name}`Nat.brecOn`.
:::

この関数を構造的再帰関数として定義するには、まず `bRec` の呼び出しを確立します。この定義は {keywordOf Lean.Parser.Command.declaration}`noncomputable` とマークしなければなりません。なぜなら Lean は {name}`Nat.brecOn` のような再帰子のためのコード生成をサポートしていないからです。

```lean (error := true) (keep := false)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      _
/- To translate:
    half.match_1 (motive := fun _ => Nat) x
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```

:::comment
The next step is to replace occurrences of `x` in the original function body with the `n` provided by {name Nat.brecOn}`brecOn`.
Because `table`'s type depends on `x`, it must also be generalized when splitting cases with {name}`half.match_1`, leading to a motive with an extra parameter.

:::

次のステップは、もとの関数本体にある `x` を {name Nat.brecOn}`brecOn` が提供する `n` で置き換えることです。`table` の型は `x` に依存するため、 {name}`half.match_1` でケースを分割する際にも一般化する必要があり、追加のパラメータを持つ同期となります。

```lean (error := true) (keep := false) (name := threeCases)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        _
        _
        _)
      table
/- To translate:
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```
:::comment
The three cases' placeholders expect the following types:
:::

3つのケースのプレースホルダは以下の型を期待します：

```leanOutput threeCases
don't know how to synthesize placeholder for argument 'h_1'
context:
x n : Nat
table : Nat.below n
⊢ Unit → (fun k => Nat.below k → Nat) Nat.zero
```

```leanOutput threeCases
don't know how to synthesize placeholder for argument 'h_2'
context:
x n : Nat
table : Nat.below n
⊢ Unit → (fun k => Nat.below k → Nat) 1
```

```leanOutput threeCases
don't know how to synthesize placeholder for argument 'h_3'
context:
x n : Nat
table : Nat.below n
⊢ (n : Nat) → (fun k => Nat.below k → Nat) n.succ.succ
```

:::comment
The first two cases in the pre-definition are constant functions, with no recursion to check:

:::

事前定義にある最初の2つのケースは定数関数で、チェックする再帰はありません：

```lean (error := true) (keep := false) (name := oneMore)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        (fun () _ => .zero)
        (fun () _ => .zero)
        _)
      table
/- To translate:
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```

:::comment
The final case contains a recursive call.
It should be translated into a lookup into the course-of-values table.
A more readable representation of the last hole's type is:
:::

最後のケースには再帰呼び出しが含まれています。これは累積テーブルへの検索に変換されるべきです。最後のホールの型をより読みやすく表現すると次のようになります：

```leanTerm
(n : Nat) →
Nat.below (motive := fun _ => Nat) n.succ.succ →
Nat
```
:::comment
which is equivalent to
:::

これは以下と同等です：

```leanTerm
(n : Nat) →
Nat ×' Nat ×' Nat.below (motive := fun _ => Nat) n →
Nat
```

```lean (show := false)
example : ((n : Nat) →
Nat.below (motive := fun _ => Nat) n.succ.succ →
Nat) = ((n : Nat) →
Nat ×' Nat ×' Nat.below (motive := fun _ => Nat) n →
Nat) := rfl
```

```lean (show := false)

variable {n : Nat}
```

:::comment
The first {lean}`Nat` in the course-of-values table is the result of recursion on {lean}`n + 1`, and the second is the result of recursion on {lean}`n`.
The recursive call can thus be replaced by a lookup, and the elaboration is successful:

:::

累積テーブルの最初の {lean}`Nat` は {lean}`n + 1` に対する再帰の結果であり、2番目は {lean}`n` に対する再帰の結果です。したがって、再帰呼び出しは検索に置き換えることができ、エラボレーションが成功します：

```lean (error := true) (keep := false) (name := oneMore)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        (fun () _ => .zero)
        (fun () _ => .zero)
        (fun _ table => Nat.succ table.2.1)
      table
```

:::comment
The actual elaborator keeps track of the relationship between the parameter being checked for structural recursion and the positions in the course-of-values tables by inserting sentinel types with fresh names into the motive.
:::

実際のエラボレータは新しい名前を持つ番兵型を動機に挿入することによって、構造的再帰のためにチェックされるパラメータと累積テーブル内での位置との間の関係を追跡します。

::::

```lean (show := false)
end
```

:::comment
For structural recursion to be detected, a parameter to the function must syntactically be a discriminant of a {keywordOf Lean.Parser.Term.match}`match`.
This maintains the connection between the discriminant and the function parameter, allowing the course-of-values table to line up with the subterms of the original argument.
This connection is checked syntactically: even simple transformations such as wrapping a discriminant and every pattern that matches it with {lean}`(·, ())` can cause elaboration to fail.
The generalization step that constructs a suitable motive for the auxiliary matchers searches for *exact occurrences of the discriminant* in the context.


:::

構造的再帰を検出するためには、関数のパラメータは {keywordOf Lean.Parser.Term.match}`match` の構文的に判別子でなければなりません。これにより、判別子と関数パラメータ間の接続が維持され、累積テーブルがもとの引数の部分項と並ぶようになります。この接続は構文的にチェックされます；判別子とそれにマッチするすえｂてのパターンを {lean}`(·, ())` でラップするような単純な変換でも、エラボレーションに失敗する可能性があります。補助マッチャーのための適切な動機を構築する一般化ステップでは、コンテキストの中で *判別子の正確な出現* を検索します。

```lean (show := false)
section
variable (n : Nat)
```

:::comment
::example "Failing Elaboration"
:::
::::example "エラボレーションの失敗"
:::comment
This definition of {lean}`half` terminates, but this can't be checked by either structural or well-founded recursion.
This is because the gratuitous tuple in the {tech}[match discriminant] breaks the connection between {lean}`n` and the patterns that match it.
:::

この {lean}`half` の定義は停止しますが、これは構造的再帰でも十分な根拠のある再帰でもチェックできません。これは、 {tech}[マッチ判別子] の中にある不必要なタプルが {lean}`n` とそれにマッチするパターンとの間のつながりを壊してしまうからです。

```lean (error := true) (name := badhalfmatch) (keep := false)
def half (n : Nat) : Nat :=
  match (n, ()) with
  | (0, ()) | (1, ()) => 0
  | (n' + 2, ()) => half n' + 1
```
```leanOutput badhalfmatch
fail to show termination for
  half
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    half n'


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n n' : Nat
⊢ n' < n
```

:::comment
The generalization step that constructs the motive for the auxiliary match functions doesn't connect {lean}`n` to its patterns, so the course-of-values table doesn't contain a suitable result of recursion.
Similarly, well-founded recursion lacks the connection between the function's parameter and the pattern, though this can be fixed by adding a proposition to the context that states their equality.
This extra information allows the proof automation for well-founded recursion to succeed.

:::

補助マッチ関数の動機を構築する一般化ステップでは、 {lean}`n` とそのパターンが接続されていないため、累積テーブルには適切な再帰の結果が含まれていません。同様に、整礎再帰は関数のパラメータとパターンとの間の接続を欠いていますが、これは等しいことを示す命題をコンテキストに追加することで修正できます。この追加情報により、整礎再帰の証明の自動化が成功します。

```lean
def half (n : Nat) : Nat :=
  match h : (n, ()) with
  | (0, ()) | (1, ()) => 0
  | (n' + 2, ()) =>
    -- Here, h : (n, ()) = (n' + 2, ())
    have : n = n' + 2 := by simp_all
    half n' + 1
```
::::


```lean (show := false)
end
```

:::comment
# Matching Pairs vs Simultaneous Matching
:::

# ペアのマッチと同時マッチ（Matching Pairs vs Simultaneous Matching）


:::comment
An important consequence of the strategies that are used to prove termination is that *simultaneous matching of two discriminants is not equivalent to matching a pair*.
Simultaneous matching maintains the connection between the discriminants and the patterns, allowing the pattern matching to refine the types of the assumptions in the local context as well as the expected type of the {keywordOf Lean.Parser.Term.match}`match`.
Essentially, the elaboration rules for {keywordOf Lean.Parser.Term.match}`match` treat the discriminants specially, and changing discriminants in a way that preserves the run-time meaning of a program does not necessarily preserve the compile-time meaning.

:::

停止を証明するために使用される戦略の重要な帰結は *2つの判別子の同時マッチはペアのマッチと等価ではない* ということです。同時マッチは判別子とパターンの間の接続を維持し、パターンマッチがローカルコンテキストの仮定の型と {keywordOf Lean.Parser.Term.match}`match` の期待される型を絞り込むことを可能にします。基本的に、 {keywordOf Lean.Parser.Term.match}`match` のエラボレーション規則は判別子を特別に扱い、プログラムの実行時の意味を保持する方法で判別子を変更してもコンパイル時の意味が保持されるとは限りません。

:::comment
::example "Simultaneous Matching vs Matching Pairs for Structural Recursion"
:::
::::example "構造的再帰に対しての同時マッチとペアのマッチ"
:::comment
This function that finds the minimum of two natural numbers is defined by structural recursion on its first parameter:
:::

2つの自然数の最小値を求めるこの関数は最初のパラメータに対しての構造的再帰によって定義されます：

```lean
def min (n k : Nat) : Nat :=
  match n, k with
  | 0, _ => 0
  | _, 0 => 0
  | n' + 1, k' + 1 => min n' k' + 1
termination_by structural n
```

:::comment
Replacing the simultaneous pattern match on both parameters with a match on a pair causes termination analysis to fail:
:::

両方のパラメータの同時パターンマッチをペアのマッチに置き換えると停止分析が失敗します：

```lean (error := true) (name := noMin)
def min' (n k : Nat) : Nat :=
  match (n, k) with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' n' k' + 1
termination_by structural n
```
```leanOutput noMin
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    min' n' k'
```

:::comment
This is because the analysis only considers direct pattern matching on parameters when matching recursive calls to strictly-smaller argument values.
Wrapping the discriminants in a pair breaks the connection.
:::

これは厳密により小さな引数値への再帰呼び出しをマッチさせる際に、分析がパラメータの直接的なパターンマッチしか考慮しないためです。判別子をペアで包むとそのつながりが断ち切られます。

::::

:::comment
::example "No Structural Recursion Over Pair Components"
:::
::::example "ペアの要素上では構造的再帰が無い"
:::comment
This function that finds the minimum of the two components of a pair can't be elaborated via structural recursion.
:::

ペアの2つの成分の最小値を求めるこの関数は構造的再帰によってエラボレートすることができません。

```lean
def min (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min (n', k') + 1
termination_by structural nk
```
:::comment
This is because the parameter's type's course-of-values recursor is used to justify the recursive definition, but the product type {name}`Prod` is not recursive and thus does not have a course-of-values recursor.
This definition is accepted using {tech}[well-founded recursion], however:
:::

これは、再帰定義を正当化するためにパラメータの型の累積再帰子が使用されますが、直積型 {name}`Prod` は再帰的ではなく、したがって累積再帰子を持たないためです。しかし、この定義は {tech}[well-founded recursion] を使用して受け入れられます：

```lean
def min (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min (n', k') + 1
termination_by mk
```
::::




# Mutual Structural Recursion

::: planned 56
This section will describe the specification of the translation to recursors.
:::
