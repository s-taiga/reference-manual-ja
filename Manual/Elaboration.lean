/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

import Manual.Meta
import Manual.Papers

open Verso.Genre Manual

set_option pp.rawOnError true

open Lean (Syntax SourceInfo)



/-
#doc (Manual) "Elaboration and Compilation" =>
-/
#doc (Manual) "エラボレーションとコンパイル（Elaboration and Compilation）" =>
%%%
htmlSplit := .never
%%%

:::comment
Roughly speaking, Lean's processing of a source file can be divided into the following stages:
:::

大まかに言うと、Lean のソースファイルに対する処理は以下のステージに分類されます：

:::comment
: Parsing

  The parser transforms sequences of characters into syntax trees of type {lean}`Syntax`.
  Lean's parser is extensible, so the {lean}`Syntax` type is very general.
:::

: パース

  パーサは文字のシーケンスを {lean}`Syntax` 型の構文木に変換します。Lean のパーサは拡張可能であるため、 {lean}`Syntax` 型は非常に一般的です。

:::comment
: Macro Expansion

  Macros are transformations that replace syntactic sugar with more basic syntax.
  Both the input and output of macro expansion have type {lean}`Syntax`.
:::

: マクロ展開

  マクロは構文糖衣をより基本的な構文に置き換える変換です。マクロ展開の入力と出力のどちらも {lean}`Syntax` 型を持ちます。

:::comment
: Elaboration

  {deftech key:="elaborator"}[Elaboration] is the process of transforming Lean's user-facing syntax into its core type theory.
  This core theory is much simpler, enabling the trusted kernel to be very small.
  Elaboration additionally produces metadata, such as proof states or the types of expressions, used for Lean's interactive features, storing them in a side table.
:::

: エラボレーション

  {deftech key:="エラボレータ"}[エラボレーション] （elaboration）とは、Lean のユーザ向けの構文をコア型理論に変換するプロセスです。このコア理論はよりシンプルであり、信頼されたカーネルを非常に小さくすることができます。エラボレーションはさらに、Lean の対話的機能に使用される証明状態や式の型などのメタデータを生成し、サイドテーブルに格納します。

:::comment
: Kernel Checking

  Lean's trusted kernel checks the output of the elaborator to ensure that it follows the rules of the type theory.
:::

: カーネルによるチェック

  Lean の信頼されたカーネルはエラボレータの出力が型理論の規則に従っているかどうかをチェックします。

:::comment
: Compilation

  The compiler transforms elaborated Lean code into executables that can be run.
:::

: コンパイル

  コンパイラはエラボレートされた Lean のコードを実行可能な実行ファイルへと変換します。

:::figure "The Lean Pipeline" (name := "pipeline-overview")
![The Lean Pipeline](/static/figures/pipeline-overview.svg)
:::


:::comment
In reality, the stages described above do not strictly occur one after the other.
Lean parses a single {tech}[command] (top-level declaration), elaborates it, and performs any necessary kernel checks.
Macro expansion is part of elaboration; before translating a piece of syntax, the elaborator first expands any macros present at the outermost layer.
Macro syntax may remain at deeper layers, but it will be expanded when the elaborator reaches those layers.
There are multiple kinds of elaboration: command elaboration implements the effects of each top-level command (e.g. declaring {tech}[inductive types], saving definitions, evaluating expressions), while term elaboration is responsible for constructing the terms that occur in many commands (e.g. types in signatures, the right-hand sides of definitions, or expressions to be evaluated).
Tactic execution is a specialization of term elaboration.
:::

実際には、上記の段階は厳密に次々と行われるわけではありません。Lean は1つの {tech}[コマンド] （command、トップレベルの宣言）をパースし、ついでエラボレートし、必要なカーネルのチェックを実行します。マクロ展開はエラボレーションの一部です；構文の一部を翻訳する前に、エラボレータはまず一番外側のレイヤに存在するマクロを展開します。マクロ構文はより深いレイヤに残っているかもしれませんが、その後でエラボレータがそれらのレイヤに到達した時に展開されます。エラボレーションには複数の種類が存在します：コマンドエラボレーションは各トップレベルのコマンドの作用（例えば {tech}[帰納型] の宣言・定義の保存・式の評価）を実装し、項エラボレーションは多くのコマンドで出現する項（例えばシグネチャ内の型・定義の右辺・評価される式）の構築を担当します。タクティクの実行は、項エラボレーションの特殊化です。

:::comment
When a command is elaborated, the state of Lean changes.
New definitions or types may have been saved for future use, the syntax may be extended, or the set of names that can be referred to without explicit qualification may have changed.
The next command is parsed and elaborated in this updated state, and itself updates the state for subsequent commands.
:::

あるコマンドがエラボレートされると、Lean の状態は変化します。新しい定義や型が将来の使用のために保存されたり、構文が拡張されたり、明示的な修飾なしに参照できる名前の集合が変更されるかもしれません。次のコマンドはこの更新された状態で解析され、エラボレートされます。

:::comment
# Parsing
:::

# パース（Parsing）
%%%
tag := "parser"
%%%

:::comment
Lean's parser is a recursive-descent parser that uses dynamic tables based on Pratt parsing{citep pratt73}[] to resolve operator precedence and associativity.
When grammars are unambiguous, the parser does not need to backtrack; in the case of ambiguous grammars, a memoization table similar to that used in Packrat parsing avoids exponential blowup.
Parsers are highly extensible: users may define new syntax in any command, and that syntax becomes available in the next command.
The open namespaces in the current {tech}[section scope] also influence which parsing rules are used, because parser extensions may be set to be active only when a given namespace is open.
:::

Lean のパーサは再帰下降パーサであり、Pratt パーサ {citep pratt73}[] に基づく動的テーブルを使用して、演算子の優先順位と結合性を解決します。文法が曖昧でない場合、パーサはバックトラックする必要がありません；曖昧な文法の場合、パックラットパースで使用されるものと同様のメモ化テーブルによって指数関数的な爆発を避けます。Lean のパーサは非常に拡張性が高いです：ユーザはどのコマンドでも新しい構文を定義でき、その構文は次のコマンドで使用できるようになります。現在の {tech}[section scope] で開いている名前空間も、どのパース規則を使用するかに影響します。なぜなら、パーサの拡張機能は指定した名前空間が開いているときにのみ有効になるように設定できるからです。

:::comment
When ambiguity is encountered, the longest matching parse is selected.
If there is no unique longest match, then both matching parses are saved in the syntax tree in a {deftech}[choice node] to be resolved later by the elaborator.
When the parser fails, it returns a {lean}`Syntax.missing` node, allowing for error recovery.
:::

曖昧な表現に遭遇した場合、最長一致のパースが選択されます。一意に最長一致が無い場合、一致するパースの両方が {deftech}[choice node] の構文木に保存され、後でエラボレータによって解決されます。パーサが失敗した場合、 {lean}`Syntax.missing` ノードを返し、エラーの回復を可能にします。

:::comment
When successful, the parser saves sufficient information to reconstruct the original source file.
Unsuccessful parses may miss some information for the regions of the file that cannot be parsed.
The {lean}`SourceInfo` record type records information about the origin of a piece of syntax, including its source location and the surrounding whitespace.
Based on the {lean}`SourceInfo` field, there are three relationships that {lean}`Syntax` can have to a source file:
 * {lean}`SourceInfo.original` indicates that the syntax value was produced directly by the parser.
 * {lean}`SourceInfo.synthetic` indicates that the syntax value was produced programmatically, e.g. by the macro expander. Synthetic syntax may nonetheless be marked _canonical_, in which case the Lean user interface treats it as if the user had written it. Synthetic syntax is annotated with positions in the original file, but does not include leading or trailing whitespace.
 * {lean}`SourceInfo.none` indicates no relationship to a file.
:::

成功した場合、パーサは元のソースファイルを再構築するのに十分な情報を保存します。成功しなかったパースは、パース出来なかったファイルの領域に関する情報を見逃す可能性があります。 {lean}`SourceInfo` レコード型はソースの位置と周囲の空白を含む、構文の一部分のソースに関する情報を記録します。 {lean}`SourceInfo` フィールドに基づいて、 {lean}`Syntax` がソースファイルに対して以下の3つの関係を持つことができます：
 * {lean}`SourceInfo.original` は、構文の値がパーサによって直接生成されたことを示します。
 * {lean}`SourceInfo.synthetic` は、構文の値がマクロ展開などによってプログラム的に生成されたことを示します。そうであるにも関わらず、統合的な構文は _標準_ （canonical）とマークされることがあります。これによって Lean のユーザインタフェースはこの構文をあたかもユーザが書いたかのように扱います。統合的な構文には元のファイル位置が注釈されますが、先頭や末尾の空白は含まれません。
 * {lean}`SourceInfo.none` は、ファイルとの関係がないことを示します。

:::comment
The parser maintains a token table that tracks the reserved words that are currently part of the language.
Defining new syntax or opening namespaces can cause a formerly-valid identifier to become a keyword.
:::

パーサは、現在において言語の一部となっている予約語を追跡する字句テーブルを保持します。新しい構文を定義したり、名前空間を開いたりすると、以前は有効だった識別子がキーワードになることがあります。

:::comment
Each production in Lean's grammar is named.
The name of a production is called its {deftech}_kind_.
These syntax kinds are important, because they are the key used to look up the interpretation of the syntax in the elaborator's tables.
:::

Lean の文法では、各生成物に名前が付けられています。この生成物の名前は {deftech}_種_ （kind）と呼ばれています。これらの構文の種は重要です。なぜならエラボレータのテーブルで構文の解釈を検索するために使用されるキーだからです。

:::comment
Syntax extensions are described in more detail in {ref "language-extension"}[a dedicated chapter].
:::

構文拡張については {ref "language-extension"}[専用の章] で詳しく説明されています。

:::comment
# Macro Expansion and Elaboration
:::

# マクロ展開とエラボレーション（Macro Expansion and Elaboration）
%%%
tag := "macro-and-elab"
%%%

:::comment
Having parsed a command, the next step is to elaborate it.
The precise meaning of _elaboration_ depends on what is being elaborated: elaborating a command effects a change in the state of Lean, while elaborating a term results in a term in Lean's core type theory.
Elaboration of both commands and terms may be recursive, both because of command combinators such as {keywordOf Lean.Parser.Command.in}`in` and because terms may contain other terms.
:::

コマンドをパースした後、次のステップはそれをエラボレートすることです。 _エラボレーション_ （elaboration）の正確な意味は何をエラボレートするかによって異なります：コマンドのエラボレートは Lean の状態変化に作用し、項のエラボレートによって Lean のコア型理論の項が生成されます。コマンドと項エラボレーションのどちらも再帰的となり得ます。これはどちらも {keywordOf Lean.Parser.Command.in}`in` のようなコマンドコンビネータや、項が他の項を含むことがあるためです。

:::comment
Command and term elaboration have different capabilities.
Command elaboration may have side effects on an environment, and it has access to run arbitrary computations in {lean}`IO`.
Lean environments contain the usual mapping from names to definitions along with additional data defined in {deftech}[environment extensions], which are additional tables associated with an environment; environment extensions are used to track most other information about Lean code, including {tactic}`simp` lemmas, custom pretty printers, and internals such as the compiler's intermediate representations.
Command elaboration also maintains a message log with the contents of the compiler's informational output, warnings, and errors, a set of {tech}[info trees] that associate metadata with the original syntax (used for interactive features such as displaying proof states, identifier completion, and showing documentation), accumulated debugging traces, the open {tech}[section scopes], and some internal state related to macro expansion.
Term elaboration may modify all of these fields except the open scopes.
Additionally, it has access to all the machinery needed to create fully-explicit terms in the core language from Lean's terse, friendly syntax, including unification, type class instance synthesis, and type checking.
:::

コマンドエラボレーションと項エラボレーションは異なる能力を持ちます。コマンドエラボレーションは環境に副作用を与える可能性があり、 {lean}`IO` で任意の計算を実行するアクセス権を持っています。Lean の環境は名前から定義への通常のマッピングに加え、 {deftech}[環境拡張] （environment extension）で定義される追加データを含んでいます；環境拡張は {tactic}`simp` 補題・カスタムのプリティプリンタ・コンパイラの中間表現などの内部を含む、Lean コードに関する他のほとんどの情報を追跡するために使用されます。コマンドエラボレーションはまた、コンパイラの情報出力・警告・およびエラー内容を含むメッセージログ・メタデータをもとの構文に関連付ける {tech}[情報木] のセット（証明状態の表示・識別子の補完・ドキュメントの表示などの対話的な機能に使用されます）・蓄積されたデバッグトレース・開いた {tech}[section scope] ・マクロ展開に関連するいくつかの内部状態を維持します。項エラボレーションは開いたスコープを除くこれらすべてのフィールドを変更することができます。さらに、Lean の簡潔で親しみやすい構文からコア言語で完全に明示的な項を作成するために必要な単一化・型クラスインスタンス合成・型チェックを含むすべての機構にアクセスすることができます。

:::comment
The first step in both term and command elaboration is macro expansion.
There is a table that maps syntax kinds to macro implementations; macro implementations are monadic functions that transform the macro syntax into new syntax.
Macros are saved in the same table and execute in the same monad for terms, commands, tactics, and any other macro-extensible part of Lean.
If the syntax returned by the macro is itself a macro, then that syntax is again expanded—this process is repeated until either a syntax whose kind is not a macro is produced, or until a maximum number of iterations is reached, at which point Lean produces an error.
Typical macros process some outer layer of their syntax, leaving some subterms untouched.
This means that even when macro expansion has been completed, there still may be macro invocations remaining in the syntax below the top level.
New macros may be added to the macro table.
Defining new macros is described in detail in {ref "macros"}[the section on macros].
:::

項とコマンドエラボレーションのどちらも最初のステップはマクロ展開です。構文の種とマクロの実装を対応付けるテーブルが存在し、マクロの実装はマクロ構文を新しい構文に変換するモナド関数です。マクロは同じテーブルに保存され、項・コマンド・タクティク・および Lean のその他のマクロ拡張可能な部分に対して同じモナドで実行されます。マクロによって拡張された構文それ自体がマクロである場合、その構文は再び拡張されます。このプロセスはマクロではない構文がせいせいされるか、最大反復回数に達するまで繰り返されます。最大反復回数に到達した場合、Lean はエラーを出力します。一般的なマクロは構文の外側のレイヤを処理し、いくつかの部分項はそのままにします。つまり、マクロ展開が完了しても、トップレベル以下の構文にはマクロ呼び出しが残っている可能性があります。新しいマクロをマクロテーブルに追加することができます。新しいマクロの定義については {ref "macros"}[マクロの節] で詳しく説明されます。

:::comment
After macro expansion, both the term and command elaborators consult tables that map syntax kinds to elaboration procedures.
Term elaborators map syntax and an optional expected type to a core language expression using the very powerful monad mentioned above.
Command elaborators accept syntax and return no value, but may have monadic side effects on the global command state.
While both term and command elaborators have access to {lean}`IO`, it's unusual that they perform side effects; exceptions include interactions with external tools or solvers.
:::

マクロ展開の後、項とコマンドエラボレータのどちらも、構文の種をエラボレータの手続きにマップするテーブルを参照します。項エラボレータは、構文とオプションで期待される型を、前述の非常に強力なモナドを使用するコア言語の式にマッピングします。コマンドエラボレータは構文を受け入れ、値を返しませんが、グローバルのコマンド状態に対してモナドの副作用を持つかもしれません。項とコマンドエラボレータのどちらも {lean}`IO` にアクセスできますが、副作用を実行するのは一般的ではありません；例外は外部ツールやソルバとのやり取りを含みます。

:::comment
The elaborator tables may be extended to enable the use of new syntax for both terms and commands by extending the tables.
See {ref "elaborators"}[the section on elaborators] for a description of how to add additional elaborators to Lean.
When commands or terms contain further commands or terms, they recursively invoke the appropriate elaborator on the nested syntax.
This elaborator will then expand macros before invoking elaborators from the table.
While macro expansion occurs prior to elaboration for a given “layer” of the syntax, macro expansion and elaboration are interleaved in general.
:::

エラボレータのテーブルは、項とコマンドの両方に新しい構文を使用することができるように拡張することができます。Lean にエラボレータを追加する方法については {ref "elaborators"}[エラボレータの節] を参照してください。コマンドや項がさらなるコマンドや項を含む場合、ネストされた構文に対して適切なエラボレータを再帰的に呼び出します。このエラボレータはテーブルからエラボレータを呼び出す前にマクロを展開します。マクロ展開は構文の与えられた「レイヤ」のエラボレーションの前に行われますが、マクロ展開とエラボレーションは一般的に交互に実行されます。

:::comment
## Info Trees
:::

## 情報木（Info Trees）

:::comment
When interacting with Lean code, much more information is needed than when simply importing it as a dependency.
For example, Lean's interactive environment can be used to view the types of selected expressions, to step through all the intermediate states of a proof, to view documentation, and highlight all occurrences of a bound variable.
The information necessary to use Lean interactively is stored in a side table called the  {deftech}_info trees_ during elaboration.
:::

Lean のコードと対話する場合、単に依存関係としてインポートする場合よりもはるかに多くの情報が必要になります。例えば、Lean の対話型環境は、選択した式の型を表示したり、証明のすべての中間状態をステップごとに眺めていったり、ドキュメントを表示したり、束縛変数のすべての出現をハイライトしたりするために使用できます。Lean を対話的に使用するために必要な情報はエラボレーション中において {deftech}_情報木_ （info tree）と呼ばれるサイドテーブルに格納されます。

````lean (show := false)
open Lean.Elab (Info)
deriving instance TypeName for Unit
````


:::comment
Info trees relate metadata to the user's original syntax.
Their tree structure corresponds closely to the tree structure of the syntax, although a given node in the syntax tree may have many corresponding info tree nodes that document different aspects of it.
This metadata includes the elaborator's output in Lean's core language, the proof state active at a given point, suggestions for interactive identifier completion, and much more.
The metadata can also be arbitrarily extended; the constructor {lean}`Info.ofCustomInfo` accepts a {lean}`Dynamic` type.
This can be used to add information to be used by custom code actions or other user interface extensions.
:::

情報木はユーザのオリジナルの構文にメタデータを関連付けます。その木構造は構文の木構造に密接に対応していますが、構文木のあるノードにはそれについて異なる側面を文書化する多くの対応する情報木があるかもしれません。このメタデータには、Lean のコア言語におけるエラボレータの出力・ある時点でアクティブな証明状態・対話的な識別子補完のための提案等その他多くのものが含まれます。またこのメタデータは任意に拡張可能です；コンストラクタ {lean}`Info.ofCustomInfo` は {lean}`Dynamic` 型を受け付けます。これを使用して、カスタムコードアクションやその他のユーザインタフェース拡張で使用する情報を追加することができます。

:::comment
# The Kernel
:::

# カーネル（The Kernel）

:::comment
Lean's trusted {deftech}_kernel_ is a small, robust implementation of a type checker for the core type theory.
It does not include a syntactic termination checker, nor does it perform unification; termination is guaranteed by elaborating all recursive functions into uses of primitive {tech}[recursors], and unification is expected to have already been carried out by the elaborator.
Before new inductive types or definitions are added to the environment by the command or term elaborators, they must be checked by the kernel to guard against potential bugs in elaboration.
:::

Lean が信頼する {deftech}_カーネル_ （kernel）はコア型理論のための型チェッカの小さく堅牢な実装です。カーネルには構文的停止チェッカは含まれず、単一化も行いません；停止性はすべての再帰関数をプリミティブ {tech}[再帰子] の使用にエラボレートすることで保証され、単一化はエラボレータによってすでに実行されていることが期待されます。コマンドと項エラボレータによって新しい帰納型や定義が環境に追加される前に、エラボレータによって潜在的なバグを防ぐために、それらはカーネルによってチェックされなければなりません。

:::comment
Lean's kernel is written in C++.
There are independent re-implementations in [Rust](https://github.com/ammkrn/nanoda_lib) and [Lean](https://github.com/digama0/lean4lean), and the Lean project is interested in having as many implementations as possible so that they can be cross-checked against each other.
:::

Lean のカーネルは C++ で書かれています。また独立した再実装として [Rust](https://github.com/ammkrn/nanoda_lib) と [Lean](https://github.com/digama0/lean4lean) によるものもあり、Lean プロジェクトは可能な限り多くの実装を用意して、互いにクロスチェックできるようにすることを望んでいます。

:::comment
The language implemented by the kernel is a version of the Calculus of Constructions, a dependent type theory with the following features:
 * Full dependent types
 * Inductively-defined types that may be mutually inductive or include recursion nested under other inductive types
 * An {tech}[impredicative], definitionally proof-irrelevant, extensional {tech}[universe] of {tech}[propositions]
 * A {tech}[predicative], non-cumulative hierarchy of universes of data
 * {ref "quotients"}[Quotient types] with a definitional computation rule
 * Propositional function extensionality{margin}[Function extensionality is a theorem that can be proved using quotient types, but it is such an important consequence that it's worth listing separately.]
 * Definitional η-equality for functions and products
 * Universe-polymorphic definitions
 * Consistency: there is no axiom-free closed term of type {lean}`False`
:::

カーネルが実装する言語は Calculus of Constructions の一種で、以下の特徴を持つ依存型理論です：
+ 完全な依存型
+ 相互に帰納的であったり、他の帰納型の下で入れ子になった再帰を含んだりする帰納的に定義されたデータ型
+ {tech}[impredicative] ・定義上証明と irrelevant な {tech}[命題] の拡張的 {tech}[宇宙]
+ {tech}[predicative] なデータの宇宙の非蓄積な階層
* 定義上の計算規則を伴った {ref "quotients"}[商型] （Quotient type）
+ 命題上の関数外延性 {margin}[関数外延性は商型を使って証明できる定理ですが、重要な帰結であるため別で挙げておきます。]
+ 関数と積についての定義上のη等価性
+ 宇宙多相定義
+ 一貫性： {lean}`False` 型の公理にとらわれない閉項は存在しません

```lean (show := false) (keep := false)
-- Test definitional eta for structures
structure A where
  x : Nat
  y : Int
example (a : A) : ⟨a.x, a.y⟩ = a := rfl
inductive B where
  | mk (x : Nat) (y : Int) : B
example (b : B) : ⟨b.1, b.2⟩ = b := rfl
/--
error: type mismatch
  rfl
has type
  ?m.713 = ?m.713 : Prop
but is expected to have type
  e1 = e2 : Prop
-/
#guard_msgs in
example (e1 e2 : Empty) : e1 = e2 := rfl
```

:::comment
This theory is rich enough to express leading-edge research mathematics, and yet simple enough to admit a small, efficient implementation.
The presence of explicit proof terms makes it feasible to implement independent proof checkers, increasing our confidence.
It is described in detail by {citet carneiro19}[] and {citet ullrich23}[].
:::

この理論は最先端の研究数学を表現するのに十分豊かでありながら、小規模で効率的な実装が可能なほどシンプルです。明示的な証明項が存在することで、独立した証明チェッカを実装することが可能であり、信頼性が高まります。詳しくは {citet carneiro19}[] と {citet ullrich23}[] で説明されています。

:::comment
Lean's type theory does not feature subject reduction, the definitional equality is not necessarily transitive, and it is possible to make the type checker fail to terminate.
None of these metatheoretic properties cause problems in practice—failures of transitivity are exceedingly rare, and as far as we know, non-termination has not occurred except when crafting code specifically to exercise it.
Most importantly, logical soundness is not affected.
In practice, apparent non-termination is indistinguishable from sufficiently slow programs; the latter are the causes observed in the wild.
These metatheoretic properties are a result of having impredicativity, quotient types that compute, definitional proof irrelevance, and propositional extensionality; these features are immensely valuable both to support ordinary mathematical practice and to enable automation.
:::

Lean の型理論には subject reduction の機能はなく、定義上の等価性は必ずしも推移的ではなく、型チェッカが停止しないようにすることも可能です。これらのメタ理論的な特性はいずれも実際には問題になりません。推移性が失敗するのは非常にまれであり、知る限りではそれを行使するために特別にコードを作成した場合を除き非停止は発生していません。最も重要なことは、論理的健全性に影響がないことです。実際には、見かけ上の非停止は十分に遅いプログラムと区別がつきません。これらのメタ理論的特性は、impredicativity・計算する商型・定義上の証明の irrelevance・命題上の外延性からの帰結です；これらの機能は、通常の数学的実践をサポートする上でも、自動化を可能にするうえでも非常に価値があります。

:::comment
# Elaboration Results
:::

# エラボレーションの結果（Elaboration Results）
%%%
tag := "elaboration-results"
%%%

:::comment
Lean's core type theory does not include pattern matching or recursive definitions.
Instead, it provides low-level {tech}[recursors] that can be used to implement both case distinction and primitive recursion.
Thus, the elaborator must translate definitions that use pattern matching and recursion into definitions that use recursors.{margin}[More details on the elaboration of recursive definitions is available in the {ref "recursive-definitions"}[dedicated section] on the topic.]
This translation is additionally a proof that the function terminates for all potential arguments, because all functions that can be translated to recursors also terminate.
:::

Lean のコア型理論には、パターンマッチや再帰定義は含まれていません。その代わりに、場合分けと原始再帰の両方を実装するために使用できる低レベルの {tech}[再帰子] を提供します。したがって、エラボレータはパターンマッチと再帰を使用する定義から再帰子を使用する定義に変換する必要があります。この変換はさらに、関数がすべての潜在的な引数に対して停止することの証明でもあります。なぜなら再帰子へ翻訳されるすべての関数は停止するからです。

:::comment
The translation to recursors happens in two phases: during term elaboration, uses of pattern matching are replaced by appeals to {deftech}_auxiliary matching functions_ that implement the particular case distinction that occurs in the code.
These auxiliary functions are themselves defined using recursors, though they do not make use of the recursors' ability to actually implement recursive behavior.{margin}[They use the `casesOn` construction that is described in the {ref "recursor-elaboration-helpers"}[section on recursors and elaboration].]
The term elaborator thus returns core-language terms in which pattern matching has been replaced with the use of special functions that implement case distinction, but these terms may still contain recursive occurrences of the function being defined.
To see auxiliary pattern matching functions in Lean's output, set the option {option}`pp.match` to {lean}`false`.
:::

再帰子への翻訳には2つのフェーズが発生します：項エラボレーションの間、パターンマッチの使用はコード中で発生する特定の場合分けを実装する {deftech}_補助マッチ関数_ （auxiliary matching function）の出現に置き換えられます。これらの補助関数はそれ自体が再帰子を使用して定義されますが、再帰子が実際に再帰的な動作を実装する機能は使用しません。 {margin}[再帰子は {ref "recursor-elaboration-helpers"}[再帰子とエラボレーションの節] で記述する `casesOn` 構成を使います。] このように、項エラボレータはパターンマッチが場合分けを実装する特別な関数の使用に置き換えられたコア言語による項を返しますが、これらの項には定義されている関数の再帰的な出現が含まれる可能性があります。Lean の出力に補助的なパターンマッチ関数を表示するには、オプション {option}`pp.match` を {lean}`false` に設定します。

{optionDocs pp.match}


```lean (show := false) (keep := false)
def third_of_five : List α → Option α
  | [_, _, x, _, _] => some x
  | _ => none
set_option pp.match false
/--
info: third_of_five.eq_def.{u_1} {α : Type u_1} (x✝ : List α) :
  third_of_five x✝ = third_of_five.match_1 (fun x => Option α) x✝ (fun head head x head head => some x) fun x => none
-/
#guard_msgs in
#check third_of_five.eq_def
/--
info: def third_of_five.match_1.{u_1, u_2} : {α : Type u_1} →
  (motive : List α → Sort u_2) →
    (x : List α) →
      ((head head_1 x head_2 head_3 : α) → motive [head, head_1, x, head_2, head_3]) →
        ((x : List α) → motive x) → motive x :=
fun {α} motive x h_1 h_2 =>
  List.casesOn x (h_2 []) fun head tail =>
    List.casesOn tail (h_2 [head]) fun head_1 tail =>
      List.casesOn tail (h_2 [head, head_1]) fun head_2 tail =>
        List.casesOn tail (h_2 [head, head_1, head_2]) fun head_3 tail =>
          List.casesOn tail (h_2 [head, head_1, head_2, head_3]) fun head_4 tail =>
            List.casesOn tail (h_1 head head_1 head_2 head_3 head_4) fun head_5 tail =>
              h_2 (head :: head_1 :: head_2 :: head_3 :: head_4 :: head_5 :: tail)
-/
#guard_msgs in
#print third_of_five.match_1
```

:::comment
The elaborated definition is then sent to the compiler and to the kernel.
The compiler receives the version in which recursion is still present, while the version sent to the kernel undergoes a second transformation that replaces explicit recursion with uses of recursors.
This split is for three reasons:
 * The compiler can compile {ref "partial-unsafe"}[`partial` functions] that the kernel treats as opaque constants for the purposes of reasoning.
 * The compiler can also compile {ref "partial-unsafe"}[`unsafe` functions] that bypass the kernel entirely.
 * Translation to recursors does not necessarily preserve the cost model expected by programmers, in particular laziness vs strictness, but compiled code must have predictable performance.

The compiler stores an intermediate representation in an environment extension.
:::

こうしてエラボレートされた定義はコンパイラとカーネルに送られます。コンパイラは再帰が残っているバージョンを受け取りますが、カーネルに送られたバージョンは、明示的な再帰を再帰子の使用に置き換える2つ目の変換を受けます。この区別には3つの理由があります：
 * コンパイラは {ref "partial-unsafe"}[`partial` 関数] をコンパイルすることができますが、カーネルは推論のためにこれを不透明な定数として扱います。
 * コンパイラは {ref "partial-unsafe"}[`unsafe` 関数] もコンパイルすることができますが、これはカーネルでは完全に無視されます。
 * 再帰子への翻訳は、特に遅延か正格についてプログラマに期待されたコストモデルを保存する必要はありません。しかし、コンパイルされたコードは予測可能な性能を持たなければなりません。
コンパイラは中間表現を環境拡張に保存します。

:::comment
For straightforwardly structurally recursive functions, the translation will use the type's recursor.
These functions tend to be relatively efficient when run in the kernel, their defining equations hold definitionally, and they are easy to understand.
Functions that use other patterns of recursion that cannot be captured by the type's recursor are translated using {deftech}[well-founded recursion], which is structural recursion on a proof that some {deftech}_measure_ decreases at each recursive call.
Lean can automatically derive many of these cases, but some require manual proofs.
Well-founded recursion is more flexible, but the resulting functions are often slower to execute in the kernel due to the proof terms that show that a measure decreases, and their defining equations may hold only propositionally.
To provide a uniform interface to functions defined via structural and well-founded recursion and to check its own correctness, the elaborator proves equational lemmas that relate the function to its original definition.
In the function's namespace, `eq_unfold` relates the function directly to its definition, `eq_def` relates it to the definition after instantiating implicit parameters, and $`N` lemmas `eq_N` relate each case of its pattern-matching to the corresponding right-hand side, including sufficient assumptions to indicate that earlier branches were not taken.
:::

構造的に単純な再帰関数の場合、その翻訳は型の再帰子を使用します。このような関数はカーネルで実行すると比較的効率的である傾向があり、定義された等式が定義上成立し、理解も容易です。型の再帰子で捕捉できないその他のパターンの再帰を使用する関数は {deftech}[整礎再帰] （well-founded recursion）を使用して翻訳されます。これは各再帰呼び出しのたびに何かしらの基準が減少することの証明のもとの構造的な再帰です。Lean はこれらのケースの多くを自動的に導出できますが、手作業での証明が必要なものもあります。整礎再帰はより柔軟なものですが、基準が減少することを示す証明項が定義する等式が成立するのは命題上だけであるため、結果として得られる関数はカーネルでの実行速度が遅くなることが多いです。構造的で整礎な再帰によって定義された関数に統一されたインタフェースを提供し、それ自身の正しさをチェックするために、エラボレータは関数をもとの定義に関連付ける等式の補題を証明します。関数の名前空間において、`eq_unfold` は関数を直接定義に関連付け、`eq_def` は暗黙のパラメータをインスタンス化した後の定義に関連付け、 $`N` 個の補題 `eq_N` はパターンマッチの各ケースと対応する右辺を関連付けます。これにはそれより前の分岐が取られないことの十分な仮定を含みます。

:::::keepEnv
:::comment
::example "Equational Lemmas"
:::
::::example "等式の補題"
:::comment
Given the definition of {lean}`thirdOfFive`:
:::

定義 {lean}`thirdOfFive` に対して：

```lean
def thirdOfFive : List α → Option α
  | [_, _, x, _, _] => some x
  | _ => none
```
:::comment
equational lemmas are generated that relate {lean}`thirdOfFive` to its definition.
:::

{lean}`thirdOfFive` をその定義に関連付ける等式の補題が生成されます。

:::comment
{lean}`thirdOfFive.eq_unfold` states that it can be unfolded to its original definition when no arguments are provided:
:::

{lean}`thirdOfFive.eq_unfold` は引数が与えられていないもとの定義に展開できることを示します：

```signature
thirdOfFive.eq_unfold.{u_1} :
  @thirdOfFive.{u_1} = fun {α : Type u_1} x =>
    match x with
    | [head, head_1, x, head_2, head_3] => some x
    | x => none
```

:::comment
{lean}`thirdOfFive.eq_def` states that it matches its definition when applied to arguments:
:::

{lean}`thirdOfFive.eq_def` は引数に適用されたときにその定義を一致することを示します：

```signature
thirdOfFive.eq_def.{u_1} {α : Type u_1} :
  ∀ (x : List α),
    thirdOfFive x =
      match x with
      | [head, head_1, x, head_2, head_3] => some x
      | x => none
```

:::comment
{lean}`thirdOfFive.eq_1` shows that its first defining equation holds:
:::

{lean}`thirdOfFive.eq_1` はその最初の定義された等式が成り立つことを示しています：

```signature
thirdOfFive.eq_1.{u} {α : Type u}
    (head head_1 x head_2 head_3 : α) :
  thirdOfFive [head, head_1, x, head_2, head_3] = some x
```

:::comment
{lean}`thirdOfFive.eq_2` shows that its second defining equation holds:
:::

{lean}`thirdOfFive.eq_2` は二番目に定義された等式が成り立つことを示しています：

```signature
thirdOfFive.eq_2.{u_1} {α : Type u_1} :
  ∀ (x : List α),
    (∀ (head head_1 x_1 head_2 head_3 : α),
      x = [head, head_1, x_1, head_2, head_3] → False) →
    thirdOfFive x = none
```
:::comment
The final lemma {lean}`thirdOfFive.eq_2` includes a premise that the first branch could not have matched (that is, that the list does not have exactly five elements).
:::

最後の補題 {lean}`thirdOfFive.eq_2` は最初の分岐がマッチしなかった（つまりリストがちょうど5つの要素を持たない）という前提を含んでいます。

::::
:::::

:::::keepEnv
:::comment
::example "Recursive Equational Lemmas"
:::
::::example "再帰的な等式の補題"
:::comment
Given the definition of {lean}`everyOther`:
:::

定義 {lean}`everyOther` に対して：

```lean
def everyOther : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: everyOther xs
```

:::comment
equational lemmas are generated that relate {lean}`everyOther`'s recursor-based implementation to its original recursive definition.
:::

{lean}`everyOther`' の再帰子ベースの実装をもとの再帰定義に関連付ける等式の補題が生成されます。

:::comment
{lean}`everyOther.eq_unfold` states that `everyOther` with no arguments is equal to its unfolding:
:::

{lean}`everyOther.eq_unfold` は引数の無い `everyOther` がその展開と等しいことを示します：

```signature
everyOther.eq_unfold.{u} :
  @everyOther.{u} = fun {α} x =>
    match x with
    | [] => []
    | [x] => [x]
    | x :: _ :: xs => x :: everyOther xs
```

:::comment
{lean}`everyOther.eq_def` states that a `everyOther` is equal to its definition when applied to arguments:
:::

{lean}`everyOther.eq_def` は `everyOther` が引数に適用されたとき、その定義と等しいことを示します：

```signature
everyOther.eq_def.{u} {α : Type u} :
  ∀ (x : List α),
    everyOther x =
      match x with
      | [] => []
      | [x] => [x]
      | x :: _ :: xs => x :: everyOther xs
```

:::comment
{lean}`everyOther.eq_1` demonstrates its first pattern:
:::

{lean}`everyOther.eq_1` はその最初のパターンを説明します：

```signature
everyOther.eq_1.{u} {α : Type u} : everyOther [] = ([] : List α)
```

:::comment
{lean}`everyOther.eq_2` demonstrates its second pattern:
:::

{lean}`everyOther.eq_2` は二番目のパターンを説明します：

```signature
everyOther.eq_2.{u} {α : Type u} (x : α) : everyOther [x] = [x]
```

:::comment
{lean}`everyOther.eq_3` demonstrates its final pattern:
:::

{lean}`everyOther.eq_3` は最後のパターンを説明します：

```signature
everyOther.eq_3.{u} {α : Type u} (x y : α) (xs : List α) :
  everyOther (x :: y :: xs) = x :: everyOther xs
```

:::comment
Because the patterns do not overlap, no assumptions about prior patterns not having matched are necessary for the equational lemmas.
:::

パターンが重複しないため、これらの等式の補題には先行するパターンと一致しないという仮定は必要ありません。

::::
:::::

:::comment
After elaborating a module, having checked each addition to the environment with the kernel, the changes that the module made to the global environment (including extensions) are serialized to a `.olean` file.
In these files, Lean terms and values are represented just as they are in memory; thus the file can be directly memory-mapped.
All code paths that lead to Lean adding to the environment involve the new type or definition first being checked by the kernel.
However, Lean is a very open, flexible system.
To guard against the possibility of poorly-written metaprograms jumping through hoops to add unchecked values to the environment, a separate tool `lean4checker` can be used to validate that the entire environment in a `.olean` file satisfies the kernel.
:::

モジュールをエラボレートした後、カーネルで環境に対する各追加をチェックし、モジュールがグローバル環境（拡張を含む）に加えた変更を `.olean` ファイルにシリアライズします。これらのファイルでは、Lean の項と値はメモリにあるものと同じように表演されます；そのため、ファイルを直接メモリマップすることができます。Lean が環境に追加するすべてのコードパスでは、新しい型や定義が最初にカーネルによってチェックされます。しかし、Lean は非常にオープンで柔軟なシステムです。不完全に書かれたメタプログラムがチェックされていない値を環境に追加するために抜け穴をくぐってしまう可能性から守るために、別のツール `lean4lean` を使って `.olean` ファイル内の環境全体がカーネルを満たしているかどうかを検証することができます。

:::comment
In addition to the `.olean` file, the elaborator produces a `.ilean` file, which is an index used by the language server.
This file contains information needed to work interactively with the module without fully loading it, such as the source positions of definitions.
The contents of `.ilean` files are an implementation detail and may change at any release.
:::

`.olean` ファイルに加えて、エラボレータは言語サーバが使用するインデックスである `.ilean` ファイルを生成します。このファイルには定義のソース位置など、モジュールを完全にロードせずに対話的に作業するために必要な情報が含まれています。`.ilean` ファイルの内容は実装の詳細であり、どのリリースでも変更される可能性があります。

:::comment
Finally, the compiler is invoked to translate the intermediate representation of functions stored in its environment extension into C code.
A C file is produced for each Lean module; these are then compiled to native code using a bundled C compiler.
If the `precompileModules` option is set in the build configuration, then this native code can be dynamically loaded and invoked by Lean; otherwise, an interpreter is used.
For most workloads, the overhead of compilation is larger than the time saved by avoiding the interpreter, but some workloads can be sped up dramatically by pre-compiling tactics, language extensions, or other extensions to Lean.
:::

最後に、環境拡張に格納された関数の中間表現を C コードに変換するためにコンパイラが起動されます。Lean モジュールごとに C ファイルが生成され、バンドルされている C コンパイラを使ってネイティブコードにコンパイルされます。ビルド構成で `precompileModules` オプションが設定されている場合、このネイティブコードは動的にロードされ、Lean によって呼び出されます。ほとんどのワークロードでは、コンパイルのオーバーヘッドはインタプリタを使用しないことで節約できる時間よりも大きいですが、一部のワークロードではタクティク・言語拡張・Lean の他の拡張をプリコンパイルすることで劇的に高速化できます。

## Memory Allocation and Reference Counting

:::planned 208

The most important topics related to Lean's reference-counting-based allocator:

 * Overview of {deftech key:="reference count"}_reference counting_

 * Compact regions

 * When are counts incremented and decremented?

 * Tools for debugging uniqueness issues

 * When should C code increment or decrement reference counts?

 * What is the meaning of the borrow annotation (`@&`)?

:::

:::comment
# Initialization
:::

# 初期化（Initialization）

:::comment
Before starting up, the elaborator must be correctly initialized.
Lean itself contains {deftech}[initialization] code that must be run in order to correctly construct the compiler's initial state; this code is run before loading any modules and before the elaborator is invoked.
Furthermore, each dependency may itself contribute initialization code, _e.g._ to set up environment extensions.
Internally, each environment extension is assigned a unique index into an array, and this array's size is equal to the number of registered environment extensions, so the number of extensions must be known in order to correctly allocate an environment.
:::

起動する前に、エラボレータは正しく初期化されなければなりません。コンパイラの初期状態を正しく構築するために、Lean 自身は実行しなければならない {deftech}[初期化] （initialization）コードを含んでいます；このコードはモジュールのロード前とエラボレータの起動前に実行されます。さらに、各依存関係は環境拡張をセットアップするために初期化コードを提供することもあります。内部的には、各環境拡張は配列に一意のインデックスが割り当てられ、この配列のサイズは登録された環境拡張の数に等しいため、環境を正確に割り当てるために拡張の数は既知でなければなりません。

:::comment
After running Lean's own builtin initializers, the module's header is parsed and the dependencies' `.olean` files are loaded into memory.
A “pre-environment” is constructed that contains the union of the dependencies' environments.
Next, all initialization code specified by the dependencies is executed in the interpreter.
At this point, the number of environment extensions is known, so the pre-environment can be reallocated into an environment structure with a correctly-sized extensions array.
:::

Lean 自身の組み込み初期化を実行した後、モジュールのヘッダが解析され、依存関係の `.olean` ファイルがメモリにロードされます。依存関係の環境の合併を含む「事前環境」が構築されます。次に、依存関係によって指定されたすべての初期化コードがインタプリタで実行されます。この時点で、環境拡張の数がわかっているため、事前環境を正しいサイズの拡張配列を持つ環境構造体に再割り当てすることができます。

::::syntax command
:::comment
An {keywordOf Lean.Parser.Command.initialize}`initialize` block adds code to the module's initializers.
The contents of an {keywordOf Lean.Parser.Command.initialize}`initialize` block are treated as the contents of a {keywordOf Lean.Parser.Term.do}`do` block in the {lean}`IO` monad.
:::

{keywordOf Lean.Parser.Command.initialize}`initialize` ブロックはモジュールの初期化にコードを追加します。 {keywordOf Lean.Parser.Command.initialize}`initialize` ブロックの内容は、 {lean}`IO` モナドの {keywordOf Lean.Parser.Term.do}`do` ブロックの内容として扱われます。

:::comment
Sometimes, initialization only needs to extend internal data structures by side effects.
In that case the contents are expected to have type {lean}`IO Unit`:
:::

時には、初期化は副作用によって内部データ構造を拡張することだけを必要とします。その場合、内容は {lean}`IO Unit` 型を持つことが期待されます：

```grammar
initialize
  $cmd*
```

:::comment
Initialization may also be used to construct values that contain references to internal state, such as attributes that are backed by an environment extension.
In this form of {keywordOf Lean.Parser.Command.initialize}`initialize`, initialization should return the specified type in the {lean}`IO` monad.
:::

初期化は、環境拡張によってバックアップされた属性などの内部状態への参照を含む値を構築するためにも使用できます。この形式の {keywordOf Lean.Parser.Command.initialize}`initialize` では、初期化は {lean}`IO` モナドで指定された型を返す必要があります。

```grammar
initialize $x:ident : $t:term ←
  $cmd*
```
::::


::::syntax command
:::comment
Lean's internals also define code that must run during initialization.
However, because Lean is a bootstrapping compiler, special care must be taken with initializers defined as part of Lean itself, and Lean's own initializers must run prior to importing or loading _any_ modules.
These initializers are specified using {keywordOf Lean.Parser.Command.initialize}`builtin_initialize`, which should not be used outside the compiler's implementation.
:::

Lean の内部では、初期化中に実行しなければならないコードも定義されています。しかし、Lean はブートストラップコンパイラであるため、Lean 自身の一部として定義された初期化には特別な注意が必要であり、Lean 自身の初期化は _任意の_ モジュールを先にインポートやロードする前に実行しなければなりません。これらの初期化は {keywordOf Lean.Parser.Command.initialize}`builtin_initialize` を使って指定し、これはコンパイラの実装外では使うべきではありません。

```grammar
builtin_initialize
  $cmd*
```
```grammar
builtin_initialize $x:ident : $t:term ←
  $cmd*
```
::::
