/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Lean.Parser.Command

import Manual.IO.Console
import Manual.IO.Files
import Manual.IO.Threads
import Manual.IO.Ref

open Manual
open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "IO" =>
%%%
tag := "io"
%%%



:::comment
Lean is a pure functional programming language.
While Lean code is strictly evaluated at run time, the order of evaluation that is used during type checking, especially while checking {tech}[definitional equality], is formally unspecified and makes use of a number of heuristics that improve performance but are subject to change.
This means that simply adding operations that perform side effects (such as file I/O, exceptions, or mutable references) would lead to programs in which the order of effects is unspecified.
During type checking, even terms with free variables are reduced; this would make side effects even more difficult to predict.
Finally, a basic principle of Lean's logic is that functions are _functions_ that map each element of the domain to a unique element of the range.
Including side effects such as console I/O, arbitrary mutable state, or random number generation would violate this principle.

:::

Lean は純粋関数型プログラミング言語です。Lean のコードは実行時に正格評価されますが、型チェック、特に {tech}[定義上の等価性] のチェックをする際に使用される評価の順序は形式的に指定されておらず、パフォーマンスを向上させる今後変更の可能性がある多くのヒューリスティックを使用しています。つまり、副作用（ファイル I/O・例外・可変な参照など）を実行する操作を単純に追加すると、作用の順序が特定されないプログラムになります。型チェックでは、自由変数を持つ項でさえも簡約されます；これは副作用の予測をさらに難しくします。最後に、Lean のロジックの基本法則は、関数は定義域の各要素を値域の一意な値にマッピングする _関数_ であるということです。コンソール I/O・任意の可変状態・乱数生成などの副作用を含めると、この原則に反することになります。

:::::keepEnv
```lean (show := false)
/-- A type -/
axiom α : Type
```

:::comment
Programs that may have side effects have a type (typically {lean}`IO α`) that distinguishes them from pure functions.
Logically speaking, {lean}`IO` describes the sequencing and data dependencies of side effects.
Many of the basic side effects, such as reading from files, are opaque constants from the perspective of Lean's logic.
Others are specified by code that is logically equivalent to the run-time version.
At run time, the compiler produces ordinary code.

:::

副作用を持つ可能性のあるプログラムを純粋な関数と区別するための型（一般的に {lean}`IO α` と書かれる）があります。論理的に言えば、 {lean}`IO` は副作用のシーケンスとデータの依存関係を記述します。ファイルからの読み込みなどの基本的な副作用の多くは、Lean の論理の視点からすると不透明な定数です。その他の副作用は、実行時のコードと論理的に同等なコードによって指定されます。実行時には、コンパイラは通常のコードを生成します。

:::::

:::comment
# Logical Model
:::

# 論理モデル（Logical Model）


:::::keepEnv
```lean (show := false)
/-- A type -/
axiom α : Type
```
:::comment
Conceptually, Lean distinguishes evaluation or reduction of terms from _execution_ of side effects.
Term reduction is specified by rules such as {tech}[β] and {tech}[δ], which may occur anywhere at any time.
Side effects, which must be executed in the correct order, are abstractly described in Lean's logic.
When programs are run, the Lean runtime system is responsible for actually carrying out the described effects.


:::

概念的に、Lean は項の評価や簡約と副作用の _実行_ を区別します。項の簡約は {tech}[β] や {tech}[δ] のような規則で指定され、いつでも・どこでも発生する可能性があります。正しい順序で実行されなければならない副作用は Lean の論理で抽象的に記述されます。プログラムが実行されると、Lean のランタイムシステムは記述された作用を実際に実行する責任を負います。

:::comment
The type {lean}`IO α` is a description of a process that, by performing side effects, should either return a value of type {lean}`α` or throw an error.
It can be thought of as a {tech}[state monad] in which the state is the entire world.
Just as a value of type {lean}`StateM Nat Bool` computes a {lean}`Bool` while having the ability to mutate a natural number, a value of type {lean}`IO Bool` computes a {lean}`Bool` while potentially changing the world.
Error handling is accomplished by layering an appropriate exception monad transformer on top of this.

:::

{lean}`IO α` 型は副作用を実行することによって {lean}`α` 型の値を返すか、エラーを投げるべきプロセスについての記述です。これは世界全体を状態とする {tech}[state monad] として考えることができます。 {lean}`StateM Nat Bool` 型の値が自然数をミューテーションさせる能力を持ちながら {lean}`Bool` を計算することと同じように、 {lean}`IO Bool` 型の値は世界を変化させる可能性を有しながら {lean}`Bool` を計算します。エラー処理は、適切な例外モナド変換子をこの上に重ねることで達成されます。

:::::

:::comment
Because the entire world can't be represented in memory, the actual implementation uses an abstract token that stands for its state.
The Lean runtime system is responsible for providing the initial token when the program is run, and each primitive action accepts a token that represents the world and returns another when finished.
This ensures that effects occur in the proper order, and it clearly separates the execution of side effects from the reduction semantics of Lean terms.



:::

世界全体をメモリ上で表現することはできないため、実際の実装ではその状態を表す抽象的なトークンを使用します。Lean のランタイムシステムは、プログラムの実行時に最初のトークンを提供する責任を負い、各プリミティブのアクションは世界を表すトークンを受け入れ、終了時に別のトークンを返します。これにより作用が適切な順序で発生することが保証され、Lean の項の簡約セマンティクスから副作用の実行が明確に分離されます。

:::comment
Non-termination via general recursion is treated separately from the effects described by {name}`IO`.
Programs that may not terminate due to infinite loops must be defined as {ref "partial-unsafe"}[`partial`] functions.
From the logical perspective, they are treated as arbitrary constants; {name}`IO` is not needed.

:::

一般的な再帰による停止しない処理は、 {name}`IO` で説明される作用とは別に扱われます。無限ループによって終了しない可能性のあるプログラムは {ref "partial-unsafe"}[`partial`] 関数として定義する必要があります。論理的な観点からは、これらは任意の定数として扱われます； {name}`IO` である必要はありません。

:::comment
A very important property of {lean}`IO` is that there is no way for values to “escape”.
Without using one of a few clearly-marked unsafe operators, programs have no way to extract a pure {lean}`Nat` from an {lean}`IO Nat`.
This ensures that the correct ordering of side effects is preserved, and it ensures that programs that have side effects are clearly marked as such.

:::

{lean}`IO` の非常に重要な特性は、値が「エスケープ」する方法がないということです。いくつかの明確にマークされた安全でない演算子を使用しない限り、プログラムは {lean}`IO Nat` から純粋な {lean}`Nat` を取り出す方法がありません。これにより副作用の正しい順序が保たれ、副作用のあるプログラムが副作用を持つものとして明確にマークされることが保証されます。

:::comment
## The `IO`, `EIO` and `BaseIO` Monads
:::

## `IO` ・ `EIO` ・ `BaseIO` モナド（The `IO`, `EIO` and `BaseIO` Monads）


:::comment
There are two monads that are typically used for programs that interact with the real world:

:::

現実世界と相互作用するプログラムで典型的に使われるモナドが2つあります：

:::comment
 * Actions in {lean}`IO` may throw exceptions of type {lean}`IO.Error` or modify the world.
 * Actions in {lean}`BaseIO` can't throw exceptions, but they can modify the world.

:::

 * {lean}`IO` のアクションは {lean}`IO.Error` 型の例外を投げるか、世界を変更することができます。
 * {lean}`BaseIO` のアクションは例外を投げることができませんが、世界を変更することができます。

:::comment
The distinction makes it possible to tell whether exceptions are possible by looking at an action's type signature.
{lean}`BaseIO` actions are automatically promoted to {lean}`IO` as necessary.

:::

この区別により、アクションの型シグネチャを見れば例外が発生するかどうかがわかります。 {lean}`BaseIO` アクションは必要に応じて自動的に {lean}`IO` に昇格します。

{docstring IO}

{docstring BaseIO}

:::comment
Both {lean}`IO` and {lean}`BaseIO` are instances of {lean}`EIO`, in which the type of errors is a parameter.
{lean}`IO` is defined as {lean}`EIO IO.Error`, while {lean}`BaseIO` is defined as {lean}`EIO Empty`.
In some circumstances, such as bindings to non-Lean libraries, it can be convenient to use {lean}`EIO` with a custom error type, which ensures that errors are handled at the boundaries between these and other {lean}`IO` actions.

:::

{lean}`IO` と {lean}`BaseIO` はどちらもエラーの型をパラメータとする {lean}`EIO` のインスタンスです。 {lean}`IO` は {lean}`EIO IO.Error` として定義される一方、 {lean}`BaseIO` は {lean}`EIO Empty` として定義されます。 Lean 以外のライブラリへのバインディングなど、状況によっては {lean}`EIO` をカスタムのエラー型で使用すると便利です。これによってそれらのアクションとそれ以外の {lean}`IO` アクションの間に境界を設けてエラーハンドリングされることが保証されます。

```lean (show := false)
-- Check claim in preceding paragraph
example : IO = EIO IO.Error := rfl
example : BaseIO = EIO Empty := rfl
```

{docstring EIO}

{docstring IO.lazyPure}

{docstring BaseIO.toIO}

{docstring BaseIO.toEIO}

{docstring EIO.toBaseIO}

{docstring EIO.toIO}

{docstring EIO.toIO'}

{docstring IO.toEIO}

:::comment
## Errors and Error Handling
:::

## エラーとエラーハンドリング（Errors and Error Handling）


:::comment
Error handling in the {lean}`IO` monad uses the same facilities as any other {tech}[exception monad].
In particular, throwing and catching exceptions uses the methods of the {name}`MonadExceptOf` {tech}[type class].
The exceptions thrown in {lean}`IO` have the type {lean}`IO.Error`.
The constructors of this type represent the low-level errors that occur on most operating systems, such as files not existing.
The most-used constructor is {name IO.Error.userError}`userError`, which covers all other cases and includes a string that describes the problem.

:::

{lean}`IO` モナドにおけるエラー処理は、他の {tech}[exception monad] と同じ機能を使用します。特に、例外のスローとキャッチは {name}`MonadExceptOf` {tech}[型クラス] のメソッドを使用します。 {lean}`IO` で投げられる例外は {lean}`IO.Error` 型を持ちます。このコンストラクタは、ファイルが存在しないなど、ほとんどのオペレーティングシステムで発生する低レベルのエラーを表します。最もよく使われるエラーは {name IO.Error.userError}`userError` で、これは他のすべてのケースをカバーし、問題を説明する文字列を含みます。

{docstring IO.Error}

{docstring IO.Error.toString}

{docstring IO.ofExcept}

{docstring EIO.catchExceptions}

{docstring IO.userError}

:::comment
::example "Throwing and Catching Errors"
:::
:::::example "例外のスローとキャッチ"
::::ioExample
:::comment
This program repeatedly demands a password, using exceptions for control flow.
The syntax used for exceptions is available in all exception monads, not just {lean}`IO`.
When an incorrect password is provided, an exception is thrown, which is caught by the loop that repeats the password check.
A correct password allows control to proceed past the check, terminating the loop, and any other exceptions are re-thrown.

:::

このプログラムは制御フローに例外を使用して繰り返しパスワードを要求します。例外の構文は {lean}`IO` だけでなく、すべての例外モナドで使用できます。不正なパスワードが提供されると例外が投げられ、パスワードチェックを繰り返すループでキャッチされます。正しいパスワードが指定された場合、制御はチェックを通過してループを終了し、他の例外は再度投げられます。

```ioLean
def accessControl : IO Unit := do
  IO.println "What is the password?"
  let password ← (← IO.getStdin).getLine
  if password.trim != "secret" then
    throw (.userError "Incorrect password")
  else return

def repeatAccessControl : IO Unit := do
  repeat
    try
      accessControl
      break
    catch
      | .userError "Incorrect password" =>
        continue
      | other =>
        throw other

def main : IO Unit := do
  repeatAccessControl
  IO.println "Access granted!"
```

:::comment
When run with this input:
:::

以下の入力で実行すると：

```stdin
publicinfo
secondtry
secret
```

:::comment
the program emits:
:::

このプログラムは以下を出力します：

```stdout
What is the password?
What is the password?
What is the password?
Access granted!
```
::::
:::::

:::comment
### Constructing IO Errors
:::

### IO エラーの構成（Constructing IO Errors）


{docstring IO.Error.mkUnsupportedOperation}

{docstring IO.Error.mkUnsatisfiedConstraints}

{docstring IO.Error.mkProtocolError}

{docstring IO.Error.mkResourceBusy}

{docstring IO.Error.mkResourceVanished}

{docstring IO.Error.mkNoSuchThing}

{docstring IO.Error.mkNoSuchThingFile}

{docstring IO.Error.mkEofError}

{docstring IO.Error.mkPermissionDenied}

{docstring IO.Error.mkNoFileOrDirectory}

{docstring IO.Error.mkTimeExpired}

{docstring IO.Error.fopenErrorToString}

{docstring IO.Error.mkAlreadyExists}

{docstring IO.Error.mkInvalidArgument}

{docstring IO.Error.mkHardwareFault}

{docstring IO.Error.mkResourceExhausted}

{docstring IO.Error.mkInappropriateType}

{docstring IO.Error.mkOtherError}

{docstring IO.Error.otherErrorToString}

{docstring IO.Error.mkInvalidArgumentFile}

{docstring IO.Error.mkResourceExhaustedFile}

{docstring IO.Error.mkAlreadyExistsFile}


{docstring IO.Error.mkIllegalOperation}

{docstring IO.Error.mkPermissionDeniedFile}

{docstring IO.Error.mkInterrupted}

{docstring IO.Error.mkInappropriateTypeFile}

:::comment
# Control Structures
:::

# 制御構造（Control Structures）


:::comment
Normally, programs written in {lean}`IO` use {ref "monads-and-do"}[the same control structures as those written in other monads].
There is one specific {lean}`IO` helper.

:::

通常、 {lean}`IO` で書かれたプログラムは {ref "monads-and-do"}[他のモナドで書かれたものと同じ制御構造] を使用します。特定の {lean}`IO` 補助関数が1つ存在します。

{docstring IO.iterate}

{include 0 Manual.IO.Console}

{include 0 Manual.IO.Ref}

{include 0 Manual.IO.Files}

# 環境変数（Environment Variables）

:::comment
# Environment Variables

:::

{docstring IO.getEnv}

:::comment
# Timing
:::

# タイミング（Timing）


{docstring IO.sleep}

{docstring IO.monoNanosNow}

{docstring IO.monoMsNow}

{docstring IO.getNumHeartbeats}

{docstring IO.addHeartbeats}

:::comment
# Processes

:::

# プロセス（Processes）


:::comment
## Current Process
:::

## 現在のプロセス（Current Process）


{docstring IO.Process.getCurrentDir}

{docstring IO.Process.setCurrentDir}

{docstring IO.Process.exit}

{docstring IO.Process.getPID}

:::comment
## Running Processes
:::

## プロセスの実行（Running Processes）


:::comment
There are three primary ways to run other programs from Lean:

:::

Lean から他のプログラムを実行するには主に3つの方法があります：

:::comment
 1. {lean}`IO.Process.run` synchronously executes another program, returning its standard output as a string. It throws an error if the process exits with an error code other than `0`.
 2. {lean}`IO.Process.output` synchronously executes another program with an empty standard input, capturing its standard output, standard error, and exit code. No error is thrown if the process terminates unsuccessfully.
 3. {lean}`IO.Process.spawn` starts another program asynchronously and returns a data structure that can be used to access the process's standard input, output, and error streams.

:::

 1. {lean}`IO.Process.run` は他のプログラムを同期的に実行し、その標準出力を文字列として返します。プロセスが `0` 以外のエラーコードで終了した場合、エラーを投げます。
 2. {lean}`IO.Process.output` は空の標準入力で別のプログラムを同期的に実行し、その標準出力・標準エラー・終了コードをキャプチャします。プロセスが失敗して終了してもエラーは投げられません。
 3. {lean}`IO.Process.spawn` は別のプログラムを非同期に開始し、プロセスの標準入力・標準出力・エラーストリームにアクセスするために使用できるデータ構造を返します。

{docstring IO.Process.run}

:::comment
::example "Running a Program"
:::
:::::example "プログラムの実行"
:::comment
When run, this program concatenates its own source code with itself twice using the Unix tool `cat`.

:::

このプログラムを実行すると、Unix のツール `cat` を使って自分のソースコードと自分自身を2回連結します。

::::ioExample
```ioLean
-- Main.lean begins here
def main : IO Unit := do
  let src2 ← IO.Process.run {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  IO.println src2
-- Main.lean ends here
```

:::comment
Its output is:
:::

これは以下を出力します：

```stdout
-- Main.lean begins here
def main : IO Unit := do
  let src2 ← IO.Process.run {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  IO.println src2
-- Main.lean ends here
-- Main.lean begins here
def main : IO Unit := do
  let src2 ← IO.Process.run {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  IO.println src2
-- Main.lean ends here
```
::::
:::::

:::comment
::example "Running a Program on a File"
:::
:::::example "ファイルに対するプログラムの実行"

:::comment
This program uses the Unix utility `grep` as a filter to find four-digit palindromes.
It creates a file that contains all numbers from {lean}`0` through {lean}`9999`, and then invokes `grep` on it, reading the result from its standard output.

:::

このプログラムは Unix ユーティリティ `grep` をフィルタとして使って4桁の回文を見つけます。 {lean}`0` から {lean}`9999` までのすべての数字を含むファイルを作成し、それに対して `grep` を実行し、その結果を標準出力から読み取ります。

::::ioExample
```ioLean
def main : IO Unit := do
  -- Feed the input to the subprocess
  IO.FS.withFile "numbers.txt" .write fun h =>
    for i in [0:10000] do
      h.putStrLn (toString i)

  let palindromes ← IO.Process.run {
    cmd := "grep",
    args := #[r#"^\([0-9]\)\([0-9]\)\2\1$"#, "numbers.txt"]
  }

  let count := palindromes.trim.splitOn "\n" |>.length

  IO.println s!"There are {count} four-digit palindromes."
```

:::comment
Its output is:
:::

これは以下を出力します：

```stdout
There are 90 four-digit palindromes.
```
::::
:::::


{docstring IO.Process.output}

:::comment
::example "Checking Exit Codes"
:::
:::::example "終了コードのチェック"
:::comment
When run, this program first invokes `cat` on a nonexistent file and displays the resulting error code.
It then concatenates its own source code with itself twice using the Unix tool `cat`.

:::

このプログラムを実行すると、まず存在しないファイルに対して `cat` を呼び出し、その結果のエラーコードを表示します。その後、Unix のツールである `cat` を使って自分自身のソースコードと自分自身を2回連結します。

::::ioExample
```ioLean
-- Main.lean begins here
def main : IO UInt32 := do
  let src1 ← IO.Process.output {cmd := "cat", args := #["Nonexistent.lean"]}
  IO.println s!"Exit code from failed process: {src1.exitCode}"

  let src2 ← IO.Process.output {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  if src2.exitCode == 0 then
    IO.println src2.stdout
  else
    IO.eprintln "Concatenation failed"
    return 1

  return 0
-- Main.lean ends here
```

:::comment
Its output is:
:::

これは以下を出力します：

```stdout
Exit code from failed process: 1
-- Main.lean begins here
def main : IO UInt32 := do
  let src1 ← IO.Process.output {cmd := "cat", args := #["Nonexistent.lean"]}
  IO.println s!"Exit code from failed process: {src1.exitCode}"

  let src2 ← IO.Process.output {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  if src2.exitCode == 0 then
    IO.println src2.stdout
  else
    IO.eprintln "Concatenation failed"
    return 1

  return 0
-- Main.lean ends here
-- Main.lean begins here
def main : IO UInt32 := do
  let src1 ← IO.Process.output {cmd := "cat", args := #["Nonexistent.lean"]}
  IO.println s!"Exit code from failed process: {src1.exitCode}"

  let src2 ← IO.Process.output {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  if src2.exitCode == 0 then
    IO.println src2.stdout
  else
    IO.eprintln "Concatenation failed"
    return 1

  return 0
-- Main.lean ends here

```
::::
:::::


{docstring IO.Process.spawn}

:::comment
::example "Asynchronous Subprocesses"
:::
:::::example "非同期なサブプロセス"

:::comment
This program uses the Unix utility `grep` as a filter to find four-digit palindromes.
It feeds all numbers from {lean}`0` through {lean}`9999` to the `grep` process and then reads its result.
This code is only correct when `grep` is sufficiently fast and when the output pipe is large enough to contain all 90 four-digit palindromes.

:::

このプログラムは Unix ユーティリティ `grep` をフィルタとして使って4桁の回文を見つけます。 {lean}`0` から {lean}`9999` までのすべての数字を `grep` プロセスに送り、その結果を読み込みます。このコードは `grep` が十分に高速で、出力パイプが90個の4桁回文をすべて含むのに十分な大きさがある場合においてのみ正しく動作します。

::::ioExample
```ioLean
def main : IO Unit := do
  let grep ← IO.Process.spawn {
    cmd := "grep",
    args := #[r#"^\([0-9]\)\([0-9]\)\2\1$"#],
    stdin := .piped,
    stdout := .piped,
    stderr := .null
  }

  -- Feed the input to the subprocess
  for i in [0:10000] do
    grep.stdin.putStrLn (toString i)

  -- Consume its output, after waiting 100ms for grep to process the data.
  IO.sleep 100
  let count := (← grep.stdout.readToEnd).trim.splitOn "\n" |>.length

  IO.println s!"There are {count} four-digit palindromes."
```

:::comment
Its output is:
:::

これは以下を出力します：

```stdout
There are 90 four-digit palindromes.
```
::::
:::::

{docstring IO.Process.SpawnArgs}

{docstring IO.Process.StdioConfig}

{docstring IO.Process.Stdio}

{docstring IO.Process.Stdio.toHandleType}

{docstring IO.Process.Child}

{docstring IO.Process.Child.wait}

{docstring IO.Process.Child.tryWait}

{docstring IO.Process.Child.kill}

{docstring IO.Process.Child.takeStdin}

:::comment
::example "Closing a Subprocess's Standard Input"
:::
:::::example "サブプロセスの標準入力を閉じる"

:::comment
This program uses the Unix utility `grep` as a filter to find four-digit palindromes, ensuring that the subprocess terminates successfully.
It feeds all numbers from {lean}`0` through {lean}`9999` to the `grep` process, then closes the process's standard input, which causes it to terminate.
After checking `grep`'s exit code, the program extracts its result.

:::

このプログラムは Unix ユーティリティ `grep` をフィルタとして使って4桁の回文を見つけ、サブプロセスが正常に終了するようにします。 {lean}`0` から {lean}`9999` までのすべての数字を `grep` プロセスに送り、それからプロセスの標準入力を閉じて終了させます。`grep` の終了コードをチェックした後、プログラムはその結果を取り出します。

::::ioExample
```ioLean
def main : IO UInt32 := do
  let grep ← do
    let (stdin, child) ← (← IO.Process.spawn {
      cmd := "grep",
      args := #[r#"^\([0-9]\)\([0-9]\)\2\1$"#],
      stdin := .piped,
      stdout := .piped,
      stderr := .null
    }).takeStdin

    -- Feed the input to the subprocess
    for i in [0:10000] do
      stdin.putStrLn (toString i)

    -- Return the child without its stdin handle.
    -- This closes the handle, because there are
    -- no more references to it.
    pure child

  -- Wait for grep to terminate
  if (← grep.wait) != 0 then
    IO.eprintln s!"grep terminated unsuccessfully"
    return 1

  -- Consume its output
  let count := (← grep.stdout.readToEnd).trim.splitOn "\n" |>.length

  IO.println s!"There are {count} four-digit palindromes."
  return 0
```

:::comment
Its output is:
:::

これは以下を出力します：

```stdout
There are 90 four-digit palindromes.
```
::::
:::::

{docstring IO.Process.Output}



:::comment
# Random Numbers
:::

# 乱数（Random Numbers）


{docstring IO.setRandSeed}

{docstring IO.rand}

{docstring randBool}

{docstring randNat}

:::comment
## Random Generators
:::

## 乱数生成（Random Generators）


{docstring RandomGen}

{docstring StdGen}

{docstring stdRange}

{docstring stdNext}

{docstring stdSplit}

{docstring mkStdGen}

:::comment
## System Randomness
:::

## システムの乱数（System Randomness）


{docstring IO.getRandomBytes}

{include 0 Manual.IO.Threads}
