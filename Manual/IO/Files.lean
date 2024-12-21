/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

/-
#doc (Manual) "Files, File Handles, and Streams" =>
-/
#doc (Manual) "ファイル・ファイルハンドラ・ストリーム（Files, File Handles, and Streams）" =>

:::comment
Lean provides a consistent filesystem API on all supported platforms.
These are the key concepts:

:::

Lean はサポート対象のすべてのプラットフォームに対して一貫したファイルシステム API を提供します。以下がカギとなるコンセプトです：

:::comment
: {deftech}[Files]

  Files are an abstraction provided by operating systems that provide random access to persistently-stored data, organized hierarchically into directories.

:::

: {deftech}[ファイル] （file）

  ファイルとはオペレーティングシステムが提供する抽象化で、ディレクトリとして階層的に編成された永続的に保存されるデータへのランダムアクセスを提供します。

:::comment
: {deftech}[Directories]

  Directories, also known as _folders_, may contain files or other directories.
  Fundamentally, a directory maps names to the files and/or directories that it contains.

:::

: {deftech}[ディレクトリ] （directory）

  ディレクトリは _フォルダ_ （folder）としても知られ、ファイルや他のディレクトリを含むことができます。基本的に、ディレクトリはその中に含まれるファイルやディレクトリに名前をマッピングします。

:::comment
: {deftech}[File Handles]

  File handles ({name IO.FS.Handle}`Handle`) are abstract references to files that have been opened for reading and/or writing.
  A file handle maintains a mode that determines whether reading and/or writing are allowed, along with a cursor that points at a specific location in the file.
  Reading from or writing to a file handle advances the cursor.
  File handles may be {deftech}[buffered], which means that reading from a file handle may not return the current contents of the persistent data, and writing to a file handle may not modify them immediately.

:::

: {deftech}[ファイルハンドラ] （file handler）

  ファイルハンドラ（ {name IO.FS.Handle}`Handle` ）は読み書きのどちらか、もしくは両方のためにオープンされたファイルへの抽象的な参照です。ファイルハンドラはファイルの特定の場所を指すカーソルと共に、読み書きのどちらか、もしくは両方が許可されているかどうかを決定するモードを保持します。ファイルハンドラからの読み込みやファイルハンドラへの書き込みによってカーソルが進められます。ファイルハンドラは {deftech}[バッファ] される可能性があります。これはファイルハンドラからの読み込みが永続データの現在の内容を返さない可能性およびファイルハンドラへの書き込みが直ちに反映されない可能性があることを意味します。

:::comment
: Paths

  Files are primarily accessed via {deftech}_paths_ ({name}`System.FilePath`).
  A path is a sequence of directory names, potentially terminated by a file name.
  They are represented by strings in which separator characters {margin}[The current platform's separator characters are listed in {name}`System.FilePath.pathSeparators`.] delimit the names.

  The details of paths are platform-specific.
  {deftech}[Absolute paths] begin in a {deftech}_root directory_; some operating systems have a single root, while others may have multiple root directories.
  Relative paths do not begin in a root directory and require that some other directory be taken as a starting point.
  In addition to directories, paths may contain the special directory names `.`, which refers to the directory in which it is found, and `..`, which refers to prior directory in the path.

  Filenames, and thus paths, may end in one or more {deftech}_extensions_ that identify the file's type.
  Extensions are delimited by the character {name}`System.FilePath.extSeparator`.
  On some platforms, executable files have a special extension ({name}`System.FilePath.exeExtension`).

:::

: パス

  ファイルは主に {deftech}_パス_ （path、 {name}`System.FilePath` ）を介してアクセスされます。パスはディレクトリ名の列で、ファイル名で終わる可能性があります。パスは名前を区切り文字 {margin}[現在のプラットフォームでの区切り文字は {name}`System.FilePath.pathSeparators` にリストされています。] で区切られた文字列として表現されます。

  パスの詳細はプラットフォームに固有です。 {deftech}[絶対パス] （absolute path）は {deftech}_ルートディレクトリ_ （root directory）から始まります；いくつかのオペレーティングシステムでは単一のルートを持ちますが、それ以外では複数のルートディレクトリを持つ可能性があります。相対パスはルートディレクトリから始まらず、他のディレクトリを始点とする必要があります。ディレクトリに加えて、パスは特別なディレクトリ名 `.` を含むことができます。これは見つかったディレクトリを指します。また `..` はパス内の前のディレクトリを指します。

  ファイル名、またパスはファイルの種類を識別する1つ以上の {deftech}_拡張子_ （extension）で終わることがあります。拡張子は {name}`System.FilePath.extSeparator` 文字で区切られます。一部のプラットフォームでは、実行ファイルは特別な拡張子（ {name}`System.FilePath.exeExtension` ）を持ちます。

:::comment
: {deftech}[Streams]

  Streams are a higher-level abstraction over files, both providing additional functionality and hiding some details of files.
  While {tech}[file handles] are essentially a thin wrapper around the operating system's representation, streams are implemented in Lean as a structure called {lean}`IO.FS.Stream`.
  Because streams are implemented in Lean, user code can create additional streams, which can be used seamlessly together with those provided in the standard library.

:::

: {deftech}[ストリーム] （stream）

  ストリームはファイルをより高度に抽象化したもので、追加機能を提供しつつファイルの詳細を隠します。 {tech}[ファイルハンドラ] は基本的にオペレーティングシステムの表現の薄いラッパーですが、ストリームは Lean では {lean}`IO.FS.Stream` という構造体として実装されています。ストリームは Lean 上で実装されているため、ユーザコードは追加のストリームを作成することができ、標準ライブラリで提供されるストリームとシームレスに併用することができます。

:::comment
# Low-Level File API
:::

# 低レベルのファイル API（Low-Level File API）


:::comment
At the lowest level, files are explicitly opened using {name IO.FS.Handle.mk}`Handle.mk`.
When the last reference to the handle object is dropped, the file is closed.
There is no explicit way to close a file handle other than by ensuring that there are no references to it.


:::

最も低いレベルでは、ファイルは {name IO.FS.Handle.mk}`Handle.mk` を使って明示的にオープンされます。ハンドラオブジェクトへの最後の参照が削除されると、ファイルはクローズされます。ファイルハンドラを閉じる明示的な方法は、そのハンドラへの参照がないことを確認する以外に存在しません。

{docstring IO.FS.Handle}

{docstring IO.FS.Handle.mk}

{docstring IO.FS.Mode}

{docstring IO.FS.Handle.read}

{docstring IO.FS.Handle.readToEnd}

{docstring IO.FS.Handle.readBinToEnd}

{docstring IO.FS.Handle.readBinToEndInto}

{docstring IO.FS.Handle.getLine}

{docstring IO.FS.Handle.write}

{docstring IO.FS.Handle.putStr}

{docstring IO.FS.Handle.putStrLn}

{docstring IO.FS.Handle.flush}

{docstring IO.FS.Handle.rewind}

{docstring IO.FS.Handle.truncate}

{docstring IO.FS.Handle.isTty}

{docstring IO.FS.Handle.lock}

{docstring IO.FS.Handle.tryLock}

{docstring IO.FS.Handle.unlock}


:::comment
::example "One File, Multiple Handles"
:::
:::::example "1つのファイルと複数のハンドラ"
:::comment
This program has two handles to the same file.
Because file I/O may be buffered independently for each handle, {name IO.FS.Handle.flush}`Handle.flush` should be called when the buffers need to be synchronized with the file's actual contents.
Here, the two handles proceed in lock-step through the file, with one of them a single byte ahead of the other.
The first handle is used to count the number of occurrences of `'A'`, while the second is used to replace each `'A'` with `'!'`.
The second handle is opened in {name IO.FS.Mode.readWrite}`readWrite` mode rather than {name IO.FS.Mode.write}`write` mode because opening an existing file in {name IO.FS.Mode.write}`write` mode replaces it with an empty file.
In this case, the buffers don't need to be flushed during execution because modifications occur only to parts of the file that will not be read again, but the write handle should be flushed after the loop has completed.

:::

このプログラムには同じファイルに対する2つのハンドラがあります。ファイル I/O はハンドラごとに独立してバッファされることがあるため、バッファをファイルの実際の内容と同期させる必要がある場合は {name IO.FS.Handle.flush}`Handle.flush` を呼び出す必要があります。ここでは2つのハンドラは一方のハンドラが他方のハンドラより1バイト先になるようにファイル内をロックステップで進みます。最初のハンドラは `'A'` の出現回数を数えるために使われ、2番目のハンドラは `'A'` を `'!'` に置き換えるために使われます。2番目のハンドラは {name IO.FS.Mode.write}`write` モードではなく {name IO.FS.Mode.readWrite}`readWrite` モードで開かれています。これは {name IO.FS.Mode.write}`write` モードで既存のファイルを開くと空のファイルに置き換わるからです。今回の場合、バッファは実行中にフラッシュされる必要はありません。なぜなら変更はファイルの再読み込みされない部分に対してのみ行われるものの、書き出しハンドラはループが完了したらフラッシュしなければならないからです。

::::ioExample
```ioLean
open IO.FS (Handle)

def main : IO Unit := do
  IO.println s!"Starting contents: '{(← IO.FS.readFile "data").trim}'"

  let h ← Handle.mk "data" .read
  let h' ← Handle.mk "data" .readWrite
  h'.rewind

  let mut count := 0
  let mut buf : ByteArray ← h.read 1
  while ok : buf.size = 1 do
    if Char.ofUInt8 buf[0] == 'A' then
      count := count + 1
      h'.write (ByteArray.empty.push '!'.toUInt8)
    else
      h'.write buf
    buf ← h.read 1

  h'.flush

  IO.println s!"Count: {count}"
  IO.println s!"Contents: '{(← IO.FS.readFile "data").trim}'"
```

:::comment
When run on this file:
:::

このファイルに対して実行すると：

```inputFile "data"
AABAABCDAB
```

:::comment
the program outputs:
:::

プログラムは以下を出力します：

```stdout
Starting contents: 'AABAABCDAB'
Count: 5
Contents: '!!B!!BCD!B'
```
```stderr (show := false)
```

:::comment
Afterwards, the file contains:
:::

その後、ファイル内容は以下のようになります：

```outputFile "data"
!!B!!BCD!B
```

::::
:::::

:::comment
# Streams
:::

# ストリーム（Streams）


{docstring IO.FS.Stream}

{docstring IO.FS.withIsolatedStreams}

{docstring IO.FS.Stream.ofBuffer}

{docstring IO.FS.Stream.ofHandle}

{docstring IO.FS.Stream.putStrLn}

{docstring IO.FS.Stream.Buffer}

{docstring IO.FS.Stream.Buffer.data}

{docstring IO.FS.Stream.Buffer.pos}

:::comment
# Paths
:::

# パス（Paths）


:::comment
Paths are represented by strings.
Different platforms have different conventions for paths: some use slashes (`/`) as directory separators, others use backslashes (`\`).
Some are case-sensitive, others are not.
Different Unicode encodings and normal forms may be used to represent filenames, and some platforms consider filenames to be byte sequences rather than strings.
A string that represents an {tech}[absolute path] on one system may not even be a valid path on another system.

:::

パスは文字列として表現されます。ディレクトリの区切り文字としてスラッシュ（`/`）を使う場合もあれば、バックスラッシュ（`\`）を使う場合もあります。大文字小文字を区別する場合もあれば区別しない場合もあります。ファイル名を表現するために異なる Unicode エンコーディングや正規形が使われるかもしれず、プラットフォームによってはファイル名を文字列ではなくバイト列とみなすものもあります。あるシステムでは {tech}[絶対パス] を表す文字列が別のシステムでは有効なパスではないこともあります。

:::comment
To write Lean code that is as compatible as possible with multiple systems, it can be helpful to use Lean's path manipulation primitives instead of raw string manipulation.
Helpers such as {name}`System.FilePath.join` take platform-specific rules for absolute paths into account, {name}`System.FilePath.pathSeparator` contains the appropriate path separator for the current platform, and {name}`System.FilePath.exeExtension` contains any necessary extension for executable files.
Avoid hard-coding these rules.

:::

複数のシステムで可能な限り互換性のある Lean コードを書くには、生の文字列操作の代わりに Lean のパス操作プリミティブを使用すると便利です。 {name}`System.FilePath.join` のような補助関数は絶対パスのプラットフォーム固有の規則を考慮し、 {name}`System.FilePath.pathSeparator` は現在のプラットフォームに適切なパス区切り文字を保持し、 {name}`System.FilePath.exeExtension` は実行ファイルに必要な拡張子を保持します。これらの規則をハードコードすることは避けてください。

:::comment
There is an instance of the {lean}`Div` type class for {name System.FilePath}`FilePath` which allows the slash operator to be used to concatenate paths.

:::

{name System.FilePath}`FilePath` の {lean}`Div` 型クラスのインスタンスがあり、スラッシュ演算子を使ってパスを連結することができます。

{docstring System.FilePath}

{docstring System.mkFilePath}

{docstring System.FilePath.join}

{docstring System.FilePath.normalize}

{docstring System.FilePath.isAbsolute}

{docstring System.FilePath.isRelative}

{docstring System.FilePath.parent}

{docstring System.FilePath.components}

{docstring System.FilePath.fileName}

{docstring System.FilePath.fileStem}

{docstring System.FilePath.extension}

{docstring System.FilePath.addExtension}

{docstring System.FilePath.withExtension}

{docstring System.FilePath.withFileName}

{docstring System.FilePath.pathSeparator}

{docstring System.FilePath.pathSeparators}

{docstring System.FilePath.extSeparator}

{docstring System.FilePath.exeExtension}

:::comment
# Interacting with the Filesystem
:::

# ファイルシステムの対話（Interacting with the Filesystem）


:::comment
Some operations on paths consult the filesystem.

:::

パスに対するいくつかの操作はファイルシステムを参照します。

{docstring IO.FS.Metadata}

{docstring System.FilePath.metadata}

{docstring System.FilePath.pathExists}

{docstring System.FilePath.isDir}

{docstring IO.FS.DirEntry}

{docstring IO.FS.DirEntry.path}

{docstring System.FilePath.readDir}

{docstring System.FilePath.walkDir}

{docstring IO.FileRight}

{docstring IO.FileRight.flags}

{docstring IO.setAccessRights}

{docstring IO.FS.removeFile}

{docstring IO.FS.rename}

{docstring IO.FS.removeDir}

{docstring IO.FS.lines}

{docstring IO.FS.withTempFile}

{docstring IO.FS.createDirAll}

{docstring IO.FS.writeBinFile}

{docstring IO.FS.withFile}

{docstring IO.FS.removeDirAll}

{docstring IO.FS.createTempFile}

{docstring IO.FS.readFile}

{docstring IO.FS.realPath}

{docstring IO.FS.writeFile}

{docstring IO.FS.readBinFile}

{docstring IO.FS.createDir}

:::comment
# Standard I/O
:::

# 標準 I/O（Standard I/O）

%%%
tag := "stdio"
%%%

:::comment
On operating systems that are derived from or inspired by Unix, {deftech}_standard input_, {deftech}_standard output_, and {deftech}_standard error_ are the names of three streams that are available in each process.
Generally, programs are expected to read from standard input, write ordinary output to the standard output, and error messages to the standard error.
By default, standard input receives input from the console, while standard output and standard error output to the console, but all three are often redirected to or from pipes or files.

:::

Unix から派生した、または Unix に影響を受けたオペレーティングシステムでは、各プロセスで利用可能な3つのストリームに {deftech}_標準入力_ （standard input）・ {deftech}_標準出力_ （standard output）・ {deftech}_標準エラー_ （standard エラー）の名前がついています。一般的に、プログラムは標準入力から読み、標準出力に通常の出力を書き、標準エラーにエラーメッセージを書き込むことが期待されています。デフォルトでは、標準入力はコンソールからの入力を受け取り、標準出力と標準エラーに出力を行いますが、3つともパイプやファイルにリダイレクトされることが多いです。

:::comment
Rather than providing direct access to the operating system's standard I/O facilities, Lean wraps them in {name IO.FS.Stream}`Stream`s.
Additionally, the {lean}`IO` monad contains special support for replacing or locally overriding them.
This extra level of indirection makes it possible to redirect input and output within a Lean program.


:::

Lean はオペレーティングシステムの標準 I/O 機能への直接アクセスを提供するのではなく、 {name IO.FS.Stream}`Stream` でラップしています。さらに、 {lean}`IO` モナドはそれらを置き換えたり、ローカルでオーバーライドするための特別なサポートを含んでいます。この特別なレベルのインダイレクトにより、Lean プログラム内で入出力をリダイレクトすることが可能になります。

{docstring IO.getStdin}

:::comment
::example "Reading from Standard Input"
:::
:::::example "標準入力からの読み取り"
:::comment
In this example, {lean}`IO.getStdin` and {lean}`IO.getStdout` are used to get the current standard input and output, respectively.
These can be read from and written to.

:::

この例では、 {lean}`IO.getStdin` と {lean}`IO.getStdout` がそれぞれ現在の標準入力と標準出力を取得するために使用されています。これらは読み込みと書き込みが可能です。

::::ioExample
```ioLean
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "Who is it?"
  let name ← stdin.getLine
  stdout.putStr "Hello, "
  stdout.putStrLn name
```

:::comment
With this standard input:
:::

以下の標準入力に対して：

```stdin
Lean user
```
:::comment
the standard output is:
:::

標準出力は以下のようになります：

```stdout
Who is it?
Hello, Lean user
```
::::
:::::

{docstring IO.setStdin}

{docstring IO.withStdin}

{docstring IO.getStdout}

{docstring IO.setStdout}

{docstring IO.withStdout}

{docstring IO.getStderr}

{docstring IO.setStderr}

{docstring IO.withStderr}

{docstring IO.FS.withIsolatedStreams}

:::::keepEnv
:::comment
::example "Redirecting Standard I/O to Strings"
:::
::::example "標準 I/O から文字列へのリダイレクト"
:::comment
The {lean}`countdown` function counts down from a specified number, writing its progress to standard output.
Using `IO.FS.withIsolatedStreams`, this output can be redirected to a string.

:::



```lean (name := countdown)
def countdown : Nat → IO Unit
  | 0 =>
    IO.println "Blastoff!"
  | n + 1 => do
    IO.println s!"{n + 1}"
    countdown n

def runCountdown : IO String := do
  let (output, ()) ← IO.FS.withIsolatedStreams (countdown 10)
  return output

#eval runCountdown
```

:::comment
Running {lean}`countdown` yields a string that contains the output:
:::

{lean}`countdown` を実行すると、出力を含む文字列が得られます：

```leanOutput countdown
"10\n9\n8\n7\n6\n5\n4\n3\n2\n1\nBlastoff!\n"
```
::::
:::::

:::comment
# Files and Directories
:::

# ファイルとディレクトリ（Files and Directories）


{docstring IO.currentDir}

{docstring IO.appPath}

{docstring IO.appDir}
