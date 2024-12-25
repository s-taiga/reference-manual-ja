/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Verso.Genre Manual
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode


/-
#doc (Manual) "Recursion Example (for inclusion elsewhere)" =>
-/
#doc (Manual) "再帰の例（Recursion Example (for inclusion elsewhere)）" =>


```lean (show := false)
section
variable (n k : Nat) (mot : Nat → Sort u)
```
:::comment
::example "Recursion vs Recursors"
:::
::::example "再帰 vs 再帰子"
:::comment
Addition of natural numbers can be defined via recursion on the second argument.
This function is straightforwardly structurally recursive.
:::

自然数の足し算は、第2引数に対する再帰によって定義することができます。この関数は単純な構造的再帰です。

```lean
def add (n : Nat) : Nat → Nat
  | .zero => n
  | .succ k => .succ (add n k)
```

:::comment
Defined using {name}`Nat.rec`, it is much further from the notations that most people are used to.
:::

{name}`Nat.rec` を使って定義すると、多くの人が慣れ親しんでいる表記からかけ離れています。

```lean
def add' (n : Nat) :=
  Nat.rec (motive := fun _ => Nat)
    n
    (fun k soFar => .succ soFar)
```

:::comment
Structural recursive calls made on data that isn't the immediate child of the function parameter requires either creativity or a complex yet systematic encoding.
:::

関数パラメータの直接の子要素ではないデータに対して行われる構造的再帰呼び出しには、創造性か、複雑ですが体系的なエンコーディングのどちらかが必要です。

```lean
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
```
:::comment
One way to think about this function is as a structural recursion that flips a bit at each call, only incrementing the result when the bit is set.
:::

この関数についての1つの考え方は、呼び出すたびにビットを反転させ、ビットがセットされたときだけ結果をインクリメントする構造的再帰です。

```lean
def helper : Nat → Bool → Nat :=
  Nat.rec (motive := fun _ => Bool → Nat)
    (fun _ => 0)
    (fun _ soFar =>
      fun b =>
        (if b then Nat.succ else id) (soFar !b))

def half' (n : Nat) : Nat := helper n false
```
```lean (name := halfTest)
#eval [0, 1, 2, 3, 4, 5, 6, 7, 8].map half'
```
```leanOutput halfTest
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

:::comment
Instead of creativity, a general technique called {deftech}[course-of-values recursion] can be used.
Course-of-values recursion uses helpers that can be systematically derived for every inductive type, defined in terms of the recursor; Lean derives them automatically.
For every {lean}`Nat` {lean}`n`, the type {lean}`n.below (motive := mot)` provides a value of type {lean}`mot k` for all {lean}`k < n`, represented as an iterated {TODO}[xref sigma] dependent pair type.
The course-of-values recursor {name}`Nat.brecOn` allows a function to use the result for any smaller {lean}`Nat`.
Using it to define the function is inconvenient:
:::

創造性の代わりに、 {deftech}[累積再帰] （course-of-values recursion）と呼ばれる一般的なテクニックを使用することができます。累積再帰では、再帰子で定義されたすべての帰納型に対して体系的に導出できる補助関数を使用します；Lean はこれらを自動で導出します。すべての {lean}`Nat` {lean}`n` に対して、 {lean}`n.below (motive := mot)` 型はすべての {lean}`k < n` に対して {lean}`mot k` 型の値を提供し、繰り返された依存ペア型として表現されます。累積再帰子 {name}`Nat.brecOn` は関数が任意の小さい {lean}`Nat` に対して結果を使用することを可能にします。これを使用して関数を定義することは不便です：

```lean
noncomputable def half'' (n : Nat) : Nat :=
  Nat.brecOn n (motive := fun _ => Nat)
    fun k soFar =>
      match k, soFar with
      | 0, _ | 1, _ => 0
      | _ + 2, ⟨_, ⟨h, _⟩⟩ => h + 1
```
:::comment
The function is marked {keywordOf Lean.Parser.Command.declaration}`noncomputable` because the compiler doesn't support generating code for course-of-values recursion, which is intended for reasoning rather that efficient code.
The kernel can still be used to test the function, however:
:::

この関数は {keywordOf Lean.Parser.Command.declaration}`noncomputable` とマークされていますが、これはコンパイラが累積再帰のコード生成をサポートしていないためです。というのもこれは効率的なコードではなく推論用を意図されたものだからです。しかし、カーネルを関数のテストのために使用することができます：

```lean (name := halfTest2)
#reduce [0,1,2,3,4,5,6,7,8].map half''
```
```leanOutput halfTest2
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

:::comment
The dependent pattern matching in the body of {lean}`half''` can also be encoded using recursors (specifically, {name}`Nat.casesOn`), if necessary:
:::

必要に応じて {lean}`half''` の本体で依存パターンマッチを再帰子（具体的には {name}`Nat.casesOn` ）を使ってエンコードすることもできます：

```lean
noncomputable def half''' (n : Nat) : Nat :=
  n.brecOn (motive := fun _ => Nat)
    fun k =>
      k.casesOn
        (motive :=
          fun k' =>
            (k'.below (motive := fun _ => Nat)) →
            Nat)
        (fun _ => 0)
        (fun k' =>
          k'.casesOn
            (motive :=
              fun k'' =>
                (k''.succ.below (motive := fun _ => Nat)) →
                Nat)
            (fun _ => 0)
            (fun _ soFar => soFar.2.1.succ))
```

:::comment
This definition still works.
:::

この定義も動作します。

```lean (name := halfTest3)
#reduce [0,1,2,3,4,5,6,7,8].map half''
```
```leanOutput halfTest3
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

:::comment
However, it is now far from the original definition and it has become difficult for most people to understand.
Recursors are an excellent logical foundation, but not an easy way to write programs or proofs.
:::

しかし、もはや本来の定義からかけ離れ、多くの人にとって理解しにくいものになっています。再帰子は優れた論理的基礎ですが、プログラムや証明を書くには簡単な方法ではありません。

::::
```lean (show := false)
end
```
