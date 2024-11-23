/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true


/-
#doc (Manual) "Logical Model" =>
-/
#doc (Manual) "論理モデル（Logical Model）" =>

{docstring String}

:::comment
The logical model of strings in Lean is a structure that contains a single field, which is a list of characters.
This is convenient when specifying and proving properties of string-processing functions at a low level.

:::

Lean における文字列の論理モデルは、文字のリストである1つのフィールドを含む構造体です。これは低レベルで文字列処理関数のプロパティを指定したり証明したりするときに便利です。
