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


#doc (Manual) "FFI" =>
%%%
tag := "string-ffi"
%%%


{docstring String.csize}

::::ffi "lean_string_object" kind := type
```
typedef struct {
    lean_object m_header;
    /* byte length including '\0' terminator */
    size_t      m_size;
    size_t      m_capacity;
    /* UTF8 length */
    size_t      m_length;
    char        m_data[0];
} lean_string_object;
```
:::comment
The representation of strings in C. See {ref "string-runtime"}[the description of run-time {name}`String`s] for more details.
:::

C での文字列の表現。詳細は {ref "string-runtime"}[{name}`String` のランタイムについての説明] を参照してください。

::::

::::ffi "lean_is_string"
````
bool lean_is_string(lean_object * o)
````

:::comment
Returns `true` if `o` is a string, or `false` otherwise.
:::

`o` が文字列であれば `true` を、そうでなければ `false` を返します。

::::

::::ffi "lean_to_string"
````
lean_string_object * lean_to_string(lean_object * o)
````
:::comment
Performs a runtime check that `o` is indeed a string. If `o` is not a string, an assertion fails.
:::

`o` が本当に文字列であることのランタイムチェックの実行。`o` が文字列でない場合は失敗を主張します。

:::planned 158
 * Complete C API for {lean}`String`
:::

::::
