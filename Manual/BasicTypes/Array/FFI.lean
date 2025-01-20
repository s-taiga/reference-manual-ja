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
tag := "array-ffi"
%%%

::::ffi "lean_string_object" kind := type
```
typedef struct {
    lean_object   m_header;
    size_t        m_size;
    size_t        m_capacity;
    lean_object * m_data[];
} lean_array_object;
```
:::comment
The representation of arrays in C. See {ref "array-runtime"}[the description of run-time {name}`Array`s] for more details.
:::

C における配列表現。詳しくは {ref "array-runtime"}[ランタイムにおける {name}`Array` についての説明] を参照してください。

::::

::::ffi "lean_is_array"
````
bool lean_is_array(lean_object * o)
````

:::comment
Returns `true` if `o` is an array, or `false` otherwise.
:::

`o` が配列であれば `true` を、そうでない場合は `false` を返します。

::::

::::ffi "lean_to_array"
````
lean_array_object * lean_to_array(lean_object * o)
````
:::comment
Performs a runtime check that `o` is indeed an array. If `o` is not an array, an assertion fails.
:::

`o` が本当に配列であるかどうかを実行時にチェックします。`o` が配列でない場合、アサートが失敗します。

::::


:::planned 158
 * Complete C API for {lean}`Array`
:::
