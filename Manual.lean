import Verso.Genre.Manual

import Manual.Intro
import Manual.Elaboration
import Manual.Language
import Manual.BuiltInTypes

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "The Lean Language Reference" =>

%%%
authors := ["Lean Developers"]
%%%

{include Manual.Intro}

{include Manual.Elaboration}

{include Manual.Language}

{include Manual.BuiltInTypes}


# Progress

:::progress
```namespace
String Char
```
```exceptions
String.revFindAux String.extract.go₂ String.substrEq.loop String.casesOn
String.offsetOfPosAux String.extract.go₁ String.mapAux String.firstDiffPos.loop String.utf8SetAux String.revPosOfAux String.replace.loop
String.rec String.recOn String.posOfAux String.splitAux String.foldrAux
String.splitOnAux String.intercalate.go String.anyAux String.findAux
String.utf8GetAux? String.foldlAux String.utf8GetAux
String.utf8PrevAux String.noConfusionType String.noConfusion
String.utf8ByteSize.go String.validateUTF8.loop
String.crlfToLf.go
String.fromUTF8.loop
String.one_le_csize
```

```exceptions
String.sluggify
```
:::


# Index
%%%
number := false
%%%

{theIndex}
