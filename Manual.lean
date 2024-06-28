import Verso.Genre.Manual

import Manual.Intro
import Manual.Elaboration
import Manual.BuiltInTypes

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "The Lean Language Reference" =>

%%%
authors := ["Lean Developers"]
%%%

{include Manual.Intro}

{include Manual.Elaboration}

{include Manual.BuiltInTypes}


# Index
%%%
number := false
%%%

{theIndex}
