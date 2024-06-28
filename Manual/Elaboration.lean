import Verso.Genre.Manual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Elaboration, Evaluation, and Compilation" =>

Outline:

 * Describe the roles of the kernel, the interpreter, the compiler, the elaborator, and how they interact
 * Sketch the pipeline (parser -> command elaborator (with macro expansion) -> term elaborator (with macro expansion) -> ...
