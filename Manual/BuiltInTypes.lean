import Verso.Genre.Manual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

example := Char

#doc (Manual) "Built-In Types" =>

Lean includes a number of built-in datatypes that are specially supported by the compiler.
Some additionally have special support in the kernel.

# Natural Numbers

# Fixed-Precision Integer Types



# Characters

{docstring Char}

## Syntax

## Logical Model



## Run-Time Representation

In monomorphic contexts, characters are represented as 32-bit immediate values. In other words, a field of a datatype or structure of type `Char` does not require indirection to access. In polymorphic contexts, characters are boxed.


## API Reference

### Character Classes

{docstring Char.isAlpha}

{docstring Char.isAlphanum}

{docstring Char.isDigit}

{docstring Char.isLower}

{docstring Char.isUpper}

{docstring Char.isWhitespace}

# Strings


{docstring String}

## Syntax

Lean has two kinds of string literals: ordinary string literals and raw string literals.


- Gaps
- Raw strings
- Valid escape codes

## Run-Time Representation

Strings are represented as arrays of bytes, encoded in UTF-8.

## Logical Model

The logical model of strings in Lean is as a structure that contains a single field, which is a list of characters.

## API Reference

### Positions

{docstring String.Pos}

### Iterators

{docstring String.Iterator}

{docstring String.iter}

{docstring String.Iterator.hasNext}

{docstring String.Iterator.next}

{docstring String.Iterator.atEnd}

# Arrays
