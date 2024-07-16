import Verso.Genre.Manual

import Manual.Meta

import Manual.BuiltInTypes.String.Logical
import Manual.BuiltInTypes.String.Literals
import Manual.BuiltInTypes.String.FFI

open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true

example := Char

#doc (Manual) "Strings" =>

{include 0 Manual.BuiltInTypes.String.Logical}

# Run-Time Representation

:::figure "Memory layout of strings" (name := "stringffi")
![Memory layout of strings](/static/figures/string.svg)
:::

Strings are represented as dynamic arrays of bytes, encoded in UTF-8.
After the object header, a string contains:

: byte count

  The number of bytes that currently contain valid string data

: capacity

  The number of bytes presently allocated for the string

: length

  The length of the encoded string, which may be shorter than the byte count due to UTF-8 multibyte characters

: data

  The actual character data in the string, null-terminated

Many string functions in the Lean runtime check whether they have exclusive access to their argument by consulting the reference count in the object header.
If they do, and the string's capacity is sufficient, then the existing string can be mutated rather than allocating fresh memory.
Otherwise, a new string must be allocated.


## Performance Notes

Despite the fact that they appear to be an ordinary constructor and projection, {name}`String.mk` and {name}`String.data` take *time linear in the length of the string*.
This is because they must implement the conversions between lists of characters and packed arrays of bytes, which must necessarily visit each character.

{include 0 Manual.BuiltInTypes.String.Literals}

# API Reference

## Constructing

{docstring String.singleton}

{docstring String.append}

{docstring String.join}

{docstring String.intercalate}

## Conversions

{docstring String.toList}

{docstring String.isNat}

{docstring String.toNat?}

{docstring String.toNat!}

{docstring String.isInt}

{docstring String.toInt?}

{docstring String.toInt!}

{docstring String.toFormat}

## Properties

{docstring String.isEmpty}

{docstring String.length}

{docstring String.str}

## Positions

{docstring String.Pos}

{docstring String.Pos.isValid}

{docstring String.atEnd}

{docstring String.endPos}

{docstring String.next}

{docstring String.next'}

{docstring String.nextWhile}

{docstring String.nextUntil}

{docstring String.prev}

{docstring String.Pos.min}

## Lookups and Modifications

{docstring String.get}

{docstring String.get?}

{docstring String.get!}

{docstring String.get'}

{docstring String.extract}

{docstring String.take}

{docstring String.takeWhile}

{docstring String.takeRight}

{docstring String.takeRightWhile}

{docstring String.drop}

{docstring String.dropWhile}

{docstring String.dropRight}

{docstring String.dropRightWhile}

{docstring String.trim}

{docstring String.trimLeft}

{docstring String.trimRight}

{docstring String.removeLeadingSpaces}

{docstring String.set}

{docstring String.modify}

{docstring String.front}

{docstring String.back}

{docstring String.posOf}

{docstring String.revPosOf}

{docstring String.contains}

{docstring String.offsetOfPos}

{docstring String.replace}

{docstring String.findLineStart}

{docstring String.find}

{docstring String.revFind}


## Folds and Aggregation

{docstring String.map}

{docstring String.foldl}

{docstring String.foldr}

{docstring String.all}

{docstring String.any}

## Comparisons

{docstring String.le}

{docstring String.firstDiffPos}

{docstring String.substrEq}

{docstring String.isPrefixOf}

{docstring String.startsWith}

{docstring String.endsWith}

{docstring String.decEq}

{docstring String.hash}

## Manipulation

{docstring String.split}

{docstring String.splitOn}

{docstring String.push}

{docstring String.pushn}

{docstring String.capitalize}

{docstring String.decapitalize}

{docstring String.toUpper}

{docstring String.toLower}

## Iterators

TODO: Text that describes the usual patterns for using a string iterator, and that it should be used instead of e.g. building a GetElem instance

{docstring String.Iterator}

{docstring String.iter}

{docstring String.mkIterator}

{docstring String.Iterator.curr}

{docstring String.Iterator.hasNext}

{docstring String.Iterator.next}

{docstring String.Iterator.forward}

{docstring String.Iterator.nextn}

{docstring String.Iterator.hasPrev}

{docstring String.Iterator.prev}

{docstring String.Iterator.prevn}

{docstring String.Iterator.atEnd}

{docstring String.Iterator.toEnd}

{docstring String.Iterator.setCurr}

{docstring String.Iterator.extract}

{docstring String.Iterator.remainingToString}

{docstring String.Iterator.remainingBytes}

{docstring String.Iterator.pos}

## Substrings

TODO Substring API xref

{docstring String.toSubstring}

{docstring String.toSubstring'}

## Proof Automation

{docstring String.reduceGT}

{docstring String.reduceGE}

{docstring String.reduceBinPred}

{docstring String.reduceLT}

{docstring String.reduceLE}

{docstring String.reduceBEq}

{docstring String.reduceEq}

{docstring String.reduceAppend}

{docstring String.reduceMk}

{docstring String.reduceBoolPred}

{docstring String.reduceBNe}

{docstring String.reduceNe}

## Metaprogramming

{docstring String.toName}

{docstring String.toFileMap}

{docstring String.quote}

{docstring String.fromExpr?}

## Encodings

{docstring String.utf16PosToCodepointPos}

{docstring String.utf16PosToCodepointPosFrom}

{docstring String.codepointPosToUtf16Pos}

{docstring String.codepointPosToUtf16PosFrom}

{docstring String.getUtf8Byte}

{docstring String.utf8ByteSize}

{docstring String.utf8EncodeChar}

{docstring String.utf8DecodeChar?}

{docstring String.fromUTF8}

{docstring String.fromUTF8?}

{docstring String.fromUTF8!}

{docstring String.toUTF8}

{docstring String.validateUTF8}

{docstring String.utf16Length}

{docstring String.codepointPosToUtf8PosFrom}

{docstring String.crlfToLf}


{include 0 Manual.BuiltInTypes.String.FFI}
