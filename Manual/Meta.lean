import Lean.Elab.Command
import Lean.Elab.InfoTree

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import Verso.Genre.Manual
import Verso.Code

import SubVerso.Highlighting

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code
open SubVerso.Highlighting Highlighted

namespace Manual

@[role_expander versionString]
def versionString : RoleExpander
  | #[], #[] => do pure #[← ``(Verso.Doc.Inline.text $(quote Lean.versionString))]
  | _, _ => throwError "Unexpected arguments"

def parserInputString [Monad m] [MonadFileMap m] (str : TSyntax `str) : m String := do
  let preString := (← getFileMap).source.extract 0 (str.raw.getPos?.getD 0)
  let mut code := ""
  let mut iter := preString.iter
  while !iter.atEnd do
    if iter.curr == '\n' then code := code.push '\n'
    else
      for _ in [0:iter.curr.utf8Size] do
        code := code.push ' '
    iter := iter.next
  code := code ++ str.getString
  return code

def Block.lean : Block where
  name := `Manual.lean

structure LeanBlockConfig where
  «show» : Option Bool := none
  keep : Option Bool := none
  name : Option Name := none
  error : Option Bool := none

def LeanBlockConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LeanBlockConfig :=
  LeanBlockConfig.mk <$> .named `show .bool true <*> .named `keep .bool true <*> .named `name .name true <*> .named `error .bool true

@[code_block_expander lean]
def lean : CodeBlockExpander
  | args, str => do
    let config ← LeanBlockConfig.parse.run args

    let altStr ← parserInputString str

    let ictx := Parser.mkInputContext altStr (← getFileName)
    let cctx : Command.Context := { fileName := ← getFileName, fileMap := FileMap.ofString altStr, tacticCache? := none, snap? := none, cancelTk? := none}
    let mut cmdState : Command.State := {env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes := [{header := ""}, {header := ""}]}
    let mut pstate := {pos := 0, recovering := false}
    let mut cmds := #[]

    repeat
      let scope := cmdState.scopes.head!
      let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
      let (cmd, ps', messages) := Parser.parseCommand ictx pmctx pstate cmdState.messages
      cmds := cmds.push cmd
      pstate := ps'
      cmdState := {cmdState with messages := messages}


      cmdState ← withInfoTreeContext (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `Manual.Meta.lean, stx := cmd})) do
        match (← liftM <| EIO.toIO' <| (Command.elabCommand cmd cctx).run cmdState) with
        | Except.error e => logError e.toMessageData; return cmdState
        | Except.ok ((), s) => return s

      if Parser.isTerminalCommand cmd then break

    let origEnv ← getEnv
    try
      setEnv cmdState.env
      for t in cmdState.infoState.trees do
        pushInfoTree t

      match config.error with
      | none =>
        for msg in cmdState.messages.toArray do
          logMessage msg
      | some true =>
        if cmdState.messages.hasErrors then
          for msg in cmdState.messages.errorsToWarnings.toArray do
            logMessage msg
        else
          throwErrorAt str "Error expected in code block, but none occurred"
      | some false =>
        for msg in cmdState.messages.toArray do
          logMessage msg
        if cmdState.messages.hasErrors then
          throwErrorAt str "No error expected in code block, one occurred"

      let mut hls := Highlighted.empty
      for cmd in cmds do
        hls := hls ++ (← highlight cmd cmdState.messages.toArray cmdState.infoState.trees)

      if config.show.getD true then
        pure #[← `(Block.other {Block.lean with data := ToJson.toJson $(quote hls)} #[Block.code $(quote str.getString)])]
      else
        pure #[]
    finally
      if !config.keep.getD true then setEnv origEnv

@[block_extension lean]
def lean.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        pure <| hl.blockHtml "exercises"


inductive FFIDocType where
  | function
  | type
deriving DecidableEq, Repr, ToJson, FromJson

open Syntax in
open FFIDocType in
instance : Quote FFIDocType where
  quote
    | .function => mkCApp ``function #[]
    | .type => mkCApp ``type #[]

def FFIDocType.describe : FFIDocType → String
  | .function => "function"
  | .type => "type"

structure FFIConfig where
  name : String
  kind : FFIDocType := .function

def FFIConfig.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m FFIConfig :=
  FFIConfig.mk <$> .positional `name .string <*> ((·.getD .function) <$> .named `kind kind true)
where
  kind : ValDesc m FFIDocType := {
    description := m!"{true} or {false}"
    get := fun
      | .name b => open FFIDocType in do
        let b' ← liftM <| realizeGlobalConstNoOverloadWithInfo b

        if b' == ``function then pure .function
        else if b' == ``type then pure .type
        else throwErrorAt b "Expected 'true' or 'false'"
      | other => throwError "Expected Boolean, got {repr other}"
  }

def Block.ffi : Block where
  name := `Manual.ffi

@[directive_expander ffi]
def ffi : DirectiveExpander
  | args, blocks => do
    let config : FFIConfig ← FFIConfig.parse.run args
    if h : blocks.size = 0 then
      throwError "Expected at least one block"
    else
      let firstBlock := blocks[0]
      let moreBlocks := blocks.extract 1 blocks.size
      let `<low|(Verso.Syntax.codeblock (column ~_col) ~_open ~_args ~(.atom _info contents) ~_close )> := firstBlock
        | throwErrorAt firstBlock "Expected code block"
      let body ← moreBlocks.mapM elabBlock
      pure #[← `(Block.other {Block.ffi with data := ToJson.toJson ($(quote config.name), $(quote config.kind), $(quote contents))} #[$body,*])]

@[block_extension ffi]
def ffi.descr : BlockDescr where
  traverse id info _ := do
    let .ok (name, _declType, _signature) := FromJson.fromJson? (α := String × FFIDocType × String) info
      | do logError "Failed to deserialize FFI doc data"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name
    Index.addEntry id {term := Doc.Inline.code name}
    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (_name, ffiType, signature) := FromJson.fromJson? (α := String × FFIDocType × String) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize FFI doc data"; pure .empty
      let sig : Html := {{<pre>{{signature}}</pre>}}

      let (_, _, xref) ← read
      let idAttr :=
        if let some (_, htmlId) := xref.externalTags.find? id then
          #[("id", htmlId)]
        else #[]


      return {{
        <div class="namedocs" {{idAttr}}>
          <span class="label">"FFI " {{ffiType.describe}}</span>
          <pre class="signature">{{sig}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  toTeX := some <| fun _goI goB _ _ contents =>
    contents.mapM goB -- TODO
