import Lean.Elab.Command
import Lean.Elab.InfoTree

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import Verso.Genre.Manual
import Verso.Code

import SubVerso.Highlighting

import Manual.Meta.Figure

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

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

initialize leanOutputs : EnvExtension (NameMap (List (MessageSeverity × String))) ←
  registerEnvExtension (pure {})

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

      if let some name := config.name then
        let msgs ← cmdState.messages.toList.mapM fun msg => do

          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let txt := withNewline <| head ++ (← msg.data.toString)

          pure (msg.severity, txt)
        modifyEnv (leanOutputs.modifyState · (·.insert name msgs))

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
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str


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
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.blockHtml "examples"

def Block.leanOutput : Block where
  name := `Manual.leanOutput

structure LeanOutputConfig where
  name : Ident
  «show» : Bool := true
  severity : Option MessageSeverity
  summarize : Bool
  whitespace : WhitespaceMode

def LeanOutputConfig.parser [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LeanOutputConfig :=
  LeanOutputConfig.mk <$>
    .positional `name output <*>
    ((·.getD true) <$> .named `show .bool true) <*>
    .named `severity sev true <*>
    ((·.getD false) <$> .named `summarize .bool true) <*>
    ((·.getD .exact) <$> .named `whitespace ws true)
where
  output : ValDesc m Ident := {
    description := "output name",
    get := fun
      | .name x => pure x
      | other => throwError "Expected output name, got {repr other}"
  }
  opt {α} (p : ArgParse m α) : ArgParse m (Option α) := (some <$> p) <|> pure none
  optDef {α} (fallback : α) (p : ArgParse m α) : ArgParse m α := p <|> pure fallback
  sev : ValDesc m MessageSeverity := {
    description := open MessageSeverity in m!"The expected severity: '{``error}', '{``warning}', or '{``information}'",
    get := open MessageSeverity in fun
      | .name b => do
        let b' ← realizeGlobalConstNoOverloadWithInfo b
        if b' == ``MessageSeverity.error then pure MessageSeverity.error
        else if b' == ``MessageSeverity.warning then pure MessageSeverity.warning
        else if b' == ``MessageSeverity.information then pure MessageSeverity.information
        else throwErrorAt b "Expected '{``error}', '{``warning}', or '{``information}'"
      | other => throwError "Expected severity, got {repr other}"
  }
  ws : ValDesc m WhitespaceMode := {
    description := open WhitespaceMode in m!"The expected whitespace mode: '{``exact}', '{``normalized}', or '{``lax}'",
    get := open WhitespaceMode in fun
      | .name b => do
        let b' ← realizeGlobalConstNoOverloadWithInfo b
        if b' == ``WhitespaceMode.exact then pure WhitespaceMode.exact
        else if b' == ``WhitespaceMode.normalized then pure WhitespaceMode.normalized
        else if b' == ``WhitespaceMode.lax then pure WhitespaceMode.lax
        else throwErrorAt b "Expected '{``exact}', '{``normalized}', or '{``lax}'"
      | other => throwError "Expected whitespace mode, got {repr other}"
  }

defmethod Lean.NameMap.getOrSuggest [Monad m] [MonadInfoTree m] [MonadError m]
    (map : NameMap α) (key : Ident) : m α := do
  match map.find? key.getId with
  | some v => pure v
  | none =>
    for (n, _) in map do
      if FuzzyMatching.fuzzyMatch key.getId.toString n.toString then
        Suggestion.saveSuggestion key n.toString n.toString
    throwErrorAt key "'{key}' not found - options are {map.toList.map (·.fst)}"

open Syntax (mkCApp) in
open MessageSeverity in
instance : Quote MessageSeverity where
  quote
    | .error => mkCApp ``error #[]
    | .information => mkCApp ``information #[]
    | .warning => mkCApp ``warning #[]

@[code_block_expander leanOutput]
def leanOutput : CodeBlockExpander
 | args, str => do
    let config ← LeanOutputConfig.parser.run args
    let msgs : List (MessageSeverity × String) ← leanOutputs.getState (← getEnv) |>.getOrSuggest config.name

    for (sev, txt) in msgs do
      if mostlyEqual config.whitespace str.getString txt then
        if let some s := config.severity then
          if s != sev then
            throwErrorAt str s!"Expected severity {sevStr s}, but got {sevStr sev}"
        if config.show then
          let content ← `(Block.other {Block.leanOutput with data := ToJson.toJson ($(quote sev), $(quote txt), $(quote config.summarize))} #[Block.code $(quote str.getString)])
          return #[content]
        else return #[]

    for (_, m) in msgs do
      Verso.Doc.Suggestion.saveSuggestion str (m.take 30 ++ "…") m
    throwErrorAt str "Didn't match - expected one of: {indentD (toMessageData <| msgs.map (·.2))}\nbut got:{indentD (toMessageData str.getString)}"
where
  sevStr : MessageSeverity → String
    | .error => "error"
    | .information => "information"
    | .warning => "warning"

  mostlyEqual (ws : WhitespaceMode) (s1 s2 : String) : Bool :=
    ws.apply s1.trim == ws.apply s2.trim

@[block_extension leanOutput]
def leanOutput.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok ((sev, txt, summarize) : MessageSeverity × String × Bool) =>
        let wrap html :=
          if summarize then {{<details><summary>"Expand..."</summary>{{html}}</details>}}
          else html
        pure <| wrap {{<div class={{getClass sev}}><pre>{{txt}}</pre></div>}}
where
  getClass
    | .error => "error"
    | .information => "information"
    | .warning => "warning"

def Inline.name : Inline where
  name := `Manual.name

structure NameConfig where
  full : Option Name

def NameConfig.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m NameConfig :=
  NameConfig.mk <$> ((fun _ => none) <$> .done <|> .positional `name ref <|> pure none)
where
  ref : ValDesc m (Option Name) := {
    description := m!"reference name"
    get := fun
      | .name x =>
        some <$> liftM (realizeGlobalConstNoOverloadWithInfo x)
      | other => throwError "Expected Boolean, got {repr other}"
  }


@[role_expander name]
partial def name : RoleExpander
  | args, #[arg] => do
    let cfg ← NameConfig.parse.run args
    let `(inline|code{ $name:str }) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let exampleName := name.getString.toName
    let identStx := mkIdentFrom arg (cfg.full.getD exampleName) (canonical := true)
    let _resolvedName ← withInfoTreeContext (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `Manual.Meta.name, stx := identStx})) <| realizeGlobalConstNoOverloadWithInfo identStx

    let hl : Highlighted ← constTok (cfg.full.getD exampleName) name.getString

    pure #[← `(Inline.other {Inline.name with data := ToJson.toJson $(quote hl)} #[Inline.code $(quote name.getString)])]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected arguments"
where
  constTok name str := do
    let docs ← findDocString? (← getEnv) name
    let sig := toString (← (PrettyPrinter.ppSignature name)).1
    pure <| .token ⟨.const name sig docs, str⟩

@[inline_extension name]
def name.descr : InlineDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml "examples"

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
        if let some (_, htmlId) := xref.externalTags[id]? then
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
