import Kenosis.Value
import Std.Data.HashMap.Raw

namespace Kenosis.Json

open Std

inductive ParseError where
  | unexpectedEof : ParseError
  | unexpectedChar : Char → ParseError
  | expectedChar : (expected : Char) → (got : Char) → ParseError
  | expectedDigit : ParseError
  | invalidEscape : Char → ParseError
  | invalidHexDigit : Char → ParseError
  | expectedArrayEnd : Char → ParseError
  | expectedObjectEnd : Char → ParseError
  | trailingContent : ParseError
  deriving Repr, Inhabited, BEq

instance : ToString ParseError where
  toString
    | .unexpectedEof => "Unexpected end of input"
    | .unexpectedChar c => s!"Unexpected character: '{c}'"
    | .expectedChar expected got => s!"Expected '{expected}', got '{got}'"
    | .expectedDigit => "Expected digit"
    | .invalidEscape c => s!"Invalid escape sequence: \\{c}"
    | .invalidHexDigit c => s!"Invalid hex digit: '{c}'"
    | .expectedArrayEnd c => s!"Expected ',' or ']', got '{c}'"
    | .expectedObjectEnd c => s!"Expected ',' or '}}', got '{c}'"
    | .trailingContent => "Unexpected characters after JSON value"

structure ParseState where
  input : String
  pos : Nat
  deriving Repr, Inhabited

inductive ParseResult (α : Type) where
  | ok : α → ParseState → ParseResult α
  | error : ParseError → Nat → ParseResult α
  deriving Repr

instance : Inhabited (ParseResult α) where
  default := ParseResult.error .unexpectedEof 0

def Parser (α : Type) := ParseState → ParseResult α

instance : Inhabited (Parser α) where
  default := fun s => ParseResult.error .unexpectedEof s.pos

instance : Monad Parser where
  pure a := fun s => ParseResult.ok a s
  bind p f := fun s =>
    match p s with
    | ParseResult.ok a s' => f a s'
    | ParseResult.error e pos => ParseResult.error e pos

instance : MonadExceptOf ParseError Parser where
  throw e := fun s => ParseResult.error e s.pos
  tryCatch p handler := fun s =>
    match p s with
    | ParseResult.ok a s' => ParseResult.ok a s'
    | ParseResult.error e _ => handler e s

def getState : Parser ParseState := fun s => ParseResult.ok s s

def setState (s : ParseState) : Parser Unit := fun _ => ParseResult.ok () s

def isEof : Parser Bool := do
  let s ← getState
  pure (s.pos >= s.input.length)

def peek? : Parser (Option Char) := do
  let s ← getState
  if s.pos >= s.input.length then
    pure none
  else
    pure (some (s.input.toList[s.pos]!))

def next : Parser Char := do
  let s ← getState
  if s.pos >= s.input.length then
    throw ParseError.unexpectedEof
  else
    let c := s.input.toList[s.pos]!
    setState { s with pos := s.pos + c.utf8Size }
    pure c

partial def skipWhitespace : Parser Unit := do
  let c? ← peek?
  match c? with
  | some ' ' | some '\n' | some '\r' | some '\t' =>
    let _ ← next
    skipWhitespace
  | _ => pure ()

def expect (expected : Char) : Parser Unit := do
  let c ← next
  if c != expected then
    throw (ParseError.expectedChar expected c)

def expectString (expected : String) : Parser Unit := do
  for c in expected.toList do
    expect c

def parseNull : Parser Kenosis.Value := do
  expectString "null"
  pure Kenosis.Value.null

def parseBool : Parser Kenosis.Value := do
  let c ← next
  if c == 't' then
    expectString "rue"
    pure (Kenosis.Value.bool true)
  else if c == 'f' then
    expectString "alse"
    pure (Kenosis.Value.bool false)
  else
    throw (ParseError.unexpectedChar c)

def digitValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat) else none

def hexDigitValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseHexEscape : Parser Char := do
  let mut value : Nat := 0
  for _ in [0:4] do
    let c ← next
    match hexDigitValue c with
    | some d => value := value * 16 + d
    | none => throw (ParseError.invalidHexDigit c)
  pure (Char.ofNat value)

partial def parseString : Parser String := do
  expect '"'
  let mut result : String := ""

  repeat do
    let c ← next
    if c == '"' then
      break
    else if c == '\\' then
      let escaped ← next
      let unescaped ← match escaped with
        | '"' => pure '"'
        | '\\' => pure '\\'
        | '/' => pure '/'
        | 'b' => pure '\x08'
        | 'f' => pure '\x0C'
        | 'n' => pure '\n'
        | 'r' => pure '\r'
        | 't' => pure '\t'
        | 'u' => parseHexEscape
        | _ => throw (ParseError.invalidEscape escaped)
      result := result.push unescaped
    else
      result := result.push c

  pure result

def parseStringValue : Parser Kenosis.Value := do
  let s ← parseString
  pure (Kenosis.Value.str s)

partial def parseNumber : Parser Kenosis.Value := do
  let c? ← peek?
  let negative ← match c? with
    | some '-' => let _ ← next; pure true
    | _ => pure false

  let mut intPart : Int := 0
  let mut hasDigits := false

  repeat do
    let c? ← peek?
    match c? with
    | some c =>
      match digitValue c with
      | some d =>
        let _ ← next
        intPart := intPart * 10 + d
        hasDigits := true
      | none => break
    | none => break

  if !hasDigits then
    throw ParseError.expectedDigit

  let c? ← peek?
  match c? with
  | some '.' =>
    let _ ← next
    repeat do
      let c? ← peek?
      match c? with
      | some c =>
        if digitValue c |>.isSome then
          let _ ← next
        else break
      | none => break
  | _ => pure ()

  let c? ← peek?
  match c? with
  | some 'e' | some 'E' =>
    let _ ← next
    let c? ← peek?
    match c? with
    | some '+' | some '-' => let _ ← next
    | _ => pure ()
    repeat do
      let c? ← peek?
      match c? with
      | some c =>
        if digitValue c |>.isSome then
          let _ ← next
        else break
      | none => break
  | _ => pure ()

  let value := if negative then -intPart else intPart
  if value >= 0 then
    pure (Kenosis.Value.nat value.toNat)
  else
    pure (Kenosis.Value.int value)

mutual
  partial def parseValue_ : Parser Kenosis.Value := do
    skipWhitespace
    let c? ← peek?
    match c? with
    | some 'n' => parseNull
    | some 't' | some 'f' => parseBool
    | some '"' => parseStringValue
    | some '[' => parseArray
    | some '{' => parseObject
    | some '-' => parseNumber
    | some c =>
      if digitValue c |>.isSome then
        parseNumber
      else
        throw (ParseError.unexpectedChar c)
    | none => throw ParseError.unexpectedEof

  partial def parseArray : Parser Kenosis.Value := do
    expect '['
    skipWhitespace
    let c? ← peek?
    match c? with
    | some ']' =>
      let _ ← next
      pure (Kenosis.Value.list [])
    | _ =>
      let mut elements : List Kenosis.Value := []
      repeat do
        let elem ← parseValue_
        elements := elements ++ [elem]
        skipWhitespace
        let c? ← peek?
        match c? with
        | some ',' =>
          let _ ← next
          skipWhitespace
        | some ']' =>
          let _ ← next
          break
        | some c => throw (ParseError.expectedArrayEnd c)
        | none => throw ParseError.unexpectedEof
      pure (Kenosis.Value.list elements)

  partial def parseObject : Parser Kenosis.Value := do
    expect '{'
    skipWhitespace
    let c? ← peek?
    match c? with
    | some '}' =>
      let _ ← next
      pure (Kenosis.Value.obj {})
    | _ =>
      let mut entries : HashMap.Raw String Kenosis.Value := {}
      repeat do
        skipWhitespace
        let key ← parseString
        skipWhitespace
        expect ':'
        let value ← parseValue_
        entries := entries.insert key value
        skipWhitespace
        let c? ← peek?
        match c? with
        | some ',' =>
          let _ ← next
          skipWhitespace
        | some '}' =>
          let _ ← next
          break
        | some c => throw (ParseError.expectedObjectEnd c)
        | none => throw ParseError.unexpectedEof
      pure (Kenosis.Value.obj entries)
end

structure ParseFailure where
  error : ParseError
  position : Nat
  deriving Repr, Inhabited, BEq

instance : ToString ParseFailure where
  toString f := s!"Parse error at position {f.position}: {f.error}"

def runParser (p : Parser α) (input : String) : Except ParseFailure α :=
  let state : ParseState := { input := input, pos := 0 }
  match p state with
  | ParseResult.ok a _ => Except.ok a
  | ParseResult.error e pos => Except.error { error := e, position := pos }

def Json.parseValue (input : String) : Except ParseFailure Kenosis.Value := do
  runParser (do
    let value ← parseValue_
    skipWhitespace
    let eof ← isEof
    if !eof then
      throw ParseError.trailingContent
    pure value
  ) input

def Json.parseValue? (input : String) : Option Kenosis.Value :=
  match Json.parseValue input with
  | Except.ok v => some v
  | Except.error _ => none

end Kenosis.Json
