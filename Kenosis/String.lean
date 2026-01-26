import Kenosis.Utils

namespace Kenosis.String

inductive StringError where
  | unexpectedEof (expected : String)
  | unexpectedChar (expected : String) (got : Char) (pos : Nat)
  | unexpectedToken (expected : String) (got : String) (pos : Nat)
  | invalidEscape (char : Char) (pos : Nat)
  | invalidNumber (pos : Nat)
  | trailingContent (pos : Nat)
  | custom (msg : String) (pos : Nat)
  deriving Repr, BEq
  
instance : ToString StringError where
  toString
    | .unexpectedEof expected => s!"unexpected end of input, expected {expected}"
    | .unexpectedChar expected got pos => s!"at position {pos}: expected {expected}, got '{got}'"
    | .unexpectedToken expected got pos => s!"at position {pos}: expected {expected}, got '{got}'"
    | .invalidEscape c pos => s!"at position {pos}: invalid escape sequence '\\{c}'"
    | .invalidNumber pos => s!"at position {pos}: invalid number"
    | .trailingContent pos => s!"at position {pos}: trailing content after JSON value"
    | .custom msg pos => s!"at position {pos}: {msg}"

structure WriterState where
  buffer : String
  deriving Inhabited

def StringWriter (_β : Type) (α : Type) := WriterState → (α × WriterState)

instance (β : Type) : Monad (StringWriter β) where
  pure a := fun s => (a, s)
  bind m f := fun s =>
    let (a, s') := m s
    f a s'

def StringWriter.run {β : Type} (w : StringWriter β Unit) : String :=
  let ((), s) := w { buffer := "" }
  s.buffer

def write (str : String) {β : Type} : StringWriter β Unit := fun s =>
  ((), { buffer := s.buffer ++ str })
  
def writeListWith {β : Type} (sep : String) (elems : List (StringWriter β Unit)) : StringWriter β Unit :=
  match elems with
  | [] => pure ()
  | [e] => e
  | e :: es => do
    e
    es.forM fun elem => do
      write sep
      elem
      
def writeEscapedString {β : Type} (s : String) : StringWriter β Unit := do
  write "\""
  write (escapeString s)
  write "\""

structure ReaderState where
  input : String
  pos : String.Pos.Raw
  deriving Inhabited

abbrev StringReader (α : Type) := ReaderState → Except StringError (α × ReaderState)

instance : Monad StringReader where
  pure a := fun s => .ok (a, s)
  bind m f := fun s =>
    match m s with
    | .ok (a, s') => f a s'
    | .error e => .error e

instance : MonadExceptOf StringError StringReader where
  throw e := fun _ => .error e
  tryCatch m handler := fun s =>
    match m s with
    | .ok result => .ok result
    | .error e => handler e s

def StringReader.run (input : String) (r : StringReader α) : Except StringError α :=
  match r { input, pos := 0 } with
  | .ok (a, _) => .ok a
  | .error e => .error e

def getPos : StringReader Nat := fun s => .ok (s.pos.byteIdx, s)

def isEof : StringReader Bool := fun s => .ok (s.pos >= s.input.rawEndPos, s)

def peek : StringReader (Option Char) := fun s =>
  if s.pos < s.input.rawEndPos then
    .ok (some (String.Pos.Raw.get s.input s.pos), s)
  else
    .ok (none, s)

def advance : StringReader Unit := fun s =>
  .ok ((), { s with pos := String.Pos.Raw.next s.input s.pos })

def consume : StringReader Char := fun s =>
  if s.pos < s.input.rawEndPos then
    let c := String.Pos.Raw.get s.input s.pos
    .ok (c, { s with pos := String.Pos.Raw.next s.input s.pos })
  else
    .error (.unexpectedEof "character")

partial def skipWhitespace : StringReader Unit := do
  let c? ← peek
  match c? with
  | some ' ' | some '\n' | some '\r' | some '\t' => do
    advance
    skipWhitespace
  | _ => pure ()

def expectChar (expected : Char) : StringReader Unit := do
  skipWhitespace
  let c ← consume
  if c == expected then pure ()
  else do
    let pos ← getPos
    throw (.unexpectedChar s!"'{expected}'" c pos)

def expectString (expected : String) : StringReader Unit := do
  let rec go (chars : List Char) : StringReader Unit :=
    match chars with
    | [] => pure ()
    | c :: cs => do
      let got ← consume
      if got != c then do
        let pos ← getPos
        throw (.unexpectedChar s!"'{c}' in \"{expected}\"" got pos)
      go cs
  go expected.toList

end Kenosis.String