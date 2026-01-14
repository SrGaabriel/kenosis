import Kenosis.Codec
import Kenosis.Utils

namespace Kenosis.Json

open Kenosis

structure WriterState where
  buffer : String
  deriving Inhabited

def JsonWriter (α : Type) := WriterState → (α × WriterState)

instance : Monad JsonWriter where
  pure a := fun s => (a, s)
  bind m f := fun s =>
    let (a, s') := m s
    f a s'

def JsonWriter.run (w : JsonWriter Unit) : String :=
  let ((), s) := w { buffer := "" }
  s.buffer

def write (str : String) : JsonWriter Unit := fun s =>
  ((), { buffer := s.buffer ++ str })

def writeJsonString (s : String) : JsonWriter Unit := do
  write "\""
  write (escapeString s)
  write "\""

def writeListWith (sep : String) (elems : List (JsonWriter Unit)) : JsonWriter Unit :=
  match elems with
  | [] => pure ()
  | [e] => e
  | e :: es => do
    e
    es.forM fun elem => do
      write sep
      elem

instance : Encoder JsonWriter where
  putBool b := write (if b then "true" else "false")
  putNat n := write (toString n)
  putInt n := write (toString n)
  putInt64 n := write (toString n)
  putString s := writeJsonString s
  putNull := write "null"

  putList elems := do
    write "["
    writeListWith ", " elems
    write "]"

  putObject fields := do
    write "{"
    let fieldWriters := fields.map fun (name, putValue) => do
      writeJsonString name
      write ": "
      putValue
    writeListWith ", " fieldWriters
    write "}"

  putVariant _idx name payload := do
    match payload with
    | none => writeJsonString name
    | some p => do
      write "{"
      writeJsonString name
      write ": "
      p
      write "}"

inductive JsonValue where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (xs : List JsonValue)
  | obj (fields : List (String × JsonValue))
  deriving Repr, BEq, Inhabited

inductive JsonError where
  | unexpectedEof (expected : String)
  | unexpectedChar (expected : String) (got : Char) (pos : Nat)
  | unexpectedToken (expected : String) (got : String) (pos : Nat)
  | invalidEscape (char : Char) (pos : Nat)
  | invalidNumber (pos : Nat)
  | trailingContent (pos : Nat)
  | custom (msg : String) (pos : Nat)
  deriving Repr, BEq

instance : ToString JsonError where
  toString
    | .unexpectedEof expected => s!"unexpected end of input, expected {expected}"
    | .unexpectedChar expected got pos => s!"at position {pos}: expected {expected}, got '{got}'"
    | .unexpectedToken expected got pos => s!"at position {pos}: expected {expected}, got '{got}'"
    | .invalidEscape c pos => s!"at position {pos}: invalid escape sequence '\\{c}'"
    | .invalidNumber pos => s!"at position {pos}: invalid number"
    | .trailingContent pos => s!"at position {pos}: trailing content after JSON value"
    | .custom msg pos => s!"at position {pos}: {msg}"

structure ReaderState where
  input : String
  pos : String.Pos.Raw
  deriving Inhabited

abbrev JsonReader (α : Type) := ReaderState → Except JsonError (α × ReaderState)

instance : Monad JsonReader where
  pure a := fun s => .ok (a, s)
  bind m f := fun s =>
    match m s with
    | .ok (a, s') => f a s'
    | .error e => .error e

instance : MonadExceptOf JsonError JsonReader where
  throw e := fun _ => .error e
  tryCatch m handler := fun s =>
    match m s with
    | .ok result => .ok result
    | .error e => handler e s

def JsonReader.run (input : String) (r : JsonReader α) : Except JsonError α :=
  match r { input, pos := 0 } with
  | .ok (a, _) => .ok a
  | .error e => .error e

def getPos : JsonReader Nat := fun s => .ok (s.pos.byteIdx, s)

def isEof : JsonReader Bool := fun s => .ok (s.pos >= s.input.rawEndPos, s)

def peek : JsonReader (Option Char) := fun s =>
  if s.pos < s.input.rawEndPos then
    .ok (some (String.Pos.Raw.get s.input s.pos), s)
  else
    .ok (none, s)

def advance : JsonReader Unit := fun s =>
  .ok ((), { s with pos := String.Pos.Raw.next s.input s.pos })

def consume : JsonReader Char := fun s =>
  if s.pos < s.input.rawEndPos then
    let c := String.Pos.Raw.get s.input s.pos
    .ok (c, { s with pos := String.Pos.Raw.next s.input s.pos })
  else
    .error (.unexpectedEof "character")

partial def skipWhitespace : JsonReader Unit := do
  let c? ← peek
  match c? with
  | some ' ' | some '\n' | some '\r' | some '\t' => do
    advance
    skipWhitespace
  | _ => pure ()

def expectChar (expected : Char) : JsonReader Unit := do
  skipWhitespace
  let c ← consume
  if c == expected then pure ()
  else do
    let pos ← getPos
    throw (.unexpectedChar s!"'{expected}'" c pos)

def expectString (expected : String) : JsonReader Unit := do
  let rec go (chars : List Char) : JsonReader Unit :=
    match chars with
    | [] => pure ()
    | c :: cs => do
      let got ← consume
      if got != c then do
        let pos ← getPos
        throw (.unexpectedChar s!"'{c}' in \"{expected}\"" got pos)
      go cs
  go expected.toList

partial def parseStringContent : JsonReader String := do
  let rec go (acc : String) : JsonReader String := do
    let c ← consume
    match c with
    | '"' => pure acc
    | '\\' => do
      let escaped ← consume
      let unescaped ← match escaped with
        | '"' => pure '"'
        | '\\' => pure '\\'
        | '/' => pure '/'
        | 'n' => pure '\n'
        | 'r' => pure '\r'
        | 't' => pure '\t'
        | 'b' => pure '\x08'
        | 'f' => pure '\x0C'
        | 'u' => do
          let rec parseHex (n : Nat) (acc : UInt32) : JsonReader UInt32 :=
            if n == 0 then pure acc
            else do
              let d ← consume
              let digit ← match d with
                | '0' => pure 0 | '1' => pure 1 | '2' => pure 2 | '3' => pure 3
                | '4' => pure 4 | '5' => pure 5 | '6' => pure 6 | '7' => pure 7
                | '8' => pure 8 | '9' => pure 9
                | 'a' | 'A' => pure 10 | 'b' | 'B' => pure 11
                | 'c' | 'C' => pure 12 | 'd' | 'D' => pure 13
                | 'e' | 'E' => pure 14 | 'f' | 'F' => pure 15
                | _ => do
                  let pos ← getPos
                  throw (.custom s!"invalid hex digit '{d}'" pos)
              parseHex (n - 1) (acc * 16 + digit.toUInt32)
          let code ← parseHex 4 0
          pure (Char.ofNat code.toNat)
        | _ => do
          let pos ← getPos
          throw (.invalidEscape escaped pos)
      go (acc.push unescaped)
    | c => go (acc.push c)
  go ""

def parseJsonString : JsonReader String := do
  skipWhitespace
  expectChar '"'
  parseStringContent

partial def readDigits (acc : Nat) (hasDigits : Bool) : JsonReader (Nat × Bool) := do
  let c? ← peek
  match c? with
  | some c =>
    if '0' ≤ c && c ≤ '9' then do
      advance
      readDigits (acc * 10 + (c.toNat - '0'.toNat)) true
    else
      pure (acc, hasDigits)
  | none => pure (acc, hasDigits)

partial def parseNumber : JsonReader Int := do
  skipWhitespace
  let c? ← peek
  let negative ← match c? with
    | some '-' => do advance; pure true
    | _ => pure false

  let (n, hasDigits) ← readDigits 0 false

  if !hasDigits then do
    let pos ← getPos
    throw (.invalidNumber pos)

  let c? ← peek
  match c? with
  | some '.' => do
    advance
    let _ ← readDigits 0 false
  | _ => pure ()

  let c? ← peek
  match c? with
  | some 'e' | some 'E' => do
    advance
    let c? ← peek
    match c? with
    | some '+' | some '-' => advance
    | _ => pure ()
    let _ ← readDigits 0 false
  | _ => pure ()

  if negative then pure (-(n : Int)) else pure n

mutual
  partial def parseValue : JsonReader JsonValue := do
    skipWhitespace
    let c? ← peek
    match c? with
    | some '"' => JsonValue.str <$> parseJsonString
    | some '[' => JsonValue.arr <$> parseArray
    | some '{' => JsonValue.obj <$> parseObject
    | some 't' => do expectString "true"; pure (JsonValue.bool true)
    | some 'f' => do expectString "false"; pure (JsonValue.bool false)
    | some 'n' => do expectString "null"; pure JsonValue.null
    | some c =>
      if c == '-' || ('0' ≤ c && c ≤ '9') then
        JsonValue.num <$> parseNumber
      else do
        let pos ← getPos
        throw (.unexpectedChar "JSON value" c pos)
    | none => throw (.unexpectedEof "JSON value")

  partial def parseArray : JsonReader (List JsonValue) := do
    expectChar '['
    skipWhitespace
    let c? ← peek
    match c? with
    | some ']' => do advance; pure []
    | _ => do
      let first ← parseValue
      let rec go (acc : List JsonValue) : JsonReader (List JsonValue) := do
        skipWhitespace
        let c? ← peek
        match c? with
        | some ',' => do
          advance
          let v ← parseValue
          go (v :: acc)
        | some ']' => do
          advance
          pure acc.reverse
        | some c => do
          let pos ← getPos
          throw (.unexpectedChar "',' or ']'" c pos)
        | none => throw (.unexpectedEof "']' or ','")
      go [first]

  partial def parseObject : JsonReader (List (String × JsonValue)) := do
    expectChar '{'
    skipWhitespace
    let c? ← peek
    match c? with
    | some '}' => do advance; pure []
    | _ => do
      let key ← parseJsonString
      expectChar ':'
      let value ← parseValue
      let rec go (acc : List (String × JsonValue)) : JsonReader (List (String × JsonValue)) := do
        skipWhitespace
        let c? ← peek
        match c? with
        | some ',' => do
          advance
          let k ← parseJsonString
          expectChar ':'
          let v ← parseValue
          go ((k, v) :: acc)
        | some '}' => do
          advance
          pure acc.reverse
        | some c => do
          let pos ← getPos
          throw (.unexpectedChar "',' or '}'" c pos)
        | none => throw (.unexpectedEof "'}' or ','")
      go [(key, value)]
end

structure DecoderState where
  value : JsonValue

instance : Inhabited DecoderState where
  default := { value := JsonValue.null }

abbrev JsonDecoder (α : Type) := DecoderState → Except JsonError (α × DecoderState)

instance : Monad JsonDecoder where
  pure a := fun s => .ok (a, s)
  bind m f := fun s =>
    match m s with
    | .ok (a, s') => f a s'
    | .error e => .error e

def JsonDecoder.run (v : JsonValue) (d : JsonDecoder α) : Except JsonError α :=
  match d { value := v } with
  | .ok (a, _) => .ok a
  | .error e => .error e

def getValue : JsonDecoder JsonValue := fun s => .ok (s.value, s)

def withValue (v : JsonValue) (d : JsonDecoder α) : JsonDecoder α := fun s =>
  match d { value := v } with
  | .ok (a, _) => .ok (a, s)
  | .error e => .error e

def failJson (msg : String) : JsonDecoder α := fun _ =>
  .error (.custom msg 0)

instance : Decoder JsonDecoder where
  getBool := do
    let v ← getValue
    match v with
    | JsonValue.bool b => pure b
    | _ => failJson "expected boolean"

  getNat := do
    let v ← getValue
    match v with
    | JsonValue.num n => if n >= 0 then pure n.toNat else failJson "expected non-negative number"
    | _ => failJson "expected number"

  getInt := do
    let v ← getValue
    match v with
    | JsonValue.num n => pure n
    | _ => failJson "expected number"

  getInt64 := do
    let v ← getValue
    match v with
    | JsonValue.num n =>
      let minInt64 : Int := -9223372036854775808
      let maxInt64 : Int := 9223372036854775807
      if n < minInt64 || n > maxInt64 then
        failJson s!"number {n} out of Int64 range"
      else
        pure n.toInt64
    | _ => failJson "expected number"

  getString := do
    let v ← getValue
    match v with
    | JsonValue.str s => pure s
    | _ => failJson "expected string"

  getNull := do
    let v ← getValue
    match v with
    | JsonValue.null => pure ()
    | _ => failJson "expected null"

  getList getElem := do
    let v ← getValue
    match v with
    | JsonValue.arr xs => xs.mapM fun x => withValue x getElem
    | _ => failJson "expected array"

  getOption getElem := do
    let v ← getValue
    match v with
    | JsonValue.null => pure none
    | _ => some <$> getElem

  withObject action := do
    let v ← getValue
    match v with
    | JsonValue.obj _ => action
    | _ => failJson "expected object"

  getField name action := do
    let v ← getValue
    match v with
    | JsonValue.obj fields =>
      match fields.find? (fun (k, _) => k == name) with
      | some (_, fieldValue) => withValue fieldValue action
      | none => failJson s!"missing field '{name}'"
    | _ => failJson "expected object"

  matchVariant _numCtors _byIndex byName := do
    let v ← getValue
    match v with
    | JsonValue.str tag => byName tag
    | JsonValue.obj [(tag, payload)] => withValue payload (byName tag)
    | JsonValue.obj _ => failJson "expected single-key object for variant"
    | _ => failJson "expected string or object for variant"

  fail msg := failJson msg

def encode [Serialize α] (a : α) : String :=
  JsonWriter.run (Serialize.serialize a)

def decode [Deserialize α] (input : String) : Except JsonError α := do
  let value ← JsonReader.run input parseValue
  let decoded : JsonDecoder α := @Deserialize.deserialize α _ JsonDecoder _ _
  JsonDecoder.run value decoded

def decode? [Deserialize α] (input : String) : Option α :=
  decode input |>.toOption

def decode! [Deserialize α] [Inhabited α] (input : String) : α :=
  match decode input with
  | .ok a => a
  | .error e => panic! s!"Json.decode! failed: {e}"

end Kenosis.Json
