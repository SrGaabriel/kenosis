import Kenosis.Codec
import Kenosis.Utils
import Kenosis.Utf

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

def JsonWriter.run {α : Type} (w : JsonWriter α) : String :=
  let (_, s) := w { buffer := "" }
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
  putFloat f := write (toString f)
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
  | num (n : Float)
  | str (s : String)
  | arr (xs : List JsonValue)
  | obj (fields : List (String × JsonValue))
  deriving Repr, Inhabited

abbrev JsonReader (α : Type) := UtfReader α
abbrev JsonError := ReaderError

def JsonReader.run (input : String) (r : JsonReader α) : Except JsonError α :=
  match r { input, pos := 0 } with
  | .ok (a, _) => .ok a
  | .error e => .error e

mutual
  partial def parseValue : JsonReader JsonValue := do
    skipWhitespace
    let c? ← peek
    match c? with
    | some '"' => JsonValue.str <$> parseStringLiteral
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
      let key ← parseStringLiteral
      expectChar ':'
      let value ← parseValue
      let rec go (acc : List (String × JsonValue)) : JsonReader (List (String × JsonValue)) := do
        skipWhitespace
        let c? ← peek
        match c? with
        | some ',' => do
          advance
          let k ← parseStringLiteral
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
    | JsonValue.num n =>
      if n >= 0 && n == n.floor then
        pure n.toUInt64.toNat
      else failJson "expected non-negative integer"
    | _ => failJson "expected number"

  getInt := do
    let v ← getValue
    match v with
    | JsonValue.num n =>
      if n == n.floor then
        if n >= 0 then
          pure n.toUInt64.toNat
        else
          pure (-((-n).toUInt64.toNat : Int))
      else failJson "expected integer"
    | _ => failJson "expected number"

  getInt64 := do
    let v ← getValue
    match v with
    | JsonValue.num n =>
      if n == n.floor then
        if n >= 0 then
          pure (Int64.ofNat n.toUInt64.toNat)
        else
          pure (-Int64.ofNat (-n).toUInt64.toNat)
      else failJson "expected integer"
    | _ => failJson "expected number"

  getFloat := do
    let v ← getValue
    match v with
    | JsonValue.num n => pure n
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