import Kenosis.Codec
import Kenosis.Utils
import Kenosis.String

namespace Kenosis.Json

open Kenosis
open Kenosis.String

def writeJsonString (s : String) : StringWriter Unit := do
  write "\""
  write (escapeString s)
  write "\""

instance : Encoder StringWriter where
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

partial def parseStringContent : StringReader String := do
  let rec go (acc : String) : StringReader String := do
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
          let rec parseHex (n : Nat) (acc : UInt32) : StringReader UInt32 :=
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

def parseJsonString : StringReader String := do
  skipWhitespace
  expectChar '"'
  parseStringContent

partial def readDigits (acc : Nat) (hasDigits : Bool) : StringReader (Nat × Bool) := do
  let c? ← peek
  match c? with
  | some c =>
    if '0' ≤ c && c ≤ '9' then do
      advance
      readDigits (acc * 10 + (c.toNat - '0'.toNat)) true
    else
      pure (acc, hasDigits)
  | none => pure (acc, hasDigits)

partial def parseNumber : StringReader Float := do
  skipWhitespace
  let c? ← peek
  let negative ← match c? with
    | some '-' => do advance; pure true
    | _ => pure false

  let (intPart, hasIntDigits) ← readDigits 0 false
  if !hasIntDigits then do
    let pos ← getPos
    throw (.invalidNumber pos)

  let c? ← peek
  let (fracPart, fracDigits) ← match c? with
    | some '.' => do
      advance
      let (frac, hasFrac) ← readDigits 0 false
      if !hasFrac then do
        let pos ← getPos
        throw (.invalidNumber pos)
      let rec countDigits (n : Nat) (count : Nat) : Nat :=
        if n == 0 then count else countDigits (n / 10) (count + 1)
      let numFracDigits := if frac == 0 then 1 else countDigits frac 0
      pure (frac, numFracDigits)
    | _ => pure (0, 0)

  let c? ← peek
  let expValue ← match c? with
    | some 'e' | some 'E' => do
      advance
      let c? ← peek
      let expNeg ← match c? with
        | some '-' => do advance; pure true
        | some '+' => do advance; pure false
        | _ => pure false
      let (exp, hasExp) ← readDigits 0 false
      if !hasExp then do
        let pos ← getPos
        throw (.invalidNumber pos)
      pure (if expNeg then -(exp : Int) else exp)
    | _ => pure (0 : Int)

  let mantissa := intPart * (10 ^ fracDigits) + fracPart
  let adjustedExp := expValue - fracDigits

  let result := if adjustedExp >= 0 then
    Float.ofScientific mantissa false adjustedExp.toNat
  else
    Float.ofScientific mantissa true (-adjustedExp).toNat

  pure (if negative then -result else result)

mutual
  partial def parseValue : StringReader JsonValue := do
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

  partial def parseArray : StringReader (List JsonValue) := do
    expectChar '['
    skipWhitespace
    let c? ← peek
    match c? with
    | some ']' => do advance; pure []
    | _ => do
      let first ← parseValue
      let rec go (acc : List JsonValue) : StringReader (List JsonValue) := do
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

  partial def parseObject : StringReader (List (String × JsonValue)) := do
    expectChar '{'
    skipWhitespace
    let c? ← peek
    match c? with
    | some '}' => do advance; pure []
    | _ => do
      let key ← parseJsonString
      expectChar ':'
      let value ← parseValue
      let rec go (acc : List (String × JsonValue)) : StringReader (List (String × JsonValue)) := do
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

abbrev JsonDecoder (α : Type) := DecoderState → Except StringError (α × DecoderState)

instance : Monad JsonDecoder where
  pure a := fun s => .ok (a, s)
  bind m f := fun s =>
    match m s with
    | .ok (a, s') => f a s'
    | .error e => .error e

def JsonDecoder.run (v : JsonValue) (d : JsonDecoder α) : Except StringError α :=
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
  StringWriter.run (Serialize.serialize a)

def decode [Deserialize α] (input : String) : Except StringError α := do
  let value ← StringReader.run input parseValue
  let decoded : JsonDecoder α := @Deserialize.deserialize α _ JsonDecoder _ _
  JsonDecoder.run value decoded

def decode? [Deserialize α] (input : String) : Option α :=
  decode input |>.toOption

def decode! [Deserialize α] [Inhabited α] (input : String) : α :=
  match decode input with
  | .ok a => a
  | .error e => panic! s!"Json.decode! failed: {e}"

end Kenosis.Json
