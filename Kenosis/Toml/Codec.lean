import Kenosis.Codec
import Kenosis.Utils
import Kenosis.Utf

namespace Kenosis.Toml

open Kenosis

structure WriterState where
  buffer : String
  currentTable : Option String
  deriving Inhabited

inductive TomlObject
  | table
  | value
  | null
  deriving Inhabited

structure TomlWriter (α : Type) where
  runState : WriterState -> (α × WriterState)
  object : TomlObject
  deriving Inhabited

instance : Monad TomlWriter where
  pure a := { runState := fun s => (a, s), object := .value }
  bind w f := {
    runState := fun s =>
      let (a, s') := w.runState s
      (f a).runState s',
    object := w.object
  }

def TomlWriter.run {α : Type} (w : TomlWriter α) : String :=
  let (_, s) := w.runState { buffer := "", currentTable := .none }
  s.buffer

def writeValue (str : String) : TomlWriter Unit :=
  { runState := fun s => ((), { s with buffer := s.buffer ++ str }), object := .value }

def writeObject (tableName : String) : TomlWriter Unit :=
  { runState := fun s => ((), { s with buffer := s.buffer ++ "\n[" ++ tableName ++ "]\n", currentTable := some tableName }), object := .table }

def writeListWith (sep : String) (elems : List (TomlWriter Unit)) : TomlWriter Unit :=
  match elems with
  | [] => pure ()
  | [e] => e
  | e :: es => do
    e
    es.forM fun elem => do
      writeValue sep
      elem

instance : Encoder TomlWriter where
  putBool b := writeValue (if b then "true" else "false")
  putNat n := writeValue (toString n)
  putInt i := writeValue (toString i)
  putInt64 i := writeValue (toString i)
  putFloat f := writeValue (toString f)
  putString s := writeValue ("\"" ++ escapeString s ++ "\"")
  putNull := { runState := fun s => ((), s), object := .null }

  putOption opt := match opt with
    | none => { runState := fun s => ((), s), object := .null }
    | some p => p

  putList elems := do
    writeValue "["
    writeListWith ", " elems
    writeValue "]"

  putObject fields := {
    runState := fun s =>
      let fields := fields.filter fun (_, valWriter) =>
        match valWriter.object with
        | TomlObject.null => false
        | _ => true
      let (values, tables) := fields.partition fun (_, valWriter) =>
        match valWriter.object with
        | TomlObject.table => false
        | _ => true
      let valueWriters := values.map fun (key, valWriter) => do
        writeValue key
        writeValue " = "
        valWriter
      let tableWriters := tables.map fun (key, valWriter) => do
        writeObject key
        valWriter
      let allWriters := valueWriters ++ tableWriters
      (writeListWith "\n" allWriters).runState s,
    object := .table
  }

  putVariant _idx name payload := do
    match payload with
    | none => writeValue name
    | some p => do
        writeValue name
        writeValue " = "
        p

inductive TomlValue where
  | bool (b : Bool)
  | num (n : Float)
  | str (s : String)
  | arr (xs : List TomlValue)
  | table (fields : List (String × TomlValue))
  deriving Inhabited

abbrev TomlReader (α : Type) := UtfReader α
abbrev TomlError := ReaderError

def TomlReader.run (input : String) (r : TomlReader α) : Except TomlError α :=
  match r { input, pos := 0 } with
  | .ok (a, _) => .ok a
  | .error e => .error e

partial def skipTomlWhitespace : TomlReader Unit := do
  let c? ← peek
  match c? with
  | some ' ' | some '\t' => do
    advance
    skipTomlWhitespace
  | _ => pure ()

partial def skipComment : TomlReader Unit := do
  let c? ← peek
  match c? with
  | some '\n' => advance
  | some '\r' => do
    advance
    let c2? ← peek
    if c2? == some '\n' then advance
  | some _ => do
    advance
    skipComment
  | none => pure ()

partial def skipToEndOfLine : TomlReader Unit := do
  let c? ← peek
  match c? with
  | some '#' => do
    advance
    skipComment
  | some '\n' => advance
  | some '\r' => do
    advance
    let c2? ← peek
    if c2? == some '\n' then advance
  | some _ => do
    let pos ← getPos
    let c ← consume
    throw (.unexpectedChar "end of line" c pos)
  | none => pure ()

partial def skipWhitespaceAndComments : TomlReader Unit := do
  let c? ← peek
  match c? with
  | some ' ' | some '\t' | some '\n' => do
    advance
    skipWhitespaceAndComments
  | some '\r' => do
    advance
    let c2? ← peek
    if c2? == some '\n' then advance
    skipWhitespaceAndComments
  | some '#' => do
    advance
    skipComment
    skipWhitespaceAndComments
  | _ => pure ()

def isTomlBareKeyChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') ||
  ('0' ≤ c && c ≤ '9') || c == '_' || c == '-'

partial def parseBareKey : TomlReader String := do
  let rec go (acc : String) : TomlReader String := do
    let c? ← peek
    match c? with
    | some c =>
      if isTomlBareKeyChar c then do
        advance
        go (acc.push c)
      else
        pure acc
    | none => pure acc
  let result ← go ""
  if result.isEmpty then do
    let pos ← getPos
    throw (.custom "expected key" pos)
  pure result

partial def parseHexDigits (n : Nat) (acc : UInt32) : TomlReader UInt32 :=
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
    parseHexDigits (n - 1) (acc * 16 + digit.toUInt32)

partial def parseBasicStringContent : TomlReader String := do
  let rec go (acc : String) : TomlReader String := do
    let c ← consume
    match c with
    | '"' => pure acc
    | '\\' => do
      let escaped ← consume
      let unescaped ← match escaped with
        | '"' => pure '"'
        | '\\' => pure '\\'
        | 'n' => pure '\n'
        | 'r' => pure '\r'
        | 't' => pure '\t'
        | 'b' => pure '\x08'
        | 'f' => pure '\x0C'
        | 'u' => do
          let code ← parseHexDigits 4 0
          pure (Char.ofNat code.toNat)
        | 'U' => do
          let code ← parseHexDigits 8 0
          pure (Char.ofNat code.toNat)
        | _ => do
          let pos ← getPos
          throw (.invalidEscape escaped pos)
      go (acc.push unescaped)
    | c => go (acc.push c)
  go ""

partial def parseLiteralStringContent : TomlReader String := do
  let rec go (acc : String) : TomlReader String := do
    let c ← consume
    match c with
    | '\'' => pure acc
    | c => go (acc.push c)
  go ""

partial def skipMultilineWhitespace : TomlReader Unit := do
  let c? ← peek
  match c? with
  | some ' ' | some '\t' | some '\n' => do
    advance
    skipMultilineWhitespace
  | some '\r' => do
    advance
    skipMultilineWhitespace
  | _ => pure ()

partial def parseMultilineBasicStringContent : TomlReader String := do
  let c? ← peek
  match c? with
  | some '\n' => advance
  | some '\r' => do
    advance
    let c2? ← peek
    if c2? == some '\n' then advance
  | _ => pure ()
  let rec go (acc : String) : TomlReader String := do
    let c ← consume
    match c with
    | '"' => do
      let c2? ← peek
      match c2? with
      | some '"' => do
        advance
        let c3? ← peek
        match c3? with
        | some '"' => do
          advance
          pure acc
        | _ => go (acc ++ "\"\"")
      | _ => go (acc.push '"')
    | '\\' => do
      let c2? ← peek
      match c2? with
      | some '\n' => do
        advance
        skipMultilineWhitespace
        go acc
      | some '\r' => do
        advance
        let c3? ← peek
        if c3? == some '\n' then advance
        skipMultilineWhitespace
        go acc
      | some ' ' | some '\t' => do
        skipMultilineWhitespace
        let c3? ← peek
        match c3? with
        | some '\n' => do
          advance
          skipMultilineWhitespace
          go acc
        | some '\r' => do
          advance
          let c4? ← peek
          if c4? == some '\n' then advance
          skipMultilineWhitespace
          go acc
        | _ => do
          let pos ← getPos
          throw (.custom "invalid escape in multiline string" pos)
      | _ => do
        let escaped ← consume
        let unescaped ← match escaped with
          | '"' => pure '"'
          | '\\' => pure '\\'
          | 'n' => pure '\n'
          | 'r' => pure '\r'
          | 't' => pure '\t'
          | 'b' => pure '\x08'
          | 'f' => pure '\x0C'
          | 'u' => do
            let code ← parseHexDigits 4 0
            pure (Char.ofNat code.toNat)
          | 'U' => do
            let code ← parseHexDigits 8 0
            pure (Char.ofNat code.toNat)
          | _ => do
            let pos ← getPos
            throw (.invalidEscape escaped pos)
        go (acc.push unescaped)
    | c => go (acc.push c)
  go ""

partial def parseMultilineLiteralStringContent : TomlReader String := do
  let c? ← peek
  match c? with
  | some '\n' => advance
  | some '\r' => do
    advance
    let c2? ← peek
    if c2? == some '\n' then advance
  | _ => pure ()
  let rec go (acc : String) : TomlReader String := do
    let c ← consume
    match c with
    | '\'' => do
      let c2? ← peek
      match c2? with
      | some '\'' => do
        advance
        let c3? ← peek
        match c3? with
        | some '\'' => do
          advance
          pure acc
        | _ => go (acc ++ "''")
      | _ => go (acc.push '\'')
    | c => go (acc.push c)
  go ""

def parseTomlString : TomlReader String := do
  skipTomlWhitespace
  let c ← consume
  match c with
  | '"' => do
    let c2? ← peek
    match c2? with
    | some '"' => do
      advance
      let c3? ← peek
      match c3? with
      | some '"' => do
        advance
        parseMultilineBasicStringContent
      | _ => pure ""
    | _ => parseBasicStringContent
  | '\'' => do
    let c2? ← peek
    match c2? with
    | some '\'' => do
      advance
      let c3? ← peek
      match c3? with
      | some '\'' => do
        advance
        parseMultilineLiteralStringContent
      | _ => pure ""
    | _ => parseLiteralStringContent
  | _ => do
    let pos ← getPos
    throw (.unexpectedChar "string" c pos)

def parseKey : TomlReader String := do
  skipTomlWhitespace
  let c? ← peek
  match c? with
  | some '"' => do
    advance
    parseBasicStringContent
  | some '\'' => do
    advance
    parseLiteralStringContent
  | some c =>
    if isTomlBareKeyChar c then
      parseBareKey
    else do
      let pos ← getPos
      throw (.unexpectedChar "key" c pos)
  | none => throw (.unexpectedEof "key")

partial def parseDottedKey : TomlReader (List String) := do
  let first ← parseKey
  let rec go (acc : List String) : TomlReader (List String) := do
    skipTomlWhitespace
    let c? ← peek
    match c? with
    | some '.' => do
      advance
      let next ← parseKey
      go (next :: acc)
    | _ => pure acc.reverse
  go [first]

partial def readTomlDigits (acc : Nat) (hasDigits : Bool) : TomlReader (Nat × Bool) := do
  let c? ← peek
  match c? with
  | some '_' => do
    advance
    readTomlDigits acc hasDigits
  | some c =>
    if '0' ≤ c && c ≤ '9' then do
      advance
      readTomlDigits (acc * 10 + (c.toNat - '0'.toNat)) true
    else
      pure (acc, hasDigits)
  | none => pure (acc, hasDigits)

partial def parseTomlNumber : TomlReader Float := do
  skipTomlWhitespace
  let c? ← peek
  let negative ← match c? with
    | some '-' => do advance; pure true
    | some '+' => do advance; pure false
    | _ => pure false

  let c? ← peek
  match c? with
  | some 'i' => do
    expectString "inf"
    pure (if negative then -(1.0 / 0.0) else (1.0 / 0.0))
  | some 'n' => do
    expectString "nan"
    pure (0.0 / 0.0)
  | some '0' => do
    advance
    let c2? ← peek
    match c2? with
    | some 'x' => do
      advance
      parseHexNumber negative
    | some 'o' => do
      advance
      parseOctalNumber negative
    | some 'b' => do
      advance
      parseBinaryNumber negative
    | _ => parseDecimalNumber negative 0
  | _ => do
    let (intPart, _) ← readTomlDigits 0 false
    parseDecimalNumber negative intPart
where
  parseHexNumber (negative : Bool) : TomlReader Float := do
    let rec go (acc : Nat) : TomlReader Nat := do
      let c? ← peek
      match c? with
      | some '_' => do advance; go acc
      | some c =>
        if '0' ≤ c && c ≤ '9' then do
          advance
          go (acc * 16 + (c.toNat - '0'.toNat))
        else if 'a' ≤ c && c ≤ 'f' then do
          advance
          go (acc * 16 + (c.toNat - 'a'.toNat + 10))
        else if 'A' ≤ c && c ≤ 'F' then do
          advance
          go (acc * 16 + (c.toNat - 'A'.toNat + 10))
        else pure acc
      | none => pure acc
    let n ← go 0
    pure (if negative then -Float.ofNat n else Float.ofNat n)

  parseOctalNumber (negative : Bool) : TomlReader Float := do
    let rec go (acc : Nat) : TomlReader Nat := do
      let c? ← peek
      match c? with
      | some '_' => do advance; go acc
      | some c =>
        if '0' ≤ c && c ≤ '7' then do
          advance
          go (acc * 8 + (c.toNat - '0'.toNat))
        else pure acc
      | none => pure acc
    let n ← go 0
    pure (if negative then -Float.ofNat n else Float.ofNat n)

  parseBinaryNumber (negative : Bool) : TomlReader Float := do
    let rec go (acc : Nat) : TomlReader Nat := do
      let c? ← peek
      match c? with
      | some '_' => do advance; go acc
      | some '0' => do advance; go (acc * 2)
      | some '1' => do advance; go (acc * 2 + 1)
      | _ => pure acc
    let n ← go 0
    pure (if negative then -Float.ofNat n else Float.ofNat n)

  parseDecimalNumber (negative : Bool) (intPart : Nat) : TomlReader Float := do
    let c? ← peek
    let (fracPart, fracDigits) ← match c? with
      | some '.' => do
        advance
        let (frac, hasFrac) ← readTomlDigits 0 false
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
        let (exp, hasExp) ← readTomlDigits 0 false
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
  partial def parseTomlValue : TomlReader TomlValue := do
    skipTomlWhitespace
    let c? ← peek
    match c? with
    | some '"' => TomlValue.str <$> parseTomlString
    | some '\'' => TomlValue.str <$> parseTomlString
    | some '[' => TomlValue.arr <$> parseTomlArray
    | some '{' => TomlValue.table <$> parseInlineTable
    | some 't' => do expectString "true"; pure (TomlValue.bool true)
    | some 'f' => do expectString "false"; pure (TomlValue.bool false)
    | some c =>
      if c == '-' || c == '+' || ('0' ≤ c && c ≤ '9') || c == 'i' || c == 'n' then
        TomlValue.num <$> parseTomlNumber
      else do
        let pos ← getPos
        throw (.unexpectedChar "TOML value" c pos)
    | none => throw (.unexpectedEof "TOML value")

  partial def parseTomlArray : TomlReader (List TomlValue) := do
    expectChar '['
    skipWhitespaceAndComments
    let c? ← peek
    match c? with
    | some ']' => do advance; pure []
    | _ => do
      let first ← parseTomlValue
      let rec go (acc : List TomlValue) : TomlReader (List TomlValue) := do
        skipWhitespaceAndComments
        let c? ← peek
        match c? with
        | some ',' => do
          advance
          skipWhitespaceAndComments
          let c2? ← peek
          match c2? with
          | some ']' => do
            advance
            pure acc.reverse
          | _ => do
            let v ← parseTomlValue
            go (v :: acc)
        | some ']' => do
          advance
          pure acc.reverse
        | some c => do
          let pos ← getPos
          throw (.unexpectedChar "',' or ']'" c pos)
        | none => throw (.unexpectedEof "']' or ','")
      go [first]

  partial def parseInlineTable : TomlReader (List (String × TomlValue)) := do
    expectChar '{'
    skipTomlWhitespace
    let c? ← peek
    match c? with
    | some '}' => do advance; pure []
    | _ => do
      let key ← parseKey
      skipTomlWhitespace
      expectChar '='
      let value ← parseTomlValue
      let rec go (acc : List (String × TomlValue)) : TomlReader (List (String × TomlValue)) := do
        skipTomlWhitespace
        let c? ← peek
        match c? with
        | some ',' => do
          advance
          skipTomlWhitespace
          let k ← parseKey
          skipTomlWhitespace
          expectChar '='
          let v ← parseTomlValue
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

def insertAtPath (table : List (String × TomlValue)) (path : List String) (value : TomlValue) : List (String × TomlValue) :=
  match path with
  | [] => table
  | [key] =>
    let existing := table.find? fun (k, _) => k == key
    match existing with
    | some _ => table.map fun (k, v) => if k == key then (k, value) else (k, v)
    | none => table ++ [(key, value)]
  | key :: rest =>
    let existing := table.find? fun (k, _) => k == key
    match existing with
    | some (_, TomlValue.table nested) =>
      table.map fun (k, v) =>
        if k == key then (k, TomlValue.table (insertAtPath nested rest value))
        else (k, v)
    | some _ =>
      table.map fun (k, v) =>
        if k == key then (k, TomlValue.table (insertAtPath [] rest value))
        else (k, v)
    | none =>
      table ++ [(key, TomlValue.table (insertAtPath [] rest value))]

def parseKeyValue : TomlReader (List String × TomlValue) := do
  let keys ← parseDottedKey
  skipTomlWhitespace
  expectChar '='
  let value ← parseTomlValue
  pure (keys, value)

def parseTableHeader : TomlReader (List String) := do
  expectChar '['
  let keys ← parseDottedKey
  skipTomlWhitespace
  expectChar ']'
  pure keys

def parseArrayTableHeader : TomlReader (List String) := do
  expectChar '['
  expectChar '['
  let keys ← parseDottedKey
  skipTomlWhitespace
  expectChar ']'
  expectChar ']'
  pure keys

def insertArrayTable (table : List (String × TomlValue)) (path : List String) (value : TomlValue) : List (String × TomlValue) :=
  match path with
  | [] => table
  | [key] =>
    let existing := table.find? fun (k, _) => k == key
    match existing with
    | some (_, TomlValue.arr arr) =>
      table.map fun (k, v) => if k == key then (k, TomlValue.arr (arr ++ [value])) else (k, v)
    | some _ =>
      table.map fun (k, v) => if k == key then (k, TomlValue.arr [value]) else (k, v)
    | none => table ++ [(key, TomlValue.arr [value])]
  | key :: rest =>
    let existing := table.find? fun (k, _) => k == key
    match existing with
    | some (_, TomlValue.table nested) =>
      table.map fun (k, v) =>
        if k == key then (k, TomlValue.table (insertArrayTable nested rest value))
        else (k, v)
    | some (_, TomlValue.arr arr) =>
      match arr.getLast? with
      | some (TomlValue.table nested) =>
        let newNested := insertArrayTable nested rest value
        let newArr := arr.dropLast ++ [TomlValue.table newNested]
        table.map fun (k, v) => if k == key then (k, TomlValue.arr newArr) else (k, v)
      | _ =>
        table.map fun (k, v) =>
          if k == key then (k, TomlValue.arr (arr ++ [TomlValue.table (insertArrayTable [] rest value)]))
          else (k, v)
    | some _ =>
      table.map fun (k, v) =>
        if k == key then (k, TomlValue.table (insertArrayTable [] rest value))
        else (k, v)
    | none =>
      table ++ [(key, TomlValue.table (insertArrayTable [] rest value))]

partial def parseTomlDocument : TomlReader TomlValue := do
  let rec go (table : List (String × TomlValue)) (currentPath : List String) : TomlReader (List (String × TomlValue)) := do
    skipWhitespaceAndComments
    let eof ← isEof
    if eof then
      pure table
    else do
      let c? ← peek
      match c? with
      | some '[' => do
        advance
        let c2? ← peek
        match c2? with
        | some '[' => do
          advance
          let keys ← parseDottedKey
          skipTomlWhitespace
          expectChar ']'
          expectChar ']'
          skipTomlWhitespace
          skipToEndOfLine
          let newTable := insertArrayTable table keys (TomlValue.table [])
          go newTable keys
        | _ => do
          let keys ← parseDottedKey
          skipTomlWhitespace
          expectChar ']'
          skipTomlWhitespace
          skipToEndOfLine
          let newTable := insertAtPath table keys (TomlValue.table [])
          go newTable keys
      | some '#' => do
        advance
        skipComment
        go table currentPath
      | some c =>
        if isTomlBareKeyChar c || c == '"' || c == '\'' then do
          let (keys, value) ← parseKeyValue
          skipTomlWhitespace
          skipToEndOfLine
          let fullPath := currentPath ++ keys
          let newTable := insertAtPath table fullPath value
          go newTable currentPath
        else do
          let pos ← getPos
          throw (.unexpectedChar "key or table header" c pos)
      | none => pure table
  let result ← go [] []
  pure (TomlValue.table result)

structure DecoderState where
  value : TomlValue

instance : Inhabited DecoderState where
  default := { value := TomlValue.table [] }

abbrev TomlDecoder (α : Type) := DecoderState → Except TomlError (α × DecoderState)

instance : Monad TomlDecoder where
  pure a := fun s => .ok (a, s)
  bind m f := fun s =>
    match m s with
    | .ok (a, s') => f a s'
    | .error e => .error e

def TomlDecoder.run (v : TomlValue) (d : TomlDecoder α) : Except TomlError α :=
  match d { value := v } with
  | .ok (a, _) => .ok a
  | .error e => .error e

def getTomlValue : TomlDecoder TomlValue := fun s => .ok (s.value, s)

def withTomlValue (v : TomlValue) (d : TomlDecoder α) : TomlDecoder α := fun s =>
  match d { value := v } with
  | .ok (a, _) => .ok (a, s)
  | .error e => .error e

def failToml (msg : String) : TomlDecoder α := fun _ =>
  .error (.custom msg 0)

instance : Decoder TomlDecoder where
  getBool := do
    let v ← getTomlValue
    match v with
    | TomlValue.bool b => pure b
    | _ => failToml "expected boolean"

  getNat := do
    let v ← getTomlValue
    match v with
    | TomlValue.num n =>
      if n >= 0 && n == n.floor then
        pure n.toUInt64.toNat
      else failToml "expected non-negative integer"
    | _ => failToml "expected number"

  getInt := do
    let v ← getTomlValue
    match v with
    | TomlValue.num n =>
      if n == n.floor then
        if n >= 0 then
          pure n.toUInt64.toNat
        else
          pure (-((-n).toUInt64.toNat : Int))
      else failToml "expected integer"
    | _ => failToml "expected number"

  getInt64 := do
    let v ← getTomlValue
    match v with
    | TomlValue.num n =>
      if n == n.floor then
        if n >= 0 then
          pure (Int64.ofNat n.toUInt64.toNat)
        else
          pure (-Int64.ofNat (-n).toUInt64.toNat)
      else failToml "expected integer"
    | _ => failToml "expected number"

  getFloat := do
    let v ← getTomlValue
    match v with
    | TomlValue.num n => pure n
    | _ => failToml "expected number"

  getString := do
    let v ← getTomlValue
    match v with
    | TomlValue.str s => pure s
    | _ => failToml "expected string"

  getNull := do
    let v ← getTomlValue
    match v with
    | TomlValue.table [] => pure ()
    | _ => failToml "expected empty table (null equivalent)"

  getList getElem := do
    let v ← getTomlValue
    match v with
    | TomlValue.arr xs => xs.mapM fun x => withTomlValue x getElem
    | _ => failToml "expected array"

  getOption getElem := do
    let v ← getTomlValue
    match v with
    | TomlValue.table [] => pure none
    | _ => some <$> getElem

  withObject action := do
    let v ← getTomlValue
    match v with
    | TomlValue.table _ => action
    | _ => failToml "expected table"

  getField name action := do
    let v ← getTomlValue
    match v with
    | TomlValue.table fields =>
      match fields.find? (fun (k, _) => k == name) with
      | some (_, fieldValue) => withTomlValue fieldValue action
      | none => failToml s!"missing field '{name}'"
    | _ => failToml "expected table"

  matchVariant _numCtors _byIndex byName := do
    let v ← getTomlValue
    match v with
    | TomlValue.str tag => byName tag
    | TomlValue.table [(tag, payload)] => withTomlValue payload (byName tag)
    | TomlValue.table _ => failToml "expected single-key table for variant"
    | _ => failToml "expected string or table for variant"

  fail msg := failToml msg

def encode [Serialize α] (a : α) : String :=
  TomlWriter.run (Serialize.serialize a)

def decode [Deserialize α] (input : String) : Except TomlError α := do
  let value ← TomlReader.run input parseTomlDocument
  let decoded : TomlDecoder α := @Deserialize.deserialize α _ TomlDecoder _ _
  TomlDecoder.run value decoded

def decode? [Deserialize α] (input : String) : Option α :=
  decode input |>.toOption

def decode! [Deserialize α] [Inhabited α] (input : String) : α :=
  match decode input with
  | .ok a => a
  | .error e => panic! s!"Toml.decode! failed: {e}"

end Kenosis.Toml
