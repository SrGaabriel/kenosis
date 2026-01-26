namespace Kenosis

structure ReaderState where
  input : String
  pos : String.Pos.Raw
  deriving Inhabited

inductive ReaderError where
  | unexpectedEof (expected : String)
  | unexpectedChar (expected : String) (got : Char) (pos : Nat)
  | unexpectedToken (expected : String) (got : String) (pos : Nat)
  | invalidEscape (char : Char) (pos : Nat)
  | invalidNumber (pos : Nat)
  | trailingContent (pos : Nat)
  | custom (msg : String) (pos : Nat)
  deriving Repr, BEq

instance : ToString ReaderError where
  toString
    | .unexpectedEof expected => s!"unexpected end of input, expected {expected}"
    | .unexpectedChar expected got pos => s!"at position {pos}: expected {expected}, got '{got}'"
    | .unexpectedToken expected got pos => s!"at position {pos}: expected {expected}, got '{got}'"
    | .invalidEscape c pos => s!"at position {pos}: invalid escape sequence '\\{c}'"
    | .invalidNumber pos => s!"at position {pos}: invalid number"
    | .trailingContent pos => s!"at position {pos}: trailing content after value"
    | .custom msg pos => s!"at position {pos}: {msg}"

abbrev UtfReader (α : Type) := ReaderState → Except ReaderError (α × ReaderState)

instance : Monad UtfReader where
  pure a := fun s => .ok (a, s)
  bind m f := fun s =>
    match m s with
    | .ok (a, s') => f a s'
    | .error e => .error e

instance : MonadExceptOf ReaderError UtfReader where
  throw e := fun _ => .error e
  tryCatch m handler := fun s =>
    match m s with
    | .ok result => .ok result
    | .error e => handler e s

def UtfReader.run (input : String) (r : UtfReader α) : Except ReaderError α :=
  match r { input, pos := 0 } with
  | .ok (a, _) => .ok a
  | .error e => .error e

def getPos : UtfReader Nat := fun s => .ok (s.pos.byteIdx, s)

def isEof : UtfReader Bool := fun s => .ok (s.pos >= s.input.rawEndPos, s)

def peek : UtfReader (Option Char) := fun s =>
  if s.pos < s.input.rawEndPos then
    .ok (some (String.Pos.Raw.get s.input s.pos), s)
  else
    .ok (none, s)

def advance : UtfReader Unit := fun s =>
  .ok ((), { s with pos := String.Pos.Raw.next s.input s.pos })

def consume : UtfReader Char := fun s =>
  if s.pos < s.input.rawEndPos then
    let c := String.Pos.Raw.get s.input s.pos
    .ok (c, { s with pos := String.Pos.Raw.next s.input s.pos })
  else
    .error (.unexpectedEof "character")

partial def skipWhitespace : UtfReader Unit := do
  let c? ← peek
  match c? with
  | some ' ' | some '\n' | some '\r' | some '\t' => do
    advance
    skipWhitespace
  | _ => pure ()

partial def expectLine : UtfReader Unit := do
  let c? ← peek
  match c? with
  | some '\n' => advance
  | some '\r' => do
    advance
    let c2? ← peek
    match c2? with
    | some '\n' => advance
    | _ => pure ()
  | none => pure ()
  | some c => do
    let pos ← getPos
    throw (.unexpectedChar "line ending" c pos)

def expectChar (expected : Char) : UtfReader Unit := do
  skipWhitespace
  let c ← consume
  if c == expected then pure ()
  else do
    let pos ← getPos
    throw (.unexpectedChar s!"'{expected}'" c pos)

def expectString (expected : String) : UtfReader Unit := do
  let rec go (chars : List Char) : UtfReader Unit :=
    match chars with
    | [] => pure ()
    | c :: cs => do
      let got ← consume
      if got != c then do
        let pos ← getPos
        throw (.unexpectedChar s!"'{c}' in \"{expected}\"" got pos)
      go cs
  go expected.toList

partial def parseStringContent : UtfReader String := do
  let rec go (acc : String) : UtfReader String := do
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
          let rec parseHex (n : Nat) (acc : UInt32) : UtfReader UInt32 :=
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

def parseStringLiteral : UtfReader String := do
  skipWhitespace
  expectChar '"'
  parseStringContent

partial def readDigits (acc : Nat) (hasDigits : Bool) : UtfReader (Nat × Bool) := do
  let c? ← peek
  match c? with
  | some c =>
    if '0' ≤ c && c ≤ '9' then do
      advance
      readDigits (acc * 10 + (c.toNat - '0'.toNat)) true
    else
      pure (acc, hasDigits)
  | none => pure (acc, hasDigits)

partial def parseNumber : UtfReader Float := do
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

end Kenosis