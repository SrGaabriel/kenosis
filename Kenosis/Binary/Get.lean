namespace Kenosis.Binary

inductive GetError where
  | unexpectedEof (expected : String) (position : Nat)
  | invalidData (message : String) (position : Nat)
  | overflow (message : String) (position : Nat)
  deriving Repr, BEq

instance : ToString GetError where
  toString
    | .unexpectedEof expected pos => s!"unexpected end of input at position {pos}, expected {expected}"
    | .invalidData msg pos => s!"invalid data at position {pos}: {msg}"
    | .overflow msg pos => s!"overflow at position {pos}: {msg}"

structure GetState where
  input : ByteArray
  position : Nat
  deriving Inhabited

abbrev Get (α : Type) := GetState → Except GetError (α × GetState)

instance : Monad Get where
  pure a := fun s => .ok (a, s)
  bind m f := fun s =>
    match m s with
    | .ok (a, s') => f a s'
    | .error e => .error e

instance : MonadExceptOf GetError Get where
  throw e := fun _ => .error e
  tryCatch m handler := fun s =>
    match m s with
    | .ok result => .ok result
    | .error e => handler e s

def Get.run (input : ByteArray) (g : Get α) : Except GetError α :=
  match g { input, position := 0 } with
  | .ok (a, _) => .ok a
  | .error e => .error e

def Get.runWithConsumed (input : ByteArray) (g : Get α) : Except GetError (α × Nat) :=
  match g { input, position := 0 } with
  | .ok (a, s) => .ok (a, s.position)
  | .error e => .error e

def getPosition : Get Nat := fun s => .ok (s.position, s)

def getRemaining : Get Nat := fun s => .ok (s.input.size - s.position, s)

def isEof : Get Bool := fun s => .ok (s.position >= s.input.size, s)

def failEof (expected : String) : Get α := fun s =>
  .error (.unexpectedEof expected s.position)

def failInvalid (message : String) : Get α := fun s =>
  .error (.invalidData message s.position)

def failOverflow (message : String) : Get α := fun s =>
  .error (.overflow message s.position)

def getWord8 : Get UInt8 := fun s =>
  if h : s.position < s.input.size then
    let byte := s.input.get s.position h
    .ok (byte, { s with position := s.position + 1 })
  else
    .error (.unexpectedEof "1 byte" s.position)

def getBytes (n : Nat) : Get ByteArray := fun s =>
  if s.position + n <= s.input.size then
    let bytes := s.input.extract s.position (s.position + n)
    .ok (bytes, { s with position := s.position + n })
  else
    .error (.unexpectedEof s!"{n} bytes" s.position)

def getWord16be : Get UInt16 := do
  let b0 ← getWord8
  let b1 ← getWord8
  pure ((b0.toUInt16 <<< 8) ||| b1.toUInt16)

def getWord32be : Get UInt32 := do
  let b0 ← getWord8
  let b1 ← getWord8
  let b2 ← getWord8
  let b3 ← getWord8
  pure ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) |||
        (b2.toUInt32 <<< 8) ||| b3.toUInt32)

def getWord64be : Get UInt64 := do
  let b0 ← getWord8
  let b1 ← getWord8
  let b2 ← getWord8
  let b3 ← getWord8
  let b4 ← getWord8
  let b5 ← getWord8
  let b6 ← getWord8
  let b7 ← getWord8
  pure ((b0.toUInt64 <<< 56) ||| (b1.toUInt64 <<< 48) |||
        (b2.toUInt64 <<< 40) ||| (b3.toUInt64 <<< 32) |||
        (b4.toUInt64 <<< 24) ||| (b5.toUInt64 <<< 16) |||
        (b6.toUInt64 <<< 8) ||| b7.toUInt64)

def getInt16be : Get Int16 := do
  let w ← getWord16be
  pure w.toInt16

def getInt32be : Get Int32 := do
  let w ← getWord32be
  pure w.toInt32

def getInt64be : Get Int64 := do
  let w ← getWord64be
  pure w.toInt64

def getFloat64be : Get Float := do
  let w ← getWord64be
  pure (Float.ofBits w)

partial def getNatLeb128 : Get Nat := do
  let rec go (acc : Nat) (shift : Nat) : Get Nat := do
    let byte ← getWord8
    let value := acc ||| ((byte.toNat &&& 0x7F) <<< shift)
    if byte &&& 0x80 == 0 then
      pure value
    else
      go value (shift + 7)
  go 0 0

def getIntLeb128 : Get Int := do
  let sign ← getWord8
  let magnitude ← getNatLeb128
  match sign with
  | 0 => pure magnitude
  | 1 => pure (-magnitude)
  | _ => failInvalid s!"invalid sign byte: {sign}"

def getBool : Get Bool := do
  let byte ← getWord8
  match byte with
  | 0 => pure false
  | 1 => pure true
  | _ => failInvalid s!"invalid boolean byte: {byte}"

def getString : Get String := do
  let len ← getNatLeb128
  let bytes ← getBytes len
  match String.fromUTF8? bytes with
  | some s => pure s
  | none => failInvalid "invalid UTF-8 sequence"

def getList (getElem : Get α) : Get (List α) := do
  let len ← getNatLeb128
  let rec go (n : Nat) (acc : List α) : Get (List α) :=
    match n with
    | 0 => pure acc.reverse
    | n + 1 => do
      let elem ← getElem
      go n (elem :: acc)
  go len []

def getOption (getElem : Get α) : Get (Option α) := do
  let tag ← getWord8
  match tag with
  | 0 => pure none
  | 1 => some <$> getElem
  | _ => failInvalid s!"invalid option tag: {tag}"

def skip (n : Nat) : Get Unit := fun s =>
  if s.position + n <= s.input.size then
    .ok ((), { s with position := s.position + n })
  else
    .error (.unexpectedEof s!"{n} bytes to skip" s.position)

def peekWord8 : Get UInt8 := fun s =>
  if h : s.position < s.input.size then
    let byte := s.input.get s.position h
    .ok (byte, s)
  else
    .error (.unexpectedEof "1 byte (peek)" s.position)

def tryGet (g : Get α) : Get (Option α) := fun s =>
  match g s with
  | .ok (a, s') => .ok (some a, s')
  | .error _ => .ok (none, s)

def runExact (input : ByteArray) (g : Get α) : Except GetError α := do
  match g { input, position := 0 } with
  | .ok (a, s) =>
    if s.position == s.input.size then
      .ok a
    else
      .error (.invalidData s!"trailing data: {s.input.size - s.position} bytes remaining" s.position)
  | .error e => .error e

end Kenosis.Binary
