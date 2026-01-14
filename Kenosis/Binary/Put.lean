namespace Kenosis.Binary

structure PutState where
  buffer : ByteArray
  deriving Inhabited

def Put (α : Type) := PutState → (α × PutState)

instance : Monad Put where
  pure a := fun s => (a, s)
  bind m f := fun s =>
    let (a, s') := m s
    f a s'

instance : MonadStateOf PutState Put where
  get := fun s => (s, s)
  set s := fun _ => ((), s)
  modifyGet f := fun s => f s

def Put.run (p : Put Unit) : ByteArray :=
  let ((), s) := p { buffer := ByteArray.empty }
  s.buffer

def Put.runWithCapacity (_capacity : Nat) (p : Put Unit) : ByteArray :=
  let ((), s) := p { buffer := ByteArray.empty }
  s.buffer

def putWord8 (b : UInt8) : Put Unit := fun s =>
  ((), { buffer := s.buffer.push b })

def putBytes (bytes : ByteArray) : Put Unit := fun s =>
  ((), { buffer := s.buffer ++ bytes })

def putWord16be (n : UInt16) : Put Unit := do
  putWord8 (n >>> 8).toUInt8
  putWord8 n.toUInt8

def putWord32be (n : UInt32) : Put Unit := do
  putWord8 (n >>> 24).toUInt8
  putWord8 (n >>> 16).toUInt8
  putWord8 (n >>> 8).toUInt8
  putWord8 n.toUInt8

def putWord64be (n : UInt64) : Put Unit := do
  putWord8 (n >>> 56).toUInt8
  putWord8 (n >>> 48).toUInt8
  putWord8 (n >>> 40).toUInt8
  putWord8 (n >>> 32).toUInt8
  putWord8 (n >>> 24).toUInt8
  putWord8 (n >>> 16).toUInt8
  putWord8 (n >>> 8).toUInt8
  putWord8 n.toUInt8

def putInt16be (n : Int16) : Put Unit :=
  putWord16be n.toUInt16

def putInt32be (n : Int32) : Put Unit :=
  putWord32be n.toUInt32

def putInt64be (n : Int64) : Put Unit :=
  putWord64be n.toUInt64

partial def putNatLeb128 (n : Nat) : Put Unit := do
  let byte := (n % 128).toUInt8
  let rest := n / 128
  if rest == 0 then
    putWord8 byte
  else
    putWord8 (byte ||| 0x80)
    putNatLeb128 rest

def putIntLeb128 (n : Int) : Put Unit := do
  if n >= 0 then
    putWord8 0
    putNatLeb128 n.toNat
  else
    putWord8 1
    putNatLeb128 (-n).toNat

def putBool (b : Bool) : Put Unit :=
  putWord8 (if b then 1 else 0)

def putString (s : String) : Put Unit := do
  let bytes := s.toUTF8
  putNatLeb128 bytes.size
  putBytes bytes

def putList (putElem : α → Put Unit) (xs : List α) : Put Unit := do
  putNatLeb128 xs.length
  xs.forM putElem

def putOption (putElem : α → Put Unit) : Option α → Put Unit
  | none => putWord8 0
  | some a => do
    putWord8 1
    putElem a

def getSize : Put Nat := fun s =>
  (s.buffer.size, s)

end Kenosis.Binary
