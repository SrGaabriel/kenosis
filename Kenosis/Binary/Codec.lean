import Kenosis.Codec
import Kenosis.Binary.Put
import Kenosis.Binary.Get

namespace Kenosis.Binary

open Kenosis

instance : Encoder Put where
  putBool := putBool
  putNat := putNatLeb128
  putInt := putIntLeb128
  putInt64 := putInt64be
  putFloat := putFloat64be
  putString := putString
  putNull := pure ()

  putOption opt := match opt with
    | none => putWord8 0
    | some p => do
      putWord8 1
      p

  putList elems := do
    putNatLeb128 elems.length
    for e in elems do
      e

  putObject fields := do
    for (_, putField) in fields do
      putField

  putVariant idx _name payload := do
    putWord8 idx.toUInt8
    match payload with
    | none => pure ()
    | some p => p

instance : Decoder Get where
  getBool := getBool
  getNat := getNatLeb128
  getInt := getIntLeb128
  getInt64 := getInt64be
  getFloat := getFloat64be
  getString := getString
  getNull := pure ()

  getList getElem := do
    let len ← getNatLeb128
    let rec go (n : Nat) (acc : List _) : Get (List _) :=
      match n with
      | 0 => pure acc.reverse
      | n + 1 => do
        let elem ← getElem
        go n (elem :: acc)
    go len []

  getOption getElem := do
    let tag ← getWord8
    match tag with
    | 0 => pure none
    | 1 => some <$> getElem
    | _ => failInvalid s!"invalid option tag: {tag}"

  withObject action := action

  getField _name action := action

  matchVariant numCtors byIndex _byName := do
    let tag ← getWord8
    if tag.toNat < numCtors then
      byIndex tag.toNat
    else
      failInvalid s!"invalid variant tag: {tag}, expected < {numCtors}"

  fail msg := failInvalid msg

def encode [Serialize α] (a : α) : ByteArray :=
  Put.run (Serialize.serialize a)

def encodeWithCapacity [Serialize α] (capacity : Nat) (a : α) : ByteArray :=
  Put.runWithCapacity capacity (Serialize.serialize a)

def decode [Deserialize α] (bytes : ByteArray) : Except GetError α :=
  Get.run bytes Deserialize.deserialize

def decodeExact [Deserialize α] (bytes : ByteArray) : Except GetError α :=
  runExact bytes Deserialize.deserialize

def decode? [Deserialize α] (bytes : ByteArray) : Option α :=
  decode bytes |>.toOption

def decode! [Deserialize α] [Inhabited α] (bytes : ByteArray) : α :=
  match decode bytes with
  | .ok a => a
  | .error e => panic! s!"Binary.decode! failed: {e}"

end Kenosis.Binary
