namespace Kenosis

class Deserializer (D : Type) where
  decodeNat : D → Except String (Nat × D)
  decodeInt : D → Except String (Int × D)
  decodeString : D → Except String (String × D)
  decodeBool : D → Except String (Bool × D)
  decodeOption : {α : Type} → (D → Except String (α × D)) → D → Except String (Option α × D)
  decodeList : {α : Type} → (D → Except String (α × D)) → D → Except String (List α × D)
  decodeStructBegin : D → String → Except String D
  decodeField : {α : Type} → D → String → (D → Except String (α × D)) → Except String (α × D)
  decodeStructEnd : D → Except String D
  decodeEnumBegin : D → Except String (String × D)
  decodeEnumEnd : D → Except String D

class Deserialize (α : Type u) where
  deserialize : {D : Type} → [Deserializer D] → D → Except String (α × D)

instance : Deserialize Nat where
  deserialize {D} [Deserializer D] d := Deserializer.decodeNat d

instance : Deserialize Int where
  deserialize {D} [Deserializer D] d := Deserializer.decodeInt d

instance : Deserialize String where
  deserialize {D} [Deserializer D] d := Deserializer.decodeString d

instance : Deserialize Bool where
  deserialize {D} [Deserializer D] d := Deserializer.decodeBool d

instance [Deserialize α] : Deserialize (Option α) where
  deserialize {D} [Deserializer D] d := Deserializer.decodeOption Deserialize.deserialize d

instance [Deserialize α] : Deserialize (List α) where
  deserialize {D} [Deserializer D] d := Deserializer.decodeList Deserialize.deserialize d

end Kenosis
