namespace Kenosis

class Encoder (m : Type → Type) where
  putBool : Bool → m Unit
  putNat : Nat → m Unit
  putInt : Int → m Unit
  putInt64 : Int64 → m Unit
  putString : String → m Unit
  putNull : m Unit
  putList : List (m Unit) → m Unit
  putObject : List (String × m Unit) → m Unit
  putVariant : Nat → String → Option (m Unit) → m Unit

class Decoder (m : Type → Type) where
  getBool : m Bool
  getNat : m Nat
  getInt : m Int
  getInt64 : m Int64
  getString : m String
  getNull : m Unit
  getList : m α → m (List α)
  getOption : m α → m (Option α)
  withObject : m α → m α
  getField : String → m α → m α
  matchVariant : Nat → (Nat → m α) → (String → m α) → m α
  fail : String → m α

class Serialize (α : Type) where
  serialize : {m : Type → Type} → [Monad m] → [Encoder m] → α → m Unit

class Deserialize (α : Type) where
  deserialize : {m : Type → Type} → [Monad m] → [Decoder m] → m α

instance : Serialize Bool where
  serialize b := Encoder.putBool b

instance : Deserialize Bool where
  deserialize := Decoder.getBool

instance : Serialize Nat where
  serialize n := Encoder.putNat n

instance : Deserialize Nat where
  deserialize := Decoder.getNat

instance : Serialize Int where
  serialize n := Encoder.putInt n

instance : Deserialize Int where
  deserialize := Decoder.getInt

instance : Serialize Int64 where
  serialize n := Encoder.putInt64 n

instance : Deserialize Int64 where
  deserialize := Decoder.getInt64

instance : Serialize String where
  serialize s := Encoder.putString s

instance : Deserialize String where
  deserialize := Decoder.getString

instance : Serialize Unit where
  serialize _ := Encoder.putNull

instance : Deserialize Unit where
  deserialize := Decoder.getNull

instance [Serialize α] : Serialize (Option α) where
  serialize opt := match opt with
    | none => Encoder.putVariant 0 "none" none
    | some a => Encoder.putVariant 1 "some" (some (Serialize.serialize a))

instance [Deserialize α] : Deserialize (Option α) where
  deserialize := Decoder.matchVariant 2
    (fun idx => match idx with
      | 0 => pure none
      | 1 => some <$> Deserialize.deserialize
      | n => Decoder.fail s!"invalid Option index: {n}")
    (fun name => match name with
      | "none" => pure none
      | "some" => some <$> Deserialize.deserialize
      | s => Decoder.fail s!"unknown Option variant: {s}")

instance [Serialize α] : Serialize (List α) where
  serialize xs := Encoder.putList (xs.map Serialize.serialize)

instance [Deserialize α] : Deserialize (List α) where
  deserialize := Decoder.getList Deserialize.deserialize

instance [Serialize α] [Serialize β] : Serialize (α × β) where
  serialize pair := Encoder.putObject [
    ("fst", Serialize.serialize pair.fst),
    ("snd", Serialize.serialize pair.snd)
  ]

instance [Deserialize α] [Deserialize β] : Deserialize (α × β) where
  deserialize := do
    let a ← Decoder.getField "fst" Deserialize.deserialize
    let b ← Decoder.getField "snd" Deserialize.deserialize
    pure (a, b)

instance [Serialize α] [Serialize β] : Serialize (Sum α β) where
  serialize s := match s with
    | .inl a => Encoder.putVariant 0 "inl" (some (Serialize.serialize a))
    | .inr b => Encoder.putVariant 1 "inr" (some (Serialize.serialize b))

instance [Deserialize α] [Deserialize β] : Deserialize (Sum α β) where
  deserialize := Decoder.matchVariant 2
    (fun idx => match idx with
      | 0 => Sum.inl <$> Deserialize.deserialize
      | 1 => Sum.inr <$> Deserialize.deserialize
      | n => Decoder.fail s!"invalid Sum index: {n}")
    (fun name => match name with
      | "inl" => Sum.inl <$> Deserialize.deserialize
      | "inr" => Sum.inr <$> Deserialize.deserialize
      | s => Decoder.fail s!"unknown Sum variant: {s}")

instance [Serialize α] : Serialize (Array α) where
  serialize arr := Encoder.putList (arr.toList.map Serialize.serialize)

instance [Deserialize α] : Deserialize (Array α) where
  deserialize := Array.mk <$> Decoder.getList Deserialize.deserialize

end Kenosis
