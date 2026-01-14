namespace Kenosis

class Serialize (α : Type u) where
  serialize : α → String

instance : Serialize Nat where
  serialize n := toString n

instance : Serialize Int where
  serialize n := toString n

instance : Serialize String where
  serialize s := "\"" ++ s ++ "\""

instance : Serialize Bool where
  serialize b := if b then "true" else "false"

instance [Serialize α] : Serialize (Option α) where
  serialize
    | none => "null"
    | some a => Serialize.serialize a

instance [Serialize α] : Serialize (List α) where
  serialize xs := "[" ++ String.intercalate ", " (xs.map Serialize.serialize) ++ "]"

instance [Serialize α] [Serialize β] : Serialize (Prod α β) where
  serialize p := "(" ++ Serialize.serialize p.fst ++ ", " ++ Serialize.serialize p.snd ++ ")"

end Kenosis
