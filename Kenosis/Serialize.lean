import Kenosis.Value

namespace Kenosis

class Serialize (α : Type) where
  serialize : α → KenosisValue

instance : Serialize Nat where
  serialize n := .nat n

instance : Serialize Int where
  serialize n := .int n

instance : Serialize String where
  serialize s := .str s

instance : Serialize Bool where
  serialize b := .bool b

instance [Serialize α] : Serialize (Option α) where
  serialize
    | none => .null
    | some a => Serialize.serialize a

instance [Serialize α] : Serialize (List α) where
  serialize xs := .list (xs.map Serialize.serialize)

end Kenosis
