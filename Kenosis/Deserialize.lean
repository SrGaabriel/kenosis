import Kenosis.Value
import Kenosis.Parser

namespace Kenosis

class Deserialize (α : Type) where
  deserialize : Kenosis.Value -> Except String α

def Deserializer.field {a : Type} (value : Kenosis.Value) (name : String) [d : Deserialize a] : ParserM a :=
  match value with
  | .map objs =>
    match objs.find? (fun (k,_) => conforms name k) with
    | some (_,v) =>
      match d.deserialize v with
      | .ok res => .ok res
      | .error err => .error s!"Failed to deserialize field '{name}': {err}"
    | none => .error s!"Field '{name}' not found in object."
  | _ => .error s!"Expected an object to extract field '{name}', but got: {value}"

infix:65 " <.> " => Deserializer.field

instance : Deserialize Nat where
  deserialize
    | .nat n => .ok n
    | .int i => if i >= 0 then .ok i.toNat else .error "Expected non-negative integer for Nat"
    | _ => .error "Expected a natural number"

instance : Deserialize Int where
  deserialize
    | .int i => .ok i
    | .nat n => .ok n
    | _ => .error "Expected an integer"

instance : Deserialize String where
  deserialize
    | .str s => .ok s
    | _ => .error "Expected a string"

instance : Deserialize Bool where
  deserialize
    | .bool b => .ok b
    | _ => .error "Expected a boolean"

instance [Deserialize α] : Deserialize (Option α) where
  deserialize
    | .null => .ok none
    | v => Deserialize.deserialize v >>= fun a => .ok (some a)

instance [Deserialize α] : Deserialize (List α) where
  deserialize
    | .list xs => xs.mapM Deserialize.deserialize
    | _ => .error "Expected a list"

end Kenosis
