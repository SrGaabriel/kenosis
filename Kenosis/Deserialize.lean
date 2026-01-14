import Kenosis.Value
import Kenosis.Traverser

namespace Kenosis

abbrev DeserializeM := TraverserM
abbrev DError := TraversingError

abbrev DeserializeM.expectedType (expected : String) : DeserializeM a := TraverserM.expectedType expected
abbrev DeserializeM.expectedNat : DeserializeM a := TraverserM.expectedNat
abbrev DeserializeM.expectedInt : DeserializeM a := TraverserM.expectedInt
abbrev DeserializeM.expectedStr : DeserializeM a := TraverserM.expectedStr
abbrev DeserializeM.expectedBool : DeserializeM a := TraverserM.expectedBool
abbrev DeserializeM.expectedList : DeserializeM a := TraverserM.expectedList
abbrev DeserializeM.unknownVariant (tag : String) : DeserializeM a := TraverserM.unknownVariant tag

def DeserializeM.run (m : DeserializeM α) : Except DError α :=
  (m { scope := "root", field := none })

class Deserialize (α : Type) where
  deserialize : Kenosis.Value -> DeserializeM α

def Deserializer.field {a : Type} (value : Kenosis.Value) (name : String) [d : Deserialize a] : DeserializeM a :=
  match value with
  | .map objs =>
    match objs.find? (fun (k,_) => conforms name k) with
    | some (_,v) => withReader (fun ctx => {ctx with scope := name}) (d.deserialize v)
    | none => do
      let ctx ← read
      throw $ .missingField name ctx.scope
  | _ => do
    let ctx ← read
    throw $ .notExtractable name ctx.scope

infix:65 " <.> " => Deserializer.field

instance : Deserialize Nat where
  deserialize
    | .nat n => pure n
    | .int i => if i >= 0 then pure i.toNat else DeserializeM.expectedNat
    | _ => DeserializeM.expectedNat

instance : Deserialize Int where
  deserialize
    | .int i => pure i
    | .nat n => pure n
    | _ => DeserializeM.expectedInt

instance : Deserialize String where
  deserialize
    | .str s => pure s
    | _ => DeserializeM.expectedStr

instance : Deserialize Bool where
  deserialize
    | .bool b => pure b
    | _ => DeserializeM.expectedBool

instance [Deserialize α] : Deserialize (Option α) where
  deserialize
    | .null => pure none
    | v => Deserialize.deserialize v >>= fun a => pure (some a)

instance [Deserialize α] : Deserialize (List α) where
  deserialize
    | .list xs => xs.mapM Deserialize.deserialize
    | _ => DeserializeM.expectedList

end Kenosis
