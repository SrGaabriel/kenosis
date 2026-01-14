namespace Kenosis

inductive Value where
  | bool : Bool → Kenosis.Value
  | int : Int → Kenosis.Value
  | nat : Nat → Kenosis.Value
  | long : Int64 → Kenosis.Value
  | str : String → Kenosis.Value
  | list : List Kenosis.Value → Kenosis.Value
  | null : Kenosis.Value
  | map : List (Kenosis.Value × Kenosis.Value) → Kenosis.Value

def conforms (key : String) (value : Kenosis.Value) : Bool :=
  match value with
  | Kenosis.Value.str a => a == key
  | _ => false

partial def toStringImpl : Kenosis.Value → String
  | Kenosis.Value.bool b => toString b
  | Kenosis.Value.int i => toString i
  | Kenosis.Value.nat n => toString n
  | Kenosis.Value.long l => toString l
  | Kenosis.Value.str s => s
  | Kenosis.Value.list lst => "[" ++ String.intercalate ", " (lst.map toStringImpl) ++ "]"
  | Kenosis.Value.null => "null"
  | Kenosis.Value.map m =>
    let entries := m.map (fun (k, v) => toStringImpl k ++ ": " ++ toStringImpl v)
    "{" ++ String.intercalate ", " entries ++ "}"

instance : ToString Kenosis.Value where
  toString := toStringImpl
