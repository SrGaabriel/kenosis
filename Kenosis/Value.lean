namespace Kenosis

inductive KenosisValue where
  | bool : Bool → KenosisValue
  | int : Int → KenosisValue
  | nat : Nat → KenosisValue
  | long : Int64 → KenosisValue
  | str : String → KenosisValue
  | list : List KenosisValue → KenosisValue
  | null : KenosisValue
  | map : List (KenosisValue × KenosisValue) → KenosisValue

def conforms (key : String) (value : KenosisValue) : Bool :=
  match value with
  | KenosisValue.str a => a == key
  | _ => false

partial def toStringImpl : KenosisValue → String
  | KenosisValue.bool b => toString b
  | KenosisValue.int i => toString i
  | KenosisValue.nat n => toString n
  | KenosisValue.long l => toString l
  | KenosisValue.str s => s
  | KenosisValue.list lst => "[" ++ String.intercalate ", " (lst.map toStringImpl) ++ "]"
  | KenosisValue.null => "null"
  | KenosisValue.map m =>
    let entries := m.map (fun (k, v) => toStringImpl k ++ ": " ++ toStringImpl v)
    "{" ++ String.intercalate ", " entries ++ "}"

instance : ToString KenosisValue where
  toString := toStringImpl
