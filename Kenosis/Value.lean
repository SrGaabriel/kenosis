import Std.Data.HashMap

namespace Kenosis

open Std

inductive Value where
  | bool (b : Bool)
  | int (num : Int)
  | nat (n : Nat)
  | long (num : Int64)
  | str (string : String)
  | list (arr : List Value)
  | null
  | obj (kv : HashMap.Raw String Value)

abbrev emptyObj : HashMap.Raw String Value := {}

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
  | Kenosis.Value.obj m =>
    let entries := m.toList.map (fun (k, v) => k ++ ": " ++ toStringImpl v)
    "{" ++ String.intercalate ", " entries ++ "}"

instance : ToString Kenosis.Value where
  toString := toStringImpl
