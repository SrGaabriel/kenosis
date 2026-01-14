import Kenosis

open Kenosis

structure Person where
  name : String
  age : Nat
  deriving Serialize, Deserialize, BEq, Repr

structure Employee where
  person : Person
  department : String
  manager : Option String
  deriving Serialize, Deserialize, BEq, Repr

inductive Status
  | active
  | inactive
  | pending (reason : String)
  deriving Serialize, Deserialize, BEq, Repr

inductive Result (α : Type) (ε : Type)
  | ok (value : α)
  | err (error : ε)
  deriving BEq, Repr

instance [Serialize α] [Serialize ε] : Serialize (Result α ε) where
  serialize
    | .ok v => .map [(.str "ok", Serialize.serialize v)]
    | .err e => .map [(.str "err", Serialize.serialize e)]

instance [Deserialize α] [Deserialize ε] : Deserialize (Result α ε) where
  deserialize v := match v with
    | .map [(.str "ok", data)] => Deserialize.deserialize data >>= fun a => .ok (.ok a)
    | .map [(.str "err", data)] => Deserialize.deserialize data >>= fun e => .ok (.err e)
    | _ => .error "Expected a Result (ok or err)"

def roundtrip (x : α) [Serialize α] [Deserialize α] [BEq α] [Repr α] : IO Unit := do
  let serialized := Serialize.serialize x
  match Deserialize.deserialize serialized with
  | .ok y =>
    if x == y then
      IO.println s!"  Roundtrip OK: {repr x}"
    else
      IO.println s!"  Roundtrip MISMATCH: {repr x} -> {repr y}"
  | .error e =>
    IO.println s!"  Roundtrip FAILED: {e}"

def main : IO Unit := do
  let person := Person.mk "Alice" 30
  IO.println s!"Person: {Json.serialize person}"

  let employee := Employee.mk person "Engineering" (some "Bob")
  IO.println s!"Employee: {Json.serialize employee}"

  let status1 := Status.active
  let status2 := Status.pending "awaiting approval"
  IO.println s!"Status 1: {Json.serialize status1}"
  IO.println s!"Status 2: {Json.serialize status2}"

  let result1 : Result Nat String := .ok 42
  let result2 : Result Nat String := .err "something went wrong"
  IO.println s!"Result 1: {Json.serialize result1}"
  IO.println s!"Result 2: {Json.serialize result2}"

  let people := [Person.mk "Alice" 30, Person.mk "Bob" 25]
  IO.println s!"People list: {Json.serialize people}"

  IO.println ""

  IO.println "Person roundtrip:"
  roundtrip person

  IO.println "Employee roundtrip:"
  roundtrip employee

  IO.println "Status roundtrips:"
  roundtrip status1
  roundtrip status2

  IO.println "Result roundtrips:"
  roundtrip result1
  roundtrip result2
