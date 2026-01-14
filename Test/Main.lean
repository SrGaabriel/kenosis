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
    | .ok v => .obj (emptyObj.insert "ok" (Serialize.serialize v))
    | .err e => .obj (emptyObj.insert "err" (Serialize.serialize e))

instance [Deserialize α] [Deserialize ε] : Deserialize (Result α ε) where
  deserialize v := match v with
    | .obj m =>
      match m.get? "ok" with
      | some data => Deserialize.deserialize data >>= fun a => pure (.ok a)
      | none => match m.get? "err" with
        | some data => Deserialize.deserialize data >>= fun e => pure (.err e)
        | none => DeserializeM.expectedType "a Result (ok or err)"
    | _ => DeserializeM.expectedType "a Result (ok or err)"

def roundtrip (x : α) [Serialize α] [Deserialize α] [BEq α] [Repr α] : IO Unit := do
  let serialized := Serialize.serialize x
  match DeserializeM.run (Deserialize.deserialize serialized) with
  | .ok y =>
    if x == y then
      IO.println s!"  Roundtrip OK: {repr x}"
    else
      IO.println s!"  Roundtrip MISMATCH: {repr x} -> {repr y}"
  | .error e =>
    IO.println s!"  Roundtrip FAILED: {repr e}"

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

  IO.println "Person deserialize:"
  IO.println (repr (Json.deserialize (α := Person) "{\"name\": \"Alice\", \"age\": 30}"))

  IO.println "Employee deserialize:"
  IO.println (repr (Json.deserialize (α := Employee) "{\"person\": {\"name\": \"Alice\", \"age\": 30}, \"department\": \"Engineering\", \"manager\": \"Bob\"}"))

  IO.println "Status deserializes:"
  IO.println (repr (Json.deserialize (α := Status) "\"active\""))
  IO.println (repr (Json.deserialize (α := Status) "{\"pending\": \"awaiting approval\"}"))

  IO.println "Result deserializes:"
  IO.println (repr (Json.deserialize (α := Result Nat String) "{\"ok\": 42}"))
  IO.println (repr (Json.deserialize (α := Result Nat String) "{\"err\": \"something went wrong\"}"))
