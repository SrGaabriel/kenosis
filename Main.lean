import Kenosis

open Kenosis

structure Person where
  name : String
  age : Nat
  deriving Serialize, Deserialize

structure Employee where
  person : Person
  department : String
  manager : Option String
  deriving Serialize, Deserialize

inductive Status
  | active
  | inactive
  | pending (reason : String)
  deriving Serialize, Deserialize

inductive Result (α : Type) (ε : Type)
  | ok (value : α)
  | err (error : ε)

instance [Serialize α] [Serialize ε] : Serialize (Result α ε) where
  serialize
    | .ok v => "{\"ok\": " ++ Serialize.serialize v ++ "}"
    | .err e => "{\"err\": " ++ Serialize.serialize e ++ "}"

def main : IO Unit := do
  let person := Person.mk "Alice" 30
  IO.println s!"Person: {Serialize.serialize person}"

  let employee := Employee.mk person "Engineering" (some "Bob")
  IO.println s!"Employee: {Serialize.serialize employee}"

  let status1 := Status.active
  let status2 := Status.pending "awaiting approval"
  IO.println s!"Status 1: {Serialize.serialize status1}"
  IO.println s!"Status 2: {Serialize.serialize status2}"

  let result1 : Result Nat String := .ok 42
  let result2 : Result Nat String := .err "something went wrong"
  IO.println s!"Result 1: {Serialize.serialize result1}"
  IO.println s!"Result 2: {Serialize.serialize result2}"

  let people := [Person.mk "Alice" 30, Person.mk "Bob" 25]
  IO.println s!"People list: {Serialize.serialize people}"
