import Kenosis

open Kenosis

structure Person where
  name : String
  age : Nat
  deriving Serialize

structure Employee where
  person : Person
  department : String
  manager : Option String
  deriving Serialize

inductive Status
  | active
  | inactive
  | pending (reason : String)
  deriving Serialize

inductive Result (α : Type) (ε : Type)
  | ok (value : α)
  | err (error : ε)

instance [Serialize α] [Serialize ε] : Serialize (Result α ε) where
  serialize
    | .ok v => .map [(.str "ok", Serialize.serialize v)]
    | .err e => .map [(.str "err", Serialize.serialize e)]

def toJson (x : α) [Serialize α] : Except String String :=
  Json.serialize (Serialize.serialize x)

def main : IO Unit := do
  let person := Person.mk "Alice" 30
  IO.println s!"Person: {toJson person}"

  let employee := Employee.mk person "Engineering" (some "Bob")
  IO.println s!"Employee: {toJson employee}"

  let status1 := Status.active
  let status2 := Status.pending "awaiting approval"
  IO.println s!"Status 1: {toJson status1}"
  IO.println s!"Status 2: {toJson status2}"

  let result1 : Result Nat String := .ok 42
  let result2 : Result Nat String := .err "something went wrong"
  IO.println s!"Result 1: {toJson result1}"
  IO.println s!"Result 2: {toJson result2}"

  let people := [Person.mk "Alice" 30, Person.mk "Bob" 25]
  IO.println s!"People list: {toJson people}"
