import Kenosis.Codec
import Kenosis.Utils

namespace Kenosis.Toml

open Kenosis

structure WriterState where
  buffer : String
  currentTable : Option String
  deriving Inhabited

inductive TomlObject
  | table
  | value
  | null
  deriving Inhabited

structure TomlWriter (α : Type) where
  runState : WriterState -> (α × WriterState)
  object : TomlObject
  deriving Inhabited

instance : Monad TomlWriter where
  pure a := { runState := fun s => (a, s), object := .value }
  bind w f := {
    runState := fun s =>
      let (a, s') := w.runState s
      (f a).runState s',
    object := w.object
  }

def TomlWriter.run {α : Type} (w : TomlWriter α) : String :=
  let (_, s) := w.runState { buffer := "", currentTable := .none }
  s.buffer

def writeValue (str : String) : TomlWriter Unit :=
  { runState := fun s => ((), { s with buffer := s.buffer ++ str }), object := .value }

def writeObject (tableName : String) : TomlWriter Unit :=
  { runState := fun s => ((), { s with buffer := s.buffer ++ "\n[" ++ tableName ++ "]\n", currentTable := some tableName }), object := .table }

def writeListWith (sep : String) (elems : List (TomlWriter Unit)) : TomlWriter Unit :=
  match elems with
  | [] => pure ()
  | [e] => e
  | e :: es => do
    e
    es.forM fun elem => do
      writeValue sep
      elem

instance : Encoder TomlWriter where
  putBool b := writeValue (if b then "true" else "false")
  putNat n := writeValue (toString n)
  putInt i := writeValue (toString i)
  putInt64 i := writeValue (toString i)
  putFloat f := writeValue (toString f)
  putString s := writeValue ("\"" ++ escapeString s ++ "\"")
  putNull := { runState := fun s => ((), s), object := .null }

  putList elems := do
    writeValue "["
    writeListWith ", " elems
    writeValue "]"

  putObject fields := {
    runState := fun s =>
      let fields := fields.filter fun (_, valWriter) =>
        match valWriter.object with
        | TomlObject.null => false
        | _ => true
      let (values, tables) := fields.partition fun (_, valWriter) =>
        match valWriter.object with
        | TomlObject.table => false
        | _ => true
      let valueWriters := values.map fun (key, valWriter) => do
        writeValue key
        writeValue " = "
        valWriter
      let tableWriters := tables.map fun (key, valWriter) => do
        writeObject key
        valWriter
      let allWriters := valueWriters ++ tableWriters
      (writeListWith "\n" allWriters).runState s,
    object := .table
  }

  putVariant _idx name payload := do
    match payload with
    | none => writeValue name
    | some p => do
        writeValue name
        writeValue " = "
        p

def encode [Serialize α] (a : α) : String :=
  TomlWriter.run (Serialize.serialize a)

end Kenosis.Toml
