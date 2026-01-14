import Kenosis.Json.Write
import Kenosis.Json.Read
import Kenosis.Serialize
import Kenosis.Deserialize
import Kenosis.Traverser

namespace Kenosis

inductive JsonError where
  | syntactic : Kenosis.Json.ParseFailure -> JsonError
  | semantic : DError -> JsonError
  deriving Repr

instance : ToString JsonError where
  toString
    | .syntactic err => toString err
    | .semantic err => toString err

def Json.serialize (x : α) [s : Serialize α] : String :=
  Json.compileValue (s.serialize x)

def Json.deserialize (input : String) [d : Deserialize α] : Except JsonError α:= do
  match Json.parseValue input with
  | .ok jsonObj => match DeserializeM.run (d.deserialize jsonObj) with
    | .ok a => pure a
    | .error err => throw $ .semantic err
  | .error err => throw $ .syntactic err

def Json.deserialize? (input : String) [d : Deserialize α] : Option α :=
  Json.deserialize input |>.toOption

def Json.serialize! (input : String) [d : Deserialize α] [Inhabited α] : α :=
  match Json.deserialize input with
  | .ok a => a
  | .error err => panic! s!"Json.serialize! failed: {err}"
