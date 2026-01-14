import Kenosis.Value
import Kenosis.Utils
import Std.Data.HashMap.Raw

namespace Kenosis.Json

set_option linter.unusedVariables false in

partial def Json.compileValue (v : Kenosis.Value) : String :=
  match v with
  | .bool b => (if b then "true" else "false")
  | .int i => (toString i)
  | .nat n => (toString n)
  | .long n => (toString n)
  | .str s => ("\"" ++ escapeString s ++ "\"")
  | .null => "null"
  | .list xs => 
      let inner := xs.attach.map fun ⟨x, h⟩ => compileValue x
      ("[" ++ ", ".intercalate inner ++ "]")
  | .obj kvs =>
      let lst := kvs.toList
      let pairs := lst.map fun (k,v) =>
        let val := compileValue v
        ("\"" ++ k ++ "\": " ++ val)
      ("{" ++ ", ".intercalate pairs ++ "}")

end Kenosis.Json
