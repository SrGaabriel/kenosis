import Kenosis.Value
import Kenosis.Utils
import Kenosis.Serialize

namespace Kenosis

set_option linter.unusedVariables false in

def Json.serializeValue (v : Kenosis.Value) : Except String String :=
  match v with
  | .bool b => .ok (if b then "true" else "false")
  | .int i => .ok (toString i)
  | .nat n => .ok (toString n)
  | .long n => .ok (toString n)
  | .str s => .ok ("\"" ++ escapeString s ++ "\"")
  | .null => .ok "null"
  | .list xs => do
      let inner ← xs.attach.mapM fun ⟨x, h⟩ => serializeValue x
      .ok ("[" ++ ", ".intercalate inner ++ "]")
  | .map kvs => do
      let pairs ← kvs.attach.mapM fun ⟨(k, v), h⟩ => do
        let key ← match k with
          | .str s => pure s
          | _ => .error "JSON object keys must be strings"
        let val ← serializeValue v
        pure ("\"" ++ key ++ "\": " ++ val)
      .ok ("{" ++ ", ".intercalate pairs ++ "}")
termination_by sizeOf v
decreasing_by
  all_goals simp_wf
  · have := List.sizeOf_lt_of_mem h; omega
  · have h1 := List.sizeOf_lt_of_mem h
    have h2 : sizeOf (k, v) = 1 + sizeOf k + sizeOf v := rfl
    omega

def Json.serialize (x : α) [Serialize α] : Except String String :=
  Json.serializeValue (Serialize.serialize x)

end Kenosis
