import Kenosis.Json.Write
import Kenosis.Json.Read

namespace Kenosis

def Json.serialize (x : α) [Serialize α] : Except String String :=
  Json.compileValue (Serialize.serialize x)
