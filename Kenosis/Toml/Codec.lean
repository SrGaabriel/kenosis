import Kenosis.String

namespace Kenosis.Toml

open Kenosis
open Kenosis.String

structure TomlTag

abbrev TomlWriter (α : Type) := StringWriter TomlTag α
