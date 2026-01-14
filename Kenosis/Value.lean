namespace Kenosis

inductive KenosisValue where
  | bool : Bool → KenosisValue
  | int : Int → KenosisValue
  | nat : Nat → KenosisValue
  | long : Int64 → KenosisValue
  | str : String → KenosisValue
  | list : List KenosisValue → KenosisValue
  | null : KenosisValue
  | map : List (KenosisValue × KenosisValue) → KenosisValue