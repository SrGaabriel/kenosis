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

structure Box (α : Type) where
  value : α
  deriving Serialize, Deserialize, BEq, Repr

structure Pair (α : Type) (β : Type) where
  first : α
  second : β
  deriving Serialize, Deserialize, BEq, Repr

inductive MyResult (α : Type) (ε : Type)
  | ok (value : α)
  | err (error : ε)
  deriving Serialize, Deserialize, BEq, Repr

inductive Tree (α : Type)
  | leaf
  | node (value : α) (left : Tree α) (right : Tree α)
  deriving Serialize, Deserialize, BEq, Repr

inductive RoseTree (α : Type)
  | node (value : α) (children : List (RoseTree α))
  deriving Serialize, Deserialize, BEq, Repr

mutual
  inductive Expr
    | lit (n : Nat)
    | add (e1 e2 : Expr)
    | letIn (name : String) (value : Expr) (body : Stmt)
  deriving Serialize, Deserialize, BEq, Repr

  inductive Stmt
    | expr (e : Expr)
    | seq (s1 s2 : Stmt)
    | assign (name : String) (value : Expr)
  deriving Serialize, Deserialize, BEq, Repr
end

mutual
  inductive Forest (α : Type)
    | nil
    | cons (tree : MTree α) (rest : Forest α)
  deriving Serialize, Deserialize, BEq, Repr

  inductive MTree (α : Type)
    | node (value : α) (children : Forest α)
  deriving Serialize, Deserialize, BEq, Repr
end

inductive PrimTy where
  | i8 | i16 | i32 | i64
  | u8 | u16 | u32 | u64
  | f32 | f64
  | bool
  | unit
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

/-- Alloy types -/
inductive Ty : Nat → Type where
  /-- Primitive types -/
  | prim : PrimTy → Ty n
  /-- Pointer to a value of type t -/
  | ptr : Ty n → Ty n
  /-- Raw pointer (void*) -/
  | rawPtr : Ty n
  /-- Function pointer: (args) -> ret -/
  | funcPtr : Array (Ty n) → Ty n → Ty n
  /-- Struct type (product) with named fields -/
  | struct : Array (String × Ty n) → Ty n
  /-- Array type with static size -/
  | array : Ty n → Nat → Ty n
  /-- Tagged union (for ADTs): tag type + variant payloads -/
  | tagged : Ty n → Array (Nat × Array (Ty n)) → Ty n
  /-- Closure type: function pointer + environment pointer -/
  | closure : Array (Ty n) → Ty n → Ty n
  /-- Type variable (de Bruijn index into enclosing quantifiers) -/
  | var : Fin n → Ty n
  deriving Repr, BEq, Serialize, Deserialize

inductive UnOp (n : Nat) where
  | neg
  | not
  | trunc (to : PrimTy)
  | zext (to : PrimTy)
  | sext (to : PrimTy)
  | itof (to : PrimTy)
  | ftoi (to : PrimTy)
  | bitcast (to : Ty n)
  | ptrtoint (to : PrimTy)
  | inttoptr
  deriving BEq, Inhabited, Serialize, Deserialize

def testJson (name : String) (x : α) [Serialize α] [Deserialize α] [BEq α] [Repr α] : IO Bool := do
  IO.println s!"  Testing JSON: {name}"
  let encoded := Json.encode x
  IO.println s!"    Encoded: {encoded}"
  match Json.decode encoded with
  | .ok (y : α) =>
    if x == y then
      IO.println s!"    Roundtrip successful"
      return true
    else
      IO.println s!"    Roundtrip mismatch: {repr x} ≠ {repr y}"
      return false
  | .error e =>
    IO.println s!"    Decode failed: {e}"
    return false

def testBinary (name : String) (x : α) [Serialize α] [Deserialize α] [BEq α] [Repr α] : IO Bool := do
  IO.println s!"  Testing Binary: {name}"
  let encoded := Binary.encode x
  IO.println s!"    Encoded size: {encoded.size} bytes"
  match Binary.decode encoded with
  | .ok (y : α) =>
    if x == y then
      IO.println s!"    Roundtrip successful"
      return true
    else
      IO.println s!"    Roundtrip mismatch: {repr x}  != {repr y}"
      return false
  | .error e =>
    IO.println s!"    Decode failed: {e}"
    return false

def testBoth (name : String) (x : α) [Serialize α] [Deserialize α] [BEq α] [Repr α] : IO Bool := do
  IO.println s!"Testing: {name}"
  let jsonOk ← testJson name x
  let binaryOk ← testBinary name x
  IO.println ""
  return jsonOk && binaryOk

def testBinaryOnly (name : String) (x : α) [Serialize α] [Deserialize α] [BEq α] [Repr α] : IO Bool := do
  IO.println s!"Testing (Binary only): {name}"
  let binaryOk ← testBinary name x
  IO.println ""
  return binaryOk

def main : IO Unit := do
  IO.println "Diagnostic: Testing JSON parsing..."
  let testJson := "{\"name\": \"Alice\", \"age\": 30}"
  IO.println s!"  Input JSON: {testJson}"
  match Json.decode (α := Person) testJson with
  | .ok p => IO.println s!"  Direct decode succeeded: {repr p}"
  | .error e => IO.println s!"  Direct decode failed: {e}"
  match Json.decode (α := Nat) "42" with
  | .ok n => IO.println s!"  Nat decode succeeded: {n}"
  | .error e => IO.println s!"  Nat decode failed: {e}"
  IO.println ""

  let mut allPassed := true
  IO.println "Primitive Types"
  allPassed := allPassed && (← testBoth "Bool (true)" true)
  allPassed := allPassed && (← testBoth "Bool (false)" false)
  allPassed := allPassed && (← testBoth "Nat (0)" (0 : Nat))
  allPassed := allPassed && (← testBoth "Nat (42)" (42 : Nat))
  allPassed := allPassed && (← testBoth "Nat (large)" (123456789 : Nat))
  allPassed := allPassed && (← testBoth "Int (positive)" (42 : Int))
  allPassed := allPassed && (← testBoth "Int (negative)" (-42 : Int))
  allPassed := allPassed && (← testBoth "Int (zero)" (0 : Int))
  allPassed := allPassed && (← testBoth "String (empty)" "")
  allPassed := allPassed && (← testBoth "String (simple)" "Hello, World!")
  allPassed := allPassed && (← testBoth "String (unicode)" "Hello 世界 🌍")
  allPassed := allPassed && (← testBoth "String (escaped)" "Line1\nLine2\tTabbed\"Quoted\"")

  IO.println "Container Types"
  allPassed := allPassed && (← testBoth "Option none" (none : Option Nat))
  allPassed := allPassed && (← testBoth "Option some" (some 42 : Option Nat))
  allPassed := allPassed && (← testBoth "List (empty)" ([] : List Nat))
  allPassed := allPassed && (← testBoth "List (single)" ([42] : List Nat))
  allPassed := allPassed && (← testBoth "List (multiple)" ([1, 2, 3, 4, 5] : List Nat))
  allPassed := allPassed && (← testBoth "List (strings)" (["foo", "bar", "baz"] : List String))
  allPassed := allPassed && (← testBoth "Array (empty)" (#[] : Array Nat))
  allPassed := allPassed && (← testBoth "Array (multiple)" (#[1, 2, 3, 4, 5] : Array Nat))
  allPassed := allPassed && (← testBoth "Tuple" ((42, "hello") : Nat × String))
  allPassed := allPassed && (← testBoth "Sum (inl)" (Sum.inl 42 : Sum Nat String))
  allPassed := allPassed && (← testBoth "Sum (inr)" (Sum.inr "error" : Sum Nat String))

  IO.println "Custom Structures"
  let person := Person.mk "Alice" 30
  allPassed := allPassed && (← testBoth "Person" person)

  let employee := Employee.mk person "Engineering" (some "Bob")
  allPassed := allPassed && (← testBoth "Employee (with manager)" employee)

  let employee2 := Employee.mk person "Engineering" none
  allPassed := allPassed && (← testBoth "Employee (no manager)" employee2)

  let people := [Person.mk "Alice" 30, Person.mk "Bob" 25, Person.mk "Charlie" 35]
  allPassed := allPassed && (← testBoth "List of Persons" people)

  IO.println "Custom Enums"
  allPassed := allPassed && (← testBoth "Status (active)" Status.active)
  allPassed := allPassed && (← testBoth "Status (inactive)" Status.inactive)
  allPassed := allPassed && (← testBoth "Status (pending)" (Status.pending "awaiting approval"))

  IO.println "Nested Structures"
  let nested := (some [employee, employee2], Status.pending "review")
  allPassed := allPassed && (← testBoth "Nested (Option List Employee × Status)" nested)

  IO.println "Polymorphic Types"
  allPassed := allPassed && (← testBoth "Box Nat" (Box.mk 42 : Box Nat))
  allPassed := allPassed && (← testBoth "Box String" (Box.mk "hello" : Box String))
  allPassed := allPassed && (← testBoth "Pair Nat String" (Pair.mk 42 "hello" : Pair Nat String))
  allPassed := allPassed && (← testBoth "Pair Bool (List Nat)" (Pair.mk true [1, 2, 3] : Pair Bool (List Nat)))
  allPassed := allPassed && (← testBoth "MyResult ok" (MyResult.ok 42 : MyResult Nat String))
  allPassed := allPassed && (← testBoth "MyResult err" (MyResult.err "failed" : MyResult Nat String))
  allPassed := allPassed && (← testBoth "Nested polymorphic" (Box.mk (Pair.mk 1 "x") : Box (Pair Nat String)))

  IO.println "Recursive Types"
  allPassed := allPassed && (← testBoth "Tree (leaf)" (Tree.leaf : Tree Nat))
  allPassed := allPassed && (← testBoth "Tree (single node)" (Tree.node 42 Tree.leaf Tree.leaf : Tree Nat))
  let complexTree := Tree.node 1 (Tree.node 2 Tree.leaf Tree.leaf) (Tree.node 3 (Tree.node 4 Tree.leaf Tree.leaf) Tree.leaf)
  allPassed := allPassed && (← testBoth "Tree (complex)" complexTree)

  IO.println "Indirectly Recursive Types"
  let roseLeaf := RoseTree.node 1 []
  allPassed := allPassed && (← testBoth "RoseTree (leaf)" roseLeaf)
  let roseTree := RoseTree.node 1 [RoseTree.node 2 [], RoseTree.node 3 [RoseTree.node 4 []]]
  allPassed := allPassed && (← testBoth "RoseTree (complex)" roseTree)

  IO.println "Mutual Inductive Types"
  let simpleExpr := Expr.lit 42
  allPassed := allPassed && (← testBoth "Expr (lit)" simpleExpr)
  let addExpr := Expr.add (Expr.lit 1) (Expr.lit 2)
  allPassed := allPassed && (← testBoth "Expr (add)" addExpr)
  let simpleStmt := Stmt.expr (Expr.lit 10)
  allPassed := allPassed && (← testBoth "Stmt (expr)" simpleStmt)
  let seqStmt := Stmt.seq (Stmt.assign "x" (Expr.lit 1)) (Stmt.expr (Expr.lit 2))
  allPassed := allPassed && (← testBoth "Stmt (seq)" seqStmt)
  let letExpr := Expr.letIn "y" (Expr.add (Expr.lit 3) (Expr.lit 4)) (Stmt.assign "z" (Expr.lit 5))
  allPassed := allPassed && (← testBoth "Expr (letIn)" letExpr)

  let emptyForest : Forest Nat := Forest.nil
  allPassed := allPassed && (← testBoth "Forest (nil)" emptyForest)
  let singleTree := MTree.node 1 Forest.nil
  allPassed := allPassed && (← testBoth "MTree (single)" singleTree)
  let forest := Forest.cons (MTree.node 1 Forest.nil) (Forest.cons (MTree.node 2 Forest.nil) Forest.nil)
  allPassed := allPassed && (← testBoth "Forest (multiple trees)" forest)
  let nestedTree := MTree.node 0 (Forest.cons (MTree.node 1 (Forest.cons (MTree.node 2 Forest.nil) Forest.nil)) Forest.nil)
  allPassed := allPassed && (← testBoth "MTree (nested)" nestedTree)

  if allPassed then
    IO.println "All tests passed!"
  else
    IO.println "Some tests failed"
    IO.Process.exit 1
