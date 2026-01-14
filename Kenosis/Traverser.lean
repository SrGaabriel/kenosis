namespace Kenosis

structure TraversingContext where
  scope : String
  field : Option String

inductive TraversingError where
  | missingField (name : String) (scope : String)
  | notExtractable (field : String) (scope : String)
  | expectedType (expected : String) (field : String)
  | unknownVariant (tag : String) (scope : String)
  deriving Repr

instance : ToString TraversingError where
  toString
    | .missingField name scope => s!"Missing field '{name}' in '{scope}'"
    | .notExtractable field scope => s!"Field '{field}' is not extractable in '{scope}'"
    | .expectedType expected field => s!"Expected {expected} for field '{field}'"
    | .unknownVariant tag scope => s!"Unknown variant '{tag}' in '{scope}'"

abbrev TraverserM := ExceptT TraversingError (ReaderM TraversingContext)

def TraverserM.missingField (name : String) : TraverserM a := do
  let ctx <- read
  throw $ TraversingError.missingField name ctx.scope

def TraverserM.notExtractable (field : String) : TraverserM a := do
  let ctx <- read
  throw $ TraversingError.missingField field ctx.scope

def TraverserM.expectedType (expected : String) : TraverserM a := do
  let ctx ← read
  throw $ TraversingError.expectedType expected (ctx.field.getD "<unknown>")

def TraverserM.expectedNat : TraverserM a := TraverserM.expectedType "a natural number"

def TraverserM.expectedInt : TraverserM a := TraverserM.expectedType "an integer"

def TraverserM.expectedStr : TraverserM a := TraverserM.expectedType "a string"

def TraverserM.expectedBool : TraverserM a := TraverserM.expectedType "a boolean"

def TraverserM.expectedList : TraverserM a := TraverserM.expectedType "a list"

def TraverserM.unknownVariant (tag : String) : TraverserM a := do
  let ctx ← read
  throw $ .unknownVariant ctx.scope tag
