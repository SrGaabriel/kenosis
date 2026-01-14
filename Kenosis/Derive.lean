import Lean
import Kenosis.Serialize

namespace Kenosis

open Lean Elab Command Term Meta Syntax

private def mkRawIdent (n : Name) : Ident :=
  ⟨Syntax.ident SourceInfo.none n.toString.toSubstring n []⟩

private def mkRawQualIdent (n : Name) : Ident := mkRawIdent n

private def getStructureFields (structName : Name) : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let some structInfo := getStructureInfo? env structName | return #[]
  let mut fields : Array (Name × Name) := #[]
  for field in structInfo.fieldNames do
    fields := fields.push (field, structName ++ field)
  return fields

private def mkStructSerializeBody (_structName : Name) (fields : Array (Name × Name)) (argName : Name) : MetaM (TSyntax `term) := do
  if fields.isEmpty then
    `(Kenosis.Value.obj Kenosis.emptyObj)
  else
    let argIdent := mkRawIdent argName
    let serializeFn := mkCIdent ``Serialize.serialize
    let mut result ← `(Kenosis.emptyObj)
    for (fieldName, projName) in fields do
      let fieldStr := toString fieldName
      let projIdent := mkCIdent projName
      let fieldAccess ← `($projIdent $argIdent)
      let serializedField ← `($serializeFn $fieldAccess)
      let fieldStrLit := Syntax.mkStrLit fieldStr
      result ← `(($result).insert $fieldStrLit $serializedField)
    `(Kenosis.Value.obj $result)

private def mkCtorMatchAlt (view : InductiveVal) (ctorName : Name) : MetaM (Syntax × Syntax) := do
  let ctorInfo ← getConstInfoCtor ctorName
  let shortName := ctorName.getString!
  let serializeFn := mkCIdent ``Serialize.serialize
  let ctorIdent := mkRawQualIdent ctorName

  forallTelescopeReducing ctorInfo.type fun params _ => do
    let fieldParams := params[view.numParams:]
    let tagStrLit := Syntax.mkStrLit shortName

    if fieldParams.size == 0 then
      let pat : TSyntax `term := ⟨ctorIdent⟩
      let body ← `(Kenosis.Value.str $tagStrLit)
      return (pat.raw, body.raw)
    else if fieldParams.size == 1 then
      let fieldName := "__field0"
      let fieldIdent := mkRawIdent (Name.mkSimple fieldName)
      let patternArgs : TSyntaxArray `term := ⟨[(⟨mkRawIdent (Name.mkSimple fieldName)⟩ : TSyntax `term)]⟩
      let pat ← `($ctorIdent $patternArgs*)
      let serializedField ← `($serializeFn $fieldIdent)
      let body ← `(Kenosis.Value.obj (Kenosis.emptyObj.insert $tagStrLit $serializedField))
      return (pat.raw, body.raw)
    else
      let mut fieldNames : Array String := #[]
      for i in [:fieldParams.size] do
        fieldNames := fieldNames.push s!"__field{i}"

      let patternArgs : TSyntaxArray `term := ⟨(fieldNames.map fun n => (⟨mkRawIdent (Name.mkSimple n)⟩ : TSyntax `term)).toList⟩
      let pat ← `($ctorIdent $patternArgs*)

      let mut fieldExprs : Array (TSyntax `term) := #[]
      for fieldName in fieldNames do
        let fieldIdent := mkRawIdent (Name.mkSimple fieldName)
        let serializedField ← `($serializeFn $fieldIdent)
        fieldExprs := fieldExprs.push serializedField
      let listExpr ← `([$fieldExprs,*])
      let body ← `(Kenosis.Value.obj (Kenosis.emptyObj.insert $tagStrLit (Kenosis.Value.list $listExpr)))
      return (pat.raw, body.raw)

private def mkMatchExpr (discr : Syntax) (alts : Array (Syntax × Syntax)) : Syntax :=
  let matchAlts := alts.map fun (pat, body) =>
    let patList := Syntax.node SourceInfo.none `null #[pat]
    let patListList := Syntax.node SourceInfo.none `null #[patList]
    Syntax.node SourceInfo.none ``Parser.Term.matchAlt #[mkAtom "|", patListList, mkAtom "=>", body]
  let matchAltsList := Syntax.node SourceInfo.none `null matchAlts
  let matchAltsNode := Syntax.node SourceInfo.none ``Parser.Term.matchAlts #[matchAltsList]
  let discrNode := Syntax.node SourceInfo.none ``Parser.Term.matchDiscr #[
    Syntax.node SourceInfo.none `null #[],
    discr
  ]
  Syntax.node SourceInfo.none ``Parser.Term.match #[
    mkAtom "match",
    Syntax.node SourceInfo.none `null #[],
    Syntax.node SourceInfo.none `null #[],
    Syntax.node SourceInfo.none `null #[discrNode],
    mkAtom "with",
    matchAltsNode
  ]

private def mkEnumSerializeBody (view : InductiveVal) (argName : Name) : MetaM (TSyntax `term) := do
  let argIdent := mkRawIdent argName

  let mut alts : Array (Syntax × Syntax) := #[]
  for ctorName in view.ctors do
    let alt ← mkCtorMatchAlt view ctorName
    alts := alts.push alt

  if alts.isEmpty then
    `(panic! "empty enum")
  else
    let matchExpr := mkMatchExpr argIdent alts
    return ⟨matchExpr⟩

def mkSerializeHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false

  let declName := declNames[0]!
  let env ← getEnv

  let some info := env.find? declName | return false
  let .inductInfo view := info | return false

  let isStruct := view.ctors.length == 1 && (view.ctors[0]!).getString! == "mk"

  let argName := Name.mkSimple "__serialArg"

  let serializeBody ← liftTermElabM do
    if isStruct then
      let fields ← getStructureFields declName
      mkStructSerializeBody declName fields argName
    else
      mkEnumSerializeBody view argName

  let typeIdent := mkCIdent declName
  let serializeClass := mkCIdent ``Serialize
  let argIdent := mkRawIdent argName

  let cmd ← `(command|
    instance : $serializeClass $typeIdent where
      serialize := fun $argIdent => $serializeBody
  )

  elabCommand cmd
  return true

initialize registerDerivingHandler ``Serialize mkSerializeHandler

end Kenosis
