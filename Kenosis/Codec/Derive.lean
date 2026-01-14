import Lean
import Kenosis.Codec

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
  let argIdent := mkRawIdent argName
  let serializeFn := mkCIdent ``Serialize.serialize
  let putObjectFn := mkCIdent ``Encoder.putObject

  if fields.isEmpty then
    `($putObjectFn [])
  else
    let mut fieldExprs : Array (TSyntax `term) := #[]
    for (fieldName, projName) in fields do
      let fieldStr := Syntax.mkStrLit (toString fieldName)
      let projIdent := mkCIdent projName
      let fieldAccess ← `($projIdent $argIdent)
      let serializedField ← `($serializeFn $fieldAccess)
      let pair ← `(($fieldStr, $serializedField))
      fieldExprs := fieldExprs.push pair
    `($putObjectFn [$fieldExprs,*])

private def mkCtorSerializeAlt (view : InductiveVal) (ctorIdx : Nat) (ctorName : Name) : MetaM (Syntax × Syntax) := do
  let ctorInfo ← getConstInfoCtor ctorName
  let shortName := ctorName.getString!
  let serializeFn := mkCIdent ``Serialize.serialize
  let putVariantFn := mkCIdent ``Encoder.putVariant
  let putListFn := mkCIdent ``Encoder.putList
  let ctorIdent := mkRawQualIdent ctorName
  let idxLit := Syntax.mkNumLit (toString ctorIdx)
  let tagStrLit := Syntax.mkStrLit shortName

  forallTelescopeReducing ctorInfo.type fun params _ => do
    let fieldParams := params[view.numParams:]

    if fieldParams.size == 0 then
      let pat : TSyntax `term := ⟨ctorIdent⟩
      let body ← `($putVariantFn $idxLit $tagStrLit none)
      return (pat.raw, body.raw)
    else if fieldParams.size == 1 then
      let fieldName := "__field0"
      let fieldIdent := mkRawIdent (Name.mkSimple fieldName)
      let patternArgs : TSyntaxArray `term := ⟨[(⟨fieldIdent⟩ : TSyntax `term)]⟩
      let pat ← `($ctorIdent $patternArgs*)
      let serializedField ← `($serializeFn $fieldIdent)
      let body ← `($putVariantFn $idxLit $tagStrLit (some $serializedField))
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

      let listExpr ← `($putListFn [$fieldExprs,*])
      let body ← `($putVariantFn $idxLit $tagStrLit (some $listExpr))
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
  for (idx, ctorName) in view.ctors.toArray.mapIdx (·, ·) do
    let alt ← mkCtorSerializeAlt view idx ctorName
    alts := alts.push alt

  if alts.isEmpty then
    `(panic! "empty enum")
  else
    let matchExpr := mkMatchExpr argIdent alts
    return ⟨matchExpr⟩

private def getTypeParams (view : InductiveVal) : MetaM (Array Name) := do
  let ctorName := view.ctors[0]!
  let ctorInfo ← getConstInfoCtor ctorName
  forallTelescopeReducing ctorInfo.type fun params _ => do
    let typeParams := params[:view.numParams]
    let mut names : Array Name := #[]
    for param in typeParams do
      let name ← param.fvarId!.getUserName
      names := names.push name
    return names

def mkSerializeHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false

  let declName := declNames[0]!
  let env ← getEnv

  let some info := env.find? declName | return false
  let .inductInfo view := info | return false

  let isStruct := view.ctors.length == 1 && (view.ctors[0]!).getString! == "mk"

  let argName := Name.mkSimple "__serialArg"

  let (serializeBody, typeParamNames) ← liftTermElabM do
    let body ← if isStruct then
      let fields ← getStructureFields declName
      mkStructSerializeBody declName fields argName
    else
      mkEnumSerializeBody view argName
    let typeParams ← getTypeParams view
    return (body, typeParams)

  let typeIdent := mkCIdent declName
  let serializeClass := mkCIdent ``Serialize
  let argIdent := mkRawIdent argName

  let appliedType : TSyntax `term ←
    if typeParamNames.isEmpty then
      pure ⟨typeIdent⟩
    else
      let paramIdents : TSyntaxArray `term := ⟨typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term)) |>.toList⟩
      `($typeIdent $paramIdents*)

  let mut sigType : TSyntax `term ← `($serializeClass $appliedType)
  for n in typeParamNames.reverse do
    let paramIdent := mkIdent n
    sigType ← `([$serializeClass $paramIdent] → $sigType)

  let cmd ← `(command|
    instance : $sigType where
      serialize := fun $argIdent => $serializeBody
  )

  elabCommand cmd
  return true

initialize registerDerivingHandler ``Serialize mkSerializeHandler

private def getStructureFieldNames (structName : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some structInfo := getStructureInfo? env structName | return #[]
  return structInfo.fieldNames

private def mkStructDeserializeBody (structName : Name) (fields : Array Name) (argName : Name) : MetaM (TSyntax `term) := do
  let _ := mkRawIdent argName
  let ctorIdent := mkCIdent (structName ++ `mk)
  let getFieldFn := mkCIdent ``Decoder.getField
  let deserializeFn := mkCIdent ``Deserialize.deserialize

  if fields.isEmpty then
    `(pure $ctorIdent)
  else
    let fieldIdents : Array Ident := fields.map fun f => mkRawIdent f
    let fieldArgs : TSyntaxArray `term := ⟨fieldIdents.map (⟨·⟩ : Ident → TSyntax `term) |>.toList⟩

    let mut result ← `(pure ($ctorIdent $fieldArgs*))

    for i in [:fields.size] do
      let idx := fields.size - 1 - i
      let fieldIdent := fieldIdents[idx]!
      let fieldNameStr := Syntax.mkStrLit (toString fields[idx]!)
      result ← `($getFieldFn $fieldNameStr $deserializeFn >>= fun $fieldIdent => $result)

    pure result

private def mkEnumDeserializeBody (view : InductiveVal) (_argName : Name) : MetaM (TSyntax `term) := do
  let matchVariantFn := mkCIdent ``Decoder.matchVariant
  let deserializeFn := mkCIdent ``Deserialize.deserialize
  let failFn := mkCIdent ``Decoder.fail
  let numCtors := Syntax.mkNumLit (toString view.ctors.length)

  let mut indexAlts : Array (TSyntax `term × TSyntax `term) := #[]
  for (idx, ctorName) in view.ctors.toArray.mapIdx (·, ·) do
    let ctorInfo ← getConstInfoCtor ctorName
    let ctorIdent := mkCIdent ctorName
    let idxLit : TSyntax `term := ⟨Syntax.mkNumLit (toString idx)⟩

    let numFields ← forallTelescopeReducing ctorInfo.type fun params _ => do
      let fieldParams := params[view.numParams:]
      return fieldParams.size

    let body ← if numFields == 0 then
      `(pure $ctorIdent)
    else if numFields == 1 then
      `($ctorIdent <$> $deserializeFn)
    else
      let mut fieldIdents : Array Ident := #[]
      for i in [:numFields] do
        fieldIdents := fieldIdents.push (mkRawIdent (Name.mkSimple s!"__f{i}"))
      let fieldArgs : TSyntaxArray `term := ⟨fieldIdents.map (⟨·⟩ : Ident → TSyntax `term) |>.toList⟩

      let mut innerResult ← `(pure ($ctorIdent $fieldArgs*))
      for i in [:numFields] do
        let ridx := numFields - 1 - i
        let fieldIdent := fieldIdents[ridx]!
        innerResult ← `($deserializeFn >>= fun $fieldIdent => $innerResult)

      pure innerResult

    indexAlts := indexAlts.push (idxLit, body)

  let mut nameAlts : Array (TSyntax `term × TSyntax `term) := #[]
  for (idx, ctorName) in view.ctors.toArray.mapIdx (·, ·) do
    let shortName := ctorName.getString!
    let tagStrLit : TSyntax `term := ⟨Syntax.mkStrLit shortName⟩

    let body := indexAlts[idx]!.2
    nameAlts := nameAlts.push (tagStrLit, body)

  let idxIdent := mkRawIdent `__idx
  let nameIdent := mkRawIdent `__name

  let mut indexMatchAlts : Array (Syntax × Syntax) := #[]
  for (pat, body) in indexAlts do
    indexMatchAlts := indexMatchAlts.push (pat.raw, body.raw)
  let defaultIdx ← `($failFn s!"invalid variant index: {$idxIdent}")
  let wildPat ← `(_)
  indexMatchAlts := indexMatchAlts.push (wildPat.raw, defaultIdx.raw)

  let mut nameMatchAlts : Array (Syntax × Syntax) := #[]
  for (pat, body) in nameAlts do
    nameMatchAlts := nameMatchAlts.push (pat.raw, body.raw)
  let defaultName ← `($failFn s!"unknown variant: {$nameIdent}")
  nameMatchAlts := nameMatchAlts.push (wildPat.raw, defaultName.raw)

  let indexMatch : TSyntax `term := ⟨mkMatchExpr idxIdent indexMatchAlts⟩
  let nameMatch : TSyntax `term := ⟨mkMatchExpr nameIdent nameMatchAlts⟩

  `($matchVariantFn $numCtors (fun $idxIdent => $indexMatch) (fun $nameIdent => $nameMatch))

def mkDeserializeHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false

  let declName := declNames[0]!
  let env ← getEnv

  let some info := env.find? declName | return false
  let .inductInfo view := info | return false

  let isStruct := view.ctors.length == 1 && (view.ctors[0]!).getString! == "mk"
  let argName := Name.mkSimple "__deserialArg"

  let (deserializeBody, typeParamNames) ← liftTermElabM do
    let body ← if isStruct then
      let fields ← getStructureFieldNames declName
      mkStructDeserializeBody declName fields argName
    else
      mkEnumDeserializeBody view argName
    let typeParams ← getTypeParams view
    return (body, typeParams)

  let typeIdent := mkCIdent declName
  let deserializeClass := mkCIdent ``Deserialize
  let _ := mkRawIdent argName

  let appliedType : TSyntax `term ←
    if typeParamNames.isEmpty then
      pure ⟨typeIdent⟩
    else
      let paramIdents : TSyntaxArray `term := ⟨typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term)) |>.toList⟩
      `($typeIdent $paramIdents*)

  let mut sigType : TSyntax `term ← `($deserializeClass $appliedType)
  for n in typeParamNames.reverse do
    let paramIdent := mkIdent n
    sigType ← `([$deserializeClass $paramIdent] → $sigType)

  let cmd ← `(command|
    instance : $sigType where
      deserialize := $deserializeBody
  )

  elabCommand cmd
  return true

initialize registerDerivingHandler ``Deserialize mkDeserializeHandler

end Kenosis
