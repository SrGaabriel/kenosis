import Lean
import Kenosis.Deserialize

namespace Kenosis

open Lean Elab Command Term Meta Syntax

private def mkRawIdent (n : Name) : Ident :=
  ⟨Syntax.ident SourceInfo.none n.toString.toSubstring n []⟩

private def getStructureFieldNames (structName : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some structInfo := getStructureInfo? env structName | return #[]
  return structInfo.fieldNames

private def mkStructDeserializeBody (structName : Name) (fields : Array Name) (argName : Name) : MetaM (TSyntax `term) := do
  let argIdent := mkRawIdent argName
  let ctorIdent := mkCIdent (structName ++ `mk)
  let fieldOp := mkCIdent ``Deserializer.field

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
      result ← `($fieldOp $argIdent $fieldNameStr >>= fun $fieldIdent => $result)

    return result

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

private def mkListPattern (n : Nat) : MetaM (TSyntax `term × Array Ident) := do
  let fieldIdents : Array Ident := (List.range n).toArray.map fun i =>
    mkRawIdent (Name.mkSimple s!"__f{i}")
  let fieldTerms : TSyntaxArray `term := ⟨fieldIdents.map (⟨·⟩ : Ident → TSyntax `term) |>.toList⟩
  let pat ← `([$fieldTerms,*])
  return (pat, fieldIdents)

private def mkCtorDeserializeFromList (ctorName : Name) (numFields : Nat) : MetaM (TSyntax `term) := do
  let ctorIdent := mkCIdent ctorName
  let deserializeFn := mkCIdent ``Deserialize.deserialize
  let listIdent := mkRawIdent `__list
  let expectedTypeFn := mkCIdent ``DeserializeM.expectedType

  if numFields == 0 then
    `(pure $ctorIdent)
  else
    let (listPat, fieldIdents) ← mkListPattern numFields
    let deserializedIdents : Array Ident := fieldIdents.map fun id =>
      mkRawIdent (Name.mkSimple s!"{id.getId}_d")
    let deserializedArgs : TSyntaxArray `term := ⟨deserializedIdents.map (⟨·⟩ : Ident → TSyntax `term) |>.toList⟩

    let mut result ← `(pure ($ctorIdent $deserializedArgs*))

    for i in [:numFields] do
      let idx := numFields - 1 - i
      let fieldIdent := fieldIdents[idx]!
      let deserializedIdent := deserializedIdents[idx]!
      result ← `($deserializeFn $fieldIdent >>= fun $deserializedIdent => $result)

    let expectedMsg := s!"a list with {numFields} elements"
    let alts : Array (Syntax × Syntax) := #[
      (listPat.raw, result.raw),
      ((← `(_)).raw, (← `($expectedTypeFn $(Syntax.mkStrLit expectedMsg))).raw)
    ]
    return ⟨mkMatchExpr listIdent alts⟩

private def mkCtorDeserializeBody (ctorName : Name) (numFields : Nat) (dataIdent : Ident) : MetaM (TSyntax `term) := do
  let ctorIdent := mkCIdent ctorName
  let deserializeFn := mkCIdent ``Deserialize.deserialize
  let expectedTypeFn := mkCIdent ``DeserializeM.expectedType

  if numFields == 0 then
    `(pure $ctorIdent)
  else if numFields == 1 then
    let fieldIdent := mkRawIdent (Name.mkSimple "__field0")
    `($deserializeFn $dataIdent >>= fun $fieldIdent => pure ($ctorIdent $fieldIdent))
  else
    let listIdent := mkRawIdent `__list
    let listBody ← mkCtorDeserializeFromList ctorName numFields
    let alts : Array (Syntax × Syntax) := #[
      ((← `(.list $listIdent)).raw, listBody.raw),
      ((← `(_)).raw, (← `($expectedTypeFn "a list for enum variant with multiple fields")).raw)
    ]
    return ⟨mkMatchExpr dataIdent alts⟩

private def mkEnumDeserializeBody (view : InductiveVal) (argName : Name) : MetaM (TSyntax `term) := do
  let argIdent := mkRawIdent argName
  let tagIdent := mkRawIdent `__tag
  let dataIdent := mkRawIdent `__data
  let unknownVariantFn := mkCIdent ``DeserializeM.unknownVariant
  let expectedTypeFn := mkCIdent ``DeserializeM.expectedType

  let mut dataAlts : Array (Syntax × Syntax) := #[]
  let mut tagOnlyAlts : Array (Syntax × Syntax) := #[]

  for ctorName in view.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let shortName := ctorName.getString!
    let ctorIdent := mkCIdent ctorName
    let tagStr := Syntax.mkStrLit shortName

    let numFields ← forallTelescopeReducing ctorInfo.type fun params _ => do
      let fieldParams := params[view.numParams:]
      return fieldParams.size

    if numFields == 0 then
      let body ← `(pure $ctorIdent)
      tagOnlyAlts := tagOnlyAlts.push (tagStr, body.raw)
    else
      let body ← mkCtorDeserializeBody ctorName numFields dataIdent
      let wrappedBody ← `(withReader (fun ctx => {ctx with scope := $tagStr}) $body)
      dataAlts := dataAlts.push (tagStr, wrappedBody.raw)

  let defaultBody ← `($unknownVariantFn $tagIdent)
  let wildPat ← `(_)
  tagOnlyAlts := tagOnlyAlts.push (wildPat.raw, defaultBody.raw)
  dataAlts := dataAlts.push (wildPat.raw, defaultBody.raw)

  let tagOnlyMatch : TSyntax `term := ⟨mkMatchExpr tagIdent tagOnlyAlts⟩
  let dataMatch : TSyntax `term := ⟨mkMatchExpr tagIdent dataAlts⟩

  let mapIdent := mkRawIdent `__map
  let pairListIdent := mkRawIdent `__pairList

  let innerMatchAlts : Array (Syntax × Syntax) := #[
    ((← `([($tagIdent, $dataIdent)])).raw, dataMatch.raw),
    ((← `(_)).raw, (← `($expectedTypeFn "a single-entry map for enum")).raw)
  ]
  let innerMatch : TSyntax `term := ⟨mkMatchExpr pairListIdent innerMatchAlts⟩

  let objBody ← `(let $pairListIdent := ($mapIdent).toList; $innerMatch)

  let outerAlts : Array (Syntax × Syntax) := #[
    ((← `(.str $tagIdent)).raw, tagOnlyMatch.raw),
    ((← `(.obj $mapIdent)).raw, objBody.raw),
    ((← `(_)).raw, (← `($expectedTypeFn "a string or single-entry map for enum")).raw)
  ]
  return ⟨mkMatchExpr argIdent outerAlts⟩

def mkDeserializeHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false

  let declName := declNames[0]!
  let env ← getEnv

  let some info := env.find? declName | return false
  let .inductInfo view := info | return false

  let isStruct := view.ctors.length == 1 && (view.ctors[0]!).getString! == "mk"
  let argName := Name.mkSimple "__deserialArg"

  let deserializeBody ← liftTermElabM do
    let body ← if isStruct then
      let fields ← getStructureFieldNames declName
      mkStructDeserializeBody declName fields argName
    else
      mkEnumDeserializeBody view argName
    `(withReader (fun ctx => {ctx with scope := "root"}) $body)

  let typeIdent := mkCIdent declName
  let deserializeClass := mkCIdent ``Deserialize
  let argIdent := mkRawIdent argName

  let cmd ← `(command|
    instance : $deserializeClass $typeIdent where
      deserialize := fun $argIdent => $deserializeBody
  )

  elabCommand cmd
  return true

initialize registerDerivingHandler ``Deserialize mkDeserializeHandler

end Kenosis
