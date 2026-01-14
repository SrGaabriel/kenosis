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
  let structNameStr := Syntax.mkStrLit (toString structName)
  let ctorIdent := mkCIdent (structName ++ `mk)
  let decodeStructBegin := mkCIdent ``Deserializer.decodeStructBegin
  let decodeField := mkCIdent ``Deserializer.decodeField
  let decodeStructEnd := mkCIdent ``Deserializer.decodeStructEnd
  let deserializeFn := mkCIdent ``Deserialize.deserialize
  let dIdent := mkRawIdent `d

  if fields.isEmpty then
    `($decodeStructBegin $argIdent $structNameStr >>= fun $dIdent =>
      $decodeStructEnd $dIdent >>= fun $dIdent =>
      pure ($ctorIdent, $dIdent))
  else
    let fieldIdents : Array Ident := fields.map fun f => mkRawIdent f
    let fieldArgs : TSyntaxArray `term := ⟨fieldIdents.map (⟨·⟩ : Ident → TSyntax `term) |>.toList⟩

    let mut result ← `(pure ($ctorIdent $fieldArgs*, $dIdent))

    result ← `($decodeStructEnd $dIdent >>= fun $dIdent => $result)

    for i in [:fields.size] do
      let idx := fields.size - 1 - i
      let fieldIdent := fieldIdents[idx]!
      let fieldNameStr := Syntax.mkStrLit (toString fields[idx]!)
      result ← `($decodeField $dIdent $fieldNameStr $deserializeFn >>= fun ($fieldIdent, $dIdent) => $result)

    result ← `($decodeStructBegin $argIdent $structNameStr >>= fun $dIdent => $result)

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

private def mkCtorDeserializeBody (ctorName : Name) (numFields : Nat) : MetaM (TSyntax `term) := do
  let ctorIdent := mkCIdent ctorName
  let decodeField := mkCIdent ``Deserializer.decodeField
  let decodeEnumEnd := mkCIdent ``Deserializer.decodeEnumEnd
  let deserializeFn := mkCIdent ``Deserialize.deserialize
  let dIdent := mkRawIdent `d

  if numFields == 0 then
    `($decodeEnumEnd $dIdent >>= fun $dIdent => pure ($ctorIdent, $dIdent))
  else
    let fieldIdents : Array Ident := (List.range numFields).toArray.map fun i =>
      mkRawIdent (Name.mkSimple s!"__field{i}")
    let fieldArgs : TSyntaxArray `term := ⟨fieldIdents.map (⟨·⟩ : Ident → TSyntax `term) |>.toList⟩

    let mut result ← `(pure ($ctorIdent $fieldArgs*, $dIdent))

    result ← `($decodeEnumEnd $dIdent >>= fun $dIdent => $result)

    for i in [:numFields] do
      let idx := numFields - 1 - i
      let fieldIdent := fieldIdents[idx]!
      let fieldNameStr := Syntax.mkStrLit s!"_{idx}"
      result ← `($decodeField $dIdent $fieldNameStr $deserializeFn >>= fun ($fieldIdent, $dIdent) => $result)

    return result

private def mkEnumDeserializeBody (view : InductiveVal) (argName : Name) : MetaM (TSyntax `term) := do
  let argIdent := mkRawIdent argName
  let decodeEnumBegin := mkCIdent ``Deserializer.decodeEnumBegin
  let variantIdent := mkRawIdent `variantName
  let dIdent := mkRawIdent `d

  let mut alts : Array (Syntax × Syntax) := #[]

  for ctorName in view.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let shortName := ctorName.getString!

    let numFields ← forallTelescopeReducing ctorInfo.type fun params _ => do
      let fieldParams := params[view.numParams:]
      return fieldParams.size

    let pat := Syntax.mkStrLit shortName
    let body ← mkCtorDeserializeBody ctorName numFields
    alts := alts.push (pat, body.raw)

  let wildPat ← `(_)
  let wildBody ← `(throw "unknown variant")
  alts := alts.push (wildPat.raw, wildBody.raw)

  let matchExpr : TSyntax `term := ⟨mkMatchExpr variantIdent alts⟩

  `($decodeEnumBegin $argIdent >>= fun ($variantIdent, $dIdent) => $matchExpr)

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
    if isStruct then
      let fields ← getStructureFieldNames declName
      mkStructDeserializeBody declName fields argName
    else
      mkEnumDeserializeBody view argName

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
