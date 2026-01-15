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

private def mkCtorSerializeAlt (view : InductiveVal) (ctorIdx : Nat) (ctorName : Name) (recFnMap : List (Name × Ident) := []) : MetaM (Syntax × Syntax) := do
  let ctorInfo ← getConstInfoCtor ctorName
  let shortName := ctorName.getString!
  let serializeFn := mkCIdent ``Serialize.serialize
  let putVariantFn := mkCIdent ``Encoder.putVariant
  let putObjectFn := mkCIdent ``Encoder.putObject
  let ctorIdent := mkRawQualIdent ctorName
  let idxLit := Syntax.mkNumLit (toString ctorIdx)
  let tagStrLit := Syntax.mkStrLit shortName

  let findRecFn (paramType : Expr) : Option Ident :=
    recFnMap.find? (fun (n, _) => paramType.isAppOf n) |>.map (·.2)

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
      let paramType ← inferType fieldParams[0]!
      let serializedField ← match findRecFn paramType with
        | some recFnIdent => `($recFnIdent $fieldIdent)
        | none => `($serializeFn $fieldIdent)
      let body ← `($putVariantFn $idxLit $tagStrLit (some $serializedField))
      return (pat.raw, body.raw)
    else
      let mut fieldNames : Array String := #[]
      for i in [:fieldParams.size] do
        fieldNames := fieldNames.push s!"__field{i}"

      let patternArgs : TSyntaxArray `term := ⟨(fieldNames.map fun n => (⟨mkRawIdent (Name.mkSimple n)⟩ : TSyntax `term)).toList⟩
      let pat ← `($ctorIdent $patternArgs*)

      let mut fieldPairs : Array (TSyntax `term) := #[]
      for i in [:fieldParams.size] do
        let fieldName := fieldNames[i]!
        let fieldIdent := mkRawIdent (Name.mkSimple fieldName)
        let paramType ← inferType fieldParams[i]!
        let serializedField ← match findRecFn paramType with
          | some recFnIdent => `($recFnIdent $fieldIdent)
          | none => `($serializeFn $fieldIdent)
        let keyStr := Syntax.mkStrLit s!"_{i}"
        let pair ← `(($keyStr, $serializedField))
        fieldPairs := fieldPairs.push pair

      let objExpr ← `($putObjectFn [$fieldPairs,*])
      let body ← `($putVariantFn $idxLit $tagStrLit (some $objExpr))
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

private def mkEnumSerializeBody (view : InductiveVal) (argName : Name) (recFnMap : List (Name × Ident) := []) : MetaM (TSyntax `term) := do
  let argIdent := mkRawIdent argName

  let mut alts : Array (Syntax × Syntax) := #[]
  for (idx, ctorName) in view.ctors.toArray.mapIdx (·, ·) do
    let alt ← mkCtorSerializeAlt view idx ctorName recFnMap
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

private def typeContainsName (targetName : Name) (e : Expr) : Bool :=
  e.find? (fun sub => sub.isAppOf targetName) |>.isSome

private def typeContainsAnyName (targetNames : List Name) (e : Expr) : Bool :=
  targetNames.any (typeContainsName · e)

private def isMutualInductiveBlock (view : InductiveVal) : Bool :=
  view.all.length > 1

private def isRecursiveType (view : InductiveVal) : MetaM Bool := do
  for ctorName in view.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let isRec ← forallTelescopeReducing ctorInfo.type fun params _ => do
      let fieldParams := params[view.numParams:]
      for param in fieldParams do
        let paramType ← inferType param
        if typeContainsName view.name paramType then
          return true
      return false
    if isRec then return true
  return false

private def countCtorFields (view : InductiveVal) (ctorName : Name) : MetaM (Nat × Nat) := do
  let ctorInfo ← getConstInfoCtor ctorName
  forallTelescopeReducing ctorInfo.type fun params _ => do
    let fieldParams := params[view.numParams:]
    fieldParams.foldlM (init := (0, 0)) fun (nonRec, rec) param => do
      let paramType ← inferType param
      if view.all.any (paramType.isAppOf ·) then
        return (nonRec, rec + 1)
      else
        return (nonRec + 1, rec)

private def findBaseConstructor (view : InductiveVal) : MetaM (Option (Name × Nat × Nat)) := do
  let mut best : Option (Name × Nat × Nat) := none
  for ctorName in view.ctors do
    let (nonRecCount, recCount) ← countCtorFields view ctorName
    if recCount == 0 then
      match best with
      | none => best := some (ctorName, nonRecCount, recCount)
      | some (_, bestNonRec, _) =>
          if nonRecCount < bestNonRec then
            best := some (ctorName, nonRecCount, recCount)
  return best

private def mkInhabitedInstance (view : InductiveVal) (typeParamNames : Array Name) : CommandElabM Unit := do
  let some (ctorName, numNonRecFields, _) := (← liftTermElabM <| findBaseConstructor view) | return
  let typeIdent := mkCIdent view.name
  let ctorIdent := mkCIdent ctorName
  let inhabitedClass := mkCIdent ``Inhabited

  let appliedType : TSyntax `term ←
    if typeParamNames.isEmpty then
      pure ⟨typeIdent⟩
    else
      let paramIdents : TSyntaxArray `term := ⟨typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term)) |>.toList⟩
      `($typeIdent $paramIdents*)

  let defaultExpr ← if numNonRecFields == 0 then
    pure ⟨ctorIdent⟩
  else
    let defaultIdent := mkCIdent ``default
    let defaults : TSyntaxArray `term := ⟨(List.replicate numNonRecFields (⟨defaultIdent⟩ : TSyntax `term))⟩
    `($ctorIdent $defaults*)

  let mut sigType : TSyntax `term ← `($inhabitedClass $appliedType)
  if numNonRecFields > 0 then
    for n in typeParamNames.reverse do
      let paramIdent := mkIdent n
      sigType ← `([$inhabitedClass $paramIdent] → $sigType)

  let cmd ← `(command|
    instance : $sigType where
      default := $defaultExpr
  )
  elabCommand cmd

private def findBestConstructorForInhabited (view : InductiveVal) : MetaM (Option (Name × Nat × Nat)) := do
  let baseResult ← findBaseConstructor view
  if baseResult.isSome then return baseResult

  let mut best : Option (Name × Nat × Nat) := none
  for ctorName in view.ctors do
    let (nonRecCount, recCount) ← countCtorFields view ctorName
    let totalFields := nonRecCount + recCount
    match best with
    | none => best := some (ctorName, nonRecCount, recCount)
    | some (_, bestNonRec, bestRec) =>
        if totalFields < bestNonRec + bestRec then
          best := some (ctorName, nonRecCount, recCount)
  return best

private def mkMutualInhabitedInstances (views : Array InductiveVal) (typeParamNames : Array Name) : CommandElabM Unit := do
  let inhabitedClass := mkCIdent ``Inhabited

  let mut instanceInfos : Array (Name × Name × Nat × Nat) := #[]
    let some (ctorName, numNonRecFields, numRecFields) := (← liftTermElabM <| findBestConstructorForInhabited view) | continue
    instanceInfos := instanceInfos.push (view.name, ctorName, numNonRecFields, numRecFields)

  if instanceInfos.isEmpty then return

  let anyNeedsInhabitedConstraints := instanceInfos.any fun (_, _, nonRec, _) => nonRec > 0

  let sortedInfos := instanceInfos.qsort fun (_, _, _, rec1) (_, _, _, rec2) => rec1 < rec2

  for (typeName, ctorName, numNonRecFields, numRecFields) in sortedInfos do
    let typeIdent := mkCIdent typeName
    let ctorIdent := mkCIdent ctorName

    let appliedType : TSyntax `term ←
      if typeParamNames.isEmpty then
        pure ⟨typeIdent⟩
      else
        let paramIdents : TSyntaxArray `term := ⟨typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term)) |>.toList⟩
        `($typeIdent $paramIdents*)

    let totalFields := numNonRecFields + numRecFields
    let defaultExpr ← if totalFields == 0 then
      pure ⟨ctorIdent⟩
    else
      let defaultIdent := mkCIdent ``default
      let defaults : TSyntaxArray `term := ⟨(List.replicate totalFields (⟨defaultIdent⟩ : TSyntax `term))⟩
      `($ctorIdent $defaults*)

    let mut sigType : TSyntax `term ← `($inhabitedClass $appliedType)
    if anyNeedsInhabitedConstraints then
      for n in typeParamNames.reverse do
        let paramIdent := mkIdent n
        sigType ← `([$inhabitedClass $paramIdent] → $sigType)

    let instCmd ← `(command|
      instance : $sigType where
        default := $defaultExpr
    )
    elabCommand instCmd

private def mkSerializeHandlerSingle (declName : Name) : CommandElabM Bool := do
  let env ← getEnv

  let some info := env.find? declName | return false
  let .inductInfo view := info | return false

  let isStruct := view.ctors.length == 1 && (view.ctors[0]!).getString! == "mk"

  let argName := Name.mkSimple "__serialArg"

  let isRec ← liftTermElabM <| isRecursiveType view
  let recFnBaseName := declName ++ `__serializeRec

  let (serializeBody, typeParamNames) ← liftTermElabM do
    let recFnMap := if isRec then [(view.name, mkRawIdent recFnBaseName)] else []
    let body ← if isStruct then
      let fields ← getStructureFields declName
      mkStructSerializeBody declName fields argName
    else
      mkEnumSerializeBody view argName recFnMap
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

  if isRec then
    let recFnIdent := mkRawIdent recFnBaseName
    let mIdent := mkRawIdent `m
    let encoderClass := mkCIdent ``Encoder
    let monadClass := mkCIdent ``Monad

    let mut recFnType : TSyntax `term ← `($appliedType → $mIdent Unit)
    recFnType ← `({$mIdent : Type → Type} → [$monadClass $mIdent] → [$encoderClass $mIdent] → $recFnType)
    for n in typeParamNames.reverse do
      let paramIdent := mkIdent n
      recFnType ← `([$serializeClass $paramIdent] → $recFnType)

    let bodyWithLetI ← `(letI : $serializeClass $appliedType := ⟨$recFnIdent⟩; $serializeBody)

    let cmd ← `(command|
      partial def $recFnIdent : $recFnType := fun $argIdent => $bodyWithLetI
    )
    elabCommand cmd

    let instCmd ← `(command|
      instance : $sigType where
        serialize := $recFnIdent
    )
    elabCommand instCmd
  else
    let cmd ← `(command|
      instance : $sigType where
        serialize := fun $argIdent => $serializeBody
    )
    elabCommand cmd

  return true

private def mkSerializeHandlerMutual (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv

  let firstRecFnName := declNames[0]! ++ `__serializeRec
  if env.find? firstRecFnName |>.isSome then
    return true

  let mut views : Array InductiveVal := #[]
  for declName in declNames do
    let some info := env.find? declName | return false
    let .inductInfo view := info | return false
    views := views.push view

  let typeParamNames ← liftTermElabM <| getTypeParams views[0]!

  let serializeClass := mkCIdent ``Serialize
  let encoderClass := mkCIdent ``Encoder
  let monadClass := mkCIdent ``Monad

  let recFnMap : List (Name × Ident) := declNames.toList.map fun n => (n, mkRawIdent (n ++ `__serializeRec))

  let mut mutualDefs : Array (TSyntax `command) := #[]

  for (declName, view) in declNames.zip views do
    let argName := Name.mkSimple "__serialArg"
    let argIdent := mkRawIdent argName
    let recFnIdent := mkRawIdent (declName ++ `__serializeRec)
    let typeIdent := mkCIdent declName

    let appliedType : TSyntax `term ←
      if typeParamNames.isEmpty then
        pure ⟨typeIdent⟩
      else
        let paramIdents : TSyntaxArray `term := ⟨typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term)) |>.toList⟩
        `($typeIdent $paramIdents*)

    let mIdent := mkRawIdent `m

    let mut recFnType : TSyntax `term ← `($appliedType → $mIdent Unit)
    recFnType ← `({$mIdent : Type → Type} → [$monadClass $mIdent] → [$encoderClass $mIdent] → $recFnType)
    for n in typeParamNames.reverse do
      let paramIdent := mkIdent n
      recFnType ← `([$serializeClass $paramIdent] → $recFnType)

    let serializeBody ← liftTermElabM do
      mkEnumSerializeBody view argName recFnMap

    let mut bodyWithLetI : TSyntax `term := serializeBody
    for (n, fnIdent) in recFnMap.reverse do
      let tIdent := mkCIdent n
      let appliedT : TSyntax `term ←
        if typeParamNames.isEmpty then
          pure ⟨tIdent⟩
        else
          let paramIdents : TSyntaxArray `term := ⟨typeParamNames.map (fun nm => (⟨mkRawIdent nm⟩ : TSyntax `term)) |>.toList⟩
          `($tIdent $paramIdents*)
      bodyWithLetI ← `(letI : $serializeClass $appliedT := ⟨$fnIdent⟩; $bodyWithLetI)

    let defCmd ← `(command|
      partial def $recFnIdent : $recFnType := fun $argIdent => $bodyWithLetI
    )
    mutualDefs := mutualDefs.push defCmd

  let mutualCmd ← `(command| mutual $mutualDefs* end)
  elabCommand mutualCmd

  for declName in declNames do
    let recFnIdent := mkRawIdent (declName ++ `__serializeRec)
    let typeIdent := mkCIdent declName

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

    let instCmd ← `(command|
      instance : $sigType where
        serialize := $recFnIdent
    )
    elabCommand instCmd

  return true

def mkSerializeHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size == 0 then
    return false
  else if declNames.size == 1 then
    let declName := declNames[0]!
    let env ← getEnv
    let some info := env.find? declName | return false
    let .inductInfo view := info | return false
    if view.all.length > 1 then
      mkSerializeHandlerMutual view.all.toArray
    else
      mkSerializeHandlerSingle declName
  else
    mkSerializeHandlerMutual declNames

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

private def mkEnumDeserializeBody (view : InductiveVal) (_argName : Name) (recFnMap : List (Name × Ident) := []) : MetaM (TSyntax `term) := do
  let matchVariantFn := mkCIdent ``Decoder.matchVariant
  let deserializeFn := mkCIdent ``Deserialize.deserialize
  let failFn := mkCIdent ``Decoder.fail
  let numCtors := Syntax.mkNumLit (toString view.ctors.length)

  let findRecFn (paramType : Expr) : Option Ident :=
    recFnMap.find? (fun (n, _) => paramType.isAppOf n) |>.map (·.2)

  let mut indexAlts : Array (TSyntax `term × TSyntax `term) := #[]
  for (idx, ctorName) in view.ctors.toArray.mapIdx (·, ·) do
    let ctorInfo ← getConstInfoCtor ctorName
    let ctorIdent := mkCIdent ctorName
    let idxLit : TSyntax `term := ⟨Syntax.mkNumLit (toString idx)⟩

    let (numFields, fieldTypes) ← forallTelescopeReducing ctorInfo.type fun params _ => do
      let fieldParams := params[view.numParams:]
      let mut types : Array Expr := #[]
      for param in fieldParams do
        types := types.push (← inferType param)
      return (fieldParams.size, types)

    let body ← if numFields == 0 then
      `(pure $ctorIdent)
    else if numFields == 1 then
      match findRecFn fieldTypes[0]! with
      | some recFnIdent => `($ctorIdent <$> $recFnIdent)
      | none => `($ctorIdent <$> $deserializeFn)
    else
      let getFieldFn := mkCIdent ``Decoder.getField
      let mut fieldIdents : Array Ident := #[]
      for i in [:numFields] do
        fieldIdents := fieldIdents.push (mkRawIdent (Name.mkSimple s!"__f{i}"))
      let fieldArgs : TSyntaxArray `term := ⟨fieldIdents.map (⟨·⟩ : Ident → TSyntax `term) |>.toList⟩

      let mut innerResult ← `(pure ($ctorIdent $fieldArgs*))
      for i in [:numFields] do
        let ridx := numFields - 1 - i
        let fieldIdent := fieldIdents[ridx]!
        let deser ← match findRecFn fieldTypes[ridx]! with
          | some recFnIdent => pure (recFnIdent : TSyntax `term)
          | none => `($deserializeFn)
        let keyStr := Syntax.mkStrLit s!"_{ridx}"
        innerResult ← `($getFieldFn $keyStr $deser >>= fun $fieldIdent => $innerResult)

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

private def mkDeserializeHandlerSingle (declName : Name) : CommandElabM Bool := do
  let env ← getEnv

  let some info := env.find? declName | return false
  let .inductInfo view := info | return false

  let isStruct := view.ctors.length == 1 && (view.ctors[0]!).getString! == "mk"
  let argName := Name.mkSimple "__deserialArg"

  let isRec ← liftTermElabM <| isRecursiveType view
  let recFnImplName := declName ++ `__deserializeRecImpl

  let (deserializeBody, typeParamNames) ← liftTermElabM do
    let recFnMap := if isRec then [(view.name, mkRawIdent recFnImplName)] else []
    let body ← if isStruct then
      let fields ← getStructureFieldNames declName
      mkStructDeserializeBody declName fields argName
    else
      mkEnumDeserializeBody view argName recFnMap
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

  let needsInhabitedConstraints ← liftTermElabM do
    if !isRec then return false
    let some (_, numNonRecFields, _) ← findBaseConstructor view | return true
    return numNonRecFields > 0

  let inhabitedClass := mkCIdent ``Inhabited

  let mut sigType : TSyntax `term ← `($deserializeClass $appliedType)
  for n in typeParamNames.reverse do
    let paramIdent := mkIdent n
    if needsInhabitedConstraints then
      sigType ← `([$inhabitedClass $paramIdent] → [$deserializeClass $paramIdent] → $sigType)
    else
      sigType ← `([$deserializeClass $paramIdent] → $sigType)

  if isRec then
    mkInhabitedInstance view typeParamNames

    let recFnIdent := mkRawIdent recFnImplName
    let mIdent := mkRawIdent `m
    let decoderClass := mkCIdent ``Decoder
    let monadClass := mkCIdent ``Monad

    let mut recFnType : TSyntax `term ← `($mIdent $appliedType)
    recFnType ← `({$mIdent : Type → Type} → [$monadClass $mIdent] → [$decoderClass $mIdent] → $recFnType)
    for n in typeParamNames.reverse do
      let paramIdent := mkIdent n
      if needsInhabitedConstraints then
        recFnType ← `([$inhabitedClass $paramIdent] → [$deserializeClass $paramIdent] → $recFnType)
      else
        recFnType ← `([$deserializeClass $paramIdent] → $recFnType)

    let bodyWithLetI ← `(letI : $deserializeClass $appliedType := ⟨$recFnIdent⟩; $deserializeBody)

    let cmd ← `(command|
      partial def $recFnIdent : $recFnType := $bodyWithLetI
    )
    elabCommand cmd

    let instCmd ← `(command|
      instance : $sigType where
        deserialize := $recFnIdent
    )
    elabCommand instCmd
  else
    let cmd ← `(command|
      instance : $sigType where
        deserialize := $deserializeBody
    )
    elabCommand cmd

  return true

private def mkDeserializeHandlerMutual (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv

  let firstRecFnName := declNames[0]! ++ `__deserializeRecImpl
  if env.find? firstRecFnName |>.isSome then
    return true

  let mut views : Array InductiveVal := #[]
  for declName in declNames do
    let some info := env.find? declName | return false
    let .inductInfo view := info | return false
    views := views.push view

  let typeParamNames ← liftTermElabM <| getTypeParams views[0]!

  let deserializeClass := mkCIdent ``Deserialize
  let decoderClass := mkCIdent ``Decoder
  let monadClass := mkCIdent ``Monad
  let inhabitedClass := mkCIdent ``Inhabited

  let recFnMap : List (Name × Ident) := declNames.toList.map fun n => (n, mkRawIdent (n ++ `__deserializeRecImpl))

  mkMutualInhabitedInstances views typeParamNames

  let anyNeedsInhabitedConstraints : Bool ← liftTermElabM do
    for view in views do
      let some (_, numNonRecFields, _) ← findBaseConstructor view | return true
      if numNonRecFields > 0 then return true
    return false

  let mut mutualDefs : Array (TSyntax `command) := #[]

  for (declName, view) in declNames.zip views do
    let recFnIdent := mkRawIdent (declName ++ `__deserializeRecImpl)
    let typeIdent := mkCIdent declName

    let appliedType : TSyntax `term ←
      if typeParamNames.isEmpty then
        pure ⟨typeIdent⟩
      else
        let paramIdents : TSyntaxArray `term := ⟨typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term)) |>.toList⟩
        `($typeIdent $paramIdents*)

    let mIdent := mkRawIdent `m

    let mut recFnType : TSyntax `term ← `($mIdent $appliedType)
    recFnType ← `({$mIdent : Type → Type} → [$monadClass $mIdent] → [$decoderClass $mIdent] → $recFnType)
    for n in typeParamNames.reverse do
      let paramIdent := mkIdent n
      if anyNeedsInhabitedConstraints then
        recFnType ← `([$inhabitedClass $paramIdent] → [$deserializeClass $paramIdent] → $recFnType)
      else
        recFnType ← `([$deserializeClass $paramIdent] → $recFnType)

    let argName := Name.mkSimple "__deserialArg"
    let deserializeBody ← liftTermElabM do
      mkEnumDeserializeBody view argName recFnMap

    let mut bodyWithLetI : TSyntax `term := deserializeBody
    for (n, fnIdent) in recFnMap.reverse do
      let tIdent := mkCIdent n
      let appliedT : TSyntax `term ←
        if typeParamNames.isEmpty then
          pure ⟨tIdent⟩
        else
          let paramIdents : TSyntaxArray `term := ⟨typeParamNames.map (fun nm => (⟨mkRawIdent nm⟩ : TSyntax `term)) |>.toList⟩
          `($tIdent $paramIdents*)
      bodyWithLetI ← `(letI : $deserializeClass $appliedT := ⟨$fnIdent⟩; $bodyWithLetI)

    let defCmd ← `(command|
      partial def $recFnIdent : $recFnType := $bodyWithLetI
    )
    mutualDefs := mutualDefs.push defCmd

  let mutualCmd ← `(command| mutual $mutualDefs* end)
  elabCommand mutualCmd

  for (declName, _view) in declNames.zip views do
    let recFnIdent := mkRawIdent (declName ++ `__deserializeRecImpl)
    let typeIdent := mkCIdent declName

    let appliedType : TSyntax `term ←
      if typeParamNames.isEmpty then
        pure ⟨typeIdent⟩
      else
        let paramIdents : TSyntaxArray `term := ⟨typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term)) |>.toList⟩
        `($typeIdent $paramIdents*)

    let mut sigType : TSyntax `term ← `($deserializeClass $appliedType)
    for n in typeParamNames.reverse do
      let paramIdent := mkIdent n
      if anyNeedsInhabitedConstraints then
        sigType ← `([$inhabitedClass $paramIdent] → [$deserializeClass $paramIdent] → $sigType)
      else
        sigType ← `([$deserializeClass $paramIdent] → $sigType)

    let instCmd ← `(command|
      instance : $sigType where
        deserialize := $recFnIdent
    )
    elabCommand instCmd

  return true

def mkDeserializeHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size == 0 then
    return false
  else if declNames.size == 1 then
    let declName := declNames[0]!
    let env ← getEnv
    let some info := env.find? declName | return false
    let .inductInfo view := info | return false
    if view.all.length > 1 then
      mkDeserializeHandlerMutual view.all.toArray
    else
      mkDeserializeHandlerSingle declName
  else
    mkDeserializeHandlerMutual declNames

initialize registerDerivingHandler ``Deserialize mkDeserializeHandler

end Kenosis
