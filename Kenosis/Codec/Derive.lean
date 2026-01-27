import Lean
import Kenosis.Codec

namespace Kenosis

open Lean Elab Command Term Meta Syntax

private def mkRawIdent (n : Name) : Ident :=
  ⟨Syntax.ident SourceInfo.none n.toString.toRawSubstring n []⟩

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
    let fieldParams := params[view.numParams + view.numIndices:]

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

private def mkIfElseChain (cases : Array (TSyntax `term × TSyntax `term)) (defaultCase : TSyntax `term) : MetaM (TSyntax `term) := do
  if cases.isEmpty then
    return defaultCase
  else
    let mut result := defaultCase
    for i in [:cases.size] do
      let idx := cases.size - 1 - i
      let (cond, body) := cases[idx]!
      result ← `(if $cond then $body else $result)
    return result

private partial def mkIndexBinarySearch
    (idxIdent : Ident)
    (bodies : Array (TSyntax `term))
    (lo hi : Nat)
    (defaultCase : TSyntax `term) : MetaM (TSyntax `term) := do
  if lo > hi then
    return defaultCase
  else if lo == hi then
    return bodies[lo]!
  else if lo + 1 == hi then
    let loLit : TSyntax `term := ⟨Syntax.mkNumLit (toString lo)⟩
    let loCond ← `($idxIdent == $loLit)
    `(if $loCond then $(bodies[lo]!) else $(bodies[hi]!))
  else
    let mid := (lo + hi) / 2
    let midLit : TSyntax `term := ⟨Syntax.mkNumLit (toString mid)⟩
    let leftBranch ← mkIndexBinarySearch idxIdent bodies lo (mid - 1) defaultCase
    let midBody := bodies[mid]!
    let rightBranch ← mkIndexBinarySearch idxIdent bodies (mid + 1) hi defaultCase
    let midCond ← `($idxIdent == $midLit)
    let ltCond ← `($idxIdent < $midLit)
    `(if $ltCond then $leftBranch else if $midCond then $midBody else $rightBranch)

private partial def mkNameToIndexBinarySearch
    (nameIdent : Ident)
    (indexFnIdent : Ident)
    (nameToIdx : Array (String × Nat))
    (lo hi : Nat)
    (defaultCase : TSyntax `term) : MetaM (TSyntax `term) := do
  if lo > hi then
    return defaultCase
  else if lo == hi then
    let (name, idx) := nameToIdx[lo]!
    let nameStr : TSyntax `term := ⟨Syntax.mkStrLit name⟩
    let idxLit : TSyntax `term := ⟨Syntax.mkNumLit (toString idx)⟩
    let cond ← `($nameIdent == $nameStr)
    `(if $cond then $indexFnIdent $idxLit else $defaultCase)
  else if lo + 1 == hi then
    let (loName, loIdx) := nameToIdx[lo]!
    let (hiName, hiIdx) := nameToIdx[hi]!
    let loNameStr : TSyntax `term := ⟨Syntax.mkStrLit loName⟩
    let hiNameStr : TSyntax `term := ⟨Syntax.mkStrLit hiName⟩
    let loIdxLit : TSyntax `term := ⟨Syntax.mkNumLit (toString loIdx)⟩
    let hiIdxLit : TSyntax `term := ⟨Syntax.mkNumLit (toString hiIdx)⟩
    let loCond ← `($nameIdent == $loNameStr)
    let hiCond ← `($nameIdent == $hiNameStr)
    `(if $loCond then $indexFnIdent $loIdxLit else if $hiCond then $indexFnIdent $hiIdxLit else $defaultCase)
  else
    let mid := (lo + hi) / 2
    let (midName, midIdx) := nameToIdx[mid]!
    let midNameStr : TSyntax `term := ⟨Syntax.mkStrLit midName⟩
    let midIdxLit : TSyntax `term := ⟨Syntax.mkNumLit (toString midIdx)⟩
    let leftBranch ← mkNameToIndexBinarySearch nameIdent indexFnIdent nameToIdx lo (mid - 1) defaultCase
    let rightBranch ← mkNameToIndexBinarySearch nameIdent indexFnIdent nameToIdx (mid + 1) hi defaultCase
    let midCond ← `($nameIdent == $midNameStr)
    let ltCond ← `($nameIdent < $midNameStr)
    `(if $ltCond then $leftBranch else if $midCond then $indexFnIdent $midIdxLit else $rightBranch)

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

private def getTypeParams (view : InductiveVal) : MetaM (Array Name × Array (Name × TSyntax `term)) := do
  let ctorName := view.ctors[0]!
  let ctorInfo ← getConstInfoCtor ctorName
  forallTelescopeReducing ctorInfo.type fun params _ => do
    let allParams := params[:view.numParams]
    let mut typeParams : Array Name := #[]
    let mut nonTypeParams : Array (Name × TSyntax `term) := #[]
    for param in allParams do
      let name ← param.fvarId!.getUserName
      let type ← inferType param
      if type.isSort then
        typeParams := typeParams.push name
      else
        let typeStx : TSyntax `term ←
          if let .const typeName _ := type then
            pure ⟨mkCIdent typeName⟩
          else
            let s ← PrettyPrinter.delab type
            pure ⟨s⟩
        nonTypeParams := nonTypeParams.push (name, typeStx)
    return (typeParams, nonTypeParams)

private def getTypeIndices (view : InductiveVal) : MetaM (Array (Name × TSyntax `term)) := do
  if view.numIndices == 0 then return #[]
  let ctorName := view.ctors[0]!
  let ctorInfo ← getConstInfoCtor ctorName
  forallTelescopeReducing ctorInfo.type fun params _ => do
    let indexParams := params[view.numParams : view.numParams + view.numIndices]
    let mut result : Array (Name × TSyntax `term) := #[]
    for param in indexParams do
      let name ← param.fvarId!.getUserName
      let type ← inferType param
      let typeStx : TSyntax `term ←
        if let .const typeName _ := type then
          pure ⟨mkCIdent typeName⟩
        else if let .app fn _ := type then
          let s ← PrettyPrinter.delab type
          pure ⟨s⟩
        else
          let s ← PrettyPrinter.delab type
          pure ⟨s⟩
      result := result.push (name, typeStx)
    return result

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
      let fieldParams := params[view.numParams + view.numIndices:]
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
    let fieldParams := params[view.numParams + view.numIndices:]
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

private def mkInhabitedInstance (view : InductiveVal) (typeParamNames : Array Name) (typeIndexInfo : Array (Name × TSyntax `term) := #[]) : CommandElabM Unit := do
  let some (ctorName, numNonRecFields, _) := (← liftTermElabM <| findBaseConstructor view) | return
  let typeIdent := mkCIdent view.name
  let ctorIdent := mkCIdent ctorName
  let inhabitedClass := mkCIdent ``Inhabited

  let allArgsInhab := typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term))
              ++ typeIndexInfo.map (fun (n, _) => (⟨mkRawIdent n⟩ : TSyntax `term))
  let appliedType : TSyntax `term ←
    if allArgsInhab.isEmpty then
      pure ⟨typeIdent⟩
    else
      let argIdents : TSyntaxArray `term := ⟨allArgsInhab.toList⟩
      `($typeIdent $argIdents*)

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
  for (idxName, idxTypeStx) in typeIndexInfo.reverse do
    let idxIdent := mkRawIdent idxName
    sigType ← `({$idxIdent : $idxTypeStx} → $sigType)

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

private def mkMutualInhabitedInstances (views : Array InductiveVal) (typeParamNames : Array Name) (typeIndexInfo : Array (Name × TSyntax `term) := #[]) : CommandElabM Unit := do
  let inhabitedClass := mkCIdent ``Inhabited

  let mut instanceInfos : Array (Name × Name × Nat × Nat) := #[]
  for view in views do
    let some (ctorName, numNonRecFields, numRecFields) := (← liftTermElabM <| findBestConstructorForInhabited view) | continue
    instanceInfos := instanceInfos.push (view.name, ctorName, numNonRecFields, numRecFields)

  if instanceInfos.isEmpty then return

  let anyNeedsInhabitedConstraints := instanceInfos.any fun (_, _, nonRec, _) => nonRec > 0

  let sortedInfos := instanceInfos.qsort fun (_, _, _, rec1) (_, _, _, rec2) => rec1 < rec2

  for (typeName, ctorName, numNonRecFields, numRecFields) in sortedInfos do
    let typeIdent := mkCIdent typeName
    let ctorIdent := mkCIdent ctorName

    let allArgsMut := typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term))
                ++ typeIndexInfo.map (fun (n, _) => (⟨mkRawIdent n⟩ : TSyntax `term))
    let appliedType : TSyntax `term ←
      if allArgsMut.isEmpty then
        pure ⟨typeIdent⟩
      else
        let argIdents : TSyntaxArray `term := ⟨allArgsMut.toList⟩
        `($typeIdent $argIdents*)

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
    for (idxName, idxTypeStx) in typeIndexInfo.reverse do
      let idxIdent := mkRawIdent idxName
      sigType ← `({$idxIdent : $idxTypeStx} → $sigType)

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
  let fnImplName := declName ++ `__serializeImpl
  let currNs ← getCurrNamespace
  let fnRelativeName := fnImplName.replacePrefix currNs Name.anonymous

  let (serializeBody, typeParamNames, nonTypeParams, typeIndexInfo) ← liftTermElabM do
    let recFnMap := if isRec then [(view.name, mkRawIdent fnRelativeName)] else []
    let body ← if isStruct then
      let fields ← getStructureFields declName
      mkStructSerializeBody declName fields argName
    else
      mkEnumSerializeBody view argName recFnMap
    let (typeParams, nonTypeParams) ← getTypeParams view
    let typeIndices ← getTypeIndices view
    return (body, typeParams, nonTypeParams, typeIndices)

  let implicitParams := nonTypeParams ++ typeIndexInfo

  let typeIdent := mkCIdent declName
  let serializeClass := mkCIdent ``Serialize
  let argIdent := mkRawIdent argName

  let allArgsSer := typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term))
              ++ implicitParams.map (fun (n, _) => (⟨mkRawIdent n⟩ : TSyntax `term))
  let appliedType : TSyntax `term ←
    if allArgsSer.isEmpty then
      pure ⟨typeIdent⟩
    else
      let argIdents : TSyntaxArray `term := ⟨allArgsSer.toList⟩
      `($typeIdent $argIdents*)

  let mut sigType : TSyntax `term ← `($serializeClass $appliedType)
  for n in typeParamNames.reverse do
    let paramIdent := mkIdent n
    sigType ← `([$serializeClass $paramIdent] → $sigType)
  for (paramName, paramTypeStx) in implicitParams.reverse do
    let paramIdent := mkRawIdent paramName
    sigType ← `({$paramIdent : $paramTypeStx} → $sigType)

  let fnDefIdent := mkRawIdent fnRelativeName
  let fnRefIdent := mkCIdent fnImplName
  let mIdent := mkRawIdent `m
  let encoderClass := mkCIdent ``Encoder
  let monadClass := mkCIdent ``Monad

  let mut fnType : TSyntax `term ← `($appliedType → $mIdent Unit)
  fnType ← `({$mIdent : Type → Type} → [$monadClass $mIdent] → [$encoderClass $mIdent] → $fnType)
  for n in typeParamNames.reverse do
    let paramIdent := mkIdent n
    fnType ← `([$serializeClass $paramIdent] → $fnType)
  for (paramName, paramTypeStx) in implicitParams.reverse do
    let paramIdent := mkRawIdent paramName
    fnType ← `({$paramIdent : $paramTypeStx} → $fnType)

  if isRec then
    let bodyWithLetI ← `(letI : $serializeClass $appliedType := ⟨$fnDefIdent⟩; $serializeBody)
    if implicitParams.isEmpty then
      let cmd ← `(command| partial def $fnDefIdent : $fnType := fun $argIdent => $bodyWithLetI)
      elabCommand cmd
    else
      let mut wrappedBody : TSyntax `term ← `(fun $argIdent => $bodyWithLetI)
      for (paramName, _) in implicitParams.reverse do
        let paramIdent := mkRawIdent paramName
        wrappedBody ← `(fun {$paramIdent} => $wrappedBody)
      let cmd ← `(command| partial def $fnDefIdent : $fnType := $wrappedBody)
      elabCommand cmd
  else
    if implicitParams.isEmpty then
      let cmd ← `(command| partial def $fnDefIdent : $fnType := fun $argIdent => $serializeBody)
      elabCommand cmd
    else
      let mut wrappedBody : TSyntax `term ← `(fun $argIdent => $serializeBody)
      for (paramName, _) in implicitParams.reverse do
        let paramIdent := mkRawIdent paramName
        wrappedBody ← `(fun {$paramIdent} => $wrappedBody)
      let cmd ← `(command| partial def $fnDefIdent : $fnType := $wrappedBody)
      elabCommand cmd

  let instCmd ← `(command|
    instance : $sigType where
      serialize := $fnRefIdent
  )
  elabCommand instCmd

  return true

private def mkSerializeHandlerMutual (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv

  let firstRecFnName := declNames[0]! ++ `__serializeImpl
  if env.find? firstRecFnName |>.isSome then
    return true

  let mut views : Array InductiveVal := #[]
  for declName in declNames do
    let some info := env.find? declName | return false
    let .inductInfo view := info | return false
    views := views.push view

  let (typeParamNames, nonTypeParams) ← liftTermElabM <| getTypeParams views[0]!
  let typeIndexInfo ← liftTermElabM <| getTypeIndices views[0]!
  let implicitParams := nonTypeParams ++ typeIndexInfo

  let serializeClass := mkCIdent ``Serialize
  let encoderClass := mkCIdent ``Encoder
  let monadClass := mkCIdent ``Monad

  let currNs ← getCurrNamespace
  let recFnMap : List (Name × Ident) := declNames.toList.map fun n =>
    let fullName := n ++ `__serializeImpl
    let relativeName := fullName.replacePrefix currNs Name.anonymous
    (n, mkRawIdent relativeName)

  let mut mutualDefs : Array (TSyntax `command) := #[]

  for (declName, view) in declNames.zip views do
    let argName := Name.mkSimple "__serialArg"
    let argIdent := mkRawIdent argName
    let fullFnName := declName ++ `__serializeImpl
    let relativeFnName := fullFnName.replacePrefix currNs Name.anonymous
    let recFnIdent := mkRawIdent relativeFnName
    let typeIdent := mkCIdent declName

    let allArgsLoop := typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term))
                ++ implicitParams.map (fun (n, _) => (⟨mkRawIdent n⟩ : TSyntax `term))
    let appliedType : TSyntax `term ←
      if allArgsLoop.isEmpty then
        pure ⟨typeIdent⟩
      else
        let argIdents : TSyntaxArray `term := ⟨allArgsLoop.toList⟩
        `($typeIdent $argIdents*)

    let mIdent := mkRawIdent `m

    let mut recFnType : TSyntax `term ← `($appliedType → $mIdent Unit)
    recFnType ← `({$mIdent : Type → Type} → [$monadClass $mIdent] → [$encoderClass $mIdent] → $recFnType)
    for n in typeParamNames.reverse do
      let paramIdent := mkIdent n
      recFnType ← `([$serializeClass $paramIdent] → $recFnType)
    for (paramName, paramTypeStx) in implicitParams.reverse do
      let paramIdent := mkRawIdent paramName
      recFnType ← `({$paramIdent : $paramTypeStx} → $recFnType)

    let serializeBody ← liftTermElabM do
      mkEnumSerializeBody view argName recFnMap

    let mut bodyWithLetI : TSyntax `term := serializeBody
    for (n, fnIdent) in recFnMap.reverse do
      let tIdent := mkCIdent n
      let allArgsT := typeParamNames.map (fun nm => (⟨mkRawIdent nm⟩ : TSyntax `term))
                  ++ implicitParams.map (fun (nm, _) => (⟨mkRawIdent nm⟩ : TSyntax `term))
      let appliedT : TSyntax `term ←
        if allArgsT.isEmpty then
          pure ⟨tIdent⟩
        else
          let argIdents : TSyntaxArray `term := ⟨allArgsT.toList⟩
          `($tIdent $argIdents*)
      bodyWithLetI ← `(letI : $serializeClass $appliedT := ⟨$fnIdent⟩; $bodyWithLetI)

    let defCmd ← `(command| partial def $recFnIdent : $recFnType := fun $argIdent => $bodyWithLetI)
    mutualDefs := mutualDefs.push defCmd

  let mutualCmd ← `(command| mutual $mutualDefs* end)
  elabCommand mutualCmd

  for declName in declNames do
    let recFnIdent := mkCIdent (declName ++ `__serializeImpl)
    let typeIdent := mkCIdent declName

    let allArgsInst := typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term))
                ++ implicitParams.map (fun (n, _) => (⟨mkRawIdent n⟩ : TSyntax `term))
    let appliedType : TSyntax `term ←
      if allArgsInst.isEmpty then
        pure ⟨typeIdent⟩
      else
        let argIdents : TSyntaxArray `term := ⟨allArgsInst.toList⟩
        `($typeIdent $argIdents*)

    let mut sigType : TSyntax `term ← `($serializeClass $appliedType)
    for n in typeParamNames.reverse do
      let paramIdent := mkIdent n
      sigType ← `([$serializeClass $paramIdent] → $sigType)
    for (paramName, paramTypeStx) in implicitParams.reverse do
      let paramIdent := mkRawIdent paramName
      sigType ← `({$paramIdent : $paramTypeStx} → $sigType)

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
    let firstFieldStr := Syntax.mkStrLit (toString fields[0]!)
    let mut result ← `($ctorIdent <$> $getFieldFn $firstFieldStr $deserializeFn)

    for i in [1:fields.size] do
      let fieldNameStr := Syntax.mkStrLit (toString fields[i]!)
      let fieldExpr ← `($getFieldFn $fieldNameStr $deserializeFn)
      result ← `($result <*> $fieldExpr)

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
      let fieldParams := params[view.numParams + view.numIndices:]
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

      let mut result ← `(pure ($ctorIdent $fieldArgs*))
      for i in [:numFields] do
        let ridx := numFields - 1 - i
        let fieldIdent := fieldIdents[ridx]!
        let deser ← match findRecFn fieldTypes[ridx]! with
          | some recFnIdent => pure (recFnIdent : TSyntax `term)
          | none => `($deserializeFn)
        let keyStr := Syntax.mkStrLit s!"_{ridx}"
        let callExpr ← `($getFieldFn $keyStr $deser)
        result ← `(do let $fieldIdent ← ($callExpr); ($result))

      pure result

    indexAlts := indexAlts.push (idxLit, body)

  let mut nameToIdx : Array (String × Nat) := #[]
  for (idx, ctorName) in view.ctors.toArray.mapIdx (·, ·) do
    let shortName := ctorName.getString!
    nameToIdx := nameToIdx.push (shortName, idx)

  let idxIdent := mkRawIdent `__idx
  let nameIdent := mkRawIdent `__name
  let indexFnIdent := mkRawIdent `__indexFn

  let indexBodies := indexAlts.map (·.2)
  let defaultIdx ← `($failFn s!"invalid variant index: {$idxIdent}")
  let indexMatch ← if indexBodies.isEmpty then
    pure defaultIdx
  else
    mkIndexBinarySearch idxIdent indexBodies 0 (indexBodies.size - 1) defaultIdx

  let defaultName ← `($failFn s!"unknown variant: {$nameIdent}")

  let sortedNameToIdx := nameToIdx.qsort (fun a b => a.1 < b.1)
  let nameMatch ← if sortedNameToIdx.isEmpty then
    pure defaultName
  else
    mkNameToIndexBinarySearch nameIdent indexFnIdent sortedNameToIdx 0 (sortedNameToIdx.size - 1) defaultName

  `(let $indexFnIdent := fun $idxIdent => $indexMatch; $matchVariantFn $numCtors $indexFnIdent (fun $nameIdent => $nameMatch))

private def mkDeserializeHandlerSingle (declName : Name) : CommandElabM Bool := do
  let env ← getEnv

  let some info := env.find? declName | return false
  let .inductInfo view := info | return false

  let isStruct := view.ctors.length == 1 && (view.ctors[0]!).getString! == "mk"
  let argName := Name.mkSimple "__deserialArg"

  let isRec ← liftTermElabM <| isRecursiveType view
  let fnImplName := declName ++ `__deserializeImpl
  let currNs ← getCurrNamespace
  let fnRelativeName := fnImplName.replacePrefix currNs Name.anonymous

  let (deserializeBody, typeParamNames, nonTypeParams, typeIndexInfo) ← liftTermElabM do
    let recFnMap := if isRec then [(view.name, mkRawIdent fnRelativeName)] else []
    let body ← if isStruct then
      let fields ← getStructureFieldNames declName
      mkStructDeserializeBody declName fields argName
    else
      mkEnumDeserializeBody view argName recFnMap
    let (typeParams, nonTypeParams) ← getTypeParams view
    let typeIndices ← getTypeIndices view
    return (body, typeParams, nonTypeParams, typeIndices)

  let implicitParams := nonTypeParams ++ typeIndexInfo

  let typeIdent := mkCIdent declName
  let deserializeClass := mkCIdent ``Deserialize
  let _ := mkRawIdent argName

  let allArgsDeser := typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term))
              ++ implicitParams.map (fun (n, _) => (⟨mkRawIdent n⟩ : TSyntax `term))
  let appliedType : TSyntax `term ←
    if allArgsDeser.isEmpty then
      pure ⟨typeIdent⟩
    else
      let argIdents : TSyntaxArray `term := ⟨allArgsDeser.toList⟩
      `($typeIdent $argIdents*)

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
  for (paramName, paramTypeStx) in implicitParams.reverse do
    let paramIdent := mkRawIdent paramName
    sigType ← `({$paramIdent : $paramTypeStx} → $sigType)

  let fnDefIdent := mkRawIdent fnRelativeName
  let fnRefIdent := mkCIdent fnImplName
  let mIdent := mkRawIdent `m
  let decoderClass := mkCIdent ``Decoder
  let monadClass := mkCIdent ``Monad

  let mut fnType : TSyntax `term ← `($mIdent $appliedType)
  fnType ← `({$mIdent : Type → Type} → [$monadClass $mIdent] → [$decoderClass $mIdent] → $fnType)
  for n in typeParamNames.reverse do
    let paramIdent := mkIdent n
    if needsInhabitedConstraints then
      fnType ← `([$inhabitedClass $paramIdent] → [$deserializeClass $paramIdent] → $fnType)
    else
      fnType ← `([$deserializeClass $paramIdent] → $fnType)
  for (paramName, paramTypeStx) in implicitParams.reverse do
    let paramIdent := mkRawIdent paramName
    fnType ← `({$paramIdent : $paramTypeStx} → $fnType)

  if isRec then
    mkInhabitedInstance view typeParamNames implicitParams
    let bodyWithLetI ← `(letI : $deserializeClass $appliedType := ⟨$fnDefIdent⟩; $deserializeBody)
    if implicitParams.isEmpty then
      let cmd ← `(command| partial def $fnDefIdent : $fnType := $bodyWithLetI)
      elabCommand cmd
    else
      let mut wrappedBody : TSyntax `term := bodyWithLetI
      for (paramName, _) in implicitParams.reverse do
        let paramIdent := mkRawIdent paramName
        wrappedBody ← `(fun {$paramIdent} => $wrappedBody)
      let cmd ← `(command| partial def $fnDefIdent : $fnType := $wrappedBody)
      elabCommand cmd
  else
    if implicitParams.isEmpty then
      let cmd ← `(command| partial def $fnDefIdent : $fnType := $deserializeBody)
      elabCommand cmd
    else
      let mut wrappedBody : TSyntax `term := deserializeBody
      for (paramName, _) in implicitParams.reverse do
        let paramIdent := mkRawIdent paramName
        wrappedBody ← `(fun {$paramIdent} => $wrappedBody)
      let cmd ← `(command| partial def $fnDefIdent : $fnType := $wrappedBody)
      elabCommand cmd

  let instCmd ← `(command|
    instance : $sigType where
      deserialize := $fnRefIdent
  )
  elabCommand instCmd

  return true

private def mkDeserializeHandlerMutual (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv

  let firstRecFnName := declNames[0]! ++ `__deserializeImpl
  if env.find? firstRecFnName |>.isSome then
    return true

  let mut views : Array InductiveVal := #[]
  for declName in declNames do
    let some info := env.find? declName | return false
    let .inductInfo view := info | return false
    views := views.push view

  let (typeParamNames, nonTypeParams) ← liftTermElabM <| getTypeParams views[0]!
  let typeIndexInfo ← liftTermElabM <| getTypeIndices views[0]!
  let implicitParams := nonTypeParams ++ typeIndexInfo

  let deserializeClass := mkCIdent ``Deserialize
  let decoderClass := mkCIdent ``Decoder
  let monadClass := mkCIdent ``Monad
  let inhabitedClass := mkCIdent ``Inhabited

  let currNs ← getCurrNamespace
  let recFnMap : List (Name × Ident) := declNames.toList.map fun n =>
    let fullName := n ++ `__deserializeImpl
    let relativeName := fullName.replacePrefix currNs Name.anonymous
    (n, mkRawIdent relativeName)

  mkMutualInhabitedInstances views typeParamNames implicitParams

  let anyNeedsInhabitedConstraints : Bool ← liftTermElabM do
    for view in views do
      let some (_, numNonRecFields, _) ← findBaseConstructor view | return true
      if numNonRecFields > 0 then return true
    return false

  let mut mutualDefs : Array (TSyntax `command) := #[]

  for (declName, view) in declNames.zip views do
    let fullFnName := declName ++ `__deserializeImpl
    let relativeFnName := fullFnName.replacePrefix currNs Name.anonymous
    let recFnIdent := mkRawIdent relativeFnName
    let typeIdent := mkCIdent declName

    let allArgsLoop := typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term))
                ++ implicitParams.map (fun (n, _) => (⟨mkRawIdent n⟩ : TSyntax `term))
    let appliedType : TSyntax `term ←
      if allArgsLoop.isEmpty then
        pure ⟨typeIdent⟩
      else
        let argIdents : TSyntaxArray `term := ⟨allArgsLoop.toList⟩
        `($typeIdent $argIdents*)

    let mIdent := mkRawIdent `m

    let mut recFnType : TSyntax `term ← `($mIdent $appliedType)
    recFnType ← `({$mIdent : Type → Type} → [$monadClass $mIdent] → [$decoderClass $mIdent] → $recFnType)
    for n in typeParamNames.reverse do
      let paramIdent := mkIdent n
      if anyNeedsInhabitedConstraints then
        recFnType ← `([$inhabitedClass $paramIdent] → [$deserializeClass $paramIdent] → $recFnType)
      else
        recFnType ← `([$deserializeClass $paramIdent] → $recFnType)
    for (paramName, paramTypeStx) in implicitParams.reverse do
      let paramIdent := mkRawIdent paramName
      recFnType ← `({$paramIdent : $paramTypeStx} → $recFnType)

    let argName := Name.mkSimple "__deserialArg"
    let deserializeBody ← liftTermElabM do
      mkEnumDeserializeBody view argName recFnMap

    let mut bodyWithLetI : TSyntax `term := deserializeBody
    for (n, fnIdent) in recFnMap.reverse do
      let tIdent := mkCIdent n
      let allArgsT := typeParamNames.map (fun nm => (⟨mkRawIdent nm⟩ : TSyntax `term))
                  ++ implicitParams.map (fun (nm, _) => (⟨mkRawIdent nm⟩ : TSyntax `term))
      let appliedT : TSyntax `term ←
        if allArgsT.isEmpty then
          pure ⟨tIdent⟩
        else
          let argIdents : TSyntaxArray `term := ⟨allArgsT.toList⟩
          `($tIdent $argIdents*)
      bodyWithLetI ← `(letI : $deserializeClass $appliedT := ⟨$fnIdent⟩; $bodyWithLetI)

    let defCmd ← `(command| partial def $recFnIdent : $recFnType := $bodyWithLetI)
    mutualDefs := mutualDefs.push defCmd

  let mutualCmd ← `(command| mutual $mutualDefs* end)
  elabCommand mutualCmd

  for (declName, _view) in declNames.zip views do
    let recFnIdent := mkCIdent (declName ++ `__deserializeImpl)
    let typeIdent := mkCIdent declName

    let allArgsInst := typeParamNames.map (fun n => (⟨mkRawIdent n⟩ : TSyntax `term))
                ++ implicitParams.map (fun (n, _) => (⟨mkRawIdent n⟩ : TSyntax `term))
    let appliedType : TSyntax `term ←
      if allArgsInst.isEmpty then
        pure ⟨typeIdent⟩
      else
        let argIdents : TSyntaxArray `term := ⟨allArgsInst.toList⟩
        `($typeIdent $argIdents*)

    let mut sigType : TSyntax `term ← `($deserializeClass $appliedType)
    for n in typeParamNames.reverse do
      let paramIdent := mkIdent n
      if anyNeedsInhabitedConstraints then
        sigType ← `([$inhabitedClass $paramIdent] → [$deserializeClass $paramIdent] → $sigType)
      else
        sigType ← `([$deserializeClass $paramIdent] → $sigType)
    for (paramName, paramTypeStx) in implicitParams.reverse do
      let paramIdent := mkRawIdent paramName
      sigType ← `({$paramIdent : $paramTypeStx} → $sigType)

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
