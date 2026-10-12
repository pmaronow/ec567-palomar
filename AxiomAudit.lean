module

import all RankCertificates
import all Solution
import all RankCertificates.ConditionalPrimePatterns
import all RankCertificates.AdmissibleWResidue
import all RankCertificates.AdditiveVanDerCorput
import all RankCertificates.Admissibility
import all RankCertificates.AmbientDescent
import all RankCertificates.Binary
import all RankCertificates.Common
import all RankCertificates.ConditionalAssembly
import all RankCertificates.ConditionalFamilies
import all RankCertificates.DescentWitnesses
import all RankCertificates.DualComposition
import all RankCertificates.DualIsogenyHom
import all RankCertificates.DyadicDominance
import all RankCertificates.DyadicNorm
import all RankCertificates.DyadicNormPoint
import all RankCertificates.DyadicNormResidues
import all RankCertificates.ExtractionAsymptotics
import all RankCertificates.ExtractionBounds
import all RankCertificates.FiniteExclusions
import all RankCertificates.FiniteKatai
import all RankCertificates.FixedCharacterEvaluation
import all RankCertificates.Geometric
import all RankCertificates.GroupIndex
import all RankCertificates.InfinitudeReduction
import all RankCertificates.Integration
import all RankCertificates.Isogeny
import all RankCertificates.IsogenyComposition
import all RankCertificates.IsogenyHom
import all RankCertificates.IsogenyKernel
import all RankCertificates.IsogenyPointComposition
import all RankCertificates.IsogenyRange
import all RankCertificates.KataiAsymptotic
import all RankCertificates.Kummer
import all RankCertificates.KummerScaling
import all RankCertificates.LiteralAffineSystems
import all RankCertificates.LiteralCyclicBridge
import all RankCertificates.LiteralFiniteField
import all RankCertificates.LiteralPrimeBridge
import all RankCertificates.LocalCharacterRows
import all RankCertificates.LocalDescent
import all RankCertificates.LocalSeven
import all RankCertificates.LocalValuations
import all RankCertificates.MatrixCertificates
import all RankCertificates.MordellWeil
import all RankCertificates.MovingPrimeCharacters
import all RankCertificates.Normalization
import all RankCertificates.PartnerNormReduction
import all RankCertificates.PrimeAsymptoticBridge
import all RankCertificates.PrimeCoefficientSupport
import all RankCertificates.PrimeComplexity
import all RankCertificates.PrimeDirections
import all RankCertificates.PrimeDivisorMoments
import all RankCertificates.PrimeExtraction
import all RankCertificates.PrimeFamilyAssembly
import all RankCertificates.PrimePatterns
import all RankCertificates.PrimePowerCharacters
import all RankCertificates.PrimePowerPoints
import all RankCertificates.PrimePowerResidues
import all RankCertificates.PrimeSpecializations
import all RankCertificates.PrimeSquareParity
import all RankCertificates.PrimitiveDirections
import all RankCertificates.Rank5
import all RankCertificates.Rank5CharacterEvaluation
import all RankCertificates.Rank5CharacterRows
import all RankCertificates.Rank5ConstantCharacters
import all RankCertificates.Rank5DyadicRows
import all RankCertificates.Rank5ExactRank
import all RankCertificates.Rank5FiveDescent
import all RankCertificates.Rank5FixedCharacters
import all RankCertificates.Rank5FixedRows
import all RankCertificates.Rank5LiteralRows
import all RankCertificates.Rank5MovingRows
import all RankCertificates.Rank5OddRows
import all RankCertificates.Rank5OriginalTwoDescent
import all RankCertificates.Rank5PartnerTwoDescent
import all RankCertificates.Rank5PrimeValuations
import all RankCertificates.Rank5ThreeDescent
import all RankCertificates.Rank5TwoDescent
import all RankCertificates.Rank6
import all RankCertificates.Rank6CharacterEvaluation
import all RankCertificates.Rank6CharacterRows
import all RankCertificates.Rank6ConstantCharacters
import all RankCertificates.Rank6Descent
import all RankCertificates.Rank6ExactRank
import all RankCertificates.Rank6FixedRows
import all RankCertificates.Rank6LiteralRows
import all RankCertificates.Rank6PrimeValuations
import all RankCertificates.Rank6TwoDescent
import all RankCertificates.Rank7
import all RankCertificates.Rank7CharacterEvaluation
import all RankCertificates.Rank7ExactRank
import all RankCertificates.Rank7FixedOddDescent
import all RankCertificates.Rank7FixedRows
import all RankCertificates.Rank7PrimeValuations
import all RankCertificates.Rank7ThreeDescent
import all RankCertificates.Rank7TwoDescent
import all RankCertificates.RankLowerBounds
import all RankCertificates.RealDescent
import all RankCertificates.SingularSeries
import all RankCertificates.Specification
import all RankCertificates.SplitReductionDescent
import all RankCertificates.SquareClassClassification
import all RankCertificates.SquareClassImageFinite
import all RankCertificates.SquareClassIndependence
import all RankCertificates.SquareClassSign
import all RankCertificates.TwoIsogenyRank

import Lean.Util.CollectAxioms
import Lean.AddDecl

open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/- Direct `import all` of each owning module loads private declarations under
Lean's modern module system. Audit the complete loaded ModuleData rather than
only names in an exported namespace. A safe kernel-checked aggregate retains
every root and shares axiom traversal work. The local fallback audits the
separate negative fixture, which is never imported by the proof library. -/
run_cmd do
  let env ← getEnv
  let owners := env.header.moduleNames
  let mut roots : Array ConstantInfo := #[]
  let mut counts : Array (Name × Nat) := #[]
  for idx in [:owners.size] do
    let owner := owners[idx]!
    let text := owner.toString
    if text == "RankCertificates" || text.startsWith "RankCertificates." || text == "Solution" then
      let infos := env.header.moduleData[idx]!.constants
      counts := counts.push (owner, infos.size)
      for info in infos do
        unless (env.checked.get.find? info.name).isSome do
          throwError "Owned private kernel declaration unavailable: {info.name}"
        roots := roots.push info
  for (name, info) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      let text := name.toString
      if text.startsWith "RankCertificates." || text.startsWith "_private.RankCertificates." then
        roots := roots.push info
  unless roots.size > 0 do
    throwError "No project declaration was audited"
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  let safeRoots := roots.filter fun info => !info.isUnsafe && !info.isPartial
  let implementationRoots := roots.filter fun info => info.isUnsafe || info.isPartial
  -- Generated compiler implementation declarations cannot occur in a safe
  -- proof term. Audit their axiom metadata individually rather than putting
  -- them into the safe kernel aggregate; no owned declaration is skipped.
  for info in implementationRoots do
    let axioms ← Lean.collectAxioms info.name
    for usedAxiom in axioms do
      unless allowed.contains usedAxiom do
        throwError "Forbidden axiom {usedAxiom} in {info.name}"
  let mut value := mkConst ``True.intro
  for info in safeRoots do
    let levels := info.levelParams.map (fun _ => Level.zero)
    let rootType := info.type.instantiateLevelParams info.levelParams levels
    value := Expr.letE info.name rootType (mkConst info.name levels) value false
  let aggregateName := `RankCertificatesExhaustiveAuditRoot
  liftCoreM <| addDecl (.defnDecl {
    name := aggregateName
    levelParams := []
    type := mkConst ``True
    value := value
    hints := .abbrev
    safety := .safe
  })
  let checkedEnv ← getEnv
  let some checkedInfo := checkedEnv.checked.get.find? aggregateName
    | throwError "Checked aggregate declaration unavailable"
  let retained := checkedInfo.value!.getUsedConstants
  for info in safeRoots do
    unless retained.contains info.name do
      throwError "Aggregate lost owned dependency root {info.name}"
  let axioms ← Lean.collectAxioms aggregateName
  for usedAxiom in axioms do
    unless allowed.contains usedAxiom do
      throwError "Forbidden axiom {usedAxiom} in exhaustive project dependency roots"
  logInfo m!"Axiom audit passed for {roots.size} project declarations, including private/generated kernel declarations. Allowed: propext, Quot.sound, Classical.choice."
  logInfo m!"Owning-module counts: {counts}"
  logInfo m!"Safe aggregate roots: {safeRoots.size}; separately audited generated implementation roots: {implementationRoots.map (·.name)}"
