import RHConsequences
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let expected := #[
    `CarryForward.Targets.isStrongProbablePrime_of_prime,
    `CarryForward.Targets.fermat_of_isStrongProbablePrime,
    `CarryForward.Targets.isUnit_of_isStrongProbablePrime,
    `CarryForward.Targets.exists_proper_subgroup_of_composite,
    `CarryForward.Targets.miller_of_liar_subgroups,
    `CarryForward.Targets.millerTestIsCorrect_of_smallNonresidue,
    `CarryForward.Targets.primeCountingError_of_psi_bound,
    `CarryForward.Targets.psi_error_on_interval,
    `CarryForward.Targets.psi_bound_of_large_bound,
    `CarryForward.Targets.weightedZeroCounting_unitWindow_le,
    `CarryForward.Targets.weightedZeroCounting_unitWindow_isBigO,
    `CarryForward.Targets.abs_psi_sub_self_le_seven_eighths_of_five_thousand_le,
    `CarryForward.Targets.psi_bound_of_riemannHypothesis,
    `CarryForward.Targets.primeCountingError_of_riemannHypothesis,
    `CarryForward.Targets.norm_adjacent_cpow_averages_sub_le,
    `CarryForward.Targets.primeInShortInterval_of_riemannHypothesis,
    `CarryForward.Targets.miller_iff_of_character_witness,
    `CarryForward.Targets.dirichletLZerosOnLine_iff_primitive,
    `CarryForward.Targets.LFunction_ne_zero_right_of_half,
    `CarryForward.Targets.characterPerron_eq_sum,
    `CarryForward.Targets.norm_character_logDeriv_two_le,
    `CarryForward.Targets.psi1_lower_of_sixteen_le,
    `CarryForward.Targets.ankenyBound_of_primitivePerronBound,
    `CarryForward.Targets.miller_of_ankenyBound,
    `CarryForward.Targets.mem_characterZeros,
    `CarryForward.Targets.exists_character_contour_height,
    `CarryForward.Targets.tendsto_truncated_characterPerron,
    `CarryForward.Targets.character_rectangle_eq_sum_residues,
    `CarryForward.Targets.characterPerron_truncated_eq,
    `CarryForward.Targets.norm_character_residue_sum_le,
    `CarryForward.Targets.primitivePerronBound_of_contourBounds,
    `CarryForward.Targets.ankenyBound_of_dirichletGRH_of_contourBounds,
    `CarryForward.Targets.miller_of_dirichletGRH_of_contourBounds]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  for name in expected do
    unless (env.find? name).any (fun c => c matches .thmInfo _) do
      throwError "missing theorem {name}"
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "unexpected axioms for {name}: {axioms}"
    logInfo m!"{name}: {axioms}"

#print axioms CarryForward.Targets.isStrongProbablePrime_of_prime
#print axioms CarryForward.Targets.fermat_of_isStrongProbablePrime
#print axioms CarryForward.Targets.isUnit_of_isStrongProbablePrime
#print axioms CarryForward.Targets.exists_proper_subgroup_of_composite
#print axioms CarryForward.Targets.miller_of_liar_subgroups
#print axioms CarryForward.Targets.millerTestIsCorrect_of_smallNonresidue
#print axioms CarryForward.Targets.primeCountingError_of_psi_bound

-- Check the exported theorem declarations of the six original modules as well.
open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for modName in #[`Cryptids.Semantics.Riemann.Schmidt, `Cryptids.Semantics.Riemann.DigammaBinet,
      `Cryptids.Semantics.Riemann.ExplicitLarge, `Cryptids.Semantics.Riemann.VonMangoldtCount,
      `Cryptids.Semantics.Riemann.HorizontalBounds, `Cryptids.Semantics.Riemann.WeightedStieltjes] do
    let some idx := env.getModuleIdx? modName | throwError "missing module {modName}"
    let mut checked : Nat := 0
    for decl in env.header.moduleData[idx]!.constNames do
      if !decl.isInternalDetail && !isPrivateName decl then
        if (env.find? decl).any (fun c => c matches .thmInfo _) then
          let axioms ← collectAxioms decl
          unless axioms.all allowed.contains do
            throwError "unexpected axioms for {decl}: {axioms}"
          checked := checked + 1
    if checked == 0 then throwError "no exported theorems checked in {modName}"
    logInfo m!"{modName}: checked {checked} exported theorem declarations"

#print axioms CarryForward.Targets.psi_error_on_interval
#print axioms CarryForward.Targets.psi_bound_of_large_bound
#print axioms CarryForward.Targets.weightedZeroCounting_unitWindow_le
#print axioms CarryForward.Targets.weightedZeroCounting_unitWindow_isBigO
#print axioms CarryForward.Targets.abs_psi_sub_self_le_seven_eighths_of_five_thousand_le
#print axioms CarryForward.Targets.psi_bound_of_riemannHypothesis
#print axioms CarryForward.Targets.primeCountingError_of_riemannHypothesis
