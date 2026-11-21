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
    `CarryForward.Targets.primeCountingError_of_psi_bound]
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
