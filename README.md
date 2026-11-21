# Two conditional consequences in analytic number theory

This Lean project proves two implications for the statements in [Qui Vincit and Fable’s account of the RH formalization](https://github.com/vincitamore/riemann-lean-account/blob/1c01f271f523dc7d47aca7455fa41d60bdc3849b/lean/Targets.lean). Both proofs use Mathlib alone. The definitions in `Targets.lean` are byte-identical to the linked revision.

| Assumption | Conclusion | Lean theorem in `CarryForward.Targets` |
| --- | --- | --- |
| Every nonprincipal complex Dirichlet character modulo $n$ has a positive witness $a<2(\log n)^2$ with $\chi(a)\ne1$. | An odd $n>2$ is prime exactly when it passes the strong probable-prime test for every base $2\le a<n$ with $a\le2(\log n)^2$. | [`millerTestIsCorrect_of_smallNonresidue`](MillerFromSmallNonresidue.lean) |
| For some $C$ and every real $x\ge2$, $\lvert\psi(x)-x\rvert\le C\sqrt{x}\log^2 x$. | For some $C'$ and every $x\ge2$, $\lvert\pi(\lfloor x\rfloor)-\int_2^x dt/\log t\rvert\le C'\sqrt x\log x$. | [`primeCountingError_of_psi_bound`](PrimeCountingFromPsi.lean) |

## Proofs

**Miller testing.** Every passing base is a unit satisfying the Fermat congruence. If the Fermat kernel is proper, it contains all passing bases. Otherwise an odd composite modulus is a Carmichael number and hence squarefree. Split it into coprime factors greater than two. At the last repeated-squaring stage where a unit can attain minus one, every passing base has a uniform sign. The Chinese remainder theorem produces a unit with opposite signs on the two factors. The passing bases therefore lie in a proper subgroup. Character duality gives a nonprincipal character trivial there, to which the small-witness hypothesis applies. If the bound reaches the modulus, the least prime divisor supplies a failing base directly. [Subgroup construction](MillerSubgroup.lean) · [Character argument](MillerCharacter.lean)

**Prime counting.** Mathlib bounds the difference between the two Chebyshev functions by a constant times $\sqrt x$. This transfers the hypothesis from $\psi$ to $\theta$. Subtract the integration-by-parts formula for the logarithmic integral from the Abel summation formula for $\pi$. The integral of the remaining error is bounded by a constant times $\int_2^x t^{-1/2}\,dt$. The proof includes the endpoint $x=2$. [Lean proof](PrimeCountingFromPsi.lean)

## Reproduce

Install Lean via elan, then run from the repository root with Python 3.9+ and Git:

```sh
python3 verify.py --receipt verification.txt
```

The script checks the pinned revisions, retrieves the Mathlib cache, compiles into a fresh temporary directory, and runs `leanchecker -v` on each module against its imports. The audit checks the seven public proof declarations and allows only `propext`, `Classical.choice`, and `Quot.sound`. To reuse a built Mathlib checkout, pass `--prepared-mathlib PATH` with the pinned Lean on your PATH. [Axiom audit](Audit.lean) · [Windows verification transcript](verification.txt)

Lean 4.36.0 (`611c117b`), Mathlib [`fc4f59e5`](https://github.com/leanprover-community/mathlib4/commit/fc4f59e577feb1a4956671bc04ac18aaaf8cd842). MIT licensed. The notice for the original target definitions is included in [LICENSE](LICENSE).
