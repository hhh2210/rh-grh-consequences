# Consequences of RH and a small-character-witness bound

This Lean project proves two reductions for the [target statements of Qui Vincit and Fable](https://github.com/vincitamore/riemann-lean-account/blob/1c01f271f523dc7d47aca7455fa41d60bdc3849b/lean/Targets.lean), and proves the von Koch prime-counting error bound assuming Mathlib's `RiemannHypothesis`. The target definitions are byte-identical to that revision. All theorems below are in `CarryForward.Targets`.

| Lean theorem | Result |
| --- | --- |
| [`millerTestIsCorrect_of_smallNonresidue`](MillerFromSmallNonresidue.lean) | If every nonprincipal Dirichlet character modulo $n$ takes a value $\chi(a)\ne1$ for some $0<a<2(\log n)^2$, Miller testing to that bound decides primality for odd $n>2$. |
| [`primeCountingError_of_psi_bound`](PrimeCountingFromPsi.lean) | A bound $\lvert\psi(x)-x\rvert\le C\sqrt{x}\log^2 x$ implies $\lvert\pi(\lfloor x\rfloor)-\int_2^x dt/\log t\rvert\le C'\sqrt{x}\log x$ for every real $x\ge2$. |
| [`psi_bound_of_riemannHypothesis`](PsiFromRH.lean) | RH implies the required ψ bound for all real $x\ge2$. |
| [`primeCountingError_of_riemannHypothesis`](PsiFromRH.lean) | RH implies the stated prime-counting error bound. |
| [`weightedZeroCounting_unitWindow_le`](PsiZeroCountingWindow.lean) | Under RH, $N(T+1)-N(T)\le(512/41)\log(T+4)$ for $T\ge8$. Here $N$ counts nontrivial zeros of both signs up to absolute imaginary part $T$, with analytic multiplicity. The file also proves the $O(\log T)$ statement. |

## Proofs

**Miller.** Every passing base is a unit satisfying the Fermat congruence. When the Fermat kernel is proper it contains every passing base. Otherwise an odd composite modulus is a Carmichael number and hence squarefree. Split it into coprime factors greater than two. At the last repeated-squaring stage where minus one is attainable, every passing base has a uniform sign. CRT produces a unit with opposite signs on the two factors. Character duality then gives a nonprincipal character trivial on all passing bases. If the test bound reaches the modulus, the least prime divisor is an admissible failing base. This reduction and the ψ-to-π reduction use Mathlib alone. [Subgroup construction](MillerSubgroup.lean) · [Character argument](MillerCharacter.lean)

**The analytic input.** Google DeepMind's Cryptids formalization proves, under RH, $\lvert\psi(x)-x\rvert\le(7/8)\sqrt{x}\log^2x$ for real $x\ge5000$. Its proof combines a smoothed Perron contour shift, a multiplicity-weighted zero count, bounds for the logarithmic derivative on the left and horizontal edges, and an explicit real inequality. Five of the six upstream modules compile byte-for-byte at the pinned revision. Full `Schmidt.lean` needs a type annotation in an open-set proof on Lean 4.36. The [compatibility patch](compat/Schmidt-4.36.patch) preserves its statements. Our short adapter makes the final assembly from Cryptids’ `Analytic.lean` available independently of its register-machine application. [Published assembly, lines 590–617](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/Cryptids/Semantics/Riemann/Analytic.lean#L590-L617) · [Local assembly](PsiFromRH.lean) · [Analytic proof map](ANALYTIC.md)

**The remaining range and prime counting.** Chebyshev’s elementary upper bound supplies a uniform constant for $2\le x\le5000$. For π, Mathlib’s $O(\sqrt{x})$ bound on $\psi-\theta$ transfers the assumed error to θ. Subtracting integration by parts for the logarithmic integral from Abel summation for π leaves an integral bounded by a constant times $\int_2^x t^{-1/2}\,dt$. Both estimates include $x=2$. The separate unit-window theorem applies the Jensen estimate to the positive and negative height windows, preserving multiplicities. [Bounded intervals](PsiCompact.lean) · [Abel summation](PrimeCountingFromPsi.lean) · [Unit windows](PsiZeroCountingWindow.lean)

## Reproduce

Use Python 3.9+, Git, and Lean via elan. From the repository root:

```sh
python3 verify.py --receipt verification.txt
```

The verifier initializes the pinned Cryptids submodule, checks dependency revisions, fetches the Mathlib cache, and compiles into a fresh temporary directory. It materializes the six sources under `.lake/cryptids-src` and checks the patched Schmidt digest. For ordinary Lake commands, run `python3 verify.py --prepare-sources` once before `lake build`. The verifier runs `leanchecker -v` separately on every module against its imports. The Lean audit rejects any axiom outside `propext`, `Classical.choice` and `Quot.sound` for the project's public results and the exported theorems in the six Cryptids modules. The transcript records the source SHA-256 values, compiler outputs, named replays and exit codes. Pass `--prepared-mathlib PATH` to use an existing build at the exact pin. [Audit](Audit.lean) · [Verification transcript](verification.txt)

Lean 4.36.0 (`611c117b`), Mathlib [`fc4f59e5`](https://github.com/leanprover-community/mathlib4/commit/fc4f59e577feb1a4956671bc04ac18aaaf8cd842), Cryptids [`3647718b`](https://github.com/google-deepmind/cryptids/commit/3647718b5df22e1a61462dec0376bd204526285a). Cryptids originally pinned Lean 4.35.0-rc4. The six source modules are checked here on 4.36.0. See [LICENSE](LICENSE) for the MIT-licensed target definitions and project code; the upstream proof sources and identified adaptation in `PsiFromRH.lean` are Apache-2.0 licensed.
