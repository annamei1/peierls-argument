# Peierls — a formal proof of the Peierls argument in Lean 4

A complete, **sorry-free** Lean 4 + Mathlib formalization of the Peierls
argument for the two-dimensional Ising model, following the companion
document `Peierls_Argument.tex` of this repository (a full write-up of
§3.7.2 of Friedli–Velenik, *Statistical Mechanics of Lattice Systems*,
Chapter 3).

## Main result

```lean
theorem Peierls.peierls_argument (n : ℕ) {β : ℝ} (hβ : 2 ≤ β) :
    1 / 2 ≤ gibbsSigma0 n β
```

Here `gibbsSigma0 n β` is the literal finite-volume Gibbs expectation
`⟨σ₀⟩⁺_{B(n);β,0}` of the spin at the origin: configurations are the subsets
`S ⊆ B(n) = {-n,…,n}²` of minus-spins (the `+` boundary condition), and the
weight is `exp(−H)` with the Hamiltonian
`H = −β ∑ σᵢσⱼ` summed over all nearest-neighbour edges of `ℤ²` meeting
`B(n)` (Definition 3.3 of the transcription, at zero magnetic field).

So: for every inverse temperature `β ≥ 2`, the magnetization at the origin is
at least `½` **uniformly in the volume** — the content of the Peierls
argument (Lemmas 3.37–3.38 of the transcription; Theorem `thm:main` of
`Peierls_Argument.tex`, here with `β₀ = 2`). By spin-flip symmetry this is
the spontaneous-magnetization/phase-coexistence statement at low temperature.

## Verification

```sh
lake build                       # zero errors, zero sorries
echo 'import Peierls
#print axioms Peierls.peierls_argument' | lake env lean --stdin
-- 'Peierls.peierls_argument' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only Lean's three standard foundational axioms are used; there is no `sorry`,
no extra `axiom`, and no `native_decide` anywhere in the development.

## Design: a topology-free Peierls argument

The classical exposition uses planar topology (Jordan curves, deformation
rules). This development replaces all of it with finite combinatorics:

* **Spins** live in `ZMod 2` (`0` ↔ `+1`, `1` ↔ `−1`); a configuration is the
  `Finset` of minus-sites, so the Gibbs layer is finite powerset sums.
* **Interiors via crossing parity.** For a finite dual-edge set `γ`,
  `In γ i : ZMod 2` is the parity of the number of edges of `γ` whose dual
  crosses the rightward horizontal ray out of the site `i`. The Jordan-type
  lemmas of the prose proof become `ZMod 2` incidence identities:
  `In γ (a,b) + In γ (a+1,b) = [H a b ∈ γ]` (trivial filter splitting) and,
  for *even* `γ`, `In γ (a,b) + In γ (a,b+1) = [V a b ∈ γ]` (a handshake
  double-count over a half-line of dual vertices).
* **The σ-formula.** `spin S i = In (Dis n S) i`: the spin is the crossing
  parity of the disagreement set — proved by a one-row induction. In
  particular `σ₀ = −1` forces the origin to be "inside" the disagreement set.
* **Contours as closed walks.** Cycles are closed edge-distinct walks encoded
  by direction words, extracted from even edge sets by a greedy
  non-backtracking walk plus pigeonhole, and re-rooted (rotation/reversal) to
  an anchored normal form starting on the positive half-axis. Counting is a
  trivial word count (`≤ ℓ·4^ℓ` cycles of length `ℓ` surrounding the origin)
  — no injectivity argument needed.
* **Energy–entropy.** Flipping the interior of an even `γ ⊆ Dis n S` removes
  exactly the disagreements on `γ` (`Dis (flip) = Dis ∆ γ`) and is an
  involution, giving the Peierls estimate `μ(γ ⊆ Dis) ≤ e^{−2β|γ|}`; the
  union bound and a geometric series give `μ(σ₀ = −1) ≤ ¼` for
  `x = e^{−2β} ≤ e^{−4}`.

## Definitions

All definitions of the development (lattice, dual lattice, configurations,
disagreement set, crossing-parity interior, contours/cycle walks, Gibbs
layer), with their mathematical meaning and a dictionary against the prose
proof, are collected in [`DEFINITIONS.md`](DEFINITIONS.md).

## File structure

| File | Contents |
|---|---|
| `Peierls/Defs.lean` | Lattice, dual edges, configurations, disagreement set, crossing parity `In`, walks, weights, the Gibbs measure |
| `Peierls/Parity.lean` | Incidence double-counting, `In_horiz`/`In_vert`, row parity, evenness of `Dis`, the σ-formula |
| `Peierls/Flip.lean` | Interior bounds, the erasure involution, `Dis_flip`, the Peierls estimate `evCyc_le`, `Z_pos` |
| `Peierls/Cycles.lean` | Walk infrastructure, rotation/reversal, greedy cycle extraction, parity selection, the anchored-cycle theorem |
| `Peierls/Bound.lean` | Coverage, union bound, `54 ≤ e⁴` numerics, geometric series, the Gibbs bridge, `peierls_argument` |

Toolchain: Lean `v4.30.0`, Mathlib `v4.30.0`.
