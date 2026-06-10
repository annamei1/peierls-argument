# Definitions used in the Lean proof of the Peierls argument

This file collects **every definition** of the formalization in
`lean/Peierls/`, with its Lean code, its mathematical meaning, and its
correspondence to the prose proof (`Peierls_Argument.tex`, which itself
follows §3.7.2 of Friedli–Velenik, Chapter 3). Statements of the main
*theorems* are listed at the end for orientation; everything the theorems
mean is determined by the definitions below, so this file is the part a
reader must check by hand.

Global conventions:

* All of `ℤ²` is in play; the box and its boundary condition enter through
  the definitions, not through the ambient space.
* Spins are written **additively** in `ZMod 2`: `0` means spin `+1`, `1`
  means spin `-1`. A configuration is identified with its set of minus-sites.
* "Dual" objects (vertices and edges of the dual lattice `ℤ² + (½,½)`) are
  indexed by integer pairs; `(p, q) : DualV` *denotes* the point
  `(p + ½, q + ½)`.

---

## 1. The lattice (`Defs.lean`)

### `Site`
```lean
abbrev Site : Type := ℤ × ℤ
```
A vertex of the lattice `ℤ²`.

### `Edge`
```lean
inductive Edge : Type
  | H : ℤ → ℤ → Edge
  | V : ℤ → ℤ → Edge
```
A nearest-neighbour edge of `ℤ²`:
* `H a b` is the horizontal edge `{(a,b), (a+1,b)}`;
* `V a b` is the vertical edge `{(a,b), (a,b+1)}`.

Every nearest-neighbour edge of `ℤ²` is of exactly one of these forms, so
this is a faithful encoding of the edge set `E_{ℤ²}` of the prose proof.

### `Edge.ends`
```lean
def ends : Edge → Site × Site
  | H a b => ((a, b), (a + 1, b))
  | V a b => ((a, b), (a, b + 1))
```
The two endpoint sites of a lattice edge.

### `siteBox`
```lean
def siteBox (n : ℕ) : Finset Site :=
  Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n
```
The box `B(n) = {-n, …, n}²` (the finite volume of the prose proof).

### `boxEdges`
```lean
def boxEdges (n : ℕ) : Finset Edge :=
  ((Finset.Icc (-(n : ℤ) - 1) n ×ˢ Finset.Icc (-(n : ℤ)) n).image fun p => Edge.H p.1 p.2) ∪
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ) - 1) n).image fun p => Edge.V p.1 p.2)
```
The set of all lattice edges with **at least one endpoint in `B(n)`** — the
edge set `𝓔_{B(n)}` over which the Hamiltonian with `+` boundary condition is
summed (Definition 3.3 of the transcription). The proved lemma
`mem_boxEdges_iff : e ∈ boxEdges n ↔ e.ends.1 ∈ siteBox n ∨ e.ends.2 ∈ siteBox n`
confirms the index ranges.

---

## 2. The dual lattice (`Defs.lean`)

### `DualV`
```lean
abbrev DualV : Type := ℤ × ℤ
```
A dual vertex: `(p, q)` denotes the point `(p + ½, q + ½)` of the dual
lattice `ℤ² + (½,½)` (the centre of the plaquette whose lower-left corner is
`(p, q)`).

### `Edge.dualEnds`
```lean
def dualEnds : Edge → DualV × DualV
  | H a b => ((a, b - 1), (a, b))
  | V a b => ((a - 1, b), (a, b))
```
The two endpoints of the **dual edge** of a lattice edge:
* the dual of `H a b` is the vertical unit segment crossing it,
  from `(a+½, b−½)` to `(a+½, b+½)`, i.e. dual vertices `(a, b-1)` and `(a, b)`;
* the dual of `V a b` is the horizontal segment from `(a−½, b+½)` to
  `(a+½, b+½)`, i.e. dual vertices `(a-1, b)` and `(a, b)`.

This realizes the bijection `e ↦ e*` of the prose proof; throughout the
formalization a set of lattice edges is silently identified with the set of
their dual edges.

---

## 3. Configurations and the disagreement set (`Defs.lean`)

### `cfgs`
```lean
def cfgs (n : ℕ) : Finset (Finset Site) := (siteBox n).powerset
```
The configuration space `Ω⁺_{B(n)}`: a configuration with `+` boundary
condition is identified with the set `S ⊆ B(n)` of sites carrying spin `-1`
(all spins outside `S`, in particular outside `B(n)`, are `+1`). This builds
the `+` boundary condition into the state space.

### `spin`
```lean
def spin (S : Finset Site) (i : Site) : ZMod 2 := if i ∈ S then 1 else 0
```
The spin at `i`, additively: `0` ↔ `σᵢ = +1`, `1` ↔ `σᵢ = -1`
(i.e. `σᵢ = (-1)^{spin S i}`).

### `disInd`
```lean
def disInd (S : Finset Site) (e : Edge) : ZMod 2 :=
  spin S e.ends.1 + spin S e.ends.2
```
The disagreement indicator of an edge: `1` iff the two endpoint spins differ
(`σᵢσⱼ = -1`), `0` iff they agree — addition in `ZMod 2` is exactly "spins
differ".

### `Dis`
```lean
def Dis (n : ℕ) (S : Finset Site) : Finset Edge :=
  (boxEdges n).filter fun e => disInd S e = 1
```
The **disagreement set** `𝓔*(S)` — the prose proof's set of dual edges
separating `+` from `-` spins. Filtering inside `boxEdges n` loses nothing:
a disagreement edge has an endpoint with spin `-1`, hence in `B(n)` (lemma
`mem_Dis_iff`). The contours of the prose proof are subsets of this set.

---

## 4. Evenness and the crossing-parity interior (`Defs.lean`)

### `deg`
```lean
def deg (γ : Finset Edge) (v : DualV) : ℕ :=
  (γ.filter fun e => v = e.dualEnds.1 ∨ v = e.dualEnds.2).card
```
The degree of the dual vertex `v` in (the duals of) the edge set `γ`.

### `IsEven`
```lean
def IsEven (γ : Finset Edge) : Prop := ∀ v : DualV, Even (deg γ v)
```
`γ` is an **even** edge set: every dual vertex has even degree. This is the
formal counterpart of "the disagreement set decomposes into closed contours";
the plaquette-parity lemma (`isEven_Dis`) shows every `Dis n S` is even, and
every cycle walk has an even edge set (`isEven_walkFinset`).

### `CrossesRight`
```lean
def CrossesRight (i : Site) (e : Edge) : Prop :=
  match e with
  | .H m b => b = i.2 ∧ i.1 ≤ m
  | .V _ _ => False
```
Does the dual of `e` cross the rightward horizontal ray out of the site `i`?
Only duals of horizontal edges (vertical dual segments `x = m+½`,
`y ∈ [b−½, b+½]`) cross the ray `{(x, i.2) : x ≥ i.1}`, and they do so iff
`b = i.2` and `m ≥ i.1`.

### `In`
```lean
def In (γ : Finset Edge) (i : Site) : ZMod 2 :=
  ((γ.filter (CrossesRight i)).card : ZMod 2)
```
The **crossing-parity interior function**: the parity of the number of edges
of `γ` whose dual crosses the rightward ray from `i`. The site `i` is
*inside* `γ` iff `In γ i = 1`.

This single definition replaces the entire topological apparatus of the
prose proof (Jordan curve theorem, winding, `Int(γ*)`): the discrete
Jordan lemma `lem:edge-boundary(a)` of `Peierls_Argument.tex` becomes the two
proved identities

* `In_horiz : In γ (a,b) + In γ (a+1,b) = [H a b ∈ γ]` (any `γ`),
* `In_vert : In γ (a,b) + In γ (a,b+1) = [V a b ∈ γ]` (`γ` even),

and the surrounding lemma `lem:surround` becomes the σ-formula
`spin_eq_In : spin S i = In (Dis n S) i`.

### `Intr`
```lean
def Intr (n : ℕ) (γ : Finset Edge) : Finset Site :=
  (siteBox n).filter fun i => In γ i = 1
```
The **interior of `γ`** as a finite set, `Int(γ*)` of the prose proof. For
even `γ ⊆ boxEdges n` this captures *all* sites with `In γ i = 1`
(lemma `mem_Intr_iff` — part (b) of the discrete Jordan lemma,
`Int(γ*) ⊆ B(n)`).

### `flip`
```lean
def flip (n : ℕ) (γ : Finset Edge) (S : Finset Site) : Finset Site :=
  symmDiff S (Intr n γ)
```
The **contour-erasure map** `T_{γ*}` of the prose proof: flip all spins in
the interior of `γ` (symmetric difference of the minus-set with the
interior). It is an involution (`flip_flip`) and satisfies
`Dis n (flip n γ S) = symmDiff (Dis n S) γ` (`Dis_flip`): erasing the contour
removes exactly its disagreements.

---

## 5. Walks and contours (`Defs.lean`, plus `Cycles.lean`)

### `Dir`
```lean
inductive Dir : Type | U | D | L | R
```
Step directions for walks in the dual lattice (up/down/left/right).

### `DualV.step`
```lean
def DualV.step : DualV → Dir → DualV
  | (p, q), .U => (p, q + 1)
  | (p, q), .D => (p, q - 1)
  | (p, q), .L => (p - 1, q)
  | (p, q), .R => (p + 1, q)
```
Move a dual vertex one unit step.

### `stepEdge`
```lean
def stepEdge : DualV → Dir → Edge
  | (p, q), .U => .H p (q + 1)
  | (p, q), .D => .H p q
  | (p, q), .L => .V p q
  | (p, q), .R => .V (p + 1) q
```
The (unique) lattice edge whose dual joins `v` and `v.step d` — the edge
traversed by that step.

### `walkEnd`, `walkEdges`, `walkFinset`
```lean
def walkEnd (v : DualV) : List Dir → DualV
  | [] => v
  | d :: w => walkEnd (v.step d) w

def walkEdges (v : DualV) : List Dir → List Edge
  | [] => []
  | d :: w => stepEdge v d :: walkEdges (v.step d) w

def walkFinset (v : DualV) (w : List Dir) : Finset Edge :=
  (walkEdges v w).toFinset
```
A walk in the dual lattice is a starting dual vertex plus a **direction
word** `w : List Dir`; `walkEnd` is its endpoint, `walkEdges` the list of
(duals of) edges it traverses, `walkFinset` its edge set.

### `IsCycleWalk`
```lean
def IsCycleWalk (v : DualV) (w : List Dir) : Prop :=
  walkEnd v w = v ∧ (walkEdges v w).Nodup ∧ w ≠ []
```
A **cycle walk**: a nonempty closed walk traversing pairwise distinct dual
edges. This is the formal counterpart of a *contour* (`γ*`) of the prose
proof. (Its edge set is even — `isEven_walkFinset`; its length is even and
`≥ 4` — `even_length_of_cycleWalk`, `four_le_length_of_cycleWalk`.)

The anchored normal form produced by `exists_anchored_cycle` is a cycle walk
starting at `((k : ℤ), -1)` with first direction `U`, so its first edge is
`H k 0` — the dual edge crossing the positive horizontal axis at `k + ½`,
exactly the anchor of Lemma `lem:cross` of the prose proof, with the bound
`2k + 2 ≤ ℓ`.

### `words`
```lean
def words : ℕ → Finset (List Dir)
  | 0 => {[]}
  | m + 1 => ((Finset.univ : Finset Dir) ×ˢ words m).image fun p => p.1 :: p.2
```
All direction words of length `m` (`card_words : (words m).card = 4 ^ m`).
Counting contours by counting words is what replaces Lemma 3.38 of the book.

### `dirRev`, `revWord` (`Cycles.lean`)
```lean
def dirRev : Dir → Dir
  | .U => .D | .D => .U | .L => .R | .R => .L

def revWord (w : List Dir) : List Dir := (w.map dirRev).reverse
```
Direction reversal and word reversal: traversing a walk backwards. Used
(with rotation, i.e. `w₁ ++ w₂ ↦ w₂ ++ w₁` at a closed walk's split point)
to re-root a contour at its anchor edge.

### `idx` (`Bound.lean`)
```lean
def idx (ℓ : ℕ) : Finset (ℕ × List Dir) :=
  (Finset.range ℓ ×ˢ words (ℓ - 1)).filter fun p =>
    IsCycleWalk ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2)
```
The index set of the union bound: anchored cycle walks of length `ℓ`,
encoded by the anchor position `k < ℓ` and the word after the initial `U`.
Its cardinality is at most `ℓ · 4^(ℓ-1)` — the entropy bound.

---

## 6. Counting helpers in the parity argument (`Parity.lean`)

### `endCount`
```lean
def endCount (R : DualV → Prop) [DecidablePred R] (e : Edge) : ℕ :=
  (if R e.dualEnds.1 then 1 else 0) + (if R e.dualEnds.2 then 1 else 0)
```
The number of dual endpoints of `e` lying in a region `R`. The handshake
identity `incidence_even` (for even `γ`, `∑ e ∈ γ, endCount R e` is even)
is the engine behind `In_vert` and `rowCount_even` — it is the formal
version of "sum the degrees of the dual vertices on a half-line".

### `InRow`
```lean
def InRow (b : ℤ) (e : Edge) : Prop :=
  match e with
  | .H _ c => c = b
  | .V _ _ => False
```
Is `e` a horizontal edge in the row at height `b`? Used for the row-parity
lemma (`rowCount_even`: an even edge set has evenly many horizontal edges in
each row), which supplies the *left* crossing in the anchoring argument.

---

## 7. The Gibbs measure layer (`Defs.lean`)

All sums are finite sums over the powerset `cfgs n`; no measure theory is
needed.

### `wt`
```lean
def wt (n : ℕ) (x : ℝ) (S : Finset Site) : ℝ := x ^ (Dis n S).card
```
The weight of a configuration, with `x` an abstract parameter standing for
`e^{-2β}`. (Justified by `exp_neg_ham_eq`: the Boltzmann factor `e^{-H(S)}`
equals the constant `e^{β·|boxEdges n|}` times `(e^{-2β})^{|Dis n S|}`.)

### `Z`
```lean
def Z (n : ℕ) (x : ℝ) : ℝ := ∑ S ∈ cfgs n, wt n x S
```
The partition function `Z⁺_{B(n);β,0}` (up to the same constant factor,
which cancels from all expectations).

### `evCyc`
```lean
def evCyc (n : ℕ) (x : ℝ) (γ : Finset Edge) : ℝ :=
  ∑ S ∈ (cfgs n).filter (fun S => γ ⊆ Dis n S), wt n x S
```
The total weight of the event `{γ ⊆ Dis n S}` — "all of `γ` consists of
disagreement edges", the formal version of the event `{Γ ∋ γ*}` of
Lemma 3.37. Peierls' estimate is `evCyc_le : evCyc n x γ ≤ x^{|γ|} · Z n x`
for even `γ`.

### `evMinus`
```lean
def evMinus (n : ℕ) (x : ℝ) : ℝ :=
  ∑ S ∈ (cfgs n).filter (fun S => ((0 : ℤ), (0 : ℤ)) ∈ S), wt n x S
```
The total weight of the event `{σ₀ = -1}`. The Peierls bound is
`evMinus_le_quarter : evMinus ≤ ¼ · Z` for `0 < x ≤ e^{-4}`.

### `sigma`
```lean
def sigma (S : Finset Site) (i : Site) : ℝ := if i ∈ S then -1 else 1
```
The real-valued spin `σᵢ ∈ {±1}` (used in the Hamiltonian and the
expectation; related to `spin` by `σᵢ = (-1)^{spin S i}`).

### `ham`
```lean
def ham (n : ℕ) (β : ℝ) (S : Finset Site) : ℝ :=
  -β * ∑ e ∈ boxEdges n, sigma S e.ends.1 * sigma S e.ends.2
```
The Hamiltonian `𝓗⁺_{B(n);β,0}(σ) = -β ∑_{{i,j} ∩ B(n) ≠ ∅} σᵢσⱼ` of the
Ising model in `B(n)` with `+` boundary condition at zero magnetic field —
Definition 3.3 of the transcription with `h = 0` (spins outside `B(n)` are
`+1` because `S ⊆ B(n)`).

### `gibbsSigma0`
```lean
def gibbsSigma0 (n : ℕ) (β : ℝ) : ℝ :=
  (∑ S ∈ cfgs n, sigma S ((0 : ℤ), (0 : ℤ)) * Real.exp (-ham n β S)) /
    (∑ S ∈ cfgs n, Real.exp (-ham n β S))
```
The finite-volume Gibbs expectation `⟨σ₀⟩⁺_{B(n);β,0}` of the spin at the
origin — the quantity the main theorem bounds.

---

## 8. The main theorems (statements only, for orientation)

```lean
-- Peierls' estimate (Lemma 3.37 of the transcription, eq. (3.34))
theorem evCyc_le (n : ℕ) {x : ℝ} (hx : 0 < x) {γ : Finset Edge}
    (he : IsEven γ) : evCyc n x γ ≤ x ^ γ.card * Z n x

-- the σ-formula (lem:surround of the prose proof, in parity form)
theorem spin_eq_In {n : ℕ} {S : Finset Site} (hS : S ⊆ siteBox n) (i : Site) :
    spin S i = In (Dis n S) i

-- contour extraction + anchoring (lem:contour-decomp, lem:surround, lem:cross)
theorem exists_anchored_cycle {γ : Finset Edge} (he : IsEven γ)
    (h1 : In γ ((0 : ℤ), (0 : ℤ)) = 1) :
    ∃ (k : ℕ) (w : List Dir),
      IsCycleWalk ((k : ℤ), (-1 : ℤ)) (Dir.U :: w) ∧
      walkFinset ((k : ℤ), (-1 : ℤ)) (Dir.U :: w) ⊆ γ ∧
      2 * k + 2 ≤ (Dir.U :: w).length

-- the uniform finite-volume Peierls bound (μ(σ₀ = -1) ≤ ¼)
theorem evMinus_le_quarter (n : ℕ) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ Real.exp (-4)) : evMinus n x ≤ 1 / 4 * Z n x

-- THE MAIN THEOREM (thm:main of Peierls_Argument.tex, with β₀ = 2)
theorem peierls_argument (n : ℕ) {β : ℝ} (hβ : 2 ≤ β) :
    1 / 2 ≤ gibbsSigma0 n β
```

Axiom audit: `peierls_argument` depends only on `propext`,
`Classical.choice`, `Quot.sound`.

---

## 9. Dictionary: prose proof ↔ Lean

| `Peierls_Argument.tex` / book | Lean |
|---|---|
| box `B(n)` | `siteBox n` |
| edge set `𝓔_{B(n)}` of the Hamiltonian | `boxEdges n` |
| configuration `ω ∈ Ω⁺_{B(n)}` | minus-set `S ∈ cfgs n` |
| spin `σᵢ(ω) ∈ {±1}` | `sigma S i` (real), `spin S i` (`ZMod 2`) |
| dual lattice `ℤ² + (½,½)` | `DualV` (integer indexing, offset by ½) |
| dual edge `e*` | `Edge.dualEnds` |
| disagreement set `𝓔*(ω)` | `Dis n S` |
| even-degree property (Lemma on plaquette parity) | `IsEven`, `isEven_Dis` |
| contour `γ*` (closed circuit, deformation rule) | cycle walk `IsCycleWalk v w`, edge set `walkFinset v w` |
| `\|γ*\|` (length) | `w.length = (walkFinset v w).card` |
| interior `Int(γ*)` | `Intr n γ` = `{i ∣ In γ i = 1}` |
| "γ* surrounds 0" | `In γ (0,0) = 1` |
| discrete Jordan lemma `lem:edge-boundary` | `In_horiz`, `In_vert`, `mem_Intr_iff` |
| `lem:surround` (σ₀ = -1 ⟹ surrounded) | `spin_eq_In` + `exists_anchored_cycle` |
| `lem:cross` (anchor at `k ≤ ℓ/2 - 1`) | the `2*k + 2 ≤ ℓ` clause of `exists_anchored_cycle` |
| erasure map `T_{γ*}` | `flip n γ` |
| energy identity `H(ω) - H(T_{γ*}ω) = 2β\|γ*\|` | `card_Dis_flip` (+ `exp_neg_ham_eq` bridge) |
| Peierls' estimate (Lemma 3.37, eq. 3.34) | `evCyc_le` |
| counting Lemma 3.38 / walk count | `words`, `card_words`, `idx` |
| Gibbs measure `μ⁺_{B(n);β,0}` | weights `wt`/`Z` (≅ `exp(-ham)` by `exp_neg_ham_eq`) |
| `⟨σ₀⟩⁺_{B(n);β,0}` | `gibbsSigma0 n β` |
| Theorem `thm:main` (with `β₀ = 2` here) | `peierls_argument` |
