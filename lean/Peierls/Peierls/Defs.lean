import Mathlib

/-!
# The Peierls argument for the 2D Ising model: definitions

This file sets up the combinatorial framework for a fully formal proof of the
Peierls argument, following the companion document `Peierls_Argument.tex` of
this repository (itself a complete write-up of §3.7.2 of Friedli–Velenik,
Chapter 3), but reorganized to avoid plane topology entirely:

* Spins live in `ZMod 2` (`0` = spin `+1`, `1` = spin `-1`).  A configuration
  in the box `B(n)` with `+` boundary condition is identified with the finite
  set `S ⊆ B(n)` of sites carrying spin `-1`.
* The "contours" of the LaTeX document are replaced by *closed edge-distinct
  walks* in the dual lattice, and the notion of interior is defined by the
  *crossing parity* function `In γ i`: the parity of the number of edges of
  `γ` whose dual edge crosses the rightward horizontal ray out of the site
  `i`.  The two Jordan-type lemmas of the LaTeX document become finite
  incidence-counting identities in `ZMod 2` (file `Parity.lean`).

## Conventions

* `Site = ℤ × ℤ` are the vertices of the lattice.
* `Edge.H a b` is the horizontal lattice edge `{(a,b), (a+1,b)}`;
  `Edge.V a b` is the vertical lattice edge `{(a,b), (a,b+1)}`.
* `DualV = ℤ × ℤ`, where `(p, q) : DualV` denotes the point `(p+½, q+½)` of
  the dual lattice `ℤ² + (½,½)`.
* The dual edge of `Edge.H a b` is the vertical unit segment crossing it,
  joining the dual vertices `(a, b-1)` and `(a, b)`; the dual edge of
  `Edge.V a b` joins `(a-1, b)` and `(a, b)`.
-/

namespace Peierls

noncomputable section

open Finset

/-- Sites of the lattice `ℤ²`. -/
abbrev Site : Type := ℤ × ℤ

/-- Dual vertices: `(p, q) : DualV` denotes the dual-lattice point `(p+½, q+½)`. -/
abbrev DualV : Type := ℤ × ℤ

/-- Nearest-neighbour lattice edges.  `H a b = {(a,b), (a+1,b)}`,
`V a b = {(a,b), (a,b+1)}`. -/
inductive Edge : Type
  | H : ℤ → ℤ → Edge
  | V : ℤ → ℤ → Edge
  deriving DecidableEq

namespace Edge

/-- The two endpoints (sites) of a lattice edge. -/
def ends : Edge → Site × Site
  | H a b => ((a, b), (a + 1, b))
  | V a b => ((a, b), (a, b + 1))

/-- The two endpoints of the dual edge of a lattice edge (see module docstring). -/
def dualEnds : Edge → DualV × DualV
  | H a b => ((a, b - 1), (a, b))
  | V a b => ((a - 1, b), (a, b))

end Edge

/-- The box `B(n) = {-n, …, n}²` as a finset of sites. -/
def siteBox (n : ℕ) : Finset Site :=
  Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n

/-- All lattice edges having at least one endpoint in `B(n)`. -/
def boxEdges (n : ℕ) : Finset Edge :=
  ((Finset.Icc (-(n : ℤ) - 1) n ×ˢ Finset.Icc (-(n : ℤ)) n).image fun p => Edge.H p.1 p.2) ∪
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ) - 1) n).image fun p => Edge.V p.1 p.2)

/-- Configurations with `+` boundary condition: all subsets of the box (the set of
`-1` spins). -/
def cfgs (n : ℕ) : Finset (Finset Site) := (siteBox n).powerset

/-- The spin at site `i`, additively: `0` for spin `+1`, `1` for spin `-1`. -/
def spin (S : Finset Site) (i : Site) : ZMod 2 := if i ∈ S then 1 else 0

/-- Disagreement indicator of a lattice edge (`1` iff the two endpoint spins differ). -/
def disInd (S : Finset Site) (e : Edge) : ZMod 2 := spin S e.ends.1 + spin S e.ends.2

/-- The set of disagreement edges of the configuration `S` (within the ambient set
`boxEdges n`; every disagreement edge of a configuration `S ⊆ B(n)` lies there). -/
def Dis (n : ℕ) (S : Finset Site) : Finset Edge :=
  (boxEdges n).filter fun e => disInd S e = 1

/-- The degree of a dual vertex in (the set of duals of) a finite set of edges. -/
def deg (γ : Finset Edge) (v : DualV) : ℕ :=
  (γ.filter fun e => v = e.dualEnds.1 ∨ v = e.dualEnds.2).card

/-- An edge set is *even* if every dual vertex has even degree in it. -/
def IsEven (γ : Finset Edge) : Prop := ∀ v : DualV, Even (deg γ v)

/-- Does the dual of `e` cross the rightward horizontal ray out of site `i`?
Only duals of horizontal edges `H m b` (vertical dual segments) do, and the
crossing condition is `b = i.2 ∧ i.1 ≤ m`. -/
def CrossesRight (i : Site) (e : Edge) : Prop :=
  match e with
  | .H m b => b = i.2 ∧ i.1 ≤ m
  | .V _ _ => False

instance (i : Site) (e : Edge) : Decidable (CrossesRight i e) :=
  match e with
  | .H m b => inferInstanceAs (Decidable (b = i.2 ∧ i.1 ≤ m))
  | .V _ _ => inferInstanceAs (Decidable False)

/-- Crossing-parity "interior function": the parity of the number of edges of `γ`
whose dual crosses the rightward horizontal ray out of the site `i`.  The site `i`
is *inside* `γ` iff `In γ i = 1`. -/
def In (γ : Finset Edge) (i : Site) : ZMod 2 :=
  ((γ.filter (CrossesRight i)).card : ZMod 2)

/-- The interior of `γ`, as a subset of the box `B(n)`.  (For even `γ ⊆ boxEdges n`
this captures *all* sites with `In γ i = 1`; see `mem_Intr_iff` in `Flip.lean`.) -/
def Intr (n : ℕ) (γ : Finset Edge) : Finset Site :=
  (siteBox n).filter fun i => In γ i = 1

/-- Contour-erasure map: flip all spins in the interior of `γ`. -/
def flip (n : ℕ) (γ : Finset Edge) (S : Finset Site) : Finset Site :=
  symmDiff S (Intr n γ)

/-! ## Walks in the dual lattice -/

/-- Step directions for walks in the dual lattice. -/
inductive Dir : Type
  | U | D | L | R
  deriving DecidableEq, Fintype

/-- Move a dual vertex one step. -/
def DualV.step : DualV → Dir → DualV
  | (p, q), .U => (p, q + 1)
  | (p, q), .D => (p, q - 1)
  | (p, q), .L => (p - 1, q)
  | (p, q), .R => (p + 1, q)

/-- The lattice edge whose dual joins `v` and `v.step d`. -/
def stepEdge : DualV → Dir → Edge
  | (p, q), .U => .H p (q + 1)
  | (p, q), .D => .H p q
  | (p, q), .L => .V p q
  | (p, q), .R => .V (p + 1) q

/-- Endpoint of the walk with direction word `w` starting at `v`. -/
def walkEnd (v : DualV) : List Dir → DualV
  | [] => v
  | d :: w => walkEnd (v.step d) w

/-- The list of (lattice) edges whose duals are traversed by the walk `w` from `v`. -/
def walkEdges (v : DualV) : List Dir → List Edge
  | [] => []
  | d :: w => stepEdge v d :: walkEdges (v.step d) w

/-- A *cycle walk*: a nonempty closed walk traversing pairwise distinct dual edges.
This is the formal counterpart of a "contour" of the LaTeX companion document. -/
def IsCycleWalk (v : DualV) (w : List Dir) : Prop :=
  walkEnd v w = v ∧ (walkEdges v w).Nodup ∧ w ≠ []

instance (v : DualV) (w : List Dir) : Decidable (IsCycleWalk v w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The edge set of a walk. -/
def walkFinset (v : DualV) (w : List Dir) : Finset Edge :=
  (walkEdges v w).toFinset

/-- All direction words of length `m`, as a finset. -/
def words : ℕ → Finset (List Dir)
  | 0 => {[]}
  | m + 1 => ((Finset.univ : Finset Dir) ×ˢ words m).image fun p => p.1 :: p.2

/-! ## The Gibbs measure layer (finite sums of nonnegative real weights)

The Gibbs weight of `S` at inverse temperature `β` (at zero magnetic field, with
`+` boundary condition) is proportional to `x ^ (Dis n S).card` with
`x = exp (-2β)`; we take the latter as the definition of the weight, with `x` an
abstract parameter, and relate it to the exponential Hamiltonian form in
`Bound.lean`. -/

/-- The weight of a configuration. -/
def wt (n : ℕ) (x : ℝ) (S : Finset Site) : ℝ := x ^ (Dis n S).card

/-- The partition function. -/
def Z (n : ℕ) (x : ℝ) : ℝ := ∑ S ∈ cfgs n, wt n x S

/-- Total weight of the event "all of `γ` consists of disagreement edges". -/
def evCyc (n : ℕ) (x : ℝ) (γ : Finset Edge) : ℝ :=
  ∑ S ∈ (cfgs n).filter (fun S => γ ⊆ Dis n S), wt n x S

/-- Total weight of the event "the spin at the origin is `-1`". -/
def evMinus (n : ℕ) (x : ℝ) : ℝ :=
  ∑ S ∈ (cfgs n).filter (fun S => ((0 : ℤ), (0 : ℤ)) ∈ S), wt n x S

/-- The real-valued spin `σ_i ∈ {±1}` at site `i`. -/
def sigma (S : Finset Site) (i : Site) : ℝ := if i ∈ S then -1 else 1

/-- The Hamiltonian of the Ising model in `B(n)` with `+` boundary condition at
zero magnetic field (Definition 3.3 of the transcription, with `h = 0`):
`-β ∑ σ_i σ_j` over all nearest-neighbour edges meeting `B(n)`. -/
def ham (n : ℕ) (β : ℝ) (S : Finset Site) : ℝ :=
  -β * ∑ e ∈ boxEdges n, sigma S e.ends.1 * sigma S e.ends.2

/-- The finite-volume Gibbs expectation `⟨σ₀⟩⁺_{B(n); β, 0}` of the spin at the
origin. -/
def gibbsSigma0 (n : ℕ) (β : ℝ) : ℝ :=
  (∑ S ∈ cfgs n, sigma S ((0 : ℤ), (0 : ℤ)) * Real.exp (-ham n β S)) /
    (∑ S ∈ cfgs n, Real.exp (-ham n β S))

/-! ## Basic membership lemmas -/

theorem mem_siteBox {n : ℕ} {i : Site} :
    i ∈ siteBox n ↔ -(n : ℤ) ≤ i.1 ∧ i.1 ≤ n ∧ -(n : ℤ) ≤ i.2 ∧ i.2 ≤ n := by
  cases i with
  | mk a b => simp [siteBox, Finset.mem_Icc, and_assoc]

theorem H_mem_boxEdges {n : ℕ} {a b : ℤ} :
    Edge.H a b ∈ boxEdges n ↔ -(n : ℤ) - 1 ≤ a ∧ a ≤ n ∧ -(n : ℤ) ≤ b ∧ b ≤ n := by
  simp only [boxEdges, Finset.mem_union, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro (⟨p, q, hpq, h⟩ | ⟨p, q, hpq, h⟩)
    · cases h
      simp only [Finset.mem_Icc] at hpq
      exact ⟨hpq.1.1, hpq.1.2, hpq.2.1, hpq.2.2⟩
    · cases h
  · intro h
    exact Or.inl ⟨a, b, by simp [Finset.mem_Icc]; omega, rfl⟩

theorem V_mem_boxEdges {n : ℕ} {a b : ℤ} :
    Edge.V a b ∈ boxEdges n ↔ -(n : ℤ) ≤ a ∧ a ≤ n ∧ -(n : ℤ) - 1 ≤ b ∧ b ≤ n := by
  simp only [boxEdges, Finset.mem_union, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro (⟨p, q, hpq, h⟩ | ⟨p, q, hpq, h⟩)
    · cases h
    · cases h
      simp only [Finset.mem_Icc] at hpq
      exact ⟨hpq.1.1, hpq.1.2, hpq.2.1, hpq.2.2⟩
  · intro h
    exact Or.inr ⟨a, b, by simp [Finset.mem_Icc]; omega, rfl⟩

/-- An edge belongs to `boxEdges n` iff one of its endpoints is in the box. -/
theorem mem_boxEdges_iff {n : ℕ} {e : Edge} :
    e ∈ boxEdges n ↔ e.ends.1 ∈ siteBox n ∨ e.ends.2 ∈ siteBox n := by
  cases e with
  | H a b => simp only [Edge.ends, H_mem_boxEdges, mem_siteBox]; omega
  | V a b => simp only [Edge.ends, V_mem_boxEdges, mem_siteBox]; omega

theorem card_Dir : Fintype.card Dir = 4 := rfl

theorem card_words (m : ℕ) : (words m).card = 4 ^ m := by
  induction m with
  | zero => simp [words]
  | succ m ih =>
    rw [words, Finset.card_image_of_injective _ (fun p q h => by
      cases p; cases q; simpa using h)]
    rw [Finset.card_product, Finset.card_univ, card_Dir, ih]
    ring

theorem mem_words {m : ℕ} {w : List Dir} : w ∈ words m ↔ w.length = m := by
  induction m generalizing w with
  | zero => cases w <;> simp [words]
  | succ m ih =>
    cases w with
    | nil => simp [words]
    | cons d w' =>
      simp only [words, Finset.mem_image, Finset.mem_product, Prod.exists, List.length_cons]
      constructor
      · rintro ⟨p, q, ⟨-, hq⟩, h⟩
        cases h
        simp [ih.mp hq]
      · intro h
        exact ⟨d, w', ⟨Finset.mem_univ d, ih.mpr (by omega)⟩, rfl⟩

theorem length_walkEdges (v : DualV) (w : List Dir) :
    (walkEdges v w).length = w.length := by
  induction w generalizing v with
  | nil => rfl
  | cons d w ih => simp [walkEdges, ih]

theorem card_walkFinset {v : DualV} {w : List Dir} (h : (walkEdges v w).Nodup) :
    (walkFinset v w).card = w.length := by
  rw [walkFinset, List.toFinset_card_of_nodup h, length_walkEdges]

end

end Peierls
