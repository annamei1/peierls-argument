import Peierls.Defs

/-!
# Parity lemmas: the combinatorial Jordan machinery

This file proves the crossing-parity identities that replace the Jordan-curve
arguments of the LaTeX companion document:

* `In_horiz` (L-horiz): for any `γ`, `In γ (a,b) + In γ (a+1,b)` is the
  indicator of `H a b ∈ γ`.  (The two crossing filters differ by exactly the
  one edge `H a b`.)
* `incidence_even`: for even `γ` and any predicate `R` on dual vertices, the
  sum over `e ∈ γ` of the number of dual endpoints of `e` satisfying `R` is
  even.  (Double counting: it equals the sum over dual vertices in `R` of
  their degrees, all even.)
* `In_vert` (L-vert): for *even* `γ`,
  `In γ (a,b) + In γ (a,b+1)` is the indicator of `V a b ∈ γ`.
  Proof: apply `incidence_even` with `R v := (v.2 = b ∧ a ≤ v.1)` and classify
  the contributions: an edge `H m c ∈ γ` contributes `1` iff `a ≤ m` and
  `c = b` (this is the `In (a,b)` filter) or `c = b+1` (the `In (a,b+1)`
  filter); an edge `V m c` contributes an odd count iff `m = a ∧ c = b`.
* `rowCount_even`: for even `γ`, the number of edges `H m b ∈ γ` in any fixed
  row `b` is even.  (Same incidence argument with `R v := (b ≤ v.2)`.)
* `isEven_Dis`: the disagreement set of any configuration is even
  (plaquette parity).
* `spin_eq_In` (the σ-formula): `spin S i = In (Dis n S) i` for `S ⊆ B(n)`.
  Proof: both sides vanish far to the right and have the same increments
  along each row by `In_horiz`; induct leftwards along the row.
-/

namespace Peierls

open Finset

/-! ## Small arithmetic helpers -/

private lemma even_of_two_dvd {k : ℕ} (h : 2 ∣ k) : Even k := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t, by omega⟩

private lemma two_dvd_of_even {k : ℕ} (h : Even k) : 2 ∣ k := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t, by omega⟩

private lemma zmod_two_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

private lemma zmod_two_natCast_even {k : ℕ} (h : Even k) : ((k : ℕ) : ZMod 2) = 0 := by
  obtain ⟨t, rfl⟩ := h
  rw [Nat.cast_add]
  exact zmod_two_add_self _

private lemma even_of_natCast_zmod_two {k : ℕ} (h : ((k : ℕ) : ZMod 2) = 0) : Even k :=
  even_of_two_dvd ((CharP.cast_eq_zero_iff (ZMod 2) 2 k).mp h)

/-- The crossing parity is the (mod 2) sum of the crossing indicators. -/
private lemma In_eq_sum (γ : Finset Edge) (i : Site) :
    In γ i = ∑ e ∈ γ, if CrossesRight i e then (1 : ZMod 2) else 0 :=
  (Finset.sum_boole _ _).symm

/-! ## L-horiz -/

/-- The crossing filters of `(a, b)` and `(a+1, b)` differ exactly by `H a b`. -/
theorem In_horiz (γ : Finset Edge) (a b : ℤ) :
    In γ (a, b) + In γ (a + 1, b) = if Edge.H a b ∈ γ then 1 else 0 := by
  have hdisj : Disjoint (γ.filter (CrossesRight (a + 1, b))) (γ.filter (· = Edge.H a b)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    rw [Finset.mem_filter] at he1 he2
    obtain ⟨-, rfl⟩ := he2
    have hc := he1.2
    simp only [CrossesRight] at hc
    omega
  have hcongr : γ.filter (CrossesRight (a, b))
      = γ.filter (fun e => CrossesRight (a + 1, b) e ∨ e = Edge.H a b) := by
    apply Finset.filter_congr
    intro e _
    cases e with
    | H m c =>
      simp only [CrossesRight, Edge.H.injEq]
      omega
    | V m c =>
      simp [CrossesRight]
  have hcard : (γ.filter (CrossesRight (a, b))).card
      = (γ.filter (CrossesRight (a + 1, b))).card
        + (γ.filter (· = Edge.H a b)).card := by
    rw [hcongr, Finset.filter_or]
    exact Finset.card_union_of_disjoint hdisj
  have hH : (((γ.filter (· = Edge.H a b)).card : ℕ) : ZMod 2)
      = if Edge.H a b ∈ γ then 1 else 0 := by
    rw [Finset.filter_eq']
    split_ifs <;> simp
  have hfin : ∀ x y : ZMod 2, x + y + x = y := by decide
  simp only [In]
  rw [hcard, Nat.cast_add, hH]
  exact hfin _ _

/-! ## The incidence double-count -/

/-- The number of dual endpoints of `e` lying in a region `R`. -/
def endCount (R : DualV → Prop) [DecidablePred R] (e : Edge) : ℕ :=
  (if R e.dualEnds.1 then 1 else 0) + (if R e.dualEnds.2 then 1 else 0)

/-- The two ends of a dual edge are distinct dual vertices. -/
private lemma dualEnds_ne (e : Edge) : e.dualEnds.1 ≠ e.dualEnds.2 := by
  cases e <;>
    · simp only [Edge.dualEnds, ne_eq, Prod.mk.injEq, not_and]
      intro h
      omega

/-- Double counting: summing `endCount R` over an even edge set gives an even
number.  (It equals the sum of the degrees of the dual vertices in `R`, and each
degree is even; only finitely many dual vertices meet `γ`.) -/
theorem incidence_even {γ : Finset Edge} (hγ : IsEven γ) (R : DualV → Prop)
    [DecidablePred R] : Even (∑ e ∈ γ, endCount R e) := by
  obtain ⟨T, hT⟩ : ∃ T : Finset DualV, ∀ e ∈ γ, e.dualEnds.1 ∈ T ∧ e.dualEnds.2 ∈ T :=
    ⟨γ.biUnion fun e => {e.dualEnds.1, e.dualEnds.2}, fun e he =>
      ⟨Finset.mem_biUnion.mpr ⟨e, he, by simp⟩, Finset.mem_biUnion.mpr ⟨e, he, by simp⟩⟩⟩
  have hpoint : ∀ e ∈ γ, endCount R e
      = ∑ v ∈ T.filter R, if v = e.dualEnds.1 ∨ v = e.dualEnds.2 then 1 else 0 := by
    intro e he
    have hne := dualEnds_ne e
    have m1 : e.dualEnds.1 ∈ T.filter R ↔ R e.dualEnds.1 :=
      ⟨fun hx => (Finset.mem_filter.mp hx).2, fun hx => Finset.mem_filter.mpr ⟨(hT e he).1, hx⟩⟩
    have m2 : e.dualEnds.2 ∈ T.filter R ↔ R e.dualEnds.2 :=
      ⟨fun hx => (Finset.mem_filter.mp hx).2, fun hx => Finset.mem_filter.mpr ⟨(hT e he).2, hx⟩⟩
    have hsplit : ∀ v ∈ T.filter R,
        (if v = e.dualEnds.1 ∨ v = e.dualEnds.2 then (1 : ℕ) else 0)
          = (if v = e.dualEnds.1 then 1 else 0) + (if v = e.dualEnds.2 then 1 else 0) := by
      intro v _
      by_cases hv1 : v = e.dualEnds.1 <;> by_cases hv2 : v = e.dualEnds.2
      · exact absurd (hv1.symm.trans hv2) hne
      · rw [if_pos (Or.inl hv1), if_pos hv1, if_neg hv2]
      · rw [if_pos (Or.inr hv2), if_neg hv1, if_pos hv2]
      · rw [if_neg (fun h => h.elim hv1 hv2), if_neg hv1, if_neg hv2]
    calc endCount R e
        = (if e.dualEnds.1 ∈ T.filter R then 1 else 0)
          + (if e.dualEnds.2 ∈ T.filter R then 1 else 0) := by
          simp only [endCount, m1, m2]
      _ = ∑ v ∈ T.filter R, ((if v = e.dualEnds.1 then 1 else 0)
          + (if v = e.dualEnds.2 then 1 else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      _ = ∑ v ∈ T.filter R, if v = e.dualEnds.1 ∨ v = e.dualEnds.2 then 1 else 0 :=
          Finset.sum_congr rfl fun v hv => (hsplit v hv).symm
  have hmain : ∑ e ∈ γ, endCount R e = ∑ v ∈ T.filter R, deg γ v :=
    calc ∑ e ∈ γ, endCount R e
        = ∑ e ∈ γ, ∑ v ∈ T.filter R,
            (if v = e.dualEnds.1 ∨ v = e.dualEnds.2 then 1 else 0) :=
          Finset.sum_congr rfl hpoint
      _ = ∑ v ∈ T.filter R, ∑ e ∈ γ,
            (if v = e.dualEnds.1 ∨ v = e.dualEnds.2 then 1 else 0) := Finset.sum_comm
      _ = ∑ v ∈ T.filter R, deg γ v :=
          Finset.sum_congr rfl fun v _ => (Finset.card_filter _ _).symm
  rw [hmain]
  exact even_of_two_dvd (Finset.dvd_sum fun v _ => two_dvd_of_even (hγ v))

/-! ## L-vert and row parity -/

/-- Pointwise classification of `endCount` for the half-row region
`{v | v.2 = b ∧ a ≤ v.1}`: mod 2 it is the sum of the two crossing indicators
and the indicator of being the edge `V a b`. -/
private lemma endCount_vert (a b : ℤ) (e : Edge) :
    ((endCount (fun v => v.2 = b ∧ a ≤ v.1) e : ℕ) : ZMod 2)
      = (if CrossesRight (a, b) e then 1 else 0)
        + (if CrossesRight (a, b + 1) e then 1 else 0)
        + (if e = Edge.V a b then 1 else 0) := by
  cases e with
  | H m c =>
    simp only [endCount, Edge.dualEnds, CrossesRight, reduceCtorEq, if_false]
    split_ifs <;> first | (exfalso; omega) | (push_cast; decide)
  | V m c =>
    simp only [endCount, Edge.dualEnds, CrossesRight, Edge.V.injEq, if_false]
    split_ifs <;> first | (exfalso; omega) | (push_cast; decide)

/-- For an even edge set, crossing parities of vertical neighbours differ by the
indicator of the connecting vertical edge. -/
theorem In_vert {γ : Finset Edge} (hγ : IsEven γ) (a b : ℤ) :
    In γ (a, b) + In γ (a, b + 1) = if Edge.V a b ∈ γ then 1 else 0 := by
  have h0 : ((∑ e ∈ γ, endCount (fun v => v.2 = b ∧ a ≤ v.1) e : ℕ) : ZMod 2) = 0 :=
    zmod_two_natCast_even (incidence_even hγ _)
  have hV : (∑ e ∈ γ, if e = Edge.V a b then (1 : ZMod 2) else 0)
      = if Edge.V a b ∈ γ then 1 else 0 := by
    rw [Finset.sum_boole, Finset.filter_eq']
    split_ifs <;> simp
  have htot : In γ (a, b) + In γ (a, b + 1)
      + (if Edge.V a b ∈ γ then (1 : ZMod 2) else 0) = 0 := by
    calc In γ (a, b) + In γ (a, b + 1) + (if Edge.V a b ∈ γ then (1 : ZMod 2) else 0)
        = (∑ e ∈ γ, if CrossesRight (a, b) e then (1 : ZMod 2) else 0)
          + (∑ e ∈ γ, if CrossesRight (a, b + 1) e then (1 : ZMod 2) else 0)
          + (∑ e ∈ γ, if e = Edge.V a b then (1 : ZMod 2) else 0) := by
          rw [In_eq_sum, In_eq_sum, hV]
      _ = ∑ e ∈ γ, ((if CrossesRight (a, b) e then (1 : ZMod 2) else 0)
          + (if CrossesRight (a, b + 1) e then (1 : ZMod 2) else 0)
          + (if e = Edge.V a b then (1 : ZMod 2) else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = ∑ e ∈ γ, ((endCount (fun v => v.2 = b ∧ a ≤ v.1) e : ℕ) : ZMod 2) :=
          Finset.sum_congr rfl fun e _ => (endCount_vert a b e).symm
      _ = ((∑ e ∈ γ, endCount (fun v => v.2 = b ∧ a ≤ v.1) e : ℕ) : ZMod 2) :=
          (Nat.cast_sum _ _).symm
      _ = 0 := h0
  have hfin : ∀ x y z : ZMod 2, x + y + z = 0 → x + y = z := by decide
  exact hfin _ _ _ htot

/-- Is `e` a horizontal edge lying in the row at height `b`? -/
def InRow (b : ℤ) (e : Edge) : Prop :=
  match e with
  | .H _ c => c = b
  | .V _ _ => False

instance (b : ℤ) (e : Edge) : Decidable (InRow b e) :=
  match e with
  | .H _ c => inferInstanceAs (Decidable (c = b))
  | .V _ _ => inferInstanceAs (Decidable False)

/-- Pointwise classification of `endCount` for the upper half-plane region
`{v | b ≤ v.2}`: mod 2 it is the indicator of being a row-`b` horizontal edge. -/
private lemma endCount_row (b : ℤ) (e : Edge) :
    ((endCount (fun v => b ≤ v.2) e : ℕ) : ZMod 2) = if InRow b e then 1 else 0 := by
  cases e with
  | H m c =>
    simp only [endCount, Edge.dualEnds, InRow]
    split_ifs <;> first | (exfalso; omega) | (push_cast; decide)
  | V m c =>
    simp only [endCount, Edge.dualEnds, InRow, if_false]
    split_ifs <;> (push_cast; decide)

/-- For an even edge set, every row contains an even number of horizontal edges. -/
theorem rowCount_even {γ : Finset Edge} (hγ : IsEven γ) (b : ℤ) :
    Even ((γ.filter (InRow b)).card) := by
  apply even_of_natCast_zmod_two
  calc (((γ.filter (InRow b)).card : ℕ) : ZMod 2)
      = ∑ e ∈ γ, if InRow b e then (1 : ZMod 2) else 0 := (Finset.sum_boole _ _).symm
    _ = ∑ e ∈ γ, ((endCount (fun v => b ≤ v.2) e : ℕ) : ZMod 2) :=
        Finset.sum_congr rfl fun e _ => (endCount_row b e).symm
    _ = ((∑ e ∈ γ, endCount (fun v => b ≤ v.2) e : ℕ) : ZMod 2) := (Nat.cast_sum _ _).symm
    _ = 0 := zmod_two_natCast_even (incidence_even hγ _)

/-! ## Vanishing of `In` far away -/

/-- `In` vanishes at sites to the right of all horizontal edges of `γ`. -/
theorem In_eq_zero_right (γ : Finset Edge) (a b : ℤ)
    (h : ∀ m c : ℤ, Edge.H m c ∈ γ → m < a) : In γ (a, b) = 0 := by
  have hempty : γ.filter (CrossesRight (a, b)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e he
    cases e with
    | H m c =>
      have hm := h m c he
      simp only [CrossesRight]
      omega
    | V m c => simp [CrossesRight]
  show ((γ.filter (CrossesRight (a, b))).card : ZMod 2) = 0
  rw [hempty, Finset.card_empty, Nat.cast_zero]

/-- For even `γ`, `In` vanishes at sites to the left of all horizontal edges of
`γ` (the whole-row crossing count is even by `rowCount_even`). -/
theorem In_eq_zero_left {γ : Finset Edge} (hγ : IsEven γ) (a b : ℤ)
    (h : ∀ m c : ℤ, Edge.H m c ∈ γ → a ≤ m) : In γ (a, b) = 0 := by
  have hfe : γ.filter (CrossesRight (a, b)) = γ.filter (InRow b) := by
    apply Finset.filter_congr
    intro e he
    cases e with
    | H m c =>
      simp only [CrossesRight, InRow]
      exact ⟨fun hc => hc.1, fun hc => ⟨hc, h m c he⟩⟩
    | V m c => simp [CrossesRight, InRow]
  show ((γ.filter (CrossesRight (a, b))).card : ZMod 2) = 0
  rw [hfe]
  exact zmod_two_natCast_even (rowCount_even hγ b)

/-! ## Evenness of the disagreement set -/

/-- A disagreement edge of a configuration `S ⊆ B(n)` lies in `boxEdges n`;
hence membership in `Dis n S` is equivalent to the disagreement indicator. -/
theorem mem_Dis_iff {n : ℕ} {S : Finset Site} (hS : S ⊆ siteBox n) {e : Edge} :
    e ∈ Dis n S ↔ disInd S e = 1 := by
  unfold Dis
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hd
    refine ⟨?_, hd⟩
    have hmem : e.ends.1 ∈ S ∨ e.ends.2 ∈ S := by
      by_contra hcon
      rw [not_or] at hcon
      unfold disInd spin at hd
      rw [if_neg hcon.1, if_neg hcon.2] at hd
      exact absurd hd (by decide)
    exact mem_boxEdges_iff.mpr (hmem.imp (fun h => hS h) fun h => hS h)

/-- Plaquette parity: the disagreement set of any configuration is even. -/
theorem isEven_Dis {n : ℕ} {S : Finset Site} (hS : S ⊆ siteBox n) :
    IsEven (Dis n S) := by
  intro v
  obtain ⟨p, q⟩ := v
  have hA : ∀ e : Edge, (((p, q) : DualV) = e.dualEnds.1 ∨ ((p, q) : DualV) = e.dualEnds.2)
      ↔ e ∈ ({Edge.H p q, Edge.H p (q + 1), Edge.V p q, Edge.V (p + 1) q} : Finset Edge) := by
    intro e
    cases e with
    | H m c =>
      simp only [Edge.dualEnds, Prod.mk.injEq, Finset.mem_insert, Finset.mem_singleton,
        Edge.H.injEq, reduceCtorEq, or_false]
      omega
    | V m c =>
      simp only [Edge.dualEnds, Prod.mk.injEq, Finset.mem_insert, Finset.mem_singleton,
        Edge.V.injEq, reduceCtorEq, false_or]
      omega
  have hcongr : (Dis n S).filter
        (fun e => ((p, q) : DualV) = e.dualEnds.1 ∨ ((p, q) : DualV) = e.dualEnds.2)
      = (Dis n S).filter
        (fun e => e ∈ ({Edge.H p q, Edge.H p (q + 1), Edge.V p q,
          Edge.V (p + 1) q} : Finset Edge)) :=
    Finset.filter_congr fun e _ => hA e
  have hdeg : deg (Dis n S) (p, q)
      = (({Edge.H p q, Edge.H p (q + 1), Edge.V p q, Edge.V (p + 1) q} : Finset Edge).filter
          (fun e => e ∈ Dis n S)).card := by
    unfold deg
    rw [hcongr, Finset.filter_mem_eq_inter, Finset.inter_comm, ← Finset.filter_mem_eq_inter]
  have hne1 : Edge.H p q ∉ ({Edge.H p (q + 1), Edge.V p q, Edge.V (p + 1) q} : Finset Edge) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Edge.H.injEq, reduceCtorEq, or_false]
    omega
  have hne2 : Edge.H p (q + 1) ∉ ({Edge.V p q, Edge.V (p + 1) q} : Finset Edge) := by
    simp
  have hne3 : Edge.V p q ∉ ({Edge.V (p + 1) q} : Finset Edge) := by
    simp only [Finset.mem_singleton, Edge.V.injEq]
    omega
  have hB : ∀ e : Edge, (((if e ∈ Dis n S then 1 else 0 : ℕ)) : ZMod 2) = disInd S e := by
    intro e
    by_cases h : e ∈ Dis n S
    · rw [if_pos h, (mem_Dis_iff hS).mp h]
      exact Nat.cast_one
    · rw [if_neg h]
      have h0 : disInd S e = 0 := by
        have hz : ∀ z : ZMod 2, ¬z = 1 → z = 0 := by decide
        exact hz _ fun hh => h ((mem_Dis_iff hS).mpr hh)
      rw [h0]
      exact Nat.cast_zero
  have hcast : ((deg (Dis n S) (p, q) : ℕ) : ZMod 2)
      = disInd S (Edge.H p q) + (disInd S (Edge.H p (q + 1))
        + (disInd S (Edge.V p q) + disInd S (Edge.V (p + 1) q))) := by
    rw [hdeg, Finset.card_filter, Finset.sum_insert hne1, Finset.sum_insert hne2,
      Finset.sum_insert hne3, Finset.sum_singleton, Nat.cast_add, Nat.cast_add, Nat.cast_add,
      hB, hB, hB, hB]
  have hzero : disInd S (Edge.H p q) + (disInd S (Edge.H p (q + 1))
      + (disInd S (Edge.V p q) + disInd S (Edge.V (p + 1) q))) = 0 := by
    have hx : ∀ x y z w : ZMod 2, x + y + (z + w + (x + z + (y + w))) = 0 := by decide
    show spin S (p, q) + spin S (p + 1, q) + (spin S (p, q + 1) + spin S (p + 1, q + 1)
      + (spin S (p, q) + spin S (p, q + 1) + (spin S (p + 1, q) + spin S (p + 1, q + 1)))) = 0
    exact hx _ _ _ _
  exact even_of_natCast_zmod_two (hcast.trans hzero)

/-! ## The σ-formula -/

/-- The fundamental identity: the spin at `i` equals the crossing parity of the
disagreement set at `i`.  In particular `σ_0 = -1` forces the origin to be
"inside" the disagreement set. -/
theorem spin_eq_In {n : ℕ} {S : Finset Site} (hS : S ⊆ siteBox n) (i : Site) :
    spin S i = In (Dis n S) i := by
  obtain ⟨a, b⟩ := i
  have hfar : ∀ a' : ℤ, (n : ℤ) < a' → spin S (a', b) = In (Dis n S) (a', b) := by
    intro a' ha'
    have hmem : ((a', b) : Site) ∉ S := by
      intro hmem
      have hx : a' ≤ (n : ℤ) := (mem_siteBox.mp (hS hmem)).2.1
      omega
    have h1 : spin S (a', b) = 0 := by
      unfold spin
      rw [if_neg hmem]
    have h2 : In (Dis n S) (a', b) = 0 := by
      apply In_eq_zero_right
      intro m c hmc
      have hbox : Edge.H m c ∈ boxEdges n := by
        unfold Dis at hmc
        exact (Finset.mem_filter.mp hmc).1
      have hx : m ≤ (n : ℤ) := (H_mem_boxEdges.mp hbox).2.1
      omega
    rw [h1, h2]
  have hstep : ∀ a' : ℤ, spin S (a', b) + In (Dis n S) (a', b)
      = spin S (a' + 1, b) + In (Dis n S) (a' + 1, b) := by
    intro a'
    have hends : disInd S (Edge.H a' b) = spin S (a', b) + spin S (a' + 1, b) := rfl
    have hd : spin S (a', b) + spin S (a' + 1, b)
        = if Edge.H a' b ∈ Dis n S then 1 else 0 := by
      rw [← hends]
      by_cases h : Edge.H a' b ∈ Dis n S
      · rw [if_pos h]
        exact (mem_Dis_iff hS).mp h
      · rw [if_neg h]
        have hz : ∀ z : ZMod 2, ¬z = 1 → z = 0 := by decide
        exact hz _ fun hh => h ((mem_Dis_iff hS).mpr hh)
    have heq : spin S (a', b) + spin S (a' + 1, b)
        = In (Dis n S) (a', b) + In (Dis n S) (a' + 1, b) := by
      rw [hd, In_horiz]
    have hz2 : ∀ w x y z : ZMod 2, w + x = y + z → w + y = x + z := by decide
    exact hz2 _ _ _ _ heq
  have hz3 : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  have hg : ∀ k : ℕ, ∀ a' : ℤ, a' + (k : ℤ) = (n : ℤ) + 1
      → spin S (a', b) = In (Dis n S) (a', b) := by
    intro k
    induction k with
    | zero => exact fun a' hk => hfar a' (by omega)
    | succ k ih =>
      intro a' hk
      have hnext : spin S (a' + 1, b) = In (Dis n S) (a' + 1, b) := ih (a' + 1) (by omega)
      have hs := hstep a'
      rw [hnext, zmod_two_add_self (In (Dis n S) (a' + 1, b))] at hs
      exact hz3 _ _ hs
  by_cases ha : (n : ℤ) < a
  · exact hfar a ha
  · exact hg ((n : ℤ) + 1 - a).toNat a (by omega)

end Peierls
