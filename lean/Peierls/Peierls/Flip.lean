import Peierls.Parity

/-!
# The contour-erasure map and the per-contour (Peierls) estimate

For an even edge set `γ ⊆ boxEdges n`, flipping all spins in the interior
`Intr n γ` removes exactly the disagreements along `γ` (`Dis_flip`), and is an
involution of the configuration space.  This yields the Peierls estimate: the
total weight of configurations whose disagreement set contains `γ` is at most
`x ^ |γ|` times the partition function (`evCyc_le`).
-/

namespace Peierls

open Finset

/-- Dichotomy for `ZMod 2`. -/
private theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z; decide

/-- For even `γ ⊆ boxEdges n`, every site with `In γ i = 1` lies in the box
(this is part (b) of the discrete Jordan lemma `lem:edge-boundary` of the LaTeX
document).  Consequently membership in `Intr n γ` is equivalent to `In γ i = 1`. -/
theorem mem_Intr_iff {n : ℕ} {γ : Finset Edge} (hb : γ ⊆ boxEdges n)
    (he : IsEven γ) {i : Site} : i ∈ Intr n γ ↔ In γ i = 1 := by
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hIn
    obtain ⟨a, b⟩ := i
    refine Finset.mem_filter.mpr ⟨?_, hIn⟩
    -- the crossing filter is nonempty (its cardinality is odd)
    have hne : (γ.filter (CrossesRight (a, b))).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      simp only [In, h, Finset.card_empty, Nat.cast_zero] at hIn
      exact absurd hIn (by decide)
    obtain ⟨e, he'⟩ := hne
    rw [Finset.mem_filter] at he'
    obtain ⟨heγ, hcr⟩ := he'
    cases e with
    | V m c => exact absurd hcr (by simp [CrossesRight])
    | H m c =>
      obtain ⟨hcb, ham⟩ : c = b ∧ a ≤ m := hcr
      have hbox := H_mem_boxEdges.mp (hb heγ)
      -- lower bound on `a` by contradiction, via `In_eq_zero_left`
      have hlow : -(n : ℤ) ≤ a := by
        by_contra hlt
        push Not at hlt
        have h0 : In γ (a, b) = 0 :=
          In_eq_zero_left he a b fun m' c' hm' => by
            have := (H_mem_boxEdges.mp (hb hm')).1
            omega
        rw [h0] at hIn
        exact absurd hIn (by decide)
      exact mem_siteBox.mpr ⟨hlow, by omega, by omega, by omega⟩

/-- The spin of a symmetric difference is the sum of the spins. -/
private theorem spin_symmDiff (S T : Finset Site) (i : Site) :
    spin (symmDiff S T) i = spin S i + spin T i := by
  simp only [spin, Finset.mem_symmDiff]
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]
  decide

/-- The spin of the interior set is the crossing parity. -/
private theorem spin_Intr {n : ℕ} {γ : Finset Edge} (hb : γ ⊆ boxEdges n)
    (he : IsEven γ) (i : Site) : spin (Intr n γ) i = In γ i := by
  rcases zmod2_cases (In γ i) with h | h
  · rw [h, spin, if_neg]
    intro hmem
    rw [mem_Intr_iff hb he, h] at hmem
    exact absurd hmem (by decide)
  · rw [h, spin, if_pos ((mem_Intr_iff hb he).mpr h)]

/-- Spins after flipping: the spin at `i` changes by `In γ i`. -/
theorem spin_flip {n : ℕ} {γ : Finset Edge} (hb : γ ⊆ boxEdges n)
    (he : IsEven γ) (S : Finset Site) (i : Site) :
    spin (flip n γ S) i = spin S i + In γ i := by
  rw [flip, spin_symmDiff, spin_Intr hb he]

/-- The flip map is an involution. -/
theorem flip_flip (n : ℕ) (γ : Finset Edge) (S : Finset Site) :
    flip n γ (flip n γ S) = S := by
  simp only [flip]
  rw [symmDiff_symmDiff_cancel_right]

/-- The flip map preserves the configuration space. -/
theorem flip_mem_cfgs {n : ℕ} {γ : Finset Edge} {S : Finset Site}
    (hS : S ∈ cfgs n) : flip n γ S ∈ cfgs n := by
  rw [cfgs, Finset.mem_powerset] at hS ⊢
  intro i hi
  rw [flip, Finset.mem_symmDiff] at hi
  rcases hi with ⟨hiS, -⟩ | ⟨hiI, -⟩
  · exact hS hiS
  · exact Finset.filter_subset _ _ hiI

/-- Flipping the interior of `γ` toggles the disagreement indicator exactly on `γ`
(uses `In_horiz` for horizontal and `In_vert` for vertical edges). -/
theorem disInd_flip {n : ℕ} {γ : Finset Edge} (hb : γ ⊆ boxEdges n)
    (he : IsEven γ) (S : Finset Site) (e : Edge) :
    disInd (flip n γ S) e = disInd S e + (if e ∈ γ then 1 else 0) := by
  have key : ∀ i j : Site, spin (flip n γ S) i + spin (flip n γ S) j
      = (spin S i + spin S j) + (In γ i + In γ j) := fun i j => by
    rw [spin_flip hb he, spin_flip hb he]; ring
  cases e with
  | H a b =>
    show spin (flip n γ S) (a, b) + spin (flip n γ S) (a + 1, b)
        = spin S (a, b) + spin S (a + 1, b) + _
    rw [key, In_horiz]
  | V a b =>
    show spin (flip n γ S) (a, b) + spin (flip n γ S) (a, b + 1)
        = spin S (a, b) + spin S (a, b + 1) + _
    rw [key, In_vert he]

/-- The disagreement set of the flipped configuration is the symmetric difference
with `γ`. -/
theorem Dis_flip {n : ℕ} {γ : Finset Edge} (hb : γ ⊆ boxEdges n)
    (he : IsEven γ) {S : Finset Site} (hS : S ⊆ siteBox n) :
    Dis n (flip n γ S) = symmDiff (Dis n S) γ := by
  have hflip : flip n γ S ⊆ siteBox n :=
    Finset.mem_powerset.mp (flip_mem_cfgs (Finset.mem_powerset.mpr hS))
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  ext e
  rw [mem_Dis_iff hflip, Finset.mem_symmDiff, mem_Dis_iff hS, disInd_flip hb he]
  by_cases hg : e ∈ γ <;>
    rcases zmod2_cases (disInd S e) with h | h <;>
      simp [hg, h, h11, h01]

/-- Erasing a contour contained in the disagreement set lowers the number of
disagreement edges by exactly `|γ|`. -/
theorem card_Dis_flip {n : ℕ} {γ : Finset Edge} (hb : γ ⊆ boxEdges n)
    (he : IsEven γ) {S : Finset Site} (hS : S ⊆ siteBox n)
    (hγS : γ ⊆ Dis n S) :
    (Dis n (flip n γ S)).card + γ.card = (Dis n S).card := by
  have h1 : Dis n (flip n γ S) = Dis n S \ γ := by
    rw [Dis_flip hb he hS]
    ext e
    rw [Finset.mem_symmDiff, Finset.mem_sdiff]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd (hγS h.1) h.2
    · exact Or.inl
  rw [h1, Finset.card_sdiff_add_card_eq_card hγS]

/-- The partition function is positive. -/
theorem Z_pos (n : ℕ) {x : ℝ} (hx : 0 < x) : 0 < Z n x :=
  Finset.sum_pos (fun _ _ => pow_pos hx _)
    ⟨∅, Finset.empty_mem_powerset _⟩

/-- **Peierls' estimate** (Lemma 3.37 of the transcription, eq. (3.34); Lemma
`lem:peierls` of the LaTeX companion): the total weight of the event
`γ ⊆ Dis n S` is at most `x ^ |γ| · Z`.  Stated for arbitrary even `γ`; when
`γ ⊄ boxEdges n` the event is empty and the bound is trivial. -/
theorem evCyc_le (n : ℕ) {x : ℝ} (hx : 0 < x) {γ : Finset Edge}
    (he : IsEven γ) : evCyc n x γ ≤ x ^ γ.card * Z n x := by
  by_cases hb : γ ⊆ boxEdges n
  · set F := (cfgs n).filter (fun S => γ ⊆ Dis n S) with hF
    have key : ∀ S ∈ F, wt n x S = x ^ γ.card * wt n x (flip n γ S) := by
      intro S hSF
      rw [hF, Finset.mem_filter] at hSF
      have hSbox : S ⊆ siteBox n := Finset.mem_powerset.mp hSF.1
      have hc := card_Dis_flip hb he hSbox hSF.2
      rw [wt, wt, ← hc, pow_add, mul_comm]
    have hinj : ∀ a ∈ F, ∀ b ∈ F, flip n γ a = flip n γ b → a = b := by
      intro a _ b _ hab
      have := congrArg (flip n γ) hab
      rwa [flip_flip, flip_flip] at this
    calc evCyc n x γ = ∑ S ∈ F, wt n x S := rfl
      _ = ∑ S ∈ F, x ^ γ.card * wt n x (flip n γ S) := Finset.sum_congr rfl key
      _ = x ^ γ.card * ∑ S ∈ F, wt n x (flip n γ S) := by rw [Finset.mul_sum]
      _ ≤ x ^ γ.card * Z n x := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hx.le _)
        rw [← Finset.sum_image hinj]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => pow_nonneg hx.le _
        intro S' hS'
        simp only [Finset.mem_image] at hS'
        obtain ⟨S, hSF, rfl⟩ := hS'
        exact flip_mem_cfgs (Finset.mem_filter.mp hSF).1
  · have hempty : (cfgs n).filter (fun S => γ ⊆ Dis n S) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro S _ hsub
      exact hb (hsub.trans (Finset.filter_subset _ _))
    rw [evCyc, hempty, Finset.sum_empty]
    exact le_of_lt (mul_pos (pow_pos hx _) (Z_pos n hx))

end Peierls
