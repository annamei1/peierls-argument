import Peierls.Flip
import Peierls.Cycles

/-!
# The Peierls argument: union bound, numerics, and the main theorem

Combining the coverage of the event `σ₀ = -1` by anchored-cycle events
(`Cycles.lean`), the per-cycle Peierls estimate (`Flip.lean`), and the count of
anchored words (`≤ ℓ · 4^(ℓ-1)` for cycles of length `ℓ`), we obtain for
`x = exp (-2β) ≤ exp (-4)`:

`evMinus ≤ (∑_{ℓ ≥ 4} ℓ 4^ℓ x^ℓ) · Z ≤ (∑_{ℓ ≥ 4} (8x)^ℓ) · Z ≤ ((8x)⁴/(1-8x)) · Z ≤ ¼ · Z`,

i.e. `μ⁺_{B(n);β,0}(σ₀ = -1) ≤ ¼` for all `n` and all `β ≥ 2`, whence
`⟨σ₀⟩⁺_{B(n);β,0} ≥ ½` *uniformly in the volume*: the conclusion of the Peierls
argument (Theorem `thm:main` of the LaTeX companion document, with `β₀ = 2`).
-/

namespace Peierls

open Finset

/-- Index set for the union bound: anchored cycle walks of length `ℓ`, encoded by
the anchor position `k < ℓ` and the direction word after the initial `Dir.U`. -/
def idx (ℓ : ℕ) : Finset (ℕ × List Dir) :=
  (Finset.range ℓ ×ˢ words (ℓ - 1)).filter fun p =>
    IsCycleWalk ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2)

/-- Coverage: a configuration with a minus spin at the origin makes some anchored
cycle event happen, with cycle length between `4` and `(boxEdges n).card`. -/
theorem coverage {n : ℕ} {S : Finset Site} (hS : S ∈ cfgs n)
    (h0 : ((0 : ℤ), (0 : ℤ)) ∈ S) :
    ∃ ℓ ∈ Finset.Icc 4 (boxEdges n).card, ∃ p ∈ idx ℓ,
      walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S := by
  have hS' : S ⊆ siteBox n := Finset.mem_powerset.mp hS
  have h1 : In (Dis n S) ((0 : ℤ), (0 : ℤ)) = 1 := by
    rw [← spin_eq_In hS']
    simp [spin, h0]
  obtain ⟨k, w, hcyc, hsub, hlen⟩ := exists_anchored_cycle (isEven_Dis hS') h1
  simp only [List.length_cons] at hlen
  refine ⟨w.length + 1, ?_, (k, w), ?_, hsub⟩
  · rw [Finset.mem_Icc]
    constructor
    · have h4 := four_le_length_of_cycleWalk hcyc
      simpa using h4
    · have hcard := card_walkFinset hcyc.2.1
      simp only [List.length_cons] at hcard
      have hle1 : (walkFinset ((k : ℤ), (-1 : ℤ)) (Dir.U :: w)).card ≤ (Dis n S).card :=
        Finset.card_le_card hsub
      have hle2 : (Dis n S).card ≤ (boxEdges n).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      omega
  · simp only [idx, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨by omega, ?_⟩, hcyc⟩
    rw [mem_words]
    omega

/-- The union bound: the weight of the event `σ₀ = -1` is controlled by the sum
over lengths of (number of anchored words) × (per-cycle estimate). -/
theorem evMinus_le_sum (n : ℕ) {x : ℝ} (hx : 0 < x) :
    evMinus n x ≤
      (∑ ℓ ∈ Finset.Icc 4 (boxEdges n).card, (ℓ : ℝ) * 4 ^ ℓ * x ^ ℓ) * Z n x := by
  have hwt : ∀ S : Finset Site, 0 ≤ wt n x S := fun S => pow_nonneg hx.le _
  have hZnn : (0 : ℝ) ≤ Z n x := (Z_pos n hx).le
  set L := (boxEdges n).card with hL
  set A := (cfgs n).filter (fun S => ((0 : ℤ), (0 : ℤ)) ∈ S) with hA
  -- the pointwise union bound, by `coverage`
  have step1 : ∀ S ∈ A, wt n x S ≤
      ∑ ℓ ∈ Finset.Icc 4 L, ∑ p ∈ idx ℓ,
        (if walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S
          then wt n x S else 0) := by
    intro S hSA
    rw [hA, Finset.mem_filter] at hSA
    obtain ⟨ℓ₀, hℓ₀, p₀, hp₀, hsub⟩ := coverage hSA.1 hSA.2
    have hnn : ∀ p : ℕ × List Dir,
        (0 : ℝ) ≤ (if walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S
          then wt n x S else 0) := by
      intro p
      split
      · exact hwt S
      · exact le_rfl
    calc wt n x S
        = (if walkFinset ((p₀.1 : ℤ), (-1 : ℤ)) (Dir.U :: p₀.2) ⊆ Dis n S
            then wt n x S else 0) := by rw [if_pos hsub]
      _ ≤ ∑ p ∈ idx ℓ₀,
            (if walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S
              then wt n x S else 0) :=
          Finset.single_le_sum (fun p _ => hnn p) hp₀
      _ ≤ ∑ ℓ ∈ Finset.Icc 4 L, ∑ p ∈ idx ℓ,
            (if walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S
              then wt n x S else 0) :=
          Finset.single_le_sum
            (fun ℓ _ => Finset.sum_nonneg fun p _ => hnn p) hℓ₀
  -- the per-(length, word) estimate, by `evCyc_le` and the word count
  have inner : ∀ ℓ ∈ Finset.Icc 4 L,
      (∑ p ∈ idx ℓ, ∑ S ∈ A,
        (if walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S
          then wt n x S else 0))
        ≤ ((ℓ : ℝ) * 4 ^ ℓ * x ^ ℓ) * Z n x := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    have hterm : ∀ p ∈ idx ℓ,
        (∑ S ∈ A, if walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S
          then wt n x S else 0)
          ≤ x ^ ℓ * Z n x := by
      intro p hp
      simp only [idx, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      obtain ⟨⟨hp1, hp2⟩, hcyc⟩ := hp
      have hcard : (walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2)).card = ℓ := by
        rw [card_walkFinset hcyc.2.1, List.length_cons, mem_words.mp hp2]
        omega
      calc (∑ S ∈ A, if walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S
              then wt n x S else 0)
          = ∑ S ∈ A.filter
              (fun S => walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S),
              wt n x S := (Finset.sum_filter _ _).symm
        _ ≤ ∑ S ∈ (cfgs n).filter
              (fun S => walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S),
              wt n x S :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
              (fun S _ _ => hwt S)
        _ = evCyc n x (walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2)) := rfl
        _ ≤ x ^ (walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2)).card * Z n x :=
            evCyc_le n hx (isEven_walkFinset hcyc)
        _ = x ^ ℓ * Z n x := by rw [hcard]
    have hcardidx : ((idx ℓ).card : ℝ) ≤ (ℓ : ℝ) * 4 ^ ℓ := by
      have h1 : (idx ℓ).card ≤ ℓ * 4 ^ (ℓ - 1) := by
        have h := Finset.card_filter_le (Finset.range ℓ ×ˢ words (ℓ - 1))
          (fun p => IsCycleWalk ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2))
        simpa [idx, Finset.card_product, Finset.card_range, card_words] using h
      have h4 : (4 : ℝ) ^ (ℓ - 1) ≤ 4 ^ ℓ :=
        pow_le_pow_right₀ (by norm_num) (Nat.sub_le ℓ 1)
      calc ((idx ℓ).card : ℝ)
          ≤ ((ℓ * 4 ^ (ℓ - 1) : ℕ) : ℝ) := Nat.cast_le.mpr h1
        _ = (ℓ : ℝ) * 4 ^ (ℓ - 1) := by push_cast; ring
        _ ≤ (ℓ : ℝ) * 4 ^ ℓ := mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg ℓ)
    calc (∑ p ∈ idx ℓ, ∑ S ∈ A,
          (if walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S
            then wt n x S else 0))
        ≤ ∑ _p ∈ idx ℓ, x ^ ℓ * Z n x := Finset.sum_le_sum hterm
      _ = ((idx ℓ).card : ℝ) * (x ^ ℓ * Z n x) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((ℓ : ℝ) * 4 ^ ℓ) * (x ^ ℓ * Z n x) :=
          mul_le_mul_of_nonneg_right hcardidx
            (mul_nonneg (pow_nonneg hx.le ℓ) hZnn)
      _ = ((ℓ : ℝ) * 4 ^ ℓ * x ^ ℓ) * Z n x := by ring
  calc evMinus n x = ∑ S ∈ A, wt n x S := rfl
    _ ≤ ∑ S ∈ A, ∑ ℓ ∈ Finset.Icc 4 L, ∑ p ∈ idx ℓ,
          (if walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S
            then wt n x S else 0) := Finset.sum_le_sum step1
    _ = ∑ ℓ ∈ Finset.Icc 4 L, ∑ S ∈ A, ∑ p ∈ idx ℓ,
          (if walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S
            then wt n x S else 0) := Finset.sum_comm
    _ = ∑ ℓ ∈ Finset.Icc 4 L, ∑ p ∈ idx ℓ, ∑ S ∈ A,
          (if walkFinset ((p.1 : ℤ), (-1 : ℤ)) (Dir.U :: p.2) ⊆ Dis n S
            then wt n x S else 0) :=
        Finset.sum_congr rfl fun ℓ _ => Finset.sum_comm
    _ ≤ ∑ ℓ ∈ Finset.Icc 4 L, ((ℓ : ℝ) * 4 ^ ℓ * x ^ ℓ) * Z n x :=
        Finset.sum_le_sum inner
    _ = (∑ ℓ ∈ Finset.Icc 4 L, (ℓ : ℝ) * 4 ^ ℓ * x ^ ℓ) * Z n x :=
        (Finset.sum_mul _ _ _).symm

/-- Numerical input: `54 ≤ e⁴`. -/
theorem le_exp_four : (54 : ℝ) ≤ Real.exp 4 := by
  have h1 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 4
  have h2 : Real.exp 1 ^ 4 = Real.exp 4 := by
    rw [Real.exp_one_pow]
    norm_num
  calc (54 : ℝ) ≤ (2.7182818283 : ℝ) ^ 4 := by norm_num
    _ ≤ Real.exp 1 ^ 4 := h1
    _ = Real.exp 4 := h2

/-- The series bound: for `0 < x ≤ e⁻⁴` and any `L`,
`∑_{ℓ=4}^{L} ℓ 4^ℓ x^ℓ ≤ ¼` (via `ℓ 4^ℓ ≤ 8^ℓ` and a geometric tail). -/
theorem series_le_quarter {x : ℝ} (hx0 : 0 < x) (hx : x ≤ Real.exp (-4)) (L : ℕ) :
    (∑ ℓ ∈ Finset.Icc 4 L, (ℓ : ℝ) * 4 ^ ℓ * x ^ ℓ) ≤ 1 / 4 := by
  have h54 : x ≤ 1 / 54 := by
    have h2 : (Real.exp 4)⁻¹ ≤ (54 : ℝ)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos 4) (by norm_num)).mpr le_exp_four
    calc x ≤ Real.exp (-4) := hx
      _ = (Real.exp 4)⁻¹ := Real.exp_neg 4
      _ ≤ (54 : ℝ)⁻¹ := h2
      _ = 1 / 54 := by norm_num
  set y := 8 * x with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 4 / 27 := by rw [hy]; linarith
  -- pointwise: `ℓ 4^ℓ x^ℓ ≤ (8x)^ℓ`
  have hsum1 : (∑ ℓ ∈ Finset.Icc 4 L, (ℓ : ℝ) * 4 ^ ℓ * x ^ ℓ)
      ≤ ∑ ℓ ∈ Finset.Icc 4 L, y ^ ℓ := by
    apply Finset.sum_le_sum
    intro ℓ _
    have h2 : (ℓ : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast ℓ.lt_two_pow_self.le
    calc (ℓ : ℝ) * 4 ^ ℓ * x ^ ℓ
        = (ℓ : ℝ) * (4 ^ ℓ * x ^ ℓ) := by ring
      _ ≤ (2 : ℝ) ^ ℓ * (4 ^ ℓ * x ^ ℓ) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = y ^ ℓ := by
          rw [hy, show (8 : ℝ) * x = 2 * 4 * x from by ring, mul_pow, mul_pow]
          ring
  -- geometric tail: `∑_{ℓ=4}^{L} y^ℓ ≤ ¼` for `0 < y ≤ 4/27`
  have hsum2 : (∑ ℓ ∈ Finset.Icc 4 L, y ^ ℓ) ≤ 1 / 4 := by
    rcases Nat.lt_or_ge L 4 with hL | hL
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      norm_num
    · have hy_ne : y ≠ 1 := by
        intro h
        rw [h] at hy1
        norm_num at hy1
      have hIcc : Finset.Icc 4 L = Finset.Ico 4 (L + 1) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hIcc, geom_sum_Ico' hy_ne (by omega)]
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - y)]
      have h4 : y ^ 4 ≤ (4 / 27 : ℝ) ^ 4 := pow_le_pow_left₀ hy0.le hy1 4
      have h5 : (0 : ℝ) ≤ y ^ (L + 1) := by positivity
      have h6 : ((4 : ℝ) / 27) ^ 4 ≤ 1 / 1000 := by norm_num
      linarith
  linarith

/-- **Uniform finite-volume Peierls bound**: for `0 < x ≤ e⁻⁴`,
`μ(σ₀ = -1) ≤ ¼` in every volume. -/
theorem evMinus_le_quarter (n : ℕ) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ Real.exp (-4)) : evMinus n x ≤ 1 / 4 * Z n x :=
  calc evMinus n x
      ≤ (∑ ℓ ∈ Finset.Icc 4 (boxEdges n).card, (ℓ : ℝ) * 4 ^ ℓ * x ^ ℓ) * Z n x :=
        evMinus_le_sum n hx0
    _ ≤ 1 / 4 * Z n x :=
        mul_le_mul_of_nonneg_right (series_le_quarter hx0 hx _) (Z_pos n hx0).le

/-! ## From weights to the Gibbs form -/

/-- The expectation of `σ₀` in terms of the minus-event weight. -/
theorem sum_sigma_eq (n : ℕ) (x : ℝ) :
    ∑ S ∈ cfgs n, sigma S ((0 : ℤ), (0 : ℤ)) * wt n x S = Z n x - 2 * evMinus n x := by
  unfold Z evMinus
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : ((0 : ℤ), (0 : ℤ)) ∈ S
  · simp only [sigma, if_pos h]
    ring
  · simp only [sigma, if_neg h]
    ring

/-- The product of the spins at the two ends of an edge, in terms of the
disagreement indicator. -/
theorem sigma_mul_sigma (S : Finset Site) (e : Edge) :
    sigma S e.ends.1 * sigma S e.ends.2 =
      1 - 2 * (if disInd S e = 1 then (1 : ℝ) else 0) := by
  unfold sigma disInd spin
  by_cases h1 : e.ends.1 ∈ S <;> by_cases h2 : e.ends.2 ∈ S
  · simp only [if_pos h1, if_pos h2]
    rw [if_neg (by decide : ¬((1 : ZMod 2) + 1 = 1))]
    norm_num
  · simp only [if_pos h1, if_neg h2]
    rw [if_pos (by decide : ((1 : ZMod 2) + 0 = 1))]
    norm_num
  · simp only [if_neg h1, if_pos h2]
    rw [if_pos (by decide : ((0 : ZMod 2) + 1 = 1))]
    norm_num
  · simp only [if_neg h1, if_neg h2]
    rw [if_neg (by decide : ¬((0 : ZMod 2) + 0 = 1))]
    norm_num

/-- The interaction sum in terms of the disagreement count. -/
theorem sum_sigma_sigma (n : ℕ) (S : Finset Site) :
    ∑ e ∈ boxEdges n, sigma S e.ends.1 * sigma S e.ends.2 =
      ((boxEdges n).card : ℝ) - 2 * ((Dis n S).card : ℝ) := by
  rw [Finset.sum_congr rfl fun e _ => sigma_mul_sigma S e]
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.sum_boole]
  simp [Dis]

/-- The Boltzmann factor in terms of the disagreement count: with
`x = exp (-2β)`, `exp (-H(S)) = exp (β |boxEdges n|) · x ^ |Dis n S|`. -/
theorem exp_neg_ham_eq (n : ℕ) (β : ℝ) (S : Finset Site) :
    Real.exp (-ham n β S) =
      Real.exp (β * (boxEdges n).card) * Real.exp (-2 * β) ^ (Dis n S).card := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  unfold ham
  rw [sum_sigma_sigma]
  ring

/-- The Gibbs expectation of `σ₀` equals its expectation under the
`x`-weights, `x = exp (-2β)`. -/
theorem gibbsSigma0_eq (n : ℕ) (β : ℝ) :
    gibbsSigma0 n β =
      (∑ S ∈ cfgs n, sigma S ((0 : ℤ), (0 : ℤ)) * wt n (Real.exp (-2 * β)) S) /
        Z n (Real.exp (-2 * β)) := by
  have hc : Real.exp (β * (boxEdges n).card) ≠ 0 := Real.exp_ne_zero _
  have hnum : (∑ S ∈ cfgs n, sigma S ((0 : ℤ), (0 : ℤ)) * Real.exp (-ham n β S)) =
      Real.exp (β * (boxEdges n).card) *
        ∑ S ∈ cfgs n, sigma S ((0 : ℤ), (0 : ℤ)) * wt n (Real.exp (-2 * β)) S := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [exp_neg_ham_eq]
    unfold wt
    ring
  have hden : (∑ S ∈ cfgs n, Real.exp (-ham n β S)) =
      Real.exp (β * (boxEdges n).card) * Z n (Real.exp (-2 * β)) := by
    unfold Z wt
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun S _ => exp_neg_ham_eq n β S
  unfold gibbsSigma0
  rw [hnum, hden, mul_div_mul_left _ _ hc]

/-- **The Peierls argument** (the content of Lemmas 3.37–3.38 of the
transcription and of Theorem `thm:main` of the LaTeX companion document, with
`β₀ = 2`): at zero magnetic field, in any box `B(n)` with `+` boundary
condition, for every inverse temperature `β ≥ 2` the expected spin at the
origin is at least `½` — *uniformly in the volume*.  Hence the spontaneous
magnetization persists in the thermodynamic limit and the `+` and `-` states
differ for all `β ≥ 2`: a first-order phase transition. -/
theorem peierls_argument (n : ℕ) {β : ℝ} (hβ : 2 ≤ β) :
    1 / 2 ≤ gibbsSigma0 n β := by
  have hx0 : 0 < Real.exp (-2 * β) := Real.exp_pos _
  have hxle : Real.exp (-2 * β) ≤ Real.exp (-4) :=
    Real.exp_le_exp.mpr (by linarith)
  have hZ : 0 < Z n (Real.exp (-2 * β)) := Z_pos n hx0
  have hq : evMinus n (Real.exp (-2 * β)) ≤ 1 / 4 * Z n (Real.exp (-2 * β)) :=
    evMinus_le_quarter n hx0 hxle
  rw [gibbsSigma0_eq, sum_sigma_eq, le_div_iff₀ hZ]
  linarith

end Peierls
