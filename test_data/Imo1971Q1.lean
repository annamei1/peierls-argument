import Mathlib

/-!
# IMO 1971, Problem 1

Prove that the following assertion is true for `n = 3` and `n = 5`, and that
it is false for every other natural number `n > 2`: if `a₁, …, aₙ` are
arbitrary real numbers, then `∑ i, ∏_{j ≠ i} (aᵢ - aⱼ) ≥ 0`.

## Formalization

For `a : Fin n → ℝ` set `E n a = ∑ i, ∏ j ∈ univ.erase i, (a i - a j)`.
The main theorem `Imo1971Q1.nonneg_iff` states that, for `n > 2`,

`(∀ a, 0 ≤ E n a) ↔ n = 3 ∨ n = 5`.

## Proof

*Positive cases.* `E` is symmetric under permutation of the variables
(`E_comp_perm`), so we may sort the tuple increasingly (`Tuple.sort`).
For `n = 3` the expression equals `½ ∑ (aᵢ - aⱼ)²`, handled by `nlinarith`.
For sorted `b 0 ≤ b 1 ≤ b 2 ≤ b 3 ≤ b 4` the five terms are grouped as in the
classical solution: terms 0 and 1 combine to
`(b 1 - b 0) * ((b 2 - b 0)(b 3 - b 0)(b 4 - b 0) - (b 2 - b 1)(b 3 - b 1)(b 4 - b 1)) ≥ 0`,
term 2 is a product of two nonnegative and two nonpositive factors, and terms
3 and 4 combine symmetrically to terms 0 and 1.

*Negative cases.* For even `n ≥ 4` take `a = (-1, 0, …, 0)`; all terms but
the first vanish and `E = (-1)^(n-1) = -1`. For odd `n ≥ 7` take
`a = (0, -1, -1, -1, 1, …, 1)`; every term whose value is repeated vanishes
and the remaining term is `(0-(-1))³ (0-1)^(n-4) = (-1)^(n-4) = -1`.
-/

namespace Imo1971Q1

open Finset

/-- The expression of the problem: `E n a = ∑ i, ∏_{j ≠ i} (a i - a j)`. -/
def E (n : ℕ) (a : Fin n → ℝ) : ℝ := ∑ i, ∏ j ∈ univ.erase i, (a i - a j)

/-- `E` is invariant under permutation of the variables. -/
lemma E_comp_perm {n : ℕ} (a : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    E n (a ∘ σ) = E n a := by
  unfold E
  rw [← Equiv.sum_comp σ fun i => ∏ j ∈ univ.erase i, (a i - a j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : univ.erase (σ i) = (univ.erase i).map σ.toEmbedding := by
    rw [Finset.map_erase, Finset.map_univ_equiv, Equiv.coe_toEmbedding]
  rw [h, Finset.prod_map]
  rfl

/-- The assertion holds for `n = 3`. -/
theorem holds_three (a : Fin 3 → ℝ) : 0 ≤ E 3 a := by
  have h0 : univ.erase (0 : Fin 3) = {1, 2} := by decide
  have h1 : univ.erase (1 : Fin 3) = {0, 2} := by decide
  have h2 : univ.erase (2 : Fin 3) = {0, 1} := by decide
  unfold E
  rw [Fin.sum_univ_three, h0, h1, h2]
  simp +decide only [Finset.prod_insert, Finset.mem_singleton,
    Finset.prod_singleton]
  nlinarith [sq_nonneg (a 0 - a 1), sq_nonneg (a 1 - a 2), sq_nonneg (a 0 - a 2)]

/-- If `0 ≤ vᵢ ≤ uᵢ` componentwise then `v₁v₂v₃ ≤ u₁u₂u₃`. -/
private lemma triple_mono {u1 u2 u3 v1 v2 v3 : ℝ} (h1 : 0 ≤ v1) (h2 : 0 ≤ v2)
    (h3 : 0 ≤ v3) (e1 : v1 ≤ u1) (e2 : v2 ≤ u2) (e3 : v3 ≤ u3) :
    v1 * v2 * v3 ≤ u1 * u2 * u3 := by
  have h12 : v1 * v2 ≤ u1 * u2 := mul_le_mul e1 e2 h2 (h1.trans e1)
  exact mul_le_mul h12 e3 h3 (mul_nonneg (h1.trans e1) (h2.trans e2))

/-- The case `n = 5` for an increasingly sorted tuple. -/
lemma holds_five_sorted (b : Fin 5 → ℝ) (h01 : b 0 ≤ b 1) (h12 : b 1 ≤ b 2)
    (h23 : b 2 ≤ b 3) (h34 : b 3 ≤ b 4) : 0 ≤ E 5 b := by
  -- terms 0 and 1 of the sum combine to a nonnegative quantity
  have g1 : 0 ≤ (b 1 - b 0) *
      ((b 2 - b 0) * (b 3 - b 0) * (b 4 - b 0) -
        (b 2 - b 1) * (b 3 - b 1) * (b 4 - b 1)) := by
    have key : (b 2 - b 1) * (b 3 - b 1) * (b 4 - b 1) ≤
        (b 2 - b 0) * (b 3 - b 0) * (b 4 - b 0) :=
      triple_mono (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
    exact mul_nonneg (by linarith) (sub_nonneg.mpr key)
  -- term 2 is a product of two nonnegative and two nonpositive factors
  have g2 : 0 ≤ (b 2 - b 0) * (b 2 - b 1) * (b 3 - b 2) * (b 4 - b 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith))
      (by linarith)) (by linarith)
  -- terms 3 and 4 combine symmetrically to terms 0 and 1
  have g3 : 0 ≤ (b 4 - b 3) *
      ((b 4 - b 0) * (b 4 - b 1) * (b 4 - b 2) -
        (b 3 - b 0) * (b 3 - b 1) * (b 3 - b 2)) := by
    have key : (b 3 - b 0) * (b 3 - b 1) * (b 3 - b 2) ≤
        (b 4 - b 0) * (b 4 - b 1) * (b 4 - b 2) :=
      triple_mono (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
    exact mul_nonneg (by linarith) (sub_nonneg.mpr key)
  have e0 : univ.erase (0 : Fin 5) = {1, 2, 3, 4} := by decide
  have e1 : univ.erase (1 : Fin 5) = {0, 2, 3, 4} := by decide
  have e2 : univ.erase (2 : Fin 5) = {0, 1, 3, 4} := by decide
  have e3 : univ.erase (3 : Fin 5) = {0, 1, 2, 4} := by decide
  have e4 : univ.erase (4 : Fin 5) = {0, 1, 2, 3} := by decide
  unfold E
  rw [Fin.sum_univ_five, e0, e1, e2, e3, e4]
  simp +decide only [Finset.prod_insert, Finset.mem_insert,
    Finset.mem_singleton, Finset.prod_singleton]
  nlinarith [g1, g2, g3]

/-- The assertion holds for `n = 5`. -/
theorem holds_five (a : Fin 5 → ℝ) : 0 ≤ E 5 a := by
  have hm : Monotone (a ∘ Tuple.sort a) := Tuple.monotone_sort a
  have h := holds_five_sorted (a ∘ Tuple.sort a)
    (hm (by decide)) (hm (by decide)) (hm (by decide)) (hm (by decide))
  rwa [E_comp_perm] at h

/-- The assertion fails for every `n > 2` other than `3` and `5`. -/
theorem not_holds {n : ℕ} (hn : 2 < n) (h3 : n ≠ 3) (h5 : n ≠ 5) :
    ∃ a : Fin n → ℝ, E n a < 0 := by
  rcases Nat.even_or_odd n with he | ho
  · -- even case, `n ≥ 4`: take `a = (-1, 0, …, 0)`
    set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
    set a : Fin n → ℝ := fun j => if j = i₀ then (-1 : ℝ) else 0 with ha
    refine ⟨a, ?_⟩
    have hE : E n a = (-1 : ℝ) ^ (n - 1) := by
      unfold E
      rw [Finset.sum_eq_single i₀]
      · have hconst : ∀ j ∈ univ.erase i₀, a i₀ - a j = -1 := by
          intro j hj
          have hj0 : j ≠ i₀ := (Finset.mem_erase.mp hj).1
          simp [ha, hj0]
        rw [Finset.prod_congr rfl hconst, Finset.prod_const,
          Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
          Fintype.card_fin]
      · intro i _ hi
        -- a second vertex with value `0` produces a zero factor
        by_cases hc : i = ⟨1, by omega⟩
        · refine Finset.prod_eq_zero (i := (⟨2, by omega⟩ : Fin n))
            (Finset.mem_erase.mpr ⟨?_, mem_univ _⟩) ?_
          · rw [hc]
            intro hcon
            rw [Fin.ext_iff] at hcon
            simp at hcon
          · have h2 : (⟨2, by omega⟩ : Fin n) ≠ i₀ := by
              rw [hi₀]
              intro hcon
              rw [Fin.ext_iff] at hcon
              simp at hcon
            simp [ha, hi, h2]
        · refine Finset.prod_eq_zero (i := (⟨1, by omega⟩ : Fin n))
            (Finset.mem_erase.mpr ⟨?_, mem_univ _⟩) ?_
          · exact fun hcon => hc hcon.symm
          · have h1 : (⟨1, by omega⟩ : Fin n) ≠ i₀ := by
              rw [hi₀]
              intro hcon
              rw [Fin.ext_iff] at hcon
              simp at hcon
            simp [ha, hi, h1]
      · intro h
        exact absurd (mem_univ i₀) h
    rw [hE]
    obtain ⟨t, ht⟩ := he
    have hodd : Odd (n - 1) := ⟨t - 1, by omega⟩
    rw [hodd.neg_one_pow]
    norm_num
  · -- odd case, `n ≥ 7`: take `a = (0, -1, -1, -1, 1, …, 1)`
    have hn7 : 7 ≤ n := by
      obtain ⟨t, ht⟩ := ho
      omega
    set a : Fin n → ℝ := fun j =>
      if j.val = 0 then 0 else if j.val ≤ 3 then -1 else 1 with ha
    refine ⟨a, ?_⟩
    set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
    have hE : E n a = (-1 : ℝ) ^ (n - 4) := by
      unfold E
      rw [Finset.sum_eq_single i₀]
      · -- the surviving term: `∏_{j ≠ 0} (0 - a j) = (-1)^(n-4)`
        have hcongr : ∀ j ∈ univ.erase i₀,
            a i₀ - a j = if 4 ≤ j.val then (-1 : ℝ) else 1 := by
          intro j hj
          have hj0 : j.val ≠ 0 := by
            have h' := (Finset.mem_erase.mp hj).1
            simpa [hi₀, Fin.ext_iff] using h'
          rcases le_or_gt j.val 3 with hle | hgt
          · have h4 : ¬ 4 ≤ j.val := by omega
            simp [ha, hi₀, hj0, hle, h4]
          · have h4 : 4 ≤ j.val := by omega
            have h3' : ¬ j.val ≤ 3 := by omega
            simp [ha, hi₀, hj0, h3', h4]
        have hcard : (univ.filter fun j : Fin n => 4 ≤ j.val).card = n - 4 := by
          have hneg : (univ.filter fun j : Fin n => ¬ 4 ≤ j.val) =
              (Finset.range 4).attachFin
                (fun m hm => lt_of_lt_of_le (Finset.mem_range.mp hm)
                  (by omega)) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_attachFin, Finset.mem_range]
            omega
          have hsum := Finset.card_filter_add_card_filter_not
            (s := (univ : Finset (Fin n))) (p := fun j : Fin n => 4 ≤ j.val)
          rw [hneg, Finset.card_attachFin, Finset.card_range,
            Finset.card_univ, Fintype.card_fin] at hsum
          omega
        rw [Finset.prod_congr rfl hcongr,
          Finset.prod_erase (f := fun j : Fin n => if 4 ≤ j.val then (-1 : ℝ) else 1)
            univ (by simp [hi₀]),
          Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
          hcard]
      · intro i _ hi
        -- another vertex with the same value produces a zero factor
        have hival : i.val ≠ 0 := by
          simpa [hi₀, Fin.ext_iff] using hi
        rcases le_or_gt i.val 3 with hle | hgt
        · by_cases hc : i.val = 1
          · refine Finset.prod_eq_zero (i := (⟨2, by omega⟩ : Fin n))
              (Finset.mem_erase.mpr ⟨?_, mem_univ _⟩) ?_
            · intro hcon
              rw [Fin.ext_iff] at hcon
              simp at hcon
              omega
            · simp [ha, hc]
          · refine Finset.prod_eq_zero (i := (⟨1, by omega⟩ : Fin n))
              (Finset.mem_erase.mpr ⟨?_, mem_univ _⟩) ?_
            · intro hcon
              rw [Fin.ext_iff] at hcon
              simp at hcon
              omega
            · simp [ha, hival, hle]
        · have h3' : ¬ i.val ≤ 3 := by omega
          by_cases hc : i.val = 4
          · refine Finset.prod_eq_zero (i := (⟨5, by omega⟩ : Fin n))
              (Finset.mem_erase.mpr ⟨?_, mem_univ _⟩) ?_
            · intro hcon
              rw [Fin.ext_iff] at hcon
              simp at hcon
              omega
            · simp [ha, hival, h3']
          · refine Finset.prod_eq_zero (i := (⟨4, by omega⟩ : Fin n))
              (Finset.mem_erase.mpr ⟨?_, mem_univ _⟩) ?_
            · intro hcon
              rw [Fin.ext_iff] at hcon
              simp at hcon
              omega
            · simp [ha, hival, h3']
      · intro h
        exact absurd (mem_univ i₀) h
    rw [hE]
    obtain ⟨t, ht⟩ := ho
    have hodd : Odd (n - 4) := ⟨t - 2, by omega⟩
    rw [hodd.neg_one_pow]
    norm_num

/-- **IMO 1971, Problem 1.** For `n > 2`, the assertion
"for all real `a₁, …, aₙ` one has `∑ i, ∏_{j ≠ i} (aᵢ - aⱼ) ≥ 0`" holds
if and only if `n = 3` or `n = 5`. -/
theorem nonneg_iff (n : ℕ) (hn : 2 < n) :
    (∀ a : Fin n → ℝ, 0 ≤ E n a) ↔ n = 3 ∨ n = 5 := by
  constructor
  · intro h
    by_contra hc
    simp only [not_or] at hc
    obtain ⟨a, hA⟩ := not_holds hn hc.1 hc.2
    exact absurd (h a) (by linarith)
  · rintro (rfl | rfl)
    · exact holds_three
    · exact holds_five

end Imo1971Q1
