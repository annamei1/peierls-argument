import Mathlib

/-!
# IMO 1994, Problem 3

For any positive integer `k`, let `f k` be the number of elements in the set
`{k+1, k+2, …, 2k}` whose base-2 representation has precisely three `1`s.

* (a) Prove that, for each positive integer `m`, there exists at least one
  positive integer `k` such that `f k = m`.
* (b) Determine all positive integers `m` for which there exists exactly one
  `k` with `f k = m`.  (Answer: `m = C(n,2) + 1` for some `n ≥ 2`.)

## Formalization

`ones n` is the number of `1`s in `Nat.digits 2 n`, and
`f k = #{n ∈ Ioc k (2k) | ones n = 3}`.  The two parts are
`Imo1994Q3.part_a` and `Imo1994Q3.part_b`.

## Proof

Everything rests on the step identity (`f_succ`): passing from `Ioc k (2k)`
to `Ioc (k+1) (2k+2)` removes `k+1` and adds `2k+1` and `2k+2`, and
`2k+2 = 2(k+1)` has the same number of binary ones as `k+1`, so

`f (k+1) = f k + (if ones (2k+1) = 3 then 1 else 0)`.

Hence `f` is nondecreasing with steps `0` or `1`; since `f 1 = 0` and
`f (2^n) = C(n,2)` (the numbers with three ones in `(2^n, 2^(n+1)]` are
exactly `2^n + 2^a + 2^b` with `b < a < n`), `f` is unbounded and attains
every positive integer (part (a), a discrete intermediate value argument).

For part (b), `m` is attained exactly once iff both neighbours of the
witness `k` jump, i.e. both `2k-1` and `2k+1` have three ones, i.e.
`ones (k-1) = ones k = 2`.  Writing `k-1 = 2^a + 2^b` (`b < a`), the
condition `ones k = 2` forces `b = 0` and `a ≥ 2`, so `k = 2^a + 2`; and
`f (2^a + 2) = C(a,2) + 1` by direct computation from the step identity.
-/

namespace Imo1994Q3

open Finset

/-! ### Counting binary ones -/

/-- The number of `1`s in the binary representation of `n`. -/
def ones (n : ℕ) : ℕ := (Nat.digits 2 n).count 1

@[simp] lemma ones_zero : ones 0 = 0 := by simp [ones]

lemma ones_two_mul {n : ℕ} (hn : 0 < n) : ones (2 * n) = ones n := by
  unfold ones
  rw [Nat.digits_def' (b := 2) (by norm_num) (by omega)]
  have h1 : 2 * n % 2 = 0 := by omega
  have h2 : 2 * n / 2 = n := by omega
  rw [h1, h2]
  simp

lemma ones_two_mul_add_one (n : ℕ) : ones (2 * n + 1) = ones n + 1 := by
  unfold ones
  rw [Nat.digits_def' (b := 2) (by norm_num) (by omega)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]
  simp

lemma ones_one : ones 1 = 1 := by
  simpa using ones_two_mul_add_one 0

lemma ones_two_pow (a : ℕ) : ones (2 ^ a) = 1 := by
  induction a with
  | zero => simpa using ones_one
  | succ a ih =>
    rw [show 2 ^ (a + 1) = 2 * 2 ^ a by ring, ones_two_mul (by positivity)]
    exact ih

/-- Adding a two-power above `m` adds one binary `1`. -/
lemma ones_two_pow_add {a m : ℕ} (hm : m < 2 ^ a) :
    ones (2 ^ a + m) = ones m + 1 := by
  induction a generalizing m with
  | zero =>
    have h0 : m = 0 := by simpa using hm
    subst h0
    simpa using ones_one
  | succ a ih =>
    have hpow : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · subst ht
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · simpa using ones_two_pow (a + 1)
      · rw [show 2 ^ (a + 1) + (t + t) = 2 * (2 ^ a + t) by ring,
          ones_two_mul (by positivity), ih (m := t) (by omega),
          show t + t = 2 * t by ring, ones_two_mul ht0]
    · subst ht
      rw [show 2 ^ (a + 1) + (2 * t + 1) = 2 * (2 ^ a + t) + 1 by ring,
        ones_two_mul_add_one, ih (m := t) (by omega), ones_two_mul_add_one]

/-! ### Structure of numbers with few binary ones -/

lemma eq_zero_of_ones_eq_zero : ∀ n : ℕ, ones n = 0 → n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    rcases Nat.even_or_odd n with ⟨t, ht⟩ | ⟨t, ht⟩
    · have ht0 : 0 < t := by omega
      rw [show n = 2 * t by omega, ones_two_mul ht0] at h
      have := ih t (by omega) h
      omega
    · rw [show n = 2 * t + 1 by omega, ones_two_mul_add_one] at h
      omega

lemma exists_pow_of_ones_eq_one : ∀ n : ℕ, ones n = 1 → ∃ a, n = 2 ^ a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at h
    rcases Nat.even_or_odd n with ⟨t, ht⟩ | ⟨t, ht⟩
    · have ht0 : 0 < t := by omega
      have h2 : n = 2 * t := by omega
      rw [h2, ones_two_mul ht0] at h
      obtain ⟨a, ha⟩ := ih t (by omega) h
      exact ⟨a + 1, by rw [h2, ha]; ring⟩
    · have h2 : n = 2 * t + 1 := by omega
      rw [h2, ones_two_mul_add_one] at h
      have h0 := eq_zero_of_ones_eq_zero t (by omega)
      exact ⟨0, by omega⟩

lemma exists_pair_of_ones_eq_two :
    ∀ n : ℕ, ones n = 2 → ∃ a b, b < a ∧ n = 2 ^ a + 2 ^ b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at h
    rcases Nat.even_or_odd n with ⟨t, ht⟩ | ⟨t, ht⟩
    · have ht0 : 0 < t := by omega
      have h2 : n = 2 * t := by omega
      rw [h2, ones_two_mul ht0] at h
      obtain ⟨a, b, hba, hab⟩ := ih t (by omega) h
      exact ⟨a + 1, b + 1, by omega, by rw [h2, hab]; ring⟩
    · have h2 : n = 2 * t + 1 := by omega
      rw [h2, ones_two_mul_add_one] at h
      obtain ⟨a, ha⟩ := exists_pow_of_ones_eq_one t (by omega)
      exact ⟨a + 1, 0, by omega, by rw [h2, ha]; ring⟩

/-! ### Two-power arithmetic helpers -/

private lemma one_le_two_pow {n : ℕ} : 1 ≤ 2 ^ n := by
  simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.zero_le n)

private lemma two_pow_lt_two_pow {a b : ℕ} (h : a < b) : 2 ^ a < 2 ^ b := by
  have h1 : 2 ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
  have h3 : 0 < 2 ^ a := by positivity
  omega

private lemma lt_of_two_pow_lt {a b : ℕ} (h : 2 ^ a < 2 ^ b) : a < b := by
  by_contra hc
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show b ≤ a by omega)
  omega

private lemma two_pow_pair_inj {a b c d : ℕ} (hba : b < a) (hdc : d < c)
    (h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d) : a = c ∧ b = d := by
  have hac : a = c := by
    by_contra hne
    rcases Nat.lt_or_ge a c with hlt | hge
    · have h1 : 2 ^ (a + 1) ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ b < 2 ^ a := two_pow_lt_two_pow hba
      have h3 : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
      have h4 : 0 < 2 ^ d := by positivity
      omega
    · have hlt : c < a := by omega
      have h1 : 2 ^ (c + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ d < 2 ^ c := two_pow_lt_two_pow hdc
      have h3 : 2 ^ (c + 1) = 2 * 2 ^ c := by ring
      have h4 : 0 < 2 ^ b := by positivity
      omega
  subst hac
  have hbd : (2 : ℕ) ^ b = 2 ^ d := by omega
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2) hbd⟩

/-- Two consecutive integers both having exactly two binary ones must be
`2^a + 1` and `2^a + 2` with `a ≥ 2`. -/
lemma consecutive_ones_two {t : ℕ} (h1 : ones t = 2) (h2 : ones (t + 1) = 2) :
    ∃ a, 2 ≤ a ∧ t = 2 ^ a + 1 := by
  obtain ⟨a, b, hba, rfl⟩ := exists_pair_of_ones_eq_two t h1
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · refine ⟨a, ?_, by norm_num⟩
    by_contra hc
    have ha1 : a = 1 := by omega
    subst ha1
    rw [show 2 ^ 1 + 2 ^ 0 + 1 = 2 ^ 2 by norm_num, ones_two_pow] at h2
    omega
  · exfalso
    have ha2 : 2 ≤ a := by omega
    have key : 2 ^ b + 1 < 2 ^ a := by
      have e1 : 2 ^ b ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e2 : 2 * 2 ^ (a - 1) = 2 ^ a := by
        rw [← pow_succ']
        congr 1
        omega
      have e3 : 2 ≤ 2 ^ (a - 1) := by
        calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hb1 : 1 < 2 ^ b := by
      calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    have h3 : ones (2 ^ a + 2 ^ b + 1) = 3 := by
      rw [add_assoc, ones_two_pow_add key, ones_two_pow_add hb1, ones_one]
    omega

/-! ### The counting function `f` -/

/-- `f k` is the number of elements of `{k+1, …, 2k}` having exactly three
binary `1`s. -/
def f (k : ℕ) : ℕ := ((Finset.Ioc k (2 * k)).filter fun n => ones n = 3).card

/-- The indicator of "exactly three binary ones". -/
def ind (n : ℕ) : ℕ := if ones n = 3 then 1 else 0

lemma f_eq_sum (k : ℕ) : f k = ∑ n ∈ Finset.Ioc k (2 * k), ind n := by
  rw [f, Finset.card_filter]
  simp only [ind]

/-- The step identity: from `Ioc k (2k)` to `Ioc (k+1) (2k+2)` one removes
`k+1` and adds `2k+1` and `2k+2`, and `2k+2 = 2(k+1)` has as many ones as
`k+1`. -/
lemma f_succ {k : ℕ} (hk : 1 ≤ k) :
    f (k + 1) = f k + ind (2 * k + 1) := by
  have htop : Finset.Ioc (k + 1) (2 * (k + 1)) =
      insert (2 * k + 2) (insert (2 * k + 1) (Finset.Ioc (k + 1) (2 * k))) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  have hbot : Finset.Ioc k (2 * k) =
      insert (k + 1) (Finset.Ioc (k + 1) (2 * k)) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  have hmem1 : (2 * k + 2) ∉ insert (2 * k + 1) (Finset.Ioc (k + 1) (2 * k)) := by
    simp only [Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hmem2 : (2 * k + 1) ∉ Finset.Ioc (k + 1) (2 * k) := by
    simp only [Finset.mem_Ioc]
    omega
  have hmem3 : (k + 1) ∉ Finset.Ioc (k + 1) (2 * k) := by
    simp only [Finset.mem_Ioc]
    omega
  have hind : ind (2 * k + 2) = ind (k + 1) := by
    unfold ind
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, ones_two_mul (by omega)]
  rw [f_eq_sum, f_eq_sum, htop, hbot, Finset.sum_insert hmem1,
    Finset.sum_insert hmem2, Finset.sum_insert hmem3]
  omega

lemma f_one : f 1 = 0 := by
  have h : Finset.Ioc 1 (2 * 1) = {2} := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    omega
  have h2 : ones 2 = 1 := by
    rw [show (2 : ℕ) = 2 * 1 by norm_num, ones_two_mul (by norm_num), ones_one]
  rw [f, h, Finset.filter_singleton]
  simp [h2]

lemma f_mono {k l : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l) : f k ≤ f l := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hl ih =>
    have hstep := f_succ (k := l) (by omega)
    omega

/-- The value at a power of two: the elements of `(2^n, 2^(n+1)]` with three
binary ones are exactly the `2^n + 2^a + 2^b` with `b < a < n`. -/
lemma f_two_pow (n : ℕ) : f (2 ^ n) = n.choose 2 := by
  classical
  have hcard : ((Finset.range n).sigma fun a => Finset.range a).card =
      n.choose 2 := by
    rw [Finset.card_sigma]
    simp only [Finset.card_range]
    rw [Finset.sum_range_id, Nat.choose_two_right]
  rw [← hcard, f]
  refine (Finset.card_bij (fun s _ => 2 ^ n + 2 ^ s.1 + 2 ^ s.2)
    ?_ ?_ ?_).symm
  · rintro ⟨a, b⟩ hs
    simp only [Finset.mem_sigma, Finset.mem_range] at hs
    obtain ⟨ha, hb⟩ := hs
    have hba : 2 ^ b < 2 ^ a := two_pow_lt_two_pow hb
    have hlt : 2 ^ a + 2 ^ b < 2 ^ n := by
      have h1 : 2 ^ (a + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
      omega
    have h0 : 0 < 2 ^ b := by positivity
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [add_assoc, ones_two_pow_add (by omega), ones_two_pow_add hba,
      ones_two_pow]
  · rintro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
    simp only [Finset.mem_sigma, Finset.mem_range] at ha hc
    dsimp only at heq
    have h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d := by omega
    obtain ⟨hac, hbd⟩ := two_pow_pair_inj ha.2 hc.2 h
    subst hac
    subst hbd
    rfl
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
    obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hq
    set m := q - 2 ^ n with hm
    have hq' : q = 2 ^ n + m := by omega
    by_cases hm2 : m = 2 ^ n
    · exfalso
      have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      rw [show q = 2 ^ (n + 1) by omega, ones_two_pow] at hq3
      omega
    · have hmlt : m < 2 ^ n := by omega
      have hone : ones m = 2 := by
        rw [hq', ones_two_pow_add hmlt] at hq3
        omega
      obtain ⟨a, b, hba, hab⟩ := exists_pair_of_ones_eq_two m hone
      have han : a < n := by
        have h0 : 0 < 2 ^ b := by positivity
        exact lt_of_two_pow_lt (by omega)
      refine ⟨⟨a, b⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_range]
        exact ⟨han, hba⟩
      · dsimp only
        omega

/-! ### Values near `2^n` -/

lemma f_two_pow_add_one (n : ℕ) : f (2 ^ n + 1) = n.choose 2 := by
  have h := f_succ (k := 2 ^ n) one_le_two_pow
  have hones : ones (2 * 2 ^ n + 1) = 2 := by
    rw [ones_two_mul_add_one, ones_two_pow]
  rw [f_two_pow] at h
  rw [h]
  simp [ind, hones]

lemma f_two_pow_add_two {n : ℕ} (hn : 1 ≤ n) :
    f (2 ^ n + 2) = n.choose 2 + 1 := by
  have h2n : 1 ≤ 2 ^ n := one_le_two_pow
  have h := f_succ (k := 2 ^ n + 1) (by omega)
  have harg : 2 * (2 ^ n + 1) + 1 = 2 ^ (n + 1) + 3 := by ring
  have hones : ones (2 ^ (n + 1) + 3) = 3 := by
    have h3 : (3 : ℕ) < 2 ^ (n + 1) := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
        (show 2 ≤ n + 1 by omega)
      omega
    rw [ones_two_pow_add h3, show (3 : ℕ) = 2 * 1 + 1 by norm_num,
      ones_two_mul_add_one, ones_one]
  rw [harg] at h
  rw [show 2 ^ n + 2 = 2 ^ n + 1 + 1 by omega, h, f_two_pow_add_one]
  simp [ind, hones]

lemma f_two_pow_add_three {n : ℕ} (hn : 2 ≤ n) :
    f (2 ^ n + 3) = n.choose 2 + 2 := by
  have h2n : 1 ≤ 2 ^ n := one_le_two_pow
  have h := f_succ (k := 2 ^ n + 2) (by omega)
  have harg : 2 * (2 ^ n + 2) + 1 = 2 ^ (n + 1) + 5 := by ring
  have hones : ones (2 ^ (n + 1) + 5) = 3 := by
    have h5 : (5 : ℕ) < 2 ^ (n + 1) := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
        (show 3 ≤ n + 1 by omega)
      omega
    rw [ones_two_pow_add h5, show (5 : ℕ) = 2 * 2 + 1 by norm_num,
      ones_two_mul_add_one, show (2 : ℕ) = 2 * 1 by norm_num,
      ones_two_mul (by norm_num), ones_one]
  rw [harg] at h
  rw [show 2 ^ n + 3 = 2 ^ n + 2 + 1 by omega, h,
    f_two_pow_add_two (by omega)]
  simp [ind, hones]

/-! ### Part (a) -/

/-- **IMO 1994, Problem 3, part (a).** Every positive integer `m` is a value
of `f` at some positive integer. -/
theorem part_a (m : ℕ) (hm : 0 < m) : ∃ k : ℕ, 0 < k ∧ f k = m := by
  classical
  -- `f` is unbounded: `f (2^(m+2)) = C(m+2, 2) ≥ m`
  have hub : ∃ j : ℕ, m ≤ f (j + 1) := by
    refine ⟨2 ^ (m + 2) - 1, ?_⟩
    have hp : 1 ≤ 2 ^ (m + 2) := one_le_two_pow
    rw [show 2 ^ (m + 2) - 1 + 1 = 2 ^ (m + 2) by omega, f_two_pow]
    have h1 : (m + 2).choose 2 = (m + 1).choose 1 + (m + 1).choose 2 :=
      Nat.choose_succ_succ (m + 1) 1
    have h2 : (m + 1).choose 1 = m + 1 := Nat.choose_one_right (m + 1)
    omega
  -- the least `j` with `m ≤ f (j+1)` gives `f (j+1) = m`, since `f 1 = 0`
  -- and the steps of `f` are `0` or `1`
  set N := Nat.find hub with hNdef
  have hN : m ≤ f (N + 1) := Nat.find_spec hub
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · exfalso
    rw [h0, zero_add, f_one] at hN
    omega
  · have hmin := Nat.find_min hub (show N - 1 < N by omega)
    rw [show N - 1 + 1 = N by omega] at hmin
    have hlt : f N < m := by omega
    have hstep := f_succ (k := N) hpos
    refine ⟨N + 1, by omega, ?_⟩
    unfold ind at hstep
    split at hstep <;> omega

/-! ### Part (b) -/

/-- **IMO 1994, Problem 3, part (b).** A positive integer `m` is attained by
`f` at exactly one positive integer iff `m = C(n,2) + 1` for some `n ≥ 2`. -/
theorem part_b (m : ℕ) (hm : 0 < m) :
    (∃! k : ℕ, 0 < k ∧ f k = m) ↔ ∃ n : ℕ, 2 ≤ n ∧ m = n.choose 2 + 1 := by
  constructor
  · rintro ⟨k, ⟨hkpos, hkm⟩, huniq⟩
    -- `k ≥ 2` since `f 1 = 0 < m`
    have hk2 : 2 ≤ k := by
      by_contra hc
      have hk1 : k = 1 := by omega
      rw [hk1, f_one] at hkm
      omega
    -- the step after `k` must jump, else `k+1` is a second witness
    have hnext : ones (2 * k + 1) = 3 := by
      have hstep := f_succ (k := k) (by omega)
      have hne : f (k + 1) ≠ m := fun hcon => by
        have := huniq (k + 1) ⟨by omega, hcon⟩
        omega
      unfold ind at hstep
      split at hstep
      · assumption
      · omega
    -- the step into `k` must jump, else `k-1` is a second witness
    have hprev : ones (2 * (k - 1) + 1) = 3 := by
      have hstep := f_succ (k := k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at hstep
      have hne : f (k - 1) ≠ m := fun hcon => by
        have := huniq (k - 1) ⟨by omega, hcon⟩
        omega
      unfold ind at hstep
      split at hstep
      · assumption
      · omega
    -- so `ones (k-1) = ones k = 2`, forcing `k = 2^a + 2` with `a ≥ 2`
    have h1 : ones (k - 1) = 2 := by
      have := ones_two_mul_add_one (k - 1)
      omega
    have h2 : ones k = 2 := by
      have := ones_two_mul_add_one k
      omega
    obtain ⟨a, ha2, hka⟩ := consecutive_ones_two (t := k - 1) h1
      (by rw [show k - 1 + 1 = k by omega]; exact h2)
    have hk : k = 2 ^ a + 2 := by omega
    refine ⟨a, ha2, ?_⟩
    rw [hk, f_two_pow_add_two (by omega)] at hkm
    omega
  · rintro ⟨n, hn2, rfl⟩
    have h2n : 1 ≤ 2 ^ n := one_le_two_pow
    refine ⟨2 ^ n + 2, ⟨by omega, f_two_pow_add_two (by omega)⟩, ?_⟩
    rintro y ⟨hypos, hym⟩
    rcases lt_trichotomy y (2 ^ n + 2) with hlt | heq | hgt
    · exfalso
      have hle : f y ≤ f (2 ^ n + 1) := f_mono hypos (by omega)
      rw [f_two_pow_add_one] at hle
      omega
    · exact heq
    · exfalso
      have hle : f (2 ^ n + 3) ≤ f y := f_mono (by omega) (by omega)
      rw [f_two_pow_add_three hn2] at hle
      omega

/-- Part (b) restated with the answer in the form `n(n-1)/2 + 1` used in the
classical solution. -/
theorem part_b' (m : ℕ) (hm : 0 < m) :
    (∃! k : ℕ, 0 < k ∧ f k = m) ↔
      ∃ n : ℕ, 2 ≤ n ∧ m = n * (n - 1) / 2 + 1 := by
  rw [part_b m hm]
  refine exists_congr fun n => and_congr_right fun _ => ?_
  rw [Nat.choose_two_right]

end Imo1994Q3
