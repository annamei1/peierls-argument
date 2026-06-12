import Mathlib

/-!
# The pentagon problem (IMO 1986, Problem 3)

To each vertex of a regular pentagon an integer is assigned, so that the sum
of all five numbers is positive. If three consecutive vertices carry the
numbers `x, y, z` with `y < 0`, the following operation is allowed: replace
`x, y, z` by `x + y, -y, z + y`. Such an operation is performed repeatedly as
long as at least one of the five numbers is negative. We prove that this
procedure necessarily comes to an end after a finite number of steps.

## Formalization

A configuration is a function `Fin 5 → ℤ` (vertex indices taken mod 5).
`Step x x'` holds when `x'` is obtained from `x` by one allowed operation,
i.e. operating at a vertex carrying a negative number. The main theorem
`Pentagon.terminates` states that there is no infinite `Step`-chain starting
from a configuration with positive sum.

## Proof (monovariant argument)

The total sum `total x = ∑ i, x i` is invariant under the operation, hence
stays positive. The quantity `energy x = ∑ i, (x i - x (i + 2)) ^ 2` is a
nonnegative integer and satisfies the exact identity

`energy (operate x i) = energy x + 2 * x i * total x`,

so each allowed step (where `x i < 0` and `total x > 0`) strictly decreases
`energy`. A strictly decreasing sequence of nonnegative integers is finite.
-/

namespace Pentagon

/-- A configuration: an integer assigned to each vertex of the pentagon. -/
abbrev State := Fin 5 → ℤ

/-- The sum of the five numbers. -/
def total (x : State) : ℤ := ∑ i, x i

/-- The monovariant `∑ i, (x i - x (i + 2)) ^ 2`, indices mod 5.
For `x = (x₁, …, x₅)` this is `∑ (xᵢ - xᵢ₊₂)²` with `x₆ = x₁`, `x₇ = x₂`. -/
def energy (x : State) : ℤ := ∑ i, (x i - x (i + 2)) ^ 2

/-- The allowed operation centred at vertex `i`: the three consecutive values
`x (i-1), x i, x (i+1)` are replaced by `x (i-1) + x i, -(x i), x (i+1) + x i`
respectively; the other two vertices are unchanged. -/
def operate (x : State) (i : Fin 5) : State := fun j =>
  if j = i - 1 then x (i - 1) + x i
  else if j = i then -x i
  else if j = i + 1 then x (i + 1) + x i
  else x j

/-- One step of the procedure: operating at a vertex whose number is
negative. -/
def Step (x x' : State) : Prop := ∃ i, x i < 0 ∧ x' = operate x i

lemma energy_nonneg (x : State) : 0 ≤ energy x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The operation preserves the total sum. -/
lemma total_operate (x : State) (i : Fin 5) :
    total (operate x i) = total x := by
  fin_cases i <;>
    · simp +decide [total, operate, Fin.sum_univ_five,
        show (-1 : Fin 5) = 4 by decide]
      ring

/-- The exact change of the monovariant under one operation. -/
lemma energy_operate (x : State) (i : Fin 5) :
    energy (operate x i) = energy x + 2 * x i * total x := by
  fin_cases i <;>
    · simp +decide [energy, operate, total, Fin.sum_univ_five,
        show (-1 : Fin 5) = 4 by decide]
      ring

/-- A step preserves the total sum. -/
lemma total_step {x x' : State} (h : Step x x') : total x' = total x := by
  obtain ⟨i, -, rfl⟩ := h
  exact total_operate x i

/-- A step strictly decreases the monovariant, provided the total sum is
positive. -/
lemma energy_step {x x' : State} (h : Step x x') (hpos : 0 < total x) :
    energy x' < energy x := by
  obtain ⟨i, hi, rfl⟩ := h
  have hneg : x i * total x < 0 := mul_neg_of_neg_of_pos hi hpos
  rw [energy_operate]
  linarith

/-- **The pentagon problem (IMO 1986, Problem 3).**
The procedure necessarily comes to an end after a finite number of steps:
there is no infinite sequence of allowed operations starting from a
configuration whose five numbers have positive sum. -/
theorem terminates (g : ℕ → State) (hpos : 0 < total (g 0)) :
    ¬ (∀ n, Step (g n) (g (n + 1))) := by
  intro hstep
  -- the total sum is invariant along the run, hence always positive
  have htotal : ∀ n, total (g n) = total (g 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [total_step (hstep n), ih]
  -- the energy strictly decreases at every step
  have hdec : ∀ n, energy (g (n + 1)) < energy (g n) := fun n =>
    energy_step (hstep n) (by rw [htotal n]; exact hpos)
  -- hence it drops by at least 1 per step
  have hle : ∀ n : ℕ, energy (g n) + n ≤ energy (g 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hdec n
      push_cast at ih ⊢
      omega
  -- after `energy (g 0) + 1` steps the energy would be negative
  have h₁ := hle ((energy (g 0)).toNat + 1)
  have h₂ := energy_nonneg (g ((energy (g 0)).toNat + 1))
  have h₃ : ((energy (g 0)).toNat : ℤ) = energy (g 0) :=
    Int.toNat_of_nonneg (energy_nonneg (g 0))
  push_cast at h₁
  omega

end Pentagon
