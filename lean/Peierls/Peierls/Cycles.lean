import Peierls.Parity

/-!
# Cycle extraction and anchoring

This file provides the graph-theoretic half of the Peierls argument:

* every cycle walk has an even edge set (`isEven_walkFinset`), even length
  (`even_length_of_cycleWalk`), and length at least 4 (`four_le_length_of_cycleWalk`);
* from an even edge set `γ` with `In γ (0,0) = 1` one can extract a cycle walk
  whose edge set is contained in `γ`, still has crossing parity `1` at the
  origin, and which is *anchored*: it starts at the dual vertex `(k, -1)` with
  first step `Dir.U` (so its first edge is `H k 0`, the dual edge crossing the
  positive horizontal axis at `k + ½`), where `0 ≤ k` and `2k + 2 ≤ ℓ`
  (`exists_anchored_cycle`).

## Proof sketch for `exists_anchored_cycle`

1. **Extraction.**  By strong induction on `γ.card`: an even nonempty edge set
   contains a cycle walk (greedy walk: every dual vertex met has even positive
   degree, hence a way out not using the incoming edge; by pigeonhole some
   dual vertex repeats; the segment between the first repetition is a closed
   walk with distinct edges).  Remove its edge set `κ` from `γ`: the rest is
   even, and crossing parities add (`In_sdiff`), so either `In κ (0,0) = 1`
   (done) or recurse on `γ \ κ`.
2. **Anchoring.**  Given a cycle walk with edge set `κ`, `In κ (0,0) = 1`
   means an odd number of edges `H m 0 ∈ κ` with `m ≥ 0`; pick one, say
   `H k 0`.  By `rowCount_even` there is also an edge `H m' 0 ∈ κ` with
   `m' < 0`.  The walk visits both dual endpoints of each of its edges; rotate
   the word (and reverse it if necessary) so that the walk starts at `(k, -1)`
   with first step `U`.  Rotation and reversal do not change the edge set.
3. **Length bound.**  The (rotated) closed walk visits `(k, -1)` and a dual
   vertex with first coordinate `m' ≤ -1`; each step changes the first
   coordinate by at most 1, so each of the two arcs between the two visits has
   length at least `k - m' ≥ k + 1`, whence `ℓ ≥ 2k + 2`.
-/

namespace Peierls

open Finset

/-! ## Elementary lemmas on steps and dual edges -/

theorem step_ne (v : DualV) (d : Dir) : v.step d ≠ v := by
  obtain ⟨p, q⟩ := v
  cases d <;> simp [DualV.step, Prod.ext_iff]

theorem step_injective {v v' : DualV} (d : Dir) (h : v.step d = v'.step d) : v = v' := by
  obtain ⟨p, q⟩ := v
  obtain ⟨p', q'⟩ := v'
  cases d <;> simp [DualV.step, Prod.ext_iff] at h ⊢ <;> omega

/-- The reverse of a step direction. -/
def dirRev : Dir → Dir
  | .U => .D
  | .D => .U
  | .L => .R
  | .R => .L

theorem step_dirRev (v : DualV) (d : Dir) : (v.step d).step (dirRev d) = v := by
  obtain ⟨p, q⟩ := v
  cases d <;> simp [DualV.step, dirRev]

theorem stepEdge_dirRev (v : DualV) (d : Dir) :
    stepEdge (v.step d) (dirRev d) = stepEdge v d := by
  obtain ⟨p, q⟩ := v
  cases d <;> simp [DualV.step, dirRev, stepEdge]

theorem dualEnds_ne (e : Edge) : e.dualEnds.1 ≠ e.dualEnds.2 := by
  cases e <;> simp [Edge.dualEnds, Prod.ext_iff]

/-- The dual endpoints of `stepEdge v d` are exactly `v` and `v.step d`. -/
theorem mem_dualEnds_stepEdge (v : DualV) (d : Dir) (x : DualV) :
    (x = (stepEdge v d).dualEnds.1 ∨ x = (stepEdge v d).dualEnds.2) ↔
      (x = v ∨ x = v.step d) := by
  obtain ⟨p, q⟩ := v
  cases d <;> simp [stepEdge, Edge.dualEnds, DualV.step, Prod.ext_iff] <;> omega

/-- Every edge is the step edge from its first dual endpoint towards its second. -/
theorem exists_dir_of_dualEnds (e : Edge) :
    ∃ d, e.dualEnds.2 = e.dualEnds.1.step d ∧ e = stepEdge e.dualEnds.1 d := by
  cases e with
  | H a b =>
    refine ⟨.U, ?_, ?_⟩ <;> simp [Edge.dualEnds, DualV.step, stepEdge]
  | V a b =>
    refine ⟨.R, ?_, ?_⟩ <;> simp [Edge.dualEnds, DualV.step, stepEdge]

/-- Two distinct dual endpoints of an edge differ by a unit step realising the edge. -/
theorem exists_step_of_ends {e : Edge} {x y : DualV}
    (hx : x = e.dualEnds.1 ∨ x = e.dualEnds.2)
    (hy : y = e.dualEnds.1 ∨ y = e.dualEnds.2) (hxy : x ≠ y) :
    ∃ d, y = x.step d ∧ e = stepEdge x d := by
  obtain ⟨d, hd1, hd2⟩ := exists_dir_of_dualEnds e
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact ⟨d, hd1, hd2⟩
  · refine ⟨dirRev d, ?_, ?_⟩
    · conv_rhs => rw [hd1]
      rw [step_dirRev]
    · rw [hd1, stepEdge_dirRev]
      exact hd2
  · exact absurd rfl hxy

/-- An edge has exactly two dual endpoints: any endpoint of `e` equals one of two
given distinct endpoints. -/
theorem end_cases {e : Edge} {x y z : DualV} (hxy : x ≠ y)
    (hx : x = e.dualEnds.1 ∨ x = e.dualEnds.2)
    (hy : y = e.dualEnds.1 ∨ y = e.dualEnds.2)
    (hz : z = e.dualEnds.1 ∨ z = e.dualEnds.2) : z = x ∨ z = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> tauto

/-! ## Walk infrastructure -/

theorem walkEnd_append (v : DualV) (w₁ w₂ : List Dir) :
    walkEnd v (w₁ ++ w₂) = walkEnd (walkEnd v w₁) w₂ := by
  induction w₁ generalizing v with
  | nil => rfl
  | cons d w ih => simp [walkEnd, ih]

theorem walkEdges_append (v : DualV) (w₁ w₂ : List Dir) :
    walkEdges v (w₁ ++ w₂) = walkEdges v w₁ ++ walkEdges (walkEnd v w₁) w₂ := by
  induction w₁ generalizing v with
  | nil => rfl
  | cons d w ih => simp [walkEdges, walkEnd, ih]

/-- Any edge of a walk splits the word: it is the step edge taken at some position. -/
theorem exists_split_of_mem_walkEdges {v : DualV} {w : List Dir} {e : Edge}
    (he : e ∈ walkEdges v w) :
    ∃ w₁ d w₂, w = w₁ ++ d :: w₂ ∧ e = stepEdge (walkEnd v w₁) d := by
  induction w generalizing v with
  | nil => simp [walkEdges] at he
  | cons d w ih =>
    simp only [walkEdges, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨[], d, w, rfl, rfl⟩
    · obtain ⟨w₁, d', w₂, rfl, hed⟩ := ih (v := v.step d) he
      exact ⟨d :: w₁, d', w₂, rfl, hed⟩

/-- Each step changes the first coordinate by at most one. -/
theorem walkEnd_fst_bounds (v : DualV) (w : List Dir) :
    (walkEnd v w).1 ≤ v.1 + w.length ∧ v.1 - w.length ≤ (walkEnd v w).1 := by
  induction w generalizing v with
  | nil => simp [walkEnd]
  | cons d w ih =>
    obtain ⟨h1, h2⟩ := ih (v.step d)
    have hstep : (v.step d).1 ≤ v.1 + 1 ∧ v.1 - 1 ≤ (v.step d).1 := by
      obtain ⟨p, q⟩ := v
      cases d <;> simp [DualV.step] <;> omega
    simp only [walkEnd, List.length_cons] at *
    push_cast at *
    omega

/-! ## Rotation and reversal of closed walks -/

theorem walkEnd_rotate {v : DualV} {w₁ w₂ : List Dir} (h : walkEnd v (w₁ ++ w₂) = v) :
    walkEnd (walkEnd v w₁) (w₂ ++ w₁) = walkEnd v w₁ := by
  rw [walkEnd_append] at h
  rw [walkEnd_append, h]

theorem walkEdges_rotate {v : DualV} {w₁ w₂ : List Dir} (h : walkEnd v (w₁ ++ w₂) = v) :
    List.Perm (walkEdges (walkEnd v w₁) (w₂ ++ w₁)) (walkEdges v (w₁ ++ w₂)) := by
  rw [walkEnd_append] at h
  rw [walkEdges_append (walkEnd v w₁) w₂ w₁, walkEdges_append v w₁ w₂, h]
  exact List.perm_append_comm

/-- The reversed direction word, traversing a walk backwards. -/
def revWord (w : List Dir) : List Dir := (w.map dirRev).reverse

theorem revWord_cons (d : Dir) (w : List Dir) :
    revWord (d :: w) = revWord w ++ [dirRev d] := by
  simp [revWord]

theorem walkEnd_revWord (v : DualV) (w : List Dir) :
    walkEnd (walkEnd v w) (revWord w) = v := by
  induction w generalizing v with
  | nil => rfl
  | cons d w ih =>
    rw [revWord_cons]
    show walkEnd (walkEnd (v.step d) w) (revWord w ++ [dirRev d]) = v
    rw [walkEnd_append, ih (v.step d)]
    exact step_dirRev v d

theorem walkEdges_revWord (v : DualV) (w : List Dir) :
    walkEdges (walkEnd v w) (revWord w) = (walkEdges v w).reverse := by
  induction w generalizing v with
  | nil => rfl
  | cons d w ih =>
    rw [revWord_cons]
    show walkEdges (walkEnd (v.step d) w) (revWord w ++ [dirRev d])
      = (stepEdge v d :: walkEdges (v.step d) w).reverse
    rw [walkEdges_append, ih (v.step d), walkEnd_revWord, List.reverse_cons]
    congr 1
    show [stepEdge (v.step d) (dirRev d)] = [stepEdge v d]
    rw [stepEdge_dirRev]

/-- **Re-rooting.**  A cycle walk through an edge `e` can be re-rooted (by rotation,
and reversal if needed) so as to start at either prescribed dual endpoint `x` of
`e`, with `e` as its first edge; the multiset of traversed edges is unchanged. -/
theorem exists_reroot {v : DualV} {w : List Dir} (h : IsCycleWalk v w) {e : Edge}
    (he : e ∈ walkEdges v w) {x : DualV}
    (hx : x = e.dualEnds.1 ∨ x = e.dualEnds.2) :
    ∃ d w', IsCycleWalk x (d :: w') ∧ stepEdge x d = e ∧
      List.Perm (walkEdges x (d :: w')) (walkEdges v w) := by
  obtain ⟨hclosed, hnd, hwne⟩ := h
  obtain ⟨w₁, d, w₂, rfl, hed⟩ := exists_split_of_mem_walkEdges he
  have hrotEnd := walkEnd_rotate hclosed
  have hrotEdges := walkEdges_rotate hclosed
  rw [show (d :: w₂) ++ w₁ = d :: (w₂ ++ w₁) from rfl] at hrotEnd hrotEdges
  have hxmem : x = walkEnd v w₁ ∨ x = (walkEnd v w₁).step d :=
    (mem_dualEnds_stepEdge (walkEnd v w₁) d x).mp (by rw [← hed]; exact hx)
  rcases hxmem with rfl | rfl
  · exact ⟨d, w₂ ++ w₁, ⟨hrotEnd, hrotEdges.nodup_iff.mpr hnd, by simp⟩,
      hed.symm, hrotEdges⟩
  · -- the walk traverses `e` *into* `x`: reverse it first.
    set u : DualV := walkEnd v w₁ with hu
    set W : List Dir := d :: (w₂ ++ w₁) with hW
    have hrevEnd : walkEnd u (revWord W) = u := by
      have h0 := walkEnd_revWord u W
      rw [hrotEnd] at h0
      exact h0
    have hrevW : revWord W = revWord (w₂ ++ w₁) ++ [dirRev d] := revWord_cons _ _
    have hclosed'' : walkEnd u (revWord (w₂ ++ w₁) ++ [dirRev d]) = u := by
      rw [← hrevW]; exact hrevEnd
    have hrotEnd2 := walkEnd_rotate hclosed''
    have hrotEdges2 := walkEdges_rotate hclosed''
    set u' : DualV := walkEnd u (revWord (w₂ ++ w₁)) with hu'
    have hstep' : u'.step (dirRev d) = u := by
      have h3 : walkEnd u' [dirRev d] = u := by
        rw [hu', ← walkEnd_append]
        exact hclosed''
      exact h3
    have hux : u' = u.step d := by
      apply step_injective (dirRev d)
      rw [hstep', step_dirRev]
    have hedgesW : walkEdges u (revWord W) = (walkEdges u W).reverse := by
      have h0 := walkEdges_revWord u W
      rw [hrotEnd] at h0
      exact h0
    have hperm : List.Perm (walkEdges u' (dirRev d :: revWord (w₂ ++ w₁)))
        (walkEdges v (w₁ ++ d :: w₂)) := by
      have p1 := hrotEdges2
      rw [← hrevW, hedgesW] at p1
      exact p1.trans (((walkEdges u W).reverse_perm).trans hrotEdges)
    rw [← hux]
    refine ⟨dirRev d, revWord (w₂ ++ w₁), ⟨?_, ?_, by simp⟩, ?_, ?_⟩
    · exact hrotEnd2
    · exact hperm.nodup_iff.mpr hnd
    · rw [hux, stepEdge_dirRev]
      exact hed.symm
    · exact hperm

/-! ## Generalities on cycle walks -/

/-- Auxiliary handshake count: along any walk, the number of traversed edges
incident to `u`, corrected by indicators at the two ends, is even. -/
private theorem even_incidence_aux (u : DualV) (w : List Dir) (v : DualV) :
    Even ((walkEdges v w).countP (fun e => decide (u = e.dualEnds.1 ∨ u = e.dualEnds.2))
      + (if u = v then 1 else 0) + (if u = walkEnd v w then 1 else 0)) := by
  induction w generalizing v with
  | nil =>
    by_cases h : u = v <;> simp [walkEdges, walkEnd, h]
  | cons d w ih =>
    have IH := ih (v.step d)
    have hne := step_ne v d
    have hcv := mem_dualEnds_stepEdge v d u
    show Even ((walkEdges v (d :: w)).countP
        (fun e => decide (u = e.dualEnds.1 ∨ u = e.dualEnds.2))
      + (if u = v then 1 else 0) + (if u = walkEnd (v.step d) w then 1 else 0))
    rw [show walkEdges v (d :: w) = stepEdge v d :: walkEdges (v.step d) w from rfl,
      List.countP_cons]
    by_cases h1 : u = v <;> by_cases h2 : u = v.step d
    · exact absurd (h2.symm.trans h1) hne
    · rw [if_pos (decide_eq_true (hcv.mpr (Or.inl h1))), if_pos h1]
      rw [if_neg h2] at IH
      rw [Nat.even_iff] at IH ⊢
      omega
    · rw [if_pos (decide_eq_true (hcv.mpr (Or.inr h2))), if_neg h1]
      rw [if_pos h2] at IH
      rw [Nat.even_iff] at IH ⊢
      omega
    · rw [if_neg (fun hb => (hcv.mp (of_decide_eq_true hb)).elim h1 h2), if_neg h1]
      rw [if_neg h2] at IH
      rw [Nat.even_iff] at IH ⊢
      omega

/-- The edge set of a cycle walk is even: the degree of a dual vertex `v` in it
is twice the number of times the closed walk visits `v`. -/
theorem isEven_walkFinset {v : DualV} {w : List Dir} (h : IsCycleWalk v w) :
    IsEven (walkFinset v w) := by
  obtain ⟨hclosed, hnd, -⟩ := h
  intro u
  have key := even_incidence_aux u w v
  rw [hclosed] at key
  have hdeg : deg (walkFinset v w) u =
      (walkEdges v w).countP (fun e => decide (u = e.dualEnds.1 ∨ u = e.dualEnds.2)) := by
    rw [List.countP_eq_length_filter]
    simp only [deg]
    rw [show (walkFinset v w).filter (fun e => u = e.dualEnds.1 ∨ u = e.dualEnds.2) =
        ((walkEdges v w).filter
          (fun e => decide (u = e.dualEnds.1 ∨ u = e.dualEnds.2))).toFinset by
      ext e
      simp [walkFinset]]
    exact List.toFinset_card_of_nodup (hnd.filter _)
  rw [hdeg]
  by_cases h1 : u = v
  · rw [if_pos h1] at key
    rw [Nat.even_iff] at key ⊢
    omega
  · rw [if_neg h1] at key
    simpa using key

/-- The parity of the coordinate sum of a dual vertex. -/
private def coordParity (v : DualV) : ZMod 2 := ((v.1 + v.2 : ℤ) : ZMod 2)

private theorem coordParity_step (v : DualV) (d : Dir) :
    coordParity (v.step d) = coordParity v + 1 := by
  obtain ⟨p, q⟩ := v
  cases d <;>
    (simp only [DualV.step, coordParity]
     rw [← sub_eq_zero]
     push_cast
     ring_nf) <;>
    decide

private theorem coordParity_walkEnd (v : DualV) (w : List Dir) :
    coordParity (walkEnd v w) = coordParity v + (w.length : ZMod 2) := by
  induction w generalizing v with
  | nil => simp [walkEnd]
  | cons d w ih =>
    simp only [walkEnd, List.length_cons]
    rw [ih (v.step d), coordParity_step]
    push_cast
    ring

/-- A closed walk has even length (each step flips the coordinate-sum parity). -/
theorem even_length_of_cycleWalk {v : DualV} {w : List Dir} (h : IsCycleWalk v w) :
    Even w.length := by
  have hp := coordParity_walkEnd v w
  rw [h.1] at hp
  have h0 : ((w.length : ℕ) : ZMod 2) = 0 := by
    have h2 : coordParity v + (0 : ZMod 2) = coordParity v + (w.length : ZMod 2) := by
      rw [add_zero]; exact hp
    exact (add_left_cancel h2).symm
  exact ZMod.natCast_eq_zero_iff_even.mp h0

/-- A cycle walk has length at least 4 (lengths 1 and 2 are impossible for a
closed walk with distinct edges, and the length is even). -/
theorem four_le_length_of_cycleWalk {v : DualV} {w : List Dir} (h : IsCycleWalk v w) :
    4 ≤ w.length := by
  have hev := even_length_of_cycleWalk h
  obtain ⟨hclosed, hnd, hwne⟩ := h
  rcases w with _ | ⟨d₁, w⟩
  · exact absurd rfl hwne
  rcases w with _ | ⟨d₂, w⟩
  · norm_num at hev
  rcases w with _ | ⟨d₃, w⟩
  · exfalso
    have hc2 : (v.step d₁).step d₂ = v := hclosed
    have hd : d₂ = dirRev d₁ := by
      obtain ⟨p, q⟩ := v
      cases d₁ <;> cases d₂ <;>
        simp only [DualV.step, dirRev, Prod.mk.injEq] at hc2 ⊢ <;>
        first | rfl | omega
    have hedge : stepEdge (v.step d₁) d₂ = stepEdge v d₁ := by
      rw [hd, stepEdge_dirRev]
    simp [walkEdges, hedge] at hnd
  · obtain ⟨t, ht⟩ := hev
    simp only [List.length_cons] at ht ⊢
    omega

/-! ## Crossing parity under removal -/

/-- Crossing parity is additive under removal of a subset. -/
theorem In_sdiff {γ κ : Finset Edge} (h : κ ⊆ γ) (i : Site) :
    In (γ \ κ) i = In γ i + In κ i := by
  have hsub : κ.filter (CrossesRight i) ⊆ γ.filter (CrossesRight i) :=
    Finset.filter_subset_filter _ h
  have hfil : (γ \ κ).filter (CrossesRight i) =
      γ.filter (CrossesRight i) \ κ.filter (CrossesRight i) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  simp only [In]
  rw [hfil, Finset.card_sdiff_of_subset hsub,
    Nat.cast_sub (Finset.card_le_card hsub), CharTwo.sub_eq_add]

/-- `In` takes only the values `0` and `1` (it lives in `ZMod 2`). -/
private theorem In_eq_zero_or_one (γ : Finset Edge) (z : Site) :
    In γ z = 0 ∨ In γ z = 1 := by
  simp only [In]
  rcases Nat.even_or_odd (γ.filter (CrossesRight z)).card with h | h
  · exact Or.inl (ZMod.natCast_eq_zero_iff_even.mpr h)
  · exact Or.inr (ZMod.natCast_eq_one_iff_odd.mpr h)

/-- Removing an even subset preserves evenness. -/
private theorem isEven_sdiff {γ κ : Finset Edge} (hsub : κ ⊆ γ) (hγ : IsEven γ)
    (hκ : IsEven κ) : IsEven (γ \ κ) := by
  intro u
  have hfsub : κ.filter (fun e => u = e.dualEnds.1 ∨ u = e.dualEnds.2) ⊆
      γ.filter (fun e => u = e.dualEnds.1 ∨ u = e.dualEnds.2) :=
    Finset.filter_subset_filter _ hsub
  have hfil : (γ \ κ).filter (fun e => u = e.dualEnds.1 ∨ u = e.dualEnds.2) =
      γ.filter (fun e => u = e.dualEnds.1 ∨ u = e.dualEnds.2) \
        κ.filter (fun e => u = e.dualEnds.1 ∨ u = e.dualEnds.2) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have h1 := hγ u
  have h2 := hκ u
  have hle := Finset.card_le_card hfsub
  simp only [deg] at h1 h2 ⊢
  rw [hfil, Finset.card_sdiff_of_subset hfsub]
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  exact ⟨a - b, by omega⟩

/-! ## Extraction of a cycle walk from an even nonempty edge set -/

/-- Inside an even edge set, every edge–endpoint incidence admits a *different*
edge at the same endpoint (the degree is even and positive, hence at least 2). -/
private theorem exists_other_incident {γ : Finset Edge} (hγ : IsEven γ) {u : DualV}
    {e : Edge} (he : e ∈ γ) (hu : u = e.dualEnds.1 ∨ u = e.dualEnds.2) :
    ∃ e', (e' ∈ γ ∧ (u = e'.dualEnds.1 ∨ u = e'.dualEnds.2)) ∧ e' ≠ e := by
  have hmem : e ∈ γ.filter (fun e => u = e.dualEnds.1 ∨ u = e.dualEnds.2) :=
    Finset.mem_filter.mpr ⟨he, hu⟩
  have hpos : 0 < deg γ u := by
    simp only [deg]
    exact Finset.card_pos.mpr ⟨e, hmem⟩
  have h2 : 1 < deg γ u := by
    obtain ⟨t, ht⟩ := hγ u
    omega
  have h2' : 1 < (γ.filter (fun e => u = e.dualEnds.1 ∨ u = e.dualEnds.2)).card := h2
  obtain ⟨e', he', hne'⟩ := Finset.exists_mem_ne h2' e
  exact ⟨e', Finset.mem_filter.mp he', hne'⟩

/-- The other dual endpoint of an edge. -/
private def otherEnd (e : Edge) (u : DualV) : DualV :=
  if u = e.dualEnds.1 then e.dualEnds.2 else e.dualEnds.1

private theorem otherEnd_mem (e : Edge) (u : DualV) :
    otherEnd e u = e.dualEnds.1 ∨ otherEnd e u = e.dualEnds.2 := by
  unfold otherEnd
  split <;> simp

private theorem otherEnd_ne (e : Edge) (u : DualV) : otherEnd e u ≠ u := by
  by_cases h : u = e.dualEnds.1
  · simp only [otherEnd, if_pos h]
    rw [h]
    exact (dualEnds_ne e).symm
  · simp only [otherEnd, if_neg h]
    exact fun hh => h hh.symm

/-- The state of the greedy walk: the current dual vertex together with the
edge just traversed into it. -/
private abbrev GWState (γ : Finset Edge) : Type :=
  {p : DualV × Edge // p.2 ∈ γ ∧ (p.1 = p.2.dualEnds.1 ∨ p.1 = p.2.dualEnds.2)}

/-- One greedy step: pick an edge of `γ` at the current vertex different from the
incoming one and move to its other endpoint. -/
private noncomputable def gNext {γ : Finset Edge} (hγ : IsEven γ) (s : GWState γ) :
    GWState γ :=
  ⟨(otherEnd (exists_other_incident hγ s.2.1 s.2.2).choose s.1.1,
    (exists_other_incident hγ s.2.1 s.2.2).choose),
   (exists_other_incident hγ s.2.1 s.2.2).choose_spec.1.1,
   otherEnd_mem _ _⟩

private theorem gNext_spec {γ : Finset Edge} (hγ : IsEven γ) (s : GWState γ) :
    (s.1.1 = (gNext hγ s).1.2.dualEnds.1 ∨ s.1.1 = (gNext hγ s).1.2.dualEnds.2) ∧
    (gNext hγ s).1.2 ≠ s.1.2 ∧
    (gNext hγ s).1.1 = otherEnd ((gNext hγ s).1.2) s.1.1 :=
  ⟨(exists_other_incident hγ s.2.1 s.2.2).choose_spec.1.2,
   (exists_other_incident hγ s.2.1 s.2.2).choose_spec.2,
   rfl⟩

/-- Turn a step sequence into a walk: the direction word along a segment of the
sequence realizes the corresponding vertices and edges. -/
private theorem walk_of_seq (U : ℕ → DualV) (E : ℕ → Edge) (d : ℕ → Dir)
    (h : ∀ k, U (k + 1) = (U k).step (d k) ∧ E (k + 1) = stepEdge (U k) (d k)) :
    ∀ n a, walkEnd (U a) ((List.range n).map (fun t => d (a + t))) = U (a + n) ∧
      walkEdges (U a) ((List.range n).map (fun t => d (a + t))) =
        (List.range n).map (fun t => E (a + t + 1)) := by
  intro n
  induction n with
  | zero => intro a; simp [walkEnd, walkEdges]
  | succ n ih =>
    intro a
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, add_zero]
    have hfd : ((fun t => d (a + t)) ∘ Nat.succ) = (fun t => d ((a + 1) + t)) := by
      funext t
      simp only [Function.comp]
      congr 1
      omega
    have hfE : ((fun t => E (a + t + 1)) ∘ Nat.succ) = (fun t => E ((a + 1) + t + 1)) := by
      funext t
      simp only [Function.comp]
      congr 1
      omega
    rw [hfd, hfE]
    have h1 := (h a).1
    have h2 := (h a).2
    constructor
    · show walkEnd ((U a).step (d a)) _ = _
      rw [← h1, (ih (a + 1)).1]
      congr 1
      omega
    · show stepEdge (U a) (d a) :: walkEdges ((U a).step (d a)) _ = _
      rw [← h1, ← h2, (ih (a + 1)).2]

/-- **Cycle extraction.**  An even nonempty edge set contains a cycle walk. -/
theorem exists_cycleWalk {γ : Finset Edge} (hγ : IsEven γ) (hne : γ.Nonempty) :
    ∃ v w, IsCycleWalk v w ∧ walkFinset v w ⊆ γ := by
  classical
  obtain ⟨e₀, he₀⟩ := hne
  let s0 : GWState γ := ⟨(e₀.dualEnds.1, e₀), he₀, Or.inl rfl⟩
  let U : ℕ → DualV := fun k => ((gNext hγ)^[k] s0).1.1
  let E : ℕ → Edge := fun k => ((gNext hγ)^[k] s0).1.2
  have hEmem : ∀ k, E k ∈ γ := fun k => ((gNext hγ)^[k] s0).2.1
  have hUend : ∀ k, U k = (E k).dualEnds.1 ∨ U k = (E k).dualEnds.2 :=
    fun k => ((gNext hγ)^[k] s0).2.2
  have hstep : ∀ k, (U k = (E (k + 1)).dualEnds.1 ∨ U k = (E (k + 1)).dualEnds.2) ∧
      E (k + 1) ≠ E k ∧ U (k + 1) = otherEnd (E (k + 1)) (U k) := by
    intro k
    have hit : (gNext hγ)^[k + 1] s0 = gNext hγ ((gNext hγ)^[k] s0) :=
      Function.iterate_succ_apply' _ _ _
    have h := gNext_spec hγ ((gNext hγ)^[k] s0)
    rw [← hit] at h
    exact ⟨h.1, h.2.1, h.2.2⟩
  -- choose the step directions
  have hadj : ∀ k, ∃ d, U (k + 1) = (U k).step d ∧ E (k + 1) = stepEdge (U k) d := by
    intro k
    obtain ⟨hend, hEne, hother⟩ := hstep k
    have hUend' := hUend (k + 1)
    have hne' : U k ≠ U (k + 1) := by
      rw [hother]
      exact (otherEnd_ne _ _).symm
    exact exists_step_of_ends hend hUend' hne'
  choose dd hd1 hd2 using hadj
  -- pigeonhole: some dual vertex repeats
  have hUmem : ∀ k, U k ∈ γ.biUnion (fun e => {e.dualEnds.1, e.dualEnds.2}) := by
    intro k
    apply Finset.mem_biUnion.mpr
    exact ⟨E k, hEmem k, by rcases hUend k with h | h <;> simp [h]⟩
  have hrep : ∃ J, 0 < J ∧ ∃ j, j < J ∧ U j = U J := by
    set Vγ := γ.biUnion (fun e => {e.dualEnds.1, e.dualEnds.2}) with hVγ
    obtain ⟨a, ha, b, hb, hab, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (s := Finset.range (Vγ.card + 1)) (t := Vγ)
        (by simp) (fun k _ => hUmem k)
    rcases Nat.lt_or_ge a b with hlt | hge
    · exact ⟨b, by omega, a, hlt, heq⟩
    · have hba : b < a := by omega
      exact ⟨a, by omega, b, hba, heq.symm⟩
  set J := Nat.find hrep with hJ
  obtain ⟨hJpos, j₀, hj₀J, hUJ⟩ := Nat.find_spec hrep
  -- minimality of J: U is injective below J
  have hinj : ∀ a b, a < J → b < J → U a = U b → a = b := by
    intro a b ha hb heq
    by_contra hne'
    rcases Nat.lt_or_ge a b with hlt | hge
    · exact Nat.find_min hrep hb ⟨by omega, a, hlt, heq⟩
    · have hba : b < a := by omega
      exact Nat.find_min hrep ha ⟨by omega, b, hba, heq.symm⟩
  -- the segment word
  have hWalk := walk_of_seq U E dd (fun k => ⟨hd1 k, hd2 k⟩) (J - j₀) j₀
  have hJj : j₀ + (J - j₀) = J := by omega
  rw [hJj] at hWalk
  refine ⟨U j₀, (List.range (J - j₀)).map (fun t => dd (j₀ + t)), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hWalk.1]
    exact hUJ.symm
  · -- Nodup of the traversed edges
    rw [hWalk.2]
    refine List.Nodup.map_on ?_ (List.nodup_range)
    intro s hs t ht hEeq
    rw [List.mem_range] at hs ht
    by_contra hst
    have haux : ∀ k m, j₀ < k → k < m → m ≤ J → E k = E m → False := by
      intro k m hjk hkm hmJ heq
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hk'1 := (hstep k').1
      have hk'2 := hUend (k' + 1)
      have hm'1 := (hstep m').1
      have hm'2 := hUend (m' + 1)
      have hneq_m : U m' ≠ U (m' + 1) := by
        rw [(hstep m').2.2]
        exact (otherEnd_ne _ _).symm
      rw [heq] at hk'1 hk'2
      have hc1 : U k' = U m' ∨ U k' = U (m' + 1) := end_cases hneq_m hm'1 hm'2 hk'1
      have hc2 : U (k' + 1) = U m' ∨ U (k' + 1) = U (m' + 1) :=
        end_cases hneq_m hm'1 hm'2 hk'2
      rcases hc1 with h1 | h1
      · have := hinj k' m' (by omega) (by omega) h1
        omega
      · by_cases hmJ' : m' + 1 = J
        · have hUm' : U (m' + 1) = U j₀ := by rw [hmJ']; exact hUJ.symm
          have hkj : k' = j₀ :=
            hinj k' j₀ (by omega) (by omega) (by rw [h1, hUm'])
          rcases hc2 with h2 | h2
          · have hkm' : k' + 1 = m' := hinj (k' + 1) m' (by omega) (by omega) h2
            -- consecutive: contradicts the no-backtracking construction
            have := (hstep (k' + 1)).2.1
            rw [← hkm'] at heq
            exact this heq.symm
          · have : k' + 1 = j₀ :=
              hinj (k' + 1) j₀ (by omega) (by omega) (by rw [h2, hUm'])
            omega
        · have := hinj k' (m' + 1) (by omega) (by omega) h1
          omega
    rcases Nat.lt_or_ge s t with hlt | hge
    · exact haux (j₀ + s + 1) (j₀ + t + 1) (by omega) (by omega) (by omega) hEeq
    · have hts : t < s := by omega
      exact haux (j₀ + t + 1) (j₀ + s + 1) (by omega) (by omega) (by omega) hEeq.symm
  · -- nonempty word
    intro hnil
    have : ((List.range (J - j₀)).map (fun t => dd (j₀ + t))).length = J - j₀ := by simp
    rw [hnil] at this
    simp at this
    omega
  · -- edge set contained in γ
    intro e he
    simp only [walkFinset, List.mem_toFinset] at he
    rw [hWalk.2] at he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
    exact hEmem _

/-! ## Parity selection -/

private theorem exists_cycleWalk_In_one_aux (n : ℕ) :
    ∀ γ : Finset Edge, γ.card ≤ n → IsEven γ → ∀ z : Site, In γ z = 1 →
      ∃ v w, IsCycleWalk v w ∧ walkFinset v w ⊆ γ ∧ In (walkFinset v w) z = 1 := by
  induction n with
  | zero =>
    intro γ hcard hγ z h1
    have hγe : γ = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hγe
    have h0 : In (∅ : Finset Edge) z = 0 := by simp [In]
    rw [h0] at h1
    exact absurd h1 (by decide)
  | succ n ih =>
    intro γ hcard hγ z h1
    have hne : γ.Nonempty := by
      rcases γ.eq_empty_or_nonempty with rfl | h
      · have h0 : In (∅ : Finset Edge) z = 0 := by simp [In]
        rw [h0] at h1
        exact absurd h1 (by decide)
      · exact h
    obtain ⟨v, w, hcw, hsub⟩ := exists_cycleWalk hγ hne
    by_cases hIn : In (walkFinset v w) z = 1
    · exact ⟨v, w, hcw, hsub, hIn⟩
    · have hIn0 : In (walkFinset v w) z = 0 :=
        (In_eq_zero_or_one _ z).resolve_right hIn
      have hκne : (walkFinset v w).Nonempty := by
        obtain ⟨-, -, hwne⟩ := hcw
        rcases w with _ | ⟨d, w'⟩
        · exact absurd rfl hwne
        · exact ⟨stepEdge v d, by simp [walkFinset, walkEdges]⟩
      have heven' : IsEven (γ \ walkFinset v w) :=
        isEven_sdiff hsub hγ (isEven_walkFinset hcw)
      have hIn' : In (γ \ walkFinset v w) z = 1 := by
        rw [In_sdiff hsub, h1, hIn0, add_zero]
      have hcard' : (γ \ walkFinset v w).card ≤ n := by
        have h1' : (walkFinset v w).card ≤ γ.card := Finset.card_le_card hsub
        have h2' : 0 < (walkFinset v w).card := Finset.card_pos.mpr hκne
        rw [Finset.card_sdiff_of_subset hsub]
        omega
      obtain ⟨v', w', hcw', hsub', hIn''⟩ := ih (γ \ walkFinset v w) hcard' heven' z hIn'
      exact ⟨v', w', hcw', hsub'.trans (Finset.sdiff_subset), hIn''⟩

/-- Cycle extraction with parity selection: from an even edge set with crossing
parity `1` at `z`, extract a cycle walk inside it that still has crossing parity
`1` at `z`. -/
theorem exists_cycleWalk_In_one {γ : Finset Edge} (hγ : IsEven γ) {z : Site}
    (h1 : In γ z = 1) :
    ∃ v w, IsCycleWalk v w ∧ walkFinset v w ⊆ γ ∧ In (walkFinset v w) z = 1 :=
  exists_cycleWalk_In_one_aux γ.card γ le_rfl hγ z h1

/-! ## Extraction of an anchored cycle -/

/-- **Anchored cycle extraction.**  From an even edge set with crossing parity
`1` at the origin one can extract a cycle walk contained in it, anchored on the
positive horizontal half-axis, with the crossing-position bound `2k + 2 ≤ ℓ`.
This combines the contour-decomposition Lemma `lem:contour-decomp`, the
surrounding Lemma `lem:surround` and the crossing Lemma `lem:cross` of the LaTeX
companion document. -/
theorem exists_anchored_cycle {γ : Finset Edge} (he : IsEven γ)
    (h1 : In γ ((0 : ℤ), (0 : ℤ)) = 1) :
    ∃ (k : ℕ) (w : List Dir),
      IsCycleWalk ((k : ℤ), (-1 : ℤ)) (Dir.U :: w) ∧
      walkFinset ((k : ℤ), (-1 : ℤ)) (Dir.U :: w) ⊆ γ ∧
      2 * k + 2 ≤ (Dir.U :: w).length := by
  classical
  obtain ⟨v, w, hcw, hsub, hIn⟩ := exists_cycleWalk_In_one he h1
  -- the crossing filter is odd, hence nonempty: pick an anchor edge `H m₀ 0`, `0 ≤ m₀`
  have hodd : Odd (((walkFinset v w).filter (CrossesRight ((0 : ℤ), (0 : ℤ)))).card) := by
    simp only [In] at hIn
    exact ZMod.natCast_eq_one_iff_odd.mp hIn
  have hfne : ((walkFinset v w).filter (CrossesRight ((0 : ℤ), (0 : ℤ)))).Nonempty := by
    rw [← Finset.card_pos]
    obtain ⟨t, ht⟩ := hodd
    omega
  obtain ⟨e₀, he₀⟩ := hfne
  rw [Finset.mem_filter] at he₀
  obtain ⟨he₀κ, he₀cross⟩ := he₀
  obtain ⟨m₀, b₀, rfl⟩ : ∃ m b, e₀ = Edge.H m b := by
    cases e₀ with
    | H m b => exact ⟨m, b, rfl⟩
    | V m b => exact absurd he₀cross (by simp [CrossesRight])
  have hcr : b₀ = 0 ∧ 0 ≤ m₀ := he₀cross
  obtain ⟨rfl, hm₀⟩ := hcr
  -- there is also an edge `H m' 0 ∈ κ` with `m' ≤ -1` (else the row count is odd)
  have hleft : ∃ m', Edge.H m' 0 ∈ walkFinset v w ∧ m' ≤ -1 := by
    by_contra hno
    simp only [not_exists, not_and] at hno
    have hfeq : (walkFinset v w).filter (CrossesRight ((0 : ℤ), (0 : ℤ)))
        = (walkFinset v w).filter (InRow 0) := by
      apply Finset.filter_congr
      intro e hemem
      cases e with
      | H m c =>
        show (c = 0 ∧ 0 ≤ m) ↔ c = 0
        constructor
        · rintro ⟨hc, -⟩
          exact hc
        · intro hc
          subst hc
          have := hno m hemem
          exact ⟨rfl, by omega⟩
      | V m c => show False ↔ False; rfl
    rw [hfeq] at hodd
    have heven := rowCount_even (isEven_walkFinset hcw) 0
    exact (Nat.not_odd_iff_even.mpr heven) hodd
  -- re-root the walk at `(m₀, -1)` with first edge `H m₀ 0`
  have he₀edges : Edge.H m₀ 0 ∈ walkEdges v w := List.mem_toFinset.mp he₀κ
  have hx1 : ((m₀ : ℤ), (-1 : ℤ)) = (Edge.H m₀ 0).dualEnds.1 := by
    simp [Edge.dualEnds]
  obtain ⟨d, w', hcw', hsd, hperm⟩ := exists_reroot hcw he₀edges (Or.inl hx1)
  -- the first step must be `U`
  have hdU : d = Dir.U := by
    cases d
    case U => rfl
    case D =>
      exfalso
      have hDD : (Edge.H m₀ (-1)) = Edge.H m₀ 0 := hsd
      injection hDD with h₁ h₂
      omega
    case L => exact absurd hsd (by simp [stepEdge])
    case R => exact absurd hsd (by simp [stepEdge])
  subst hdU
  -- conclude with `k := m₀.toNat`
  have hcast : ((m₀.toNat : ℕ) : ℤ) = m₀ := Int.toNat_of_nonneg hm₀
  have hfinEq : walkFinset ((m₀ : ℤ), (-1 : ℤ)) (Dir.U :: w') = walkFinset v w :=
    List.toFinset_eq_of_perm _ _ hperm
  refine ⟨m₀.toNat, w', ?_, ?_, ?_⟩
  · rw [hcast]
    exact hcw'
  · rw [hcast, hfinEq]
    exact hsub
  · -- the length bound
    obtain ⟨m', hm'mem, hm'le⟩ := hleft
    have hm'edges : Edge.H m' 0 ∈ walkEdges ((m₀ : ℤ), (-1 : ℤ)) (Dir.U :: w') := by
      rw [hperm.mem_iff]
      exact List.mem_toFinset.mp hm'mem
    obtain ⟨w₁, d'', w₂, hsplit, hed''⟩ := exists_split_of_mem_walkEdges hm'edges
    set z : DualV := walkEnd ((m₀ : ℤ), (-1 : ℤ)) w₁ with hz
    have hzfst : z.1 = m' := by
      have hzend : z = (Edge.H m' 0).dualEnds.1 ∨ z = (Edge.H m' 0).dualEnds.2 := by
        rw [hed'']
        exact (mem_dualEnds_stepEdge z d'' z).mpr (Or.inl rfl)
      rcases hzend with h | h <;> rw [h] <;> simp [Edge.dualEnds]
    have hb1 := walkEnd_fst_bounds ((m₀ : ℤ), (-1 : ℤ)) w₁
    rw [← hz] at hb1
    have hsuf : walkEnd z (d'' :: w₂) = ((m₀ : ℤ), (-1 : ℤ)) := by
      have h0 := hcw'.1
      rw [hsplit, walkEnd_append, ← hz] at h0
      exact h0
    have hb2 := walkEnd_fst_bounds z (d'' :: w₂)
    rw [hsuf] at hb2
    have hlen : (Dir.U :: w').length = w₁.length + (w₂.length + 1) := by
      rw [hsplit]
      simp
    simp only [List.length_cons] at hb2
    rw [hzfst] at hb1 hb2
    omega

end Peierls
