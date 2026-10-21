module

public import WeightedMIS.Walks
public import WeightedMIS.Decomposition
public import WeightedMIS.ShortestPath

/-!
# Bounded closed walks in a signed-stub graph

Erasing closed portions from the tail of a nonempty closed walk leaves a
nonempty closed walk with no repeated arc. A signed-stub graph has at most two
arcs of any edge label, so the resulting projection is bounded by two.
-/

@[expose] public section

namespace WeightedMIS.BoundedCycles

open WeightedMIS.Walks

variable {Row Edge : Type*}

/-- Arc labels with their orientations retained. -/
def arcs {C : Edge → Column Row} {u v : State Row} : Walk C u v → List (Arc C)
  | .nil _ => []
  | .cons a w => a :: arcs w

theorem labels_eq_map_arcs {C : Edge → Column Row} {u v : State Row}
    (w : Walk C u v) : w.labels = (arcs w).map (fun a => a.val.1) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [arcs, Walk.labels, ih]

theorem arcs_isWalk {C : Edge → Column Row} {u v : State Row}
    (w : Walk C u v) : ShortestPath.IsWalk (source C) (target C) u v (arcs w) := by
  induction w with
  | nil => rfl
  | cons a w ih => exact ⟨rfl, ih⟩

theorem walk_of_arcs (C : Edge → Column Row) {u v : State Row} (l : List (Arc C))
    (hl : ShortestPath.IsWalk (source C) (target C) u v l) :
    ∃ w : Walk C u v, arcs w = l := by
  induction l generalizing u with
  | nil =>
      have h : u = v := hl
      subst u
      exact ⟨.nil v, rfl⟩
  | cons a l ih =>
      have h : source C a = u := hl.1
      subst u
      obtain ⟨w, hw⟩ := ih hl.2
      exact ⟨.cons a w, by simp [arcs, hw]⟩

/-- Every nonempty closed walk contains a nonempty closed subwalk with distinct
arc labels. The sublist condition preserves every original multiplicity. -/
theorem extract_bounded_cycle (C : Edge → Column Row)
    {u : State Row} (w : Walk C u u) (hne : w.labels ≠ []) :
    ∃ c : ClosedWalk C, c.2.labels ≠ [] ∧ (arcs c.2).Nodup ∧
      (arcs c.2).Sublist (arcs w) := by
  classical
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons a w =>
      obtain ⟨q, hq, hs, hsub⟩ := ShortestPath.exists_simple_path_sublist
        (source C) (target C) (arcs_isWalk w)
      obtain ⟨c, hc⟩ := walk_of_arcs C (a :: q) ⟨rfl, hq⟩
      refine ⟨⟨source C a, c⟩, ?_, ?_, ?_⟩
      · rw [labels_eq_map_arcs, hc]
        simp
      · rw [hc]
        exact List.Nodup.of_map (target C) hs
      · rw [hc]
        exact hsub.cons_cons a

private theorem count_first (l : List (Edge × Bool)) [DecidableEq Edge] (e : Edge) :
    (l.map Prod.fst).count e = l.count (e, false) + l.count (e, true) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rcases a with ⟨f, b⟩
      cases b <;> by_cases h : f = e <;>
        simp_all [eq_comm] <;> omega

/-- At most two oriented arc labels lie over any one original edge label. -/
theorem projection_le_two [DecidableEq Edge] (C : Edge → Column Row)
    {u v : State Row} (w : Walk C u v) (hn : (arcs w).Nodup) (e : Edge) :
    projection w.labels e ≤ 2 := by
  classical
  have hval : ((arcs w).map Subtype.val).Nodup := hn.map Subtype.val_injective
  have h0 := List.nodup_iff_count_le_one.mp hval (e, false)
  have h1 := List.nodup_iff_count_le_one.mp hval (e, true)
  have hc := count_first ((arcs w).map Subtype.val) e
  rw [labels_eq_map_arcs]
  unfold projection
  simp only [List.map_map, Function.comp_def] at hc
  rw [hc]
  omega

/-- Every nonnegative integral signed-stub flow decomposes into closed walks
with distinct oriented arcs. Multiplicities are preserved exactly. -/
theorem decompose_bounded_flow [Fintype Row] [Fintype Edge]
    [DecidableEq Row] [DecidableEq Edge]
    (C : Edge → Column Row) (y : Edge → ℕ)
    (hz : ∀ r, (∑ e, columnVector (C e) r * (y e : ℤ)) = 0) :
    ∃ ws : List (ClosedWalk C),
      (∀ e, projection (ws.flatMap (fun w => w.2.labels)) e = y e) ∧
      ∀ w ∈ ws, (arcs w.2).Nodup := by
  classical
  by_cases hzero : ∀ e, y e = 0
  · exact ⟨[], by simp [projection, hzero], by simp⟩
  · obtain ⟨e, he⟩ := not_forall.mp hzero
    obtain ⟨ws, hproj, _⟩ := Decomposition.decompose_flow C y hz
    have hepos : 0 < projection (ws.flatMap (fun w => w.2.labels)) e := by
      rw [hproj]
      omega
    have he_mem : e ∈ ws.flatMap (fun w => w.2.labels) := List.count_pos_iff.mp hepos
    obtain ⟨w, hw, hew⟩ := List.mem_flatMap.mp he_mem
    have wne : w.2.labels ≠ [] := by intro h; simp [h] at hew
    obtain ⟨c, hcne, hcnd, hcsub⟩ := extract_bounded_cycle C w.2 wne
    have hlabels : c.2.labels.Sublist w.2.labels := by
      simpa only [← labels_eq_map_arcs] using hcsub.map (fun a => a.val.1)
    have hwsub : w.2.labels.Sublist (ws.flatMap (fun w => w.2.labels)) := by
      exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨w, hw, rfl⟩)
    have hle : ∀ e, projection c.2.labels e ≤ y e := by
      intro e
      rw [← hproj]
      exact (hlabels.trans hwsub).count_le e
    let rest : Edge → ℕ := fun e => y e - projection c.2.labels e
    have hrest_add (e : Edge) : rest e + projection c.2.labels e = y e :=
      Nat.sub_add_cancel (hle e)
    have hrest_cast (e : Edge) : (rest e : ℤ) = (y e : ℤ) -
        (projection c.2.labels e : ℤ) := by
      have h : (rest e : ℤ) + (projection c.2.labels e : ℤ) = (y e : ℤ) := by
        exact_mod_cast hrest_add e
      omega
    have hrest_zero : ∀ r, (∑ e, columnVector (C e) r * (rest e : ℤ)) = 0 := by
      intro r
      simp_rw [hrest_cast, mul_sub]
      rw [Finset.sum_sub_distrib, hz r, c.2.closed_projection_kernel r]
      omega
    obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil c.2.labels hcne
    have hpos : 0 < projection c.2.labels e₀ := List.count_pos_iff.mpr he₀
    have hless : (∑ e, rest e) < ∑ e, y e := by
      apply Finset.sum_lt_sum
      · intro e _
        exact Nat.sub_le _ _
      · refine ⟨e₀, Finset.mem_univ _, ?_⟩
        have h := hrest_add e₀
        omega
    obtain ⟨cs, hcs, hnd⟩ := decompose_bounded_flow C rest hrest_zero
    refine ⟨c :: cs, ?_, ?_⟩
    · intro e
      simp only [List.flatMap_cons, projection, List.count_append]
      change projection c.2.labels e + projection (cs.flatMap (fun w => w.2.labels)) e = y e
      rw [hcs]
      exact (Nat.add_comm _ _).trans (hrest_add e)
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hcnd
      · exact hnd w hw
termination_by ∑ e, y e

/-- Every integral signed-stub flow is a sum of integral kernel vectors with
entries between zero and two. This is a bounded-generation existence result. -/
theorem flow_generated_by_bounded_cycles [Fintype Row] [Fintype Edge]
    [DecidableEq Row] [DecidableEq Edge]
    (C : Edge → Column Row) (y : Edge → ℕ)
    (hz : ∀ r, (∑ e, columnVector (C e) r * (y e : ℤ)) = 0) :
    ∃ ws : List (ClosedWalk C),
      (∀ e, projection (ws.flatMap (fun w => w.2.labels)) e = y e) ∧
      ∀ w ∈ ws, ∀ e, projection w.2.labels e ≤ 2 := by
  obtain ⟨ws, hp, hn⟩ := decompose_bounded_flow C y hz
  exact ⟨ws, hp, fun w hw e => projection_le_two C w.2 (hn w hw) e⟩

end WeightedMIS.BoundedCycles
