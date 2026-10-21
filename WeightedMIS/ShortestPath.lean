module

public import Mathlib

/-!
# Minimum-cost paths in finite directed multigraphs

The vertices and arc labels are explicit finite types.  Source and target maps
retain loops and parallel arcs, and a walk is a list of these labels.

For nonnegative rational costs, cycle erasure produces a simple path of no
greater cost.  The finite family of simple paths therefore contains a global
cost minimizer whenever the target is reachable.  This is the existence and
recovery foundation used by the shortest-path reduction in Lemma 10.  No
running-time or Dijkstra implementation claim is made here.
-/

public section

namespace WeightedMIS.ShortestPath

variable {V A : Type*}

/-- An arc list is a directed walk from `s` to `t` if all incidences match.
The empty list is a walk exactly when its two endpoints coincide. -/
@[expose] def IsWalk (source target : A → V) (s t : V) : List A → Prop
  | [] => s = t
  | e :: p => source e = s ∧ IsWalk source target (target e) t p

/-- The visited vertices, including both endpoints of a valid walk. -/
@[expose] def vertices (target : A → V) (s : V) (p : List A) : List V :=
  s :: p.map target

/-- A simple path has no repeated visited vertex. -/
@[expose] def IsSimple (target : A → V) (s : V) (p : List A) : Prop :=
  (vertices target s p).Nodup

/-- The exact rational cost of an arc list, counted with multiplicity. -/
@[expose] def pathCost (cost : A → ℚ) (p : List A) : ℚ :=
  (p.map cost).sum

@[simp] theorem cost_nil (cost : A → ℚ) : pathCost cost [] = 0 := rfl

@[simp] theorem cost_cons (cost : A → ℚ) (e : A) (p : List A) :
    pathCost cost (e :: p) = cost e + pathCost cost p := rfl

@[simp] theorem cost_append (cost : A → ℚ) (p q : List A) :
    pathCost cost (p ++ q) = pathCost cost p + pathCost cost q := by
  simp [pathCost]

theorem cost_nonnegative (cost : A → ℚ) (hcost : ∀ e, 0 ≤ cost e)
    (p : List A) : 0 ≤ pathCost cost p := by
  induction p with
  | nil => simp
  | cons e p ih => simpa using add_nonneg (hcost e) ih

theorem walk_append (source target : A → V) {s u t : V} {p q : List A}
    (hp : IsWalk source target s u p) (hq : IsWalk source target u t q) :
    IsWalk source target s t (p ++ q) := by
  induction p generalizing s with
  | nil =>
    have hs : s = u := hp
    simpa [hs] using hq
  | cons e p ih =>
    exact ⟨hp.1, ih hp.2⟩

/-- A visited vertex splits a walk into a prefix and a suffix.  The suffix's
vertex trace is a sublist of the original trace. -/
theorem split_at_vertex (source target : A → V) {s t v : V} {p : List A}
    (hp : IsWalk source target s t p) (hv : v ∈ vertices target s p) :
    ∃ pre post : List A,
      p = pre ++ post ∧
      IsWalk source target s v pre ∧
      IsWalk source target v t post ∧
      (vertices target v post).Sublist (vertices target s p) := by
  induction p generalizing s with
  | nil =>
    have hvs : v = s := by simpa [vertices] using hv
    subst v
    exact ⟨[], [], rfl, rfl, hp, List.Sublist.refl _⟩
  | cons e p ih =>
    rcases List.mem_cons.mp hv with hvs | hv
    · subst v
      exact ⟨[], e :: p, rfl, rfl, hp, List.Sublist.refl _⟩
    · have hv' : v ∈ vertices target (target e) p := hv
      obtain ⟨pre, post, heq, hpre, hpost, hsub⟩ := ih hp.2 hv'
      refine ⟨e :: pre, post, by simp [heq], ⟨hp.1, hpre⟩, hpost, ?_⟩
      exact hsub.cons s

/-- Deleting a closed intermediate portion preserves a walk and cannot
increase its cost when all arc costs are nonnegative. -/
theorem remove_closed_portion (source target : A → V) (cost : A → ℚ)
    (hcost : ∀ e, 0 ≤ cost e) {s u t : V} {pre cycle post : List A}
    (hpre : IsWalk source target s u pre)
    (hcycle : IsWalk source target u u cycle)
    (hpost : IsWalk source target u t post) :
    IsWalk source target s t (pre ++ post) ∧
      IsWalk source target s t (pre ++ cycle ++ post) ∧
      pathCost cost (pre ++ post) ≤ pathCost cost (pre ++ cycle ++ post) := by
  refine ⟨walk_append source target hpre hpost,
    walk_append source target (walk_append source target hpre hcycle) hpost, ?_⟩
  have hc := cost_nonnegative cost hcost cycle
  simp only [cost_append]
  linarith

/-- Cycle erasure can retain a sublist of the original arc occurrences,
preserving their order. No cost function is needed for this stronger witness. -/
theorem exists_simple_path_sublist (source target : A → V) {s t : V} {p : List A}
    (hp : IsWalk source target s t p) :
    ∃ q : List A, IsWalk source target s t q ∧ IsSimple target s q ∧ q.Sublist p := by
  classical
  induction p generalizing s with
  | nil => exact ⟨[], hp, by simp [IsSimple, vertices], List.Sublist.refl _⟩
  | cons e p ih =>
    obtain ⟨q, hq, hsimple, hsub⟩ := ih hp.2
    by_cases hs : s ∈ vertices target (target e) q
    · obtain ⟨pre, post, heq, _, hpost, htrace⟩ :=
        split_at_vertex source target hq hs
      have hpostsub : post.Sublist q := by
        rw [heq]
        exact List.sublist_append_right pre post
      exact ⟨post, hpost, List.Nodup.sublist htrace hsimple,
        (hpostsub.trans hsub).cons e⟩
    · exact ⟨e :: q, ⟨hp.1, hq⟩, List.nodup_cons.mpr ⟨hs, hsimple⟩,
        hsub.cons_cons e⟩

/-- Cycle erasure, preserving endpoints and never increasing rational cost. -/
theorem exists_simple_path_le (source target : A → V) (cost : A → ℚ)
    (hcost : ∀ e, 0 ≤ cost e) {s t : V} {p : List A}
    (hp : IsWalk source target s t p) :
    ∃ q : List A, IsWalk source target s t q ∧ IsSimple target s q ∧
      pathCost cost q ≤ pathCost cost p := by
  classical
  induction p generalizing s with
  | nil =>
    exact ⟨[], hp, by simp [IsSimple, vertices], le_rfl⟩
  | cons e p ih =>
    obtain ⟨q, hq, hsimple, hcostq⟩ := ih hp.2
    by_cases hs : s ∈ vertices target (target e) q
    · obtain ⟨pre, post, heq, _, hpost, hsub⟩ :=
        split_at_vertex source target hq hs
      refine ⟨post, hpost, List.Nodup.sublist hsub hsimple, ?_⟩
      have hpre := cost_nonnegative cost hcost pre
      have he := hcost e
      have hcpost : pathCost cost post ≤ pathCost cost q := by
        rw [heq, cost_append]
        linarith
      simp only [cost_cons]
      linarith
    · refine ⟨e :: q, ⟨hp.1, hq⟩, ?_, ?_⟩
      · exact List.nodup_cons.mpr ⟨hs, hsimple⟩
      · simpa using add_le_add_left hcostq (cost e)

/-- A simple path cannot repeat an arc label. -/
theorem simple_arc_nodup (target : A → V) {s : V} {p : List A}
    (hp : IsSimple target s p) : p.Nodup :=
  List.Nodup.of_map target (List.nodup_cons.mp hp).2

/-- In a finite vertex set, a simple path uses fewer arcs than vertices. -/
theorem simple_length_lt_card [Fintype V] (target : A → V) {s : V} {p : List A}
    (hp : IsSimple target s p) : p.length < Fintype.card V := by
  have h := List.Nodup.length_le_card hp
  simp only [vertices, List.length_cons, List.length_map] at h
  omega

/-- A reachable pair of vertices in a finite directed multigraph admits a
globally minimum-cost path.  The witness retains the actual arc labels, has
no repeated vertex, and uses fewer arcs than there are vertices.

The finite minimization is over the explicit finite type of non-repeating
arc lists, filtered by walk validity and simplicity.  Cycle erasure compares
this finite minimum with every walk, regardless of length or repetitions.
-/
theorem exists_minimum_cost_path [Fintype V] [Fintype A]
    (source target : A → V) (cost : A → ℚ) (hcost : ∀ e, 0 ≤ cost e)
    (s t : V) (hreachable : ∃ p : List A, IsWalk source target s t p) :
    ∃ p : List A,
      IsWalk source target s t p ∧
      IsSimple target s p ∧
      p.length < Fintype.card V ∧
      ∀ q : List A, IsWalk source target s t q → pathCost cost p ≤ pathCost cost q := by
  classical
  obtain ⟨p₀, hp₀⟩ := hreachable
  obtain ⟨q₀, hq₀, hs₀, _⟩ := exists_simple_path_le source target cost hcost hp₀
  let candidates : Finset {p : List A // p.Nodup} :=
    Finset.univ.filter fun p => IsWalk source target s t p.val ∧ IsSimple target s p.val
  let q₀' : {p : List A // p.Nodup} := ⟨q₀, simple_arc_nodup target hs₀⟩
  have hmem : q₀' ∈ candidates := by simp [candidates, q₀', hq₀, hs₀]
  obtain ⟨p, hpc, hmin⟩ := Finset.exists_min_image candidates
    (fun p => pathCost cost p.val) ⟨q₀', hmem⟩
  have hp := (Finset.mem_filter.mp hpc).2
  refine ⟨p.val, hp.1, hp.2, simple_length_lt_card target hp.2, ?_⟩
  intro q hq
  obtain ⟨r, hr, hsr, hcostr⟩ := exists_simple_path_le source target cost hcost hq
  let r' : {p : List A // p.Nodup} := ⟨r, simple_arc_nodup target hsr⟩
  have hrmem : r' ∈ candidates := by simp [candidates, r', hr, hsr]
  exact (hmin r' hrmem).trans hcostr

end WeightedMIS.ShortestPath
