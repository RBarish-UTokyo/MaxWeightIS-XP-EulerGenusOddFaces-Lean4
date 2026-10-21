module

public import WeightedMIS.ShortestPath

/-!
# Deterministic supported-cycle search

The successor of an arc is the first supported outgoing arc in a supplied
finite enumeration. Following successors until the first repeated arc yields
a nonempty closed walk with distinct arcs. The search uses at most one more
successor step than the enumeration length and never expands flow copies.
-/

@[expose] public section

namespace WeightedMIS.CycleSearch

open ShortestPath

variable {V A : Type*} [DecidableEq V] [DecidableEq A]

/-- First supported outgoing arc, falling back only if no such arc exists. -/
def successor (source target : A → V) (active : A → Bool) (enumeration : List A) (a : A) : A :=
  (enumeration.find? fun b => active b && decide (source b = target a)).getD a

omit [DecidableEq A] in
/-- The successor is supported and begins at the preceding target whenever
such an enumerated successor exists. -/
theorem successor_spec (source target : A → V) (active : A → Bool) (enumeration : List A)
    (a : A) (hex : ∃ b ∈ enumeration, active b = true ∧ source b = target a) :
    active (successor source target active enumeration a) = true ∧
      source (successor source target active enumeration a) = target a := by
  have hsome : (enumeration.find? fun b => active b && decide (source b = target a)).isSome := by
    apply List.find?_isSome.mpr
    simpa using hex
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
  have h := List.find?_some hb
  simpa [successor, hb] using h

/-- Keep the suffix beginning with the first occurrence of an arc. -/
def cycleSuffix (a : A) (seen : List A) : List A := seen.dropWhile fun b => decide (b ≠ a)

theorem cycleSuffix_sublist (a : A) (seen : List A) : (cycleSuffix a seen).Sublist seen :=
  List.dropWhile_sublist _

theorem cycleSuffix_ne_nil (a : A) (seen : List A) (ha : a ∈ seen) : cycleSuffix a seen ≠ [] := by
  induction seen with
  | nil => simp at ha
  | cons b seen ih =>
      by_cases h : b = a
      · subst b
        simp [cycleSuffix]
      · have hat : a ∈ seen := (List.mem_cons.mp ha).resolve_left (Ne.symm h)
        simpa [cycleSuffix, h] using ih hat

omit [DecidableEq V] in
/-- The suffix after a repeated arc starts at that arc's source and closes. -/
theorem cycleSuffix_walk (source target : A → V) (a : A) {s : V} (seen : List A)
    (hp : IsWalk source target s (source a) seen) (ha : a ∈ seen) :
    IsWalk source target (source a) (source a) (cycleSuffix a seen) := by
  induction seen generalizing s with
  | nil => simp at ha
  | cons b seen ih =>
      by_cases h : b = a
      · subst b
        have hs : source a = s := hp.1
        simpa [cycleSuffix, hs] using hp
      · have hat : a ∈ seen := (List.mem_cons.mp ha).resolve_left (Ne.symm h)
        simpa [cycleSuffix, h] using ih hp.2 hat

/-- Follow successors, stopping at the first repeated arc. -/
def search (next : A → A) : ℕ → A → List A → List A
  | 0, _, _ => []
  | fuel + 1, a, seen =>
      if a ∈ seen then cycleSuffix a seen else search next fuel (next a) (seen ++ [a])

omit [DecidableEq V] in
/-- A positive surplus of fuel over the remaining distinct arcs guarantees
that the deterministic search returns a supported simple-arc cycle. -/
theorem search_spec (source target : A → V) (active : A → Bool)
    (enumeration : List A) (hcover : ∀ a, active a = true → a ∈ enumeration)
    (next : A → A)
    (hnext : ∀ a, active a = true → active (next a) = true ∧ source (next a) = target a)
    (fuel : ℕ) (a : A) (seen : List A) (s : V)
    (ha : active a = true) (hseen : ∀ b ∈ seen, active b = true)
    (hn : seen.Nodup) (hp : IsWalk source target s (source a) seen)
    (hbig : enumeration.length < fuel + seen.length) :
    ∃ u, IsWalk source target u u (search next fuel a seen) ∧
      search next fuel a seen ≠ [] ∧ (search next fuel a seen).Nodup ∧
      ∀ b ∈ search next fuel a seen, active b = true := by
  induction fuel generalizing a seen s with
  | zero =>
      have hsubset : seen ⊆ enumeration := fun b hb => hcover b (hseen b hb)
      have hle := (List.subperm_of_subset hn hsubset).length_le
      omega
  | succ fuel ih =>
      by_cases hmem : a ∈ seen
      · simp only [search, hmem, ↓reduceIte]
        refine ⟨source a, cycleSuffix_walk source target a seen hp hmem,
          cycleSuffix_ne_nil a seen hmem, hn.sublist (cycleSuffix_sublist a seen), ?_⟩
        intro b hb
        exact hseen b ((cycleSuffix_sublist a seen).subset hb)
      · have hnexta := hnext a ha
        have hn' : (seen ++ [a]).Nodup := by
          simp only [List.nodup_append, hn, List.nodup_singleton, true_and, List.mem_singleton,
            forall_eq, ne_eq]
          intro b hb hba
          exact hmem (hba ▸ hb)
        have hs' : ∀ b ∈ seen ++ [a], active b = true := by
          intro b hb
          rcases List.mem_append.mp hb with hb | hb
          · exact hseen b hb
          · have heq : b = a := by simpa using hb
            subst b
            exact ha
        have hp' : IsWalk source target s (source (next a)) (seen ++ [a]) := by
          apply walk_append source target hp
          exact ⟨rfl, hnexta.2.symm⟩
        have hbig' : enumeration.length < fuel + (seen ++ [a]).length := by
          simp only [List.length_append, List.length_singleton]
          omega
        simpa only [search, hmem, ↓reduceIte] using
          ih (next a) (seen ++ [a]) s hnexta.1 hs' hn' hp' hbig'

/-- The fully specified deterministic cycle finder. -/
def findCycle (source target : A → V) (active : A → Bool) (enumeration : List A) (a : A) : List A :=
  search (successor source target active enumeration) (enumeration.length + 1) a []

/-- Correctness of deterministic cycle search on every nonempty supported
successor graph, with distinct returned arc labels. -/
theorem findCycle_spec (source target : A → V) (active : A → Bool)
    (enumeration : List A) (hcover : ∀ a, active a = true → a ∈ enumeration)
    (hnext : ∀ a, active a = true → ∃ b ∈ enumeration, active b = true ∧ source b = target a)
    (a : A) (ha : active a = true) :
    ∃ u, IsWalk source target u u (findCycle source target active enumeration a) ∧
      findCycle source target active enumeration a ≠ [] ∧
      (findCycle source target active enumeration a).Nodup ∧
      (findCycle source target active enumeration a).length ≤ enumeration.length ∧
      ∀ b ∈ findCycle source target active enumeration a, active b = true := by
  obtain ⟨u, hp, hne, hn, hs⟩ := search_spec source target active enumeration hcover
    (successor source target active enumeration)
    (fun b hb => successor_spec source target active enumeration b (hnext b hb))
    (enumeration.length + 1) a [] (source a) ha (by simp) (by simp) rfl (by simp)
  refine ⟨u, hp, hne, hn, ?_, hs⟩
  exact (List.subperm_of_subset hn (fun b hb => hcover b (hs b hb))).length_le

end WeightedMIS.CycleSearch
