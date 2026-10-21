module

public import WeightedMIS.ComputedKernel
public import WeightedMIS.RationalWidth

/-!
# Uniform widths throughout complement selection

Every membership test uses only the original integral rows and previously
retained integral candidates. Thus the general elimination width bound applies
at every actual recursive selection call with a uniform polynomial parameter.
-/

@[expose] public section

namespace WeightedMIS.ComplementWidth

open Matrix ComputedKernel DeterministicComplement RationalWidth

variable {m : ℕ}

theorem annihilator_fits (rows : List (Fin m → ℤ)) (B : ℕ)
    (hrows : ∀ r ∈ rows, ∀ j, (r j).natAbs ≤ 2 ^ B)
    (x : Fin m → ℚ) (hx : x ∈ annihilatorGenerators (rows.map rationalRow)) (j : Fin m) :
    Fits (x j) ((rows.length + m + 2 * B) * m + m ^ 2 + 1) := by
  rw [annihilatorGenerators_eq] at hx
  simp only [List.map_map, Function.comp_def] at hx
  exact EliminationCertificate.eliminateRows_coordinate_size rows B hrows x hx j

/-- The integer row lists at the actual recursive membership tests. -/
def stages (rows : List (Fin m → ℤ)) : List (Fin m → ℤ) → List (List (Fin m → ℤ))
  | [] => []
  | v :: vs =>
      rows :: if outside (rows.map rationalRow) (rationalRow v) then
        stages (v :: rows) vs else stages rows vs

theorem stages_bounds (rows candidates : List (Fin m → ℤ))
    (s : List (Fin m → ℤ)) (hs : s ∈ stages rows candidates) :
    s.length ≤ rows.length + candidates.length ∧
      ∀ r ∈ s, r ∈ rows ∨ r ∈ candidates := by
  induction candidates generalizing rows with
  | nil => simp [stages] at hs
  | cons v vs ih =>
      simp only [stages, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨by simp, fun r hr => Or.inl hr⟩
      · split at hs
        · obtain ⟨hlen, hmem⟩ := ih (v :: rows) hs
          refine ⟨by simp only [List.length_cons] at hlen ⊢; omega, ?_⟩
          intro r hr
          rcases hmem r hr with hm | hm
          · rcases List.mem_cons.mp hm with rfl | hm
            · exact Or.inr List.mem_cons_self
            · exact Or.inl hm
          · exact Or.inr (List.mem_cons_of_mem v hm)
        · obtain ⟨hlen, hmem⟩ := ih rows hs
          refine ⟨by simp only [List.length_cons]; omega, ?_⟩
          intro r hr
          exact (hmem r hr).imp_right (List.mem_cons_of_mem v)

/-- The annihilator vectors tested by every actual selection stage have a
single bound depending only on the original integer input dimensions. -/
theorem stage_annihilator_fits (rows candidates : List (Fin m → ℤ)) (B : ℕ)
    (hrows : ∀ r ∈ rows ++ candidates, ∀ j, (r j).natAbs ≤ 2 ^ B)
    (s : List (Fin m → ℤ)) (hs : s ∈ stages rows candidates)
    (x : Fin m → ℚ) (hx : x ∈ annihilatorGenerators (s.map rationalRow)) (j : Fin m) :
    Fits (x j) ((rows.length + candidates.length + m + 2 * B) * m + m ^ 2 + 1) := by
  obtain ⟨hlen, hmem⟩ := stages_bounds rows candidates s hs
  have hh := annihilator_fits s B (fun r hr => hrows r (List.mem_append.mpr (hmem r hr))) x hx j
  apply fits_mono hh
  have hmul := Nat.mul_le_mul_right m
    (Nat.add_le_add_right (Nat.add_le_add_right hlen m) (2 * B))
  omega

/-- All dot-product membership tests have polynomial transient widths. -/
theorem stage_dot_fits (rows candidates : List (Fin m → ℤ)) (B : ℕ)
    (hrows : ∀ r ∈ rows ++ candidates, ∀ j, (r j).natAbs ≤ 2 ^ B)
    (s : List (Fin m → ℤ)) (hs : s ∈ stages rows candidates)
    (v : Fin m → ℤ) (hv : v ∈ candidates)
    (x : Fin m → ℚ) (hx : x ∈ annihilatorGenerators (s.map rationalRow)) :
    Fits (dotProduct (rationalRow v) x)
      ((B + 1 + ((rows.length + candidates.length + m + 2 * B) * m + m ^ 2 + 1) + 1) * m + 1) := by
  apply fits_dot
  · intro j
    exact fits_int (v j) B (hrows v (List.mem_append_right _ hv) j)
  · exact stage_annihilator_fits rows candidates B hrows s hs x hx

/-- Execute selection while recording precisely the row lists supplied to
each membership test. -/
def selectTrace (rows : List (Fin m → ℤ)) : List (Fin m → ℤ) →
    List (Fin m → ℤ) × List (List (Fin m → ℤ))
  | [] => ([], [])
  | v :: vs =>
      if outside (rows.map rationalRow) (rationalRow v) then
        let r := selectTrace (v :: rows) vs
        (v :: r.1, rows :: r.2)
      else
        let r := selectTrace rows vs
        (r.1, rows :: r.2)

theorem selectTrace_spec (rows candidates : List (Fin m → ℤ)) :
    (selectTrace rows candidates).1 = selectInteger (rows.map rationalRow) candidates ∧
      (selectTrace rows candidates).2 = stages rows candidates := by
  induction candidates generalizing rows with
  | nil => exact ⟨rfl, rfl⟩
  | cons v vs ih =>
      by_cases h : outside (rows.map rationalRow) (rationalRow v) = true
      · simp only [selectTrace, selectInteger, stages, h, ↓reduceIte]
        simpa only [List.map_cons] using And.intro
          (congrArg (List.cons v) (ih (v :: rows)).1)
          (congrArg (List.cons rows) (ih (v :: rows)).2)
      · simp only [selectTrace, selectInteger, stages, h, Bool.false_eq_true, ↓reduceIte]
        exact ⟨(ih rows).1, congrArg (List.cons rows) (ih rows).2⟩

end WeightedMIS.ComplementWidth
