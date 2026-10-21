module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

/-!
# Selecting a kernel complement from bounded generators

In a finite-dimensional space, a spanning set extends any subspace to the
whole space using exactly the difference of the dimensions. The selected
vectors belong to the original spanning set, so bounds on generators are
preserved. The proof does not assert a running-time bound for the selection.
-/

@[expose] public section

namespace WeightedMIS.Complement

open Submodule Module

variable {𝕂 M : Type*} [DivisionRing 𝕂] [AddCommGroup M] [Module 𝕂 M]
    [FiniteDimensional 𝕂 M]

private theorem exists_extension_length (K : Submodule 𝕂 M) (S : Set M)
    (hS : span 𝕂 S = K) (n : ℕ) :
    ∀ P : Submodule 𝕂 M, P ≤ K → finrank 𝕂 K - finrank 𝕂 P = n →
      ∃ f : Fin n → M, (∀ i, f i ∈ S) ∧ P ⊔ span 𝕂 (Set.range f) = K := by
  classical
  induction n with
  | zero =>
      intro P hPK hn
      have heq : P = K := eq_of_le_of_finrank_le hPK (by omega)
      subst P
      refine ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩
      simp
  | succ n ih =>
      intro P hPK hn
      have hne : P ≠ K := by intro h; subst P; simp at hn
      have hex : ∃ v ∈ S, v ∉ P := by
        by_contra! h
        have hKP : K ≤ P := by rw [← hS]; exact span_le.mpr h
        exact hne (le_antisymm hPK hKP)
      obtain ⟨v, hvS, hvP⟩ := hex
      let P' : Submodule 𝕂 M := P ⊔ span 𝕂 {v}
      have hP'K : P' ≤ K := by
        apply sup_le hPK
        apply span_le.mpr
        intro x hx
        have hxv : x = v := Set.mem_singleton_iff.mp hx
        subst x
        rw [← hS]
        exact subset_span hvS
      have hdim : finrank 𝕂 P' = finrank 𝕂 P + 1 := finrank_sup_span_singleton hvP
      have hn' : finrank 𝕂 K - finrank 𝕂 P' = n := by
        have hle := Submodule.finrank_mono hPK
        omega
      obtain ⟨f, hf, hspan⟩ := ih P' hP'K hn'
      refine ⟨Matrix.vecCons v f, ?_, ?_⟩
      · intro i
        refine Fin.cases hvS (fun j => ?_) i
        exact hf j
      · rw [Matrix.range_cons, span_union]
        exact (sup_assoc P (span 𝕂 {v}) (span 𝕂 (Set.range f))).symm.trans hspan

/-- Exactly the codimension many members of the given spanning set suffice
to complete a specified subspace. -/
theorem exists_fin_complement (P K : Submodule 𝕂 M) (hPK : P ≤ K)
    (S : Set M) (hS : span 𝕂 S = K) :
    ∃ f : Fin (finrank 𝕂 K - finrank 𝕂 P) → M,
      (∀ i, f i ∈ S) ∧ P ⊔ span 𝕂 (Set.range f) = K :=
  exists_extension_length K S hS _ P hPK rfl

end WeightedMIS.Complement
