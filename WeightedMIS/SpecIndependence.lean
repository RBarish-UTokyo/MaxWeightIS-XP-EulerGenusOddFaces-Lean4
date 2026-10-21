module

public import WeightedMIS.Spec
public import WeightedMIS.Persistence
public import WeightedMIS.EdgeTransport

/-!
# Statement independent sets are the internal ones

Statement independence forbids both endpoints of an edge; internally it is
stated for the symmetric adjacency of the edge endpoints. The statement weight
is a finite sum, internally a dot product with the indicator vector.
-/

@[expose] public section

namespace WeightedMIS.Spec

namespace Drawing

variable (D : Drawing)

theorem independent_iff (I : Finset (Fin D.vertices)) :
    D.Independent I ↔ Persistence.Independent (EdgeTransport.Adj D.left D.right) I := by
  constructor
  · rintro h u v ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ hu hv
    · exact h e ⟨hu, hv⟩
    · exact h e ⟨hv, hu⟩
  · intro h e ⟨hl, hr⟩
    exact h _ _ ⟨e, Or.inl ⟨rfl, rfl⟩⟩ hl hr

theorem weight_eq (w : Fin D.vertices → ℚ) (I : Finset (Fin D.vertices)) :
    Persistence.weight w I = ∑ v ∈ I, w v := by
  simp [Persistence.weight, Persistence.objective, Persistence.indicator, Finset.sum_ite_mem]

/-- The internal optimality statement is the statement maximality. -/
theorem isMaximum_of (w : Fin D.vertices → ℚ) (I : Finset (Fin D.vertices))
    (hI : Persistence.Independent (EdgeTransport.Adj D.left D.right) I)
    (hmax : ∀ J, Persistence.Independent (EdgeTransport.Adj D.left D.right) J →
      Persistence.weight w J ≤ Persistence.weight w I) :
    D.IsMaximum w I := by
  refine ⟨(D.independent_iff I).mpr hI, fun J hJ => ?_⟩
  rw [← D.weight_eq, ← D.weight_eq]
  exact hmax J ((D.independent_iff J).mp hJ)

end Drawing

end WeightedMIS.Spec
