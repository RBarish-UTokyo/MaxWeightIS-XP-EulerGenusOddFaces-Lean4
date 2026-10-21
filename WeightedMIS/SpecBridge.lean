module

public import WeightedMIS.SpecRegions
public import WeightedMIS.SpecDrawnCorner
public import WeightedMIS.SpecIndependence
public import WeightedMIS.ComputedDrawingParameters

/-!
# The solver's guarantees in statement terms

From a closed-surface map `A` and a drawing `D` placed in it, the internal
cellular embedding of `A`, the internal corner system of `D`, the drawn-edge
relabelling and the vertex map are constructed. The deterministic solver run
on the corner system read from `D` returns a maximum-weight independent set,
and every hard residual search uses at most `D(γ, k)` computed coordinates,
where `γ` and `k` are the statement Euler genus and odd-region count; on an
orientable surface the sharper exponent applies.
-/

@[expose] public section

namespace WeightedMIS.Spec

/-- The internal exponent is the statement exponent. -/
theorem exponent_eq (γ k : ℕ) : Parameters.exponent γ k = exponentD γ k := rfl

/-- The internal orientable exponent is the statement orientable exponent. -/
theorem orientableExponent_eq (γ k : ℕ) :
    Parameters.orientableExponent γ k = orientableExponentD γ k := rfl

/-- The Euler genus of a closed-surface map satisfies `V - E + F = 2 - γ`
exactly; the natural-number subtraction in its definition never truncates. -/
theorem Map.eulerGenus_identity (A : Map) (hA : A.IsClosedSurface) :
    A.eulerGenus + A.vertices + Nat.card A.Face = A.edges + 2 := by
  classical
  have h := (A.cellular hA).eulerGenus_identity (A.connected hA)
  rw [A.cellular_eulerGenus hA, Fintype.card_fin, Fintype.card_fin] at h
  rw [Nat.card_congr (A.faceEquiv hA), Nat.card_eq_fintype_card]
  exact h

namespace Drawing

/-- The internal ribbon of the drawing has exactly the drawing's corners. -/
theorem ribbon_corner {A : Map} (hA : A.IsClosedSurface) {D : Drawing} (W : D.In A)
    (x : Flag (Fin D.edges)) :
    (ribbon hA W).corner (Flag.equiv _ x) = Flag.equiv _ (D.corner x) :=
  ribbonOf_corner _ _ _ _ _ _ x

/-- Correctness and parameter bounds of the deterministic solver on a drawing
in a closed surface, with all parameters as defined in the statement. -/
theorem solve_spec (A : Map) (hA : A.IsClosedSurface) (D : Drawing) (W : D.In A)
    (weights : Fin D.vertices → ℚ) :
    let R := ribbon hA W
    let kept := ExecutableMIS.residualVertices (left := D.left) (right := D.right) weights
    D.IsMaximum weights (ExecutableMIS.solve R weights) ∧
      ∀ root : Fin (ComputedInduced.vertices kept).length,
        ¬ Incidence.Bipartite
          (ComputedComponents.localLeft (ComputedInduced.localLeft D.left D.right kept)
            (ComputedInduced.localRight D.left D.right kept) root)
          (ComputedComponents.localRight (ComputedInduced.localLeft D.left D.right kept)
            (ComputedInduced.localRight D.left D.right kept) root) →
        (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
          (ComputedInduced.localLeft D.left D.right kept)
          (ComputedInduced.localRight D.left D.right kept) root
          (ComputedInduced.ribbon D.left D.right kept R))).length ≤
            exponentD A.eulerGenus (A.oddRegionCount W.drawn) ∧
        (A.Orientable →
          (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
            (ComputedInduced.localLeft D.left D.right kept)
            (ComputedInduced.localRight D.left D.right kept) root
            (ComputedInduced.ribbon D.left D.right kept R))).length ≤
              orientableExponentD A.eulerGenus (A.oddRegionCount W.drawn)) := by
  classical
  intro R kept
  obtain ⟨h1, h2, h3⟩ := ComputedDrawing.solve_correct_and_parameters (A.cellular hA) R W.drawn
    (edgeEquiv W) W.vertexMap W.vertexMap_injective W.left_comm W.right_comm
    (ribbon_corner_map hA W) weights (A.connected hA)
  refine ⟨D.isMaximum_of weights _ h1 h2, fun root hnb => ?_⟩
  obtain ⟨b1, b2⟩ := h3 root hnb
  rw [A.cellular_eulerGenus hA, A.cellular_oddRegionCount hA] at b1 b2
  refine ⟨b1, fun hO => ?_⟩
  obtain ⟨O⟩ := Map.nonempty_orientation (hA := hA) hO
  exact b2 O

end Drawing

/-- The statement-to-solver bridge: for a drawing `D` in a closed-surface map
`A`, there is an internal corner system with exactly the corners of `D` on
which the deterministic solver is correct for all weights, and every hard
residual search has dimension at most `D(γ, k)` (and at most the orientable
exponent on an orientable surface). -/
theorem spec_bridge (A : Map) (hA : A.IsClosedSurface) (D : Drawing) (W : D.In A) :
    ∃ R : EmbeddingFaces.Ribbon D.left D.right,
      (∀ x : Flag (Fin D.edges), R.corner (Flag.equiv _ x) = Flag.equiv _ (D.corner x)) ∧
      ∀ weights : Fin D.vertices → ℚ,
        let kept := ExecutableMIS.residualVertices (left := D.left) (right := D.right) weights
        D.IsMaximum weights (ExecutableMIS.solve R weights) ∧
          ∀ root : Fin (ComputedInduced.vertices kept).length,
            ¬ Incidence.Bipartite
              (ComputedComponents.localLeft (ComputedInduced.localLeft D.left D.right kept)
                (ComputedInduced.localRight D.left D.right kept) root)
              (ComputedComponents.localRight (ComputedInduced.localLeft D.left D.right kept)
                (ComputedInduced.localRight D.left D.right kept) root) →
            (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
              (ComputedInduced.localLeft D.left D.right kept)
              (ComputedInduced.localRight D.left D.right kept) root
              (ComputedInduced.ribbon D.left D.right kept R))).length ≤
                exponentD A.eulerGenus (A.oddRegionCount W.drawn) ∧
            (A.Orientable →
              (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
                (ComputedInduced.localLeft D.left D.right kept)
                (ComputedInduced.localRight D.left D.right kept) root
                (ComputedInduced.ribbon D.left D.right kept R))).length ≤
                  orientableExponentD A.eulerGenus (A.oddRegionCount W.drawn)) :=
  ⟨Drawing.ribbon hA W, Drawing.ribbon_corner hA W, Drawing.solve_spec A hA D W⟩

end WeightedMIS.Spec
