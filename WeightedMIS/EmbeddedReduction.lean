module

public import WeightedMIS.EmbeddedDimensions
public import WeightedMIS.ColumnEncoding
public import WeightedMIS.KernelBasis
public import WeightedMIS.EdgeTransport
public import WeightedMIS.Reduction

/-!
# The assembled mathematical reduction for a connected embedded residual graph

Starting with an actual finite polygon-side embedding and an all-half optimal
rational weighted instance, this file derives the edge costs, actual local
stub columns, bounded supplementary rows, odd row, minimum search path, and a
maximum-weight independent set for the original vertex weights. No matrix,
rank, kernel-spanning, dual-cost, or successful-output hypothesis is supplied.
The number of supplementary coordinates satisfies the derived genus/odd-face
bound, with the orientable sharpening. This is mathematical correctness and
attainment; an executable bit-operation bound is a separate theorem.
-/

@[expose] public section

namespace WeightedMIS.EmbeddedReduction

open Matrix WeightedMIS.Walks WeightedMIS.EmbeddingFaces

variable {V E F : Type*} {left right : E → V}
variable [Fintype V] [Fintype E] [Fintype F]
variable [DecidableEq V] [DecidableEq E] [DecidableEq F]

/-- Actual facial columns and a bounded integral complement supply all the
kernel equations, with exactly the derived number of coordinates. -/
theorem exists_search_matrices (M : CellularEmbedding left right F)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    ∃ C : E → Column (Faces.EvenFaces M.faces),
      ∃ W : E → Fin (coordinateCount M) → ℤ,
        Reduction.localMatrix C = Faces.matrix M.faces ∧
        (∀ e i, |W e i| ≤ 2) ∧
        Submodule.span ℚ (Set.range (Reduction.localMatrix C) ∪
          Set.range (Reduction.globalMatrix W)) =
            LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  obtain ⟨C, hC⟩ := ColumnEncoding.exists_columns (Faces.integerMatrix M.faces)
    (Faces.column_natAbs_sum_le_two M.faces M.twoSides)
  have hlocal : Reduction.localMatrix C = Faces.matrix M.faces := by
    ext r e
    change (columnVector (C e) r : ℚ) = (Faces.integerMatrix M.faces r e : ℚ)
    rw [hC e r]
  have h := KernelBasis.bounded_complement left right hc hnb (faceRowSpace M)
    (Faces.row_span_le_left_kernel M.faces)
  rw [faceRowSpace_finrank] at h
  obtain ⟨U, hU, hspan⟩ := h
  let W : E → Fin (coordinateCount M) → ℤ := fun e i => U i e
  refine ⟨C, W, hlocal, (fun e i => (hU i).2 e), ?_⟩
  rw [hlocal, Submodule.span_union]
  exact hspan

omit [Fintype F] [DecidableEq E] [DecidableEq F] in
/-- The constructed edge costs have half the total original vertex weight. -/
theorem totalCost_eq_half_weight (cost : E → ℚ) (w : V → ℚ)
    (hw : ∀ v, Slack.vertexWeight left right cost v = w v) :
    Slack.totalCost cost = (∑ v, w v) / 2 := by
  have htotal : (∑ v, w v) = 2 * Slack.totalCost cost := by
    calc
      (∑ v, w v) = ∑ v, Slack.vertexWeight left right cost v := by
        apply Finset.sum_congr rfl
        intro v _
        exact (hw v).symm
      _ = 2 * Slack.totalCost cost := by
        simp only [Slack.vertexWeight, Slack.totalCost, Finset.sum_add_distrib]
        rw [Finset.sum_comm, Finset.sum_comm (f := fun v e => if right e = v then cost e else 0)]
        simp
        ring
  linarith

/-- Complete search data and an attained solution for the original vertex
weights. All matrix and cost identities are outputs of the reduction. -/
def Recovery (M : CellularEmbedding left right F) (w : V → ℚ) : Prop :=
  ∃ C : E → Column (Faces.EvenFaces M.faces),
    ∃ W : E → Fin (coordinateCount M) → ℤ,
      ∃ cost : E → ℚ,
        Reduction.localMatrix C = Faces.matrix M.faces ∧
        (∀ e i, |W e i| ≤ 2) ∧
        Submodule.span ℚ (Set.range (Reduction.localMatrix C) ∪
          Set.range (Reduction.globalMatrix W)) =
            LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin ∧
        (∀ e, 0 ≤ cost e) ∧
        (∀ v, Slack.vertexWeight left right cost v = w v) ∧
        ∃ root : V, ∃ π : E → ℤ, IntegerSlacks.OddRow left right root π ∧
          ∃ path : Reduction.SearchPath C W π,
            SearchOptimum.pathLength path <
              2 * (4 * Fintype.card E + 1) ^ coordinateCount M *
                (1 + (2 * Fintype.card (Faces.EvenFaces M.faces) + 1) ^ 2) ∧
            (∀ q : Reduction.SearchPath C W π, path.cost cost ≤ q.cost cost) ∧
            ∃ x : V → ℤ, Slack.Feasible left right x ∧
              (∀ e, Slack.slack left right x e = (projection path.labels e : ℤ)) ∧
              Slack.Independent left right (Slack.threshold x) ∧
              (∀ J : Finset V, Slack.Independent left right J →
                (∑ v ∈ J, w v) ≤ ∑ v ∈ Slack.threshold x, w v) ∧
              (∑ v ∈ Slack.threshold x, w v) = (∑ v, w v) / 2 - path.cost cost

/-- The complete mathematical search reduction is obtained solely from the
actual embedding, connected nonbipartiteness, and all-half LP optimality. -/
theorem exists_recovery (M : CellularEmbedding left right F)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (w : V → ℚ)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2)) :
    Recovery M w := by
  obtain ⟨C, W, hC, hW, hspan⟩ := exists_search_matrices M hc hnb
  obtain ⟨cost, hn, hw⟩ := EdgeTransport.edge_costs_of_half_optimal left right w ho
  obtain ⟨root, π, hπ, path, hlen, hmin, x, hx, hs, hI, hmax, heq⟩ :=
    Reduction.exists_optimal_search_recovery left right hc hnb C W hspan hW cost hn
  refine ⟨C, W, cost, hC, hW, hspan, hn, hw, root, π, hπ,
    path, ?_, hmin, x, hx, hs, hI, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using hlen
  · intro J hJ
    simpa only [Slack.setWeight, hw] using hmax J hJ
  · have htotal := totalCost_eq_half_weight cost w hw
    simpa only [Slack.setWeight, hw, htotal] using heq

/-- Connected embedded all-half instances have the derived parameter bound
and an actual attained finite-search recovery of their original weighted MIS. -/
theorem embedded_half_reduction (M : CellularEmbedding left right F)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (w : V → ℚ)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2)) :
    coordinateCount M ≤ Parameters.exponent M.eulerGenus (oddFaceCount M) ∧
      Recovery M w :=
  ⟨coordinateCount_le_exponent M hc hnb, exists_recovery M hc hnb w ho⟩

/-- The same actual reduction obeys the sharper exponent in the orientable case. -/
theorem orientable_embedded_half_reduction (M : CellularEmbedding left right F)
    (O : M.sides.Orientation)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (w : V → ℚ)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2)) :
    coordinateCount M ≤ Parameters.orientableExponent M.eulerGenus (oddFaceCount M) ∧
      Recovery M w :=
  ⟨coordinateCount_le_orientableExponent M O hc hnb, exists_recovery M hc hnb w ho⟩

end WeightedMIS.EmbeddedReduction
