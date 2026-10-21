module

public import WeightedMIS.ComputedFaceMatrix
public import WeightedMIS.DeterministicKernel
public import WeightedMIS.EmbeddedDimensions
public import WeightedMIS.Reduction

/-!
# Deterministic search matrices for an embedded graph

The actual even facial rows are enumerated in canonical flag order. The
verified kernel algorithm extends their span with bounded integer rows, and
the computed list length obeys the genus and odd-face parameter bounds.
-/

@[expose] public section

namespace WeightedMIS.ComputedEmbeddedMatrices

open Matrix EmbeddingFaces SidePairing

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- The computed facial rows in their explicit numeric order. -/
def localRows (R : Ribbon left right) : List (Fin m → ℚ) :=
  List.ofFn fun i : R.EvenRowIndex (Flag.canonicalOrder m) =>
    fun e => (R.computedIntegerMatrix (Flag.canonicalOrder m) i e : ℚ)

/-- The deterministic bounded complement of those actual facial rows. -/
def globalRows (R : Ribbon left right) : List (Fin m → ℤ) :=
  DeterministicKernel.complement left right (localRows R)

/-- The emitted integer rows, transposed for the expanded-state search. -/
def globalColumn (R : Ribbon left right) (e : Fin m)
    (i : Fin (globalRows R).length) : ℤ := (globalRows R).get i e

theorem localRows_span (R : Ribbon left right) :
    RationalElimination.listSpan (localRows R) =
      Submodule.span ℚ (Set.range (Faces.matrix (R.enumeratedFace (Flag.canonicalOrder m)))) := by
  unfold RationalElimination.listSpan
  congr 1
  ext x
  simp only [localRows, Set.mem_ofPred_eq, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨R.evenRowFace (Flag.canonicalOrder m) i, rfl⟩
  · rintro ⟨f, rfl⟩
    obtain ⟨i, rfl⟩ := R.evenRowFace_surjective (Flag.canonicalOrder m) f
    exact ⟨i, rfl⟩

theorem localRows_kernel (R : Ribbon left right) :
    RationalElimination.listSpan (localRows R) ≤
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  rw [localRows_span]
  exact Faces.row_span_le_left_kernel _

theorem globalColumn_span (R : Ribbon left right) :
    Submodule.span ℚ (Set.range (Reduction.globalMatrix (globalColumn R))) =
      RationalElimination.listSpan ((globalRows R).map ComputedKernel.rationalRow) := by
  unfold RationalElimination.listSpan
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(globalRows R).get i, List.get_mem _ _, rfl⟩
  · rintro ⟨row, hrow, rfl⟩
    obtain ⟨i, rfl⟩ := List.get_of_mem hrow
    exact ⟨i, rfl⟩

/-- Every emitted global coefficient is bounded by two, and its row is an
actual incidence-kernel vector. -/
theorem globalRows_spec (R : Ribbon left right)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    (∀ row ∈ globalRows R,
      KernelBasis.IntegralKernel left right row ∧ ∀ e, |row e| ≤ 2) ∧
      (globalRows R).length = m - n - Module.finrank ℚ
        (RationalElimination.listSpan (localRows R)) ∧
      RationalElimination.listSpan (localRows R) ⊔
        RationalElimination.listSpan ((globalRows R).map ComputedKernel.rationalRow) =
          LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin :=
  DeterministicKernel.complement_spec left right hc hnb (localRows R) (localRows_kernel R)

/-- The actual columns and actual computed complement provide all and only
incidence-kernel equations required by the search. -/
theorem computed_matrices_spec (R : Ribbon left right)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    (∀ e i, |globalColumn R e i| ≤ 2) ∧
      Submodule.span ℚ (Set.range (Reduction.localMatrix
        (R.computedColumn (Flag.canonicalOrder m))) ∪
        Set.range (Reduction.globalMatrix (globalColumn R))) =
          LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  have hspec := globalRows_spec R hc hnb
  constructor
  · intro e i
    exact (hspec.1 _ (List.get_mem _ _)).2 e
  · have hlocal : Submodule.span ℚ (Set.range (Reduction.localMatrix
        (R.computedColumn (Flag.canonicalOrder m)))) =
        RationalElimination.listSpan (localRows R) := by
      unfold RationalElimination.listSpan
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq, localRows, List.mem_ofFn]
      have heq (i : R.EvenRowIndex (Flag.canonicalOrder m)) :
          Reduction.localMatrix (R.computedColumn (Flag.canonicalOrder m)) i =
            fun e => (R.computedIntegerMatrix (Flag.canonicalOrder m) i e : ℚ) := by
        funext e
        change (Walks.columnVector (R.computedColumn (Flag.canonicalOrder m) e) i : ℚ) = _
        rw [R.computedColumn_spec _ Flag.mem_canonicalOrder]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (heq i).symm.trans hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (heq i).trans hi⟩
    rw [Submodule.span_union, hlocal, globalColumn_span]
    exact hspec.2.2

/-- A nonbipartite endpoint graph has an actual edge. -/
theorem edge_nonempty (hnb : ¬ Incidence.Bipartite left right) : Nonempty (Fin m) := by
  by_contra hn
  have hi : IsEmpty (Fin m) := not_nonempty_iff.mp hn
  exact hnb ⟨fun _ => false, fun e => hi.false e |>.elim⟩

/-- Exact computed codimension for the deterministically enumerated embedding. -/
theorem globalRows_length {F : Type*} [Fintype F] [DecidableEq F]
    (M : CellularEmbedding left right F)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    (globalRows M.sides.toRibbon).length = EmbeddedReduction.coordinateCount
      (M.enumerate (Flag.canonicalOrder m) Flag.mem_canonicalOrder (edge_nonempty hnb)) := by
  have h := (globalRows_spec M.sides.toRibbon hc hnb).2.1
  have hs : RationalElimination.listSpan (localRows M.sides.toRibbon) =
      EmbeddedReduction.faceRowSpace
        (M.enumerate (Flag.canonicalOrder m) Flag.mem_canonicalOrder (edge_nonempty hnb)) :=
    localRows_span M.sides.toRibbon
  rw [hs, EmbeddedReduction.faceRowSpace_finrank] at h
  simpa only [EmbeddedReduction.coordinateCount, Fintype.card_fin] using h

/-- The number of coordinates actually produced by complement selection has
 the original embedding's genus and odd-face bound. -/
theorem globalRows_parameter_bound {F : Type*} [Fintype F] [DecidableEq F]
    (M : CellularEmbedding left right F)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    (globalRows M.sides.toRibbon).length ≤
      Parameters.exponent M.eulerGenus (EmbeddedReduction.oddFaceCount M) := by
  rw [globalRows_length M hc hnb]
  have h := EmbeddedReduction.coordinateCount_le_exponent
    (M.enumerate (Flag.canonicalOrder m) Flag.mem_canonicalOrder (edge_nonempty hnb)) hc hnb
  have hg := M.enumerate_eulerGenus (Flag.canonicalOrder m) Flag.mem_canonicalOrder
    (edge_nonempty hnb) hc
  have hk := M.enumerate_odd_count (Flag.canonicalOrder m) Flag.mem_canonicalOrder
    (edge_nonempty hnb)
  change EmbeddedReduction.oddFaceCount
    (M.enumerate (Flag.canonicalOrder m) Flag.mem_canonicalOrder (edge_nonempty hnb)) =
      EmbeddedReduction.oddFaceCount M at hk
  rwa [hg, hk] at h

/-- Coherent surface orientation gives the sharper bound on that same computed
 list, without changing the algorithm or supplying any rank assumption. -/
theorem globalRows_orientable_bound {F : Type*} [Fintype F] [DecidableEq F]
    (M : CellularEmbedding left right F) (O : M.sides.Orientation)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    (globalRows M.sides.toRibbon).length ≤
      Parameters.orientableExponent M.eulerGenus (EmbeddedReduction.oddFaceCount M) := by
  rw [globalRows_length M hc hnb]
  have h := EmbeddedReduction.coordinateCount_le_orientableExponent
    (M.enumerate (Flag.canonicalOrder m) Flag.mem_canonicalOrder (edge_nonempty hnb))
    (M.enumerateOrientation (Flag.canonicalOrder m) Flag.mem_canonicalOrder
      (edge_nonempty hnb) O) hc hnb
  have hg := M.enumerate_eulerGenus (Flag.canonicalOrder m) Flag.mem_canonicalOrder
    (edge_nonempty hnb) hc
  have hk := M.enumerate_odd_count (Flag.canonicalOrder m) Flag.mem_canonicalOrder
    (edge_nonempty hnb)
  change EmbeddedReduction.oddFaceCount
    (M.enumerate (Flag.canonicalOrder m) Flag.mem_canonicalOrder (edge_nonempty hnb)) =
      EmbeddedReduction.oddFaceCount M at hk
  rwa [hg, hk] at h

end WeightedMIS.ComputedEmbeddedMatrices
