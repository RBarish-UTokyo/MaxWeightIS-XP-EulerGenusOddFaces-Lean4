module

public import WeightedMIS.EmbeddingEuler
public import WeightedMIS.Parameters

/-!
# Supplementary-coordinate bounds for actual embeddings

The local row rank, the incidence rank, and Euler's identity are derived from
the supplied polygon-side map. They imply the manuscript's general and
orientable coordinate bounds without numerical rank or genus hypotheses.
-/

@[expose] public section

namespace WeightedMIS.EmbeddedReduction

open Matrix
open WeightedMIS.EmbeddingFaces

variable {V E F : Type*} {left right : E → V}
variable [Fintype V] [Fintype E] [Fintype F]
variable [DecidableEq V] [DecidableEq E] [DecidableEq F]

/-- Number of actual odd-length facial walks. -/
def oddFaceCount (M : CellularEmbedding left right F) : ℕ :=
  Fintype.card { f // Odd (M.faces f).boundary.length }

/-- Ordinary rational span of the actual even facial rows. -/
def faceRowSpace (M : CellularEmbedding left right F) : Submodule ℚ (E → ℚ) :=
  Submodule.span ℚ (Set.range (Faces.matrix M.faces))

/-- Exact number of supplementary kernel coordinates. -/
noncomputable def coordinateCount (M : CellularEmbedding left right F) : ℕ :=
  Fintype.card E - Fintype.card V - (Faces.matrix M.faces).rank

omit [Fintype V] [DecidableEq V] [DecidableEq F] in
theorem faceRowSpace_finrank (M : CellularEmbedding left right F) :
    Module.finrank ℚ (faceRowSpace M) = (Faces.matrix M.faces).rank :=
  (Matrix.rank_eq_finrank_span_row _).symm

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [DecidableEq F] in
theorem even_odd_face_count (M : CellularEmbedding left right F) :
    Fintype.card (Faces.EvenFaces M.faces) + oddFaceCount M = Fintype.card F := by
  have h := Fintype.card_subtype_compl (fun f => Odd (M.faces f).boundary.length)
  have hb := Fintype.card_subtype_le (fun f => Odd (M.faces f).boundary.length)
  have heq := Fintype.card_congr (Equiv.subtypeEquivRight
    (fun f : F => Nat.not_odd_iff_even (n := (M.faces f).boundary.length)))
  rw [heq] at h
  change Fintype.card (Faces.EvenFaces M.faces) = Fintype.card F - oddFaceCount M at h
  change oddFaceCount M ≤ Fintype.card F at hb
  omega

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [DecidableEq F] in

theorem all_faces_even_of_count_zero (M : CellularEmbedding left right F)
    (hk : oddFaceCount M = 0) : ∀ f, Even (M.faces f).boundary.length := by
  intro f
  by_contra hf
  have hp : 0 < Fintype.card {f // Odd (M.faces f).boundary.length} :=
    Fintype.card_pos_iff.mpr ⟨⟨f, Nat.not_even_iff_odd.mp hf⟩⟩
  change 0 < oddFaceCount M at hp
  omega

omit [DecidableEq F] in
/-- The actual face rows lie in the incidence kernel, so their rank fits its
derived dimension. -/
theorem face_rank_le_kernel (M : CellularEmbedding left right F)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    (Faces.matrix M.faces).rank ≤ Fintype.card E - Fintype.card V := by
  have h := Submodule.finrank_mono (Faces.row_span_le_left_kernel M.faces)
  rw [Incidence.left_kernel_finrank left right hc hnb] at h
  change Module.finrank ℚ (faceRowSpace M) ≤ _ at h
  rw [faceRowSpace_finrank] at h
  exact h

omit [DecidableEq F] in
/-- The codimension plus local rank and vertex count accounts for every edge. -/
theorem coordinateCount_identity (M : CellularEmbedding left right F)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    coordinateCount M + (Faces.matrix M.faces).rank + Fintype.card V = Fintype.card E := by
  have hr := face_rank_le_kernel M hc hnb
  have ha := Matrix.rank_le_card_height (Incidence.unsigned left right)
  rw [Incidence.unsigned_rank_eq_card left right hc hnb] at ha
  unfold coordinateCount
  omega

/-- The exact odd-face rank supplies the stronger bound when odd faces exist. -/
theorem coordinateCount_odd (M : CellularEmbedding left right F)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (hk : oddFaceCount M ≠ 0) : coordinateCount M + 2 = M.eulerGenus + oddFaceCount M := by
  obtain ⟨f⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hk)
  have hf : ¬ Even (M.faces f.val).boundary.length := Nat.not_even_iff_odd.mpr f.property
  have hr := M.even_matrix_rank hc f.val hf
  have hc' := coordinateCount_identity M hc hnb
  have he := M.eulerGenus_identity hc
  have hcount := even_odd_face_count M
  omega

/-- The general all-even rank bound supplies one fewer independent constraint. -/
theorem coordinateCount_even (M : CellularEmbedding left right F)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (hk : oddFaceCount M = 0) : coordinateCount M + 1 ≤ M.eulerGenus := by
  have hr := M.all_even_matrix_rank hc (all_faces_even_of_count_zero M hk)
  have hc' := coordinateCount_identity M hc hnb
  have he := M.eulerGenus_identity hc
  have hF : 0 < Fintype.card F := Fintype.card_pos_iff.mpr M.face_present
  omega

/-- The manuscript's parameter exponent bounds the constructed codimension. -/
theorem coordinateCount_le_exponent (M : CellularEmbedding left right F)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    coordinateCount M ≤ Parameters.exponent M.eulerGenus (oddFaceCount M) := by
  unfold Parameters.exponent
  by_cases hk : oddFaceCount M = 0
  · have h := coordinateCount_even M hc hnb hk
    omega
  · have h := coordinateCount_odd M hc hnb hk
    omega

/-- In an orientable all-even map the facial rows are fully independent. -/
theorem coordinateCount_orientable (M : CellularEmbedding left right F)
    (O : M.sides.Orientation)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    coordinateCount M + 2 = M.eulerGenus + oddFaceCount M := by
  by_cases hk : oddFaceCount M = 0
  · have hr := M.orientable_all_even_rank O hc hnb (all_faces_even_of_count_zero M hk)
    have hc' := coordinateCount_identity M hc hnb
    have he := M.eulerGenus_identity hc
    omega
  · exact coordinateCount_odd M hc hnb hk

/-- The sharper orientable parameter exponent bounds the same constructed data. -/
theorem coordinateCount_le_orientableExponent (M : CellularEmbedding left right F)
    (O : M.sides.Orientation)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    coordinateCount M ≤ Parameters.orientableExponent M.eulerGenus (oddFaceCount M) := by
  have h := coordinateCount_orientable M O hc hnb
  unfold Parameters.orientableExponent
  omega

end WeightedMIS.EmbeddedReduction
