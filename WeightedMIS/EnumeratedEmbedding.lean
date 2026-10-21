module

public import WeightedMIS.RibbonEnumeratedSides
public import WeightedMIS.RibbonOrientation

/-!
# Deterministic face outputs for a supplied cellular embedding

An explicit finite flag order is traced and certified against the original
embedding. Actual facial labels, boundary lengths, Euler genus, and the number
of odd faces are preserved. For finitely indexed edges a canonical executable
order is supplied, with an explicit cubic scan bound and linear output size.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open SidePairing FiniteCycleEnumeration

namespace Flag

/-- A deterministic complete flag order obtained from an edge-label list. -/
def listOrder {E : Type*} (edges : List E) : List (Flag E) :=
  edges.map (fun e => ⟨e, false, false⟩) ++ edges.map (fun e => ⟨e, false, true⟩) ++
    edges.map (fun e => ⟨e, true, false⟩) ++ edges.map (fun e => ⟨e, true, true⟩)

@[simp] theorem listOrder_length {E : Type*} (edges : List E) :
    (listOrder edges).length = 4 * edges.length := by simp [listOrder]; omega

@[simp] theorem mem_listOrder {E : Type*} (edges : List E) (x : Flag E) :
    x ∈ listOrder edges ↔ x.edge ∈ edges := by
  rcases x with ⟨e, s, t⟩
  cases s <;> cases t <;> simp [listOrder, Flag.mk.injEq]

/-- Canonical executable order for edges represented by finite integer labels. -/
def canonicalOrder (m : ℕ) : List (Flag (Fin m)) := listOrder (List.finRange m)

@[simp] theorem canonicalOrder_length (m : ℕ) : (canonicalOrder m).length = 4 * m := by
  simp [canonicalOrder]

theorem mem_canonicalOrder {m : ℕ} (x : Flag (Fin m)) : x ∈ canonicalOrder m := by
  simp [canonicalOrder]

end Flag

namespace Ribbon.FlagOrientation

variable {V E : Type*} [Fintype E] [DecidableEq E] {left right : E → V}
    {R : Ribbon left right} (O : R.FlagOrientation) (order : List (Flag E))
    (horder : ∀ x : Flag E, x ∈ order)

/-- The coherent sign attached to an actual computed facial root. -/
def enumeratedSign (i : R.EnumeratedIndex order) : ℚ := -O.sign (R.enumeratedRoot order i)

theorem enumeratedSign_signs (i : R.EnumeratedIndex order) :
    O.enumeratedSign order i = 1 ∨ O.enumeratedSign order i = -1 := by
  rcases O.signs (R.enumeratedRoot order i) with h | h <;> simp [enumeratedSign, h]

theorem enumeratedSign_position (d : Occurrence (R.enumeratedFace order)) :
    O.enumeratedSign order d.1 = -O.sign (R.enumeratedPosition order d) := by
  change -O.sign (R.enumeratedRoot order d.1) =
    -O.sign ((R.rotation : Flag E → Flag E)^[d.2.val] (R.enumeratedRoot order d.1))
  rw [O.iterate_rotation]

theorem enumeratedSign_startFlag (d : Occurrence (R.enumeratedFace order)) :
    O.sign ((R.enumeratedSidePairing order horder).startFlag d) = -O.enumeratedSign order d.1 := by
  rw [R.enumeratedSidePairing_startFlag, O.enumeratedSign_position, neg_neg]

theorem enumeratedSign_endFlag (d : Occurrence (R.enumeratedFace order)) :
    O.sign ((R.enumeratedSidePairing order horder).endFlag d) = O.enumeratedSign order d.1 := by
  rw [R.enumeratedSidePairing_endFlag, O.along, O.enumeratedSign_position]

theorem enumeratedSign_formula (x : Flag E) :
    O.sign x = O.enumeratedSign order ((R.enumeratedSidePairing order horder).flagFace x) *
      boolSign ((R.enumeratedSidePairing order horder).forward x.edge x.side) * boolSign x.endpoint := by
  obtain ⟨⟨d, t⟩, rfl⟩ := (R.enumeratedSidePairing order horder).flagEquiv.surjective x
  cases t
  · rw [(R.enumeratedSidePairing order horder).flagEquiv_false, O.enumeratedSign_startFlag,
      (R.enumeratedSidePairing order horder).flagFace_startFlag]
    simp only [startFlag, (R.enumeratedSidePairing order horder).forward_pairing, boolSign_not]
    rw [mul_neg, mul_assoc, boolSign_mul_self, mul_one]
  · rw [(R.enumeratedSidePairing order horder).flagEquiv_true, O.enumeratedSign_endFlag,
      (R.enumeratedSidePairing order horder).flagFace_endFlag]
    simp only [endFlag, (R.enumeratedSidePairing order horder).forward_pairing]
    rw [mul_assoc, boolSign_mul_self, mul_one]

/-- Deterministically selected facial directions preserve orientability by
constructing their actual coherent signs. -/
def enumeratedPolygonOrientation : (R.enumeratedSidePairing order horder).Orientation where
  sign := O.enumeratedSign order
  signs := O.enumeratedSign_signs order
  coherent := by
    intro e
    have h := O.across (⟨e, false, true⟩ : Flag E)
    rw [O.enumeratedSign_formula order horder, O.enumeratedSign_formula order horder] at h
    simp only [SidePairing.across, Equiv.coe_fn_mk, Bool.not_false, flagFace,
      show boolSign true = 1 from rfl, mul_one] at h
    linarith only [h]

end Ribbon.FlagOrientation

namespace CellularEmbedding

variable {V E F : Type*} [Fintype E] [Fintype F] [DecidableEq E]
    {left right : E → V} (M : CellularEmbedding left right F)
    (order : List (Flag E)) (horder : ∀ x : Flag E, x ∈ order)

/-- The certified actual embedding whose facial walks are computed by the
first-unseen scan of the supplied flag order. -/
noncomputable def enumerate (hne : Nonempty E) :
    CellularEmbedding left right (M.sides.toRibbon.EnumeratedIndex order) :=
  M.sides.toRibbon.enumeratedEmbedding order horder
    (M.sides.toRibbon_vertexLinks M.vertex_links) M.vertex_present hne

/-- The original coherent surface orientation induces a coherent orientation
of the deterministically computed facial polygons. -/
def enumerateOrientation (hne : Nonempty E) (O : M.sides.Orientation) :
    (M.enumerate order horder hne).sides.Orientation :=
  O.toFlagOrientation.enumeratedPolygonOrientation order horder

/-- Explicit correspondence between computed finite facial indices and the
original actual polygon labels. -/
noncomputable def enumeratedOriginalFaceEquiv :
    M.sides.toRibbon.EnumeratedIndex order ≃ F :=
  (M.sides.toRibbon.enumeratedFaceEquiv order horder).trans
    (M.sides.originalFaceEquiv M.face_nonempty)

/-- Computation preserves the length of each original boundary circle. -/
theorem enumeratedOriginalFaceEquiv_length (i : M.sides.toRibbon.EnumeratedIndex order) :
    (M.sides.toRibbon.enumeratedFace order i).boundary.length =
      (M.faces (M.enumeratedOriginalFaceEquiv order horder i)).boundary.length := by
  rw [M.sides.toRibbon.enumeratedFaceEquiv_length order horder]
  exact M.sides.originalFaceEquiv_length M.face_nonempty _

/-- Exactly the actual original odd-face parameter is retained. -/
theorem enumerate_odd_count (hne : Nonempty E) :
    Fintype.card {i : M.sides.toRibbon.EnumeratedIndex order //
      Odd ((M.enumerate order horder hne).faces i).boundary.length} =
      Fintype.card {f : F // Odd (M.faces f).boundary.length} := by
  classical
  exact Fintype.card_congr ((M.enumeratedOriginalFaceEquiv order horder).subtypeEquiv fun i => by
    change Odd (M.sides.toRibbon.enumeratedFace order i).boundary.length ↔ _
    rw [M.enumeratedOriginalFaceEquiv_length order horder])

/-- The same endpoint graph and the exact facial correspondence preserve the
Euler genus of a connected cellular embedding. -/
theorem enumerate_eulerGenus [Fintype V] [DecidableEq V]
    (hne : Nonempty E) (hc : Incidence.Connected left right) :
    (M.enumerate order horder hne).eulerGenus = M.eulerGenus := by
  classical
  have h1 := (M.enumerate order horder hne).eulerGenus_identity hc
  have h2 := M.eulerGenus_identity hc
  have hf := Fintype.card_congr (M.enumeratedOriginalFaceEquiv order horder)
  omega

end CellularEmbedding

namespace Ribbon

variable {V : Type*} {m : ℕ} {left right : Fin m → V} (R : Ribbon left right)

/-- Canonical enumeration uses polynomially many list scans and permutation
applications; the count includes repeated scans of all previously seen flags. -/
theorem canonical_scanWork_le :
    scanWork (bothTrace R.rotation along (Fintype.card (Flag (Fin m))))
      (fun _ => 3 * Fintype.card (Flag (Fin m))) [] (Flag.canonicalOrder m) ≤
      (4 * m) * (64 * m * m + 12 * m + 2) := by
  have h := R.enumerated_scanWork_le (Flag.canonicalOrder m)
  simp only [Flag.canonicalOrder_length, Flag.card, Fintype.card_fin] at *
  nlinarith

end Ribbon
end WeightedMIS.EmbeddingFaces
