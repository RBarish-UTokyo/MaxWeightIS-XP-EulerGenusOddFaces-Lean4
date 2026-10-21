module

public import WeightedMIS.EmbeddingEuler
public import WeightedMIS.RegionParity

/-!
# Complementary-cell counting and the genus gluing identity

Complement regions can retract onto components of the deleted-edge dual.
An isolated dual vertex is a disk; other components use their actual capped
polygon-side maps. Explicit equivalences of the vertex, edge, face, and cap
cells derive the Euler gluing identity. Thus its numerical equality is not
assumed. Instantiating the cell equivalences from deletion traces is separate
from this finite counting argument.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V E F : Type*} {left right : E → V}

/-- A capped regular-neighborhood component, including an isolated vertex disk. -/
inductive CappedComponent (left right : E → V) (F : Type*) where
  | embedded (map : CellularEmbedding left right F) (connected : Incidence.Connected left right)
  | isolated (vertex : Unique V) (noedges : IsEmpty E) (face : Unique F)

namespace CappedComponent

/-- Euler genus of the capped component; an isolated vertex caps to a sphere. -/
def genus [Fintype V] [Fintype E] [Fintype F] : CappedComponent left right F → ℕ
  | .embedded M _ => M.eulerGenus
  | .isolated _ _ _ => 0

/-- Both nontrivial actual maps and isolated disks satisfy their exact cell identity. -/
theorem euler_identity [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    (D : CappedComponent left right F) :
    D.genus + Fintype.card V + Fintype.card F = Fintype.card E + 2 := by
  cases D with
  | embedded M hc => exact M.eulerGenus_identity hc
  | isolated hv he hf =>
      let : Unique V := hv
      let : IsEmpty E := he
      let : Unique F := hf
      simp [genus]

end CappedComponent

namespace SidePairing

/-- Actual side fibers count the occurrences of the original facial walk. -/
theorem face_fiber_size [Fintype E] [Fintype F]
    {faces : F → Faces.Face left right} (P : SidePairing faces) (f : F) :
    RegionParity.fiberSize (fun s : E × Bool => P.face s.1 s.2) f =
      (faces f).boundary.length := by
  classical
  unfold RegionParity.fiberSize
  rw [Finset.card_filter]
  rw [← P.pairing.sum_comp
    (fun s : E × Bool => if P.face s.1 s.2 = f then (1 : ℕ) else 0)]
  simp only [P.face_pairing]
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_boole]
  calc
    _ = ∑ x : F, if x = f then (faces x).boundary.length else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = f <;> simp [hx]
    _ = _ := by simp

end SidePairing

namespace ComplementEuler

variable {VH EH FH X R : Type*}
variable {VD ED FD : R → Type*}
variable {leftH rightH : EH → VH}
variable {leftD rightD : (r : R) → ED r → VD r}
variable [Fintype V] [Fintype E] [Fintype F]
variable [Fintype VH] [Fintype EH] [Fintype FH] [Fintype X] [Fintype R]
variable [∀ r, Fintype (VD r)] [∀ r, Fintype (ED r)] [∀ r, Fintype (FD r)]
variable [DecidableEq V] [DecidableEq E] [DecidableEq F]
variable [DecidableEq VH] [DecidableEq EH] [DecidableEq FH]
variable [∀ r, DecidableEq (VD r)] [∀ r, DecidableEq (ED r)] [∀ r, DecidableEq (FD r)]

/-- The complement component containing one retained boundary circle. -/
def boundaryRegion (caps : ((r : R) × FD r) ≃ FH ⊕ X) (f : FH) : R :=
  (caps.symm (Sum.inl f)).1

/-- Exact Euler gluing from actual cell partitions. The caps pair either with
a retained boundary circle or with one omitted original vertex disk. -/
theorem gluing_counts
    (G : CellularEmbedding left right F) (hcG : Incidence.Connected left right)
    (H : CellularEmbedding leftH rightH FH) (hcH : Incidence.Connected leftH rightH)
    (D : (r : R) → CappedComponent (leftD r) (rightD r) (FD r))
    (vertices : V ≃ VH ⊕ X)
    (edges : E ≃ EH ⊕ ((r : R) × ED r))
    (faces : F ≃ ((r : R) × VD r))
    (caps : ((r : R) × FD r) ≃ FH ⊕ X) :
    G.eulerGenus + 2 * Fintype.card R =
      H.eulerGenus + (∑ r, (D r).genus) + 2 * Fintype.card FH := by
  have hn := Fintype.card_congr vertices
  have hm := Fintype.card_congr edges
  have hf := Fintype.card_congr faces
  have hb := Fintype.card_congr caps
  simp only [Fintype.card_sum, Fintype.card_sigma] at hn hm hf hb
  have hG := G.eulerGenus_identity hcG
  have hH := H.eulerGenus_identity hcH
  have hD := congrArg (fun q : R → ℕ => ∑ r, q r)
    (funext fun r => (D r).euler_identity)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at hD
  omega

omit [Fintype V] [Fintype E] [Fintype F] [Fintype VH] [Fintype EH] [Fintype X]
    [∀ r, Fintype (VD r)] [∀ r, Fintype (ED r)] [∀ r, Fintype (FD r)]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    [DecidableEq VH] [DecidableEq EH] [DecidableEq FH] [Fintype R]
    [∀ r, DecidableEq (VD r)] [∀ r, DecidableEq (ED r)] [∀ r, DecidableEq (FD r)] in
/-- A region meeting a retained boundary has at least one boundary circle. -/
theorem boundary_fiber_pos (region : FH → R) (hs : Function.Surjective region) (r : R) :
    1 ≤ (Finset.univ.filter fun f => region f = r).card := by
  classical
  obtain ⟨f, hf⟩ := hs r
  exact Finset.card_pos.mpr ⟨f, by simp [hf]⟩

omit [Fintype V] [Fintype E] [Fintype F] [Fintype VH] [Fintype EH] [Fintype X]
    [∀ r, Fintype (VD r)] [∀ r, Fintype (ED r)] [∀ r, Fintype (FD r)]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    [DecidableEq VH] [DecidableEq EH] [DecidableEq FH]
    [∀ r, DecidableEq (VD r)] [∀ r, DecidableEq (ED r)] [∀ r, DecidableEq (FD r)] in
/-- Counting nonempty boundary fibers separates one circle per region. -/
theorem boundary_excess_count (region : FH → R) (hs : Function.Surjective region) :
    (∑ r, ((Finset.univ.filter fun f => region f = r).card - 1)) + Fintype.card R =
      Fintype.card FH := by
  classical
  have hsum : (∑ r, (Finset.univ.filter fun f => region f = r).card) = Fintype.card FH := by
    simpa using RegionParity.sum_region_count region (fun _ => True)
  have hsingle (r : R) :
      ((Finset.univ.filter fun f => region f = r).card - 1) + 1 =
        (Finset.univ.filter fun f => region f = r).card := by
    have h := boundary_fiber_pos region hs r
    omega
  have h := congrArg (fun q : R → ℕ => ∑ r, q r) (funext hsingle)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one, hsum] using h

/-- The manuscript's genus gluing identity is a consequence of the actual
cell correspondences and of every complementary region meeting the boundary. -/
theorem gluing_identity
    (G : CellularEmbedding left right F) (hcG : Incidence.Connected left right)
    (H : CellularEmbedding leftH rightH FH) (hcH : Incidence.Connected leftH rightH)
    (D : (r : R) → CappedComponent (leftD r) (rightD r) (FD r))
    (vertices : V ≃ VH ⊕ X)
    (edges : E ≃ EH ⊕ ((r : R) × ED r))
    (faces : F ≃ ((r : R) × VD r))
    (caps : ((r : R) × FD r) ≃ FH ⊕ X)
    (hmeet : Function.Surjective (boundaryRegion caps)) :
    G.eulerGenus = H.eulerGenus + (∑ r, (D r).genus) +
      2 * ∑ r, ((Finset.univ.filter fun f => boundaryRegion caps f = r).card - 1) := by
  have h := gluing_counts G hcG H hcH D vertices edges faces caps
  have hb := boundary_excess_count (boundaryRegion caps) hmeet
  omega

/-- In particular the capped retained component has no larger Euler genus. -/
theorem genus_mono
    (G : CellularEmbedding left right F) (hcG : Incidence.Connected left right)
    (H : CellularEmbedding leftH rightH FH) (hcH : Incidence.Connected leftH rightH)
    (D : (r : R) → CappedComponent (leftD r) (rightD r) (FD r))
    (vertices : V ≃ VH ⊕ X)
    (edges : E ≃ EH ⊕ ((r : R) × ED r))
    (faces : F ≃ ((r : R) × VD r))
    (caps : ((r : R) × FD r) ≃ FH ⊕ X)
    (hmeet : Function.Surjective (boundaryRegion caps)) : H.eulerGenus ≤ G.eulerGenus := by
  have h := gluing_identity G hcG H hcH D vertices edges faces caps hmeet
  omega

/-- The full per-component genus and odd-face monotonicity follows from
actual cell correspondences, paired deleted sides, and actual boundary-position
bijections. Neither an Euler gluing equality nor a parity congruence is assumed. -/
theorem parameter_mono_from_cells
    (G : CellularEmbedding left right F) (hcG : Incidence.Connected left right)
    (H : CellularEmbedding leftH rightH FH) (hcH : Incidence.Connected leftH rightH)
    (D : (r : R) → CappedComponent (leftD r) (rightD r) (FD r))
    (vertices : V ≃ VH ⊕ X)
    (edges : E ≃ EH ⊕ ((r : R) × ED r))
    (faceCells : F ≃ ((r : R) × VD r))
    (caps : ((r : R) × FD r) ≃ FH ⊕ X)
    (hmeet : Function.Surjective (boundaryRegion caps))
    (boundary : E × Bool → Option FH)
    (paired : ∀ e, boundary (e, false) = none ↔ boundary (e, true) = none)
    (deleted : ∀ e, boundary (e, false) = none →
      (faceCells (G.sides.face e false)).1 = (faceCells (G.sides.face e true)).1)
    (retained : ∀ s f, boundary s = some f →
      boundaryRegion caps f = (faceCells (G.sides.face s.1 s.2)).1)
    (positions : ∀ f : FH, {s : E × Bool // boundary s = some f} ≃
      Fin (H.faces f).boundary.length) :
    H.eulerGenus ≤ G.eulerGenus ∧
      H.eulerGenus + Fintype.card {f // Odd (H.faces f).boundary.length} ≤
        G.eulerGenus + Fintype.card {f // Odd (G.faces f).boundary.length} := by
  classical
  have hg := gluing_identity G hcG H hcH D vertices edges faceCells caps hmeet
  have h := RegionParity.genus_bookkeeping_from_sides
    (fun s : E × Bool => G.sides.face s.1 s.2)
    (fun f => (faceCells f).1) boundary (boundaryRegion caps)
    paired deleted retained (boundary_fiber_pos (boundaryRegion caps) hmeet)
    G.eulerGenus H.eulerGenus (fun r => (D r).genus) hg
  have hb (f : FH) : RegionParity.boundarySize boundary f = (H.faces f).boundary.length := by
    have he := Fintype.card_congr (positions f)
    rw [Fintype.card_subtype, Fintype.card_fin] at he
    unfold RegionParity.boundarySize RegionParity.fiberSize
    convert he using 1
    congr 1
    ext s
    simp
  simpa only [hb, G.sides.face_fiber_size, Fintype.card_subtype] using h

end ComplementEuler
end WeightedMIS.EmbeddingFaces
