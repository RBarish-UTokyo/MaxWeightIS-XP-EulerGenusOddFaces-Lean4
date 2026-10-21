module

public import WeightedMIS.SpecConnectivity
public import WeightedMIS.RibbonRestriction

/-!
# Statement drawn corners are the internal first-return corners

`Map.DrawnCorner` rotates around a vertex past deleted edges. Internally the
corner system of a subdrawing is obtained by the first-return construction on
the vertex rotation. The two agree, so a drawing placed in a closed-surface
map carries an internal corner system whose relabelled corners are exactly the
inherited ones.
-/

@[expose] public section

namespace WeightedMIS.Spec

open EmbeddingFaces

namespace Map

variable (A : Map) (hA : A.IsClosedSurface)

/-- The traced side pairing of the internal embedding of a closed-surface map. -/
noncomputable abbrev tracedSides := (A.cellular hA).sides.toRibbon.sidePairing

/-- The internal vertex rotation is the statement `turn`. -/
theorem vertexNext_equiv (x : Flag (Fin A.edges)) :
    (A.tracedSides hA).vertexNext (Flag.equiv _ x) = Flag.equiv _ (A.turn x) := by
  change SidePairing.across ((A.tracedSides hA).corner (Flag.equiv _ x)) = _
  rw [Ribbon.sidePairing_corner]
  change SidePairing.across ((A.ribbon hA).sidePairing.corner (Flag.equiv _ x)) = _
  rw [Ribbon.sidePairing_corner, A.ribbon_corner hA]
  rfl

theorem vertexNext_iterate (n : ℕ) (x : Flag (Fin A.edges)) :
    ((A.tracedSides hA).vertexNext : EmbeddingFaces.Flag (Fin A.edges) → _)^[n] (Flag.equiv _ x) =
      Flag.equiv _ (A.turn^[n] x) := by
  have h : Function.Semiconj (Flag.equiv (Fin A.edges)) A.turn (A.tracedSides hA).vertexNext :=
    fun x => (A.vertexNext_equiv hA x).symm
  exact (h.iterate_right n x).symm

/-- A statement drawn corner is the internal first-return corner. -/
theorem retainedCorner_of_drawnCorner (keep : Fin A.edges → Prop)
    (u : Flag (Fin A.edges)) (hu : keep u.edge) (v : Flag (Fin A.edges))
    (h : A.DrawnCorner keep u v) :
    ((A.tracedSides hA).retainedCorner keep ⟨Flag.equiv _ u, hu⟩).val = Flag.equiv _ v := by
  obtain ⟨t, ht, hmem, hbefore, rfl⟩ := h
  have hrt : PermutationDeletion.returnTime (A.tracedSides hA).vertexNext
      (fun x => keep x.edge) ⟨Flag.equiv _ u, hu⟩ = t := by
    apply PermutationDeletion.returnTime_eq_of_trace _ _ _ t ht
    · change keep (((A.tracedSides hA).vertexNext : EmbeddingFaces.Flag (Fin A.edges) → _)^[t]
        (Flag.equiv _ u)).edge
      rw [A.vertexNext_iterate hA]
      exact hmem
    · intro j hj hjt
      change ¬ keep (((A.tracedSides hA).vertexNext : EmbeddingFaces.Flag (Fin A.edges) → _)^[j]
        (Flag.equiv _ u)).edge
      rw [A.vertexNext_iterate hA]
      exact hbefore j hj hjt
  change SidePairing.across ((PermutationDeletion.firstReturn (A.tracedSides hA).vertexNext
    (fun x => keep x.edge) ⟨Flag.equiv _ u, hu⟩).val) = _
  rw [PermutationDeletion.firstReturn_apply, hrt]
  change SidePairing.across (((A.tracedSides hA).vertexNext : EmbeddingFaces.Flag (Fin A.edges) → _)^[t]
    (Flag.equiv _ u)) = _
  rw [A.vertexNext_iterate hA]
  rfl

end Map

namespace Drawing

variable {A : Map} (hA : A.IsClosedSurface) {D : Drawing} (W : D.In A)

/-- Drawing edges are the drawn edges of the ambient map. -/
noncomputable def edgeEquiv : Fin D.edges ≃ {e : Fin A.edges // W.drawn e} :=
  Equiv.ofBijective (fun d => ⟨W.edgeMap d, d, rfl⟩)
    ⟨fun _ _ h => W.edgeMap_injective (congrArg Subtype.val h),
      fun ⟨_, d, hd⟩ => ⟨d, Subtype.ext hd⟩⟩

@[simp] theorem edgeEquiv_val (d : Fin D.edges) : (edgeEquiv W d).val = W.edgeMap d := rfl

/-- The internal subdrawing ribbon of the ambient map. -/
noncomputable abbrev ambientRestriction :
    Ribbon (fun e : {e : Fin A.edges // W.drawn e} => A.left e.val) (fun e => A.right e.val) :=
  (A.cellular hA).sides.toRibbon.restrict W.drawn

/-- Relabelled drawing flags. -/
noncomputable def flagMap (x : Flag (Fin D.edges)) :
    EmbeddingFaces.Flag {e : Fin A.edges // W.drawn e} :=
  Flag.mapEquiv (edgeEquiv W) (Flag.equiv _ x)

theorem flagMap_injective : Function.Injective (flagMap W) :=
  (Flag.mapEquiv (edgeEquiv W)).injective.comp (Flag.equiv _).injective

/-- The drawing's corner pairing is the inherited first-return corner. -/
theorem flagMap_corner (x : Flag (Fin D.edges)) :
    flagMap W (D.corner x) = (ambientRestriction hA W).corner (flagMap W x) := by
  apply (Flag.retainedEquiv W.drawn).injective
  apply Subtype.ext
  have h := A.retainedCorner_of_drawnCorner hA W.drawn (x.map W.edgeMap) ⟨x.edge, rfl⟩
    ((D.corner x).map W.edgeMap) (W.corner_comm x)
  have hr : (Flag.retainedEquiv W.drawn) ((ambientRestriction hA W).corner (flagMap W x)) =
      (A.tracedSides hA).retainedCorner W.drawn (Flag.retainedEquiv W.drawn (flagMap W x)) := by
    simp [Ribbon.restrict]
  rw [hr]
  exact h.symm

include hA W in
theorem corner_involutive (x : Flag (Fin D.edges)) : D.corner (D.corner x) = x := by
  apply flagMap_injective W
  rw [flagMap_corner hA W, flagMap_corner hA W, (ambientRestriction hA W).involutive]

include hA W in
theorem corner_ne (x : Flag (Fin D.edges)) : D.corner x ≠ x := by
  intro h
  apply (ambientRestriction hA W).ne_self (flagMap W x)
  rw [← flagMap_corner hA W, h]

theorem flagMap_vertex (x : Flag (Fin D.edges)) :
    W.vertexMap ((Flag.equiv _ x).vertex D.left D.right) =
      (flagMap W x).vertex (fun e : {e : Fin A.edges // W.drawn e} => A.left e.val)
        (fun e => A.right e.val) :=
  Flag.mapEquiv_vertex (edgeEquiv W) W.vertexMap D.left D.right _ _ W.left_comm W.right_comm _

include hA W in
theorem corner_vertex (x : Flag (Fin D.edges)) :
    (Flag.equiv _ (D.corner x)).vertex D.left D.right = (Flag.equiv _ x).vertex D.left D.right := by
  apply W.vertexMap_injective
  rw [flagMap_vertex W, flagMap_vertex W, flagMap_corner hA W, (ambientRestriction hA W).vertex]

/-- The internal corner system read directly from the drawing's own corner
pairing. -/
def ribbon : Ribbon D.left D.right :=
  ribbonOf D.left D.right D.corner (corner_involutive hA W) (corner_ne hA W) (corner_vertex hA W)

theorem ribbon_corner_apply (y : EmbeddingFaces.Flag (Fin D.edges)) :
    (ribbon hA W).corner y = Flag.equiv _ (D.corner ((Flag.equiv _).symm y)) := rfl

/-- The project-level corner hypothesis for the drawing's ribbon. -/
theorem ribbon_corner_map (y : EmbeddingFaces.Flag (Fin D.edges)) :
    Flag.mapEquiv (edgeEquiv W) ((ribbon hA W).corner y) =
      (ambientRestriction hA W).corner (Flag.mapEquiv (edgeEquiv W) y) := by
  have h := flagMap_corner hA W ((Flag.equiv _).symm y)
  simp only [flagMap, Equiv.apply_symm_apply] at h
  rw [ribbon_corner_apply]
  exact h

end Drawing

end WeightedMIS.Spec
