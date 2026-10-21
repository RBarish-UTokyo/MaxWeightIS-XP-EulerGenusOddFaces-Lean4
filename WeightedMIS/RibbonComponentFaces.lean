module

public import WeightedMIS.RibbonComponents

/-!
# Partitioning actual ribbon boundary circles among graph components

The inclusion of component flags commutes with the boundary rotation. Hence
its unoriented circles are exactly the original circles in that component.
This supplies the actual face-cell equivalence needed for Euler sums.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.Ribbon

open SidePairing Incidence

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype E] {left right : E → V} (R : Ribbon left right)

omit [Fintype E] in
/-- Traversing a boundary keeps the endpoint-graph component fixed. -/
theorem rotation_component (x : Flag E) :
    componentOf left right (left (R.rotation x).edge) = componentOf left right (left x.edge) :=
  R.corner_component (along x)

omit [Fintype E] in
theorem iterate_rotation_component (n : ℕ) (x : Flag E) :
    componentOf left right (left (((R.rotation : Flag E → Flag E)^[n]) x).edge) =
      componentOf left right (left x.edge) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', R.rotation_component, ih]

theorem sameCycle_component {x y : Flag E} (h : R.rotation.SameCycle x y) :
    componentOf left right (left y.edge) = componentOf left right (left x.edge) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have heq : ((R.rotation : Flag E → Flag E)^[n]) x = y := by
    simpa only [Equiv.Perm.coe_pow] using hn
  rw [← heq]
  exact R.iterate_rotation_component n x

theorem sameFace_component {x y : Flag E} (h : R.SameFace x y) :
    componentOf left right (left y.edge) = componentOf left right (left x.edge) := by
  rcases h with h | h
  · exact R.sameCycle_component h
  · have hh := R.sameCycle_component h
    exact hh

omit [Fintype E] in
@[simp] theorem component_rotation_coe (q : Component left right)
    (x : Flag (ComponentEdge left right q)) :
    componentFlag ((R.componentRibbon q).rotation x) = R.rotation (componentFlag x) := rfl

omit [Fintype E] in
@[simp] theorem component_along_coe {q : Component left right}
    (x : Flag (ComponentEdge left right q)) :
    componentFlag (along x) = along (componentFlag x) := rfl

omit [Fintype E] in
theorem component_iterate_coe (q : Component left right) (n : ℕ)
    (x : Flag (ComponentEdge left right q)) :
    componentFlag (((R.componentRibbon q).rotation : _ → _)^[n] x) =
      (R.rotation : _ → _)^[n] (componentFlag x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      component_rotation_coe, ih]

/-- Inclusion preserves and reflects actual oriented boundary cycles. -/
theorem component_sameCycle_iff (q : Component left right)
    (x y : Flag (ComponentEdge left right q)) :
    (R.componentRibbon q).rotation.SameCycle x y ↔
      R.rotation.SameCycle (componentFlag x) (componentFlag y) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    have hh := congrArg componentFlag hn
    simpa only [zpow_natCast, Equiv.Perm.coe_pow, component_iterate_coe] using hh
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    apply componentFlag_injective q
    simpa only [zpow_natCast, Equiv.Perm.coe_pow, component_iterate_coe] using hn

/-- Inclusion preserves and reflects the actual unoriented facial circles. -/
theorem component_sameFace_iff (q : Component left right)
    (x y : Flag (ComponentEdge left right q)) :
    (R.componentRibbon q).SameFace x y ↔ R.SameFace (componentFlag x) (componentFlag y) := by
  simp only [SameFace, R.component_sameCycle_iff, component_along_coe]

/-- A component facial circle maps to its original ribbon circle. -/
noncomputable def componentFaceMap (q : Component left right) : (R.componentRibbon q).FaceIndex → R.FaceIndex :=
  Quotient.map componentFlag (fun _ _ h => (R.component_sameFace_iff q _ _).mp h)

@[simp] theorem componentFaceMap_faceOf (q : Component left right)
    (x : Flag (ComponentEdge left right q)) :
    R.componentFaceMap q ((R.componentRibbon q).faceOf x) = R.faceOf (componentFlag x) := rfl

theorem componentFaceMap_injective (q : Component left right) :
    Function.Injective (R.componentFaceMap q) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h x =>
      induction b using Quotient.inductionOn with
      | h y =>
          intro h
          exact Quotient.sound ((R.component_sameFace_iff q x y).mpr (Quotient.exact h))

/-- All component facial circles map to the global facial circles. -/
noncomputable def componentFacePartitionMap : ((q : Component left right) × (R.componentRibbon q).FaceIndex) →
    R.FaceIndex := fun qf => R.componentFaceMap qf.1 qf.2

theorem componentFacePartitionMap_injective : Function.Injective R.componentFacePartitionMap := by
  rintro ⟨q, f⟩ ⟨r, g⟩ h
  induction f using Quotient.inductionOn with
  | h x =>
      induction g using Quotient.inductionOn with
      | h y =>
          have hxy : R.SameFace (componentFlag x) (componentFlag y) := Quotient.exact h
          have hqr : q = r := x.edge.property.symm.trans
            ((R.sameFace_component hxy).symm.trans y.edge.property)
          subst r
          apply Sigma.mk.inj_iff.mpr
          exact ⟨rfl, heq_of_eq (R.componentFaceMap_injective q h)⟩

theorem componentFacePartitionMap_surjective : Function.Surjective R.componentFacePartitionMap := by
  intro f
  let x := R.faceRoot f
  let q := componentOf left right (left x.edge)
  refine ⟨⟨q, (R.componentRibbon q).faceOf (inComponent q x rfl)⟩, ?_⟩
  exact R.faceOf_root f

/-- The exact face-cell partition: each genuine boundary circle belongs to
exactly one actual graph component. -/
noncomputable def componentFacePartition :
    ((q : Component left right) × (R.componentRibbon q).FaceIndex) ≃ R.FaceIndex :=
  Equiv.ofBijective R.componentFacePartitionMap
    ⟨R.componentFacePartitionMap_injective, R.componentFacePartitionMap_surjective⟩

/-- The face set of an edge-free component has no flag representatives. -/
theorem componentFace_isEmpty (q : Component left right)
    (he : ¬Nonempty (ComponentEdge left right q)) : IsEmpty (R.componentRibbon q).FaceIndex := by
  refine ⟨fun f => ?_⟩
  exact he ⟨((R.componentRibbon q).faceRoot f).edge⟩

/-- The capping convention adds exactly one disk to an edge-free component. -/
noncomputable def cappedFaceEquiv (q : Component left right) :
    R.CappedFace q ≃ (R.componentRibbon q).FaceIndex ⊕
      PLift (¬Nonempty (ComponentEdge left right q)) := by
  by_cases he : Nonempty (ComponentEdge left right q)
  · rw [CappedFace, ite_eq_left he]
    let : IsEmpty (PLift (¬Nonempty (ComponentEdge left right q))) := ⟨fun h => h.down he⟩
    exact (Equiv.sumEmpty _ _).symm
  · rw [CappedFace, ite_eq_right he]
    let : IsEmpty (R.componentRibbon q).FaceIndex := R.componentFace_isEmpty q he
    let : Unique (PLift (¬Nonempty (ComponentEdge left right q))) :=
      ⟨⟨⟨he⟩⟩, fun x => Subsingleton.elim x _⟩
    exact (Equiv.ofUnique _ _).trans (Equiv.emptySum _ _).symm

/-- All capped boundary cells are exactly the traced circles together with
one disk for every isolated original vertex. -/
noncomputable def cappedFacePartition :
    ((q : Component left right) × R.CappedFace q) ≃
      R.FaceIndex ⊕ IsolatedVertex left right :=
  (Equiv.sigmaCongrRight R.cappedFaceEquiv).trans
    ((Equiv.sigmaSumDistrib (fun q => (R.componentRibbon q).FaceIndex)
      (fun q => PLift (¬Nonempty (ComponentEdge left right q)))).trans
      (Equiv.sumCongr R.componentFacePartition
        ((Equiv.sigmaPLiftEquivSubtype _).trans (isolatedComponentEquiv left right))))

end WeightedMIS.EmbeddingFaces.Ribbon
