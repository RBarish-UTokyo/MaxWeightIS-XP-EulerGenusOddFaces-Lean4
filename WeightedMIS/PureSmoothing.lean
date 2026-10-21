module

public import WeightedMIS.SmoothingFaces
public import WeightedMIS.GraphComponents
public import WeightedMIS.OriginalFaces

/-!
# Smoothing circles without retained edges

A shared circle with no retained flag is exactly a removed original vertex
disk. The proof uses the actual connected local links and follows the actual
smoothing permutation, including the case of vertices incident only to
removed edges.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.Ribbon

open SidePairing

variable {V E : Type*} [Fintype E] {left right : E → V} (R : Ribbon left right)
    (keep : E → Prop) [DecidablePred keep]

/-- The shared circle containing an original flag, after relabelling deleted
edge coordinates. -/
noncomputable def commonFace (x : Flag E) : (R.sidePairing.smoothingRibbon keep).FaceIndex :=
  (R.sidePairing.smoothingRibbon keep).faceOf (Flag.deletionToggle keep x)

/-- Original corners always preserve the shared boundary circle. -/
theorem commonFace_corner (x : Flag E) : R.commonFace keep (R.corner x) = R.commonFace keep x := by
  have h := (R.sidePairing.smoothingRibbon keep).faceOf_corner (Flag.deletionToggle keep x)
  simpa only [commonFace, SidePairing.smoothingRibbon, Equiv.trans_apply,
    Flag.deletionToggle_twice, R.sidePairing_corner] using h

/-- Across a deleted edge is the reflection of the shared boundary circle. -/
theorem commonFace_across (x : Flag E) (hx : ¬keep x.edge) :
    R.commonFace keep (across x) = R.commonFace keep x := by
  simp only [commonFace, Flag.deletionToggle, Equiv.coe_fn_mk, across, hx, ite_false]
  exact (R.sidePairing.smoothingRibbon keep).faceOf_along (Flag.swapSideEndpoint x)

/-- A retained flag on a shared circle witnesses that the circle survives. -/
theorem commonFace_meets (x : Flag E) (hx : keep x.edge) :
    R.MeetsRetained keep (R.commonFace keep x) := by
  refine ⟨(Flag.retainedEquiv keep).symm ⟨x, hx⟩, ?_⟩
  simp only [smoothingFlag, Equiv.apply_symm_apply, commonFace, Flag.deletionToggle,
    Equiv.coe_fn_mk, hx, ite_true]

/-- A shared circle without a retained position has only deleted flags. -/
theorem not_meets_deleted {f : (R.sidePairing.smoothingRibbon keep).FaceIndex}
    (hf : ¬R.MeetsRetained keep f) {x : Flag E} (hx : R.commonFace keep x = f) :
    ¬keep x.edge := by
  intro h
  exact hf (hx ▸ R.commonFace_meets keep x h)

/-- Connected original vertex links remain inside a shared circle which has
no retained flags. -/
theorem pure_linkReach {f : (R.sidePairing.smoothingRibbon keep).FaceIndex}
    (hf : ¬R.MeetsRetained keep f) {x y : Flag E}
    (hx : R.commonFace keep x = f) (hxy : Relation.ReflTransGen R.LinkStep x y) :
    R.commonFace keep y = f := by
  induction hxy with
  | refl => exact hx
  | @tail y z _ hs ih =>
      cases hs with
      | across => exact (R.commonFace_across keep y (R.not_meets_deleted keep hf ih)).trans ih
      | corner => exact (R.commonFace_corner keep y).trans ih

/-- A flag at an isolated retained-graph vertex belongs to a deleted edge. -/
theorem isolated_flag_deleted
    (v : Incidence.IsolatedVertex (fun e : {e : E // keep e} => left e.val)
      (fun e => right e.val)) (x : Flag E) (hx : x.vertex left right = v.val) :
    ¬keep x.edge := by
  intro he
  apply v.property
  refine ⟨⟨x.edge, he⟩, ?_⟩
  cases h : x.endpoint
  · exact Or.inl (by simpa only [Flag.vertex, h, Bool.false_eq_true, ite_false] using hx)
  · exact Or.inr (by simpa only [Flag.vertex, h, ite_true] using hx)

/-- Original flags on a common circle are related by its smoothing rotation,
possibly followed by the local reflection. -/
theorem commonFace_eq_iff (x y : Flag E) :
    R.commonFace keep x = R.commonFace keep y ↔
      (R.sidePairing.smoothing keep).SameCycle x y ∨
      (R.sidePairing.smoothing keep).SameCycle x (Flag.deletionSwitch keep y) := by
  have heq : Flag.deletionToggle keep (Flag.deletionSwitch keep y) =
      along (Flag.deletionToggle keep y) := by
    simp only [Flag.deletionSwitch, Equiv.trans_apply, Flag.deletionToggle_twice]
  rw [PermutationDeletion.sameCycle_iff_of_semiconj (R.sidePairing.smoothing keep)
    (R.sidePairing.smoothingRibbon keep).rotation (Flag.deletionToggle keep)
    (Flag.deletionToggle keep).injective (R.sidePairing.smoothing_conjugate keep)]
  rw [PermutationDeletion.sameCycle_iff_of_semiconj (R.sidePairing.smoothing keep)
    (R.sidePairing.smoothingRibbon keep).rotation (Flag.deletionToggle keep)
    (Flag.deletionToggle keep).injective (R.sidePairing.smoothing_conjugate keep), heq]
  exact Quotient.eq

/-- Smoothing cannot leave a vertex incident only to deleted edges. -/
theorem isolated_iterate_vertex
    (v : Incidence.IsolatedVertex (fun e : {e : E // keep e} => left e.val)
      (fun e => right e.val)) (x : Flag E) (hx : x.vertex left right = v.val) (n : ℕ) :
    (((R.sidePairing.smoothing keep : Flag E → Flag E)^[n]) x).vertex left right = v.val := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      rw [Function.iterate_succ_apply', R.sidePairing.smoothing_apply,
        ite_eq_right (isolated_flag_deleted keep v _ ih), R.sidePairing_corner, R.vertex]
      exact ih

/-- Every original flag on a circle surrounding an isolated retained vertex
has that same vertex. -/
theorem isolated_commonFace_vertex
    (v : Incidence.IsolatedVertex (fun e : {e : E // keep e} => left e.val)
      (fun e => right e.val)) (x y : Flag E) (hx : x.vertex left right = v.val)
    (hface : R.commonFace keep x = R.commonFace keep y) : y.vertex left right = v.val := by
  have hcycle : ∀ z, (R.sidePairing.smoothing keep).SameCycle x z → z.vertex left right = v.val := by
    intro z hz
    obtain ⟨n, hn⟩ := hz.exists_nat_pow_eq
    have hv := R.isolated_iterate_vertex keep v x hx n
    have hn' : ((R.sidePairing.smoothing keep : Flag E → Flag E)^[n]) x = z := by
      simpa only [Equiv.Perm.coe_pow] using hn
    rwa [hn'] at hv
  rcases (R.commonFace_eq_iff keep x y).mp hface with h | h
  · exact hcycle y h
  · have hv := hcycle (Flag.deletionSwitch keep y) h
    have hd := isolated_flag_deleted keep v (Flag.deletionSwitch keep y) hv
    have he : (Flag.deletionSwitch keep y).edge = y.edge := by
      rw [Flag.deletionSwitch_apply]
      split <;> rfl
    rw [he] at hd
    rw [Flag.deletionSwitch_apply, ite_eq_right hd] at hv
    exact hv

/-- A removed original vertex determines a circle with no retained position. -/
theorem isolated_commonFace_pure
    (v : Incidence.IsolatedVertex (fun e : {e : E // keep e} => left e.val)
      (fun e => right e.val)) (x : Flag E) (hx : x.vertex left right = v.val) :
    ¬R.MeetsRetained keep (R.commonFace keep x) := by
  rintro ⟨y, hy⟩
  have heq : R.commonFace keep (smoothingFlag keep y) = R.commonFace keep x := by
    simpa only [commonFace, Flag.deletionToggle, Equiv.coe_fn_mk, smoothingFlag,
      Flag.retainedEquiv, y.edge.property, ite_true] using hy
  have hv := R.isolated_commonFace_vertex keep v x (smoothingFlag keep y) hx heq.symm
  exact isolated_flag_deleted keep v (smoothingFlag keep y) hv y.edge.property

/-- An original flag chosen on a shared circle. -/
noncomputable def commonRoot (f : (R.sidePairing.smoothingRibbon keep).FaceIndex) : Flag E :=
  Flag.deletionToggle keep ((R.sidePairing.smoothingRibbon keep).faceRoot f)

@[simp] theorem commonFace_root (f : (R.sidePairing.smoothingRibbon keep).FaceIndex) :
    R.commonFace keep (R.commonRoot keep f) = f := by
  simp only [commonFace, commonRoot, Flag.deletionToggle_twice, faceOf_root]

/-- A shared circle without retained edges surrounds an actual isolated
vertex of the retained graph. -/
noncomputable def pureVertexMap (hlinks : R.VertexLinks)
    (f : {f : (R.sidePairing.smoothingRibbon keep).FaceIndex // ¬R.MeetsRetained keep f}) :
    Incidence.IsolatedVertex (fun e : {e : E // keep e} => left e.val) (fun e => right e.val) :=
  ⟨(R.commonRoot keep f.val).vertex left right, by
    rintro ⟨e, he | he⟩
    · let y : Flag E := ⟨e.val, false, false⟩
      have hy : y.vertex left right = (R.commonRoot keep f.val).vertex left right := he
      have hr := R.pure_linkReach keep f.property (R.commonFace_root keep f.val)
        (hlinks _ y hy.symm)
      exact R.not_meets_deleted keep f.property hr e.property
    · let y : Flag E := ⟨e.val, false, true⟩
      have hy : y.vertex left right = (R.commonRoot keep f.val).vertex left right := he
      have hr := R.pure_linkReach keep f.property (R.commonFace_root keep f.val)
        (hlinks _ y hy.symm)
      exact R.not_meets_deleted keep f.property hr e.property⟩

/-- Connected local links prevent two pure circles from representing the
same removed vertex. -/
theorem pureVertexMap_injective (hlinks : R.VertexLinks) :
    Function.Injective (R.pureVertexMap keep hlinks) := by
  intro f g h
  have hv := congrArg Subtype.val h
  have hr := R.pure_linkReach keep f.property (R.commonFace_root keep f.val)
    (hlinks (R.commonRoot keep f.val) (R.commonRoot keep g.val) hv)
  rw [R.commonFace_root] at hr
  exact Subtype.ext hr.symm

/-- Every original vertex incident only to deleted edges contributes its
actual pure boundary circle. -/
theorem pureVertexMap_surjective (hlinks : R.VertexLinks)
    (hvertices : ∀ v, ∃ x : Flag E, x.vertex left right = v) :
    Function.Surjective (R.pureVertexMap keep hlinks) := by
  intro v
  obtain ⟨x, hx⟩ := hvertices v.val
  let f : {f : (R.sidePairing.smoothingRibbon keep).FaceIndex // ¬R.MeetsRetained keep f} :=
    ⟨R.commonFace keep x, R.isolated_commonFace_pure keep v x hx⟩
  refine ⟨f, ?_⟩
  apply Subtype.ext
  exact R.isolated_commonFace_vertex keep v x (R.commonRoot keep f.val) hx
    (R.commonFace_root keep f.val).symm

/-- Pure common circles are exactly the removed original vertex disks. -/
noncomputable def pureFaceEquiv (hlinks : R.VertexLinks)
    (hvertices : ∀ v, ∃ x : Flag E, x.vertex left right = v) :
    {f : (R.sidePairing.smoothingRibbon keep).FaceIndex // ¬R.MeetsRetained keep f} ≃
      Incidence.IsolatedVertex (fun e : {e : E // keep e} => left e.val) (fun e => right e.val) :=
  Equiv.ofBijective (R.pureVertexMap keep hlinks)
    ⟨R.pureVertexMap_injective keep hlinks, R.pureVertexMap_surjective keep hlinks hvertices⟩

/-- The common boundary circles consist exactly of retained graph boundary
circles and the disks around original vertices omitted by edge deletion. -/
noncomputable def commonFacePartition (hlinks : R.VertexLinks)
    (hvertices : ∀ v, ∃ x : Flag E, x.vertex left right = v) :
    (R.sidePairing.smoothingRibbon keep).FaceIndex ≃
      (R.restrict keep).FaceIndex ⊕
        Incidence.IsolatedVertex (fun e : {e : E // keep e} => left e.val) (fun e => right e.val) := by
  classical
  exact (Equiv.sumCompl (R.MeetsRetained keep)).symm.trans
    (Equiv.sumCongr (R.smoothingFaceEquiv keep).symm (R.pureFaceEquiv keep hlinks hvertices))

@[simp] theorem commonFacePartition_symm_inl (hlinks : R.VertexLinks)
    (hvertices : ∀ v, ∃ x : Flag E, x.vertex left right = v) (f : (R.restrict keep).FaceIndex) :
    (R.commonFacePartition keep hlinks hvertices).symm (Sum.inl f) = R.smoothingFaceMap keep f := by
  classical
  rfl

/-- On a retained boundary position the partition keeps its actual restricted
boundary circle. -/
@[simp] theorem commonFacePartition_retained (hlinks : R.VertexLinks)
    (hvertices : ∀ v, ∃ x : Flag E, x.vertex left right = v) (x : Flag {e : E // keep e}) :
    R.commonFacePartition keep hlinks hvertices (R.commonFace keep (smoothingFlag keep x)) =
      Sum.inl ((R.restrict keep).faceOf x) := by
  apply (R.commonFacePartition keep hlinks hvertices).symm.injective
  rw [Equiv.symm_apply_apply, R.commonFacePartition_symm_inl, R.smoothingFaceMap_faceOf]
  simp only [commonFace, Flag.deletionToggle, smoothingFlag, Flag.retainedEquiv,
    Equiv.coe_fn_mk, x.edge.property, ite_true]

/-- A circle around an omitted vertex maps to that actual vertex disk. -/
@[simp] theorem commonFacePartition_isolated (hlinks : R.VertexLinks)
    (hvertices : ∀ v, ∃ x : Flag E, x.vertex left right = v)
    (v : Incidence.IsolatedVertex (fun e : {e : E // keep e} => left e.val) (fun e => right e.val))
    (x : Flag E) (hx : x.vertex left right = v.val) :
    R.commonFacePartition keep hlinks hvertices (R.commonFace keep x) = Sum.inr v := by
  classical
  have hp := R.isolated_commonFace_pure keep v x hx
  simp only [commonFacePartition, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hp,
    Equiv.sumCongr_apply, Sum.map_inr, Sum.inr.injEq]
  apply Subtype.ext
  exact R.isolated_commonFace_vertex keep v x
    (R.commonRoot keep (R.commonFace keep x)) hx (R.commonFace_root keep _).symm

end WeightedMIS.EmbeddingFaces.Ribbon
