module

public import WeightedMIS.EmbeddingPermutations
public import WeightedMIS.PermutationDeletion

/-!
# Inherited corner matchings after edge deletion

The retained flags are precisely the original flags on retained edges. Their
vertex rotations are constructed by first return in the original rotation;
the resulting corners are proved to be fixed-point-free involutions preserving
the supplied graph vertices. Thus deleted edge bands are genuinely spliced out.
Constructing and counting the resulting facial boundary cycles, and proving the
ambient Euler-genus comparison, require further results.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

namespace Flag

/-- Flags have exactly one edge label and two independent endpoint/side bits. -/
def equivProd (E : Type*) : Flag E ≃ E × Bool × Bool where
  toFun x := (x.edge, x.side, x.endpoint)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rcases x with ⟨e, s, t⟩; rfl

instance [Fintype E] : Fintype (Flag E) := Fintype.ofEquiv _ (equivProd E).symm

@[simp] theorem card [Fintype E] : Fintype.card (Flag E) = 4 * Fintype.card E := by
  rw [Fintype.card_congr (equivProd E)]
  simp
  omega

end Flag

namespace SidePairing

variable {V E F : Type*} [Fintype E] {left right : E → V}
    {faces : F → Faces.Face left right} (P : SidePairing faces)

/-- Flags surviving deletion of all edges outside `keep`. -/
abbrev RetainedFlag (keep : E → Prop) := {x : Flag E // keep x.edge}

omit [Fintype E] in
/-- Edge retention always retains both sides and both endpoints. -/
theorem across_retained (keep : E → Prop) (x : Flag E) :
    keep (across x).edge ↔ keep x.edge := Iff.rfl

/-- The actual inherited vertex rotation skips the deleted flags. -/
noncomputable def retainedVertexNext (keep : E → Prop) : Equiv.Perm (RetainedFlag keep) :=
  PermutationDeletion.firstReturn P.vertexNext (fun x => keep x.edge)

/-- The retained across-edge matching. -/
def retainedAcross (keep : E → Prop) : Equiv.Perm (RetainedFlag keep) :=
  across.subtypePerm (across_retained keep)

/-- The inherited corner matching is the first-return rotation followed by
crossing to the other side of the final retained edge. -/
noncomputable def retainedCorner (keep : E → Prop) : Equiv.Perm (RetainedFlag keep) :=
  PermutationDeletion.splicedCorner P.vertexNext across (fun x => keep x.edge)
    (across_retained keep)

omit [Fintype E] in
theorem across_reverses_vertexNext : Function.Semiconj across P.vertexNext P.vertexNext.symm := by
  intro x
  have h := P.across_vertexNext_across (across x)
  simpa only [across_across] using h

/-- Deletion leaves actual pairs of corners. -/
theorem retainedCorner_involutive (keep : E → Prop) :
    Function.Involutive (P.retainedCorner keep) :=
  PermutationDeletion.splicedCorner_involutive P.vertexNext across _
    (across_retained keep) across_across P.across_reverses_vertexNext

/-- A corner is never paired with itself, including after arbitrarily many
edge deletions. -/
theorem retainedCorner_ne_self (keep : E → Prop) (x : RetainedFlag keep) :
    P.retainedCorner keep x ≠ x := by
  apply PermutationDeletion.splicedCorner_ne_self P.vertexNext across _
    (across_retained keep) across_across P.across_reverses_vertexNext across_ne_self
  intro y
  simpa only [vertexNext, Equiv.trans_apply, across_across] using P.corner_ne_self y

omit [Fintype E] in
/-- Every step in the original vertex rotation remains at its original vertex. -/
theorem iterate_vertexNext_vertex (n : ℕ) (x : Flag E) :
    ((P.vertexNext : Flag E → Flag E)^[n] x).vertex left right = x.vertex left right := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', P.vertexNext_vertex, ih]

/-- Inherited corners still join the same actual graph vertex. -/
theorem retainedCorner_vertex (keep : E → Prop) (x : RetainedFlag keep) :
    (P.retainedCorner keep x).val.vertex left right = x.val.vertex left right := by
  change (across (PermutationDeletion.firstReturn P.vertexNext
    (fun y => keep y.edge) x).val).vertex left right = _
  rw [across_vertex, PermutationDeletion.firstReturn_apply]
  exact P.iterate_vertexNext_vertex _ _

/-- A single deletion trace has length at most four times the original edge
count; this is a bound on an actual trace, not on an assumed algorithm. -/
theorem retained_trace_length (keep : E → Prop) (x : RetainedFlag keep) :
    0 < PermutationDeletion.returnTime P.vertexNext (fun y => keep y.edge) x ∧
    PermutationDeletion.returnTime P.vertexNext (fun y => keep y.edge) x ≤
      4 * Fintype.card E := by
  constructor
  · exact PermutationDeletion.returnTime_pos _ _ _
  · simpa using PermutationDeletion.returnTime_le_card P.vertexNext (fun y => keep y.edge) x

/-- Every intermediate flag on a deletion trace belongs to a deleted edge. -/
theorem retained_trace_intermediate_deleted (keep : E → Prop) (x : RetainedFlag keep)
    {n : ℕ} (hn : 0 < n)
    (hlt : n < PermutationDeletion.returnTime P.vertexNext (fun y => keep y.edge) x) :
    ¬keep (((P.vertexNext : Flag E → Flag E)^[n] x.val).edge) :=
  PermutationDeletion.before_return_deleted _ _ _ hn hlt

/-- Retaining entries preserves the oriented cycles of each vertex link. -/
theorem retainedVertexNext_sameCycle (keep : E → Prop) (x y : RetainedFlag keep) :
    (P.retainedVertexNext keep).SameCycle x y ↔ P.vertexNext.SameCycle x.val y.val :=
  PermutationDeletion.sameCycle_firstReturn_iff _ _ _ _

omit [Fintype E] in
/-- Any vertex-link path stays in one of the two oriented rotation cycles. -/
theorem linkReach_rotation_or_reflection {x y : Flag E}
    (h : Relation.ReflTransGen P.LinkStep x y) :
    P.vertexNext.SameCycle x y ∨ P.vertexNext.SameCycle x (across y) := by
  have hacross (z : Flag E)
      (hz : P.vertexNext.SameCycle x z ∨ P.vertexNext.SameCycle x (across z)) :
      P.vertexNext.SameCycle x (across z) ∨
        P.vertexNext.SameCycle x (across (across z)) := by
    simpa only [across_across] using hz.symm
  have hcorner (z : Flag E)
      (hz : P.vertexNext.SameCycle x z ∨ P.vertexNext.SameCycle x (across z)) :
      P.vertexNext.SameCycle x (P.corner z) ∨
        P.vertexNext.SameCycle x (across (P.corner z)) := by
    have hrot : P.corner z = across (P.vertexNext z) := by
      simp only [vertexNext, Equiv.trans_apply, across_across]
    rw [hrot, across_across]
    have hrev : across (P.vertexNext z) = P.vertexNext.symm (across z) :=
      P.across_reverses_vertexNext z
    rw [hrev]
    simpa only [Equiv.Perm.sameCycle_apply_right,
      Equiv.Perm.sameCycle_symm_apply_right] using hz.symm
  induction h with
  | refl => exact Or.inl (Equiv.Perm.SameCycle.refl _ _)
  | @tail y z h hyz ih =>
      cases hyz with
      | across e s t => exact hacross _ ih
      | corner d =>
          simpa only [P.corner_endFlag] using hcorner (P.endFlag d) ih
      | cornerRev d =>
          have heq : P.corner (P.startFlag (faceNext d)) = P.endFlag d := by
            rw [P.corner_startFlag]
            simp [facePrev]
          simpa only [heq] using hcorner (P.startFlag (faceNext d)) ih

/-- Traversing one edge side changes its endpoint and leaves its side label. -/
def along : Equiv.Perm (Flag E) where
  toFun x := ⟨x.edge, x.side, !x.endpoint⟩
  invFun x := ⟨x.edge, x.side, !x.endpoint⟩
  left_inv := by intro x; cases x; simp
  right_inv := by intro x; cases x; simp

omit [Fintype E] in
@[simp] theorem along_along (x : Flag E) : along (along x) = x := by
  cases x
  simp [along]

omit [Fintype E] in
theorem along_ne_self (x : Flag E) : along x ≠ x := by
  intro h
  have he := congrArg Flag.endpoint h
  cases x.endpoint <;> simp [along] at he

/-- Traversal of a retained edge side remains available after deletion. -/
def retainedAlong (keep : E → Prop) : Equiv.Perm (RetainedFlag keep) :=
  along.subtypePerm (fun _ => Iff.rfl)

/-- Actual link steps of the constructed retained corner system. -/
inductive RetainedLinkStep (keep : E → Prop) : RetainedFlag keep → RetainedFlag keep → Prop where
  | across (x) : RetainedLinkStep keep x (retainedAcross keep x)
  | corner (x) : RetainedLinkStep keep x (P.retainedCorner keep x)

omit [Fintype E] in
@[simp] theorem retainedAcross_twice (keep : E → Prop) (x : RetainedFlag keep) :
    retainedAcross keep (retainedAcross keep x) = x := by
  apply Subtype.ext
  exact across_across x.val

/-- One step of the inherited vertex rotation is two actual retained link steps. -/
theorem retainedVertexNext_linkReach (keep : E → Prop) (x : RetainedFlag keep) :
    Relation.ReflTransGen (P.RetainedLinkStep keep) x (P.retainedVertexNext keep x) := by
  have h := (Relation.ReflTransGen.single (RetainedLinkStep.corner (P := P) (keep := keep) x)).tail
    (RetainedLinkStep.across (P := P) (keep := keep) (P.retainedCorner keep x))
  have heq : retainedAcross keep (P.retainedCorner keep x) = P.retainedVertexNext keep x := by
    apply Subtype.ext
    exact across_across _
  rwa [heq] at h

/-- A whole retained rotation orbit lies in its actual vertex link. -/
theorem retained_sameCycle_linkReach (keep : E → Prop) {x y : RetainedFlag keep}
    (h : (P.retainedVertexNext keep).SameCycle x y) :
    Relation.ReflTransGen (P.RetainedLinkStep keep) x y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hwalk (j : ℕ) : Relation.ReflTransGen (P.RetainedLinkStep keep) x
      ((P.retainedVertexNext keep : RetainedFlag keep → RetainedFlag keep)^[j] x) := by
    induction j with
    | zero => exact .refl
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact ih.trans (P.retainedVertexNext_linkReach keep _)
  simpa only [← Equiv.Perm.coe_pow, hn] using hwalk n

/-- Edge deletion preserves the connected local link at every retained vertex.
This proves the local surface condition for the constructed matching, rather
than assuming it for the residual graph. -/
theorem retained_vertexLinks (keep : E → Prop) (hlinks : P.VertexLinks)
    (x y : RetainedFlag keep) (hvertex : x.val.vertex left right = y.val.vertex left right) :
    Relation.ReflTransGen (P.RetainedLinkStep keep) x y := by
  rcases P.linkReach_rotation_or_reflection (hlinks x.val y.val hvertex) with h | h
  · exact P.retained_sameCycle_linkReach keep ((P.retainedVertexNext_sameCycle keep x y).mpr h)
  · have h' : P.vertexNext.SameCycle x.val (retainedAcross keep y).val := h
    have hr := P.retained_sameCycle_linkReach keep
      ((P.retainedVertexNext_sameCycle keep x (retainedAcross keep y)).mpr h')
    have hs := Relation.ReflTransGen.single
      (RetainedLinkStep.across (P := P) (keep := keep) (retainedAcross keep y))
    rw [retainedAcross_twice] at hs
    exact hr.trans hs

end SidePairing
end WeightedMIS.EmbeddingFaces
