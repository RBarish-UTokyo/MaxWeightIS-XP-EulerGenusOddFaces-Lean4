module

public import WeightedMIS.RibbonLinks

/-!
# The actual dual ribbon of a polygon-side embedding

Duality exchanges the side and endpoint bits of every original flag. Its
corner matching is the conjugate of the original matching. Thus dual vertices
are actual original faces, and the edge labels are unchanged. All local
matching properties are proved from the original boundary data.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

variable {V E F : Type*} {left right : E → V} {faces : F → Faces.Face left right}

namespace Flag

/-- Interchange vertex endpoints and face sides when passing to the dual. -/
def swapSideEndpoint : Equiv.Perm (Flag E) where
  toFun x := ⟨x.edge, x.endpoint, x.side⟩
  invFun x := ⟨x.edge, x.endpoint, x.side⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x; rfl

@[simp] theorem swapSideEndpoint_twice (x : Flag E) :
    swapSideEndpoint (swapSideEndpoint x) = x := by cases x; rfl

@[simp] theorem swapSideEndpoint_across (x : Flag E) :
    swapSideEndpoint (SidePairing.across x) = SidePairing.along (swapSideEndpoint x) := rfl

@[simp] theorem swapSideEndpoint_along (x : Flag E) :
    swapSideEndpoint (SidePairing.along x) = SidePairing.across (swapSideEndpoint x) := rfl

end Flag

namespace SidePairing

variable (P : SidePairing faces)

/-- Corners stay on the same actual facial boundary. -/
theorem corner_flagFace (x : Flag E) : P.flagFace (P.corner x) = P.flagFace x := by
  obtain ⟨⟨d, t⟩, rfl⟩ := P.flagEquiv.surjective x
  cases t <;> simp [facePrev, faceNext]

/-- Swapping the flag bits makes its original face into its dual vertex. -/
theorem swap_vertex (x : Flag E) :
    (Flag.swapSideEndpoint x).vertex (fun e => P.face e false) (fun e => P.face e true) =
      P.flagFace x := by
  cases h : x.side <;> simp [Flag.swapSideEndpoint, Flag.vertex, flagFace, h]

/-- The dual corner is the very same corner with side and endpoint exchanged. -/
def dualCorner : Equiv.Perm (Flag E) :=
  (Flag.swapSideEndpoint.trans P.corner).trans Flag.swapSideEndpoint

@[simp] theorem dualCorner_apply (x : Flag E) :
    P.dualCorner x = Flag.swapSideEndpoint (P.corner (Flag.swapSideEndpoint x)) := rfl

theorem dualCorner_involutive : Function.Involutive P.dualCorner := by
  intro x
  simp

theorem dualCorner_ne_self (x : Flag E) : P.dualCorner x ≠ x := by
  intro h
  have h' := congrArg Flag.swapSideEndpoint h
  simp only [dualCorner_apply, Flag.swapSideEndpoint_twice] at h'
  exact P.corner_ne_self _ h'

theorem dualCorner_vertex (x : Flag E) :
    (P.dualCorner x).vertex (fun e => P.face e false) (fun e => P.face e true) =
      x.vertex (fun e => P.face e false) (fun e => P.face e true) := by
  rw [dualCorner_apply, P.swap_vertex, P.corner_flagFace]
  have h := P.swap_vertex (Flag.swapSideEndpoint x)
  simpa only [Flag.swapSideEndpoint_twice] using h.symm

/-- The actual dual ribbon, retaining all original edge labels and multiplicities. -/
def dualRibbon : Ribbon (fun e => P.face e false) (fun e => P.face e true) where
  corner := P.dualCorner
  involutive := P.dualCorner_involutive
  ne_self := P.dualCorner_ne_self
  vertex := P.dualCorner_vertex

/-- Endpoint coordinates do not change the actual incident face. -/
theorem flagFace_flagEquiv (d : Occurrence faces) (t : Bool) :
    P.flagFace (P.flagEquiv (d, t)) = d.1 := by
  cases t <;> simp

@[simp] theorem along_startFlag (d : Occurrence faces) :
    along (P.startFlag d) = P.endFlag d := by
  simp [along, startFlag, endFlag]

@[simp] theorem along_endFlag (d : Occurrence faces) :
    along (P.endFlag d) = P.startFlag d := rfl

/-- An original along-side move is an across move at the corresponding dual vertex. -/
theorem dual_link_along (x : Flag E) :
    P.dualRibbon.LinkStep (Flag.swapSideEndpoint x) (Flag.swapSideEndpoint (along x)) := by
  rw [Flag.swapSideEndpoint_along]
  exact .across _

/-- Original corners are the actual corners of the dual after swapping the bits. -/
theorem dual_link_corner (x : Flag E) :
    P.dualRibbon.LinkStep (Flag.swapSideEndpoint x) (Flag.swapSideEndpoint (P.corner x)) := by
  have h := Ribbon.LinkStep.corner (R := P.dualRibbon) (Flag.swapSideEndpoint x)
  simpa only [dualRibbon, dualCorner_apply, Flag.swapSideEndpoint_twice] using h

/-- Following an actual original facial occurrence makes two steps at its dual vertex. -/
theorem dual_link_next (d : Occurrence faces) :
    Relation.ReflTransGen P.dualRibbon.LinkStep
      (Flag.swapSideEndpoint (P.startFlag d))
      (Flag.swapSideEndpoint (P.startFlag (faceNext d))) := by
  have h := (Relation.ReflTransGen.single (P.dual_link_along (P.startFlag d))).tail
    (P.dual_link_corner (along (P.startFlag d)))
  simpa only [along_startFlag, P.corner_endFlag] using h

/-- Every finite sequence of original facial successors is a dual-vertex link path. -/
theorem dual_link_iterate (d : Occurrence faces) (n : ℕ) :
    Relation.ReflTransGen P.dualRibbon.LinkStep
      (Flag.swapSideEndpoint (P.startFlag d))
      (Flag.swapSideEndpoint (P.startFlag ((faceNext : Occurrence faces → Occurrence faces)^[n] d))) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (P.dual_link_next _)

/-- Iterating face successors is exactly cyclic rotation of the position index. -/
theorem faceNext_iterate (f : F) (i : Fin (faces f).boundary.length) (n : ℕ) :
    (faceNext : Occurrence faces → Occurrence faces)^[n] ⟨f, i⟩ =
      ⟨f, ((finRotate (faces f).boundary.length :
        Fin (faces f).boundary.length → Fin (faces f).boundary.length)^[n] i)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih]
      rfl

/-- Any two positions of one genuine face lie in the same dual vertex link. -/
theorem dual_link_positions (f : F) (i j : Fin (faces f).boundary.length) :
    Relation.ReflTransGen P.dualRibbon.LinkStep
      (Flag.swapSideEndpoint (P.startFlag ⟨f, i⟩))
      (Flag.swapSideEndpoint (P.startFlag ⟨f, j⟩)) := by
  let : NeZero (faces f).boundary.length := ⟨Nat.ne_of_gt i.pos⟩
  let k : Fin (faces f).boundary.length := j - i
  have hk : ((finRotate (faces f).boundary.length :
      Fin (faces f).boundary.length → Fin (faces f).boundary.length)^[k.val] i) = j := by
    rw [← finCycle_eq_finRotate_iterate, finCycle_apply]
    simp [k, sub_eq_add_neg]
  have h := P.dual_link_iterate (⟨f, i⟩ : Occurrence faces) k.val
  rw [faceNext_iterate, hk] at h
  exact h

/-- Either endpoint flag of an occurrence connects to its beginning. -/
theorem dual_link_to_start (d : Occurrence faces) (t : Bool) :
    Relation.ReflTransGen P.dualRibbon.LinkStep
      (Flag.swapSideEndpoint (P.flagEquiv (d, t)))
      (Flag.swapSideEndpoint (P.startFlag d)) := by
  cases t
  · simp only [flagEquiv_false]
    exact .refl
  · simp only [flagEquiv_true]
    have h := Relation.ReflTransGen.single (P.dual_link_along (P.endFlag d))
    simpa only [along_endFlag] using h

/-- The original cyclic facial walk supplies the connected link of its dual vertex. -/
theorem dual_link_same_face (x y : Flag E) (hface : P.flagFace x = P.flagFace y) :
    Relation.ReflTransGen P.dualRibbon.LinkStep
      (Flag.swapSideEndpoint x) (Flag.swapSideEndpoint y) := by
  obtain ⟨⟨⟨f, i⟩, t⟩, rfl⟩ := P.flagEquiv.surjective x
  obtain ⟨⟨⟨g, j⟩, u⟩, rfl⟩ := P.flagEquiv.surjective y
  have hfg : f = g := by simpa only [P.flagFace_flagEquiv] using hface
  subst g
  exact (P.dual_link_to_start ⟨f, i⟩ t).trans
    ((P.dual_link_positions f i j).trans
      (P.dualRibbon.linkReach_symm (P.dual_link_to_start ⟨f, j⟩ u)))

/-- All dual vertex links are connected, derived from the actual original
facial boundary cycles rather than supplied as an extra embedding condition. -/
theorem dual_vertexLinks : P.dualRibbon.VertexLinks := by
  intro x y hxy
  have hx := P.swap_vertex (Flag.swapSideEndpoint x)
  have hy := P.swap_vertex (Flag.swapSideEndpoint y)
  simp only [Flag.swapSideEndpoint_twice] at hx hy
  have hface : P.flagFace (Flag.swapSideEndpoint x) = P.flagFace (Flag.swapSideEndpoint y) := by
    rw [← hx, ← hy]
    exact hxy
  have h := P.dual_link_same_face (Flag.swapSideEndpoint x) (Flag.swapSideEndpoint y) hface
  simpa only [Flag.swapSideEndpoint_twice] using h

/-- Every nonempty original facial boundary supplies an actual dual vertex flag. -/
theorem dual_vertex_present (hfaces : ∀ f, 0 < (faces f).boundary.length) (f : F) :
    ∃ x : Flag E, x.vertex (fun e => P.face e false) (fun e => P.face e true) = f := by
  refine ⟨Flag.swapSideEndpoint (P.startFlag ⟨f, 0, hfaces f⟩), ?_⟩
  rw [P.swap_vertex, P.flagFace_startFlag]

end SidePairing
end WeightedMIS.EmbeddingFaces
