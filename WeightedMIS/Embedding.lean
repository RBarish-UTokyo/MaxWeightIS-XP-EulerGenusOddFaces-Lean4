module

public import WeightedMIS.EmbeddingVertices
public import WeightedMIS.OddRow

/-!
# Polygon-side maps with connected vertex links

Flags distinguish an edge, one of its two sides, and one of its two endpoints.
The link at a graph vertex alternates the two sides of an endpoint and the
actual corners of facial boundary walks. The local connected-link condition
excludes pinched vertices. Primal connectedness then implies dual connectedness;
it is not supplied as a dual-rank assumption.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

universe u v w
variable {V : Type u} {E : Type v} {F : Type w} {left right : E → V}

/-- One endpoint of one side of an original edge. -/
structure Flag (E : Type v) where
  edge : E
  side : Bool
  endpoint : Bool

namespace Flag

/-- Endpoint labels distinguish the two ends even when the edge is a loop. -/
def vertex (left right : E → V) (x : Flag E) : V :=
  if x.endpoint then right x.edge else left x.edge

end Flag

namespace SidePairing

variable {faces : F → Faces.Face left right} (P : SidePairing faces)

/-- Face incident to a flag. -/
def flagFace (x : Flag E) : F := P.face x.edge x.side

/-- The flag at the beginning of an actual boundary occurrence. -/
def startFlag (d : Occurrence faces) : Flag E :=
  ⟨(P.pairing d).1, (P.pairing d).2, !((faces d.1).boundary.forwardAt d.2)⟩

/-- The flag at the end of an actual boundary occurrence. -/
def endFlag (d : Occurrence faces) : Flag E :=
  ⟨(P.pairing d).1, (P.pairing d).2, (faces d.1).boundary.forwardAt d.2⟩

@[simp] theorem face_pairing (d : Occurrence faces) :
    P.face (P.pairing d).1 (P.pairing d).2 = d.1 := by
  simp [face, side]

@[simp] theorem flagFace_startFlag (d : Occurrence faces) :
    P.flagFace (P.startFlag d) = d.1 := P.face_pairing d

@[simp] theorem flagFace_endFlag (d : Occurrence faces) :
    P.flagFace (P.endFlag d) = d.1 := P.face_pairing d

@[simp] theorem startFlag_vertex (d : Occurrence faces) :
    (P.startFlag d).vertex left right = (faces d.1).boundary.startAt d.2 := by
  change (if !(faces d.1).boundary.forwardAt d.2 then right (P.pairing d).1
      else left (P.pairing d).1) =
    if (faces d.1).boundary.forwardAt d.2 then left ((faces d.1).boundary.edgeAt d.2)
      else right ((faces d.1).boundary.edgeAt d.2)
  rw [← P.edge_eq d]
  have hb (b : Bool) (x y : V) : (if !b then x else y) = (if b then y else x) := by
    cases b <;> rfl
  exact hb _ _ _

@[simp] theorem endFlag_vertex (d : Occurrence faces) :
    (P.endFlag d).vertex left right = (faces d.1).boundary.endAt d.2 := by
  simp only [endFlag, Flag.vertex, Faces.Boundary.endAt]
  rw [← P.edge_eq d]
  rfl

/-- Vertex-link steps are the two sides of one edge endpoint or an actual
facial corner (in either direction). -/
inductive LinkStep : Flag E → Flag E → Prop where
  | across (e : E) (s t : Bool) :
      LinkStep ⟨e, s, t⟩ ⟨e, !s, t⟩
  | corner (d : Occurrence faces) :
      LinkStep (P.endFlag d) (P.startFlag (faceNext d))
  | cornerRev (d : Occurrence faces) :
      LinkStep (P.startFlag (faceNext d)) (P.endFlag d)

/-- Every vertex-link step preserves the actual supplied graph vertex. -/
theorem linkStep_vertex {x y : Flag E} (h : P.LinkStep x y) :
    x.vertex left right = y.vertex left right := by
  cases h with
  | across => rfl
  | corner d =>
      simp only [endFlag_vertex, startFlag_vertex, faceNext, Equiv.sigmaCongrRight_apply]
      exact (faces d.1).boundary.endAt_eq_startAt_rotate d.2
  | cornerRev d =>
      simp only [endFlag_vertex, startFlag_vertex, faceNext, Equiv.sigmaCongrRight_apply]
      exact ((faces d.1).boundary.endAt_eq_startAt_rotate d.2).symm

/-- The local surface condition: all flags of a supplied graph vertex form
one connected link, using only actual corners and paired edge sides. -/
def VertexLinks : Prop :=
  ∀ x y : Flag E, x.vertex left right = y.vertex left right →
    Relation.ReflTransGen P.LinkStep x y

/-- Reachability in the actual face-side dual graph. -/
def DualReach (a b : F) : Prop :=
  ∃ n, Incidence.Walk (fun e => P.face e false) (fun e => P.face e true) a b n

@[refl] theorem dualReach_refl (f : F) : P.DualReach f f := ⟨0, .nil f⟩

theorem dualReach_trans {a b c : F} (h : P.DualReach a b) (k : P.DualReach b c) :
    P.DualReach a c := by
  obtain ⟨n, p⟩ := h
  obtain ⟨m, q⟩ := k
  exact ⟨n + m, OddRow.walk_append _ _ p q⟩

/-- Every local-link step either stays in a face or crosses its actual dual edge. -/
theorem linkStep_dualReach {x y : Flag E} (h : P.LinkStep x y) :
    P.DualReach (P.flagFace x) (P.flagFace y) := by
  cases h with
  | across e s t =>
      cases s
      · exact ⟨1, .forward e rfl (.nil _)⟩
      · exact ⟨1, .backward e rfl (.nil _)⟩
  | corner d =>
      simpa only [flagFace_endFlag, flagFace_startFlag, faceNext,
        Equiv.sigmaCongrRight_apply] using P.dualReach_refl d.1
  | cornerRev d =>
      simpa only [flagFace_endFlag, flagFace_startFlag, faceNext,
        Equiv.sigmaCongrRight_apply] using P.dualReach_refl d.1

/-- Incident flags at one vertex have dual-connected faces, by its actual link. -/
theorem vertex_dualReach (hlinks : P.VertexLinks) {x y : Flag E}
    (hxy : x.vertex left right = y.vertex left right) :
    P.DualReach (P.flagFace x) (P.flagFace y) := by
  have h := hlinks x y hxy
  clear hxy
  induction h with
  | refl => exact P.dualReach_refl _
  | tail _ hstep ih => exact P.dualReach_trans ih (P.linkStep_dualReach hstep)

/-- Primal walks connect the incident faces once all local vertex links are
connected. This derives dual connectivity from genuine primal traversal. -/
theorem walk_dualReach (hlinks : P.VertexLinks) {a b : V} {n : ℕ}
    (p : Incidence.Walk left right a b n) (x y : Flag E)
    (hx : x.vertex left right = a) (hy : y.vertex left right = b) :
    P.DualReach (P.flagFace x) (P.flagFace y) := by
  induction p generalizing x y with
  | nil => exact P.vertex_dualReach hlinks (hx.trans hy.symm)
  | @forward b n e hb p ih =>
      subst b
      have h₁ := ih x ⟨e, false, false⟩ hx rfl
      have h₂ := P.vertex_dualReach hlinks
        (x := ⟨e, false, true⟩) (y := y) hy.symm
      exact P.dualReach_trans h₁ h₂
  | @backward b n e hb p ih =>
      subst b
      have h₁ := ih x ⟨e, false, true⟩ hx rfl
      have h₂ := P.vertex_dualReach hlinks
        (x := ⟨e, false, false⟩) (y := y) hy.symm
      exact P.dualReach_trans h₁ h₂

/-- A connected primal graph with connected vertex links has connected full dual. -/
theorem dual_connected (hlinks : P.VertexLinks)
    (hfaces : ∀ f, 0 < (faces f).boundary.length)
    (hc : Incidence.Connected left right) :
    Incidence.Connected (fun e => P.face e false) (fun e => P.face e true) := by
  intro f g
  let d : Occurrence faces := ⟨f, ⟨0, hfaces f⟩⟩
  let d' : Occurrence faces := ⟨g, ⟨0, hfaces g⟩⟩
  obtain ⟨n, p⟩ := hc ((P.startFlag d).vertex left right) ((P.startFlag d').vertex left right)
  have h := P.walk_dualReach hlinks p (P.startFlag d) (P.startFlag d') rfl rfl
  change P.DualReach f g
  simpa only [flagFace_startFlag] using h

end SidePairing

/-- A finite polygon-side representation with genuine closed boundary walks
and connected vertex links. At least one face is present. Empty faces and unused graph vertices are excluded;
an isolated-vertex component is handled separately. No matrix rank or global
dual-connectivity conclusion is included among the fields. -/
structure CellularEmbedding (left right : E → V) (F : Type w) where
  faces : F → Faces.Face left right
  face_present : Nonempty F
  sides : SidePairing faces
  face_nonempty : ∀ f, 0 < (faces f).boundary.length
  vertex_present : ∀ v, ∃ x : Flag E, x.vertex left right = v
  vertex_links : sides.VertexLinks

namespace CellularEmbedding

variable (M : CellularEmbedding left right F)

/-- The actual side dual of a connected combinatorial embedding is connected. -/
theorem dual_connected (hc : Incidence.Connected left right) :
    Incidence.Connected (fun e => M.sides.face e false) (fun e => M.sides.face e true) :=
  M.sides.dual_connected M.vertex_links M.face_nonempty hc

/-- Every original edge has exactly two genuine facial occurrences. -/
theorem twoSides [Fintype F] [Fintype E] [DecidableEq E] : Faces.TwoSides M.faces :=
  M.sides.twoSides

/-- The actual even-face rows are independent if at least one face is odd. -/
theorem even_matrix_rank [Fintype F] [Fintype E] [DecidableEq E] [DecidableEq F]
    (hc : Incidence.Connected left right) (f : F)
    (hf : ¬ Even (M.faces f).boundary.length) :
    (Faces.matrix M.faces).rank = Fintype.card (Faces.EvenFaces M.faces) :=
  M.sides.even_matrix_rank (M.dual_connected hc) f hf

/-- The general all-even rank bound follows from the actual embedding data. -/
theorem all_even_matrix_rank [Fintype F] [Fintype E] [DecidableEq E] [DecidableEq F]
    (hc : Incidence.Connected left right)
    (heven : ∀ f, Even (M.faces f).boundary.length) :
    Fintype.card F - 1 ≤ (Faces.matrix M.faces).rank :=
  M.sides.all_even_matrix_rank (M.dual_connected hc) heven

end CellularEmbedding

end WeightedMIS.EmbeddingFaces
