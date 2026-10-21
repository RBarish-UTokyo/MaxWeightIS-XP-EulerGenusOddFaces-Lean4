module

public import WeightedMIS.Embedding

/-!
# Independence of all even facial rows in an orientable map

A coherent orientation chooses a sign for each polygon so that the induced
traversals on the two sides of every edge disagree. A dependence of alternating
rows then induces a well-defined vertex potential along the actual vertex
links. It is an unsigned-incidence kernel vector. Nonbipartiteness kills this
potential and hence the original row dependence.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open Matrix

variable {V E F : Type*} {left right : E → V}

/-- Turn a direction bit into its signed incidence value. -/
def boolSign (b : Bool) : ℚ := if b then 1 else -1

@[simp] theorem boolSign_not (b : Bool) : boolSign (!b) = -boolSign b := by
  cases b <;> norm_num [boolSign]

@[simp] theorem boolSign_mul_self (b : Bool) : boolSign b * boolSign b = 1 := by
  cases b <;> norm_num [boolSign]

@[simp] theorem boolSign_ne_zero (b : Bool) : boolSign b ≠ 0 := by
  cases b <;> norm_num [boolSign]

/-- Alternating signs change at the cyclic last-to-first corner of an even
face as well as at every internal corner. -/
theorem alternating_rotate {n : ℕ} (hn : Even n) (i : Fin n) :
    (-1 : ℚ) ^ (finRotate n i).val = -((-1 : ℚ) ^ i.val) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      by_cases hi : i = Fin.last n
      · subst i
        have hpow := hn.neg_one_pow (α := ℚ)
        rw [pow_succ] at hpow
        simp only [finRotate_last, Fin.val_zero, pow_zero, Fin.val_last]
        linarith
      · rw [coe_finRotate_of_ne_last hi, pow_succ]
        ring

namespace SidePairing

variable {faces : F → Faces.Face left right} (P : SidePairing faces)

@[simp] theorem sign_pairing (d : Occurrence faces) :
    P.sign (P.pairing d).1 (P.pairing d).2 = (-1 : ℚ) ^ d.2.val := by
  change (-1 : ℚ) ^ (P.pairing.symm (P.pairing d)).2.val = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem forward_pairing (d : Occurrence faces) :
    P.forward (P.pairing d).1 (P.pairing d).2 = (faces d.1).boundary.forwardAt d.2 := by
  change (faces (P.pairing.symm (P.pairing d)).1).boundary.forwardAt
    (P.pairing.symm (P.pairing d)).2 = _
  rw [Equiv.symm_apply_apply]

/-- Coherent polygon orientations: after orienting each face, the two sides
of every edge induce opposite directions. This is an edge-gluing condition,
not a matrix-rank premise. -/
structure Orientation where
  sign : F → ℚ
  signs : ∀ f, sign f = 1 ∨ sign f = -1
  coherent : ∀ e,
    sign (P.face e false) * boolSign (P.forward e false) =
      -(sign (P.face e true) * boolSign (P.forward e true))

namespace Orientation

variable {P} (O : P.Orientation)

theorem sign_ne_zero (f : F) : O.sign f ≠ 0 := by
  rcases O.signs f with h | h <;> simp [h]

/-- A candidate vertex potential at an individual flag. -/
def flagValue (c : F → ℚ) (x : Flag E) : ℚ :=
  c (P.flagFace x) * P.sign x.edge x.side * O.sign (P.flagFace x) *
    boolSign (P.forward x.edge x.side) * boolSign x.endpoint

@[simp] theorem flagValue_endFlag (c : F → ℚ) (d : Occurrence faces) :
    O.flagValue c (P.endFlag d) = c d.1 * (-1 : ℚ) ^ d.2.val * O.sign d.1 := by
  simp only [flagValue, endFlag, flagFace, face_pairing, sign_pairing, forward_pairing]
  rw [mul_assoc, boolSign_mul_self, mul_one]

@[simp] theorem flagValue_startFlag (c : F → ℚ) (d : Occurrence faces) :
    O.flagValue c (P.startFlag d) = -(c d.1 * (-1 : ℚ) ^ d.2.val * O.sign d.1) := by
  simp only [flagValue, startFlag, flagFace, face_pairing, sign_pairing, forward_pairing,
    boolSign_not]
  rw [mul_neg, mul_assoc, boolSign_mul_self, mul_one]

/-- The two sides of one endpoint give the same potential by the actual
column equation and the coherent orientation. -/
theorem flagValue_across (c : F → ℚ)
    (hc : FaceRank.Dependence (fun e => P.face e false) (fun e => P.face e true)
      (fun e => P.sign e false) (fun e => P.sign e true) c)
    (e : E) (s t : Bool) :
    O.flagValue c ⟨e, s, t⟩ = O.flagValue c ⟨e, !s, t⟩ := by
  have h := hc e
  have ho := O.coherent e
  have ha : c (P.face e false) * P.sign e false =
      -(c (P.face e true) * P.sign e true) := by
    dsimp [FaceRank.Dependence] at h
    linarith
  have hv : O.flagValue c ⟨e, false, t⟩ = O.flagValue c ⟨e, true, t⟩ := by
    change (c (P.face e false) * P.sign e false) * O.sign (P.face e false) *
        boolSign (P.forward e false) * boolSign t =
      (c (P.face e true) * P.sign e true) * O.sign (P.face e true) *
        boolSign (P.forward e true) * boolSign t
    rw [mul_assoc (c (P.face e false) * P.sign e false),
      mul_assoc (c (P.face e true) * P.sign e true), ha, ho]
    ring
  cases s
  · exact hv
  · exact hv.symm

/-- The potential agrees across every actual vertex-link step. -/
theorem flagValue_linkStep (heven : ∀ f, Even (faces f).boundary.length)
    (c : F → ℚ)
    (hc : FaceRank.Dependence (fun e => P.face e false) (fun e => P.face e true)
      (fun e => P.sign e false) (fun e => P.sign e true) c)
    {x y : Flag E} (h : P.LinkStep x y) : O.flagValue c x = O.flagValue c y := by
  have hcorner (d : Occurrence faces) :
      O.flagValue c (P.endFlag d) = O.flagValue c (P.startFlag (faceNext d)) := by
    rw [flagValue_endFlag, flagValue_startFlag]
    change c d.1 * (-1 : ℚ) ^ d.2.val * O.sign d.1 =
      -(c d.1 * (-1 : ℚ) ^ (finRotate (faces d.1).boundary.length d.2).val * O.sign d.1)
    rw [alternating_rotate (heven d.1)]
    ring
  cases h with
  | across e s t => exact O.flagValue_across c hc e s t
  | corner d => exact hcorner d
  | cornerRev d => exact (hcorner d).symm

/-- Connected links make the flag potential a function of the graph vertex. -/
theorem flagValue_eq_of_vertex (hlinks : P.VertexLinks)
    (heven : ∀ f, Even (faces f).boundary.length) (c : F → ℚ)
    (hc : FaceRank.Dependence (fun e => P.face e false) (fun e => P.face e true)
      (fun e => P.sign e false) (fun e => P.sign e true) c)
    {x y : Flag E} (hxy : x.vertex left right = y.vertex left right) :
    O.flagValue c x = O.flagValue c y := by
  have h := hlinks x y hxy
  clear hxy
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (O.flagValue_linkStep heven c hc hstep)

end Orientation
end SidePairing

namespace CellularEmbedding

variable (M : CellularEmbedding left right F)

/-- A coherent orientation and nonbipartiteness force every full facial-row
dependence to vanish. This is the all-even orientable sharpening. -/
theorem orientable_dependence_zero (O : M.sides.Orientation)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (heven : ∀ f, Even (M.faces f).boundary.length) (c : F → ℚ)
    (hdep : FaceRank.Dependence (fun e => M.sides.face e false)
      (fun e => M.sides.face e true) (fun e => M.sides.sign e false)
      (fun e => M.sides.sign e true) c) : c = 0 := by
  classical
  let rep (v : V) : Flag E := Classical.choose (M.vertex_present v)
  have hrep (v : V) : (rep v).vertex left right = v :=
    Classical.choose_spec (M.vertex_present v)
  let x : V → ℚ := fun v => O.flagValue c (rep v)
  have hflag (z : Flag E) : x (z.vertex left right) = O.flagValue c z := by
    exact O.flagValue_eq_of_vertex M.vertex_links heven c hdep (hrep _)
  have hker (e : E) : x (left e) + x (right e) = 0 := by
    have hl := hflag ⟨e, false, false⟩
    have hr := hflag ⟨e, false, true⟩
    change x (left e) = _ at hl
    change x (right e) = _ at hr
    rw [hl, hr]
    change (c (M.sides.face e false) * M.sides.sign e false * O.sign (M.sides.face e false) *
      boolSign (M.sides.forward e false) * (-1)) +
      (c (M.sides.face e false) * M.sides.sign e false * O.sign (M.sides.face e false) *
      boolSign (M.sides.forward e false) * 1) = 0
    ring
  have hx : x = 0 := Incidence.kernel_eq_zero_of_nonbipartite left right hc hnb x hker
  funext f
  let d : Occurrence M.faces := ⟨f, ⟨0, M.face_nonempty f⟩⟩
  have hf := hflag (M.sides.endFlag d)
  rw [hx, Pi.zero_apply, SidePairing.Orientation.flagValue_endFlag] at hf
  change 0 = c f * (-1 : ℚ) ^ 0 * O.sign f at hf
  have hs := O.sign_ne_zero f
  simpa only [pow_zero, mul_one, Pi.zero_apply] using
    (mul_eq_zero.mp hf.symm).resolve_right hs

/-- Actual alternating rows of a connected nonbipartite orientable all-even
map are linearly independent. -/
theorem orientable_all_even_rank [Fintype F] [Fintype E]
    [DecidableEq E] [DecidableEq F]
    (O : M.sides.Orientation)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (heven : ∀ f, Even (M.faces f).boundary.length) :
    (Faces.matrix M.faces).rank = Fintype.card F := by
  let S := FaceRank.signed (fun e => M.sides.face e false) (fun e => M.sides.face e true)
    (fun e => M.sides.sign e false) (fun e => M.sides.sign e true)
  have hk : LinearMap.ker Sᵀ.mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_eq_bot_iff]
    intro c hc'
    exact M.orientable_dependence_zero O hc hnb heven c
      ((FaceRank.transpose_eq_zero_iff _ _ _ _ c).mp hc')
  have hr : S.rank = Fintype.card F := by
    rw [← Matrix.rank_transpose, Matrix.rank, LinearMap.finrank_range_of_inj]
    · exact Module.finrank_pi ℚ
    · exact LinearMap.ker_eq_bot.mp hk
  let ef : Faces.EvenFaces M.faces ≃ F :=
    { toFun := Subtype.val
      invFun := fun f => ⟨f, heven f⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have heq : Faces.matrix M.faces = S.submatrix ef (Equiv.refl E) := by
    ext f e
    exact M.sides.row_eq_signed f.val e
  rw [heq, Matrix.rank_submatrix]
  exact hr

end CellularEmbedding

end WeightedMIS.EmbeddingFaces
