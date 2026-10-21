module

public import WeightedMIS.FlagKeyFaces
public import WeightedMIS.ComputedFaceMatrix
public import WeightedMIS.RegisterPotentialStep

/-!
# Even-face rows as alternating sums over boundary cycles

The alternating row of a boundary walk is the alternating count of the
positions of each edge on the traced cycle. The stored even-face matrix is
therefore determined by the even facial cycles of the canonical enumeration,
row by row and edge by edge. On flag keys the same sum is computed with edge
words, and with signed binary words by a right fold that adds one at a
matching position and negates at every position.
-/

@[expose] public section

namespace WeightedMIS.FaceRowSemantics

open WeightedMIS.FiniteCycleEnumeration WeightedMIS.EmbeddingFaces WeightedMIS.RibbonTable
open WeightedMIS.EfficientSearch WeightedMIS.FlagKeyFaces WeightedMIS.RegisterPotentialStep

/-! ## Alternating rows of position lists -/

section Alt

variable {α E : Type*} [DecidableEq E]

/-- Alternating count of the positions whose edge is `e`. -/
def altRow (edge : α → E) : List α → E → ℤ
  | [], _ => 0
  | x :: l, e => (if edge x = e then 1 else 0) - altRow edge l e

theorem altRow_append_single (edge : α → E) (l : List α) (y : α) (e : E) :
    altRow edge (l ++ [y]) e = altRow edge l e + (-1) ^ l.length * (if edge y = e then 1 else 0) := by
  induction l with
  | nil => simp [altRow]
  | cons x l ih =>
    simp only [List.cons_append, altRow, ih, List.length_cons, pow_succ]
    ring

theorem natAbs_altRow_le (edge : α → E) (l : List α) (e : E) :
    (altRow edge l e).natAbs ≤ l.length := by
  induction l with
  | nil => simp [altRow]
  | cons x l ih =>
    simp only [altRow, List.length_cons]
    split <;> omega

theorem altRow_map {β F : Type*} [DecidableEq F] (edge : α → E) (edge' : β → F) (enc : α → β)
    (g : E → F) (hg : Function.Injective g) (hcomm : ∀ x, edge' (enc x) = g (edge x))
    (l : List α) (e : E) : altRow edge' (l.map enc) (g e) = altRow edge l e := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, altRow, ih, hcomm, hg.eq_iff]

end Alt

theorem trace_succ {α : Type*} (f : α → α) (n : ℕ) (x : α) :
    trace f (n + 1) x = trace f n x ++ [f^[n] x] := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change x :: trace f (n + 1) (f x) = x :: trace f n (f x) ++ [f^[n + 1] x]
    rw [ih, Function.iterate_succ_apply]
    rfl

/-! ## Boundary rows of traced walks -/

section Boundary

variable {V E : Type*} [DecidableEq E] {left right : E → V}

theorem row_castEnd {a b c : V} (p : Faces.Boundary left right a b) (h : b = c) (e : E) :
    (p.castEnd h).row e = p.row e := by
  subst c
  rfl

theorem row_appendFlag (R : Ribbon left right) {a : V} (x : Flag E)
    (p : Faces.Boundary left right a (x.vertex left right)) (e : E) :
    (R.appendFlag x p).row e = p.row e + (-1) ^ p.length * (if x.edge = e then 1 else 0) := by
  rcases x with ⟨f, s, t⟩
  cases t <;> simp only [Ribbon.appendFlag, row_castEnd, Faces.Boundary.row] <;>
    by_cases hf : e = f <;> simp [hf, eq_comm]
  all_goals rfl

/-- The row of a traced walk is the alternating count along its flag trace. -/
theorem row_trace (R : Ribbon left right) (x : Flag E) (n : ℕ) (e : E) :
    (R.trace x n).row e = altRow Flag.edge (trace R.rotation n x) e := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Ribbon.trace, row_castEnd, row_appendFlag, ih, R.trace_length, trace_succ,
      altRow_append_single, trace_length]

variable [Fintype E] (R : Ribbon left right) (order : List (Flag E))

theorem enumeratedFace_row (i : R.EnumeratedIndex order) (e : E) :
    (R.enumeratedFace order i).boundary.row e =
      altRow Flag.edge (cycleList R.rotation (R.enumeratedRoot order i)) e := by
  simp only [Ribbon.enumeratedFace, row_castEnd, row_trace, cycleList]

theorem filter_finRange_get {β : Type*} (l : List β) (p : β → Bool) :
    ((List.finRange l.length).filter (fun i => p (l.get i))).map l.get = l.filter p := by
  have h := (List.filter_map (f := l.get) (p := p) (l := List.finRange l.length)).symm
  rw [List.map_get_finRange] at h
  exact h

/-- The stored even rows are taken at exactly the even computed roots. -/
theorem evenRootIndices_roots :
    (R.evenRootIndices order).map (R.enumeratedRoot order) = evenRoots R order := by
  have hp : ∀ i : R.EnumeratedIndex order,
      decide (Even (R.enumeratedFace order i).boundary.length) =
        (fun x => !parity (cycleList R.rotation x)) ((R.enumeratedRoots order).get i) := by
    intro i
    rw [R.enumeratedFace_length]
    have hlen : (cycleList R.rotation (R.enumeratedRoot order i)).length =
        periodLength R.rotation (R.enumeratedRoot order i) := by rw [cycleList, trace_length]
    change decide (Even (periodLength R.rotation (R.enumeratedRoot order i))) =
      !parity (cycleList R.rotation (R.enumeratedRoot order i))
    rcases hq : parity (cycleList R.rotation (R.enumeratedRoot order i)) with _ | _
    · have he := (parity_eq_false_iff _).mp hq
      rw [hlen] at he
      simp [he]
    · have he : ¬Even (periodLength R.rotation (R.enumeratedRoot order i)) := by
        intro h'
        rw [← hlen] at h'
        have := (parity_eq_false_iff _).mpr h'
        rw [hq] at this
        exact absurd this (by simp)
      simp [he]
  unfold Ribbon.evenRootIndices
  simp_rw [hp]
  exact filter_finRange_get (R.enumeratedRoots order) (fun x => !parity (cycleList R.rotation x))

theorem computedIntegerMatrix_eq_altRow (r : R.EvenRowIndex order) (e : E) :
    R.computedIntegerMatrix order r e =
      altRow Flag.edge (cycleList R.rotation ((evenRoots R order).get
        ⟨r.val, by rw [← evenRootIndices_roots, List.length_map]; exact r.isLt⟩)) e := by
  rw [Ribbon.computedIntegerMatrix, enumeratedFace_row]
  congr 3
  have h := evenRootIndices_roots R order
  have hr : r.val < ((R.evenRootIndices order).map (R.enumeratedRoot order)).length := by
    simp
  have := List.getElem_of_eq h hr
  simp only [List.getElem_map] at this
  exact this

theorem evenRow_count :
    (R.evenRootIndices order).length = (evenRoots R order).length := by
  rw [← evenRootIndices_roots, List.length_map]

end Boundary

/-- The fully stored matrix is the alternating row list of the even cycles. -/
theorem storedEvenMatrix_eq {V : Type*} {m : ℕ} {left right : Fin m → V} (R : Ribbon left right) :
    R.storedEvenMatrix = (evenRoots R (Flag.canonicalOrder m)).map
      (fun x => (List.finRange m).map (fun e => altRow Flag.edge (cycleList R.rotation x) e)) := by
  rw [Ribbon.storedEvenMatrix]
  rw [← evenRootIndices_roots, List.map_map]
  conv_rhs => rw [← List.map_get_finRange (R.evenRootIndices (Flag.canonicalOrder m)), List.map_map]
  apply List.map_congr_left
  intro r _
  apply List.map_congr_left
  intro e _
  rw [Ribbon.computedIntegerMatrix, enumeratedFace_row]

/-! ## Key-level and word-level rows -/

section Keys

variable {W b : ℕ}

/-- Alternating count of the positions of an edge word on a key cycle. -/
abbrev altRowK (e : Bits W) (c : List (Bits (W + 2))) : ℤ := altRow edgePart c e

theorem altRowK_encode {m : ℕ} (hm : m < 2 ^ W) (c : List (EmbeddingFaces.Flag (Fin m))) (e : Fin m) :
    altRowK (word W e.val) (c.map (flagKey W)) = altRow Flag.edge c e :=
  altRow_map Flag.edge edgePart (flagKey W) (fun e : Fin m => word W e.val)
    (fun _ _ h => (word_fin_inj hm).mp h) (fun _ => rfl) c e

/-- Right fold computing an alternating count with signed binary words:
negate at every position and add one at matching positions. -/
def entryW (one zero : Bits b) (e : Bits W) : List (Bits (W + 2)) → Word b
  | [] => (false, zero)
  | k :: c =>
      let v := entryW one zero e c
      if edgePart k = e then (BinaryRational.signedAdd false (!v.1) one v.2).1 else (!v.1, v.2)

theorem entryW_value (one zero : Bits b) (hone : one.value = 1) (hzero : zero.value = 0)
    (e : Bits W) (c : List (Bits (W + 2))) (hc : c.length < 2 ^ b) :
    value (entryW one zero e c) = altRowK e c := by
  induction c with
  | nil => simp [entryW, value, hzero, BinaryRational.signed, altRow]
  | cons k c ih =>
    have hc' : c.length < 2 ^ b := by simp at hc; omega
    have hv := ih hc'
    have hmag : (entryW one zero e c).2.value ≤ c.length := by
      rw [← value_natAbs, hv]
      exact natAbs_altRow_le _ _ _
    simp only [entryW]
    split
    · rename_i hk
      have hfit : one.value + (entryW one zero e c).2.value < 2 ^ b := by
        simp at hc; omega
      rw [value, BinaryRational.signedAdd_value _ _ _ _ hfit, signed_not]
      change BinaryRational.signed false one.value + -value (entryW one zero e c) = _
      rw [hv, hone]
      simp [altRow, hk, BinaryRational.signed]
      ring
    · rename_i hk
      change BinaryRational.signed (!(entryW one zero e c).1) (entryW one zero e c).2.value = _
      rw [signed_not]
      change -value (entryW one zero e c) = _
      rw [hv]
      simp [altRow, hk]

/-- One stored row: one entry per table record, in table order. -/
def rowW (one zero : Bits b) (T : List (EdgeRec W)) (c : List (Bits (W + 2))) : List (Word b) :=
  T.map (fun r => entryW one zero r.key c)

/-- The rows of a list of key cycles. -/
def rowsW (one zero : Bits b) (T : List (EdgeRec W)) (cs : List (List (Bits (W + 2)))) :
    List (List (Word b)) :=
  cs.map (rowW one zero T)

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- Word rows of the key cycles denote the stored even-face matrix. -/
theorem rowsW_encode (hm : m < 2 ^ W) (hb : 4 * m < 2 ^ b) (one zero : Bits b)
    (hone : one.value = 1) (hzero : zero.value = 0) (R : Ribbon left right) :
    List.Forall₂ (List.Forall₂ (fun w z => value w = z))
      (rowsW one zero (encodeRibbon W R)
        ((evenRoots R (EmbeddingFaces.Flag.canonicalOrder m)).map
          (fun x => (cycleList R.rotation x).map (flagKey W))))
      R.storedEvenMatrix := by
  rw [storedEvenMatrix_eq, rowsW, List.map_map, List.forall₂_map_left_iff,
    List.forall₂_map_right_iff]
  apply List.forall₂_same.mpr
  intro x _
  rw [Function.comp_apply, rowW, encodeRibbon, List.map_map, List.forall₂_map_left_iff,
    List.forall₂_map_right_iff]
  apply List.forall₂_same.mpr
  intro e _
  have hlen : ((cycleList R.rotation x).map (flagKey W)).length < 2 ^ b := by
    rw [List.length_map, cycleList_length]
    have hc : Function.minimalPeriod R.rotation x ≤ Fintype.card (EmbeddingFaces.Flag (Fin m)) :=
      Function.minimalPeriod_le_card
    simp only [EmbeddingFaces.Flag.card, Fintype.card_fin] at hc
    omega
  change value (entryW one zero (word W e.val) _) = _
  rw [entryW_value one zero hone hzero _ _ hlen, altRowK_encode hm]

end Keys

end WeightedMIS.FaceRowSemantics
