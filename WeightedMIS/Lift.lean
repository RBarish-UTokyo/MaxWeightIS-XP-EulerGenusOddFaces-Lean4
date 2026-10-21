module

public import WeightedMIS.Expanded

/-!
# Completeness witnesses for the bounded expanded graph

A list of closed signed-stub walks using at most m arcs lifts into the actual
finite expanded graph. If its total W-signature is zero and its parity is odd,
the lift joins the prescribed source to target and uses exactly the same labels.
The proof does not assume that arbitrary unbounded feasible flows fit in the box.
-/

@[expose] public section

namespace WeightedMIS.Lift

open WeightedMIS.Walks WeightedMIS.Expanded

/-- Encode an arbitrary integer vector in the finite box by reduction modulo
4m+1. It decodes to the original vector whenever that vector lies in the box. -/
def encode {Coord : Type*} (m : ℕ) (z : Coord → ℤ) : Box Coord m :=
  fun r => ⟨(z r + 2 * (m : ℤ)).toNat % (4 * m + 1), Nat.mod_lt _ (by omega)⟩

/-- The encoding is exact on the intended interval. -/
theorem coordinate_encode {Coord : Type*} (m : ℕ) (z : Coord → ℤ) (r : Coord)
    (h : |z r| ≤ 2 * (m : ℤ)) : coordinate (encode m z) r = z r := by
  have hb := abs_le.mp h
  have hn : 0 ≤ z r + 2 * (m : ℤ) := by omega
  have hlt : (z r + 2 * (m : ℤ)).toNat < 4 * m + 1 := by omega
  simp only [coordinate, encode, Nat.mod_eq_of_lt hlt]
  omega

/-- Decoded coordinates determine a box state. -/
theorem box_ext {Coord : Type*} {m : ℕ} {z z' : Box Coord m}
    (h : ∀ r, coordinate z r = coordinate z' r) : z = z' := by
  funext r
  apply Fin.ext
  have hr := h r
  dsimp [coordinate] at hr
  omega

/-- Integer sum of the signature labels seen so far. -/
def accumulated {Edge Coord : Type*} (W : Edge → Coord → ℤ) (l : List Edge) (r : Coord) : ℤ :=
  (l.map (fun e => W e r)).sum

/-- The signature state associated with a prefix of original-edge labels. -/
def traceBox {Edge Coord : Type*} (m : ℕ) (W : Edge → Coord → ℤ) (l : List Edge) : Box Coord m :=
  encode m (accumulated W l)

/-- The parity state associated with a prefix. -/
def traceParity {Edge : Type*} (π : Edge → ZMod 2) (l : List Edge) : ZMod 2 :=
  (l.map π).sum

@[simp] theorem traceParity_nil {Edge : Type*} (π : Edge → ZMod 2) : traceParity π [] = 0 := rfl

@[simp] theorem traceParity_snoc {Edge : Type*} (π : Edge → ZMod 2) (l : List Edge) (e : Edge) :
    traceParity π (l ++ [e]) = traceParity π l + π e := by
  simp [traceParity]

/-- For prefixes of at most m labels, the coordinate encoding is exact. -/
theorem coordinate_traceBox {Edge Coord : Type*} (m : ℕ)
    (W : Edge → Coord → ℤ) (l : List Edge) (r : Coord)
    (hW : ∀ e r, |W e r| ≤ 2) (hlen : l.length ≤ m) :
    coordinate (traceBox m W l) r = accumulated W l r := by
  apply coordinate_encode
  have h := abs_sum_le_two_length l (fun e => W e r) (fun e _ => hW e r)
  have hc : (l.length : ℤ) ≤ (m : ℤ) := by exact_mod_cast hlen
  dsimp [accumulated]
  omega

@[simp] theorem traceBox_nil {Edge Coord : Type*} (m : ℕ) (W : Edge → Coord → ℤ) :
    traceBox m W [] = zeroBox Coord m := by
  apply box_ext
  intro r
  rw [coordinate_zeroBox]
  exact coordinate_encode m (accumulated W []) r (by simp [accumulated])

/-- Appending one original-edge label produces exactly the allowed update. -/
theorem traceBox_snoc {Edge Coord : Type*} (m : ℕ) (W : Edge → Coord → ℤ)
    (l : List Edge) (e : Edge) (hW : ∀ e r, |W e r| ≤ 2)
    (hlen : (l ++ [e]).length ≤ m) (r : Coord) :
    coordinate (traceBox m W (l ++ [e])) r = coordinate (traceBox m W l) r + W e r := by
  have hp : l.length ≤ m := by simpa using (le_trans (by simp : l.length ≤ (l ++ [e]).length) hlen)
  rw [coordinate_traceBox m W (l ++ [e]) r hW hlen, coordinate_traceBox m W l r hW hp]
  simp [accumulated]

/-- Lift a working portion, preserving every original edge occurrence. -/
theorem lift_walk {Row Edge Coord : Type*} (C : Edge → Column Row)
    (W : Edge → Coord → ℤ) (π : Edge → ZMod 2) (m : ℕ)
    (hW : ∀ e r, |W e r| ≤ 2) (anchor : State Row)
    {u v : State Row} (w : Walk C u v) (before : List Edge)
    (hlen : (before ++ w.labels).length ≤ m) :
    ∃ path : Path C W π m
        (.work anchor u (traceBox m W before) (traceParity π before))
        (.work anchor v (traceBox m W (before ++ w.labels)) (traceParity π (before ++ w.labels))),
      path.labels = w.labels := by
  induction w generalizing before with
  | nil u =>
      rw [Walk.labels, List.append_nil]
      let p : Path C W π m
          (.work anchor u (traceBox m W before) (traceParity π before))
          (.work anchor u (traceBox m W before) (traceParity π before)) := .nil _
      exact ⟨p, rfl⟩
  | @cons e v tail ih =>
      let after := before ++ [e.val.1]
      have ht : (after ++ tail.labels).length ≤ m := by
        simpa [after, Walk.labels, List.length_append, Nat.add_assoc] using hlen
      have hs : (before ++ [e.val.1]).length ≤ m := by
        simp only [Walk.labels, List.length_append, List.length_cons] at hlen
        simp only [List.length_append, List.length_singleton]
        omega
      obtain ⟨tailPath, htail⟩ := ih after ht
      have step : Step C W π m
          (.work anchor (source C e) (traceBox m W before) (traceParity π before))
          (some e.val.1)
          (.work anchor (target C e) (traceBox m W after) (traceParity π after)) := by
        dsimp [after]
        rw [traceParity_snoc]
        exact Step.move anchor e _ _ _ (traceBox_snoc m W before e.val.1 hW hs)
      have out : ∃ path : Path C W π m
          (.work anchor (source C e) (traceBox m W before) (traceParity π before))
          (.work anchor v (traceBox m W (after ++ tail.labels)) (traceParity π (after ++ tail.labels))),
          path.labels = e.val.1 :: tail.labels :=
        ⟨Path.cons _ step tailPath, by simp [Path.labels, htail]⟩
      have ha : after ++ tail.labels = before ++ e.val.1 :: tail.labels := by
        dsimp [after]
        rw [List.append_assoc]
        rfl
      rw [ha] at out
      simpa only [Walk.labels] using out

/-- Open and close one working portion at its anchor. -/
theorem lift_closed_walk {Row Edge Coord : Type*} (C : Edge → Column Row)
    (W : Edge → Coord → ℤ) (π : Edge → ZMod 2) (m : ℕ)
    (hW : ∀ e r, |W e r| ≤ 2) (w : ClosedWalk C) (before : List Edge)
    (hlen : (before ++ w.2.labels).length ≤ m) :
    ∃ path : Path C W π m
        (.hub (traceBox m W before) (traceParity π before))
        (.hub (traceBox m W (before ++ w.2.labels)) (traceParity π (before ++ w.2.labels))),
      path.labels = w.2.labels := by
  obtain ⟨middle, hm⟩ := lift_walk C W π m hW w.1 w.2 before hlen
  let entry := Path.cons none (Step.enter w.1 (traceBox m W before) (traceParity π before)) middle
  let last : Path C W π m
      (.work w.1 w.1 (traceBox m W (before ++ w.2.labels)) (traceParity π (before ++ w.2.labels)))
      (.hub (traceBox m W (before ++ w.2.labels)) (traceParity π (before ++ w.2.labels))) :=
    Path.cons none (Step.exit _ _ _) (Path.nil _)
  refine ⟨entry.append last, ?_⟩
  simp [entry, last, Path.labels, hm]

/-- Lift all closed working portions without changing their order or labels. -/
theorem lift_closed_walks {Row Edge Coord : Type*} (C : Edge → Column Row)
    (W : Edge → Coord → ℤ) (π : Edge → ZMod 2) (m : ℕ)
    (hW : ∀ e r, |W e r| ≤ 2) (ws : List (ClosedWalk C)) (before : List Edge)
    (hlen : (before ++ ws.flatMap (fun w => w.2.labels)).length ≤ m) :
    ∃ path : Path C W π m
        (.hub (traceBox m W before) (traceParity π before))
        (.hub (traceBox m W (before ++ ws.flatMap (fun w => w.2.labels)))
          (traceParity π (before ++ ws.flatMap (fun w => w.2.labels)))),
      path.labels = ws.flatMap (fun w => w.2.labels) := by
  induction ws generalizing before with
  | nil =>
      rw [List.flatMap_nil, List.append_nil]
      let p : Path C W π m
          (.hub (traceBox m W before) (traceParity π before))
          (.hub (traceBox m W before) (traceParity π before)) := .nil _
      exact ⟨p, rfl⟩
  | cons w ws ih =>
      have hw : (before ++ w.2.labels).length ≤ m := by
        simp only [List.flatMap_cons, List.length_append] at hlen ⊢
        omega
      have ht : ((before ++ w.2.labels) ++ ws.flatMap (fun w => w.2.labels)).length ≤ m := by
        simpa only [List.flatMap_cons, List.length_append, Nat.add_assoc] using hlen
      obtain ⟨first, hf⟩ := lift_closed_walk C W π m hW w before hw
      obtain ⟨rest, hr⟩ := ih (before ++ w.2.labels) ht
      have out : ∃ path : Path C W π m
          (.hub (traceBox m W before) (traceParity π before))
          (.hub (traceBox m W ((before ++ w.2.labels) ++ ws.flatMap (fun w => w.2.labels)))
            (traceParity π ((before ++ w.2.labels) ++ ws.flatMap (fun w => w.2.labels)))),
          path.labels = w.2.labels ++ ws.flatMap (fun w => w.2.labels) :=
        ⟨first.append rest, by rw [Path.labels_append, hf, hr]⟩
      rw [List.append_assoc] at out
      rw [List.flatMap_cons]
      exact out

/-- Bounded completeness: a decomposition of a binary-length witness with zero
signature and odd parity produces a source-to-target walk in the finite graph. -/
theorem source_target_of_closed_walks {Row Edge Coord : Type*} (C : Edge → Column Row)
    (W : Edge → Coord → ℤ) (π : Edge → ZMod 2) (m : ℕ)
    (hW : ∀ e r, |W e r| ≤ 2) (ws : List (ClosedWalk C))
    (hlen : (ws.flatMap (fun w => w.2.labels)).length ≤ m)
    (hsig : ∀ r, accumulated W (ws.flatMap (fun w => w.2.labels)) r = 0)
    (hpar : traceParity π (ws.flatMap (fun w => w.2.labels)) = 1) :
    ∃ path : Path C W π m (start m) (finish m),
      path.labels = ws.flatMap (fun w => w.2.labels) := by
  have hbox : traceBox m W (ws.flatMap (fun w => w.2.labels)) = zeroBox Coord m := by
    apply box_ext
    intro r
    rw [coordinate_traceBox m W _ r hW hlen, hsig, coordinate_zeroBox]
  have h := lift_closed_walks C W π m hW ws [] (by simpa using hlen)
  rw [List.nil_append, traceBox_nil, traceParity_nil, hbox, hpar] at h
  exact h

end WeightedMIS.Lift
