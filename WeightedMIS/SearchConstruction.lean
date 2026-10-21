module

public import WeightedMIS.Lift
public import WeightedMIS.NodeEncoding

/-!
# Executable outgoing lists for the finite search graph

Hub lists enumerate signed anchors. Working lists scan at most two signed arcs
per original edge, test the source, and compute one bounded coordinate update.
They never scan pairs of expanded vertices.
-/

@[expose] public section

namespace WeightedMIS.SearchConstruction

open WeightedMIS.Walks WeightedMIS.Expanded WeightedMIS.Lift WeightedMIS.NodeEncoding

/-- Executable enumeration of all signed states. -/
def signedStates (r : ℕ) : List (State (Fin r)) :=
  none :: (List.finRange r).flatMap (fun v => [some (v, false), some (v, true)])

@[simp] theorem mem_signedStates {r : ℕ} (v : State (Fin r)) : v ∈ signedStates r := by
  cases v with
  | none => simp [signedStates]
  | some v =>
      rcases v with ⟨v, b⟩
      cases b <;> simp [signedStates, List.mem_flatMap]

theorem signedStates_length (r : ℕ) : (signedStates r).length = 2 * r + 1 := by
  simp [signedStates, List.length_flatMap, Nat.mul_comm]

/-- Executable enumeration of the actual signed arcs, preserving coincident
arcs and retaining just one loop for a zero column. -/
def signedArcs {r m : ℕ} (C : Fin m → Column (Fin r)) : List (Arc C) :=
  (List.finRange m).flatMap (fun e =>
    let forward : Arc C := ⟨(e, false), Or.inr rfl⟩
    if h : C e = .zero then [forward]
    else [forward, ⟨(e, true), Or.inl h⟩])

theorem mem_signedArcs {r m : ℕ} (C : Fin m → Column (Fin r)) (a : Arc C) :
    a ∈ signedArcs C := by
  rcases a with ⟨⟨e, b⟩, h⟩
  apply List.mem_flatMap.mpr
  refine ⟨e, by simp, ?_⟩
  cases b with
  | false => split <;> simp
  | true =>
      have hn : C e ≠ .zero := by simpa using h
      simp [hn]

theorem signedArcs_length_le {r m : ℕ} (C : Fin m → Column (Fin r)) :
    (signedArcs C).length ≤ 2 * m := by
  let f (e : Fin m) : List (Arc C) :=
    if h : C e = .zero then [⟨(e, false), Or.inr rfl⟩]
    else [⟨(e, false), Or.inr rfl⟩, ⟨(e, true), Or.inl h⟩]
  have hf (e : Fin m) : (f e).length ≤ 2 := by
    dsimp [f]
    split <;> simp
  have aux (l : List (Fin m)) : (l.flatMap f).length ≤ 2 * l.length := by
    induction l with
    | nil => simp
    | cons a l ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have ha := hf a
        omega
  simpa [signedArcs, f] using aux (List.finRange m)

/-- Try the actual signature update. A failed range check emits no arc. -/
def updateBox {d : ℕ} (radius : ℕ) (z : Box (Fin d) radius) (delta : Fin d → ℤ) :
    Option (Box (Fin d) radius) :=
  if ∀ i, |coordinate z i + delta i| ≤ 2 * (radius : ℤ) then
    some (encode radius (fun i => coordinate z i + delta i))
  else none

/-- Exact range checking: successful updates are precisely the coordinate
solutions represented by states of the finite box. -/
theorem updateBox_eq_some_iff {d : ℕ} (radius : ℕ)
    (z z' : Box (Fin d) radius) (delta : Fin d → ℤ) :
    updateBox radius z delta = some z' ↔
      ∀ i, coordinate z' i = coordinate z i + delta i := by
  unfold updateBox
  split
  next h =>
    constructor
    · intro he
      have hz := Option.some.inj he
      subst z'
      exact fun i => coordinate_encode radius _ i (h i)
    · intro hz
      congr 1
      apply box_ext
      intro i
      rw [coordinate_encode radius _ i (h i), hz]
  next h =>
    constructor
    · intro he; cases he
    · intro hz
      apply False.elim
      apply h
      intro i
      rw [← hz i]
      exact coordinate_bound z' i

/-- A single signed-arc candidate contributes zero or one outgoing move. -/
def moveCandidate {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (anchor current : State (Fin r)) (z : Box (Fin d) radius) (p : ZMod 2) (a : Arc C) :
    Option (Option (Fin m) × Node (Fin r) (Fin d) radius) :=
  if source C a = current then
    (updateBox radius z (W a.val.1)).map
      (fun z' => (some a.val.1, .work anchor (target C a) z' (p + π a.val.1)))
  else none

/-- All outgoing arcs, produced by local candidate scans. -/
def outgoing {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) :
    Node (Fin r) (Fin d) radius → List (Option (Fin m) × Node (Fin r) (Fin d) radius)
  | .hub z p => (signedStates r).map (fun a => (none, .work a a z p))
  | .work anchor current z p =>
      (if current = anchor then [(none, .hub z p)] else []) ++
        (signedArcs C).filterMap (moveCandidate C W π radius anchor current z p)

/-- A generated move is exactly an original arc with a valid updated box. -/
theorem moveCandidate_eq_some_iff {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (anchor current : State (Fin r)) (z : Box (Fin d) radius) (p : ZMod 2)
    (a : Arc C) (label : Option (Fin m)) (v : Node (Fin r) (Fin d) radius) :
    moveCandidate C W π radius anchor current z p a = some (label, v) ↔
      source C a = current ∧ ∃ z' : Box (Fin d) radius,
        (∀ i, coordinate z' i = coordinate z i + W a.val.1 i) ∧
        (some a.val.1, Node.work anchor (target C a) z' (p + π a.val.1)) = (label, v) := by
  by_cases hs : source C a = current
  · simp [moveCandidate, hs, Option.map_eq_some_iff, updateBox_eq_some_iff]
  · simp [moveCandidate, hs]

/-- Every emitted outgoing entry is an actual expanded-graph step. -/
theorem outgoing_sound {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (s t : Node (Fin r) (Fin d) radius) (label : Option (Fin m))
    (h : (label, t) ∈ outgoing C W π radius s) : Step C W π radius s label t := by
  cases s with
  | hub z p =>
      obtain ⟨a, _, he⟩ := List.mem_map.mp h
      cases he
      exact Step.enter a z p
  | work anchor current z p =>
      rcases List.mem_append.mp h with he | hm
      · split at he
        next hc =>
          have ht := List.mem_singleton.mp he
          cases ht
          subst current
          exact Step.exit anchor z p
        next hc => simp at he
      · obtain ⟨a, _, ha⟩ := List.mem_filterMap.mp hm
        obtain ⟨hs, z', hz, he⟩ := (moveCandidate_eq_some_iff C W π radius _ _ _ _ _ _ _).mp ha
        cases he
        rw [← hs]
        exact Step.move anchor a z z' p hz

/-- Every actual expanded-graph step occurs in its source's generated list. -/
theorem outgoing_complete {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    {s t : Node (Fin r) (Fin d) radius} {label : Option (Fin m)}
    (h : Step C W π radius s label t) : (label, t) ∈ outgoing C W π radius s := by
  cases h with
  | enter a z p =>
      apply List.mem_map.mpr
      exact ⟨a, mem_signedStates a, rfl⟩
  | exit a z p => simp [outgoing]
  | move anchor a z z' p hz =>
      apply List.mem_append.mpr
      right
      apply List.mem_filterMap.mpr
      refine ⟨a, mem_signedArcs C a, ?_⟩
      apply (moveCandidate_eq_some_iff C W π radius _ _ _ _ _ _ _).mpr
      exact ⟨rfl, z', hz, rfl⟩

theorem mem_outgoing_iff {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (s t : Node (Fin r) (Fin d) radius) (label : Option (Fin m)) :
    (label, t) ∈ outgoing C W π radius s ↔ Step C W π radius s label t :=
  ⟨outgoing_sound C W π radius s t label, outgoing_complete C W π radius⟩

/-- Working-state generation has at most one exit and two moves per edge. -/
theorem working_outgoing_length_le {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (anchor current : State (Fin r)) (z : Box (Fin d) radius) (p : ZMod 2) :
    (outgoing C W π radius (.work anchor current z p)).length ≤ 1 + 2 * m := by
  have hf := List.length_filterMap_le (moveCandidate C W π radius anchor current z p) (signedArcs C)
  have ha := signedArcs_length_le C
  simp only [outgoing, List.length_append]
  split <;> simp only [List.length_singleton, List.length_nil] <;> omega

/-- Hub generation has exactly q=2r+1 entries. -/
theorem hub_outgoing_length {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (z : Box (Fin d) radius) (p : ZMod 2) :
    (outgoing C W π radius (.hub z p)).length = 2 * r + 1 := by
  simp [outgoing, signedStates_length]

/-- Executable adjacency lists on binary-encodable Fin vertex IDs. -/
def encodedOutgoing {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (s : Fin (nodeCount r d radius)) :
    List (Option (Fin m) × Fin (nodeCount r d radius)) :=
  (outgoing C W π radius ((nodeEquiv r d radius).symm s)).map
    (fun e => (e.1, nodeEquiv r d radius e.2))

/-- Numeric adjacency is exactly the concrete expanded-graph relation. -/
theorem mem_encodedOutgoing_iff {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (s t : Fin (nodeCount r d radius)) (label : Option (Fin m)) :
    (label, t) ∈ encodedOutgoing C W π radius s ↔
      Step C W π radius ((nodeEquiv r d radius).symm s) label
        ((nodeEquiv r d radius).symm t) := by
  constructor
  · intro h
    obtain ⟨⟨e, v⟩, hm, he⟩ := List.mem_map.mp h
    have hel : e = label := congrArg Prod.fst he
    have hev : nodeEquiv r d radius v = t := congrArg Prod.snd he
    subst e
    have hv : v = (nodeEquiv r d radius).symm t :=
      (nodeEquiv r d radius).eq_symm_apply.mpr hev
    subst v
    exact outgoing_sound C W π radius _ _ label hm
  · intro h
    apply List.mem_map.mpr
    refine ⟨(label, (nodeEquiv r d radius).symm t), outgoing_complete C W π radius h, ?_⟩
    simp

end WeightedMIS.SearchConstruction
