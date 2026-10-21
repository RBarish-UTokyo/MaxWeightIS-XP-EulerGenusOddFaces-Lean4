module

public import WeightedMIS.SearchConstruction
public import WeightedMIS.EncodingCost

/-!
# Instrumented sparse-generation loops

This file measures actual recursive scans, separately from arithmetic bit cost.
`visits` counts coordinate predicates, source/exit tests, and list recursion.
The measured routine refines the executable outgoing generator exactly. Tuple
encoding arithmetic has its own trace in `EncodingCost`. Enumeration of the
small signed-state/arc tables and refinement of primitive arithmetic/memory
access to bit operations are intentionally separate obligations.
-/

@[expose] public section

namespace WeightedMIS.GenerationCost

open WeightedMIS.Walks WeightedMIS.Expanded WeightedMIS.Lift
open WeightedMIS.SearchConstruction WeightedMIS.NodeEncoding

structure Measured (α : Type*) where
  value : α
  visits : ℕ

/-- Inspect every coordinate, so the trace is independent of early rejection. -/
def inspect {d : ℕ} (radius : ℕ) (z : Box (Fin d) radius) (delta : Fin d → ℤ) :
    List (Fin d) → Measured Bool
  | [] => ⟨true, 1⟩
  | i :: indices =>
      let result := decide (|coordinate z i + delta i| ≤ 2 * (radius : ℤ))
      let rest := inspect radius z delta indices
      ⟨result && rest.value, rest.visits + 1⟩

theorem inspect_value {d : ℕ} (radius : ℕ) (z : Box (Fin d) radius)
    (delta : Fin d → ℤ) (indices : List (Fin d)) :
    (inspect radius z delta indices).value = true ↔
      ∀ i ∈ indices, |coordinate z i + delta i| ≤ 2 * (radius : ℤ) := by
  induction indices with
  | nil => simp [inspect]
  | cons i indices ih => simp [inspect, ih]

theorem inspect_visits {d : ℕ} (radius : ℕ) (z : Box (Fin d) radius)
    (delta : Fin d → ℤ) (indices : List (Fin d)) :
    (inspect radius z delta indices).visits = indices.length + 1 := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp [inspect, ih, Nat.add_assoc]

/-- Input, output, and range-bound integers of each inspected predicate have
small magnitudes; arbitrary weight sizes do not enter these coordinates. -/
theorem inspected_operands {d : ℕ} (radius : ℕ) (z : Box (Fin d) radius)
    (delta : Fin d → ℤ) (hdelta : ∀ i, |delta i| ≤ 2) (i : Fin d) :
    |coordinate z i| ≤ 2 * (radius : ℤ) ∧ |delta i| ≤ 2 ∧
      |coordinate z i + delta i| ≤ 2 * (radius : ℤ) + 2 := by
  refine ⟨coordinate_bound z i, hdelta i, ?_⟩
  exact le_trans (abs_add_le _ _) (add_le_add (coordinate_bound z i) (hdelta i))

/-- Signed magnitudes in coordinate addition/comparison fit in logarithmically
many bits in the radius. A separate bit stores the sign. -/
theorem inspected_operand_bits {d : ℕ} (radius : ℕ) (z : Box (Fin d) radius)
    (delta : Fin d → ℤ) (hdelta : ∀ i, |delta i| ≤ 2) (i : Fin d) :
    (coordinate z i + delta i).natAbs.size ≤ (2 * radius + 2).size := by
  have h := (inspected_operands radius z delta hdelta i).2.2
  apply Nat.size_le_size
  have hn : ((coordinate z i + delta i).natAbs : ℤ) ≤ ((2 * radius + 2 : ℕ) : ℤ) := by
    simpa using h
  exact_mod_cast hn

/-- A source test followed, when necessary, by an actual coordinate scan. -/
def measuredMove {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (anchor current : State (Fin r)) (z : Box (Fin d) radius) (p : ZMod 2) (a : Arc C) :
    Measured (Option (Option (Fin m) × Node (Fin r) (Fin d) radius)) :=
  if source C a = current then
    let checked := inspect radius z (W a.val.1) (List.finRange d)
    let result := if checked.value then
      some (some a.val.1, Node.work anchor (target C a)
        (encode radius (fun i => coordinate z i + W a.val.1 i)) (p + π a.val.1)) else none
    ⟨result, checked.visits + 1⟩
  else ⟨none, 1⟩

theorem measuredMove_value {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (anchor current : State (Fin r)) (z : Box (Fin d) radius) (p : ZMod 2) (a : Arc C) :
    (measuredMove C W π radius anchor current z p a).value =
      moveCandidate C W π radius anchor current z p a := by
  have hc : (inspect radius z (W a.val.1) (List.finRange d)).value = true ↔
      ∀ i, |coordinate z i + W a.val.1 i| ≤ 2 * (radius : ℤ) := by
    simpa using inspect_value radius z (W a.val.1) (List.finRange d)
  by_cases hs : source C a = current
  · by_cases hcheck : ∀ i, |coordinate z i + W a.val.1 i| ≤ 2 * (radius : ℤ)
    · simp [measuredMove, moveCandidate, updateBox, hs, hcheck, hc.mpr hcheck]
    · have hn : (inspect radius z (W a.val.1) (List.finRange d)).value = false := by
        cases hv : (inspect radius z (W a.val.1) (List.finRange d)).value
        · rfl
        · exact False.elim (hcheck (hc.mp hv))
      simp [measuredMove, moveCandidate, updateBox, hs, hcheck, hn]
  · simp [measuredMove, moveCandidate, hs]

theorem measuredMove_visits_le {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (anchor current : State (Fin r)) (z : Box (Fin d) radius) (p : ZMod 2) (a : Arc C) :
    (measuredMove C W π radius anchor current z p a).visits ≤ d + 2 := by
  unfold measuredMove
  split
  · simp [inspect_visits]
  · simp

/-- Instrument the recursive candidate scan, including each list branch. -/
def scan {α β : Type*} (f : α → Measured (Option β)) : List α → Measured (List β)
  | [] => ⟨[], 1⟩
  | a :: as =>
      let head := f a
      let tail := scan f as
      ⟨match head.value with | none => tail.value | some b => b :: tail.value,
        head.visits + tail.visits + 1⟩

theorem scan_value {α β : Type*} (f : α → Measured (Option β)) (as : List α) :
    (scan f as).value = as.filterMap (fun a => (f a).value) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [scan, List.filterMap_cons]
      cases h : (f a).value <;> simp [ih]

theorem scan_visits_le {α β : Type*} (f : α → Measured (Option β))
    (as : List α) (k : ℕ) (hf : ∀ a ∈ as, (f a).visits ≤ k) :
    (scan f as).visits ≤ (k + 1) * as.length + 1 := by
  induction as with
  | nil => simp [scan]
  | cons a as ih =>
      have ha := hf a List.mem_cons_self
      have ht := ih (fun b hb => hf b (List.mem_cons_of_mem a hb))
      simp only [scan, List.length_cons]
      nlinarith

/-- Instrument an anchor traversal. -/
def mapMeasured {α β : Type*} (f : α → β) : List α → Measured (List β)
  | [] => ⟨[], 1⟩
  | a :: as =>
      let tail := mapMeasured f as
      ⟨f a :: tail.value, tail.visits + 1⟩

@[simp] theorem mapMeasured_value {α β : Type*} (f : α → β) (as : List α) :
    (mapMeasured f as).value = as.map f := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [mapMeasured, ih]

@[simp] theorem mapMeasured_visits {α β : Type*} (f : α → β) (as : List α) :
    (mapMeasured f as).visits = as.length + 1 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [mapMeasured, ih, Nat.add_assoc]

/-- The measured local loop consumes explicit precomputed small tables. -/
def outgoingMeasured {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (anchors : List (State (Fin r))) (arcs : List (Arc C)) :
    Node (Fin r) (Fin d) radius → Measured (List (Option (Fin m) × Node (Fin r) (Fin d) radius))
  | .hub z p => mapMeasured (fun a => (none, .work a a z p)) anchors
  | .work anchor current z p =>
      let moved := scan (measuredMove C W π radius anchor current z p) arcs
      ⟨(if current = anchor then [(none, .hub z p)] else []) ++ moved.value, moved.visits + 1⟩

/-- Output refinement to the executable uninstrumented generator. -/
theorem outgoingMeasured_value {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (v : Node (Fin r) (Fin d) radius) :
    (outgoingMeasured C W π radius (signedStates r) (signedArcs C) v).value =
      outgoing C W π radius v := by
  cases v with
  | hub z p => simp [outgoingMeasured, outgoing]
  | work anchor current z p =>
      simp only [outgoingMeasured, outgoing, scan_value]
      congr 1
      apply List.filterMap_congr
      intro a ha
      exact measuredMove_value C W π radius anchor current z p a

/-- At most (d+3) visits per signed-arc candidate, plus constant loop overhead.
This is a bound on executed scans, not a claim that vertex cardinality is time. -/
theorem outgoingMeasured_visits_le {r m d : ℕ} (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ)
    (v : Node (Fin r) (Fin d) radius) :
    (outgoingMeasured C W π radius (signedStates r) (signedArcs C) v).visits ≤
      (2 * r + 1) + (d + 3) * (2 * m) + 2 := by
  cases v with
  | hub z p => simp [outgoingMeasured, signedStates_length]; omega
  | work anchor current z p =>
      have hs := scan_visits_le (measuredMove C W π radius anchor current z p)
        (signedArcs C) (d + 2) (fun a _ => measuredMove_visits_le C W π radius anchor current z p a)
      have hs' : (scan (measuredMove C W π radius anchor current z p)
          (signedArcs C)).visits ≤ (d + 3) * (signedArcs C).length + 1 := by
        simpa [Nat.add_assoc] using hs
      have ha := signedArcs_length_le C
      have hm := Nat.mul_le_mul_left (d + 3) ha
      dsimp [outgoingMeasured]
      omega

end WeightedMIS.GenerationCost
