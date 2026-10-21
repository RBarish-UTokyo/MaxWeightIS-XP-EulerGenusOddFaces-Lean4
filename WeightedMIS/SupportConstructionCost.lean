module

public import WeightedMIS.DeterministicKernelWidth
public import WeightedMIS.StoredEliminationCost

/-!
# Operation counts for deterministic support construction

The counted routines follow the same first-successor and repeated-arc branches
as the executable construction. Costs include list traversals, coordinate
accesses, and scalar arithmetic or comparisons. Scalar bit implementations and
the previously proved operand widths refine this operation model separately.
-/

@[expose] public section

namespace WeightedMIS.SupportConstructionCost

open DeterministicKernel

section Lists

variable {A : Type*} [DecidableEq A]

/-- First successful predicate test, recording every visited list cell. -/
def find (p : A → Bool) : List A → Option A × ℕ
  | [] => (none, 1)
  | a :: as => if p a then (some a, 1) else
      let r := find p as
      (r.1, r.2 + 1)

omit [DecidableEq A] in
theorem find_spec (p : A → Bool) (xs : List A) :
    (find p xs).1 = xs.find? p ∧ (find p xs).2 ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [find]
  | cons a as ih =>
      cases h : p a <;> simp [find, h, List.find?, ih.1]
      omega

/-- Membership scan with an exact test count. -/
def member (a : A) : List A → Bool × ℕ
  | [] => (false, 1)
  | b :: bs => if a = b then (true, 1) else
      let r := member a bs
      (r.1, r.2 + 1)

theorem member_spec (a : A) (xs : List A) :
    (member a xs).1 = decide (a ∈ xs) ∧ (member a xs).2 ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [member]
  | cons b bs ih =>
      by_cases h : a = b <;> simp [member, h, ih.1]
      omega

/-- Drop the initial segment preceding the repeated arc. -/
def suffix (a : A) : List A → List A × ℕ
  | [] => ([], 1)
  | b :: bs => if b = a then (b :: bs, 1) else
      let r := suffix a bs
      (r.1, r.2 + 1)

theorem suffix_spec (a : A) (xs : List A) :
    (suffix a xs).1 = CycleSearch.cycleSuffix a xs ∧ (suffix a xs).2 ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [suffix, CycleSearch.cycleSuffix]
  | cons b bs ih =>
      by_cases h : b = a <;> simp [suffix, h, CycleSearch.cycleSuffix] at *
      exact ih

/-- Repeated-arc search with the actual successor work supplied at each step. -/
def search (next : A → A) (nextWork : A → ℕ) : ℕ → A → List A → List A × ℕ
  | 0, _, _ => ([], 1)
  | fuel + 1, a, seen =>
      let h := member a seen
      if h.1 then
        let r := suffix a seen
        (r.1, h.2 + r.2 + 1)
      else
        let r := search next nextWork fuel (next a) (seen ++ [a])
        (r.1, h.2 + nextWork a + seen.length + 2 + r.2)

theorem search_value (next : A → A) (nextWork : A → ℕ)
    (fuel : ℕ) (a : A) (seen : List A) :
    (search next nextWork fuel a seen).1 = CycleSearch.search next fuel a seen := by
  induction fuel generalizing a seen with
  | zero => rfl
  | succ fuel ih =>
      simp only [search, (member_spec a seen).1]
      by_cases h : a ∈ seen <;>
        simp [h, CycleSearch.search, (suffix_spec a seen).1, ih]

theorem search_work_le (next : A → A) (nextWork : A → ℕ) (N : ℕ)
    (hnext : ∀ a, nextWork a ≤ N) (fuel : ℕ) (a : A) (seen : List A) :
    (search next nextWork fuel a seen).2 ≤
      fuel * (3 * (seen.length + fuel + 1) + N + 5) + 1 := by
  induction fuel generalizing a seen with
  | zero => simp [search]
  | succ fuel ih =>
      have hm := (member_spec a seen).2
      have hs := (suffix_spec a seen).2
      have hn := hnext a
      have hi := ih (next a) (seen ++ [a])
      simp only [List.length_append, List.length_singleton] at hi
      simp only [search]
      split <;> nlinarith

end Lists

section Cycles

variable {V A : Type*} [DecidableEq V] [DecidableEq A]

/-- A successor scan, with seven scalar accesses/tests per visited arc. -/
def successor (source target : A → V) (active : A → Bool) (enum : List A) (a : A) : A × ℕ :=
  let r := find (fun b => active b && decide (source b = target a)) enum
  (r.1.getD a, 7 * r.2 + 1)

omit [DecidableEq A] in
theorem successor_value (source target : A → V) (active : A → Bool) (enum : List A) (a : A) :
    (successor source target active enum a).1 = CycleSearch.successor source target active enum a := by
  simp only [successor, (find_spec _ enum).1, CycleSearch.successor]

omit [DecidableEq A] in
theorem successor_work_le (source target : A → V) (active : A → Bool) (enum : List A) (a : A) :
    (successor source target active enum a).2 ≤ 7 * (enum.length + 1) + 1 := by
  have h := (find_spec (fun b => active b && decide (source b = target a)) enum).2
  simp only [successor]
  omega

/-- Counted finite-cycle search refines the actual supported-cycle finder. -/
def findCycle (source target : A → V) (active : A → Bool) (enum : List A) (a : A) : List A × ℕ :=
  let r := search (CycleSearch.successor source target active enum)
    (fun b => (successor source target active enum b).2) (enum.length + 1) a []
  (r.1, r.2 + 2)

theorem findCycle_value (source target : A → V) (active : A → Bool) (enum : List A) (a : A) :
    (findCycle source target active enum a).1 = CycleSearch.findCycle source target active enum a :=
  search_value _ _ _ _ _

theorem findCycle_work_le (source target : A → V) (active : A → Bool) (enum : List A) (a : A) :
    (findCycle source target active enum a).2 ≤
      (enum.length + 1) * (10 * enum.length + 19) + 3 := by
  have h := search_work_le (CycleSearch.successor source target active enum)
    (fun b => (successor source target active enum b).2) (7 * (enum.length + 1) + 1)
    (successor_work_le source target active enum) (enum.length + 1) a []
  simp only [List.length_nil] at h
  simp only [findCycle]
  nlinarith

end Cycles

section Incidence

variable {n m : ℕ}

theorem cycleSearch_length_le {A : Type*} [DecidableEq A]
    (next : A → A) (fuel : ℕ) (a : A) (seen : List A) :
    (CycleSearch.search next fuel a seen).length ≤ seen.length + fuel := by
  induction fuel generalizing a seen with
  | zero => simp [CycleSearch.search]
  | succ fuel ih =>
      simp only [CycleSearch.search]
      split
      · exact (CycleSearch.cycleSuffix_sublist a seen).length_le.trans (by omega)
      · have h := ih (next a) (seen ++ [a])
        simp only [List.length_append, List.length_singleton] at h
        omega

/-- Count the concrete support-cycle call, including the initial active-arc
scan and construction of the two-orientation enumeration. -/
def cycle (left right : Fin m → Fin n) (x : Fin m → ℚ) : List (OrientedEdge m) × ℕ :=
  let first := find (active x) (arcList m)
  match first.1 with
  | none => ([], 4 * first.2 + 3 * m + 1)
  | some a =>
      let r := findCycle (arcSource left right x) (arcTarget left right x) (active x) (arcList m) a
      (r.1, 4 * first.2 + 3 * m + 1 + r.2)

theorem cycle_value (left right : Fin m → Fin n) (x : Fin m → ℚ) :
    (cycle left right x).1 = DeterministicKernel.cycle left right x := by
  simp only [cycle]
  rw [(find_spec _ _).1]
  unfold DeterministicKernel.cycle
  split
  · next he => simp only [he]
  · next a he =>
      simpa only [he] using (findCycle_value
        (arcSource left right x) (arcTarget left right x) (active x) (arcList m) a)

/-- Uniform number of support-cycle operations, valid even on non-kernel inputs. -/
def cycleBudget (m : ℕ) : ℕ := (2 * m + 1) * (20 * m + 19) + 11 * m + 8

theorem cycle_work_le (left right : Fin m → Fin n) (x : Fin m → ℚ) :
    (cycle left right x).2 ≤ cycleBudget m := by
  have hf := (find_spec (active x) (arcList m)).2
  rw [arcList_length] at hf
  simp only [cycle]
  split
  · unfold cycleBudget
    nlinarith
  · next a _ =>
      have h := findCycle_work_le (arcSource left right x) (arcTarget left right x)
        (active x) (arcList m) a
      rw [arcList_length] at h
      unfold cycleBudget
      nlinarith

theorem cycle_length_le (left right : Fin m → Fin n) (x : Fin m → ℚ) :
    (cycle left right x).1.length ≤ 2 * m + 1 := by
  rw [cycle_value]
  unfold DeterministicKernel.cycle
  split
  · simp
  · next a _ =>
      have h := cycleSearch_length_le
        (CycleSearch.successor (arcSource left right x) (arcTarget left right x)
          (active x) (arcList m)) ((arcList m).length + 1) a []
      simpa only [CycleSearch.findCycle, List.length_nil, zero_add, arcList_length] using h

/-- Count a label's multiplicity by a linear list scan. -/
def count {A : Type*} [DecidableEq A] (a : A) : List A → ℕ × ℕ
  | [] => (0, 1)
  | b :: bs =>
      let r := count a bs
      (if b = a then r.1 + 1 else r.1, r.2 + 2)

theorem count_spec {A : Type*} [DecidableEq A] (a : A) (xs : List A) :
    (count a xs).1 = xs.count a ∧ (count a xs).2 = 2 * xs.length + 1 := by
  induction xs with
  | nil => simp [count]
  | cons b bs ih =>
      by_cases h : b = a <;> simp [count, h, ih.1, ih.2,
        Nat.mul_add, Nat.add_assoc]

/-- One generator coordinate, including a fresh cycle computation as in the
current materializing implementation. -/
def generatorCoordinate (left right : Fin m → Fin n) (x : Fin m → ℚ) (e : Fin m) : ℤ × ℕ :=
  let c := cycle left right x
  let r := count e (c.1.map Prod.fst)
  (Walks.signValue (SparseKernel.rationalSign x e) * (r.1 : ℤ),
    c.2 + c.1.length + r.2 + 5)

theorem generatorCoordinate_value (left right : Fin m → Fin n) (x : Fin m → ℚ) (e : Fin m) :
    (generatorCoordinate left right x e).1 = generator left right x e := by
  simp only [generatorCoordinate, (count_spec _ _).1, cycle_value, generator]

theorem generatorCoordinate_work_le (left right : Fin m → Fin n) (x : Fin m → ℚ) (e : Fin m) :
    (generatorCoordinate left right x e).2 ≤ cycleBudget m + 6 * m + 9 := by
  have hc := cycle_work_le left right x
  have hl := cycle_length_le left right x
  simp only [generatorCoordinate, (count_spec _ _).2, List.length_map]
  omega

/-- Work needed to materialize every generator coordinate. -/
def generatorWork (left right : Fin m → Fin n) (x : Fin m → ℚ) : ℕ :=
  (List.ofFn (fun e => (generatorCoordinate left right x e).2 + 1)).sum + 1

theorem generatorWork_le (left right : Fin m → Fin n) (x : Fin m → ℚ) :
    generatorWork left right x ≤ m * (cycleBudget m + 6 * m + 10) + 1 := by
  unfold generatorWork
  apply Nat.add_le_add_right
  rw [List.sum_ofFn]
  calc
    _ ≤ ∑ _e : Fin m, (cycleBudget m + 6 * m + 10) := by
      apply Finset.sum_le_sum
      intro e _
      have h := generatorCoordinate_work_le left right x e
      omega
    _ = _ := by simp

/-- Counted search for the first nonzero generator coordinate. -/
def pivotWork (g : Fin m → ℤ) : ℕ :=
  2 * (find (fun i => decide (g i ≠ 0)) (List.ofFn (fun i : Fin m => i))).2 + 1

theorem pivotWork_le (g : Fin m → ℤ) : pivotWork g ≤ 2 * m + 3 := by
  have h := (find_spec (fun i => decide (g i ≠ 0)) (List.ofFn (fun i : Fin m => i))).2
  simp only [List.length_ofFn] at h
  simp only [pivotWork]
  omega

/-- Count the existing support-decomposition branches. A residual coordinate
uses four reads, division, multiplication, subtraction and one write. -/
def decomposeWork (left right : Fin m → Fin n) : ℕ → (Fin m → ℚ) → ℕ
  | 0, _ => 1
  | fuel + 1, x =>
      let g := materializeInt (generator left right x)
      generatorWork left right x + pivotWork g +
        match pivot g with
        | none => 1
        | some e => 8 * m + 8 + decomposeWork left right fuel
            (materializeRat (KernelArithmetic.eliminate x (g, e)))

/-- Uniform scalar-operation budget for one support-elimination round. -/
def roundBudget (m : ℕ) : ℕ := m * (cycleBudget m + 6 * m + 10) + 10 * m + 12

theorem decomposeWork_le (left right : Fin m → Fin n) (fuel : ℕ) (x : Fin m → ℚ) :
    decomposeWork left right fuel x ≤ fuel * roundBudget m + 1 := by
  induction fuel generalizing x with
  | zero => simp [decomposeWork]
  | succ fuel ih =>
      have hg := generatorWork_le left right x
      have hp := pivotWork_le (materializeInt (generator left right x))
      simp only [decomposeWork]
      split
      · unfold roundBudget
        nlinarith
      · next e _ =>
          have hi := ih (materializeRat (KernelArithmetic.eliminate x
            (materializeInt (generator left right x), e)))
          unfold roundBudget at hi ⊢
          nlinarith

theorem decompose_length_le (left right : Fin m → Fin n) (fuel : ℕ) (x : Fin m → ℚ) :
    (decompose left right fuel x).length ≤ fuel := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
      simp only [decompose]
      split
      · simp
      · simpa only [List.length_cons, Nat.succ_le_succ_iff] using ih _

/-- Initial incidence elimination followed by every actual support
decomposition and its output-list traversal. -/
def candidatesWork (left right : Fin m → Fin n) : ℕ :=
  StoredEliminationCost.kernelWork (incidenceArray left right) +
    ((initial left right).map (fun x => decomposeWork left right m x +
      (decompose left right m x).length + 1)).sum + 2 * n * m + 1

/-- Explicit polynomial operation count for the whole bounded candidate
construction, including its initial rational nullspace computation. -/
def candidatesBudget (n m : ℕ) : ℕ :=
  m * (m + 1) + n * m * StoredEliminationCost.cutFactor m +
    m * (m * roundBudget m + m + 2) + 2 * n * m + 1

theorem candidatesWork_le (left right : Fin m → Fin n) :
    candidatesWork left right ≤ candidatesBudget n m := by
  have hk := StoredEliminationCost.kernelWork_le (incidenceArray left right)
  have hilen : (initial left right).length = m := by
    rw [initial_eq]
    exact ComputedKernel.rationalGenerators_length left right
  have hs : ((initial left right).map (fun x => decomposeWork left right m x +
      (decompose left right m x).length + 1)).sum ≤ m * (m * roundBudget m + m + 2) := by
    calc
      _ ≤ ((initial left right).map (fun _ => m * roundBudget m + m + 2)).sum := by
        apply List.sum_le_sum
        intro x hx
        have hd := decomposeWork_le left right m x
        have hl := decompose_length_le left right m x
        omega
      _ = _ := by simp [hilen]
  unfold candidatesWork candidatesBudget
  omega

/-- Actual complement selection after candidate construction. -/
def complementWork (left right : Fin m → Fin n) (rows : List (Fin m → ℚ)) : ℕ :=
  candidatesWork left right + StoredEliminationCost.selectWork rows
    ((candidates left right).map ComputedKernel.rationalRow)

theorem complementWork_le (left right : Fin m → Fin n) (rows : List (Fin m → ℚ)) :
    complementWork left right rows ≤ candidatesBudget n m +
      (m * m) * (StoredEliminationCost.outsideBound m (rows.length + m * m) + 1) := by
  have hc := candidatesWork_le left right
  have hlen := (candidates_spec left right).1
  have hs := StoredEliminationCost.selectWork_le rows
    ((candidates left right).map ComputedKernel.rationalRow)
  simp only [List.length_map] at hs
  have hb := StoredEliminationCost.outsideBound_mono (m := m)
    (Nat.add_le_add_left hlen rows.length)
  have hm := Nat.mul_le_mul hlen (Nat.add_le_add_right hb 1)
  unfold complementWork
  omega

end Incidence

end WeightedMIS.SupportConstructionCost
