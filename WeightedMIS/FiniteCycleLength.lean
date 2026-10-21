module

public import WeightedMIS.FiniteCycleEnumeration

/-!
# Computing the first return along a finite permutation

A bounded actual trace is scanned for its first return. The resulting natural
number is executable and equals the mathematical minimal period, so no
classical selection is needed to obtain facial boundary lengths.
-/

@[expose] public section

namespace WeightedMIS.FiniteCycleEnumeration

variable {α : Type*}

/-- The indexed position of a bounded trace is the corresponding actual
function iterate. -/
theorem trace_getElem (f : α → α) (n : ℕ) (x : α) (i : ℕ) (hi : i < n) :
    (trace f n x)[i]'(by simpa using hi) = f^[i] x := by
  induction n generalizing x i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp only [trace, List.getElem_cons_succ, Function.iterate_succ_apply]
          exact ih (f x) i (by omega)

/-- Scan at most the carrier cardinality actual successors for the first
return to the starting flag. -/
def periodLength [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (x : α) : ℕ :=
  (trace σ (Fintype.card α) (σ x)).findIdx (fun y => decide (y = x)) + 1

/-- The executable first-return length is the genuine minimal period. -/
theorem periodLength_eq [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (x : α) :
    periodLength σ x = Function.minimalPeriod σ x := by
  let p := Function.minimalPeriod σ x
  have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x)
  have hpn : p ≤ Fintype.card α := Function.minimalPeriod_le_card
  have hlt : p - 1 < (trace σ (Fintype.card α) (σ x)).length := by
    rw [trace_length]
    omega
  have hidx : (trace σ (Fintype.card α) (σ x)).findIdx (fun y => decide (y = x)) = p - 1 := by
    apply (List.findIdx_eq hlt).2
    constructor
    · rw [trace_getElem σ (Fintype.card α) (σ x) (p - 1) (by omega)]
      simp only [decide_eq_true_eq]
      rw [← Function.iterate_succ_apply]
      have he : (p - 1).succ = p := by omega
      rw [he]
      exact Function.iterate_minimalPeriod
    · intro j hj
      rw [trace_getElem σ (Fintype.card α) (σ x) j (by omega)]
      simp only [decide_eq_false_iff_not]
      intro he
      have hperiod : Function.IsPeriodicPt σ (j + 1) x := by
        simpa only [Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_succ_apply] using he
      have hmin := hperiod.minimalPeriod_le (by omega : 0 < j + 1)
      change p ≤ j + 1 at hmin
      omega
  rw [periodLength, hidx]
  omega

@[simp] theorem periodLength_pos [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (x : α) :
    0 < periodLength σ x := by simp [periodLength]

theorem periodLength_le_card [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (x : α) :
    periodLength σ x ≤ Fintype.card α := by
  rw [periodLength_eq]
  exact Function.minimalPeriod_le_card

/-- The finite, executable boundary list stops at exactly its first return. -/
def cycleList [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (x : α) : List α :=
  trace σ (periodLength σ x) x

@[simp] theorem cycleList_length [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (x : α) :
    (cycleList σ x).length = Function.minimalPeriod σ x := by
  rw [cycleList, trace_length, periodLength_eq]

/-- Each flag in one chosen orientation is visited once. -/
theorem cycleList_nodup [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (x : α) :
    (cycleList σ x).Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  apply Fin.ext
  have hi : i.val < Function.minimalPeriod σ x := by simpa only [cycleList_length] using i.isLt
  have hj : j.val < Function.minimalPeriod σ x := by simpa only [cycleList_length] using j.isLt
  have he : (σ : α → α)^[i.val] x = (σ : α → α)^[j.val] x := by
    change (trace σ (periodLength σ x) x)[i.val] =
      (trace σ (periodLength σ x) x)[j.val] at hij
    exact (trace_getElem σ (periodLength σ x) x i.val
      (by simpa only [periodLength_eq] using hi)).symm.trans
        (hij.trans (trace_getElem σ (periodLength σ x) x j.val
          (by simpa only [periodLength_eq] using hj)))
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).mp he

end WeightedMIS.FiniteCycleEnumeration
