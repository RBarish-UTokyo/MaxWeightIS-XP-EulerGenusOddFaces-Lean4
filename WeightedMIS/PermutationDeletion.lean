module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Lean.Elab.Tactic.Omega

/-!
# First return to retained points of a finite permutation

Deleting entries from a cyclic order means iterating until the next retained
entry. This file constructs that first-return permutation from a finite
permutation and a predicate. Its forward trace has positive length at most the
number of original points, and every intermediate point is deleted. These are
generic tracing results; constructing surface boundary walks from vertex links
requires a separate application.
-/

@[expose] public section

namespace WeightedMIS.PermutationDeletion

variable {α : Type*} [Fintype α]

theorem exists_return (σ : Equiv.Perm α) (p : α → Prop) (x : {a // p a}) :
    ∃ n : ℕ, 0 < n ∧ p ((σ : α → α)^[n] x.val) := by
  refine ⟨Function.minimalPeriod σ x.val,
    Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x.val), ?_⟩
  have h := Function.isPeriodicPt_minimalPeriod σ x.val
  change (σ : α → α)^[Function.minimalPeriod σ x.val] x.val = x.val at h
  rw [h]
  exact x.property

/-- The least positive number of steps needed to return to the retained set. -/
noncomputable def returnTime (σ : Equiv.Perm α) (p : α → Prop)
    (x : {a // p a}) : ℕ := by
  classical
  exact Nat.find (exists_return σ p x)

theorem returnTime_pos (σ : Equiv.Perm α) (p : α → Prop) (x : {a // p a}) :
    0 < returnTime σ p x := by
  classical
  exact (Nat.find_spec (exists_return σ p x)).1

theorem returnTime_mem (σ : Equiv.Perm α) (p : α → Prop) (x : {a // p a}) :
    p ((σ : α → α)^[returnTime σ p x] x.val) := by
  classical
  exact (Nat.find_spec (exists_return σ p x)).2

/-- No positive intermediate point survives the deletion. -/
theorem before_return_deleted (σ : Equiv.Perm α) (p : α → Prop)
    (x : {a // p a}) {n : ℕ} (hn : 0 < n) (hlt : n < returnTime σ p x) :
    ¬p ((σ : α → α)^[n] x.val) := by
  classical
  intro h
  exact Nat.find_min (exists_return σ p x) hlt ⟨hn, h⟩

/-- A single trace never needs more steps than the original finite carrier. -/
theorem returnTime_le_card (σ : Equiv.Perm α) (p : α → Prop)
    (x : {a // p a}) : returnTime σ p x ≤ Fintype.card α := by
  classical
  apply le_trans (b := Function.minimalPeriod σ x.val)
  · apply Nat.find_min' (exists_return σ p x)
    refine ⟨Function.minimalPeriod_pos_of_mem_periodicPts
      (σ.injective.mem_periodicPts x.val), ?_⟩
    have h := Function.isPeriodicPt_minimalPeriod σ x.val
    change (σ : α → α)^[Function.minimalPeriod σ x.val] x.val = x.val at h
    rw [h]
    exact x.property
  · exact Function.minimalPeriod_le_card

/-- The forward first-return map before packaging it as an equivalence. -/
noncomputable def returnMap (σ : Equiv.Perm α) (p : α → Prop)
    (x : {a // p a}) : {a // p a} :=
  ⟨(σ : α → α)^[returnTime σ p x] x.val, returnTime_mem σ p x⟩

private theorem returnMap_injective_of_le (σ : Equiv.Perm α) (p : α → Prop)
    (x y : {a // p a}) (hle : returnTime σ p x ≤ returnTime σ p y)
    (h : returnMap σ p x = returnMap σ p y) : x = y := by
  have heq : (σ : α → α)^[returnTime σ p x] x.val =
      (σ : α → α)^[returnTime σ p y] y.val := congrArg Subtype.val h
  have hx : (σ : α → α)^[returnTime σ p y - returnTime σ p x] y.val = x.val := by
    apply (σ.injective.iterate (returnTime σ p x))
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le hle]
    exact heq.symm
  by_cases ht : returnTime σ p x = returnTime σ p y
  · simp only [ht, Nat.sub_self, Function.iterate_zero, id_eq] at hx
    exact Subtype.ext hx.symm
  · have hp := returnTime_pos σ p x
    have hn : 0 < returnTime σ p y - returnTime σ p x := by omega
    have hlt : returnTime σ p y - returnTime σ p x < returnTime σ p y := by omega
    exact (before_return_deleted σ p y hn hlt (hx.symm ▸ x.property)).elim

theorem returnMap_injective (σ : Equiv.Perm α) (p : α → Prop) :
    Function.Injective (returnMap σ p) := by
  intro x y h
  rcases le_total (returnTime σ p x) (returnTime σ p y) with hle | hle
  · exact returnMap_injective_of_le σ p x y hle h
  · exact (returnMap_injective_of_le σ p y x hle h.symm).symm

/-- The inherited cyclic order on retained entries. -/
noncomputable def firstReturn (σ : Equiv.Perm α) (p : α → Prop) :
    Equiv.Perm {a // p a} :=
  Equiv.ofBijective (returnMap σ p)
    ⟨returnMap_injective σ p, Finite.surjective_of_injective (returnMap_injective σ p)⟩

@[simp] theorem firstReturn_apply (σ : Equiv.Perm α) (p : α → Prop)
    (x : {a // p a}) :
    (firstReturn σ p x).val = (σ : α → α)^[returnTime σ p x] x.val := rfl

/-- If the immediate successor survives, no splicing is needed. -/
theorem returnTime_eq_one (σ : Equiv.Perm α) (p : α → Prop)
    (x : {a // p a}) (h : p (σ x.val)) : returnTime σ p x = 1 := by
  classical
  have hle : returnTime σ p x ≤ 1 :=
    Nat.find_min' (exists_return σ p x) ⟨by decide, by simpa using h⟩
  have hpos := returnTime_pos σ p x
  omega

@[simp] theorem firstReturn_apply_of_mem (σ : Equiv.Perm α) (p : α → Prop)
    (x : {a // p a}) (h : p (σ x.val)) : (firstReturn σ p x).val = σ x.val := by
  rw [firstReturn_apply, returnTime_eq_one σ p x h]
  rfl

/-- Every retained point along the original orbit is reached by the inherited
cyclic order, without more return steps than original steps. -/
theorem retained_iterate_reachable (σ : Equiv.Perm α) (p : α → Prop)
    (n : ℕ) (x : {a // p a}) (h : p ((σ : α → α)^[n] x.val)) :
    ∃ k ≤ n, ((firstReturn σ p : {a // p a} → {a // p a})^[k] x).val =
      (σ : α → α)^[n] x.val := by
  classical
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      exact ⟨0, le_rfl, rfl⟩
    · have ht : returnTime σ p x ≤ n :=
        Nat.find_min' (exists_return σ p x) ⟨by omega, h⟩
      have hpos := returnTime_pos σ p x
      have hlt : n - returnTime σ p x < n := by omega
      have htrace : (σ : α → α)^[n - returnTime σ p x] (firstReturn σ p x).val =
          (σ : α → α)^[n] x.val := by
        rw [firstReturn_apply, ← Function.iterate_add_apply, Nat.sub_add_cancel ht]
      obtain ⟨k, hk, hr⟩ := ih (n - returnTime σ p x) hlt (firstReturn σ p x)
        (htrace.symm ▸ h)
      refine ⟨k + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply]
      exact hr.trans htrace

/-- Iterating the first-return map always follows the original orbit. -/
theorem firstReturn_iterate_exists (σ : Equiv.Perm α) (p : α → Prop)
    (n : ℕ) (x : {a // p a}) :
    ∃ m : ℕ, ((firstReturn σ p : {a // p a} → {a // p a})^[n] x).val =
      (σ : α → α)^[m] x.val := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨returnTime σ p ((firstReturn σ p : {a // p a} → {a // p a})^[n] x) + m, ?_⟩
    rw [Function.iterate_succ_apply', firstReturn_apply, hm, Function.iterate_add_apply]

/-- Deleting entries preserves exactly the cyclic components that meet the
retained set. In particular, it does not split a vertex's cyclic order. -/
theorem sameCycle_firstReturn_iff (σ : Equiv.Perm α) (p : α → Prop)
    (x y : {a // p a}) :
    (firstReturn σ p).SameCycle x y ↔ σ.SameCycle x.val y.val := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    obtain ⟨n, hn⟩ := firstReturn_iterate_exists σ p k x
    have hk' : ((firstReturn σ p : {a // p a} → {a // p a})^[k] x) = y := by
      simpa only [Equiv.Perm.coe_pow] using hk
    rw [hk'] at hn
    refine ⟨(n : ℤ), ?_⟩
    simpa only [zpow_natCast, Equiv.Perm.coe_pow] using hn.symm
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hn' : (σ : α → α)^[n] x.val = y.val := by
      simpa only [Equiv.Perm.coe_pow] using hn
    obtain ⟨k, _, hk⟩ := retained_iterate_reachable σ p n x (hn'.symm ▸ y.property)
    refine ⟨(k : ℤ), ?_⟩
    apply Subtype.ext
    simpa only [zpow_natCast, Equiv.Perm.coe_pow] using hk.trans hn'

/-- Characterization of a first return by a positive trace with no earlier
retained entry. -/
theorem returnTime_eq_of_trace (σ : Equiv.Perm α) (p : α → Prop)
    (x : {a // p a}) (n : ℕ) (hn : 0 < n)
    (hmem : p ((σ : α → α)^[n] x.val))
    (hbefore : ∀ j, 0 < j → j < n → ¬p ((σ : α → α)^[j] x.val)) :
    returnTime σ p x = n := by
  classical
  apply le_antisymm
  · exact Nat.find_min' (exists_return σ p x) ⟨hn, hmem⟩
  · by_contra h
    exact hbefore _ (returnTime_pos σ p x) (by omega) (returnTime_mem σ p x)

omit [Fintype α] in
/-- Reversing an initial part of a forward trace leaves its remaining prefix. -/
theorem reverse_trace (σ : Equiv.Perm α) (x : α) {m n : ℕ} (h : m ≤ n) :
    (σ.symm : α → α)^[m] ((σ : α → α)^[n] x) =
      (σ : α → α)^[n - m] x := by
  simp only [← Equiv.Perm.coe_pow]
  have heq : σ ^ n = σ ^ m * σ ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_of_le h]
  rw [heq, Equiv.Perm.mul_apply]
  change ((σ⁻¹) ^ m) ((σ ^ m) ((σ ^ (n - m)) x)) = _
  rw [inv_pow]
  exact (σ ^ m).symm_apply_apply _

/-- Reversing the first-return trace reaches its original starting point in
exactly the same number of steps. -/
theorem returnTime_symm_after_return (σ : Equiv.Perm α) (p : α → Prop)
    (x : {a // p a}) :
    returnTime σ.symm p (firstReturn σ p x) = returnTime σ p x := by
  apply returnTime_eq_of_trace
  · exact returnTime_pos σ p x
  · rw [firstReturn_apply, reverse_trace σ _ le_rfl]
    simpa using x.property
  · intro j hj hlt
    rw [firstReturn_apply, reverse_trace σ _ hlt.le]
    exact before_return_deleted σ p x (by omega) (by omega)

/-- The inverse inherited cyclic order is the inherited inverse order. -/
theorem firstReturn_symm_apply (σ : Equiv.Perm α) (p : α → Prop)
    (x : {a // p a}) :
    firstReturn σ.symm p (firstReturn σ p x) = x := by
  apply Subtype.ext
  rw [firstReturn_apply, returnTime_symm_after_return, firstReturn_apply,
    reverse_trace σ _ le_rfl]
  simp

theorem firstReturn_symm (σ : Equiv.Perm α) (p : α → Prop) :
    firstReturn σ.symm p = (firstReturn σ p).symm := by
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := (firstReturn σ p).surjective y
  rw [firstReturn_symm_apply, Equiv.symm_apply_apply]

/-- Relabelling a cyclic order and its retained set preserves the exact return
time. -/
theorem returnTime_conjugate (σ ρ τ : Equiv.Perm α) (p : α → Prop)
    (hconj : Function.Semiconj τ σ ρ) (hp : ∀ a, p (τ a) ↔ p a)
    (x : {a // p a}) :
    returnTime ρ p (τ.subtypePerm hp x) = returnTime σ p x := by
  apply returnTime_eq_of_trace
  · exact returnTime_pos σ p x
  · change p ((ρ : α → α)^[returnTime σ p x] (τ x.val))
    rw [← hconj.iterate_right]
    exact (hp _).mpr (returnTime_mem σ p x)
  · intro j hj hlt hmem
    apply before_return_deleted σ p x hj hlt
    apply (hp _).mp
    change p ((ρ : α → α)^[j] (τ x.val)) at hmem
    rwa [hconj.iterate_right]

/-- First return commutes with a relabelling of the original cyclic order. -/
theorem firstReturn_conjugate (σ ρ τ : Equiv.Perm α) (p : α → Prop)
    (hconj : Function.Semiconj τ σ ρ) (hp : ∀ a, p (τ a) ↔ p a)
    (x : {a // p a}) :
    τ.subtypePerm hp (firstReturn σ p x) =
      firstReturn ρ p (τ.subtypePerm hp x) := by
  apply Subtype.ext
  change τ ((firstReturn σ p x).val) = (firstReturn ρ p (τ.subtypePerm hp x)).val
  rw [firstReturn_apply, firstReturn_apply, returnTime_conjugate σ ρ τ p hconj hp]
  exact hconj.iterate_right _ _

/-- Restrict a reflection to the retained points. The predicate must retain
both partners of the reflection. -/
def retainedReflection (τ : Equiv.Perm α) (p : α → Prop)
    (hp : ∀ a, p (τ a) ↔ p a) : Equiv.Perm {a // p a} := τ.subtypePerm hp

/-- The spliced matching of corners, obtained by following the original
rotation until the next retained entry and then crossing to its partner. -/
noncomputable def splicedCorner (σ τ : Equiv.Perm α) (p : α → Prop)
    (hp : ∀ a, p (τ a) ↔ p a) : Equiv.Perm {a // p a} :=
  (firstReturn σ p).trans (retainedReflection τ p hp)

/-- Reversal symmetry makes the spliced corner map an involution. -/
theorem splicedCorner_involutive (σ τ : Equiv.Perm α) (p : α → Prop)
    (hp : ∀ a, p (τ a) ↔ p a) (hτ : Function.Involutive τ)
    (hrev : Function.Semiconj τ σ σ.symm) :
    Function.Involutive (splicedCorner σ τ p hp) := by
  intro x
  have hcomm := firstReturn_conjugate σ σ.symm τ p hrev hp
  rw [firstReturn_symm] at hcomm
  have hτ' (y : {a // p a}) : τ.subtypePerm hp (τ.subtypePerm hp y) = y := by
    apply Subtype.ext
    exact hτ y.val
  change τ.subtypePerm hp (firstReturn σ p (τ.subtypePerm hp (firstReturn σ p x))) = x
  rw [hcomm, hτ', Equiv.symm_apply_apply]

/-- For two fixed-point-free reflections, reflection exchanges the two
oriented cycles of their alternating rotation. -/
theorem reversing_no_sameCycle (σ τ : Equiv.Perm α)
    (hrev : Function.Semiconj τ σ σ.symm)
    (hreflect : ∀ a, τ a ≠ a) (hcorner : ∀ a, τ (σ a) ≠ a) (x : α) :
    ¬σ.SameCycle x (τ x) := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hn' : (σ : α → α)^[n] x = τ x := by
    simpa only [Equiv.Perm.coe_pow] using hn
  have htrace (j : ℕ) (hj : j ≤ n) :
      τ ((σ : α → α)^[j] x) = (σ : α → α)^[n - j] x := by
    rw [hrev.iterate_right j x, ← hn', reverse_trace σ x hj]
  by_cases heven : n % 2 = 0
  · have hj : n / 2 ≤ n := Nat.div_le_self _ _
    have heq : n - n / 2 = n / 2 := by omega
    have ht := htrace (n / 2) hj
    rw [heq] at ht
    exact hreflect _ ht
  · have hj : n / 2 + 1 ≤ n := by omega
    have heq : n - (n / 2 + 1) = n / 2 := by omega
    have ht := htrace (n / 2 + 1) hj
    rw [heq, Function.iterate_succ_apply'] at ht
    exact hcorner _ ht

/-- Splicing deleted entries leaves genuine pairs of distinct corners. -/
theorem splicedCorner_ne_self (σ τ : Equiv.Perm α) (p : α → Prop)
    (hp : ∀ a, p (τ a) ↔ p a) (hτ : Function.Involutive τ)
    (hrev : Function.Semiconj τ σ σ.symm)
    (hreflect : ∀ a, τ a ≠ a) (hcorner : ∀ a, τ (σ a) ≠ a)
    (x : {a // p a}) : splicedCorner σ τ p hp x ≠ x := by
  intro h
  have hh := congrArg (fun y : {a // p a} => τ y.val) h
  change τ (τ (firstReturn σ p x).val) = τ x.val at hh
  rw [hτ] at hh
  apply reversing_no_sameCycle σ τ hrev hreflect hcorner x.val
  rw [← hh]
  refine ⟨(returnTime σ p x : ℤ), ?_⟩
  rw [firstReturn_apply, zpow_natCast, Equiv.Perm.coe_pow]

end WeightedMIS.PermutationDeletion
