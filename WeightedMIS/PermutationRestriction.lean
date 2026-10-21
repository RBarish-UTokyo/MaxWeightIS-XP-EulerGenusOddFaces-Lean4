module

public import WeightedMIS.PermutationDeletion

/-!
# Compatibility of actual first-return restrictions

Relabelling a permutation preserves its first retained successor. A smaller
retained predicate has the same successor whenever that first successor
already lies in the smaller set. These trace identities apply to geometric
edge deletion and to selecting a connected component after deletion.
-/

@[expose] public section

namespace WeightedMIS.PermutationDeletion

variable {α β : Type*} [Fintype α] [Fintype β]

/-- First-return times commute with an actual permutation conjugacy. -/
theorem returnTime_map (σ : Equiv.Perm α) (ρ : Equiv.Perm β) (e : α ≃ β)
    (hσ : Function.Semiconj e σ ρ) (p : α → Prop) (q : β → Prop)
    (hp : ∀ a, p a ↔ q (e a)) (x : {a // p a}) :
    returnTime ρ q (e.subtypeEquiv hp x) = returnTime σ p x := by
  apply returnTime_eq_of_trace
  · exact returnTime_pos σ p x
  · change q ((ρ : β → β)^[returnTime σ p x] (e x.val))
    rw [← hσ.iterate_right]
    exact (hp _).mp (returnTime_mem σ p x)
  · intro j hj hjn hh
    apply before_return_deleted σ p x hj hjn
    apply (hp _).mpr
    change q ((ρ : β → β)^[j] (e x.val)) at hh
    rwa [hσ.iterate_right]

/-- The actual retained successor commutes with edge-label transport. -/
theorem firstReturn_map (σ : Equiv.Perm α) (ρ : Equiv.Perm β) (e : α ≃ β)
    (hσ : Function.Semiconj e σ ρ) (p : α → Prop) (q : β → Prop)
    (hp : ∀ a, p a ↔ q (e a)) (x : {a // p a}) :
    e ((firstReturn σ p x).val) =
      (firstReturn ρ q (e.subtypeEquiv hp x)).val := by
  rw [firstReturn_apply, firstReturn_apply, returnTime_map σ ρ e hσ p q hp]
  exact hσ.iterate_right _ _

/-- A smaller retention set has the same first successor when the first
successor in the larger set already belongs to the smaller set. -/
theorem firstReturn_subpredicate (σ : Equiv.Perm α) (p q : α → Prop)
    (hsub : ∀ a, q a → p a) (x : {a // q a})
    (hnext : q (firstReturn σ p ⟨x.val, hsub x.val x.property⟩).val) :
    (firstReturn σ q x).val =
      (firstReturn σ p ⟨x.val, hsub x.val x.property⟩).val := by
  let y : {a // p a} := ⟨x.val, hsub x.val x.property⟩
  have ht : returnTime σ q x = returnTime σ p y := by
    apply returnTime_eq_of_trace
    · exact returnTime_pos σ p y
    · exact hnext
    · intro j hj hjn hq
      exact before_return_deleted σ p y hj hjn (hsub _ hq)
  rw [firstReturn_apply, ht, firstReturn_apply]

/-- Number of original permutation steps in a succession of retained steps. -/
noncomputable def travelTime (σ : Equiv.Perm α) (p : α → Prop) : ℕ → {a // p a} → ℕ
  | 0, _ => 0
  | k + 1, x => travelTime σ p k x +
      returnTime σ p ((firstReturn σ p : {a // p a} → {a // p a})^[k] x)

theorem travelTime_strictMono (σ : Equiv.Perm α) (p : α → Prop) (x : {a // p a}) :
    StrictMono (fun k => travelTime σ p k x) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact Nat.lt_add_of_pos_right (returnTime_pos σ p _)

theorem travelTime_succ_front (σ : Equiv.Perm α) (p : α → Prop)
    (k : ℕ) (x : {a // p a}) :
    travelTime σ p (k + 1) x = returnTime σ p x + travelTime σ p k (firstReturn σ p x) := by
  induction k with
  | zero => simp only [travelTime, Function.iterate_zero, id_eq, Nat.zero_add, Nat.add_zero]
  | succ k ih =>
    rw [travelTime, ih, travelTime, Function.iterate_succ_apply]
    omega

theorem firstReturn_iterate_travelTime (σ : Equiv.Perm α) (p : α → Prop)
    (k : ℕ) (x : {a // p a}) :
    ((firstReturn σ p : {a // p a} → {a // p a})^[k] x).val =
      (σ : α → α)^[travelTime σ p k x] x.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', firstReturn_apply, ih, ← Function.iterate_add_apply,
      travelTime, Nat.add_comm]

/-- A retained endpoint at a specified original time has a retained-step
trace with exactly that total original travel time. -/
theorem exists_travelTime_eq (σ : Equiv.Perm α) (p : α → Prop)
    (n : ℕ) (x : {a // p a}) (h : p ((σ : α → α)^[n] x.val)) :
    ∃ k, travelTime σ p k x = n := by
  classical
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hn : n = 0
    · exact ⟨0, hn.symm⟩
    · have ht : returnTime σ p x ≤ n := Nat.find_min' (exists_return σ p x) ⟨by omega, h⟩
      have hpos := returnTime_pos σ p x
      have htrace : (σ : α → α)^[n - returnTime σ p x] (firstReturn σ p x).val =
          (σ : α → α)^[n] x.val := by
        rw [firstReturn_apply, ← Function.iterate_add_apply, Nat.sub_add_cancel ht]
      obtain ⟨k, hk⟩ := ih (n - returnTime σ p x) (by omega) (firstReturn σ p x) (htrace.symm ▸ h)
      refine ⟨k + 1, ?_⟩
      rw [travelTime_succ_front, hk]
      omega

/-- Deleting entries in two stages gives exactly the first return to the
smaller original set. This is equality of actual successors, not just cycles. -/
theorem firstReturn_nested (σ : Equiv.Perm α) (p q : α → Prop) [DecidablePred p]
    (hsub : ∀ a, q a → p a) (x : {a : {a // p a} // q a.val}) :
    (firstReturn (firstReturn σ p) (fun a => q a.val) x).val.val =
      (firstReturn σ q ⟨x.val.val, x.property⟩).val := by
  let y : {a // q a} := ⟨x.val.val, x.property⟩
  let n := returnTime σ q y
  have hn : 0 < n := returnTime_pos σ q y
  have hmem : p ((σ : α → α)^[n] x.val.val) := hsub _ (returnTime_mem σ q y)
  obtain ⟨k, hk⟩ := exists_travelTime_eq σ p n x.val hmem
  have hkpos : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    rw [hz] at hk
    change 0 = n at hk
    omega
  have ht : returnTime (firstReturn σ p) (fun a => q a.val) x = k := by
    apply returnTime_eq_of_trace
    · exact hkpos
    · change q (((firstReturn σ p : {a // p a} → {a // p a})^[k] x.val).val)
      rw [firstReturn_iterate_travelTime, hk]
      exact returnTime_mem σ q y
    · intro j hj hjk hq
      have hjpos : 0 < travelTime σ p j x.val := (travelTime_strictMono σ p x.val) hj
      have hjlt : travelTime σ p j x.val < n := hk ▸ (travelTime_strictMono σ p x.val) hjk
      apply before_return_deleted σ q y hjpos hjlt
      change q (((firstReturn σ p : {a // p a} → {a // p a})^[j] x.val).val) at hq
      rwa [firstReturn_iterate_travelTime] at hq
  rw [firstReturn_apply, ht, firstReturn_iterate_travelTime, hk]
  rfl

end WeightedMIS.PermutationDeletion
