module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

/-!
# Integral transportation from weighted Hall inequalities

Replace each vertex of natural weight `w v` by `w v` distinct copies and apply
the finite marriage theorem. Counting the matched copies produces a natural
transportation matrix with the prescribed row and column sums. This is an
existence proof; the copy construction makes no polynomial bit-cost claim.
-/

@[expose] public section

namespace WeightedMIS.WeightedHall

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The neighbors reached from a finite set on the left of a relation. -/
def neighbors (adj : V → V → Prop) [DecidableRel adj] (S : Finset V) : Finset V :=
  univ.filter fun v => ∃ u ∈ S, adj u v

omit [DecidableEq V] in
@[simp] theorem mem_neighbors (adj : V → V → Prop) [DecidableRel adj]
    (S : Finset V) (v : V) : v ∈ neighbors adj S ↔ ∃ u ∈ S, adj u v := by
  simp [neighbors]

/-- Distinct copies of each vertex according to its integral demand. -/
abbrev Copies (w : V → ℕ) := Σ v, Fin (w v)

/-- All copies of the vertices in a set. -/
def copies (w : V → ℕ) (S : Finset V) : Finset (Copies w) :=
  S.sigma fun v => (univ : Finset (Fin (w v)))

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_copies (w : V → ℕ) (S : Finset V) (x : Copies w) :
    x ∈ copies w S ↔ x.1 ∈ S := by
  simp [copies]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem card_copies (w : V → ℕ) (S : Finset V) :
    (copies w S).card = ∑ v ∈ S, w v := by
  simp [copies, Finset.card_sigma]

/-- Weighted Hall inequalities give a permutation of the copies supported on
the relation. Both sides have exactly the same prescribed demands. -/
theorem exists_copy_bijection (adj : V → V → Prop) [DecidableRel adj]
    (w : V → ℕ)
    (hHall : ∀ S : Finset V, (∑ u ∈ S, w u) ≤ ∑ v ∈ neighbors adj S, w v) :
    ∃ f : Copies w → Copies w, Function.Bijective f ∧ ∀ x, adj x.1 (f x).1 := by
  classical
  let t : Copies w → Finset (Copies w) :=
    fun x => copies w (neighbors adj {x.1})
  have hcard (s : Finset (Copies w)) : s.card ≤ (s.biUnion t).card := by
    have hs : s ⊆ copies w (s.image Sigma.fst) := by
      intro x hx
      simp only [mem_copies]
      exact mem_image_of_mem _ hx
    have hunion : s.biUnion t = copies w (neighbors adj (s.image Sigma.fst)) := by
      ext x
      simp only [mem_biUnion, t, mem_copies, mem_neighbors, mem_singleton, mem_image]
      aesop
    calc
      s.card ≤ (copies w (s.image Sigma.fst)).card := card_le_card hs
      _ = ∑ u ∈ s.image Sigma.fst, w u := card_copies _ _
      _ ≤ ∑ v ∈ neighbors adj (s.image Sigma.fst), w v := hHall _
      _ = (s.biUnion t).card := by rw [hunion, card_copies]
  obtain ⟨f, hf, hs⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp hcard
  refine ⟨f, ⟨hf, Finite.surjective_of_injective hf⟩, ?_⟩
  intro x
  have h := hs x
  simpa [t] using h

/-- A nonnegative integral matrix supported on the relation, with the given
row and column sums. No optimizer or transportation witness is assumed. -/
theorem exists_transport (adj : V → V → Prop) [DecidableRel adj]
    (w : V → ℕ)
    (hHall : ∀ S : Finset V, (∑ u ∈ S, w u) ≤ ∑ v ∈ neighbors adj S, w v) :
    ∃ flow : V → V → ℕ,
      (∀ u v, ¬ adj u v → flow u v = 0) ∧
      (∀ u, ∑ v, flow u v = w u) ∧ (∀ v, ∑ u, flow u v = w v) := by
  classical
  obtain ⟨f, hf, hs⟩ := exists_copy_bijection adj w hHall
  let flow : V → V → ℕ :=
    fun u v => ∑ i : Fin (w u), if (f ⟨u, i⟩).1 = v then 1 else 0
  refine ⟨flow, ?_, ?_, ?_⟩
  · intro u v huv
    apply sum_eq_zero
    intro i _
    have hne : (f ⟨u, i⟩).1 ≠ v := by
      intro h
      apply huv
      simpa only [h] using hs ⟨u, i⟩
    simp [hne]
  · intro u
    dsimp [flow]
    rw [sum_comm]
    simp
  · intro v
    change (∑ u, ∑ i : Fin (w u), if (f ⟨u, i⟩).1 = v then 1 else 0) = w v
    rw [← Fintype.sum_sigma (fun x : Copies w => if (f x).1 = v then (1 : ℕ) else 0)]
    rw [hf.sum_comp (fun x : Copies w => if x.1 = v then (1 : ℕ) else 0)]
    rw [Fintype.sum_sigma]
    simp [apply_ite]

end WeightedMIS.WeightedHall
