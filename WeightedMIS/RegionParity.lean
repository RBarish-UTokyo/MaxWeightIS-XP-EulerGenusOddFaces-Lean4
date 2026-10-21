module

public import WeightedMIS.Parameters
public import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
Parity cancellation for regions after deleting edge bands. Every edge has two
actual sides. A side belongs to an original face, and either survives on a new
boundary circle or is deleted. The hypotheses say that both sides are deleted
together, that a deleted edge lies in one region, and that surviving sides have
the same region before and after deletion. The odd-boundary congruence follows
from these incidence data; no parity or genus inequality is assumed.

Constructing these data from a surface embedding, and establishing the Euler
characteristic gluing identity, are separate topological obligations.
-/

@[expose] public section

namespace WeightedMIS.RegionParity

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

/-- The number of elements in a finite fiber. -/
noncomputable def fiberSize {S F : Type*} [Fintype S] (f : S → F) (a : F) : ℕ :=
  by classical exact #{s : S | f s = a}

/-- Counting odd summands modulo two gives the parity of their sum. -/
theorem odd_count_mod {F : Type*} (s : Finset F) (n : F → ℕ) :
    (s.filter fun f => Odd (n f)).card % 2 = (∑ f ∈ s, n f) % 2 := by
  classical
  have h := Finset.even_sum_iff_even_card_odd (s := s) n
  rw [Nat.even_iff, Nat.even_iff] at h
  omega

/-- Regrouping side occurrences by their face does not change their count. -/
theorem grouped_fiber_sum {S F R : Type*} [Fintype S] [Fintype F]
    (face : S → F) (region : F → R) (r : R) :
    (∑ f ∈ (univ.filter fun f => region f = r), fiberSize face f) =
      ∑ s : S, if region (face s) = r then 1 else 0 := by
  classical
  simp only [fiberSize]
  have h := Finset.sum_card_fiberwise_eq_card_filter (univ : Finset S)
    (univ.filter fun f => region f = r) face
  simpa only [mem_filter, mem_univ, true_and, Finset.card_filter] using h

/-- A boundary map has value `none` precisely on deleted sides. -/
noncomputable def boundarySize {S B : Type*} [Fintype S]
    (boundary : S → Option B) (b : B) : ℕ := fiberSize boundary (some b)

/-- Regroup the retained occurrences by their new boundary circles. -/
theorem grouped_boundary_sum {S B R : Type*} [Fintype S] [Fintype B]
    (boundary : S → Option B) (region : B → R) (r : R) :
    (∑ b ∈ (univ.filter fun b => region b = r), boundarySize boundary b) =
      ∑ s : S, match boundary s with
        | none => 0
        | some b => if region b = r then 1 else 0 := by
  classical
  simp only [boundarySize, fiberSize, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  cases h : boundary s with
  | none => simp
  | some b =>
    simp only [Option.some.injEq]
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hne
      simp [Ne.symm hne]
    · simp

/-- The deleted-side count is twice the number of deleted edges in a region.
This is the exact incidence cancellation underlying Lemma 2, and is independent
of directions, orientation, or whether two sides meet the same original face. -/
theorem side_cancellation {E F B R : Type*} [Fintype E]
    (face : E × Bool → F) (originalRegion : F → R)
    (boundary : E × Bool → Option B) (boundaryRegion : B → R)
    (paired : ∀ e, boundary (e, false) = none ↔ boundary (e, true) = none)
    (deleted : ∀ e, boundary (e, false) = none →
      originalRegion (face (e, false)) = originalRegion (face (e, true)))
    (retained : ∀ s b, boundary s = some b →
      boundaryRegion b = originalRegion (face s)) (r : R) :
    (∑ s : E × Bool, if originalRegion (face s) = r then 1 else 0) =
      (∑ s : E × Bool, match boundary s with
        | none => 0
        | some b => if boundaryRegion b = r then 1 else 0) +
      2 * ∑ e, if boundary (e, false) = none ∧
        originalRegion (face (e, false)) = r then 1 else 0 := by
  classical
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Fintype.sum_bool]
  cases hf : boundary (e, false) with
  | none =>
    have ht := (paired e).mp hf
    have hr := deleted e hf
    simp [ht, hr]
    split <;> omega
  | some b =>
    have ht : boundary (e, true) ≠ none := by
      intro h
      have := (paired e).mpr h
      simp [hf] at this
    cases hg : boundary (e, true) with
    | none => exact (ht hg).elim
    | some c =>
      have hb := retained (e, false) b hf
      have hc := retained (e, true) c hg
      simp [hb, hc]

/-- Counts of original odd faces and new odd boundary circles agree modulo
two, region by region, with multiplicity of side occurrences preserved. -/
theorem odd_boundary_parity {E F B R : Type*}
    [Fintype E] [Fintype F] [Fintype B]
    (face : E × Bool → F) (originalRegion : F → R)
    (boundary : E × Bool → Option B) (boundaryRegion : B → R)
    (paired : ∀ e, boundary (e, false) = none ↔ boundary (e, true) = none)
    (deleted : ∀ e, boundary (e, false) = none →
      originalRegion (face (e, false)) = originalRegion (face (e, true)))
    (retained : ∀ s b, boundary s = some b →
      boundaryRegion b = originalRegion (face s)) (r : R) :
    #{b : B | boundaryRegion b = r ∧ Odd (boundarySize boundary b)} % 2 =
      #{f : F | originalRegion f = r ∧ Odd (fiberSize face f)} % 2 := by
  classical
  have ho := odd_count_mod (univ.filter fun f => originalRegion f = r)
    (fiberSize face)
  have hb := odd_count_mod (univ.filter fun b => boundaryRegion b = r)
    (boundarySize boundary)
  simp only [Finset.filter_filter] at ho hb
  rw [grouped_fiber_sum] at ho
  rw [grouped_boundary_sum] at hb
  have hc := side_cancellation face originalRegion boundary boundaryRegion
    paired deleted retained r
  omega

/-- The local odd-boundary inequality, derived from the side data. -/
theorem odd_boundary_bound {E F B R : Type*}
    [Fintype E] [Fintype F] [Fintype B]
    (face : E × Bool → F) (originalRegion : F → R)
    (boundary : E × Bool → Option B) (boundaryRegion : B → R)
    (paired : ∀ e, boundary (e, false) = none ↔ boundary (e, true) = none)
    (deleted : ∀ e, boundary (e, false) = none →
      originalRegion (face (e, false)) = originalRegion (face (e, true)))
    (retained : ∀ s b, boundary s = some b →
      boundaryRegion b = originalRegion (face s)) (r : R)
    (nonempty_boundary : 1 ≤ #{b : B | boundaryRegion b = r}) :
    #{b : B | boundaryRegion b = r ∧ Odd (boundarySize boundary b)} ≤
      #{f : F | originalRegion f = r ∧ Odd (fiberSize face f)} +
      2 * (#{b : B | boundaryRegion b = r} - 1) := by
  classical
  apply Parameters.boundary_bound _ _ _ nonempty_boundary
  · apply Finset.card_le_card
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    exact hb.1
  · exact odd_boundary_parity face originalRegion boundary boundaryRegion
      paired deleted retained r

/-- A partition into regions counts each selected face exactly once. -/
theorem sum_region_count {F R : Type*} [Fintype F] [Fintype R]
    (region : F → R) (p : F → Prop) :
    (∑ r, #{f : F | region f = r ∧ p f}) = #{f : F | p f} := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  by_cases hp : p f <;> simp [hp]

/-- Every two-sided finite face assignment has an even number of odd faces. -/
theorem even_odd_faces {E F : Type*} [Fintype E] [Fintype F]
    (face : E × Bool → F) : Even #{f : F | Odd (fiberSize face f)} := by
  classical
  have hcount : (∑ f, fiberSize face f) = Fintype.card E * 2 := by
    simpa using grouped_fiber_sum face (fun _ => ()) ()
  have hpar := odd_count_mod (univ : Finset F) (fiberSize face)
  rw [hcount] at hpar
  rw [Nat.even_iff]
  omega

set_option maxHeartbeats 800000 in
/-- The Lemma 2 parameter estimate from actual side incidences and the Euler
characteristic gluing identity. The gluing identity and the nonempty-boundary
condition remain explicit topology premises; the odd-count estimates do not. -/
theorem genus_bookkeeping_from_sides {E F B R : Type*}
    [Fintype E] [Fintype F] [Fintype B] [Fintype R]
    (face : E × Bool → F) (originalRegion : F → R)
    (boundary : E × Bool → Option B) (boundaryRegion : B → R)
    (paired : ∀ e, boundary (e, false) = none ↔ boundary (e, true) = none)
    (deleted : ∀ e, boundary (e, false) = none →
      originalRegion (face (e, false)) = originalRegion (face (e, true)))
    (retained : ∀ s b, boundary s = some b →
      boundaryRegion b = originalRegion (face s))
    (nonempty_boundary : ∀ r, 1 ≤ #{b : B | boundaryRegion b = r})
    (γ γH : ℕ) (η : R → ℕ)
    (gluing : γ = γH + (∑ r, η r) +
      2 * ∑ r, (#{b : B | boundaryRegion b = r} - 1)) :
    γH ≤ γ ∧
      γH + #{b : B | Odd (boundarySize boundary b)} ≤
        γ + #{f : F | Odd (fiberSize face f)} := by
  classical
  have h := Parameters.summed_genus_bookkeeping γ γH
    #{f : F | Odd (fiberSize face f)}
    (fun r => #{b : B | boundaryRegion b = r}) η
    (fun r => #{b : B | boundaryRegion b = r ∧ Odd (boundarySize boundary b)})
    (fun r => #{f : F | originalRegion f = r ∧ Odd (fiberSize face f)})
    nonempty_boundary (fun r => ?_) (fun r =>
      odd_boundary_parity face originalRegion boundary boundaryRegion
        paired deleted retained r)
    (by convert sum_region_count originalRegion (fun f => Odd (fiberSize face f))) gluing
  · have hs : (∑ r, #{b : B | boundaryRegion b = r ∧ Odd (boundarySize boundary b)}) =
        #{b : B | Odd (boundarySize boundary b)} := by
      convert sum_region_count boundaryRegion (fun b => Odd (boundarySize boundary b))
    refine ⟨h.1, ?_⟩
    calc
      γH + #{b : B | Odd (boundarySize boundary b)} =
          γH + ∑ r, #{b : B | boundaryRegion b = r ∧ Odd (boundarySize boundary b)} := by
        rw [hs]
      _ ≤ _ := h.2
  · apply Finset.card_le_card
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact hb.1

end WeightedMIS.RegionParity
