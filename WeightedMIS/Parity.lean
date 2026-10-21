module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic

/-!
# Propagating integrality and the single parity equation

This is the arithmetic part of Lemma 8. Connectivity is expressed by genuine
finite walks in an endpoint multigraph. The existence of a rational solution
to the edge equations and the odd-cycle row identity are explicit premises.
The missing kernel-span construction is not assumed as a proved result.
-/

public section

namespace WeightedMIS.Parity

/-- A finite walk using either direction of an edge of an endpoint multigraph. -/
inductive Walk {V E : Type*} (left right : E → V) : V → V → Prop where
  | nil (v : V) : Walk left right v v
  | forward {a b : V} (e : E) (h : b = left e) :
      Walk left right a b → Walk left right a (right e)
  | backward {a b : V} (e : E) (h : b = right e) :
      Walk left right a b → Walk left right a (left e)

/-- Rational vertex values whose unsigned edge sums are the integer data `b`. -/
@[expose] def Realizes {V E : Type*} (left right : E → V)
    (x : V → ℚ) (b : E → ℤ) : Prop :=
  ∀ e, x (left e) + x (right e) = (b e : ℚ)

/-- Integral right-hand sides propagate integrality along any finite walk. -/
theorem integral_along_walk {V E : Type*} (left right : E → V)
    (x : V → ℚ) (b : E → ℤ) (hx : Realizes left right x b)
    {a c : V} (p : Walk left right a c)
    (ha : ∃ z : ℤ, x a = (z : ℚ)) : ∃ z : ℤ, x c = (z : ℚ) := by
  induction p with
  | nil => exact ha
  | @forward c e h p ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨b e - z, ?_⟩
      have he := hx e
      subst c
      push_cast
      linarith
  | @backward c e h p ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨b e - z, ?_⟩
      have he := hx e
      subst c
      push_cast
      linarith

/-- Connectivity and one integral coordinate give a single integer vector. -/
theorem integer_vector_of_root {V E : Type*} (left right : E → V)
    (root : V) (connected : ∀ v, Walk left right root v)
    (x : V → ℚ) (b : E → ℤ) (hx : Realizes left right x b)
    (hr : ∃ z : ℤ, x root = (z : ℚ)) :
    ∃ z : V → ℤ, ∀ v, x v = (z v : ℚ) := by
  have h : ∀ v, ∃ z : ℤ, x v = (z : ℚ) := fun v =>
    integral_along_walk left right x b hx (connected v) hr
  exact ⟨fun v => Classical.choose (h v), fun v => Classical.choose_spec (h v)⟩

/-- The alternating odd-cycle identity gives the root coordinate exactly. -/
theorem root_equation {V E : Type*} [Fintype E]
    (left right : E → V) (root : V) (π y : E → ℤ) (x : V → ℚ)
    (hπ : ∑ e, π e = 1)
    (hrow : ∑ e, (π e : ℚ) * (x (left e) + x (right e)) = 2 * x root)
    (hx : Realizes left right x (fun e => 1 - y e)) :
    2 * x root = 1 - ((∑ e, π e * y e : ℤ) : ℚ) := by
  calc
    2 * x root = ∑ e, (π e : ℚ) * (x (left e) + x (right e)) := hrow.symm
    _ = ∑ e, (π e : ℚ) * (1 - (y e : ℚ)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [hx e]
      norm_cast
    _ = (∑ e, (π e : ℚ)) - ∑ e, (π e : ℚ) * (y e : ℚ) := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    _ = 1 - ((∑ e, π e * y e : ℤ) : ℚ) := by
      have hπ' : ∑ e, (π e : ℚ) = 1 := by exact_mod_cast hπ
      rw [hπ']
      norm_cast

/-- Precisely one odd integer equation suffices once the rational solution exists. -/
theorem single_parity_criterion {V E : Type*} [Fintype E]
    (left right : E → V) (root : V)
    (connected : ∀ v, Walk left right root v)
    (π y : E → ℤ) (x : V → ℚ)
    (hπ : ∑ e, π e = 1)
    (hrow : ∑ e, (π e : ℚ) * (x (left e) + x (right e)) = 2 * x root)
    (hx : Realizes left right x (fun e => 1 - y e)) :
    (∃ z : V → ℤ, ∀ v, x v = (z v : ℚ)) ↔
      ∃ t : ℤ, ∑ e, π e * y e = 2 * t + 1 := by
  have hr := root_equation left right root π y x hπ hrow hx
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨-z root, ?_⟩
    rw [hz root] at hr
    have hc : ((∑ e, π e * y e : ℤ) : ℚ) = 2 * (-(z root : ℚ)) + 1 := by
      linarith
    exact_mod_cast hc
  · rintro ⟨t, ht⟩
    apply integer_vector_of_root left right root connected x _ hx
    refine ⟨-t, ?_⟩
    have ht' : ((∑ e, π e * y e : ℤ) : ℚ) = 2 * (t : ℚ) + 1 := by
      exact_mod_cast ht
    push_cast
    linarith

end WeightedMIS.Parity
