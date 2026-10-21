module

public import WeightedMIS.HalfIntegral
public import WeightedMIS.Persistence
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Tactic

/-!
# Existence of an optimal half-integral LP point

For a finite graph and arbitrary rational weights, compactness and an exposed
optimal face give a genuine extreme optimum of the real fractional independent-
set polytope. Half-integrality supplies rational coordinates. This is an
existence theorem; it makes no claim about an implementation or its running time.
-/

@[expose] public section

namespace WeightedMIS.LPExistence

open scoped BigOperators
open Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The usual real linear objective, summing weight times vertex value. -/
def realObjective (w x : V → ℝ) : ℝ := ∑ v, w v * x v

/-- The objective as a continuous linear functional. -/
noncomputable def objectiveCLM (w : V → ℝ) : (V → ℝ) →L[ℝ] ℝ :=
  ∑ v, w v • ContinuousLinearMap.proj v

@[simp] theorem objectiveCLM_apply (w x : V → ℝ) :
    objectiveCLM w x = realObjective w x := by
  simp [objectiveCLM, realObjective]

/-- The finite fractional independent-set polytope is closed. -/
theorem polytope_closed (adj : V → V → Prop) :
    IsClosed (HalfIntegral.polytope (K := ℝ) adj) := by
  unfold HalfIntegral.polytope
  simp only [ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun v =>
      (isClosed_le continuous_const (continuous_apply v)).inter
        (isClosed_le (continuous_apply v) continuous_const)
  · exact isClosed_iInter fun u => isClosed_iInter fun v => isClosed_iInter fun _ =>
      isClosed_le ((continuous_apply u).add (continuous_apply v)) continuous_const

/-- Vertex bounds make the closed feasible set compact. -/
theorem polytope_compact (adj : V → V → Prop) :
    IsCompact (HalfIntegral.polytope (K := ℝ) adj) := by
  apply (isCompact_Icc (a := (0 : V → ℝ)) (b := 1)).of_isClosed_subset
    (polytope_closed adj)
  intro z hz
  exact ⟨fun v => (hz.1 v).1, fun v => (hz.1 v).2⟩

/-- The zero vector is feasible for every graph. -/
theorem polytope_nonempty (adj : V → V → Prop) :
    (HalfIntegral.polytope (K := ℝ) adj).Nonempty := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro v; norm_num
  · intro u v _; norm_num

/-- A real optimum can be chosen to be a genuine extreme point. -/
theorem exists_real_extreme_optimum (adj : V → V → Prop) (w : V → ℝ) :
    ∃ z : V → ℝ, z ∈ (HalfIntegral.polytope adj).extremePoints ℝ ∧
      ∀ x ∈ HalfIntegral.polytope adj, realObjective w x ≤ realObjective w z := by
  let P := HalfIntegral.polytope (K := ℝ) adj
  let l := objectiveCLM w
  have hc : IsCompact P := polytope_compact adj
  obtain ⟨x, hx, hm⟩ := hc.exists_isMaxOn (polytope_nonempty adj) l.continuous.continuousOn
  let F := l.toExposed P
  have he : IsExposed ℝ P F := ContinuousLinearMap.toExposed.isExposed
  have hn : F.Nonempty := ⟨x, hx, hm⟩
  have hfc : IsCompact F := hc.of_isClosed_subset (he.isClosed hc.isClosed) he.subset
  obtain ⟨z, hz⟩ := hfc.extremePoints_nonempty hn
  refine ⟨z, he.isExtreme.extremePoints_subset_extremePoints hz, ?_⟩
  intro y hy
  have h := hz.1.2 y hy
  simpa [l] using h

/-- Interpret a rational vector as a real vector, coordinate by coordinate. -/
def realify (x : V → ℚ) : V → ℝ := fun v => (x v : ℝ)

/-- Rational feasibility is preserved under the ordinary inclusion into the reals. -/
theorem realify_feasible (adj : V → V → Prop) (x : V → ℚ)
    (hx : Persistence.Feasible adj x) : realify x ∈ HalfIntegral.polytope adj := by
  constructor
  · intro v
    constructor <;> dsimp [realify]
    · exact_mod_cast (hx.1 v).1
    · exact_mod_cast (hx.1 v).2
  · intro u v huv
    dsimp [realify]
    exact_mod_cast hx.2 u v huv

/-- Rational and real objectives agree exactly under scalar inclusion. -/
theorem realify_objective (w x : V → ℚ) :
    realObjective (realify w) (realify x) = (Persistence.objective w x : ℝ) := by
  simp [realObjective, realify, Persistence.objective]

/-- Feasibility of a rational vector can be read back from its real image. -/
theorem feasible_of_realify (adj : V → V → Prop) (q : V → ℚ)
    (hz : realify q ∈ HalfIntegral.polytope adj) : Persistence.Feasible adj q := by
  constructor
  · intro v
    have h0 := (hz.1 v).1
    have h1 := (hz.1 v).2
    dsimp [realify] at h0 h1
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩
  · intro u v huv
    have h := hz.2 u v huv
    dsimp [realify] at h
    exact_mod_cast h

/-- A rational point whose real image is extreme is extreme over the rationals. -/
theorem extreme_of_realify (adj : V → V → Prop) (q : V → ℚ)
    (he : realify q ∈ (HalfIntegral.polytope adj).extremePoints ℝ) :
    q ∈ (HalfIntegral.polytope adj).extremePoints ℚ := by
  refine ⟨feasible_of_realify adj q he.1, ?_⟩
  intro x hx y hy hseg
  have hs : realify q ∈ openSegment ℝ (realify x) (realify y) := by
    obtain ⟨a, b, ha, hb, hab, hv⟩ := hseg
    refine ⟨(a : ℝ), (b : ℝ), by exact_mod_cast ha, by exact_mod_cast hb,
      by exact_mod_cast hab, ?_⟩
    funext v
    have h := congrFun hv v
    change a * x v + b * y v = q v at h
    dsimp [realify]
    exact_mod_cast h
  have h := he.2 (realify_feasible adj x hx) (realify_feasible adj y hy) hs
  funext v
  have hv := congrFun h v
  dsimp [realify] at hv
  exact_mod_cast hv

/-- Every rationally weighted finite graph has a rational feasible optimum whose
coordinates are zero, one half, or one. The proof uses actual compactness and
extremeness, not an assumed optimization oracle. -/
theorem exists_rational_extreme_optimum (adj : V → V → Prop) (w : V → ℚ) :
    ∃ q : V → ℚ, Persistence.Optimal adj w q ∧
      q ∈ (HalfIntegral.polytope adj).extremePoints ℚ ∧ Persistence.HalfIntegral q := by
  obtain ⟨z, he, hm⟩ := exists_real_extreme_optimum adj (realify w)
  have hh := HalfIntegral.extreme_point_half_integral adj z he
  let q : V → ℚ := fun v => if z v = 0 then 0 else if z v = 1 then 1 else 1 / 2
  have hq : realify q = z := by
    funext v
    rcases hh v with hv | hv | hv <;> simp [realify, q, hv]
  have hqf : Persistence.Feasible adj q := by
    apply feasible_of_realify adj q
    rw [hq]
    exact he.1
  have hqe : q ∈ (HalfIntegral.polytope adj).extremePoints ℚ := by
    apply extreme_of_realify adj q
    rwa [hq]
  refine ⟨q, ⟨hqf, ?_⟩, hqe, ?_⟩
  · intro x hx
    have h := hm (realify x) (realify_feasible adj x hx)
    rw [← hq, realify_objective, realify_objective] at h
    exact_mod_cast h
  · intro v
    rcases hh v with hv | hv | hv <;> simp [q, hv]

/-- In particular, an optimal half-integral rational point exists. -/
theorem exists_rational_half_optimum (adj : V → V → Prop) (w : V → ℚ) :
    ∃ q : V → ℚ, Persistence.Optimal adj w q ∧ Persistence.HalfIntegral q := by
  obtain ⟨q, ho, _, hh⟩ := exists_rational_extreme_optimum adj w
  exact ⟨q, ho, hh⟩

/-- The mathematical preprocessing conclusion holds unconditionally for every
finite rationally weighted graph: an extreme optimum exists, its persistent
exchange never loses weight, and its residual all-half vector is optimal.
This theorem asserts existence, not a runtime bound for finding the point. -/
theorem exists_weighted_preprocessing (adj : V → V → Prop) (w : V → ℚ) :
    ∃ z : V → ℚ, Persistence.Optimal adj w z ∧
      z ∈ (HalfIntegral.polytope adj).extremePoints ℚ ∧
      (∀ I, Persistence.Independent adj I →
        Persistence.Independent adj (Persistence.replacement z I) ∧
          Persistence.weight w I ≤ Persistence.weight w (Persistence.replacement z I)) ∧
      (Persistence.ResidualFeasible adj z (fun _ => 1 / 2) ∧
        ∀ x, Persistence.ResidualFeasible adj z x →
          Persistence.residualObjective w z x ≤
            Persistence.residualObjective w z (fun _ => 1 / 2)) := by
  obtain ⟨z, ho, he, hh⟩ := exists_rational_extreme_optimum adj w
  exact ⟨z, ho, he, fun I hI => Persistence.weighted_persistence adj w z I ho hh hI,
    Persistence.residual_half_optimal adj w z ho hh⟩

end WeightedMIS.LPExistence
