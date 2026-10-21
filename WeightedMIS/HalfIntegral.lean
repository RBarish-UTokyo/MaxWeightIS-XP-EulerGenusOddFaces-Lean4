module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Half-integrality of the fractional independent-set polytope

A uniform cubic perturbation supplies an alternative proof of Lemma 3 of the
manuscript. Both signs of the perturbation preserve all vertex and edge
inequalities. An extreme point must be fixed by the perturbation, whose only
fixed points are zero, one half, and one. Extremeness is Mathlib's standard
`Set.extremePoints`, not a separately assumed replacement property.
-/

@[expose] public section

namespace WeightedMIS.HalfIntegral

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A cubic vanishing precisely at the three half-integral values. -/
def cubic (t : K) : K := t * (1 - t) * (2 * t - 1)

/-- The positive cubic perturbation. -/
def plus (t : K) : K := t + cubic t / 8

/-- The negative cubic perturbation. -/
def minus (t : K) : K := t - cubic t / 8

private theorem slope_bounds {x y : K} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    -7 ≤ -2 * (y*y + y*x + x*x) + 3 * (y+x) - 1 ∧
    -2 * (y*y + y*x + x*x) + 3 * (y+x) - 1 ≤ 5 := by
  have hx2 : x*x ≤ 1 := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have hy2 : y*y ≤ 1 := by nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
  have hxy : y*x ≤ 1 := by nlinarith [mul_le_mul hy1 hx1 hx0 (by norm_num : (0 : K) ≤ 1)]
  constructor
  · nlinarith
  · nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg hy0 hx0]

/-- Each perturbation is increasing throughout the unit interval. -/
theorem plus_monotone {x y : K} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hxy : x ≤ y) : plus x ≤ plus y := by
  have hb := (slope_bounds hx0 hx1 hy0 hy1).1
  have hp : 0 ≤ (y-x) * (8 + (-2 * (y*y + y*x + x*x) + 3*(y+x) - 1)) :=
    mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
  have he : plus y - plus x =
      (y-x) * (8 + (-2 * (y*y + y*x + x*x) + 3*(y+x) - 1)) / 8 := by
    unfold plus cubic
    ring
  exact sub_nonneg.mp (he ▸ div_nonneg hp (by norm_num))

/-- Monotonicity also holds for the other sign. -/
theorem minus_monotone {x y : K} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hxy : x ≤ y) : minus x ≤ minus y := by
  have hb := (slope_bounds hx0 hx1 hy0 hy1).2
  have hp : 0 ≤ (y-x) * (8 - (-2 * (y*y + y*x + x*x) + 3*(y+x) - 1)) :=
    mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
  have he : minus y - minus x =
      (y-x) * (8 - (-2 * (y*y + y*x + x*x) + 3*(y+x) - 1)) / 8 := by
    unfold minus cubic
    ring
  exact sub_nonneg.mp (he ▸ div_nonneg hp (by norm_num))

@[simp] theorem plus_zero : plus (0 : K) = 0 := by simp [plus, cubic]
@[simp] theorem plus_one : plus (1 : K) = 1 := by simp [plus, cubic]
@[simp] theorem minus_zero : minus (0 : K) = 0 := by simp [minus, cubic]
@[simp] theorem minus_one : minus (1 : K) = 1 := by simp [minus, cubic]

theorem plus_complement (x : K) : plus (1-x) = 1 - plus x := by unfold plus cubic; ring

theorem minus_complement (x : K) : minus (1-x) = 1 - minus x := by unfold minus cubic; ring

theorem plus_bounds {x : K} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ plus x ∧ plus x ≤ 1 := by
  constructor
  · simpa using plus_monotone (x := (0 : K)) (by norm_num) (by norm_num) hx0 hx1 hx0
  · simpa using plus_monotone hx0 hx1 (y := (1 : K)) (by norm_num) (by norm_num) hx1

theorem minus_bounds {x : K} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ minus x ∧ minus x ≤ 1 := by
  constructor
  · simpa using minus_monotone (x := (0 : K)) (by norm_num) (by norm_num) hx0 hx1 hx0
  · simpa using minus_monotone hx0 hx1 (y := (1 : K)) (by norm_num) (by norm_num) hx1

/-- The standard fractional independent-set feasible set, over an ordered field. -/
def polytope {V : Type*} (adj : V → V → Prop) : Set (V → K) :=
  {z | (∀ v, 0 ≤ z v ∧ z v ≤ 1) ∧ ∀ u v, adj u v → z u + z v ≤ 1}

theorem plus_feasible {V : Type*} (adj : V → V → Prop) (z : V → K)
    (hz : z ∈ polytope adj) : (fun v => plus (z v)) ∈ polytope adj := by
  constructor
  · intro v
    exact plus_bounds (hz.1 v).1 (hz.1 v).2
  · intro u v huv
    have hx := hz.1 u
    have hy := hz.1 v
    have he := hz.2 u v huv
    have hm := plus_monotone hy.1 hy.2 (x := z v) (y := 1-z u)
      (by linarith) (by linarith) (by linarith)
    rw [plus_complement] at hm
    linarith

theorem minus_feasible {V : Type*} (adj : V → V → Prop) (z : V → K)
    (hz : z ∈ polytope adj) : (fun v => minus (z v)) ∈ polytope adj := by
  constructor
  · intro v
    exact minus_bounds (hz.1 v).1 (hz.1 v).2
  · intro u v huv
    have hx := hz.1 u
    have hy := hz.1 v
    have he := hz.2 u v huv
    have hm := minus_monotone hy.1 hy.2 (x := z v) (y := 1-z u)
      (by linarith) (by linarith) (by linarith)
    rw [minus_complement] at hm
    linarith

/-- Every extreme point of the fractional independent-set polytope is half-integral.
This holds over both the rational and real numbers, and permits any adjacency
relation. In particular it covers finite loopless multigraphs via adjacency. -/
theorem extreme_point_half_integral {V : Type*} (adj : V → V → Prop) (z : V → K)
    (hz : z ∈ (polytope adj).extremePoints K) :
    ∀ v, z v = 0 ∨ z v = 1 / 2 ∨ z v = 1 := by
  have hsegment : z ∈ openSegment K (fun v => plus (z v)) (fun v => minus (z v)) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext v
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold plus minus
    ring
  have hfixed : (fun v => plus (z v)) = z :=
    hz.2 (plus_feasible adj z hz.1) (minus_feasible adj z hz.1) hsegment
  intro v
  have he := congr_fun hfixed v
  have hc : z v * (1-z v) * (2*z v-1) = 0 := by
    dsimp [plus, cubic] at he
    linarith
  rcases mul_eq_zero.mp hc with hc | hc
  · rcases mul_eq_zero.mp hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr (Or.inr (by linarith))
  · exact Or.inr (Or.inl (by linarith))

end WeightedMIS.HalfIntegral
