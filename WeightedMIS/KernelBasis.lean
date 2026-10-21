module

public import WeightedMIS.BoundedCycles
public import WeightedMIS.Incidence
public import WeightedMIS.Complement

/-!
# Bounded integral generators of the incidence kernel

An integral vector in the unsigned incidence kernel determines signs on edges.
Its absolute values form a nonnegative flow in the signed-stub graph. Decomposing
that flow into walks with distinct arcs produces conformal integral kernel
vectors with every coordinate between minus two and two. Clearing denominators
then gives bounded integral generators of the rational kernel.
-/

@[expose] public section

namespace WeightedMIS.KernelBasis

open WeightedMIS.Walks Matrix

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]

/-- Unsigned incidence with integer coefficients, counting both endpoints. -/
def entry (left right : E → V) (e : E) (v : V) : ℤ :=
  (if v = left e then 1 else 0) + (if v = right e then 1 else 0)

/-- The integer incidence equations. -/
def IntegralKernel (left right : E → V) (z : E → ℤ) : Prop :=
  ∀ v, ∑ e, entry left right e v * z e = 0

omit [DecidableEq E] [Fintype V] [Fintype E] in
@[simp] theorem cast_entry (left right : E → V) (e : E) (v : V) :
    (entry left right e v : ℚ) = Incidence.unsigned left right e v := by
  simp [entry, Incidence.unsigned]

omit [DecidableEq E] [Fintype V] in
/-- The integer equations are exactly rational left-kernel membership. -/
theorem integralKernel_iff (left right : E → V) (z : E → ℤ) :
    IntegralKernel left right z ↔
      (fun e => (z e : ℚ)) ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  simp only [IntegralKernel, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, funext_iff, Pi.zero_apply]
  constructor
  · intro h v
    have hcast := congrArg (fun a : ℤ => (a : ℚ)) (h v)
    simpa using hcast
  · intro h v
    apply Int.cast_injective (α := ℚ)
    simpa using h v

/-- Signs chosen from an integral edge vector. -/
def vectorSign (z : E → ℤ) (e : E) : Bool := decide (0 ≤ z e)

omit [DecidableEq E] [Fintype E] in
theorem sign_mul_natAbs (z : E → ℤ) (e : E) :
    signValue (vectorSign z e) * (z e).natAbs = z e := by
  by_cases h : 0 ≤ z e
  · simp [vectorSign, signValue, h, Int.natAbs_of_nonneg h]
  · have hn : z e ≤ 0 := le_of_lt (lt_of_not_ge h)
    simp [vectorSign, signValue, h, abs_of_nonpos hn]

/-- Both endpoint stubs receive the sign of their edge coordinate. -/
def columns (left right : E → V) (sg : E → Bool) (e : E) : Column V :=
  .two (left e, sg e) (right e, sg e)

omit [DecidableEq E] [Fintype V] [Fintype E] in
theorem column_eq (left right : E → V) (sg : E → Bool) (e : E) (v : V) :
    columnVector (columns left right sg e) v = entry left right e v * signValue (sg e) := by
  by_cases hl : v = left e <;> by_cases hr : v = right e <;>
    simp [columns, columnVector, potential, entry, hl, hr, add_mul]

omit [Fintype V] in
/-- The signed projection of a closed walk is an integral incidence-kernel vector. -/
theorem signed_projection_kernel (left right : E → V) (sg : E → Bool)
    (w : ClosedWalk (columns left right sg)) :
    IntegralKernel left right (fun e => signValue (sg e) * (projection w.2.labels e : ℤ)) := by
  intro v
  simpa only [column_eq, mul_assoc] using w.2.closed_projection_kernel v

omit [DecidableEq E] [Fintype E] in
theorem signed_projection_bound (sg : E → Bool) (p : E → ℕ)
    (hp : ∀ e, p e ≤ 2) (e : E) : |signValue (sg e) * (p e : ℤ)| ≤ 2 := by
  have h := hp e
  cases sg e <;> simp [signValue] <;> omega

/-- Each integral kernel vector is a finite sum of bounded integral kernel vectors. -/
theorem integral_decomposition (left right : E → V) (z : E → ℤ)
    (hz : IntegralKernel left right z) :
    ∃ zs : List (E → ℤ),
      zs.sum = z ∧ ∀ w ∈ zs, IntegralKernel left right w ∧ ∀ e, |w e| ≤ 2 := by
  let sg := vectorSign z
  let C := columns left right sg
  have hflow : ∀ v, ∑ e, columnVector (C e) v * ((z e).natAbs : ℤ) = 0 := by
    intro v
    simp only [C, column_eq, mul_assoc, sg, sign_mul_natAbs]
    exact hz v
  obtain ⟨ws, hproj, hb⟩ := BoundedCycles.flow_generated_by_bounded_cycles C
    (fun e => (z e).natAbs) hflow
  let project : ClosedWalk C → E → ℤ :=
    fun w e => signValue (sg e) * (projection w.2.labels e : ℤ)
  refine ⟨ws.map project, ?_, ?_⟩
  · funext e
    have hsum : ((ws.map project).sum) e =
        signValue (sg e) * (projection (ws.flatMap (fun w => w.2.labels)) e : ℤ) := by
      clear hproj hb
      induction ws with
      | nil => simp [projection]
      | cons w ws ih =>
          simp only [List.map_cons, List.sum_cons, Pi.add_apply, List.flatMap_cons,
            projection, List.count_append, Nat.cast_add, mul_add]
          exact congrArg (fun a => project w e + a) ih
    rw [hsum, hproj]
    exact sign_mul_natAbs z e
  · intro w hw
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
    exact ⟨signed_projection_kernel left right sg c,
      signed_projection_bound sg (projection c.2.labels) (hb c hc)⟩

omit [DecidableEq E] in
/-- A common positive denominator for every vector on a finite index type. -/
theorem common_denominator (x : E → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ z : E → ℤ, ∀ e, (d : ℚ) * x e = (z e : ℚ) := by
  classical
  let d := ∏ e, (x e).den
  have hd : 0 < d := Finset.prod_pos (fun e _ => (x e).den_pos)
  have hdiv (e : E) : (x e).den ∣ d :=
    Finset.dvd_prod_of_mem (fun e => (x e).den) (Finset.mem_univ e)
  refine ⟨d, hd, fun e => (d / (x e).den : ℕ) * (x e).num, ?_⟩
  intro e
  have hmul : (x e).den * (d / (x e).den) = d := Nat.mul_div_cancel' (hdiv e)
  have hm : ((x e).den : ℚ) * ((d / (x e).den : ℕ) : ℚ) = (d : ℚ) := by
    exact_mod_cast hmul
  calc
    (d : ℚ) * x e = ((d / (x e).den : ℕ) : ℚ) * (((x e).den : ℚ) * x e) := by
      rw [← hm]; ring
    _ = ((d / (x e).den : ℕ) : ℚ) * (x e).num := by rw [Rat.den_mul_eq_num]
    _ = _ := by push_cast; rfl

/-- Rational vectors obtained from bounded integral incidence-kernel vectors. -/
def boundedGenerators (left right : E → V) : Set (E → ℚ) :=
  {x | ∃ z : E → ℤ, IntegralKernel left right z ∧ (∀ e, |z e| ≤ 2) ∧
    x = fun e => (z e : ℚ)}

omit [DecidableEq E] [Fintype V] in
/-- Every bounded generator belongs to the actual incidence left kernel. -/
theorem boundedGenerators_subset (left right : E → V) :
    boundedGenerators left right ⊆
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  rintro x ⟨z, hz, _, rfl⟩
  exact (integralKernel_iff left right z).mp hz

/-- Every integral kernel vector belongs to the rational span of the bounded generators. -/
theorem integral_mem_span (left right : E → V) (z : E → ℤ)
    (hz : IntegralKernel left right z) :
    (fun e => (z e : ℚ)) ∈ Submodule.span ℚ (boundedGenerators left right) := by
  obtain ⟨zs, heq, hb⟩ := integral_decomposition left right z hz
  subst z
  clear hz
  induction zs with
  | nil =>
      convert (Submodule.span ℚ (boundedGenerators left right)).zero_mem using 1
      ext e
      simp
  | cons w ws ih =>
      have hw := hb w List.mem_cons_self
      have ht : ∀ w ∈ ws, IntegralKernel left right w ∧ ∀ e, |w e| ≤ 2 :=
        fun w hw => hb w (List.mem_cons_of_mem _ hw)
      have hm : (fun e => (w e : ℚ)) ∈ Submodule.span ℚ (boundedGenerators left right) :=
        Submodule.subset_span ⟨w, hw.1, hw.2, rfl⟩
      have hs := (Submodule.span ℚ (boundedGenerators left right)).add_mem hm (ih ht)
      convert hs using 1
      ext e
      simp

/-- The bounded integral generators span the entire rational left kernel. -/
theorem span_boundedGenerators (left right : E → V) :
    Submodule.span ℚ (boundedGenerators left right) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (boundedGenerators_subset left right)
  · intro x hx
    obtain ⟨d, hd, z, hz⟩ := common_denominator x
    have hcast : (fun e => (z e : ℚ)) = (d : ℚ) • x := by
      funext e
      exact (hz e).symm
    have hzker : IntegralKernel left right z := by
      apply (integralKernel_iff left right z).mpr
      rw [hcast]
      exact (LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin).smul_mem (d : ℚ) hx
    have hm := integral_mem_span left right z hzker
    rw [hcast] at hm
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    have hinv := (Submodule.span ℚ (boundedGenerators left right)).smul_mem ((d : ℚ)⁻¹) hm
    simpa only [smul_smul, inv_mul_cancel₀ hdq, one_smul] using hinv

/-- A connected nonbipartite graph has a rational kernel basis consisting of
integral vectors whose coordinates have absolute value at most two. -/
theorem bounded_basis (left right : E → V) (hconn : Incidence.Connected left right)
    (hnot : ¬ Incidence.Bipartite left right) :
    ∃ W : Fin (Fintype.card E - Fintype.card V) → E → ℤ,
      (∀ i, IntegralKernel left right (W i) ∧ ∀ e, |W i e| ≤ 2) ∧
      LinearIndependent ℚ (fun i e => (W i e : ℚ)) ∧
      Submodule.span ℚ (Set.range (fun i e => (W i e : ℚ))) =
        LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  have h := Submodule.exists_fun_fin_finrank_span_eq ℚ (boundedGenerators left right)
  rw [span_boundedGenerators, Incidence.left_kernel_finrank left right hconn hnot] at h
  obtain ⟨f, hf, hspan, hli⟩ := h
  simp only [boundedGenerators, Set.mem_ofPred_eq] at hf
  choose W hW hb heq using hf
  have heq' : f = (fun i e => (W i e : ℚ)) := funext heq
  rw [heq'] at hspan hli
  exact ⟨W, fun i => ⟨hW i, hb i⟩, hli, hspan⟩

/-- Bounded integral rows complete any subspace of the incidence kernel,
using exactly the difference of the dimensions. -/
theorem bounded_complement (left right : E → V) (hconn : Incidence.Connected left right)
    (hnot : ¬ Incidence.Bipartite left right) (P : Submodule ℚ (E → ℚ))
    (hP : P ≤ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) :
    ∃ W : Fin (Fintype.card E - Fintype.card V - Module.finrank ℚ P) → E → ℤ,
      (∀ i, IntegralKernel left right (W i) ∧ ∀ e, |W i e| ≤ 2) ∧
      P ⊔ Submodule.span ℚ (Set.range (fun i e => (W i e : ℚ))) =
        LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  have h := Complement.exists_fin_complement P
    (LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) hP
    (boundedGenerators left right) (span_boundedGenerators left right)
  rw [Incidence.left_kernel_finrank left right hconn hnot] at h
  obtain ⟨f, hf, hspan⟩ := h
  simp only [boundedGenerators, Set.mem_ofPred_eq] at hf
  choose W hW hb heq using hf
  have heq' : f = (fun i e => (W i e : ℚ)) := funext heq
  rw [heq'] at hspan
  exact ⟨W, fun i => ⟨hW i, hb i⟩, hspan⟩

end WeightedMIS.KernelBasis
