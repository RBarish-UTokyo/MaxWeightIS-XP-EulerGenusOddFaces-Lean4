module

public import WeightedMIS.ResidualPhaseRefinement
public import WeightedMIS.ResidualListScales
public import WeightedMIS.MaxFlowOverscaled

/-!
# Binary residual scales refine the capacity-scaling solver

Iterating `ResidualPhaseRefinement.phase_refines` over the descending binary
scales shows that the stored residual scale loop represents
`MaxFlowScaling.scales`, provided each phase receives the phase fuel
`MaxFlowScaling.phaseFuel V`. Starting from the stored capacity table and the
leading power `RegisterHalve.powerTop b`, the stored solver represents the
entry-width solver `MaxFlowScaling.solveFromExponent c nodes s t (b - 1)`, whose
flow and cut agree with those of `MaxFlowScaling.solve`.
-/

@[expose] public section

namespace WeightedMIS.ResidualScalesRefinement

open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords
open WeightedMIS.ResidualCrossingRefinement WeightedMIS.ResidualPhaseRefinement

variable {V : Type*} [Fintype V] [DecidableEq V] {n b : ℕ}

omit [DecidableEq V] in
/-- `Represents` depends only on the flow and the cut of the result. -/
theorem represents_congr {enc : V → Bits n} {nodes : List V} {c : V → V → ℕ} {s t : V}
    {words : ResidualListPhase.Result n b} {r r' : MaxFlowScaling.Result V}
    (hflow : r.flow = r'.flow) (hcut : r.cut = r'.cut)
    (hr : Represents enc nodes c s t words r) : Represents enc nodes c s t words r' := by
  obtain ⟨hf, caps, htable, hcap, hseen⟩ := hr
  exact ⟨hflow ▸ hf, caps, htable, fun u v => hflow ▸ hcap u v, hcut ▸ hseen⟩

omit [Fintype V] [DecidableEq V] in
theorem matrix_zero (c : V → V → ℕ) (u v : V) :
    MaxFlowResidual.matrix c (fun _ _ => 0) u v = c u v := by
  simp [MaxFlowResidual.matrix, MaxFlowCore.residual]

/-- `k + 1` stored rounds starting at the scale `2^k` represent the `k + 1`
phases of `MaxFlowScaling.scales c nodes s t k`. The carried cut is arbitrary. -/
theorem scales_refines (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (c : V → V → ℕ) (s t : V) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (hlen : nodes.length = Fintype.card V)
    (hwidth : ∀ u v, c u v + c v u < 2 ^ b) (k : ℕ) (delta : Bits b)
    (hdelta : delta.value = 2 ^ k)
    (f : V → V → ℤ) (hf : MaxFlowCore.Feasible c s t f)
    (caps : V → V → Bits b)
    (hcap : ∀ u v, (caps u v).value = MaxFlowResidual.matrix c f u v)
    (seen : List (Bits n)) :
    Represents enc nodes c s t
      (ResidualListScales.scales (nodes.map enc) (enc s) (enc t) (MaxFlowScaling.phaseFuel V)
        (k + 1) delta ((nodes.product nodes).map (encodeArc enc caps)) seen)
      (MaxFlowScaling.scales c nodes s t k f) := by
  induction k generalizing delta f caps seen with
  | zero =>
    have hp := phase_refines enc hinj c s t nodes complete hlen delta
      (MaxFlowScaling.phaseFuel V) f hf caps hcap hwidth
    rw [hdelta, pow_zero] at hp
    exact hp
  | succ k ih =>
    have hp := phase_refines enc hinj c s t nodes complete hlen delta
      (MaxFlowScaling.phaseFuel V) f hf caps hcap hwidth
    rw [hdelta] at hp
    obtain ⟨hf', caps', htable, hcap', -⟩ := hp
    have hhalf : (RegisterHalve.halve delta).value = 2 ^ k := by
      rw [RegisterHalve.halve_value, hdelta, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hrec := ih (RegisterHalve.halve delta) hhalf _ hf' caps' hcap'
      (ResidualListPhase.phase delta (nodes.map enc) (enc s) (enc t) (MaxFlowScaling.phaseFuel V)
        ((nodes.product nodes).map (encodeArc enc caps))).seen
    rw [← htable] at hrec
    exact represents_congr rfl rfl hrec

/-- The stored solver, started at `powerTop b` on the input capacity words,
represents the entry-width solver with exponent `b - 1`. -/
theorem solve_refines (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (c : V → V → ℕ) (s t : V) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (hlen : nodes.length = Fintype.card V) (hb : 0 < b)
    (hwidth : ∀ u v, c u v + c v u < 2 ^ b)
    (caps : V → V → Bits b) (hcap : ∀ u v, (caps u v).value = c u v) :
    Represents enc nodes c s t
      (ResidualListScales.solve (nodes.map enc) (enc s) (enc t) (MaxFlowScaling.phaseFuel V)
        ((nodes.product nodes).map (encodeArc enc caps)))
      (MaxFlowScaling.solveFromExponent c nodes s t (b - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  exact scales_refines enc hinj c s t nodes complete hlen hwidth k (RegisterHalve.powerTop (k + 1))
    (RegisterHalve.powerTop_value k) _ (MaxFlowCore.zero_feasible c s t) caps
    (fun u v => by rw [hcap, matrix_zero]) []

/-- For distinct terminals, the stored solver represents exactly the flow and
cut returned by `MaxFlowScaling.solve`. -/
theorem solve_matches (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (c : V → V → ℕ) (s t : V) (hst : s ≠ t) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (hlen : nodes.length = Fintype.card V) (hb : 0 < b)
    (hwidth : ∀ u v, c u v + c v u < 2 ^ b)
    (caps : V → V → Bits b) (hcap : ∀ u v, (caps u v).value = c u v) :
    Represents enc nodes c s t
      (ResidualListScales.solve (nodes.map enc) (enc s) (enc t) (MaxFlowScaling.phaseFuel V)
        ((nodes.product nodes).map (encodeArc enc caps)))
      (MaxFlowScaling.solve c nodes s t) := by
  have hentries (u v : V) : c u v < 2 ^ (b - 1 + 1) := by
    rw [Nat.sub_add_cancel hb]
    have := hwidth u v
    omega
  have heq := MaxFlowScaling.solveFromExponent_output_eq_of_entries c nodes s t hst (b - 1) hentries
  exact represents_congr heq.1 heq.2
    (solve_refines enc hinj c s t nodes complete hlen hb hwidth caps hcap)

/-- The same statement with the attempt count written as the length formula
`2 * N^2 + 1` of the constructed attempt list, `N` the number of vertex words. -/
theorem solve_matches_length (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (c : V → V → ℕ) (s t : V) (hst : s ≠ t) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (hlen : nodes.length = Fintype.card V) (hb : 0 < b)
    (hwidth : ∀ u v, c u v + c v u < 2 ^ b)
    (caps : V → V → Bits b) (hcap : ∀ u v, (caps u v).value = c u v) :
    Represents enc nodes c s t
      (ResidualListScales.solve (nodes.map enc) (enc s) (enc t)
        (2 * (nodes.map enc).length ^ 2 + 1) ((nodes.product nodes).map (encodeArc enc caps)))
      (MaxFlowScaling.solve c nodes s t) := by
  have hfuel : 2 * (nodes.map enc).length ^ 2 + 1 = MaxFlowScaling.phaseFuel V := by
    simp [MaxFlowScaling.phaseFuel, hlen]
  rw [hfuel]
  exact solve_matches enc hinj c s t hst nodes complete hlen hb hwidth caps hcap

end WeightedMIS.ResidualScalesRefinement
