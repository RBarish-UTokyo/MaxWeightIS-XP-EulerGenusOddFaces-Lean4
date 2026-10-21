module

public import WeightedMIS.FinalAccounting

/-!
# The main claim from a concrete procedure table

For any finite code table carrying the entry procedure
(`RegisterTopLevel.Procedures.Matches`) and the compiled hard-component
solver (`RegisterHardSolve.Procedures.Matches`), whose hard procedure is the
one called by the component loop of the entry procedure, `Spec.MainClaim`
holds with

* the entry procedure `top.top`,
* the computable coefficient `f = FinalAccounting.finalCoefficient`, where
  `finalCoefficient p = FinalCost.finalFactor (topFactor p) p 43 42`,
  `topFactor p = 2 ^ 36 + 2 ^ 230 · 5 ^ p · (p + 6) ^ 42` and
  `finalFactor F q C b = (F + 100) · (102 + 35 · (F + 100 + q + C + b + 4))`,
* the constants `C = 44` and `b = 43`.

The hard budget is charged through `FinalAccounting.sharpBudget`, which
vanishes on bipartite components (the hard procedure is never called on
them). On every nonbipartite residual component the number of global rows is
at most `D(γ, k)` (at most the orientable exponent on an orientable surface)
by `Spec.Drawing.solve_spec`, and both exponents are at most `γ + k`.
-/

@[expose] public section

namespace WeightedMIS.MainTheorem

open WeightedMIS.Spec WeightedMIS.SpecEncoding WeightedMIS.RegisterMachine
open WeightedMIS.FinalAccounting

/-- The cost coefficient of the main claim. -/
abbrev f : ℕ → ℕ := finalCoefficient

/-- The additive exponent constant of the main claim. -/
abbrev C : ℕ := 44

/-- The exponent of `L + 1` in the main claim. -/
abbrev b : ℕ := 43

theorem computable_f : Computable f := computable_finalCoefficient

/-- **The main claim, conditionally on a procedure table.** -/
theorem mainClaim_of_program {P : ℕ} (code : Code P) (top : RegisterTopLevel.Procedures P)
    (hard : RegisterHardSolve.Procedures P) (htop : top.Matches code)
    (hhard : hard.Matches code) (hid : top.hard = hard.hard) : Spec.MainClaim := by
  refine ⟨P, code, top.top, f, C, b, computable_f, ?_⟩
  intro A hA D W w
  have hspec : RegisterComponentSolve.HardSpec code top.hard (indexWidth D)
      (RegisterWeightMask.CanonAt (weightWidth w)) (sharpBudget (indexWidth D) (weightWidth w)) := by
    rw [hid]
    exact hardSpec_sharp (RegisterHardSolve.hard_spec hard code hhard _ _)
  have hR : ∀ y, (Drawing.ribbon hA W).corner y =
      Spec.Flag.equiv _ (D.corner ((Spec.Flag.equiv _).symm y)) := by
    intro y
    have := Drawing.ribbon_corner hA W ((Spec.Flag.equiv _).symm y)
    rwa [Equiv.apply_symm_apply] at this
  obtain ⟨r₀, t₀, h0, hall⟩ := RegisterTopLevel.top_runs top code htop _ D w hspec hR
  obtain ⟨hmax, hrows⟩ := Drawing.solve_spec A hA D W w
  refine ⟨⟨r₀, t₀, h0⟩, fun r t hr => ?_⟩
  obtain ⟨-, -, hout, hcost⟩ := hall r t hr
  refine ⟨⟨_, hout, hmax⟩, ?_, fun hO => ?_⟩
  · exact hcost.trans (cost_le D w _ (FinalBudget.exponentD_le _ _)
      (fun root hnb => (hrows root hnb).1))
  · exact hcost.trans (cost_le D w _ (FinalBudget.orientableExponentD_le _ _)
      (fun root hnb => (hrows root hnb).2 hO))

end WeightedMIS.MainTheorem
