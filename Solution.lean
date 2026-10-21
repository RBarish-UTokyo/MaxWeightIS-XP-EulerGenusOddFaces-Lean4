module

public import WeightedMIS.MainTheorem
public import WeightedMIS.FinalProgram

/-!
# Solution: the proved main claim

`WeightedMIS.Spec.main_claim` is Theorem 1 of *Maximum-weight independent set
in embedded graphs parameterized by Euler genus and number of odd faces*,
stated in
`Challenge.lean` for the sixteen-register pointer machine with its explicit
bit-stack cost. The witness program is the concrete table
`WeightedMIS.FinalProgram.program` of 634 closed procedure bodies, started at
its top-level entry procedure; the constants are those of
`WeightedMIS.MainTheorem` (`C = 44`, `b = 43`, and the computable coefficient
`MainTheorem.f`).
-/

@[expose] public section

/-- **Theorem 1** (uniform XP bound in `γ + k` with exponent `D(γ, k) + C`). -/
theorem WeightedMIS.Spec.main_claim : WeightedMIS.Spec.MainClaim :=
  WeightedMIS.MainTheorem.mainClaim_of_program WeightedMIS.FinalProgram.program
    WeightedMIS.FinalProgram.topIds WeightedMIS.FinalProgram.hardIds
    WeightedMIS.FinalProgram.topIds_matches WeightedMIS.FinalProgram.hardIds_matches
    WeightedMIS.FinalProgram.hard_id_eq

end
