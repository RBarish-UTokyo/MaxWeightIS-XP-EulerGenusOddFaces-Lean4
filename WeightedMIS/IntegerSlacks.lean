module

public import WeightedMIS.Incidence
public import WeightedMIS.LinearAlgebra
public import WeightedMIS.Parity
public import WeightedMIS.Slack
public import WeightedMIS.OddRow

/-!
# Integer feasibility from the kernel equations and one parity bit

Theorem `integer_slack_criterion` combines rational linear algebra with genuine
graph connectivity and integer propagation. It proves the equivalence of
Lemma 8 for the specified kernel-spanning rows. The final theorem
`exists_integer_slack_criterion` constructs the alternating odd row from
connectedness and nonbipartiteness. Constructing the kernel-spanning rows
from a surface embedding remains a separate proof obligation.
-/

@[expose] public section

namespace WeightedMIS.IntegerSlacks

open Matrix

variable {V E R S : Type*} [Fintype V] [Fintype E] [DecidableEq V]

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- Forgetting a walk's length preserves its actual edge traversals. -/
theorem walk_forget_length (left right : E → V) {a b : V} {n : ℕ}
    (p : Incidence.Walk left right a b n) : Parity.Walk left right a b := by
  induction p with
  | nil => exact .nil _
  | forward e h p ih => exact .forward e h ih
  | backward e h p ih => exact .backward e h ih

/-- A row with the alternating odd-cycle functional identity. -/
def OddRow (left right : E → V) (root : V) (π : E → ℤ) : Prop :=
  ∀ x : V → ℚ,
    ∑ e, (π e : ℚ) * (x (left e) + x (right e)) = 2 * x root

omit [Fintype V] [DecidableEq V] in
/-- Applying an odd row to the constant half-vector gives row sum one. -/
theorem odd_row_sum (left right : E → V) (root : V) (π : E → ℤ)
    (hπ : OddRow left right root π) : ∑ e, π e = 1 := by
  have h := hπ (fun _ => 1 / 2)
  norm_num at h
  exact_mod_cast h

/-- Exact integer feasibility: kernel equations plus a single odd scalar.
The matrices `B,W` are ordinary matrices whose row-span condition is explicit.
The integer vector is unbounded; nonnegativity is handled separately below. -/
theorem integer_slack_criterion (left right : E → V) (root : V)
    (hc : Incidence.Connected left right)
    (B : Matrix R E ℚ) (W : Matrix S E ℚ)
    (hspan : Submodule.span ℚ (Set.range B ∪ Set.range W) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (π : E → ℤ) (hπ : OddRow left right root π) (y : E → ℤ) :
    (∃ z : V → ℤ, ∀ e, z (left e) + z (right e) = 1 - y e) ↔
      B *ᵥ (fun e => (y e : ℚ)) = 0 ∧
      W *ᵥ (fun e => (y e : ℚ)) = 0 ∧
      ∃ t : ℤ, ∑ e, π e * y e = 2 * t + 1 := by
  have hconn : ∀ v, Parity.Walk left right root v := by
    intro v
    obtain ⟨n, p⟩ := hc root v
    exact walk_forget_length left right p
  have hsum := odd_row_sum left right root π hπ
  have heq := LinearAlgebra.kernel_equations_iff_slack
    (Incidence.unsigned left right) B W hspan
    (Incidence.unsigned_mulVec_one left right) (fun e => (y e : ℚ))
  constructor
  · rintro ⟨z, hz⟩
    let x : V → ℚ := fun v => (z v : ℚ)
    have hx : Parity.Realizes left right x (fun e => 1 - y e) := by
      intro e
      dsimp [x]
      exact_mod_cast hz e
    have hm : Incidence.unsigned left right *ᵥ x = (1 : E → ℚ) -
        (fun e => (y e : ℚ)) := by
      ext e
      simpa [Parity.Realizes] using hx e
    have hb := heq.mpr ⟨x, hm⟩
    refine ⟨hb.1, hb.2, ?_⟩
    exact (Parity.single_parity_criterion left right root hconn π y x hsum
      (hπ x) hx).mp ⟨z, fun _ => rfl⟩
  · rintro ⟨hB, hW, hp⟩
    obtain ⟨x, hx⟩ := heq.mp ⟨hB, hW⟩
    have hr : Parity.Realizes left right x (fun e => 1 - y e) := by
      intro e
      have h := congrFun hx e
      simpa using h
    obtain ⟨z, hz⟩ := (Parity.single_parity_criterion left right root hconn π y x
      hsum (hπ x) hr).mpr hp
    refine ⟨z, ?_⟩
    intro e
    have h := hr e
    rw [hz, hz] at h
    exact_mod_cast h

/-- Adding nonnegative slack is precisely the integer independent-set
relaxation used by the threshold recovery theorem. -/
theorem nonnegative_integer_slack_criterion (left right : E → V) (root : V)
    (hc : Incidence.Connected left right)
    (B : Matrix R E ℚ) (W : Matrix S E ℚ)
    (hspan : Submodule.span ℚ (Set.range B ∪ Set.range W) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (π : E → ℤ) (hπ : OddRow left right root π) (y : E → ℤ)
    (hy : ∀ e, 0 ≤ y e) :
    (∃ z : V → ℤ, Slack.Feasible left right z ∧
      ∀ e, Slack.slack left right z e = y e) ↔
      B *ᵥ (fun e => (y e : ℚ)) = 0 ∧
      W *ᵥ (fun e => (y e : ℚ)) = 0 ∧
      ∃ t : ℤ, ∑ e, π e * y e = 2 * t + 1 := by
  rw [← integer_slack_criterion left right root hc B W hspan π hπ y]
  constructor
  · rintro ⟨z, _, hz⟩
    refine ⟨z, ?_⟩
    intro e
    have h := hz e
    unfold Slack.slack at h
    omega
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_, ?_⟩
    · intro e
      have h := hz e
      have hnonneg := hy e
      omega
    · intro e
      unfold Slack.slack
      have h := hz e
      omega

/-- A connected nonbipartite graph supplies the parity row itself. Only the
separate kernel-spanning construction for the specified `B,W` remains a premise. -/
theorem exists_integer_slack_criterion (left right : E → V)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (B : Matrix R E ℚ) (W : Matrix S E ℚ)
    (hspan : Submodule.span ℚ (Set.range B ∪ Set.range W) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) :
    ∃ π : E → ℤ, (∑ e, π e) = 1 ∧
      ∀ y : E → ℤ,
        (∃ z : V → ℤ, ∀ e, z (left e) + z (right e) = 1 - y e) ↔
          B *ᵥ (fun e => (y e : ℚ)) = 0 ∧
          W *ᵥ (fun e => (y e : ℚ)) = 0 ∧
          ∃ t : ℤ, ∑ e, π e * y e = 2 * t + 1 := by
  obtain ⟨root, π, hs, hp⟩ := OddRow.exists_odd_row_of_nonbipartite left right hc hnb
  exact ⟨π, hs, fun y => integer_slack_criterion left right root hc B W hspan π hp y⟩

end WeightedMIS.IntegerSlacks
