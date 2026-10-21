module

public import WeightedMIS.FinalBudget
public import WeightedMIS.RuntimeAbsorption
public import Mathlib.Computability.Partrec

/-!
# From an event budget to the bit-stack cost

An event bound `T ≤ F N^(D+C) (L+1)^b` with a parameter exponent `D ≤ q` and
an input heap of at most `100 N^2 (L+1)` cells yields a bound
`finalFactor F q C b * N^(D+(C+1)) * (L+1)^(b+1)` on the cost of the concrete
bit-stack simulation of any framed execution. The coefficient is an explicit
closed form; the bit length of `F` appearing in the address-width estimate is
replaced by `F` itself. When `F` is a primitive recursive function of the
parameter, so is the final coefficient, hence it is computable.
-/

@[expose] public section

namespace WeightedMIS.FinalCost

open WeightedMIS.RegisterMachine WeightedMIS.PointerMemory WeightedMIS.FinalBudget

/-- Closed-form coefficient after the logarithmic simulation overhead. -/
def finalFactor (F q C b : ℕ) : ℕ := (F + 100) * (102 + 35 * (F + 100 + q + C + b + 4))

theorem finalFactor_mono {F F' q q' C b : ℕ} (hF : F ≤ F') (hq : q ≤ q') :
    finalFactor F q C b ≤ finalFactor F' q' C b := by
  unfold finalFactor
  exact Nat.mul_le_mul (by omega) (by omega)

/-- Pure arithmetic form of the assembly: events and input size in normal form
give the logarithmic-overhead product in normal form. -/
theorem overhead_le {F N L D C b q input events : ℕ} (hN : 1 ≤ N) (hD : D ≤ q)
    (hC : 2 ≤ C) (hb : 1 ≤ b) (hT : events ≤ F * N ^ (D + C) * (L + 1) ^ b)
    (hH : input ≤ 100 * N ^ 2 * (L + 1)) :
    events * (102 + 35 * (input + events).size) ≤
      finalFactor F q C b * N ^ (D + (C + 1)) * (L + 1) ^ (b + 1) := by
  have hi : input ≤ (F + 100) * N ^ (D + C) * (L + 1) ^ b := by
    refine hH.trans ?_
    have := shape_mono (c := 100) (a := 2) (b := 1) (c' := F + 100) (a' := D + C) (b' := b)
      (L := L) hN (by omega) (by omega) hb
    simpa [Shape] using this
  have he : events ≤ (F + 100) * N ^ (D + C) * (L + 1) ^ b := by
    refine hT.trans ?_
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  refine (RuntimeAbsorption.logarithmic_overhead (F + 100) N L D C b q input events
    hN hD hi he).trans ?_
  refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
  unfold finalFactor
  have := size_le_self (F + 100)
  exact Nat.mul_le_mul_left _ (by omega)

/-- The bit-stack cost of a framed execution, from an event bound and an input
heap bound. -/
theorem stackBitCost_le {P : ℕ} {code : Code P} {h : Heap} {regs : Registers}
    {command : Command P} {result : Run (List Value)} {tree : CallTree}
    (he : FramedExec code h regs command result tree) (hh : Valid h)
    (hr : RegistersBound h.length regs)
    {F N L D C b q : ℕ} (hN : 1 ≤ N) (hD : D ≤ q) (hC : 2 ≤ C) (hb : 1 ≤ b)
    (hT : result.trace.length ≤ F * N ^ (D + C) * (L + 1) ^ b)
    (hH : h.length ≤ 100 * N ^ 2 * (L + 1)) :
    stackBitCost tree.compile ≤
      finalFactor F q C b * N ^ (D + (C + 1)) * (L + 1) ^ (b + 1) :=
  (he.bitCost_le hh hr).trans (overhead_le hN hD hC hb hT hH)

/-- The same assembly from any event bound `steps ≥ trace length`. -/
theorem stackBitCost_le_of_steps {P : ℕ} {code : Code P} {h : Heap} {regs : Registers}
    {command : Command P} {result : Run (List Value)} {tree : CallTree} {steps : ℕ}
    (he : FramedExec code h regs command result tree) (hh : Valid h)
    (hr : RegistersBound h.length regs) (hlen : result.trace.length ≤ steps)
    {F N L D C b q : ℕ} (hN : 1 ≤ N) (hD : D ≤ q) (hC : 2 ≤ C) (hb : 1 ≤ b)
    (hT : steps ≤ F * N ^ (D + C) * (L + 1) ^ b)
    (hH : h.length ≤ 100 * N ^ 2 * (L + 1)) :
    stackBitCost tree.compile ≤
      finalFactor F q C b * N ^ (D + (C + 1)) * (L + 1) ^ (b + 1) :=
  (he.bitCost_le_of_length_le hh hr hlen).trans (overhead_le hN hD hC hb hT hH)

/-- General exponent `D = exponentD γ k`, parameter `γ + k`. -/
theorem stackBitCost_le_exponentD {P : ℕ} {code : Code P} {h : Heap} {regs : Registers}
    {command : Command P} {result : Run (List Value)} {tree : CallTree}
    (he : FramedExec code h regs command result tree) (hh : Valid h)
    (hr : RegistersBound h.length regs)
    {F N L C b γ k : ℕ} (hN : 1 ≤ N) (hC : 2 ≤ C) (hb : 1 ≤ b)
    (hT : result.trace.length ≤ F * N ^ (Spec.exponentD γ k + C) * (L + 1) ^ b)
    (hH : h.length ≤ 100 * N ^ 2 * (L + 1)) :
    stackBitCost tree.compile ≤
      finalFactor F (γ + k) C b * N ^ (Spec.exponentD γ k + (C + 1)) * (L + 1) ^ (b + 1) :=
  stackBitCost_le he hh hr hN (exponentD_le γ k) hC hb hT hH

/-- Orientable exponent `D' = orientableExponentD γ k`, parameter `γ + k`. -/
theorem stackBitCost_le_orientableExponentD {P : ℕ} {code : Code P} {h : Heap}
    {regs : Registers} {command : Command P} {result : Run (List Value)} {tree : CallTree}
    (he : FramedExec code h regs command result tree) (hh : Valid h)
    (hr : RegistersBound h.length regs)
    {F N L C b γ k : ℕ} (hN : 1 ≤ N) (hC : 2 ≤ C) (hb : 1 ≤ b)
    (hT : result.trace.length ≤ F * N ^ (Spec.orientableExponentD γ k + C) * (L + 1) ^ b)
    (hH : h.length ≤ 100 * N ^ 2 * (L + 1)) :
    stackBitCost tree.compile ≤
      finalFactor F (γ + k) C b *
        N ^ (Spec.orientableExponentD γ k + (C + 1)) * (L + 1) ^ (b + 1) :=
  stackBitCost_le he hh hr hN (orientableExponentD_le γ k) hC hb hT hH

/-! ## Computability of the coefficient -/

theorem primrec_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- The final coefficient as a function of the parameter. -/
def finalFunction (F : ℕ → ℕ) (C b : ℕ) (q : ℕ) : ℕ := finalFactor (F q) q C b

theorem primrec_finalFunction {F : ℕ → ℕ} (hF : Primrec F) (C b : ℕ) :
    Primrec (finalFunction F C b) := by
  unfold finalFunction finalFactor
  have hF100 : Primrec fun q => F q + 100 := Primrec.nat_add.comp hF (Primrec.const 100)
  have hsum : Primrec fun q => F q + 100 + q + C + b + 4 :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp hF100 Primrec.id) (Primrec.const C)) (Primrec.const b))
      (Primrec.const 4)
  exact Primrec.nat_mul.comp hF100 (Primrec.nat_add.comp (Primrec.const 102)
    (Primrec.nat_mul.comp (Primrec.const 35) hsum))

theorem computable_finalFunction {F : ℕ → ℕ} (hF : Primrec F) (C b : ℕ) :
    Computable (finalFunction F C b) :=
  (primrec_finalFunction hF C b).to_comp

theorem primrec_stageFactor (K a : ℕ) : Primrec (stageFactor K a) := by
  unfold stageFactor
  exact primrec_pow.comp (Primrec.const _) Primrec.succ

/-- A sum of primitive recursive coefficients is primitive recursive. -/
theorem primrec_add {F G : ℕ → ℕ} (hF : Primrec F) (hG : Primrec G) :
    Primrec fun q => F q + G q :=
  Primrec.nat_add.comp hF hG

theorem primrec_mul {F G : ℕ → ℕ} (hF : Primrec F) (hG : Primrec G) :
    Primrec fun q => F q * G q :=
  Primrec.nat_mul.comp hF hG

/-- The coefficient of the whole run when the event bound is a constant
multiple of a per-component stage factor. -/
theorem computable_stage_final (K a e C b : ℕ) :
    Computable (finalFunction (fun q => e * stageFactor K a q) C b) :=
  computable_finalFunction (primrec_mul (Primrec.const e) (primrec_stageFactor K a)) C b

end WeightedMIS.FinalCost
