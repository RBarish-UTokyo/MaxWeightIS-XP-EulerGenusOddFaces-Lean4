module

public import WeightedMIS.RegisterTopLevelRun
public import WeightedMIS.HardSolveBudget
public import WeightedMIS.FinalCost

/-!
# Accounting of the hard components

The hard-component contract `RegisterComponentSolve.HardSpec` constrains the
budget only on connected nonbipartite instances: the component procedure calls
the hard solver only on those. Hence the budget function may be chosen to
vanish on bipartite instances. `sharpBudget W w0` is the budget
`RegisterHardSolve.hardBudget W w0` on nonbipartite instances and `0` on
bipartite ones; the compiled hard solver satisfies the contract for it
(`hardSpec_sharp`).

With this budget, a component contributes only when it is nonbipartite, and
then its number `d` of global kernel rows is bounded by the parameter exponent
(`Spec.Drawing.solve_spec`). Summed over the at most `N` components, the hard
budgets are at most `hardFactor p · N ^ (Dx + 43) · (L + 1) ^ 42`, where
`Dx ≤ p` bounds `d` on every nonbipartite component and
`hardFactor p = 2 ^ 230 · 5 ^ p · (p + 6) ^ 42`. Together with the
polynomial part of the entry budget, the whole event budget is at most
`topFactor p · N ^ (Dx + 43) · (L + 1) ^ 42`, and the logarithmic overhead of
the bit-stack simulation (`FinalCost.overhead_le`) yields the final cost
bound `finalCoefficient p · N ^ (Dx + 44) · (L + 1) ^ 43` with the computable
coefficient `finalCoefficient p = FinalCost.finalFactor (topFactor p) p 43 42`.
-/

@[expose] public section

namespace WeightedMIS.FinalAccounting

open WeightedMIS.Spec WeightedMIS.SpecEncoding WeightedMIS.EmbeddingFaces
open WeightedMIS.RegisterComponentSolve (HardBudget HardSpec componentHardBudget)
open WeightedMIS.RegisterHardSolve (hardBudget)

/-! ## The budget charged only on nonbipartite instances -/

open Classical in
/-- The hard budget on nonbipartite instances, `0` on bipartite ones. -/
noncomputable def sharpBudget (W w0 : ℕ) : HardBudget :=
  fun {_n _m} {left right} R w => if Incidence.Bipartite left right then 0 else hardBudget W w0 R w

/-- The compiled hard solver satisfies the hard contract for `sharpBudget`. -/
theorem hardSpec_sharp {p : ℕ} {code : RegisterMachine.Code p} {hard : Fin p} {W w0 : ℕ}
    (h : HardSpec code hard W (RegisterWeightMask.CanonAt w0) (hardBudget W w0)) :
    HardSpec code hard W (RegisterWeightMask.CanonAt w0) (sharpBudget W w0) := by
  intro n m left right R w hn0 hn hmW hc hnb hw ho h' hh tp rp wp hT hr hwp
  unfold sharpBudget
  beta_reduce
  simp only [hnb, ↓reduceIte]
  exact h R w hn0 hn hmW hc hnb hw ho hh hT hr hwp

/-! ## Per-component and summed bounds -/

/-- The charged budget of one component, when every nonbipartite component has
at most `Dx` global rows. -/
theorem componentHardBudget_le (W w0 : ℕ) {n m : ℕ} {left right : Fin m → Fin n}
    (H : Ribbon left right) (w : Fin n → ℚ) {Dx : ℕ} (root : Fin n)
    (hd : ¬ Incidence.Bipartite (ComputedComponents.localLeft left right root)
        (ComputedComponents.localRight left right root) →
      (ComputedEmbeddedMatrices.globalRows
        (ComputedComponents.componentRibbon left right root H)).length ≤ Dx) :
    componentHardBudget (sharpBudget W w0) H w root ≤
      2 ^ 230 * (4 * m + 1) ^ Dx * (n + m + W + w0 + Dx + 2) ^ 42 := by
  unfold componentHardBudget sharpBudget
  beta_reduce
  split_ifs with hb
  · exact Nat.zero_le _
  · refine (HardSolveBudget.hardBudget_le W w0 _ _).trans ?_
    have h1 := hd hb
    have hv := ComputedComponents.vertices_length_le left right root
    have he := ComputedComponents.edges_length_le left right root
    have a : (4 * (ComputedComponents.edges left right root).length + 1) ^
        (ComputedEmbeddedMatrices.globalRows
          (ComputedComponents.componentRibbon left right root H)).length ≤
        (4 * m + 1) ^ Dx :=
      (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) h1)
    have b : ((ComputedComponents.vertices left right root).length +
        (ComputedComponents.edges left right root).length + W + w0 +
        (ComputedEmbeddedMatrices.globalRows
          (ComputedComponents.componentRibbon left right root H)).length + 2) ^ 42 ≤
        (n + m + W + w0 + Dx + 2) ^ 42 :=
      Nat.pow_le_pow_left (by omega) _
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ a) b

/-- The summed charged budget over all computed components. -/
theorem hardSum_le (W w0 : ℕ) {n m : ℕ} {left right : Fin m → Fin n}
    (H : Ribbon left right) (w : Fin n → ℚ) {Dx : ℕ}
    (hd : ∀ root : Fin n, ¬ Incidence.Bipartite (ComputedComponents.localLeft left right root)
        (ComputedComponents.localRight left right root) →
      (ComputedEmbeddedMatrices.globalRows
        (ComputedComponents.componentRibbon left right root H)).length ≤ Dx) :
    RegisterAllHalf.hardSum (sharpBudget W w0) H w ≤
      n * (2 ^ 230 * (4 * m + 1) ^ Dx * (n + m + W + w0 + Dx + 2) ^ 42) := by
  unfold RegisterAllHalf.hardSum
  refine FinalBudget.list_sum_le _ ?_ ?_
  · rw [List.length_map]; exact ComputedComponents.roots_length_le left right
  · intro x hx
    obtain ⟨root, -, rfl⟩ := List.mem_map.mp hx
    exact componentHardBudget_le W w0 H w root (hd root)

/-! ## Arithmetic normal form -/

/-- Coefficient of the summed hard budgets. -/
def hardFactor (p : ℕ) : ℕ := 2 ^ 230 * 5 ^ p * (p + 6) ^ 42

/-- Coefficient of the whole event budget. -/
def topFactor (p : ℕ) : ℕ := 2 ^ 36 + hardFactor p

theorem hard_shape {n m W w0 Dx p N L : ℕ} (hN : 1 ≤ N) (hn : n ≤ N) (hm : m ≤ N)
    (hW : W ≤ N) (hw0 : w0 ≤ L) (hD : Dx ≤ p) :
    n * (2 ^ 230 * (4 * m + 1) ^ Dx * (n + m + W + w0 + Dx + 2) ^ 42) ≤
      hardFactor p * N ^ (Dx + 43) * (L + 1) ^ 42 := by
  have a : (4 * m + 1) ^ Dx ≤ 5 ^ p * N ^ Dx := by
    calc (4 * m + 1) ^ Dx ≤ (5 * N) ^ Dx := Nat.pow_le_pow_left (by omega) _
      _ = 5 ^ Dx * N ^ Dx := Nat.mul_pow _ _ _
      _ ≤ 5 ^ p * N ^ Dx := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hD)
  set X := N * (L + 1) with hXdef
  have hX1 : N ≤ X := Nat.le_mul_of_pos_right _ (by omega)
  have hX2 : L + 1 ≤ X := by
    rw [hXdef]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hpX : p ≤ p * X := Nat.le_mul_of_pos_right _ (by omega)
  have hlin : n + m + W + w0 + Dx + 2 ≤ (p + 6) * X := by
    have e : (p + 6) * X = p * X + 6 * X := by ring
    omega
  have b : (n + m + W + w0 + Dx + 2) ^ 42 ≤ (p + 6) ^ 42 * N ^ 42 * (L + 1) ^ 42 := by
    calc (n + m + W + w0 + Dx + 2) ^ 42 ≤ ((p + 6) * X) ^ 42 := Nat.pow_le_pow_left hlin _
      _ = (p + 6) ^ 42 * N ^ 42 * (L + 1) ^ 42 := by
        rw [hXdef, Nat.mul_pow, Nat.mul_pow, Nat.mul_assoc]
  calc n * (2 ^ 230 * (4 * m + 1) ^ Dx * (n + m + W + w0 + Dx + 2) ^ 42)
      ≤ N * (2 ^ 230 * (5 ^ p * N ^ Dx) * ((p + 6) ^ 42 * N ^ 42 * (L + 1) ^ 42)) :=
        Nat.mul_le_mul hn (Nat.mul_le_mul (Nat.mul_le_mul_left _ a) b)
    _ = hardFactor p * N ^ (Dx + 43) * (L + 1) ^ 42 := by
      unfold hardFactor
      generalize (p + 6) ^ 42 = Q
      generalize (L + 1) ^ 42 = M
      generalize (5 : ℕ) ^ p = F
      generalize (2 : ℕ) ^ 230 = K
      ring

/-! ## The event budget of the entry procedure -/

/-- The event budget with the sharp hard budget, when every nonbipartite
residual component has at most `Dx ≤ p` global rows. -/
theorem budget_le (D : Drawing) (w : Fin D.vertices → ℚ) (R : Ribbon D.left D.right)
    {Dx p : ℕ} (hD : Dx ≤ p)
    (hd : ∀ root : Fin (ComputedInduced.vertices
          (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)).length,
        ¬ Incidence.Bipartite
          (ComputedComponents.localLeft (ComputedInduced.localLeft D.left D.right
              (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w))
            (ComputedInduced.localRight D.left D.right
              (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)) root)
          (ComputedComponents.localRight (ComputedInduced.localLeft D.left D.right
              (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w))
            (ComputedInduced.localRight D.left D.right
              (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)) root) →
        (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
          (ComputedInduced.localLeft D.left D.right
            (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w))
          (ComputedInduced.localRight D.left D.right
            (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)) root
          (ComputedInduced.ribbon D.left D.right
            (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w) R))).length ≤
          Dx) :
    RegisterTopLevel.inputBudget D w +
        RegisterFinalAssembly.residualHardSum (sharpBudget (indexWidth D) (weightWidth w)) R w ≤
      topFactor p * D.size ^ (Dx + 43) * (weightLength w + 1) ^ 42 := by
  have hN : 1 ≤ D.size := by simp [Drawing.size]
  have hs := hardSum_le (indexWidth D) (weightWidth w)
    (ComputedInduced.ribbon D.left D.right
      (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w) R)
    (RegisterFinalAssembly.halfWeights D.left D.right w) hd
  have hvl : (ComputedInduced.vertices
      (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)).length ≤
      D.vertices := by
    simpa [ComputedInduced.vertices] using List.length_filter_le _ (List.finRange D.vertices)
  have hel : (ComputedInduced.edges D.left D.right
      (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)).length ≤
      D.edges := by
    simpa [ComputedInduced.edges] using List.length_filter_le _ (List.finRange D.edges)
  have hW := indexWidth_le D
  have hw0 := weightWidth_le w
  have hh := hard_shape (N := D.size) (L := weightLength w) hN
    (hvl.trans (by simp [Drawing.size]; omega)) (hel.trans (by simp [Drawing.size]; omega))
    (hW.trans (by simp [Drawing.size])) hw0 hD
  have hr : RegisterFinalAssembly.residualHardSum (sharpBudget (indexWidth D) (weightWidth w)) R w ≤
      hardFactor p * D.size ^ (Dx + 43) * (weightLength w + 1) ^ 42 :=
    hs.trans hh
  have hi := RegisterTopLevel.inputBudget_le D w
  have hi' : 2 ^ 36 * D.size ^ 11 * (weightLength w + 1) ^ 2 ≤
      2 ^ 36 * D.size ^ (Dx + 43) * (weightLength w + 1) ^ 42 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN (by omega)))
      (Nat.pow_le_pow_right (by omega) (by omega))
  have e : topFactor p * D.size ^ (Dx + 43) * (weightLength w + 1) ^ 42 =
      2 ^ 36 * D.size ^ (Dx + 43) * (weightLength w + 1) ^ 42 +
        hardFactor p * D.size ^ (Dx + 43) * (weightLength w + 1) ^ 42 := by
    unfold topFactor; ring
  omega

/-! ## The final coefficient -/

/-- The final cost coefficient as a function of the parameter `p = γ + k`. -/
def finalCoefficient (p : ℕ) : ℕ := FinalCost.finalFactor (topFactor p) p 43 42

theorem primrec_topFactor : Primrec topFactor := by
  unfold topFactor hardFactor
  have h5 : Primrec fun p : ℕ => 5 ^ p := FinalCost.primrec_pow.comp (Primrec.const 5) Primrec.id
  have h6 : Primrec fun p : ℕ => (p + 6) ^ 42 :=
    FinalCost.primrec_pow.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 6))
      (Primrec.const 42)
  exact Primrec.nat_add.comp (Primrec.const _)
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const _) h5) h6)

theorem computable_finalCoefficient : Computable finalCoefficient :=
  FinalCost.computable_finalFunction primrec_topFactor 43 42

/-- The bit-stack cost bound of `RegisterTopLevel.top_runs` with the sharp hard
budget, in normal form. -/
theorem cost_le (D : Drawing) (w : Fin D.vertices → ℚ) (R : Ribbon D.left D.right)
    {Dx p : ℕ} (hD : Dx ≤ p)
    (hd : ∀ root : Fin (ComputedInduced.vertices
          (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)).length,
        ¬ Incidence.Bipartite
          (ComputedComponents.localLeft (ComputedInduced.localLeft D.left D.right
              (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w))
            (ComputedInduced.localRight D.left D.right
              (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)) root)
          (ComputedComponents.localRight (ComputedInduced.localLeft D.left D.right
              (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w))
            (ComputedInduced.localRight D.left D.right
              (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)) root) →
        (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
          (ComputedInduced.localLeft D.left D.right
            (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w))
          (ComputedInduced.localRight D.left D.right
            (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)) root
          (ComputedInduced.ribbon D.left D.right
            (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w) R))).length ≤
          Dx) :
    (RegisterTopLevel.inputBudget D w +
        RegisterFinalAssembly.residualHardSum (sharpBudget (indexWidth D) (weightWidth w)) R w) *
      (102 + 35 * ((encode D w).1.length + (RegisterTopLevel.inputBudget D w +
        RegisterFinalAssembly.residualHardSum (sharpBudget (indexWidth D) (weightWidth w)) R w)).size) ≤
      finalCoefficient p * D.size ^ (Dx + 44) * (weightLength w + 1) ^ 43 :=
  FinalCost.overhead_le (C := 43) (b := 42) (by simp [Drawing.size]) hD (by norm_num)
    (by norm_num) (budget_le D w R hD hd) (encode_length_le D w)

end WeightedMIS.FinalAccounting
