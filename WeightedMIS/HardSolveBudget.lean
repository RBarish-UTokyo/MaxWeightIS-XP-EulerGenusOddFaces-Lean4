module

public import WeightedMIS.RegisterHardSolve

/-!
# Polynomial bound of the hard-component budget

With `X = n + m + W + w0 + d + 2`, where `d` is the number of global kernel
rows, the budget of the compiled hard-component solver satisfies

  `hardTotal W w0 n m d ≤ 2 ^ 230 * (4 m + 1) ^ d * X ^ 42`.

The proof bounds every working width by `Z = X + ratWidth n m + G`
(`G` the search width), every stage budget by a constant times `Z ^ 7`
(times `(4 m + 1) ^ d` for the search), and finally `Z ≤ 2 ^ 21 * X ^ 6`.
The search width itself satisfies `G ≤ 2 ^ 17 * X ^ 3`, in particular
`G ≤ 2 ^ 17 * (d + 1) * (n + m + W + w0 + 2) ^ 2`.
-/

@[expose] public section

namespace WeightedMIS.HardSolveBudget

open WeightedMIS.HardWidths WeightedMIS.RegisterHardInputs WeightedMIS.RegisterHardSolve

/-! ## Elementary bounds -/

theorem pow_up {Z k : ℕ} (hZ : 1 ≤ Z) (hk : k ≤ 7) : Z ^ k ≤ Z ^ 7 :=
  Nat.pow_le_pow_right hZ hk

theorem up {Z k K a : ℕ} (hZ : 1 ≤ Z) (hk : k ≤ 7) (h : a ≤ K * Z ^ k) : a ≤ K * Z ^ 7 :=
  h.trans (Nat.mul_le_mul_left K (pow_up hZ hk))

/-- The domination hypotheses of all parameters by one number `Z`. -/
structure Dom (Z W n m d c N G : ℕ) : Prop where
  one : 1 ≤ Z
  W : W ≤ Z
  n : n ≤ Z
  m : m ≤ Z
  d : d ≤ Z
  c : c ≤ Z
  N : N ≤ Z
  G : G ≤ Z

theorem dblBudget_le : dblBudget ≤ 2 ^ 18 := by
  simp [dblBudget, doublesBudget, RegisterWiden.widenBudget]

theorem padBudget_le {Z w L : ℕ} (hZ : 1 ≤ Z) (hw : w ≤ Z) (hL : L ≤ 2 * Z) :
    RegisterWiden.padBudget w L ≤ 200 * Z ^ 7 := by
  refine up hZ (k := 2) (by norm_num) ?_
  unfold RegisterWiden.padBudget RegisterWiden.widenBudget
  have h1 : (26 * w + 13 + 32) * L ≤ (71 * Z) * (2 * Z) := Nat.mul_le_mul (by omega) hL
  have h2 : (71 * Z) * (2 * Z) = 142 * Z ^ 2 := by ring
  have h3 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

theorem widenBudget_le {Z w : ℕ} (hZ : 1 ≤ Z) (hw : w ≤ Z) :
    RegisterWiden.widenBudget w ≤ 39 * Z ^ 7 := by
  refine up hZ (k := 1) (by norm_num) ?_
  unfold RegisterWiden.widenBudget
  simp only [pow_one]; omega

/-! ## The kernel stage -/

theorem kernel_le {Z W n m d c G : ℕ} (D : Dom Z W n m d c (ratWidth n m) G) :
    RegisterHardKernel.kernelBudget W n m ≤ 2 ^ 31 * Z ^ 7 := by
  obtain ⟨hZ, hW, hn, hm, hd, hc, hN, hG⟩ := D
  have h7 : 1 ≤ Z ^ 7 := Nat.one_le_pow _ _ hZ
  have hcore : ratCore n m ≤ Z := by unfold ratWidth at hN; omega
  have k1 : ratConstsBudget n m ≤ 2 ^ 19 * Z ^ 7 := by
    have p1 := padBudget_le hZ hcore (L := m + 1) (by omega)
    have p2 := padBudget_le hZ hcore (L := n + 1) (by omega)
    have p3 := widenBudget_le hZ hcore
    have := dblBudget_le
    unfold ratConstsBudget
    omega
  have k2 : FaceStageProgram.stageBudget W (ratWidth n m) (ratWidth n m) m ≤ 2 ^ 25 * Z ^ 7 := by
    refine (FaceStageProgram.stageBudget_le _ _ _ _).trans (up hZ (k := 4) (by norm_num) ?_)
    calc 2 ^ 20 * (W + ratWidth n m + ratWidth n m + 1) * (m + 1) ^ 3
        ≤ 2 ^ 20 * (4 * Z) * (2 * Z) ^ 3 := by gcongr <;> omega
      _ = 2 ^ 25 * Z ^ 4 := by ring
  have k3 : (RegisterSignedRows.rowBudget m + 35) * (4 * m) + 13 ≤ 2 ^ 9 * Z ^ 7 := by
    refine up hZ (k := 2) (by norm_num) ?_
    unfold RegisterSignedRows.rowBudget
    have : (46 * m + 13 + 35) * (4 * m) ≤ (94 * Z) * (4 * Z) := by gcongr; omega
    have h2 : (94 * Z) * (4 * Z) = 376 * Z ^ 2 := by ring
    have h3 : 1 ≤ Z ^ 2 := Nat.one_le_pow _ _ hZ
    omega
  have k4 : RegisterKernelGenerators.budget W (ratWidth n m) n m ≤ 2 ^ 30 * Z ^ 7 := by
    refine (RegisterKernelGenerators.budget_le _ _ _ _).trans (up hZ (k := 6) (by norm_num) ?_)
    calc 40000 * (W + ratWidth n m + n + m + 1) ^ 6 ≤ 40000 * (5 * Z) ^ 6 := by gcongr; omega
      _ ≤ 2 ^ 30 * Z ^ 6 := by ring_nf; omega
  have k5 : RegisterCandidates.budget W (ratWidth n m) m ≤ 2 ^ 27 * Z ^ 7 := by
    refine (RegisterCandidates.budget_le _ _ _).trans (up hZ (k := 6) (by norm_num) ?_)
    calc 20000 * (W + ratWidth n m + m + 1) ^ 6 ≤ 20000 * (4 * Z) ^ 6 := by gcongr; omega
      _ ≤ 2 ^ 27 * Z ^ 6 := by ring_nf; omega
  have k6 : (RegisterSignedRows.rowBudget m + 35) * (m * m) + 13 ≤ 2 ^ 7 * Z ^ 7 := by
    refine up hZ (k := 3) (by norm_num) ?_
    unfold RegisterSignedRows.rowBudget
    have : (46 * m + 13 + 35) * (m * m) ≤ (94 * Z) * (Z * Z) := by gcongr; omega
    have h2 : (94 * Z) * (Z * Z) = 94 * Z ^ 3 := by ring
    have h3 : 1 ≤ Z ^ 3 := Nat.one_le_pow _ _ hZ
    omega
  have k7 : RegisterComplementSelect.stageBudget (ratWidth n m) m (4 * m) (m * m) ≤
      2 ^ 29 * Z ^ 7 := by
    refine (RegisterComplementSelect.stageBudget_le _ _).trans ?_
    calc 200000 * (ratWidth n m + m + 1) ^ 7 ≤ 200000 * (3 * Z) ^ 7 := by gcongr; omega
      _ ≤ 2 ^ 29 * Z ^ 7 := by ring_nf; omega
  unfold RegisterHardKernel.kernelBudget
  omega

/-! ## The stages after the kernel -/

theorem searchConsts_le {Z W n m d c N : ℕ} (D : Dom Z W n m d c N (searchWidth c n m d)) :
    searchConstsBudget c n m d ≤ 2 ^ 22 * Z ^ 7 := by
  obtain ⟨hZ, hW, hn, hm, hd, hc, hN, hG⟩ := D
  have h7 : 1 ≤ Z ^ 7 := Nat.one_le_pow _ _ hZ
  have hcore : searchCore c n m d ≤ Z := by unfold searchWidth at hG; omega
  have hshape : shapeWidth c n m ≤ Z := by
    have : shapeWidth c n m ≤ searchCore c n m d := by
      unfold searchCore padW; nlinarith
    omega
  have hpm : padW baseWidth m ≤ Z := by unfold shapeWidth at hshape; omega
  have hpn : padW baseWidth n ≤ Z := by unfold shapeWidth at hshape; omega
  have hb : baseWidth ≤ Z := by unfold shapeWidth at hshape; omega
  have p1 := padBudget_le hZ hb (L := m) (by omega)
  have p2 := padBudget_le hZ hb (L := n) (by omega)
  have p3 := padBudget_le hZ hshape (L := d + 1) (by omega)
  have q1 := widenBudget_le hZ hc
  have q2 := widenBudget_le hZ hpm
  have q3 := widenBudget_le hZ hpn
  have q4 := widenBudget_le hZ hcore
  have := dblBudget_le
  unfold searchConstsBudget
  omega

theorem stage2_le {Z W n m d c N : ℕ} (D : Dom Z W n m d c N (searchWidth c n m d)) :
    stage2Budget W c N n m d ≤ 2 ^ 62 * (4 * m + 1) ^ d * Z ^ 7 := by
  have k1 := searchConsts_le D
  obtain ⟨hZ, hW, hn, hm, hd, hc, hN, hG⟩ := D
  set G := searchWidth c n m d with hGdef
  have h7 : 1 ≤ Z ^ 7 := Nat.one_le_pow _ _ hZ
  have k2 : RegisterTranspose.stageBudget N G d m ≤ 2 ^ 16 * Z ^ 7 := by
    refine (RegisterTranspose.stageBudget_le _ _ _ _).trans (up hZ (k := 3) (by norm_num) ?_)
    calc 400 * (N + G + d + m + 1) ^ 3 ≤ 400 * (5 * Z) ^ 3 := by gcongr; omega
      _ ≤ 2 ^ 16 * Z ^ 3 := by ring_nf; omega
  have k3 : FaceStageProgram.stageBudget W G G m ≤ 2 ^ 25 * Z ^ 7 := by
    refine (FaceStageProgram.stageBudget_le _ _ _ _).trans (up hZ (k := 4) (by norm_num) ?_)
    calc 2 ^ 20 * (W + G + G + 1) * (m + 1) ^ 3 ≤ 2 ^ 20 * (4 * Z) * (2 * Z) ^ 3 := by
          gcongr <;> omega
      _ = 2 ^ 25 * Z ^ 4 := by ring
  have k4 : 28 * G + 15 ≤ 43 * Z ^ 7 := by
    have := pow_up hZ (k := 1) (by norm_num); simp only [pow_one] at this; omega
  have k5 : (RegisterResize.resizeBudget G c + 35) * m + 13 ≤ 2 ^ 8 * Z ^ 7 := by
    refine up hZ (k := 2) (by norm_num) ?_
    unfold RegisterResize.resizeBudget
    have : (60 * G + 30 * c + 60 + 35) * m ≤ (185 * Z) * Z := by gcongr; omega
    have h2 : (185 * Z) * Z = 185 * Z ^ 2 := by ring
    have h3 : 1 ≤ Z ^ 2 := Nat.one_le_pow _ _ hZ
    omega
  have k6 : RegisterOddRow.budget W W G n m ≤ 2 ^ 25 * Z ^ 7 := by
    refine (RegisterOddRow.budget_le _ _ _ _ _).trans ?_
    calc 100000 * (W + W + G + 1) * (m + 1) ^ 2 * (n + 1) ^ 4
        ≤ 100000 * (4 * Z) * (2 * Z) ^ 2 * (2 * Z) ^ 4 := by gcongr <;> omega
      _ ≤ 2 ^ 25 * Z ^ 7 := by ring_nf; omega
  have k7 : 2 ^ 40 * (4 * m + 1) ^ d * (5 * m + d + G + 2) ^ 6 ≤
      2 ^ 60 * (4 * m + 1) ^ d * Z ^ 7 := by
    calc 2 ^ 40 * (4 * m + 1) ^ d * (5 * m + d + G + 2) ^ 6
        ≤ 2 ^ 40 * (4 * m + 1) ^ d * (9 * Z) ^ 6 := by gcongr; omega
      _ = 2 ^ 40 * 9 ^ 6 * ((4 * m + 1) ^ d * Z ^ 6) := by ring
      _ ≤ 2 ^ 60 * ((4 * m + 1) ^ d * Z ^ 7) :=
          Nat.mul_le_mul (by norm_num) (Nat.mul_le_mul_left _ (pow_up hZ (k := 6) (by norm_num)))
      _ = 2 ^ 60 * (4 * m + 1) ^ d * Z ^ 7 := by ring
  have k8 : RegisterHardRecovery.budget W G n m ≤ 2 ^ 22 * Z ^ 7 := by
    refine (RegisterHardRecovery.budget_le _ _ _ _).trans ?_
    calc 6000 * (W + G + 1) ^ 2 * (m + 1) * (n + 1) ^ 4
        ≤ 6000 * (3 * Z) ^ 2 * (2 * Z) * (2 * Z) ^ 4 := by gcongr <;> omega
      _ ≤ 2 ^ 22 * Z ^ 7 := by ring_nf; omega
  have hp : 1 ≤ (4 * m + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hP : Z ^ 7 ≤ (4 * m + 1) ^ d * Z ^ 7 := Nat.le_mul_of_pos_left _ hp
  have e : 2 ^ 60 * (4 * m + 1) ^ d * Z ^ 7 = 2 ^ 60 * ((4 * m + 1) ^ d * Z ^ 7) := by ring
  have e2 : 2 ^ 62 * (4 * m + 1) ^ d * Z ^ 7 = 2 ^ 62 * ((4 * m + 1) ^ d * Z ^ 7) := by ring
  unfold stage2Budget
  rw [← hGdef]
  rw [e] at k7
  rw [e2]
  omega

/-! ## The whole solver -/

theorem width_le_sq (w0 n : ℕ) : NetworkWeights.width w0 n ≤ 2 * (n + w0 + 2) ^ 2 := by
  unfold NetworkWeights.width; nlinarith

/-- The search width is linear in `d + 1` and quadratic in the instance size. -/
theorem searchWidth_le' (W w0 n m d : ℕ) :
    searchWidth (NetworkWeights.width w0 n) n m d ≤
      2 ^ 17 * (d + 1) * (n + m + W + w0 + 2) ^ 2 := by
  have h1 := searchWidth_le (NetworkWeights.width w0 n) n m d
  have h2 := width_le_sq w0 n
  set Y := n + m + W + w0 + 2
  have hY : n + w0 + 2 ≤ Y := by omega
  have h3 : (n + w0 + 2) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hY 2
  have h4 : n + m + 1 ≤ Y ^ 2 := le_trans (by omega) (Nat.le_self_pow (by norm_num) Y)
  have h5 : NetworkWeights.width w0 n + n + m + 1 ≤ 3 * Y ^ 2 := by omega
  calc searchWidth (NetworkWeights.width w0 n) n m d
      ≤ 2 ^ 15 * (d + 1) * (NetworkWeights.width w0 n + n + m + 1) := h1
    _ ≤ 2 ^ 15 * (d + 1) * (3 * Y ^ 2) := Nat.mul_le_mul_left _ h5
    _ ≤ 2 ^ 17 * (d + 1) * Y ^ 2 := by ring_nf; omega

theorem hardTotal_le (W w0 n m d : ℕ) :
    hardTotal W w0 n m d ≤ 2 ^ 230 * (4 * m + 1) ^ d * (n + m + W + w0 + d + 2) ^ 42 := by
  obtain ⟨X, hX⟩ : ∃ X, X = n + m + W + w0 + d + 2 := ⟨_, rfl⟩
  rw [← hX]
  have hX1 : 1 ≤ X := by omega
  have hX3 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
  have hX6 : X ^ 3 ≤ X ^ 6 := Nat.pow_le_pow_right hX1 (by norm_num)
  -- the working widths
  have hNle : ratWidth n m ≤ 2 ^ 20 * X ^ 6 := by
    refine (ratWidth_le n m).trans ?_
    gcongr; omega
  have hGle : searchWidth (NetworkWeights.width w0 n) n m d ≤ 2 ^ 17 * X ^ 3 := by
    refine (searchWidth_le' W w0 n m d).trans ?_
    calc 2 ^ 17 * (d + 1) * (n + m + W + w0 + 2) ^ 2 ≤ 2 ^ 17 * X * X ^ 2 := by
          gcongr <;> omega
      _ = 2 ^ 17 * X ^ 3 := by ring
  have hcG := c_le_searchWidth (NetworkWeights.width w0 n) n m d
  generalize hN : ratWidth n m = N at hNle
  generalize hG : searchWidth (NetworkWeights.width w0 n) n m d = G at hGle hcG
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = X + N + G := ⟨_, rfl⟩
  have hZle : Z ≤ 2 ^ 21 * X ^ 6 := by
    have e : (2 : ℕ) ^ 21 = 2 ^ 20 + 2 ^ 20 := by norm_num
    rw [e]; nlinarith
  have D : Dom Z W n m d (NetworkWeights.width w0 n) N G :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have b1 := kernel_le (G := G) (by rw [hN]; exact D)
  have b2 := stage2_le (by rw [hG]; exact D)
  have b3 : RegisterEdgeCostProgram.budget W w0 n m ≤ 2 ^ 22 * X ^ 13 := by
    refine (RegisterEdgeCostProgram.budget_le W w0 n m).trans ?_
    calc 610000 * (w0 + 2) ^ 2 * (W + 3) ^ 2 * (n + m + 2) ^ 9
        ≤ 610000 * X ^ 2 * (2 * X) ^ 2 * X ^ 9 := by gcongr <;> omega
      _ = 2440000 * X ^ 13 := by ring
      _ ≤ 2 ^ 22 * X ^ 13 := by gcongr; norm_num
  have b4 : edgesBudget m + RegisterEdgeWords.keysBudget m + 100 ≤ 2 ^ 8 * X ^ 13 := by
    have : X ≤ X ^ 13 := Nat.le_self_pow (by norm_num) X
    unfold edgesBudget RegisterEdgeWords.keysBudget; omega
  -- collecting
  have hp : 1 ≤ (4 * m + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hZ7 : Z ^ 7 ≤ 2 ^ 147 * X ^ 42 := by
    calc Z ^ 7 ≤ (2 ^ 21 * X ^ 6) ^ 7 := Nat.pow_le_pow_left hZle 7
      _ = 2 ^ 147 * X ^ 42 := by rw [mul_pow, ← pow_mul, ← pow_mul]
  have hX13 : X ^ 13 ≤ X ^ 42 := Nat.pow_le_pow_right hX1 (by norm_num)
  generalize hP : (4 * m + 1) ^ d = P at hp b2 ⊢
  have hPX : X ^ 42 ≤ P * X ^ 42 := Nat.le_mul_of_pos_left _ hp
  have hPZ : P * Z ^ 7 ≤ P * (2 ^ 147 * X ^ 42) := Nat.mul_le_mul_left _ hZ7
  have hZP : Z ^ 7 ≤ P * Z ^ 7 := Nat.le_mul_of_pos_left _ hp
  unfold hardTotal
  rw [hN]
  generalize hQ : P * X ^ 42 = Q at hPX
  have e2 : P * (2 ^ 147 * X ^ 42) = 2 ^ 147 * Q := by rw [← hQ]; ring
  rw [e2] at hPZ
  have e1 : 2 ^ 62 * P * Z ^ 7 = 2 ^ 62 * (P * Z ^ 7) := by ring
  rw [e1] at b2
  have e3 : 2 ^ 230 * P * X ^ 42 = 2 ^ 230 * Q := by rw [← hQ]; ring
  rw [e3]
  generalize P * Z ^ 7 = PZ at hPZ hZP b2
  generalize Z ^ 7 = Z7 at hZP b1
  generalize X ^ 13 = X13 at b3 b4 hX13
  generalize X ^ 42 = X42 at hX13 hPX
  linarith

/-- The budget of the compiled hard-component solver, as a function of the
instance: `K (4 m + 1) ^ d X ^ 42` with `d` the number of global kernel rows. -/
theorem hardBudget_le (W w0 : ℕ) {n m : ℕ} {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) :
    hardBudget W w0 R w ≤ 2 ^ 230 * (4 * m + 1) ^ (ComputedEmbeddedMatrices.globalRows R).length *
      (n + m + W + w0 + (ComputedEmbeddedMatrices.globalRows R).length + 2) ^ 42 :=
  hardTotal_le W w0 n m _

end WeightedMIS.HardSolveBudget
