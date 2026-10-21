module

public import WeightedMIS.SupportCycleWords

/-!
# Word-level support decomposition and candidate rows

Under a stored rational row denoting `x`, one round of `decomposeW` produces
generator words denoting `DeterministicKernel.generator x`, finds the same
pivot as `DeterministicKernel.pivot` with the binary zero test, and computes
the residual with exact word arithmetic. With every residual of the actual
pivot trace fitting in width `R` and `3 R + 7 ≤ N`, the word rounds refine
`DeterministicKernel.decompose`. For the stored incidence-kernel generators
the residual width is `residualWidth n m` (from
`DeterministicKernelWidth.candidate_residual_fits`), so the uniform width
`decomposeWidth n m ≤ 64 (n + m + 3)^3` makes `candidatesW` denote
`DeterministicKernel.candidates`.
-/

@[expose] public section

namespace WeightedMIS.SupportCycleWords

open BinaryRational RationalWordRows RationalWidth EfficientSearch DeterministicKernel Walks
open GraphReachEncoded (word)

variable {W N : ℕ}

/-! ## Coordinate words and the decomposition -/

section Decompose

variable {n m : ℕ}

theorem signW_eq (q : BinaryRational.Word N) (hq : Canonical q) :
    signW q = decide (0 ≤ q.value) := by
  have hz := isZero_correct q hq.1
  have hd : (0 : ℚ) < q.denominator.value := by exact_mod_cast hq.1
  unfold signW zeroW
  cases hneg : q.negative
  · have hv : 0 ≤ q.value := by
      unfold Word.value Word.numerator
      simp only [hneg, Bool.false_eq_true, ↓reduceIte]
      positivity
    simp [hv]
  · have hv : q.value ≤ 0 := by
      unfold Word.value Word.numerator
      simp only [hneg, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
      exact div_nonpos_of_nonpos_of_nonneg (by simp) hd.le
    simp only [Bool.not_true, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    rw [hz, decide_eq_true_iff]
    constructor
    · intro h; rw [h]
    · intro h; exact le_antisymm hv h

theorem activeW_eq (q : BinaryRational.Word N) (hq : Canonical q) :
    activeW q = decide (q.value ≠ 0) := by
  have hz := isZero_correct q hq.1
  unfold activeW zeroW
  cases h : (isZero q).1
  · have : q.value ≠ 0 := fun h' => by simp [hz.mpr h'] at h
    simp [this]
  · simp [hz.mp h]

theorem arcPairW_eq (left right : Fin m → Fin n) (x : Fin m → ℚ)
    (q : BinaryRational.Word N) (e : Fin m) (hq : Rep q (x e)) :
    arcPairW q (word W e.val, (word W (left e).val, word W (right e).val)) =
      (arcEnc W left right x (e, false), arcEnc W left right x (e, true)) := by
  simp [arcPairW, arcEnc, arcSource_eq, arcTarget_eq, encState, signW_eq q hq.2,
    activeW_eq q hq.2, active, hq.1, SparseKernel.rationalSign]

theorem zipWith_ofFn {α β γ δ : Type*} {R : α → δ → Prop} (f : α → β → γ) :
    ∀ {k : ℕ} {l : List α} {d : Fin k → δ} (t : Fin k → β) (g : Fin k → γ),
      List.Forall₂ R l (List.ofFn d) → (∀ a i, R a (d i) → f a (t i) = g i) →
      List.zipWith f l (List.ofFn t) = List.ofFn g
  | 0, l, d, t, g, hl, _ => by
    have : l = [] := by simpa using hl.length_eq
    subst this
    simp
  | k + 1, l, d, t, g, hl, hf => by
    rw [List.ofFn_succ] at hl
    rw [List.ofFn_succ, List.ofFn_succ]
    cases hl with
    | cons ha hrest =>
      rw [List.zipWith_cons_cons, hf _ _ ha,
        zipWith_ofFn f (fun i => t i.succ) (fun i => g i.succ) hrest (fun a i h => hf a i.succ h)]

theorem pairsW_eq (left right : Fin m → Fin n) (x : Fin m → ℚ)
    (xs : List (BinaryRational.Word N)) (hxs : RowRep xs x) :
    pairsW xs (tableW W left right) =
      List.ofFn fun e : Fin m => (arcEnc W left right x (e, false), arcEnc W left right x (e, true)) :=
  zipWith_ofFn arcPairW _ _ hxs (fun q e hq => arcPairW_eq left right x q e hq)

theorem forall₂_ofFn {α β : Type*} {R : α → β → Prop} :
    ∀ {k : ℕ} (f : Fin k → α) (g : Fin k → β), (∀ i, R (f i) (g i)) →
      List.Forall₂ R (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | k + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (h 0) (forall₂_ofFn (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ))

/-- The generator words of one round denote the actual integer generator. -/
theorem generatorW_rep (hn : n < 2 ^ W) (hm : m < 2 ^ W) (left right : Fin m → Fin n)
    (x : Fin m → ℚ) (k : Bits N × Bits N × Bits N)
    (hk : k.1.value = 0 ∧ k.2.1.value = 1 ∧ k.2.2.value = 2)
    (xs : List (BinaryRational.Word N)) (hxs : RowRep xs x) :
    IntRowRep ((pairsW xs (tableW W left right)).map
      (genW k (cycleW (arcsW (pairsW xs (tableW W left right)))))) (generator left right x) := by
  rw [pairsW_eq left right x xs hxs, arcsW_ofFn, List.map_ofFn]
  exact forall₂_ofFn _ _ (fun e => genW_value hn hm left right x k hk e)

theorem ratW_rep (one : Bits N) (hone : one.value = 1) (w : RegisterPotentialStep.Word N) :
    Rep (ratW one w) (RegisterPotentialStep.value w : ℚ) := by
  have hv : (ratW one w).value = (RegisterPotentialStep.value w : ℚ) := by
    rcases w with ⟨b, a⟩
    cases b <;> simp [ratW, Word.value, Word.numerator, hone, RegisterPotentialStep.value,
      BinaryRational.signed]
  refine ⟨hv, ?_, ?_, ?_⟩
  · simp [ratW, hone]
  · rw [hv, Rat.num_intCast]
    simp [ratW]
  · rw [hv, Rat.den_intCast]
    simp [ratW, hone]

theorem ratW_rowRep (one : Bits N) (hone : one.value = 1)
    (gs : List (RegisterPotentialStep.Word N)) (g : Fin m → ℤ) (hg : IntRowRep gs g) :
    RowRep (gs.map (ratW one)) (fun i => (g i : ℚ)) := by
  unfold RowRep
  have hcast : List.ofFn (fun i => (g i : ℚ)) = (List.ofFn g).map (fun z : ℤ => (z : ℚ)) := by
    rw [List.map_ofFn]
    rfl
  rw [hcast, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hg.imp (fun w z h => h ▸ ratW_rep one hone w)

theorem zip_forall₂ {α β γ δ : Type*} {R : α → γ → Prop} {S : β → δ → Prop} {k : ℕ}
    {l₁ : List α} {l₂ : List β} {a : Fin k → γ} {b : Fin k → δ}
    (h₁ : List.Forall₂ R l₁ (List.ofFn a)) (h₂ : List.Forall₂ S l₂ (List.ofFn b)) :
    List.Forall₂ (fun p i => R p.1 (a i) ∧ S p.2 (b i)) (List.zipWith Prod.mk l₁ l₂)
      (List.ofFn fun i : Fin k => i) := by
  have hl₁ : l₁.length = k := by simpa using h₁.length_eq
  have hl₂ : l₂.length = k := by simpa using h₂.length_eq
  rw [List.forall₂_iff_get] at h₁ h₂ ⊢
  refine ⟨by simp [hl₁, hl₂], fun i hi hj => ?_⟩
  simp only [List.length_zipWith, List.length_ofFn] at hi hj
  have hi₁ : i < l₁.length := by omega
  have hi₂ : i < l₂.length := by omega
  have r₁ := h₁.2 i hi₁ (by simpa using hl₁ ▸ hi₁)
  have r₂ := h₂.2 i hi₂ (by simpa using hl₂ ▸ hi₂)
  simp only [List.get_eq_getElem, List.getElem_ofFn, List.getElem_zipWith] at r₁ r₂ ⊢
  exact ⟨r₁, r₂⟩

/-- Word-level support elimination refines `DeterministicKernel.decompose`
whenever every residual of the actual pivot trace fits in width `R`. -/
theorem decomposeW_correct (hn : n < 2 ^ W) (hm : m < 2 ^ W) (left right : Fin m → Fin n)
    (k : Bits N × Bits N × Bits N) (hk : k.1.value = 0 ∧ k.2.1.value = 1 ∧ k.2.2.value = 2)
    (R : ℕ) (hN : 3 * R + 7 ≤ N) {β : Type*} :
    ∀ (fuel : List β) (x : Fin m → ℚ) (xs : List (BinaryRational.Word N)), RowRep xs x →
      (∀ pre, pre <+: DeterministicKernelWidth.pivots left right fuel.length x →
        ∀ j, Fits (KernelArithmetic.eliminateList x pre j) R) →
      List.Forall₂ IntRowRep (decomposeW k (tableW W left right) fuel xs)
        ((decompose left right fuel.length x).map Prod.snd)
  | [], x, xs, _, _ => by simp [decomposeW, decompose]
  | _ :: fuel, x, xs, hxs, hfits => by
    let g := generator left right x
    have hgs := generatorW_rep hn hm left right x k hk xs hxs
    have hgq := ratW_rowRep k.2.1 hk.2.1 _ g hgs
    have hrel := find?_rel (zip_forall₂ hxs hgq) pivotPred (fun i => decide (g i ≠ 0))
      (fun pr i _ _ hr => by
        have hz := isZero_correct pr.2 hr.2.2.1
        rw [hr.2.1] at hz
        unfold pivotPred zeroW
        cases h : (isZero pr.2).1
        · have : (g i : ℚ) ≠ 0 := fun h' => by simp [hz.mpr h'] at h
          simpa using this
        · simpa using hz.mp h)
    have hdec : decompose left right (fuel.length + 1) x =
        match pivot g with
        | none => []
        | some e => (x e / (g e : ℚ), g) ::
            decompose left right fuel.length (KernelArithmetic.eliminate x (g, e)) := by
      simp only [decompose, materializeInt_eq, materializeRat_eq]
      rfl
    have hpiv : DeterministicKernelWidth.pivots left right (fuel.length + 1) x =
        match pivot g with
        | none => []
        | some e => (g, e) :: DeterministicKernelWidth.pivots left right fuel.length
            (KernelArithmetic.eliminate x (g, e)) := by
      simp only [DeterministicKernelWidth.pivots, materializeInt_eq, materializeRat_eq]
      rfl
    simp only [List.length_cons]
    rw [hdec]
    unfold decomposeW
    simp only
    unfold pivot at hdec hpiv ⊢
    rcases h1 : (List.zipWith Prod.mk xs
        ((pairsW xs (tableW W left right)).map (genW k (cycleW (arcsW (pairsW xs
          (tableW W left right))))) |>.map (ratW k.2.1))).find? pivotPred with _ | pr <;>
      rcases h2 : (List.ofFn fun i : Fin m => i).find? (fun i => decide (g i ≠ 0)) with _ | e <;>
      rw [h1, h2] at hrel <;> cases hrel
    · exact .nil
    · next hpr =>
      have he : g e ≠ 0 := by simpa using List.find?_some h2
      have hfx : ∀ j, Fits (x j) R := fun j => hfits [] (List.nil_prefix) j
      have hgb : ∀ j, Fits (g j : ℚ) 2 := fun j => fits_int _ 1 (by
        have h := generator_abs_le left right x j
        rw [Int.abs_eq_natAbs] at h
        show (generator left right x j).natAbs ≤ 2 ^ 1
        omega)
      have hq := divide_width_safe pr.1 pr.2 R 2 hpr.1.2 hpr.2.2 (hpr.1.1 ▸ hfx e)
        (hpr.2.1 ▸ hgb e) (by omega) (by rw [hpr.2.1]; exact_mod_cast he)
      rw [hpr.1.1, hpr.2.1] at hq
      have hκ : Fits (x e / (g e : ℚ)) (R + 2) := fits_div (hfx e) (hgb e)
      have hres := scaleSubW_rep _ _ ⟨hq.1, hq.2.1⟩ (R + 2) (R + 2) hκ hxs hgq
        (fun j => fits_mono (hfx j) (by omega)) (fun j => fits_mono (hgb j) (by omega))
        (by omega)
      refine .cons hgs ?_
      apply decomposeW_correct hn hm left right k hk R hN fuel _ _ hres
      intro pre hpre j
      have := hfits ((g, e) :: pre) (by
        rw [List.length_cons, hpiv, h2]
        exact List.cons_prefix_cons.mpr ⟨rfl, hpre⟩) j
      exact this

end Decompose

/-! ## Uniform width and candidate rows -/

section Candidates

variable {n m : ℕ}

/-- Width of every residual of the actual support elimination
(`DeterministicKernelWidth.candidate_residual_fits`). -/
def residualWidth (n m : ℕ) : ℕ := 3 * m + (2 * m + 1) * ((n + m + 2) * m + m ^ 2 + 1) + 3

/-- Working width of the word-level decomposition. -/
def decomposeWidth (n m : ℕ) : ℕ := 3 * residualWidth n m + 7

theorem decomposeWidth_le (n m : ℕ) : decomposeWidth n m ≤ 64 * (n + m + 3) ^ 3 := by
  unfold decomposeWidth residualWidth
  set s := n + m + 3 with hs
  have hm : m + 3 ≤ s := by omega
  have h1 : (n + m + 2) * m ≤ s * s := Nat.mul_le_mul (by omega) (by omega)
  have h2 : m ^ 2 ≤ s * s := by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
  have h3 : (2 * m + 1) * ((n + m + 2) * m + m ^ 2 + 1) ≤ (2 * s) * (3 * (s * s)) := by
    apply Nat.mul_le_mul (by omega)
    have : 1 ≤ s * s := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hs3 : s ^ 3 = s * s * s := by ring
  have h9 : 9 ≤ s * s := Nat.mul_le_mul (by omega : 3 ≤ s) (by omega : 3 ≤ s)
  have h27 : 3 * s ≤ s * s * s := by nlinarith
  rw [hs3]
  nlinarith

/-- Word-level candidate rows: one decomposition per stored generator row,
using the row itself as the round counter. -/
def candidatesW (k : Bits N × Bits N × Bits N) (table : List (EdgeW W))
    (rows : List (List (BinaryRational.Word N))) : List (List (RegisterPotentialStep.Word N)) :=
  rows.flatMap fun xs => decomposeW k table xs xs

theorem forall₂_flatMap {α β γ δ : Type*} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → List γ} {g : β → List δ} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs →
      (∀ a b, b ∈ bs → R a b → List.Forall₂ S (f a) (g b)) →
      List.Forall₂ S (as.flatMap f) (bs.flatMap g)
  | [], [], .nil, _ => .nil
  | a :: as, b :: bs, .cons hab hrest, hfg => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append (hfg a b List.mem_cons_self hab)
      (forall₂_flatMap hrest (fun a' b' hb hr => hfg a' b' (List.mem_cons_of_mem _ hb) hr))

/-- The word-level candidate rows denote `DeterministicKernel.candidates`. -/
theorem candidatesW_correct (hn : n < 2 ^ W) (hm : m < 2 ^ W) (left right : Fin m → Fin n)
    (k : Bits N × Bits N × Bits N) (hk : k.1.value = 0 ∧ k.2.1.value = 1 ∧ k.2.2.value = 2)
    (hN : decomposeWidth n m ≤ N) (rows : List (List (BinaryRational.Word N)))
    (hrows : List.Forall₂ RowRep rows (initial left right)) :
    List.Forall₂ IntRowRep (candidatesW k (tableW W left right) rows) (candidates left right) := by
  unfold candidatesW candidates
  apply forall₂_flatMap hrows
  intro xs x hx hxs
  have hlen : xs.length = m := rowRep_length hxs
  have h := decomposeW_correct hn hm left right k hk (residualWidth n m) hN xs x xs hxs
    (fun pre hpre j => by
      rw [hlen] at hpre
      exact DeterministicKernelWidth.candidate_residual_fits left right x hx pre hpre j)
  rwa [hlen] at h

end Candidates

end WeightedMIS.SupportCycleWords
