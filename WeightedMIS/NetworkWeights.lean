module

public import WeightedMIS.MaxFlowPreprocessing
public import WeightedMIS.NegativeWeights
public import WeightedMIS.BinaryRationalInterface
public import WeightedMIS.RegisterWiden
public import WeightedMIS.GraphReachEncoded

/-!
# Integral network weights from canonical rational words

Each vertex weight is a canonical binary rational word of width `w`. The
preprocessing truncates negative weights to zero: a negative word contributes
numerator `0` and denominator `1`. The common denominator is the product of the
truncated denominators, computed by a left fold of word multiplications, and
the scaled weight of a vertex is its truncated numerator times the exact
quotient of the product by its truncated denominator.

All network words have the common width `width w n = w + (w + 1) * (n + 1)`,
obtained by widening the input words by a zero padding word of width
`(w + 1) * (n + 1)`. The width bound `2 * (1 + Σ μ) < 2 ^ width w n` shows that
no fold step overflows and leaves one spare bit for later residual arithmetic.
-/

@[expose] public section

namespace WeightedMIS.NetworkWeights

open WeightedMIS.EfficientSearch BinaryRational
open scoped BigOperators

/-- The common width of all capacity words. -/
abbrev width (w n : ℕ) : ℕ := w + (w + 1) * (n + 1)

/-- Every fixed-width word is the canonical encoding of its value. -/
theorem eq_word {B : ℕ} (a : Bits B) : a = GraphReachEncoded.word B a.value :=
  ResidualListReach.bits_value_inj (GraphReachEncoded.word_value a.value_lt).symm

theorem eq_word_of_value {B x : ℕ} {a : Bits B} (h : a.value = x) :
    a = GraphReachEncoded.word B x := h ▸ eq_word a

/-! ## Truncation of canonical words -/

variable {w : ℕ}

/-- Numerator of the truncated weight. -/
def truncMag (q : Word w) : ℕ := if q.negative then 0 else q.magnitude.value

/-- Denominator of the truncated weight. -/
def truncDen (q : Word w) : ℕ := if q.negative then 1 else q.denominator.value

theorem truncation (q : Word w) (hq : Canonical q) :
    (max q.value 0).num.natAbs = truncMag q ∧ (max q.value 0).den = truncDen q := by
  obtain ⟨hpos, hmag, hden⟩ := hq
  unfold truncMag truncDen
  cases hneg : q.negative
  · have hv : 0 ≤ q.value := by
      unfold Word.value Word.numerator
      rw [hneg]
      simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_natCast]
      positivity
    simp only [max_eq_left hv, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hmag.symm, hden.symm⟩
  · have hv : q.value ≤ 0 := by
      unfold Word.value Word.numerator
      rw [hneg]
      simp only [↓reduceIte, Int.cast_neg, Int.cast_natCast, neg_div]
      have : (0 : ℚ) ≤ (q.magnitude.value : ℚ) / q.denominator.value := by positivity
      linarith
    simp [max_eq_right hv]

theorem truncDen_pos (q : Word w) (hq : Canonical q) : 0 < truncDen q := by
  unfold truncDen
  split
  · exact Nat.one_pos
  · exact hq.1

theorem width_pos_of_canonical (q : Word w) (hq : Canonical q) : 0 < w := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have := q.denominator.value_lt
    have := hq.1
    simp at *
    omega
  · exact hw

theorem truncDen_lt (q : Word w) (hq : Canonical q) : truncDen q < 2 ^ w := by
  unfold truncDen
  split
  · have hw := width_pos_of_canonical q hq
    exact Nat.one_lt_two_pow (by omega)
  · exact q.denominator.value_lt

theorem truncMag_lt (q : Word w) : truncMag q < 2 ^ w := by
  unfold truncMag
  split
  · exact Nat.two_pow_pos w
  · exact q.magnitude.value_lt

/-! ## The scaled weights of `MaxFlowPreprocessing` -/

variable {n : ℕ}

/-- The rational weights represented by the words. -/
def weightsOf (q : Fin n → Word w) (v : Fin n) : ℚ := (q v).value

/-- The truncated weights used by the preprocessing. -/
def truncated (q : Fin n → Word w) : Fin n → ℚ :=
  NegativeWeights.nonnegative (weightsOf q)

/-- The integral weights of the double-cover network. -/
def mu (q : Fin n → Word w) (v : Fin n) : ℕ :=
  MaxFlowPreprocessing.scaledWeight (truncated q) v

/-- The common denominator, as a list product in vertex order. -/
def denProduct (q : Fin n → Word w) : ℕ := ((List.finRange n).map fun v => truncDen (q v)).prod

theorem denominator_eq (q : Fin n → Word w) (hq : ∀ v, Canonical (q v)) :
    MaxFlowPreprocessing.denominator (truncated q) = denProduct q := by
  unfold MaxFlowPreprocessing.denominator denProduct
  rw [← List.prod_ofFn, List.ofFn_eq_map]
  congr 1
  apply List.map_congr_left
  intro v _
  exact (truncation (q v) (hq v)).2

theorem mu_eq (q : Fin n → Word w) (hq : ∀ v, Canonical (q v)) (v : Fin n) :
    mu q v = truncMag (q v) * (denProduct q / truncDen (q v)) := by
  unfold mu MaxFlowPreprocessing.scaledWeight
  rw [denominator_eq q hq]
  have ht := truncation (q v) (hq v)
  simp only [truncated, NegativeWeights.nonnegative, weightsOf] at *
  rw [ht.1, ht.2]

theorem denProduct_pos (q : Fin n → Word w) (hq : ∀ v, Canonical (q v)) : 0 < denProduct q := by
  unfold denProduct
  apply List.prod_pos
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  exact truncDen_pos _ (hq v)

theorem denProduct_le (q : Fin n → Word w) (hq : ∀ v, Canonical (q v)) :
    denProduct q ≤ 2 ^ (w * n) := by
  unfold denProduct
  have h := List.prod_le_pow_length ((List.finRange n).map fun v => truncDen (q v)) (2 ^ w)
    (by
      intro x hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
      exact (truncDen_lt _ (hq v)).le)
  simpa [← pow_mul] using h

theorem mu_lt (q : Fin n → Word w) (hq : ∀ v, Canonical (q v)) (v : Fin n) :
    mu q v < 2 ^ (w * (n + 1)) := by
  rw [mu_eq q hq]
  have hD := denProduct_le q hq
  have hDp := denProduct_pos q hq
  have hdiv : denProduct q / truncDen (q v) ≤ denProduct q := Nat.div_le_self _ _
  have hm := truncMag_lt (q v)
  calc truncMag (q v) * (denProduct q / truncDen (q v))
      ≤ truncMag (q v) * denProduct q := Nat.mul_le_mul_left _ hdiv
    _ < 2 ^ w * denProduct q := Nat.mul_lt_mul_of_pos_right hm hDp
    _ ≤ 2 ^ w * 2 ^ (w * n) := Nat.mul_le_mul_left _ hD
    _ = 2 ^ (w * (n + 1)) := by rw [← pow_add]; ring_nf

/-- The large internal capacity `1 + Σ μ`. -/
def big (q : Fin n → Word w) : ℕ := 1 + ∑ v, mu q v

theorem big_le (q : Fin n → Word w) (hq : ∀ v, Canonical (q v)) :
    big q ≤ (n + 1) * 2 ^ (w * (n + 1)) := by
  unfold big
  have hs : ∑ v, mu q v ≤ ∑ _v : Fin n, 2 ^ (w * (n + 1)) :=
    Finset.sum_le_sum fun v _ => (mu_lt q hq v).le
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  have hp : 1 ≤ 2 ^ (w * (n + 1)) := Nat.one_le_two_pow
  nlinarith

/-- The common width leaves a spare bit above the large capacity. -/
theorem width_bound (q : Fin n → Word w) (hq : ∀ v, Canonical (q v)) (hw : 0 < w) :
    2 * big q < 2 ^ width w n := by
  have hb := big_le q hq
  have hn : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  have hsplit : 2 ^ width w n = 2 ^ (w * (n + 1)) * (2 ^ w * 2 ^ (n + 1)) := by
    unfold width
    rw [← pow_add, ← pow_add]
    ring_nf
  have hw2 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hp : 0 < 2 ^ (w * (n + 1)) := Nat.two_pow_pos _
  have h1 : 2 * (n + 1) < 2 ^ w * 2 ^ (n + 1) := by nlinarith
  calc 2 * big q ≤ 2 * ((n + 1) * 2 ^ (w * (n + 1))) := Nat.mul_le_mul_left 2 hb
    _ = 2 ^ (w * (n + 1)) * (2 * (n + 1)) := by ring
    _ < 2 ^ (w * (n + 1)) * (2 ^ w * 2 ^ (n + 1)) := Nat.mul_lt_mul_of_pos_left h1 hp
    _ = 2 ^ width w n := hsplit.symm

theorem big_lt (q : Fin n → Word w) (hq : ∀ v, Canonical (q v)) (hw : 0 < w) :
    big q < 2 ^ width w n := by
  have := width_bound q hq hw
  omega

theorem denProduct_lt (q : Fin n → Word w) (hq : ∀ v, Canonical (q v)) :
    denProduct q < 2 ^ width w n := by
  have hD := denProduct_le q hq
  have : 2 ^ (w * n) < 2 ^ width w n :=
    Nat.pow_lt_pow_right (by norm_num) (by unfold width; nlinarith)
  omega

/-! ## Word-level folds performed by the register code -/

variable {j : ℕ}

/-- One step of the denominator product: negative words contribute `1`. -/
def denStep (P : Bits j) (acc : Bits (w + j)) (q : Word w) : Bits (w + j) :=
  if q.negative then acc else (Bits.multiply acc (Bits.widen P q.denominator)).1

/-- The scaled weight word: zero for negative words. -/
def muWord (P : Bits j) (D zero : Bits (w + j)) (q : Word w) : Bits (w + j) :=
  if q.negative then zero
  else (Bits.multiply (Bits.widen P q.magnitude) (Bits.divide D (Bits.widen P q.denominator)).1).1

/-- One step of the capacity sum. -/
def sumStep {B : ℕ} (acc m : Bits B) : Bits B := (Bits.add acc m).1

theorem denStep_value (P : Bits j) (acc : Bits (w + j)) (q : Word w)
    (hb : acc.value * truncDen q < 2 ^ (w + j)) :
    (denStep P acc q).value = acc.value * truncDen q := by
  unfold denStep truncDen at *
  cases hneg : q.negative
  · simp only [hneg, Bool.false_eq_true, ↓reduceIte] at hb ⊢
    rw [Bits.multiply_value_of_lt] <;> rw [Bits.widen_value]
    exact hb
  · simp

theorem fold_denStep (P : Bits j) (qs : List (Word w)) (hq : ∀ q ∈ qs, Canonical q)
    (acc : Bits (w + j)) (hb : acc.value * (qs.map truncDen).prod < 2 ^ (w + j)) :
    (qs.foldl (denStep P) acc).value = acc.value * (qs.map truncDen).prod := by
  induction qs generalizing acc with
  | nil => simp
  | cons q qs ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons] at hb ⊢
    have hrest : 0 < (qs.map truncDen).prod := by
      apply List.prod_pos
      intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact truncDen_pos r (hq r (List.mem_cons_of_mem q hr))
    have hstep : acc.value * truncDen q < 2 ^ (w + j) := by
      calc acc.value * truncDen q ≤ acc.value * (truncDen q * (qs.map truncDen).prod) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hrest)
        _ < _ := hb
    have hv := denStep_value P acc q hstep
    rw [ih (fun r hr => hq r (List.mem_cons_of_mem q hr)) _ (by rw [hv]; rw [← Nat.mul_assoc] at hb; exact hb), hv]
    ring

theorem muWord_value (P : Bits j) (D zero : Bits (w + j)) (q : Word w)
    (hz : zero.value = 0) (hD : 0 < D.value) (hb : 2 ^ w * D.value ≤ 2 ^ (w + j)) :
    (muWord P D zero q).value = truncMag q * (D.value / truncDen q) := by
  unfold muWord truncMag truncDen
  cases hneg : q.negative
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hdiv := (Bits.divide_value D (Bits.widen P q.denominator)).1
    rw [Bits.widen_value] at hdiv
    have hm := q.magnitude.value_lt
    have hle : q.magnitude.value * (D.value / q.denominator.value) < 2 ^ (w + j) := by
      calc q.magnitude.value * (D.value / q.denominator.value)
          ≤ q.magnitude.value * D.value := Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
        _ < 2 ^ w * D.value := Nat.mul_lt_mul_of_pos_right hm hD
        _ ≤ _ := hb
    rw [Bits.multiply_value_of_lt] <;> rw [Bits.widen_value, hdiv]
    exact hle
  · simp [hz]

theorem fold_sumStep {B : ℕ} (ms : List (Bits B)) (acc : Bits B)
    (hb : acc.value + (ms.map Bits.value).sum < 2 ^ B) :
    (ms.foldl sumStep acc).value = acc.value + (ms.map Bits.value).sum := by
  induction ms generalizing acc with
  | nil => simp
  | cons m ms ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons] at hb ⊢
    have hv : (sumStep acc m).value = acc.value + m.value :=
      (Bits.add_value_of_lt acc m (by omega)).2
    rw [ih _ (by rw [hv]; omega), hv]
    ring

/-! ## The computed words are the canonical encodings -/

/-- The unit word obtained by adding two zero words with an incoming carry. -/
def oneWord (B : ℕ) : Bits B := (Bits.addCarry (Bits.zero B) (Bits.zero B) true).1

theorem oneWord_value {B : ℕ} (hB : 0 < B) : (oneWord B).value = 1 := by
  have h := Bits.addCarry_value (Bits.zero B) (Bits.zero B) true
  simp only [Bits.value_zero, ↓reduceIte] at h
  have hlt : 1 < 2 ^ B := Nat.one_lt_two_pow (by omega)
  unfold oneWord
  split at h <;> omega

/-- The computed denominator product word. -/
def denWord (P : Bits j) (q : Fin n → Word w) : Bits (w + j) :=
  ((List.finRange n).map q).foldl (denStep P) (oneWord (w + j))

theorem denWord_value (P : Bits j) (q : Fin n → Word w) (hq : ∀ v, Canonical (q v))
    (hw : 0 < w) (hD : denProduct q < 2 ^ (w + j)) :
    (denWord P q).value = denProduct q := by
  unfold denWord
  have hl : (((List.finRange n).map q).map truncDen) =
      (List.finRange n).map fun v => truncDen (q v) := by rw [List.map_map]; rfl
  rw [fold_denStep P _ (by
      intro r hr
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
      exact hq v) _ (by rw [oneWord_value (by omega), hl]; simpa [denProduct] using hD),
    oneWord_value (by omega), hl]
  simp [denProduct]

/-- The padding word used by the register code: `pad` of any shape word. -/
abbrev Pad (w n : ℕ) := Bits ((w + 1) * (n + 1))

theorem muWord_eq (P : Pad w n) (q : Fin n → Word w) (hq : ∀ v, Canonical (q v)) (hw : 0 < w)
    (v : Fin n) :
    muWord P (denWord P q) (Bits.zero (width w n)) (q v) =
      GraphReachEncoded.word (width w n) (mu q v) := by
  apply eq_word_of_value
  have hD := denWord_value P q hq hw (denProduct_lt q hq)
  rw [muWord_value P _ _ _ (Bits.value_zero _) (by rw [hD]; exact denProduct_pos q hq), hD,
    mu_eq q hq]
  rw [hD]
  have hle := denProduct_le q hq
  calc 2 ^ w * denProduct q ≤ 2 ^ w * 2 ^ (w * n) := Nat.mul_le_mul_left _ hle
    _ = 2 ^ (w + w * n) := (pow_add _ _ _).symm
    _ ≤ 2 ^ width w n := Nat.pow_le_pow_right (by norm_num) (by unfold width; nlinarith)

/-- The words of the scaled weights, in vertex order. -/
def muWords (q : Fin n → Word w) : List (Bits (width w n)) :=
  (List.finRange n).map fun v => GraphReachEncoded.word (width w n) (mu q v)

theorem map_muWord (P : Pad w n) (q : Fin n → Word w) (hq : ∀ v, Canonical (q v))
    (hw : 0 < w) :
    ((List.finRange n).map q).map (muWord P (denWord P q) (Bits.zero (width w n))) =
      muWords q := by
  rw [List.map_map]
  exact List.map_congr_left fun v _ => muWord_eq P q hq hw v

theorem sum_muWords (q : Fin n → Word w) (hq : ∀ v, Canonical (q v)) (hw : 0 < w) :
    ((muWords q).map Bits.value).sum = ∑ v, mu q v := by
  unfold muWords
  rw [List.map_map]
  have : (Bits.value ∘ fun v => GraphReachEncoded.word (width w n) (mu q v)) = mu q := by
    funext v
    have hle : mu q v ≤ ∑ u, mu q u :=
      Finset.single_le_sum (f := mu q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    exact GraphReachEncoded.word_value (lt_of_le_of_lt (by unfold big; omega) (big_lt q hq hw))
  rw [this, ← List.sum_ofFn, List.ofFn_eq_map]

theorem bigWord_eq (q : Fin n → Word w) (hq : ∀ v, Canonical (q v)) (hw : 0 < w) :
    (muWords q).foldl sumStep (oneWord (width w n)) = GraphReachEncoded.word (width w n) (big q) := by
  apply eq_word_of_value
  have hpos : 0 < width w n := by unfold width; omega
  rw [fold_sumStep _ _ (by rw [oneWord_value hpos, sum_muWords q hq hw]; exact big_lt q hq hw),
    oneWord_value hpos, sum_muWords q hq hw]
  rfl

theorem zero_eq_word (B : ℕ) : Bits.zero B = GraphReachEncoded.word B 0 :=
  eq_word_of_value (Bits.value_zero B)

end WeightedMIS.NetworkWeights
