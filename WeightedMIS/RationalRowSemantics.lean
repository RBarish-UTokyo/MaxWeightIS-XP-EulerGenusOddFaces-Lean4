module

public import WeightedMIS.RegisterRationalRow
public import WeightedMIS.StoredElimination

/-!
# Width-safe semantics of compiled rational row arithmetic

The common working width is linear in row length and input component widths.
All suffix sums remain canonical and agree with the rational dot product.
-/

@[expose] public section

namespace WeightedMIS.RegisterRationalRow

open EfficientSearch BinaryRational RationalWidth

variable {n : ℕ}

def dotValue : List (Word n) → List (Word n) → ℚ
  | q :: qs, r :: rs => q.value * r.value + dotValue qs rs
  | _, _ => 0

theorem dotValue_fits (qs rs : List (Word n)) (a b : ℕ)
    (hq : ∀ q ∈ qs, Fits q.value a) (hr : ∀ r ∈ rs, Fits r.value b) :
    Fits (dotValue qs rs) ((a+b+1)*qs.length+1) := by
  induction qs generalizing rs with
  | nil => simpa [dotValue] using fits_zero
  | cons q qs ih =>
    cases rs with
    | nil => exact fits_mono fits_zero (by omega)
    | cons r rs =>
      have hp := fits_mul (hq q (by simp)) (hr r (by simp))
      have ht := ih rs (fun q' h => hq q' (by simp [h])) (fun r' h => hr r' (by simp [h]))
      have hs := fits_add hp ht
      convert hs using 1 <;> simp only [dotValue,List.length_cons] <;> congr 1 <;> ring

theorem dotWords_correct (qs rs : List (Word n)) (zero : Word n) (a b : ℕ)
    (hz : zero.value = 0) (hzc : Canonical zero)
    (hqc : ∀ q ∈ qs, Canonical q) (hrc : ∀ r ∈ rs, Canonical r)
    (hq : ∀ q ∈ qs, Fits q.value a) (hr : ∀ r ∈ rs, Fits r.value b)
    (hwidth : (a+b+1)*(qs.length+1)+2 ≤ n) :
    (dotWords zero qs rs).value = dotValue qs rs ∧ Canonical (dotWords zero qs rs) := by
  induction qs generalizing rs with
  | nil => exact ⟨hz,hzc⟩
  | cons q qs ih =>
    cases rs with
    | nil => exact ⟨hz,hzc⟩
    | cons r rs =>
      have hqt : ∀ q' ∈ qs, Fits q'.value a := fun q' h => hq q' (by simp [h])
      have hrt : ∀ r' ∈ rs, Fits r'.value b := fun r' h => hr r' (by simp [h])
      have ht := ih rs (fun q' h => hqc q' (by simp [h])) (fun r' h => hrc r' (by simp [h]))
        hqt hrt (by simp only [List.length_cons,Nat.mul_add] at hwidth ⊢; omega)
      have hm := multiply_width_safe q r a b (hqc q (by simp)) (hrc r (by simp))
        (hq q (by simp)) (hr r (by simp)) (by
          simp only [List.length_cons,Nat.mul_add] at hwidth
          omega)
      have hpm : Fits (multiply q r).1.value (a+b) := by
        rw [hm.1]
        exact fits_mul (hq q (by simp)) (hr r (by simp))
      have hpt : Fits (dotWords zero qs rs).value ((a+b+1)*qs.length+1) := by
        rw [ht.1]
        exact dotValue_fits qs rs a b hqt hrt
      have hs := add_width_safe (multiply q r).1 (dotWords zero qs rs)
        (a+b) ((a+b+1)*qs.length+1) hm.2.1 ht.2 hpm hpt (by
          simp only [List.length_cons,Nat.mul_add] at hwidth
          omega)
      exact ⟨hs.1.trans (by rw [hm.1,ht.1]; rfl),hs.2.1⟩

theorem dotValue_ofFn {m : ℕ} (q r : Fin m → Word n) :
    dotValue (List.ofFn q) (List.ofFn r) = ∑ i, (q i).value * (r i).value := by
  induction m with
  | zero => simp [dotValue]
  | succ m ih =>
    simp only [List.ofFn_succ,dotValue,ih,Fin.sum_univ_succ]

theorem dotWords_ofFn_correct {m : ℕ} (q r : Fin m → Word n) (zero : Word n) (a b : ℕ)
    (hz : zero.value = 0) (hzc : Canonical zero)
    (hqc : ∀ i, Canonical (q i)) (hrc : ∀ i, Canonical (r i))
    (hq : ∀ i, Fits (q i).value a) (hr : ∀ i, Fits (r i).value b)
    (hwidth : (a+b+1)*(m+1)+2 ≤ n) :
    (dotWords zero (List.ofFn q) (List.ofFn r)).value =
      StoredElimination.dot (StoredElimination.encode (fun i => (q i).value))
        (StoredElimination.encode (fun i => (r i).value)) ∧
      Canonical (dotWords zero (List.ofFn q) (List.ofFn r)) := by
  have result := dotWords_correct (List.ofFn q) (List.ofFn r) zero a b hz hzc
    (by simpa only [List.forall_mem_ofFn_iff] using hqc)
    (by simpa only [List.forall_mem_ofFn_iff] using hrc)
    (by simpa only [List.forall_mem_ofFn_iff] using hq)
    (by simpa only [List.forall_mem_ofFn_iff] using hr)
    (by simpa only [List.length_ofFn] using hwidth)
  simpa only [dotValue_ofFn,StoredElimination.dot,StoredElimination.decode_encode,dotProduct]
    using result

end WeightedMIS.RegisterRationalRow
