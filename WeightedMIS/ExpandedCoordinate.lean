module

public import WeightedMIS.ExpandedWords
public import WeightedMIS.EfficientSearchArithmeticMore

/-!
# Binary coordinate updates

Coordinates are unsigned digits in the box base. A signed delta has one sign
bit and a fixed-width magnitude. The executable update uses binary comparison,
addition and subtraction, and rejects precisely the updates outside the box.
-/

@[expose] public section

namespace WeightedMIS.ExpandedWords

open WeightedMIS.PointerMemory WeightedMIS.EfficientSearch WeightedMIS.EfficientSearch.Pointer

structure SignedWord (n : ℕ) where
  negative : Bool
  magnitude : Bits n

def SignedWord.value {n : ℕ} (d : SignedWord n) : ℤ :=
  if d.negative then -(d.magnitude.value : ℤ) else (d.magnitude.value : ℤ)

def SignedAt {n : ℕ} (h : Heap) (p : Ptr) (d : SignedWord n) : Prop :=
  ∃ mag, h[p]? = some (.bit d.negative mag) ∧ BitsAt h mag d.magnitude

def DeltasAt {n : ℕ} (h : Heap) (p : Ptr) (ds : List (SignedWord n)) : Prop :=
  ListRep (fun h p d => SignedAt h p d) h p ds

theorem SignedAt.allocated {n : ℕ} {h : Heap} {p : Ptr} {d : SignedWord n}
    (hd : SignedAt h p d) : p < h.length := by
  obtain ⟨_, hc, _⟩ := hd
  exact List.getElem?_eq_some_iff.mp hc |>.1

theorem SignedAt.mono {n : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr} {d : SignedWord n}
    (hd : SignedAt h p d) : SignedAt h' p d := by
  obtain ⟨m, hc, hm⟩ := hd
  exact ⟨m, he.lookup hc, hm.mono he⟩

theorem DeltasAt.mono {n : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr} {ds : List (SignedWord n)}
    (hd : DeltasAt h p ds) : DeltasAt h' p ds := ListRep.mono he (fun _ _ h => h.mono he) hd

def updateDigit {n : ℕ} (base digit : Bits n) (delta : SignedWord n) : Option (Bits n) :=
  if delta.negative then
    if (Bits.compare digit delta.magnitude).1 = .lt then none
    else some (Bits.subtract digit delta.magnitude).1
  else
    let sum := Bits.add digit delta.magnitude
    if sum.2.1 then none
    else if (Bits.compare sum.1 base).1 = .lt then some sum.1 else none

/-- The binary calculation agrees with signed integer addition and the
half-open coordinate range [0,base). -/
theorem updateDigit_spec {n : ℕ} (base digit : Bits n) (delta : SignedWord n)
    (hd : digit.value < base.value) :
    (updateDigit base digit delta).map (fun w => (w.value : ℤ)) =
      if 0 ≤ (digit.value : ℤ) + delta.value ∧ (digit.value : ℤ) + delta.value < base.value
      then some ((digit.value : ℤ) + delta.value) else none := by
  rcases delta with ⟨negative, magnitude⟩
  cases negative with
  | true =>
    have hcmp := (Bits.compare_correct digit magnitude).1
    by_cases hc : (Bits.compare digit magnitude).1 = .lt
    · have hlt := hcmp.mp hc
      have hn : ¬(0 ≤ (digit.value : ℤ) - magnitude.value ∧
          (digit.value : ℤ) - magnitude.value < base.value) := by omega
      simpa [updateDigit, SignedWord.value, hc, sub_eq_add_neg] using congrArg
        (fun x : Option ℤ => x) (show (none : Option ℤ) = if
          0 ≤ (digit.value : ℤ) - magnitude.value ∧ (digit.value : ℤ) - magnitude.value < base.value
          then some ((digit.value : ℤ) - magnitude.value) else none by rw [if_neg hn])
    · have hle : magnitude.value ≤ digit.value := Nat.le_of_not_gt (fun h => hc (hcmp.mpr h))
      have hv := (Bits.subtract_value_of_le digit magnitude hle).2
      have hr : 0 ≤ (digit.value : ℤ) - magnitude.value ∧
          (digit.value : ℤ) - magnitude.value < base.value := by omega
      simp [updateDigit, SignedWord.value, hc, hv, sub_eq_add_neg, Int.ofNat_sub hle]
      omega
  | false =>
    by_cases hcarry : (Bits.add digit magnitude).2.1 = true
    · have hn : ¬(0 ≤ (digit.value : ℤ) + magnitude.value ∧
          (digit.value : ℤ) + magnitude.value < base.value) := by
        intro h
        have hcap : digit.value + magnitude.value < 2 ^ n := by
          have hb := Bits.value_lt base
          omega
        have hc := (Bits.add_value_of_lt digit magnitude hcap).1
        simp [hcarry] at hc
      simp [updateDigit, SignedWord.value, hcarry, hn]
    · have hfalse : (Bits.add digit magnitude).2.1 = false := by cases hc : (Bits.add digit magnitude).2.1 <;> simp_all
      have hv := Bits.add_value_of_no_overflow digit magnitude hfalse
      have hcmp := (Bits.compare_correct (Bits.add digit magnitude).1 base).1
      by_cases hc : (Bits.compare (Bits.add digit magnitude).1 base).1 = .lt
      · have hlt := hcmp.mp hc
        have hr : 0 ≤ (digit.value : ℤ) + magnitude.value ∧
            (digit.value : ℤ) + magnitude.value < base.value := by omega
        simp [updateDigit, SignedWord.value, hfalse, hc, hv, hr]
      · have hge : base.value ≤ digit.value + magnitude.value := by
          have hn : ¬(Bits.add digit magnitude).1.value < base.value := fun h => hc (hcmp.mpr h)
          omega
        have hn : ¬(0 ≤ (digit.value : ℤ) + magnitude.value ∧
            (digit.value : ℤ) + magnitude.value < base.value) := by omega
        simp [updateDigit, SignedWord.value, hfalse, hc, hn]

def OptionWordAt {n : ℕ} (h : Heap) (p : Ptr) : Option (Bits n) → Prop
  | none => p = 0
  | some w => BitsAt h p w

theorem OptionWordAt.mono {n : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr}
    {w : Option (Bits n)} (hw : OptionWordAt h p w) : OptionWordAt h' p w := by
  cases w with
  | none => exact hw
  | some w => exact BitsAt.mono he hw

theorem DeltasAt.nil_iff {n : ℕ} {h : Heap} {p : Ptr} :
    DeltasAt h p ([] : List (SignedWord n)) ↔ h[p]? = some .nil := by
  constructor
  · rintro ⟨ps, hp, hw⟩
    cases hw
    cases hp with
    | nil hc => exact hc
  · intro hc; exact ⟨[], .nil hc, .nil⟩

theorem DeltasAt.cons_iff {n : ℕ} {h : Heap} {p : Ptr} {d : SignedWord n} {ds : List (SignedWord n)} :
    DeltasAt h p (d :: ds) ↔ ∃ head tail, h[p]? = some (.cons head tail) ∧
      SignedAt h head d ∧ DeltasAt h tail ds := by
  constructor
  · rintro ⟨ps, hp, hw⟩
    cases hw with
    | cons head rest =>
      cases hp with
      | cons hc ht => exact ⟨_, _, hc, head, _, ht, rest⟩
  · rintro ⟨head, tail, hc, hh, pointers, ht, hr⟩
    exact ⟨head :: pointers, .cons hc ht, .cons hh hr⟩

def OptionWordsAt {n : ℕ} (h : Heap) (p : Ptr) : Option (List (Bits n)) → Prop
  | none => p = 0
  | some ws => WordsAt h p ws

def updateWords {n : ℕ} (base : Bits n) : List (Bits n) → List (SignedWord n) → Option (List (Bits n))
  | [], [] => some []
  | x :: xs, d :: ds => do
      let y ← updateDigit base x d
      let ys ← updateWords base xs ds
      pure (y :: ys)
  | _, _ => none

end WeightedMIS.ExpandedWords
