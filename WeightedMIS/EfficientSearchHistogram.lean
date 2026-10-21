module

public import WeightedMIS.EfficientSearchArithmetic

/-! # Exact bounded binary histograms of recovered edge labels -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Histogram

variable {labelbits countbits : ℕ}

abbrev Table (labelbits countbits : ℕ) := Radix (Bits countbits) labelbits

def count (key : Bits labelbits) (table : Table labelbits countbits) : Bits countbits :=
  (Radix.lookup key table).1.head?.getD (Bits.zero countbits)

def bump (key : Bits labelbits) (table : Table labelbits countbits) :
    Table labelbits countbits × Bool × ℕ :=
  let old := Radix.lookup key table
  let added := Bits.addCarry (old.1.head?.getD (Bits.zero countbits)) (Bits.zero countbits) true
  let inserted := Radix.insert key added.1 table
  (inserted.1, added.2.1, old.2 + added.2.2 + inserted.2 + 1)

def collect : List (Bits labelbits) → Table labelbits countbits → Table labelbits countbits × Bool × ℕ
  | [], table => (table, false, 1)
  | key :: keys, table =>
    let updated := bump key table
    let rest := collect keys updated.1
    (rest.1, updated.2.1 || rest.2.1, updated.2.2 + rest.2.2 + 1)

def Bound (table : Table labelbits countbits) (remaining : ℕ) : Prop :=
  ∀ key, (count key table).value + remaining < 2 ^ countbits

theorem increment_value (word : Bits countbits) (h : word.value + 1 < 2 ^ countbits) :
    (Bits.addCarry word (Bits.zero countbits) true).2.1 = false ∧
      (Bits.addCarry word (Bits.zero countbits) true).1.value = word.value + 1 := by
  have hv := Bits.addCarry_value word (Bits.zero countbits) true
  simp only [Bits.value_zero, Nat.add_zero, ↓reduceIte] at hv
  cases hc : (Bits.addCarry word (Bits.zero countbits) true).2.1
  · simp [hc] at hv
    exact ⟨rfl, hv⟩
  · simp [hc] at hv
    omega

theorem count_insert (key query : Bits labelbits) (word : Bits countbits)
    (table : Table labelbits countbits) :
    count query (Radix.insert key word table).1 = if query = key then word else count query table := by
  unfold count
  rw [Radix.lookup_insert]
  split <;> simp_all

theorem bump_safe (key : Bits labelbits) (table : Table labelbits countbits) (remaining : ℕ)
    (hb : Bound table (remaining + 1)) :
    (bump key table).2.1 = false ∧ Bound (bump key table).1 remaining ∧
      ∀ query, (count query (bump key table).1).value =
        (count query table).value + if query = key then 1 else 0 := by
  have hbound := hb key
  have hi := increment_value (count key table) (by omega)
  refine ⟨hi.1, ?_, ?_⟩
  · intro query
    have hq := hb query
    simp only [bump, count_insert]
    split_ifs with he
    · subst query
      change (Bits.addCarry (count key table) (Bits.zero countbits) true).1.value + remaining < _
      rw [hi.2]
      omega
    · omega
  · intro query
    simp only [bump, count_insert]
    split_ifs with he
    · subst query
      exact hi.2
    · simp

theorem collect_correct (keys : List (Bits labelbits)) (table : Table labelbits countbits)
    (hb : Bound table keys.length) :
    (collect keys table).2.1 = false ∧ Bound (collect keys table).1 0 ∧
      ∀ key, (count key (collect keys table).1).value = (count key table).value + keys.count key := by
  induction keys generalizing table with
  | nil => exact ⟨rfl, hb, by intro key; simp [collect]⟩
  | cons key keys ih =>
    obtain ⟨hflag, hbound, hcount⟩ := bump_safe key table keys.length hb
    obtain ⟨hrestflag, hrestbound, hrestcount⟩ := ih _ hbound
    refine ⟨by simp [collect, hflag, hrestflag], hrestbound, ?_⟩
    intro query
    change (count query (collect keys (bump key table).1).1).value = _
    rw [hrestcount, hcount]
    by_cases he : query = key
    · subst query; simp; omega
    · simp [List.count_cons, he, Ne.symm he]

theorem bump_work_le (key : Bits labelbits) (table : Table labelbits countbits) :
    (bump key table).2.2 ≤ 2 * labelbits + countbits + 4 := by
  have hl := Radix.lookup_steps key table
  simp only [bump, Bits.addCarry_steps, Radix.insert_steps]
  omega

theorem collect_work_le (keys : List (Bits labelbits)) (table : Table labelbits countbits) :
    (collect keys table).2.2 ≤ (2 * labelbits + countbits + 5) * keys.length + 1 := by
  induction keys generalizing table with
  | nil => simp [collect]
  | cons key keys ih =>
    have hb := bump_work_le key table
    have hr := ih (bump key table).1
    simp only [collect, List.length_cons]
    nlinarith

theorem empty_count (key : Bits labelbits) :
    count key (.empty : Table labelbits countbits) = Bits.zero countbits := by
  cases key <;> rfl

theorem empty_correct (keys : List (Bits labelbits)) (hwidth : keys.length < 2 ^ countbits) :
    (collect keys (.empty : Table labelbits countbits)).2.1 = false ∧
      ∀ key, (count key (collect keys (.empty : Table labelbits countbits)).1).value = keys.count key := by
  have hb : Bound (.empty : Table labelbits countbits) keys.length := by
    intro key; simpa [empty_count] using hwidth
  have h := collect_correct keys .empty hb
  exact ⟨h.1, by simpa [empty_count] using h.2.2⟩

end WeightedMIS.EfficientSearch.Histogram
