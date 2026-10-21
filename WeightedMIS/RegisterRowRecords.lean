module

public import WeightedMIS.RegisterKeyTrace
public import WeightedMIS.RegisterWordArithmetic

/-!
# Row records of signed states

Row `i` of a stored matrix is represented in the signed-column ABI by a record
`pair minusKey plusKey` holding the state keys `2 i + 1` and `2 i + 2`. One
record is built per stored row by two binary additions of the word one to a
running counter; the final counter `2 r + 1` is also returned, where `r` is
the number of rows.
-/

@[expose] public section

namespace WeightedMIS.RegisterRowRecords

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys

variable {p : ℕ}

/-- The record of row `i`: the stored state keys `2 i + 1` and `2 i + 2`. -/
def PairKeysAt (wk : ℕ) (h : Heap) (ptr : Ptr) (i : ℕ) : Prop :=
  ∃ mp pp, h[ptr]? = some (.pair mp pp) ∧ BitsAt h mp (word wk (2 * i + 1)) ∧
    BitsAt h pp (word wk (2 * i + 2))

theorem PairKeysAt.mono {wk : ℕ} {h h' : Heap} (he : Extends h h') {ptr : Ptr} {i : ℕ}
    (hp : PairKeysAt wk h ptr i) : PairKeysAt wk h' ptr i := by
  obtain ⟨mp, pp, hc, hm, hpp⟩ := hp
  exact ⟨mp, pp, he.lookup hc, hm.mono he, hpp.mono he⟩

theorem PairKeysAt.allocated {wk : ℕ} {h : Heap} {ptr : Ptr} {i : ℕ}
    (hp : PairKeysAt wk h ptr i) : ptr < h.length := by
  obtain ⟨_, _, hc, _⟩ := hp
  exact (List.getElem?_eq_some_iff.mp hc).1

/-- Arguments 0 = row list, 1 = counter `2 i + 1`, 2 = one; results are the
record list and the final counter. -/
def recordsBody (self add : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.null, .register 1]
    cons := .call add [.register 1, .register 2, .flag false] [5, 6]
      (.call add [.register 5, .register 2, .flag false] [7, 8]
        (.allocate 9 (.pair (.register 1) (.register 5))
          (.call self [.register 4, .register 7, .register 2] [10, 11]
            (.allocate 12 (.cons (.register 9) (.register 10)) (.ret [.register 12, .register 11]))))) }

def recordsBudget (wk len : ℕ) : ℕ := (220 * wk + 332) * len + 15

theorem word_succ {wk i : ℕ} (one : Bits wk) (hone : one.value = 1) (hi : i + 1 < 2 ^ wk) :
    (Bits.add (word wk i) one).1 = word wk (i + 1) := by
  have hv := (Bits.add_value_of_lt (word wk i) one (by rw [word_value (by omega), hone]; omega)).2
  apply value_injective
  rw [hv, word_value (by omega), word_value hi, hone]

theorem records_compiled {α : Type*} (code : Code p) (self add : Fin p)
    (hself : code self = recordsBody self add) (hadd : code add = RegisterAdder.adderBody add)
    (InputAt : Heap → Ptr → α → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    {wk : ℕ} (one : Bits wk) (hone : one.value = 1) :
    ∀ (xs : List α) (i : ℕ) {h : Heap}, Valid h → ∀ {lp kp op : Ptr},
      ListRep InputAt h lp xs → BitsAt h kp (word wk (2 * i + 1)) → BitsAt h op one →
      2 * (i + xs.length) + 1 < 2 ^ wk →
      ∃ out q fin, Extends h out ∧ Valid out ∧
        ListRep (PairKeysAt wk) out q (List.range' i xs.length) ∧
        BitsAt out fin (word wk (2 * (i + xs.length) + 1)) ∧
        Within code h (initialRegisters [.pointer lp, .pointer kp, .pointer op]) (code self)
          [.pointer q, .pointer fin] out (recordsBudget wk xs.length) := by
  intro xs
  induction xs with
  | nil =>
    intro i h hh lp kp op hl hk _ _
    obtain ⟨ps, hlist, hrel⟩ := hl
    cases hrel
    cases hlist with
    | nil cell =>
      refine ⟨h, 0, kp, .refl h, hh, RegisterListCommon.listRep_null hh, by simpa using hk, ?_⟩
      rw [hself]
      refine (Within.load (pointer := lp) (c := Cell.nil) (by simp [Atom.eval, initialRegisters]) cell
        (ret_values (by simp [values, Atom.eval, loadRegisters, decoded, initialRegisters])
          le_rfl)).mono ?_
      simp [recordsBudget]
  | cons x xs ih =>
    intro i h hh lp kp op hl hk ho hfit
    obtain ⟨ps, hlist, hrel⟩ := hl
    cases hrel with
    | @cons xp _ ps' _ hx hxs =>
    cases hlist with
    | @cons _ _ rest _ cell hrest =>
    simp only [List.length_cons] at hfit
    obtain ⟨m1, k1, e1, v1, b1, w1⟩ := RegisterWordArithmetic.add_compiled code add hadd hh hk ho
    rw [word_succ one hone (by omega)] at b1
    obtain ⟨m2, k2, e2, v2, b2, w2⟩ := RegisterWordArithmetic.add_compiled code add hadd v1 b1
      (ho.mono e1)
    rw [word_succ one hone (by omega)] at b2
    have b2' : BitsAt m2 k2 (word wk (2 * (i + 1) + 1)) := by
      have he : 2 * i + 1 + 1 + 1 = 2 * (i + 1) + 1 := by ring
      rw [← he]; exact b2
    obtain ⟨e3, v3, c3⟩ := alloc_pair v2 ((hk.mono e1).mono e2).allocated (b1.mono e2).allocated
    obtain ⟨m4, q4, f4, e4, v4, r4, b4, w4⟩ := ih (i + 1) v3 ⟨ps', hrest.mono ((e1.trans e2).trans e3),
      hxs.imp (inputMono ((e1.trans e2).trans e3))⟩ (b2'.mono e3) ((ho.mono e1).mono e2 |>.mono e3)
      (by omega)
    have hpk : PairKeysAt wk m4 m2.length i :=
      ⟨kp, k1, e4.lookup c3, ((hk.mono e1).mono e2 |>.mono e3).mono e4, ((b1.mono e2).mono e3).mono e4⟩
    obtain ⟨e5, v5, r5⟩ := RegisterListCommon.allocate_consRep (R := PairKeysAt wk)
      (fun he _ _ hp => hp.mono he) v4 hpk hpk.allocated r4
    refine ⟨_, m4.length, f4, e1.trans (e2.trans (e3.trans (e4.trans e5))), v5, ?_, ?_, ?_⟩
    · simpa [List.range'_succ] using r5
    · have : 2 * (i + 1 + xs.length) + 1 = 2 * (i + (xs.length + 1)) + 1 := by ring
      rw [this] at b4
      exact b4.mono e5
    rw [hself]
    refine (Within.load (pointer := lp) (c := Cell.cons xp rest) (by simp [Atom.eval, initialRegisters])
      cell (call_of (by simp [values, Atom.eval, loadRegisters, decoded, initialRegisters]) w1
        (call_of (by simp [values, Atom.eval, bindResults, loadRegisters, decoded, initialRegisters]) w2
          (Within.allocate (c := Cell.pair kp k1)
            (by simp [CellExpr.eval, Atom.eval, bindResults, loadRegisters, decoded, initialRegisters,
              Value.asPointer])
            (call_of (by simp [values, Atom.eval, bindResults, loadRegisters, decoded,
              initialRegisters]) w4
              (Within.allocate (c := Cell.cons m2.length q4)
                (by simp [CellExpr.eval, Atom.eval, bindResults, Value.asPointer])
                (ret_values (by simp [values, Atom.eval, bindResults]) le_rfl))))))).mono ?_
    simp [recordsBudget, CellExpr.args]
    ring_nf
    omega

end WeightedMIS.RegisterRowRecords
