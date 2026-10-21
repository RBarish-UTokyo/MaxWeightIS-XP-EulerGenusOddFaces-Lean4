module

public import WeightedMIS.RegisterRecordLookup
public import WeightedMIS.RegisterMembership
public import WeightedMIS.RibbonTableRestrict

/-!
# The bounded first-return scan on stored flag keys

The scan is driven by a stored fuel list: each cons cell of the fuel list
permits one step, which looks up a corner, crosses the edge, and tests the
edge word of the result for membership in the stored list of retained edge
words. A fuel list of length `4 * |T|` is built once from the record list by
four null-headed cons allocations per record. The theorem refines `scanKey`
with the membership predicate on retained edge words.
-/

@[expose] public section

namespace WeightedMIS.RegisterFirstReturn

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.ExpandedWords

variable {p : ℕ}

/-! ## Membership of words -/

/-- Value membership of fixed-width words is list membership. -/
theorem found_eq_decide {n : ℕ} (q : Bits n) (ks : List (Bits n)) :
    RegisterMembership.found q ks = decide (q ∈ ks) := by
  apply Bool.eq_iff_iff.mpr
  rw [RegisterMembership.found_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨k, hk, hv⟩
    rwa [← value_injective hv]
  · exact fun h => ⟨q, h, rfl⟩

/-! ## Fuel lists -/

/-- A stored list of exactly `k` cells; its items are irrelevant. -/
def FuelAt (h : Heap) (p : Ptr) (k : ℕ) : Prop :=
  ∃ ps : List Ptr, ListAt h p ps ∧ ps.length = k

theorem FuelAt.mono {h h' : Heap} (he : Extends h h') {p : Ptr} {k : ℕ} (hf : FuelAt h p k) :
    FuelAt h' p k := by
  obtain ⟨ps, hl, hk⟩ := hf
  exact ⟨ps, hl.mono he, hk⟩

theorem FuelAt.allocated {h : Heap} {p : Ptr} {k : ℕ} (hf : FuelAt h p k) : p < h.length := by
  obtain ⟨ps, hl, -⟩ := hf
  exact hl.allocated

/-- One null-headed cons allocation extends a fuel list by one cell. -/
theorem alloc_fuel {h : Heap} (hh : Valid h) {t : Ptr} {k : ℕ} (ht : FuelAt h t k) :
    Extends h (h ++ [.cons 0 t]) ∧ Valid (h ++ [.cons 0 t]) ∧
      FuelAt (h ++ [.cons 0 t]) h.length (k + 1) := by
  obtain ⟨ps, hl, hk⟩ := ht
  obtain ⟨hs, hl'⟩ := allocate_cons hh (List.getElem?_eq_some_iff.mp hh.1).1 hl
  exact ⟨hs.1, hs.2.1, 0 :: ps, by simpa [Program.allocate] using hl', by simp [hk]⟩

/-- Arguments 0 = list, 1 = accumulated fuel; four fuel cells per list cell. -/
def fuelBody (self : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    nil := .ret [.register 1]
    cons := .call self [.register 3, .register 1] [4]
      (.allocate 5 (.cons .null (.register 4))
        (.allocate 5 (.cons .null (.register 5))
          (.allocate 5 (.cons .null (.register 5))
            (.allocate 5 (.cons .null (.register 5)) (.ret [.register 5]))))) }

theorem fuel_compiled (code : Code p) (self : Fin p) (hself : code self = fuelBody self)
    {h : Heap} (hh : Valid h) {lp acc : Ptr} {ps : List Ptr} {k : ℕ}
    (hl : ListAt h lp ps) (ha : FuelAt h acc k) :
    ∃ out q, Extends h out ∧ Valid out ∧ FuelAt out q (4 * ps.length + k) ∧
      Within code h (initialRegisters [.pointer lp, .pointer acc]) (code self) [.pointer q] out
        (50 * ps.length + 13) := by
  induction ps generalizing h lp with
  | nil =>
    cases hl with
    | nil cell =>
    refine ⟨h, acc, .refl h, hh, by simpa using ha, ?_⟩
    rw [hself]
    refine (Within.load (pointer := lp) (c := .nil) (by reg_simp) cell
      (ret_values (by reg_simp) le_rfl)).mono ?_
    simp
  | cons a ps ih =>
    cases hl with
    | @cons _ _ rest _ cell hrest =>
    obtain ⟨mid, mq, hem, hm, hf, hw⟩ := ih hh hrest ha
    obtain ⟨e1, v1, f1⟩ := alloc_fuel hm hf
    obtain ⟨e2, v2, f2⟩ := alloc_fuel v1 f1
    obtain ⟨e3, v3, f3⟩ := alloc_fuel v2 f2
    obtain ⟨e4, v4, f4⟩ := alloc_fuel v3 f3
    have hlen : 4 * (a :: ps).length + k = 4 * ps.length + k + 1 + 1 + 1 + 1 := by
      simp; ring
    rw [hlen]
    refine ⟨_, _, hem.trans (e1.trans (e2.trans (e3.trans e4))), v4, f4, ?_⟩
    rw [hself]
    refine (Within.load (pointer := lp) (c := .cons a rest) (by reg_simp) cell
      (call_of (by reg_simp) hw
      (Within.allocate (c := Cell.cons 0 mq) (by reg_simp)
      (Within.allocate (c := Cell.cons 0 mid.length) (by reg_simp)
      (Within.allocate (c := Cell.cons 0 (mid ++ [Cell.cons 0 mq]).length) (by reg_simp)
      (Within.allocate
        (c := Cell.cons 0 (mid ++ [Cell.cons 0 mq] ++ [Cell.cons 0 mid.length]).length)
        (by reg_simp)
      (ret_values (by reg_simp) le_rfl))))))).mono ?_
    simp [CellExpr.args]; omega

/-! ## The scan -/

/-- Arguments 0 = table, 1 = retained edge words, 2 = fuel, 3 = key. -/
def scanBody (self corner across edgePart mem : Fin p) : Command p :=
  .load (.register 2) 4 5 15 { CompiledTrie.failCases with
    nil := .ret [.register 3]
    cons := .call corner [.register 0, .register 3] [6]
      (.call across [.register 6] [7]
        (.call edgePart [.register 7] [8]
          (.call mem [.register 8, .register 1] [9]
            (.branch (.register 9) (.ret [.register 7])
              (.call self [.register 0, .register 1, .register 5, .register 7] [10]
                (.ret [.register 10])))))) }

structure Procedures (p : ℕ) where
  scan : Fin p
  fuel : Fin p
  lookup : RegisterRecordLookup.Procedures p
  across : Fin p
  edgePart : Fin p
  mem : Fin p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.scan = scanBody ids.scan ids.lookup.corner ids.across ids.edgePart ids.mem ∧
  code ids.fuel = fuelBody ids.fuel ∧
  ids.lookup.Matches code ∧
  code ids.across = RegisterFlagKeys.acrossBody ∧
  code ids.edgePart = RegisterFlagKeys.edgePartBody ∧
  code ids.mem = RegisterMembership.membershipBody ids.mem ids.lookup.cmp

/-- Events of one scan step. -/
def stepBudget (W t k : ℕ) : ℕ :=
  RegisterRecordLookup.cornerBudget W t + RegisterMembership.budget W k + 90

def scanBudget (W t k fuel : ℕ) : ℕ := stepBudget W t k * fuel + 13

theorem scan_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {tp kp fp xp : Ptr} {T : List (EdgeRec W)}
    {ks : List (Bits W)} {fuel : ℕ} {x : Bits (W + 2)}
    (hT : RecordsAt h tp T) (hk : WordsAt h kp ks) (hf : FuelAt h fp fuel) (hx : BitsAt h xp x) :
    ∃ out q, Extends h out ∧ Valid out ∧
      BitsAt out q (scanKey T (fun g => decide (g ∈ ks)) fuel x) ∧
      Within code h (initialRegisters [.pointer tp, .pointer kp, .pointer fp, .pointer xp])
        (code ids.scan) [.pointer q] out (scanBudget W T.length ks.length fuel) := by
  obtain ⟨hscan, -, hlookup, hacross, hedge, hmem⟩ := hm
  obtain ⟨ps, hl, rfl⟩ := hf
  induction ps generalizing h fp x xp with
  | nil =>
    cases hl with
    | nil cell =>
    refine ⟨h, xp, .refl h, hh, by simpa [scanKey] using hx, ?_⟩
    rw [hscan]
    refine (Within.load (pointer := fp) (c := .nil) (by reg_simp) cell
      (ret_values (by reg_simp) le_rfl)).mono ?_
    simp [scanBudget]
  | cons a ps ih =>
    cases hl with
    | @cons _ _ rest _ cell hrest =>
    obtain ⟨o1, q1, e1, v1, b1, w1⟩ :=
      RegisterRecordLookup.corner_compiled ids.lookup code hlookup hh hT hx
    obtain ⟨o2, q2, e2, v2, b2, w2⟩ := across_compiled code ids.across hacross v1 b1
    obtain ⟨wp, bw, w3⟩ := edgePart_compiled code ids.edgePart hedge b2
    have w4 := RegisterMembership.compiled code ids.mem ids.lookup.cmp hmem hlookup.2.2.2.2 bw
      ((hk.mono e1).mono e2)
    rw [found_eq_decide] at w4
    have e12 := e1.trans e2
    by_cases hkeep : edgePart (acrossKey (cornerKey T x)) ∈ ks
    · refine ⟨o2, q2, e12, v2, ?_, ?_⟩
      · simpa [scanKey, hkeep] using b2
      rw [hscan]
      refine (Within.load (pointer := fp) (c := .cons a rest) (by reg_simp) cell
        (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
        (call_of (by reg_simp) w4 (Within.branch (b := true) (by reg_simp; simpa using hkeep)
        (ret_values (by reg_simp) le_rfl))))))).mono ?_
      simp [scanBudget, stepBudget, Nat.mul_succ]; omega
    · obtain ⟨o3, q3, e3, v3, b3, w5⟩ := ih v2 ((hT.mono e1).mono e2) ((hk.mono e1).mono e2) b2
        ((hrest.mono e1).mono e2)
      refine ⟨o3, q3, e12.trans e3, v3, ?_, ?_⟩
      · simpa [scanKey, hkeep] using b3
      rw [hscan]
      refine (Within.load (pointer := fp) (c := .cons a rest) (by reg_simp) cell
        (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
        (call_of (by reg_simp) w4 (Within.branch (b := false) (by reg_simp; simpa using hkeep)
        (call_of (by reg_simp) w5 (ret_values (by reg_simp) le_rfl)))))))).mono ?_
      simp [scanBudget, stepBudget, Nat.mul_succ]; omega

end WeightedMIS.RegisterFirstReturn
