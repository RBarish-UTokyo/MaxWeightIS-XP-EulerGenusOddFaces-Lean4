module

public import WeightedMIS.RegisterRestrictCorner
public import WeightedMIS.RegisterListZip

/-!
# Restriction and renumbering of stored ribbon tables

Each retained edge word is zipped with its new word from a range list. The
record procedure looks up the stored record of the edge, renumbers its two
endpoint words by association with the retained vertex words, computes the
four restricted corners, and allocates the six cells of the new record. The
top procedure builds the fuel list and the stored context once. The theorem
refines `restrictTable` exactly.
-/

@[expose] public section

namespace WeightedMIS.RegisterRestrictTable

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.ExpandedWords WeightedMIS.RegisterFirstReturn WeightedMIS.RegisterPairReads
open WeightedMIS.RegisterRestrictCorner

variable {p : ℕ}

/-! ## Renumbered endpoints -/

/-- The renumbered endpoint words of the record of `g`, or `(i, i)` when
there is no such record. -/
def endpointsOf {W : ℕ} (T : List (EdgeRec W)) (vs : List (Bits W)) (g i : Bits W) :
    Bits W × Bits W :=
  match findRecord T g with
  | some r => (assoc r.left (vs.zip (rangeWords W vs.length)) r.left,
      assoc r.right (vs.zip (rangeWords W vs.length)) r.right)
  | none => (i, i)

theorem restrictRecord_eq {W : ℕ} (T : List (EdgeRec W)) (ks vs : List (Bits W)) (g i : Bits W) :
    restrictRecord T ks vs g i =
      ⟨i, (endpointsOf T vs g i).1, (endpointsOf T vs g i).2,
        restrictCorner T ks (mkKey false false g), restrictCorner T ks (mkKey false true g),
        restrictCorner T ks (mkKey true false g), restrictCorner T ks (mkKey true true g)⟩ := by
  unfold restrictRecord endpointsOf
  cases findRecord T g <;> rfl

/-! ## Procedures -/

/-- Arguments 0 = edge word, 1 = new edge word, 2 = context. -/
def endpointsBody (find assoc : Fin p) : Command p :=
  readPairs [(2, 3, 4), (4, 5, 6), (6, 7, 8), (8, 9, 10), (10, 11, 12)]
    (.call find [.register 3, .register 0] [13, 14]
      (.branch (.register 13)
        (.load (.register 14) 2 3 15 { CompiledTrie.failCases with
          pair := .load (.register 3) 4 5 15 { CompiledTrie.failCases with
            pair := .load (.register 5) 6 3 15 { CompiledTrie.failCases with
              pair := .call assoc [.register 7, .register 11, .register 4, .register 4] [8]
                (.call assoc [.register 7, .register 11, .register 6, .register 6] [9]
                  (.ret [.register 8, .register 9])) } } })
        (.ret [.register 1, .register 1])))

/-- Arguments 0 = edge word, 1 = new edge word, 2 = context. -/
def recordBody (endpoints corners : Fin p) : Command p :=
  .call endpoints [.register 0, .register 1, .register 2] [3, 4]
    (.call corners [.register 0, .register 2] [5]
      (.allocate 6 (.pair (.register 4) (.register 5))
        (.allocate 7 (.pair (.register 3) (.register 6))
          (.allocate 8 (.pair (.register 1) (.register 7)) (.ret [.register 8])))))

/-- Arguments 0 = table, 1 = retained edge words, 2 = retained vertex words,
3 = edge range words, 4 = vertex range words. -/
def restrictBody (fuel table : Fin p) : Command p :=
  .call fuel [.register 0, .null] [5]
    (.allocate 6 (.pair (.register 4) (.register 5))
      (.allocate 6 (.pair (.register 3) (.register 6))
        (.allocate 6 (.pair (.register 2) (.register 6))
          (.allocate 6 (.pair (.register 1) (.register 6))
            (.allocate 6 (.pair (.register 0) (.register 6))
              (.call table [.register 1, .register 3, .register 6] [7] (.ret [.register 7])))))))

structure Procedures (p : ℕ) where
  restrict : Fin p
  table : Fin p
  record : Fin p
  endpoints : Fin p
  corner : RegisterRestrictCorner.Procedures p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.restrict = restrictBody ids.corner.first.fuel ids.table ∧
  code ids.table = RegisterListZip.body ids.table ids.record ∧
  code ids.record = recordBody ids.endpoints ids.corner.corners ∧
  code ids.endpoints = endpointsBody ids.corner.first.lookup.find ids.corner.assoc ∧
  ids.corner.Matches code

def endpointsBudget (W t kv : ℕ) : ℕ :=
  RegisterRecordLookup.findBudget W t + 2 * RegisterWordAssoc.assocBudget W kv + 120

def recordBudget (W t k kv : ℕ) : ℕ := endpointsBudget W t kv + cornersBudget W t k + 40

def tableBudget (W t k kv : ℕ) : ℕ := (recordBudget W t k kv + 45) * k + 23

def restrictBudget (W t k kv : ℕ) : ℕ := 50 * t + tableBudget W t k kv + 70

/-! ## Correctness -/

theorem endpoints_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {gp ip cp : Ptr} {g i : Bits W} {c : Ctx W}
    (hg : BitsAt h gp g) (hi : BitsAt h ip i) (hc : CtxAt h cp c) :
    ∃ out l r, Extends h out ∧ Valid out ∧ BitsAt out l (endpointsOf c.T c.vs g i).1 ∧
      BitsAt out r (endpointsOf c.T c.vs g i).2 ∧
      Within code h (initialRegisters [.pointer gp, .pointer ip, .pointer cp])
        (code ids.endpoints) [.pointer l, .pointer r] out
        (endpointsBudget W c.T.length c.vs.length) := by
  obtain ⟨-, -, -, hend, hcm⟩ := hm
  obtain ⟨-, -, hfind, hkey, hcmp⟩ := hcm.2.2.1.2.2.1
  have hassoc := hcm.2.2.2.2.1
  obtain ⟨tp, x1, kp, x2, vp, x3, ep, x4, rp, fp, c0, c1, c2, c3, c4,
    hT, -, hv, -, hr, -, -, hvl⟩ := hc
  obtain ⟨out, q, he, ho, hs, hn, hf⟩ := RegisterRecordLookup.find_compiled code
    ids.corner.first.lookup.find ids.corner.first.lookup.keyMatch ids.corner.first.lookup.cmp
    hfind hkey hcmp hh hT hg
  cases hrec : findRecord c.T g with
  | none =>
    have hq := hn hrec
    subst hq
    rw [hrec] at hf
    refine ⟨out, ip, ip, he, ho, ?_, ?_, ?_⟩
    · simpa [endpointsOf, hrec] using hi.mono he
    · simpa [endpointsOf, hrec] using hi.mono he
    rw [hend]
    refine (Reads.within (.cons (by reg_simp) c0 (.cons (by reg_simp) c1 (.cons (by reg_simp) c2
      (.cons (by reg_simp) c3 (.cons (by reg_simp) c4 (.nil _)))))) (call_of (by reg_simp) hf
      (Within.branch (b := false) (by reg_simp) (ret_values (by reg_simp) le_rfl)))).mono ?_
    simp [endpointsBudget]; omega
  | some rec =>
    rw [hrec] at hf
    obtain ⟨kp', a, lp, b, rp', cc, -, -, -, -, -, -, hp, -, ha, hl, hb, hrr, -⟩ := hs rec hrec
    obtain ⟨lq, hlq, wl⟩ := RegisterWordAssoc.assoc_compiled code ids.corner.assoc
      ids.corner.first.lookup.cmp hassoc hcmp (hv.mono he) (hr.mono he) hl hl
    obtain ⟨rq, hrq, wr⟩ := RegisterWordAssoc.assoc_compiled code ids.corner.assoc
      ids.corner.first.lookup.cmp hassoc hcmp (hv.mono he) (hr.mono he) hrr hrr
    rw [RegisterWordAssoc.zip_rangeWords _ hvl] at hlq hrq
    refine ⟨out, lq, rq, he, ho, ?_, ?_, ?_⟩
    · simpa [endpointsOf, hrec] using hlq
    · simpa [endpointsOf, hrec] using hrq
    rw [hend]
    refine (Reads.within (.cons (by reg_simp) c0 (.cons (by reg_simp) c1 (.cons (by reg_simp) c2
      (.cons (by reg_simp) c3 (.cons (by reg_simp) c4 (.nil _)))))) (call_of (by reg_simp) hf
      (Within.branch (b := true) (by reg_simp)
      (Within.load (pointer := q) (c := .pair kp' a) (by reg_simp) hp
      (Within.load (pointer := a) (c := .pair lp b) (by reg_simp) ha
      (Within.load (pointer := b) (c := .pair rp' cc) (by reg_simp) hb
      (call_of (by reg_simp) wl (call_of (by reg_simp) wr
        (ret_values (by reg_simp) le_rfl))))))))).mono ?_
    simp [endpointsBudget]; omega

theorem record_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {gp ip cp : Ptr} {g i : Bits W} {c : Ctx W}
    (hg : BitsAt h gp g) (hi : BitsAt h ip i) (hc : CtxAt h cp c) :
    ∃ out q, Extends h out ∧ Valid out ∧
      EdgeRecAt out q (restrictRecord c.T c.ks c.vs g i) ∧
      Within code h (initialRegisters [.pointer gp, .pointer ip, .pointer cp])
        (code ids.record) [.pointer q] out
        (recordBudget W c.T.length c.ks.length c.vs.length) := by
  obtain ⟨o1, l, r, e1, v1, bl, br, w1⟩ := endpoints_compiled ids code hm hh hg hi hc
  obtain ⟨o2, q, e2, v2, hq, w2⟩ := corners_compiled ids.corner code hm.2.2.2.2 v1 (hg.mono e1)
    (hc.mono e1)
  obtain ⟨q0, q1, p00, p01, p10, p11, cq, cq0, b00, b01, cq1, b10, b11⟩ := hq
  have hqa : q < o2.length := (List.getElem?_eq_some_iff.mp cq).1
  obtain ⟨f1, s1, l1⟩ := alloc_pair v2 (br.mono e2).allocated hqa
  obtain ⟨f2, s2, l2⟩ := alloc_pair s1 ((bl.mono e2).mono f1).allocated
    (show o2.length < (o2 ++ [Cell.pair r q]).length by simp)
  obtain ⟨f3, s3, l3⟩ := alloc_pair s2 (((hi.mono (e1.trans e2)).mono f1).mono f2).allocated
    (show (o2 ++ [Cell.pair r q]).length < (o2 ++ [Cell.pair r q] ++ [Cell.pair l o2.length]).length
      by simp)
  have f123 := f1.trans (f2.trans f3)
  refine ⟨_, (o2 ++ [Cell.pair r q] ++ [Cell.pair l o2.length]).length,
    e1.trans (e2.trans f123), s3, ?_, ?_⟩
  · rw [restrictRecord_eq]
    exact ⟨ip, _, l, _, r, q, q0, q1, p00, p01, p10, p11, l3,
      (hi.mono (e1.trans e2)).mono f123, f3.lookup l2, (bl.mono e2).mono f123,
      (f2.trans f3).lookup l1, (br.mono e2).mono f123, f123.lookup cq, f123.lookup cq0,
      b00.mono f123, b01.mono f123, f123.lookup cq1, b10.mono f123, b11.mono f123⟩
  rw [hm.2.2.1]
  refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2
    (Within.allocate (c := Cell.pair r q) (by reg_simp)
    (Within.allocate (c := Cell.pair l o2.length) (by reg_simp)
    (Within.allocate (c := Cell.pair ip (o2 ++ [Cell.pair r q]).length) (by reg_simp)
    (ret_values (by reg_simp) le_rfl)))))).mono ?_
  simp [recordBudget, CellExpr.args]; omega

theorem table_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {kp ep cp : Ptr} {c : Ctx W}
    (hk : WordsAt h kp c.ks) (he : WordsAt h ep (rangeWords W c.ne)) (hc : CtxAt h cp c) :
    ∃ out q, Extends h out ∧ Valid out ∧ RecordsAt out q (restrictTable W c.T c.ks c.vs) ∧
      Within code h (initialRegisters [.pointer kp, .pointer ep, .pointer cp])
        (code ids.table) [.pointer q] out
        (tableBudget W c.T.length c.ks.length c.vs.length) := by
  have hkl : c.ks.length ≤ c.ne := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hkl, _⟩ := hc
    exact hkl
  obtain ⟨out, q, he', ho, hq, hw⟩ := RegisterListZip.compiled_const code ids.table ids.record
    hm.2.1 (fun h p (w : Bits W) => BitsAt h p w) (fun h p (w : Bits W) => BitsAt h p w)
    CtxAt EdgeRecAt (fun he _ _ hb => hb.mono he) (fun he _ _ hb => hb.mono he)
    (fun he _ _ hc => hc.mono he) (fun he _ _ hr => hr.mono he)
    (fun _ hr => hr.allocated) (fun c g i => restrictRecord c.T c.ks c.vs g i)
    (recordBudget W c.T.length c.ks.length c.vs.length) hh hk he hc
    (fun hv _ _ _ _ _ ha hb hd => record_compiled ids code hm hv ha hb hd)
  refine ⟨out, q, he', ho, ?_, hw.mono ?_⟩
  · have hz := RegisterWordAssoc.zipWith_rangeWords (W := W)
      (fun g i => restrictRecord c.T c.ks c.vs g i) c.ks hkl
    rw [hz] at hq
    exact hq
  · simp [tableBudget, Nat.min_eq_left hkl]

theorem restrict_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {tp kp vp ep rp : Ptr} {T : List (EdgeRec W)}
    {ks vs : List (Bits W)} {ne nv : ℕ}
    (hT : RecordsAt h tp T) (hk : WordsAt h kp ks) (hv : WordsAt h vp vs)
    (he : WordsAt h ep (rangeWords W ne)) (hr : WordsAt h rp (rangeWords W nv))
    (hkl : ks.length ≤ ne) (hvl : vs.length ≤ nv) :
    ∃ out q, Extends h out ∧ Valid out ∧ RecordsAt out q (restrictTable W T ks vs) ∧
      Within code h (initialRegisters [.pointer tp, .pointer kp, .pointer vp, .pointer ep,
        .pointer rp]) (code ids.restrict) [.pointer q] out
        (restrictBudget W T.length ks.length vs.length) := by
  obtain ⟨ps, hps, hrel⟩ := hT
  have hlen : ps.length = T.length := hrel.length_eq
  obtain ⟨o1, fp, e1, v1, hf, w1⟩ := fuel_compiled code ids.corner.first.fuel
    hm.2.2.2.2.2.2.1.2.1 hh hps (⟨[], .nil hh.1, rfl⟩ : FuelAt h 0 0)
  rw [hlen, Nat.add_zero] at hf
  have hT' : RecordsAt o1 tp T := ⟨ps, hps.mono e1, hrel.imp (fun _ _ hx => hx.mono e1)⟩
  obtain ⟨f1, s1, l1⟩ := alloc_pair v1 ((hr.mono e1).allocated) hf.allocated
  obtain ⟨f2, s2, l2⟩ := alloc_pair s1 (((he.mono e1).mono f1).allocated)
    (show o1.length < (o1 ++ [Cell.pair rp fp]).length by simp)
  let h2 := o1 ++ [Cell.pair rp fp] ++ [Cell.pair ep o1.length]
  obtain ⟨f3, s3, l3⟩ := alloc_pair s2 ((((hv.mono e1).mono f1).mono f2).allocated)
    (show (o1 ++ [Cell.pair rp fp]).length < h2.length by simp [h2])
  let h3 := h2 ++ [Cell.pair vp (o1 ++ [Cell.pair rp fp]).length]
  obtain ⟨f4, s4, l4⟩ := alloc_pair s3 (((((hk.mono e1).mono f1).mono f2).mono f3).allocated)
    (show h2.length < h3.length by simp [h3])
  let h4 := h3 ++ [Cell.pair kp h2.length]
  obtain ⟨f5, s5, l5⟩ := alloc_pair s4 (((((hT'.mono f1).mono f2).mono f3).mono f4).allocated)
    (show h3.length < h4.length by simp [h4])
  let h5 := h4 ++ [Cell.pair tp h3.length]
  have f15 : Extends o1 h5 := f1.trans (f2.trans (f3.trans (f4.trans f5)))
  have hctx : CtxAt h5 h4.length ⟨T, ks, vs, ne, nv⟩ :=
    ⟨tp, h3.length, kp, h2.length, vp, (o1 ++ [Cell.pair rp fp]).length, ep, o1.length, rp, fp,
      l5, f5.lookup l4, (f4.trans f5).lookup l3, (f3.trans (f4.trans f5)).lookup l2,
      (f2.trans (f3.trans (f4.trans f5))).lookup l1,
      hT'.mono f15, (hk.mono e1).mono f15, (hv.mono e1).mono f15, (he.mono e1).mono f15,
      (hr.mono e1).mono f15, hf.mono f15, hkl, hvl⟩
  have e15 := e1.trans f15
  obtain ⟨out, q, e6, v6, hq, w6⟩ :=
    table_compiled ids code hm s5 (hk.mono e15) (he.mono e15) hctx
  refine ⟨out, q, e15.trans e6, v6, hq, ?_⟩
  rw [hm.1]
  refine (call_of (by reg_simp) w1
    (Within.allocate (c := Cell.pair rp fp) (by reg_simp)
    (Within.allocate (c := Cell.pair ep o1.length) (by reg_simp)
    (Within.allocate (c := Cell.pair vp (o1 ++ [Cell.pair rp fp]).length) (by reg_simp)
    (Within.allocate (c := Cell.pair kp h2.length) (by reg_simp [h2])
    (Within.allocate (c := Cell.pair tp h3.length) (by reg_simp [h2, h3])
    (call_of (by reg_simp [h2, h3, h4]) w6 (ret_values (by reg_simp) le_rfl)))))))).mono ?_
  simp [restrictBudget, CellExpr.args, hlen]; omega

end WeightedMIS.RegisterRestrictTable
