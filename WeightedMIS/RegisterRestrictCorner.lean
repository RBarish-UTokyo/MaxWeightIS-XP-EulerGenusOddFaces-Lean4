module

public import WeightedMIS.RegisterFirstReturn
public import WeightedMIS.RegisterWordAssoc
public import WeightedMIS.RegisterPairReads

/-!
# Restricted corners of stored ribbon tables

The restriction context is stored as a chain of five pair cells holding the
record list, the retained edge words, the retained vertex words, two range
lists, and the fuel list of length `4 * |T|`. A restricted corner runs the
first-return scan, crosses the edge, and renumbers the edge word through the
association of retained edge words with the range list. The four corners of
one retained edge are stored as the two-level pair structure of a record.
-/

@[expose] public section

namespace WeightedMIS.RegisterRestrictCorner

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.ExpandedWords WeightedMIS.RegisterFirstReturn WeightedMIS.RegisterPairReads

variable {p : ℕ}

/-! ## The stored context -/

/-- Values of the restriction context. -/
structure Ctx (W : ℕ) where
  T : List (EdgeRec W)
  ks : List (Bits W)
  vs : List (Bits W)
  ne : ℕ
  nv : ℕ

/-- `p ↦ (T, x1)`, `x1 ↦ (ks, x2)`, `x2 ↦ (vs, x3)`, `x3 ↦ (range ne, x4)`,
`x4 ↦ (range nv, fuel)`. The range lists are long enough. -/
def CtxAt {W : ℕ} (h : Heap) (p : Ptr) (c : Ctx W) : Prop :=
  ∃ tp x1 kp x2 vp x3 ep x4 rp fp,
    h[p]? = some (.pair tp x1) ∧ h[x1]? = some (.pair kp x2) ∧ h[x2]? = some (.pair vp x3) ∧
    h[x3]? = some (.pair ep x4) ∧ h[x4]? = some (.pair rp fp) ∧
    RecordsAt h tp c.T ∧ WordsAt h kp c.ks ∧ WordsAt h vp c.vs ∧
    WordsAt h ep (rangeWords W c.ne) ∧ WordsAt h rp (rangeWords W c.nv) ∧
    FuelAt h fp (4 * c.T.length) ∧ c.ks.length ≤ c.ne ∧ c.vs.length ≤ c.nv

theorem CtxAt.mono {W : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr} {c : Ctx W}
    (hc : CtxAt h p c) : CtxAt h' p c := by
  obtain ⟨tp, x1, kp, x2, vp, x3, ep, x4, rp, fp, c0, c1, c2, c3, c4,
    hT, hk, hv, he', hr, hf, hkl, hvl⟩ := hc
  exact ⟨tp, x1, kp, x2, vp, x3, ep, x4, rp, fp, he.lookup c0, he.lookup c1, he.lookup c2,
    he.lookup c3, he.lookup c4, hT.mono he, hk.mono he, hv.mono he, he'.mono he, hr.mono he,
    hf.mono he, hkl, hvl⟩

/-- Four corner keys stored as `c ↦ (q0, q1)`, `q0 ↦ (a, b)`, `q1 ↦ (d, e)`. -/
def QuadAt {W : ℕ} (h : Heap) (c : Ptr) (a b d e : Bits (W + 2)) : Prop :=
  ∃ q0 q1 pa pb pd pe, h[c]? = some (.pair q0 q1) ∧
    h[q0]? = some (.pair pa pb) ∧ BitsAt h pa a ∧ BitsAt h pb b ∧
    h[q1]? = some (.pair pd pe) ∧ BitsAt h pd d ∧ BitsAt h pe e

theorem QuadAt.mono {W : ℕ} {h h' : Heap} (he : Extends h h') {c : Ptr} {a b d e : Bits (W + 2)}
    (hq : QuadAt h c a b d e) : QuadAt h' c a b d e := by
  obtain ⟨q0, q1, pa, pb, pd, pe, hc, h0, ha, hb, h1, hd, hee⟩ := hq
  exact ⟨q0, q1, pa, pb, pd, pe, he.lookup hc, he.lookup h0, ha.mono he, hb.mono he,
    he.lookup h1, hd.mono he, hee.mono he⟩

/-! ## Procedures -/

/-- Arguments 0 = key, 1 = context; the result is the restricted corner. -/
def cornerRBody (scan across relabel : Fin p) : Command p :=
  readPairs [(1, 2, 3), (3, 4, 5), (5, 6, 7), (7, 8, 9), (9, 10, 11)]
    (.call scan [.register 2, .register 4, .register 11, .register 0] [12]
      (.call across [.register 12] [13]
        (.call relabel [.register 13, .register 4, .register 8] [14] (.ret [.register 14]))))

/-- Arguments 0 = edge word, 1 = context; the result is the stored quadruple
of restricted corners of the edge's four flags. -/
def cornersBody (mk cornerR : Fin p) : Command p :=
  .call mk [.flag false, .flag false, .register 0] [2]
  (.call cornerR [.register 2, .register 1] [3]
  (.call mk [.flag false, .flag true, .register 0] [2]
  (.call cornerR [.register 2, .register 1] [4]
  (.call mk [.flag true, .flag false, .register 0] [2]
  (.call cornerR [.register 2, .register 1] [5]
  (.call mk [.flag true, .flag true, .register 0] [2]
  (.call cornerR [.register 2, .register 1] [6]
  (.allocate 7 (.pair (.register 3) (.register 4))
  (.allocate 8 (.pair (.register 5) (.register 6))
  (.allocate 9 (.pair (.register 7) (.register 8)) (.ret [.register 9])))))))))))

structure Procedures (p : ℕ) where
  corners : Fin p
  cornerR : Fin p
  first : RegisterFirstReturn.Procedures p
  relabel : Fin p
  assoc : Fin p
  mkKey : Fin p

/-- The renumbering procedures, sharing the comparator and the key splitter. -/
def Procedures.relabelIds (ids : Procedures p) : RegisterWordAssoc.Procedures p :=
  ⟨ids.relabel, ids.first.lookup.split, ids.assoc, ids.mkKey, ids.first.lookup.cmp⟩

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.corners = cornersBody ids.mkKey ids.cornerR ∧
  code ids.cornerR = cornerRBody ids.first.scan ids.first.across ids.relabel ∧
  ids.first.Matches code ∧
  code ids.relabel = RegisterWordAssoc.relabelBody ids.first.lookup.split ids.assoc ids.mkKey ∧
  code ids.assoc = RegisterWordAssoc.assocBody ids.assoc ids.first.lookup.cmp ∧
  code ids.mkKey = RegisterFlagKeys.mkBody

theorem Procedures.relabel_matches {ids : Procedures p} {code : Code p} (hm : ids.Matches code) :
    ids.relabelIds.Matches code :=
  ⟨hm.2.2.2.1, hm.2.2.1.2.2.1.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2, hm.2.2.1.2.2.1.2.2.2.2⟩

def cornerRBudget (W t k : ℕ) : ℕ :=
  scanBudget W t k (4 * t) + RegisterWordAssoc.relabelBudget W k + 100

def cornersBudget (W t k : ℕ) : ℕ := 4 * cornerRBudget W t k + 160

theorem cornerR_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {xp cp : Ptr} {x : Bits (W + 2)} {c : Ctx W}
    (hx : BitsAt h xp x) (hc : CtxAt h cp c) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (restrictCorner c.T c.ks x) ∧
      Within code h (initialRegisters [.pointer xp, .pointer cp]) (code ids.cornerR)
        [.pointer q] out (cornerRBudget W c.T.length c.ks.length) := by
  obtain ⟨tp, x1, kp, x2, vp, x3, ep, x4, rp, fp, c0, c1, c2, c3, c4,
    hT, hk, -, he, -, hf, hkl, -⟩ := hc
  obtain ⟨o1, q1, e1, v1, b1, w1⟩ := scan_compiled ids.first code hm.2.2.1 hh hT hk hf hx
  obtain ⟨o2, q2, e2, v2, b2, w2⟩ :=
    across_compiled code ids.first.across hm.2.2.1.2.2.2.1 v1 b1
  obtain ⟨o3, q3, e3, v3, b3, w3⟩ := RegisterWordAssoc.relabel_compiled ids.relabelIds code
    (Procedures.relabel_matches hm) v2 b2 ((hk.mono e1).mono e2) ((he.mono e1).mono e2)
  refine ⟨o3, q3, e1.trans (e2.trans e3), v3, ?_, ?_⟩
  · rw [RegisterWordAssoc.zip_rangeWords _ hkl] at b3
    exact b3
  rw [hm.2.1]
  refine (Reads.within (.cons (by reg_simp) c0 (.cons (by reg_simp) c1 (.cons (by reg_simp) c2
    (.cons (by reg_simp) c3 (.cons (by reg_simp) c4 (.nil _))))))
    (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
      (ret_values (by reg_simp) le_rfl))))).mono ?_
  simp [cornerRBudget, RegisterWordAssoc.relabelBudget]; omega

theorem corners_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {gp cp : Ptr} {g : Bits W} {c : Ctx W}
    (hg : BitsAt h gp g) (hc : CtxAt h cp c) :
    ∃ out q, Extends h out ∧ Valid out ∧
      QuadAt out q (restrictCorner c.T c.ks (mkKey false false g))
        (restrictCorner c.T c.ks (mkKey false true g))
        (restrictCorner c.T c.ks (mkKey true false g))
        (restrictCorner c.T c.ks (mkKey true true g)) ∧
      Within code h (initialRegisters [.pointer gp, .pointer cp]) (code ids.corners)
        [.pointer q] out (cornersBudget W c.T.length c.ks.length) := by
  have hmk := hm.2.2.2.2.2
  obtain ⟨o1, k1, e1, v1, b1, w1⟩ := mk_compiled code ids.mkKey hmk hh hg false false
  obtain ⟨o2, r1, e2, v2, d1, u1⟩ := cornerR_compiled ids code hm v1 b1 (hc.mono e1)
  have e12 := e1.trans e2
  obtain ⟨o3, k2, e3, v3, b2, w2⟩ := mk_compiled code ids.mkKey hmk v2 (hg.mono e12) false true
  obtain ⟨o4, r2, e4, v4, d2, u2⟩ := cornerR_compiled ids code hm v3 b2 ((hc.mono e12).mono e3)
  have e14 := e12.trans (e3.trans e4)
  obtain ⟨o5, k3, e5, v5, b3, w3⟩ := mk_compiled code ids.mkKey hmk v4 (hg.mono e14) true false
  obtain ⟨o6, r3, e6, v6, d3, u3⟩ := cornerR_compiled ids code hm v5 b3 ((hc.mono e14).mono e5)
  have e16 := e14.trans (e5.trans e6)
  obtain ⟨o7, k4, e7, v7, b4, w4⟩ := mk_compiled code ids.mkKey hmk v6 (hg.mono e16) true true
  obtain ⟨o8, r4, e8, v8, d4, u4⟩ := cornerR_compiled ids code hm v7 b4 ((hc.mono e16).mono e7)
  have e48 := e4.trans (e5.trans (e6.trans (e7.trans e8)))
  have e68 := e6.trans (e7.trans e8)
  have e88 := e8
  have hd1 := (d1.mono (e3.trans e48))
  have hd2 := d2.mono (e5.trans e68)
  have hd3 := d3.mono (e7.trans e88)
  obtain ⟨f1, s1, l1⟩ := alloc_pair v8 hd1.allocated (d2.mono (e5.trans e68)).allocated
  obtain ⟨f2, s2, l2⟩ := alloc_pair s1 (hd3.mono f1).allocated ((d4.mono f1)).allocated
  obtain ⟨f3, s3, l3⟩ := alloc_pair s2
    (show o8.length < (o8 ++ [Cell.pair r1 r2] ++ [Cell.pair r3 r4]).length by simp)
    (show (o8 ++ [Cell.pair r1 r2]).length < (o8 ++ [Cell.pair r1 r2] ++ [Cell.pair r3 r4]).length
      by simp)
  have f23 := f2.trans f3
  refine ⟨_, (o8 ++ [Cell.pair r1 r2] ++ [Cell.pair r3 r4]).length,
    e16.trans (e7.trans (e8.trans (f1.trans f23))), s3, ?_, ?_⟩
  · refine ⟨o8.length, (o8 ++ [Cell.pair r1 r2]).length, r1, r2, r3, r4, l3, ?_,
      (hd1.mono f1).mono f23, (hd2.mono f1).mono f23, ?_, (hd3.mono f1).mono f23,
      (d4.mono f1).mono f23⟩
    · exact f23.lookup l1
    · exact f3.lookup l2
  rw [hm.1]
  refine (call_of (by reg_simp) w1 (call_of (by reg_simp) u1 (call_of (by reg_simp) w2
    (call_of (by reg_simp) u2 (call_of (by reg_simp) w3 (call_of (by reg_simp) u3
    (call_of (by reg_simp) w4 (call_of (by reg_simp) u4
    (Within.allocate (c := Cell.pair r1 r2) (by reg_simp)
    (Within.allocate (c := Cell.pair r3 r4) (by reg_simp)
    (Within.allocate (c := Cell.pair o8.length (o8 ++ [Cell.pair r1 r2]).length) (by reg_simp)
    (ret_values (by reg_simp) le_rfl)))))))))))).mono ?_
  simp [cornersBudget, CellExpr.args]; omega

end WeightedMIS.RegisterRestrictCorner
