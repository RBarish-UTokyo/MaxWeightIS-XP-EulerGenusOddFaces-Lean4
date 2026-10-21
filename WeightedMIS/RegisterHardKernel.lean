module

public import WeightedMIS.RegisterHardInputs
public import WeightedMIS.FaceStageProgram
public import WeightedMIS.RegisterSignedRows
public import WeightedMIS.RegisterKernelGenerators
public import WeightedMIS.RegisterCandidates
public import WeightedMIS.RegisterComplementSelect
public import WeightedMIS.AllHalfEncoded

/-!
# The kernel stage of the hard-component solver

From the stored ribbon table, the vertex words, the edge endpoint records and
the edge index words, one procedure computes, at the rational width
`ratWidth n m` built by the machine itself,

1. the stored even face rows (`FaceStageProgram`), converted to stored
   rational rows denoting `ComputedEmbeddedMatrices.localRows R`,
2. the rational incidence-kernel generators (`RegisterKernelGenerators`),
3. the bounded integral candidates (`RegisterCandidates`), converted to
   stored rational rows,
4. the incremental complement selection (`RegisterComplementSelect`),

and returns stored rational rows denoting exactly
`ComputedEmbeddedMatrices.globalRows R`.
-/

@[expose] public section

namespace WeightedMIS.RegisterHardKernel

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.RibbonTable
open WeightedMIS.RegisterFlagKeys WeightedMIS.HardWidths WeightedMIS.RegisterHardInputs
open WeightedMIS.RegisterIncidenceRows (EdgeAt)
open WeightedMIS.RegisterRationalCut (RowsAt)

variable {p : ℕ}

/-! ## Semantic bridges -/

theorem value_false {N : ℕ} (x : Bits N) :
    RegisterPotentialStep.value ((false, x) : RegisterPotentialStep.Word N) = x.value := by
  simp [RegisterPotentialStep.value, BinaryRational.signed]

theorem rep_const {N : ℕ} (v : ℕ) (hv : v < 2 ^ N) (h1 : 1 < 2 ^ N) :
    RationalWordRows.Rep (⟨false, word N v, word N 1⟩ : BinaryRational.Word N) (v : ℚ) := by
  have h := RegisterSignedRows.ratOf_rep (word N 1) (word_value h1) (false, word N v)
  rw [value_false, word_value hv] at h
  exact h

theorem face_signed {n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right)
    {N : ℕ} {ws : List (List (RegisterPotentialStep.Word N))}
    (h : List.Forall₂ (List.Forall₂ (fun w z => RegisterPotentialStep.value w = z)) ws
      R.storedEvenMatrix) :
    List.Forall₂ RegisterSignedRows.SignedRowRep ws (RegisterComplementSelect.faceInts R) := by
  unfold EmbeddingFaces.Ribbon.storedEvenMatrix at h
  unfold RegisterComplementSelect.faceInts
  rw [List.ofFn_eq_map]
  rw [List.forall₂_map_right_iff] at h ⊢
  refine h.imp ?_
  intro l i hl
  unfold RegisterSignedRows.SignedRowRep
  rw [List.ofFn_eq_map]
  exact hl

theorem signed_lengths {m N : ℕ} {ls : List (List (RegisterPotentialStep.Word N))}
    {G : List (Fin m → ℤ)} (h : List.Forall₂ RegisterSignedRows.SignedRowRep ls G) :
    ∀ l ∈ ls, l.length = m := by
  induction h with
  | nil => intro l hl; simp at hl
  | cons hx _ ih =>
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · simpa using hx.length_eq
    · exact ih l hl

/-! ## Procedures -/

/-- Arguments 0 = table, 1 = vertex words, 2 = edge records, 3 = edge index words. -/
def kernelBody (consts face signed gens candConsts cands select : Fin p) : Command p :=
  .call consts [.register 1, .register 0] [4, 5, 6, 7, 8]
  (.call face [.register 0, .register 4, .register 5] [9, 10, 11]
  (.call signed [.register 10, .register 5] [10]
  (.call gens [.register 1, .register 2, .register 6, .register 7, .register 8] [9]
  (.call candConsts [.register 6, .register 7, .register 8] [11]
  (.call cands [.register 9, .register 3, .register 2, .register 11] [9]
  (.call signed [.register 9, .register 5] [9]
  (.call select [.register 10, .register 9, .register 2, .register 6, .register 7] [12]
  (.ret [.register 12]))))))))

structure Procedures (p : ℕ) where
  kernel : Fin p
  consts : Fin p
  dbl : Fin p
  pad : Fin p
  widen : Fin p
  face : FaceStageProgram.Procedures p
  signed : RegisterSignedRows.Procedures p
  gens : RegisterKernelGenerators.Procedures p
  cands : RegisterCandidates.Procedures p
  select : RegisterComplementSelect.Procedures p
  rat : RegisterRationalProducts.Procedures p

structure Procedures.Matches (ids : Procedures p) (code : Code p) : Prop where
  kernel : code ids.kernel = kernelBody ids.consts ids.face.top ids.signed.rows ids.gens.self
    ids.cands.consts ids.cands.self ids.select.stage
  consts : code ids.consts = ratConstsBody ids.dbl ids.pad ids.widen
  dbl : code ids.dbl = dblBody ids.widen
  pad : code ids.pad = RegisterWiden.padBody ids.pad ids.widen
  widen : code ids.widen = RegisterWiden.widenBody ids.widen
  face : ids.face.Matches code
  signed : ids.signed.Matches code
  gens : ids.gens.Matches code ids.rat
  cands : ids.cands.Matches code ids.rat
  select : ids.select.Matches code ids.rat

def kernelBudget (W n m : ℕ) : ℕ :=
  ratConstsBudget n m + FaceStageProgram.stageBudget W (ratWidth n m) (ratWidth n m) m +
    ((RegisterSignedRows.rowBudget m + 35) * (4 * m) + 13) +
    RegisterKernelGenerators.budget W (ratWidth n m) n m + 109 +
    RegisterCandidates.budget W (ratWidth n m) m +
    ((RegisterSignedRows.rowBudget m + 35) * (m * m) + 13) +
    RegisterComplementSelect.stageBudget (ratWidth n m) m (4 * m) (m * m) + 100

/-- The kernel stage returns stored rational rows denoting the global rows. -/
theorem kernel_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right)
    (hn : n < 2 ^ W) (hmW : m < 2 ^ W) {h : Heap} (hh : Valid h) {tp rp ep ip : Ptr}
    (hT : RecordsAt h tp (encodeRibbon W R)) (hr : WordsAt h rp (rangeWords W n))
    (he : ListRep EdgeAt h ep (GraphReachEncoded.edgeWords W left right))
    (hi : WordsAt h ip (GraphReachEncoded.rangeWords W m)) :
    ∃ out q, ∃ acc : List (List (BinaryRational.Word (ratWidth n m))),
      Extends h out ∧ Valid out ∧ RowsAt out q acc ∧
      List.Forall₂ RationalWordRows.RowRep acc
        ((ComputedEmbeddedMatrices.globalRows R).map ComputedKernel.rationalRow) ∧
      Within code h (initialRegisters [.pointer tp, .pointer rp, .pointer ep, .pointer ip])
        (code ids.kernel) [.pointer q] out (kernelBudget W n m) := by
  have h3 : 3 ≤ ratWidth n m := by
    have h1 : 1 ≤ baseWidth * (n + 1) ^ 3 * (m + 1) ^ 3 :=
      Nat.one_le_iff_ne_zero.mpr (by simp [baseWidth])
    have := ratCore_ge n m
    unfold ratWidth; omega
  have hN2 : 2 < 2 ^ (ratWidth n m) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) h3 : 2 ^ 3 ≤ _)
  have hN1 : 1 < 2 ^ (ratWidth n m) := by omega
  -- constants
  obtain ⟨rs, hrs, hrsl⟩ := listRep_listAt hr
  obtain ⟨ts, hts, htsl⟩ := listRep_listAt hT
  obtain ⟨o1, fc, oneP, zr, orr, tr, e1, v1, hc, w1⟩ := ratConsts_compiled code ids.consts ids.dbl
    ids.pad ids.widen hm.consts hm.dbl hm.pad hm.widen hh hrs (by simpa using hrsl) hts
    (by simpa using htsl)
  have hzr : RationalWordRows.Rep (⟨false, word (ratWidth n m) 0, word (ratWidth n m) 1⟩ : BinaryRational.Word (ratWidth n m)) 0 := by
    simpa using rep_const (N := ratWidth n m) 0 (by omega) hN1
  have hor : RationalWordRows.Rep (⟨false, word (ratWidth n m) 1, word (ratWidth n m) 1⟩ : BinaryRational.Word (ratWidth n m)) 1 := by
    simpa using rep_const (N := ratWidth n m) 1 hN1 hN1
  have htr : RationalWordRows.Rep (⟨false, word (ratWidth n m) 2, word (ratWidth n m) 1⟩ : BinaryRational.Word (ratWidth n m)) 2 := by
    simpa using rep_const (N := ratWidth n m) 2 hN2 hN1
  -- face rows
  obtain ⟨o2, colsP, rowsP, cntP, ws, e2, v2, -, hws, hden, -, w2⟩ :=
    FaceStageProgram.stage_compiled ids.face code hm.face R hmW (four_edges_lt_ratWidth n m)
      (edges_lt_ratWidth n m) (word (ratWidth n m) 1) (word (ratWidth n m) 0) (word_value hN1) (word_value (by omega)) v1
      (hT.mono e1) hc.face hc.one
  have hsign := face_signed R hden
  obtain ⟨o3, locP, e3, v3, hloc, w3⟩ := RegisterSignedRows.rows_compiled code ids.signed
    hm.signed v2 hws ((hc.one.mono e2)) (signed_lengths hsign)
  have hlocRep := RegisterSignedRows.rowsRep_of_signed (word (ratWidth n m) 1) (word_value hN1) hsign
  rw [← RegisterComplementSelect.localRows_eq] at hlocRep
  have e13 := e1.trans (e2.trans e3)
  -- generators
  have hr' : ListRep (fun heap ptr (w : Bits W) => BitsAt heap ptr w) o3 rp
      (GraphReachEncoded.rangeWords W n) := by
    rw [AllHalfEncoded.rangeWords_eq]; exact hr.mono e13
  obtain ⟨o4, genP, rows, e4, v4, hgen, hgenRep, w4⟩ := RegisterKernelGenerators.compiled left right
    hn (kernelWidth_le n m) code ids.gens ids.rat hm.gens v3 hzr hor htr
    hr' (he.mono e13 (fun _ _ hx => hx.mono e13)) ((hc.zeroR.mono e2).mono e3)
    ((hc.oneR.mono e2).mono e3) ((hc.twoR.mono e2).mono e3)
  have e14 := e13.trans e4
  -- candidates
  obtain ⟨o5, kp, e5, v5, hk, w5⟩ := RegisterCandidates.consts_compiled code ids.cands ids.rat
    hm.cands v4 (((hc.zeroR.mono e2).mono e3).mono e4) (((hc.oneR.mono e2).mono e3).mono e4)
    (((hc.twoR.mono e2).mono e3).mono e4)
  have hi' : ListRep (fun heap ptr (w : Bits W) => BitsAt heap ptr w) o5 ip
      (GraphReachEncoded.rangeWords W m) := hi.mono (e14.trans e5)
  obtain ⟨o6, candP, gs, e6, v6, hgs, hgsRep, hgsLen, w6⟩ := RegisterCandidates.compiled left right
    hn hmW (decomposeWidth_le n m) code ids.cands ids.rat hm.cands v5
    (k := ((word (ratWidth n m) 0), (word (ratWidth n m) 1), (word (ratWidth n m) 2)))
    ⟨word_value (by omega), word_value hN1, word_value hN2⟩ (hgen.mono e5) hgenRep hi'
    (he.mono (e14.trans e5) (fun _ _ hx => hx.mono (e14.trans e5))) hk
  have hgsS : List.Forall₂ RegisterSignedRows.SignedRowRep gs
      (DeterministicKernel.candidates left right) := hgsRep
  obtain ⟨o7, candR, e7, v7, hcand, w7⟩ := RegisterSignedRows.rows_compiled code ids.signed
    hm.signed v6 hgs ((((((hc.one.mono e2).mono e3).mono e4).mono e5).mono e6))
    (signed_lengths hgsS)
  have hcandRep := RegisterSignedRows.rowsRep_of_signed (word (ratWidth n m) 1) (word_value hN1)
    hgsS
  have e47 := e5.trans (e6.trans e7)
  -- selection
  obtain ⟨o8, accP, acc, e8, v8, hacc, haccRep, w8⟩ :=
    RegisterComplementSelect.globalRows_compiled R (selectWidth_le n m) code ids.select ids.rat
      hm.select EdgeAt (fun he' _ _ hx => hx.mono he') v7 hzr hor ((hloc.mono e4).mono e47)
      hlocRep hcand hcandRep (he.mono (e14.trans e47) (fun _ _ hx => hx.mono (e14.trans e47)))
      (by simp [GraphReachEncoded.edgeWords])
      ((((hc.zeroR.mono e2).mono e3).mono e4).mono e47)
      ((((hc.oneR.mono e2).mono e3).mono e4).mono e47)
  refine ⟨o8, accP, acc, e14.trans (e47.trans e8), v8, hacc, haccRep, ?_⟩
  rw [hm.kernel]
  refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
    (call_of (by reg_simp) w4 (call_of (by reg_simp) w5 (call_of (by reg_simp) w6
    (call_of (by reg_simp) w7 (call_of (by reg_simp) w8
    (ret_values (by reg_simp) le_rfl))))))))).mono ?_
  have hwsl : ws.length ≤ 4 * m := by
    have := hden.length_eq
    rw [this, EmbeddingFaces.Ribbon.storedEvenMatrix_rows]
    simpa using R.evenRow_count_le (EmbeddingFaces.Flag.canonicalOrder m)
  have hb1 := Nat.mul_le_mul_left (RegisterSignedRows.rowBudget m + 35) hwsl
  have hb2 := Nat.mul_le_mul_left (RegisterSignedRows.rowBudget m + 35) hgsLen
  simp only [kernelBudget, List.length_cons, List.length_nil]
  omega

end WeightedMIS.RegisterHardKernel
