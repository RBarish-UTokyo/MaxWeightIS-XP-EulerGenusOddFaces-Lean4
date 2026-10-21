module

public import WeightedMIS.SpecEncoding
public import WeightedMIS.RegisterEdgePairs
public import WeightedMIS.RegisterWeightMask
public import WeightedMIS.RegisterPreprocessing
public import WeightedMIS.RegisterFinalAssembly

/-!
# The top-level entry procedure

The entry procedure receives the root of the encoded input heap
`Spec.encode D w`. It loads the root record `pair vertices (pair table
weights)`, builds the endpoint pairs of the edge records, runs the compiled
maximum-flow preprocessing on the vertex words, the endpoint pairs and the
stored weight row, computes the nonnegativity mask and the stored truncated
weights of the row, and finally runs the compiled assembly. The hard-component
procedure is a parameter through the contract `RegisterComponentSolve.HardSpec`
for canonical stored rationals of the input weight width (`CanonAt`).

The result is the stored word list of `ExecutableMIS.solve R w` for every
internal ribbon `R` carrying the corners of `D`, within the event budget
`topBudget` plus the hard budgets of the actual hard components.
-/

@[expose] public section

namespace WeightedMIS.RegisterTopLevel

open WeightedMIS.Spec WeightedMIS.SpecEncoding
open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RegisterFlagKeys WeightedMIS.ExpandedWords
open WeightedMIS.RegisterComponentSolve (HardBudget HardSpec)
open WeightedMIS.RegisterWeightMask (CanonAt)
open WeightedMIS.RegisterFinalAssembly (residualHardSum)

variable {p : ℕ}

/-- Argument 0 = root record. -/
def topBody (pairs pre mask trunc assembly : Fin p) : Command p :=
  .load (.register 0) 1 2 15 { CompiledTrie.failCases with
    pair := .load (.register 2) 3 4 15 { CompiledTrie.failCases with
      pair := .call pairs [.register 3, .null] [5]
        (.call pre [.register 1, .register 5, .register 4] [6, 7, 8, 9]
          (.call mask [.register 4] [10]
            (.call trunc [.register 4, .null] [11]
              (.call assembly [.register 6, .register 10, .register 3, .register 1, .register 11]
                [12] (.ret [.register 12]))))) } }

structure Procedures (p : ℕ) where
  top : Fin p
  pairs : RegisterEdgePairs.Procedures p
  pre : RegisterPreprocessing.Procedures p
  weights : RegisterWeightMask.Procedures p
  assembly : RegisterFinalAssembly.Procedures p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.top = topBody ids.pairs.pairs ids.pre.self ids.weights.mask ids.weights.trunc
    ids.assembly.assembly ∧
  ids.pairs.Matches code ∧ ids.pre.Matches code ∧ ids.weights.Matches code ∧
  ids.assembly.Matches code

/-- The hard-component procedure of the table. -/
abbrev Procedures.hard (ids : Procedures p) : Fin p := ids.assembly.allHalf.component.hard

/-- Events of the entry procedure apart from the hard calls, for index width
`W`, weight width `w0`, `n` vertices and `m` edges. -/
def topBudget (W w0 n m : ℕ) : ℕ :=
  RegisterEdgePairs.pairsBudget m + RegisterPreprocessing.budget W w0 n m +
    RegisterWeightMask.maskBudget w0 n + RegisterWeightMask.truncBudget w0 n +
    RegisterFinalAssembly.assemblyBudget W n m + 60

/-- The event budget of the entry procedure on the encoded input. -/
abbrev inputBudget (D : Drawing) (w : Fin D.vertices → ℚ) : ℕ :=
  topBudget (indexWidth D) (weightWidth w) D.vertices D.edges

/-- **The entry procedure.** On the encoded input heap, the entry procedure
returns the stored word list of `ExecutableMIS.solve R w`, for every internal
ribbon `R` carrying the corners of `D`, within `topBudget` plus the hard
budgets of the actual hard components. -/
theorem top_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    (hb : HardBudget) (D : Drawing) (w : Fin D.vertices → ℚ)
    (hard : HardSpec code ids.hard (indexWidth D) (CanonAt (weightWidth w)) hb)
    {R : EmbeddingFaces.Ribbon D.left D.right}
    (hR : ∀ y, R.corner y = Spec.Flag.equiv _ (D.corner ((Spec.Flag.equiv _).symm y))) :
    ∃ out q, Extends (encode D w).1 out ∧ Valid out ∧
      WordsAt out q (GraphReachEncoded.setWords (indexWidth D) (ExecutableMIS.solve R w)) ∧
      Within code (encode D w).1 (initialRegisters [.pointer (encode D w).2]) (code ids.top)
        [.pointer q] out (inputBudget D w + residualHardSum hb R w) := by
  obtain ⟨htop, hpairs, hpre, hweights, hasm⟩ := hm
  obtain ⟨vp, rest, tp, wp, c0, c1, hv, hT, hw⟩ := encode_root D w hR
  have hh := encode_valid D w
  -- endpoint pairs
  obtain ⟨o1, ep, e1, v1, hep, w1⟩ :=
    RegisterEdgePairs.edgeWords_compiled ids.pairs code hpairs R hh hT
  -- preprocessing
  have hvG : WordsAt (encode D w).1 vp
      (GraphReachEncoded.rangeWords (indexWidth D) D.vertices) := by
    rw [rangeWords_eq]; exact hv
  obtain ⟨o2, zp, tablep, cutp, bigp, e2, v2, hz, -, w2⟩ :=
    RegisterPreprocessing.preprocessing_compiled code ids.pre hpre (vertices_lt D) D.left D.right
      w (fun v => ratWord (weightWidth w) (w v)) (weightRow_canonical w) (weightRow_value w) v1
      (hvG.mono e1) hep (hw.mono e1)
  have e12 := e1.trans e2
  -- nonnegativity mask
  obtain ⟨o3, mp, e3, v3, hmp, w3⟩ := RegisterWeightMask.weightMask_compiled ids.weights code
    hweights w (fun v => ratWord (weightWidth w) (w v)) (weightRow_canonical w)
    (weightRow_value w) v2 (hw.mono e12)
  have e13 := e12.trans e3
  -- truncated weights
  obtain ⟨o4, trp, e4, v4, htr, w4⟩ := RegisterWeightMask.truncate_compiled ids.weights code
    hweights w (fun v => ratWord (weightWidth w) (w v)) (weightRow_canonical w)
    (weightRow_value w) v3 (hw.mono e13)
  have e14 := e13.trans e4
  have e24 := e3.trans e4
  -- assembly
  obtain ⟨o5, q, e5, v5, hq, w5⟩ := RegisterFinalAssembly.assembly_compiled ids.assembly code hasm
    (CanonAt (weightWidth w)) (fun he _ _ hx => hx.mono he) hb hard (vertices_lt D) (edges_lt D)
    R w v4 (hz.mono e24) (RegisterWordFilter.MaskAt.mono e4 hmp) (hT.mono e14) (hv.mono e14) htr
  refine ⟨o5, q, e14.trans e5, v5, hq, ?_⟩
  rw [htop]
  refine (Within.load (c := Cell.pair vp rest) (by reg_simp) c0
    (Within.load (c := Cell.pair tp wp) (by reg_simp) c1
    (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
    (call_of (by reg_simp) w4 (call_of (by reg_simp) w5
    (ret_values (by reg_simp) le_rfl)))))))).mono ?_
  simp only [inputBudget, topBudget, List.length_cons, List.length_nil]
  omega

end WeightedMIS.RegisterTopLevel
