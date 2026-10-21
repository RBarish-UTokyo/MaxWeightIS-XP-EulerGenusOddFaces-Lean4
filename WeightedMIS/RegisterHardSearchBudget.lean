module

public import WeightedMIS.RegisterGenerationInputs
public import WeightedMIS.EfficientSearchOutputExact
public import WeightedMIS.RegisterHistogramValues

/-!
# Event budget of the compiled hard-component search

`budget r m d G` is the explicit interpreter-event budget of
`RegisterHardSearch.compiled`: parameter words, label keys, edge records,
template compilation plus expanded-arc enumeration plus trie construction,
the sparse search with histogram, and the ordered count extraction.

The parameter-sensitive parts (enumeration and search) are linear in the node
count `2 (4m+1)^d (1+(2r+1)^2)` and in the arc bound
`entryBound r m d m`. `budget_le` bounds the total by
`2^40 (4m+1)^d (r+m+d+G+2)^6`; no factor of the node count appears twice.
-/

@[expose] public section

namespace WeightedMIS.RegisterHardSearch

open WeightedMIS.NodeEncoding WeightedMIS.SparseSearchGraph

/-- The budget with the node count and arc bound as free parameters. -/
def boundOf (r m d G N E : ℕ) : ℕ :=
  RegisterExpandedParameters.budget G G G m d + RegisterGenerationInputs.keysBudget G m +
    RegisterEdgeMetadata.budget m d G G G G G G +
    SparseGraphConstruction.budget m G d (2 * m) (2 * r + 1) N +
    EfficientSearch.Output.steps G G G G E + RegisterHistogramValues.budget G m + 100

/-- Explicit event budget of the whole hard-component search. -/
def budget (r m d G : ℕ) : ℕ := boundOf r m d G (nodeCount r d m) (entryBound r m d m)

theorem keys_mono {G m G' m' : ℕ} (hG : G ≤ G') (hm : m ≤ m') :
    RegisterGenerationInputs.keysBudget G m ≤ RegisterGenerationInputs.keysBudget G' m' := by
  simp only [RegisterGenerationInputs.keysBudget, RegisterExpandedParameters.countFoldBudget,
    RegisterExpandedParameters.addBudget, RegisterWordRange.budget]
  gcongr

theorem edges_mono {m d n0 n1 n2 wc k cw m' d' n0' n1' n2' wc' k' cw' : ℕ} (hm : m ≤ m')
    (hd : d ≤ d') (h0 : n0 ≤ n0') (h1 : n1 ≤ n1') (h2 : n2 ≤ n2') (hw : wc ≤ wc') (hk : k ≤ k')
    (hc : cw ≤ cw') :
    RegisterEdgeMetadata.budget m d n0 n1 n2 wc k cw ≤
      RegisterEdgeMetadata.budget m' d' n0' n1' n2' wc' k' cw' := by
  simp only [RegisterEdgeMetadata.budget, RegisterEdgeMetadata.costBudget,
    RegisterEdgeMetadata.metaBudget, RegisterEdgeMetadata.edgeBudget,
    RegisterEdgeMetadata.parityItemBudget, RegisterResize.signedBudget,
    RegisterResize.resizeBudget, RegisterColumnResize.columnBudget,
    RegisterColumnResize.stubBudget]
  gcongr

theorem construction_mono {m n d t s N m' n' d' t' s' N' : ℕ} (hm : m ≤ m') (hn : n ≤ n')
    (hd : d ≤ d') (ht : t ≤ t') (hs : s ≤ s') (hN : N ≤ N') :
    SparseGraphConstruction.budget m n d t s N ≤
      SparseGraphConstruction.budget m' n' d' t' s' N' := by
  simp only [SparseGraphConstruction.budget, RegisterGraphEnumeration.budget,
    RegisterGraphEnumeration.sourceBudget, RegisterHubEntries.rangeBudget,
    RegisterWordRange.budget, RegisterWorkSource.budget, RegisterCandidate.candidateBudget,
    RegisterCandidate.continuationBudget, RegisterHorner.digitBudget]
  gcongr

theorem steps_mono {vb cb lb nb E vb' cb' lb' nb' E' : ℕ} (hv : vb ≤ vb') (hc : cb ≤ cb')
    (hl : lb ≤ lb') (hn : nb ≤ nb') (hE : E ≤ E') :
    EfficientSearch.Output.steps vb cb lb nb E ≤
      EfficientSearch.Output.steps vb' cb' lb' nb' E' := by
  simp only [EfficientSearch.Output.steps, EfficientSearch.Program.steps,
    RegisterSearchHistogram.budget]
  gcongr

theorem values_mono {G m G' m' : ℕ} (hG : G ≤ G') (hm : m ≤ m') :
    RegisterHistogramValues.budget G m ≤ RegisterHistogramValues.budget G' m' := by
  simp only [RegisterHistogramValues.budget]
  gcongr

theorem boundOf_mono {r m d G N E r' m' d' G' N' E' : ℕ} (hr : r ≤ r') (hm : m ≤ m')
    (hd : d ≤ d') (hG : G ≤ G') (hN : N ≤ N') (hE : E ≤ E') :
    boundOf r m d G N E ≤ boundOf r' m' d' G' N' E' := by
  have h1 := RegisterExpandedParameters.budget_mono hG hG hG hm hd
  have h2 := keys_mono hG hm
  have h3 := edges_mono hm hd hG hG hG hG hG hG
  have h4 := construction_mono (s := 2 * r + 1) (s' := 2 * r' + 1) (t := 2 * m) (t' := 2 * m')
    hm hG hd (by omega) (by omega) hN
  have h5 := steps_mono (lb := G) (lb' := G') (nb := G) (nb' := G') hG hG hG hG hE
  have h6 := values_mono hG hm
  simp only [boundOf]
  omega

/-! ## Polynomial bound -/

theorem pow_le_top {X Q : ℕ} (hX : 1 ≤ X) (hQ : 1 ≤ Q) {i : ℕ} (hi : i ≤ 6) :
    X ^ i ≤ X ^ 6 * Q ∧ X ^ i * Q ≤ X ^ 6 * Q := by
  have h := Nat.pow_le_pow_right hX hi
  exact ⟨h.trans (Nat.le_mul_of_pos_right _ hQ), Nat.mul_le_mul_right Q h⟩

theorem nodeCount_le (r d m X : ℕ) (hr : r + 1 ≤ X) :
    nodeCount r d m ≤ 10 * (4 * m + 1) ^ d * X ^ 2 := by
  unfold nodeCount
  have h1 : 1 + (2 * r + 1) ^ 2 ≤ 5 * X ^ 2 := by nlinarith
  calc 2 * (4 * m + 1) ^ d * (1 + (2 * r + 1) ^ 2) ≤ 2 * (4 * m + 1) ^ d * (5 * X ^ 2) :=
        Nat.mul_le_mul_left _ h1
    _ = 10 * (4 * m + 1) ^ d * X ^ 2 := by ring

theorem entryBound_le (r d m X : ℕ) (hr : r + m + 1 ≤ X) :
    entryBound r m d m ≤ 20 * (4 * m + 1) ^ d * X ^ 3 := by
  unfold entryBound
  have hN := nodeCount_le r d m X (by omega)
  calc nodeCount r d m * (2 * r + 2 * m + 2) ≤ (10 * (4 * m + 1) ^ d * X ^ 2) * (2 * X) :=
        Nat.mul_le_mul hN (by omega)
    _ = 20 * (4 * m + 1) ^ d * X ^ 3 := by ring

theorem budget_le (r m d G : ℕ) :
    budget r m d G ≤ 2 ^ 40 * (4 * m + 1) ^ d * (r + m + d + G + 2) ^ 6 := by
  have hX : 1 ≤ r + m + d + G + 2 := by omega
  have hQ : 1 ≤ (4 * m + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have key := boundOf_mono (r' := r + m + d + G + 2) (m' := r + m + d + G + 2)
    (d' := r + m + d + G + 2) (G' := r + m + d + G + 2)
    (N' := 10 * (4 * m + 1) ^ d * (r + m + d + G + 2) ^ 2)
    (E' := 20 * (4 * m + 1) ^ d * (r + m + d + G + 2) ^ 3)
    (show r ≤ r + m + d + G + 2 by omega) (show m ≤ r + m + d + G + 2 by omega)
    (show d ≤ r + m + d + G + 2 by omega) (show G ≤ r + m + d + G + 2 by omega)
    (nodeCount_le r d m _ (by omega)) (entryBound_le r d m _ (by omega))
  refine key.trans ?_
  generalize r + m + d + G + 2 = X at hX ⊢
  generalize (4 * m + 1) ^ d = Q at hQ ⊢
  obtain ⟨a0, b0⟩ := pow_le_top hX hQ (i := 0) (by omega)
  obtain ⟨a1, b1⟩ := pow_le_top hX hQ (i := 1) (by omega)
  obtain ⟨a2, b2⟩ := pow_le_top hX hQ (i := 2) (by omega)
  obtain ⟨a3, b3⟩ := pow_le_top hX hQ (i := 3) (by omega)
  obtain ⟨a4, b4⟩ := pow_le_top hX hQ (i := 4) (by omega)
  obtain ⟨a5, b5⟩ := pow_le_top hX hQ (i := 5) (by omega)
  obtain ⟨a6, b6⟩ := pow_le_top hX hQ (i := 6) (by omega)
  simp only [boundOf, RegisterExpandedParameters.budget, RegisterExpandedParameters.scalarsBudget,
    RegisterExpandedParameters.countsBudget, RegisterExpandedParameters.vertexBudget,
    RegisterExpandedParameters.countFoldBudget, RegisterExpandedParameters.sumFoldBudget,
    RegisterExpandedParameters.powFoldBudget, RegisterResize.resizeBudget,
    RegisterExpandedParameters.addBudget, RegisterExpandedParameters.mulBudget,
    RegisterExpandedParameters.subBudget, RegisterSignificant.stripBudget,
    RegisterGenerationInputs.keysBudget, RegisterWordRange.budget, RegisterEdgeMetadata.budget,
    RegisterEdgeMetadata.costBudget, RegisterEdgeMetadata.metaBudget,
    RegisterEdgeMetadata.edgeBudget, RegisterEdgeMetadata.parityItemBudget,
    RegisterResize.signedBudget, RegisterColumnResize.columnBudget,
    RegisterColumnResize.stubBudget, SparseGraphConstruction.budget,
    RegisterGraphEnumeration.budget, RegisterGraphEnumeration.sourceBudget,
    RegisterHubEntries.rangeBudget, RegisterWorkSource.budget, RegisterCandidate.candidateBudget,
    RegisterCandidate.continuationBudget, RegisterHorner.digitBudget,
    EfficientSearch.Output.steps, EfficientSearch.Program.steps, RegisterSearchHistogram.budget,
    RegisterHistogramValues.budget]
  ring_nf
  ring_nf at a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6
  linarith

end WeightedMIS.RegisterHardSearch
