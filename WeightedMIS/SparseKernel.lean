module

public import WeightedMIS.KernelBasis
public import WeightedMIS.SupportCycle

/-!
# Support-based bounded kernel extraction

The support of a nonzero rational incidence-kernel vector has an alternating
closed walk. A bounded cycle can be found after at most the number of signed
states many successor steps, independently of the magnitudes of coordinates.
-/

@[expose] public section

namespace WeightedMIS.SparseKernel

open WeightedMIS.Walks Matrix

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]

/-- The rational sign attached to an edge coordinate. -/
def rationalSign (x : E → ℚ) (e : E) : Bool := decide (0 ≤ x e)

omit [DecidableEq E] [Fintype E] in
theorem sign_opposite (x : E → ℚ) (e f : E) (h : x f * x e < 0) :
    !(rationalSign x f) = rationalSign x e := by
  by_cases he : 0 ≤ x e <;> by_cases hf : 0 ≤ x f <;>
    simp [rationalSign, he, hf] <;> nlinarith

omit [DecidableEq E] [Fintype V] in
/-- At an endpoint incident with a nonzero coordinate, balance supplies an
incident edge of the opposite sign. -/
theorem opposite_incident (left right : E → V) (x : E → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (e : E) (v : V) (hv : v = left e ∨ v = right e) (he : x e ≠ 0) :
    ∃ f, (v = left f ∨ v = right f) ∧ x f * x e < 0 := by
  have hz : ∑ f, Incidence.unsigned left right f v * x f = 0 := by
    exact congrFun hx v
  have hz' : ∑ f, Incidence.unsigned left right f v * x f * x e = 0 := by
    rw [← Finset.sum_mul, hz, zero_mul]
  have hpos : 0 < Incidence.unsigned left right e v * x e * x e := by
    have hsq : 0 < x e * x e := mul_self_pos.mpr he
    have hi : 0 < Incidence.unsigned left right e v := by
      unfold Incidence.unsigned
      split_ifs <;> norm_num; tauto
    rw [mul_assoc]
    exact mul_pos hi hsq
  have hex : ∃ f, Incidence.unsigned left right f v * x f * x e < 0 := by
    by_contra! hn
    have hle := Finset.single_le_sum (fun f (_ : f ∈ (Finset.univ : Finset E)) => hn f)
      (Finset.mem_univ e)
    linarith
  obtain ⟨f, hf⟩ := hex
  refine ⟨f, ?_, ?_⟩
  · by_contra! hn
    simp [Incidence.unsigned, hn.1, hn.2] at hf
  · have hi : 0 ≤ Incidence.unsigned left right f v := by
      unfold Incidence.unsigned
      positivity
    by_contra! h
    have hn := mul_nonneg hi h
    nlinarith


omit [DecidableEq E] [Fintype V] in
/-- Every supported arc in the signed graph has a supported successor. -/
theorem supported_successor (left right : E → V) (x : E → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (a : Arc (KernelBasis.columns left right (rationalSign x))) (ha : x a.val.1 ≠ 0) :
    ∃ b : Arc (KernelBasis.columns left right (rationalSign x)),
      x b.val.1 ≠ 0 ∧ source _ b = target _ a := by
  rcases a with ⟨⟨e, dir⟩, haCol⟩
  let v := if dir then left e else right e
  have hv : v = left e ∨ v = right e := by cases dir <;> simp [v]
  obtain ⟨f, hf, hneg⟩ := opposite_incident left right x hx e v hv ha
  have hfne : x f ≠ 0 := by intro h; simp [h] at hneg
  have hsign := sign_opposite x e f hneg
  rcases hf with hleft | hright
  · let b : Arc (KernelBasis.columns left right (rationalSign x)) :=
      ⟨(f, false), Or.inr rfl⟩
    refine ⟨b, hfne, ?_⟩
    cases dir <;> cases heq : rationalSign x e <;> cases hfq : rationalSign x f <;>
      simp_all [b, source, target, KernelBasis.columns, opposite, v]
  · let b : Arc (KernelBasis.columns left right (rationalSign x)) :=
      ⟨(f, true), Or.inl (by simp [KernelBasis.columns])⟩
    refine ⟨b, hfne, ?_⟩
    cases dir <;> cases heq : rationalSign x e <;> cases hfq : rationalSign x f <;>
      simp_all [b, source, target, KernelBasis.columns, opposite, v]

/-- Extract a bounded nonempty signed cycle directly from rational support. -/
theorem support_cycle (left right : E → V) (x : E → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) (hne : x ≠ 0) :
    ∃ c : ClosedWalk (KernelBasis.columns left right (rationalSign x)),
      c.2.labels ≠ [] ∧ (∀ e ∈ c.2.labels, x e ≠ 0) ∧
      (∀ e, projection c.2.labels e ≤ 2) ∧
      c.2.labels.length ≤ 2 * Fintype.card V + 1 := by
  classical
  let C := KernelBasis.columns left right (rationalSign x)
  have hex : ∃ e, x e ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨e, he⟩ := hex
  let a : Arc C := ⟨(e, false), Or.inr rfl⟩
  obtain ⟨u, p, hp, hpne, hpnd, hlen, hsupp⟩ := SupportCycle.exists_supported_cycle
    (source C) (target C) (fun a => x a.val.1 ≠ 0) ⟨a, he⟩
    (supported_successor left right x hx)
  obtain ⟨w, hw⟩ := BoundedCycles.walk_of_arcs C p hp
  refine ⟨⟨u, w⟩, ?_, ?_, ?_, ?_⟩
  · rw [BoundedCycles.labels_eq_map_arcs, hw]
    simpa using hpne
  · intro f hf
    rw [BoundedCycles.labels_eq_map_arcs, hw] at hf
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf
    exact hsupp b hb
  · intro f
    apply BoundedCycles.projection_le_two C w
    rw [hw]
    exact List.Nodup.of_map (target C) hpnd
  · rw [BoundedCycles.labels_eq_map_arcs, hw, List.length_map]
    simpa [Walks.state_card, Nat.mul_comm] using hlen

/-- A nonzero bounded integer kernel vector supported on the given rational
kernel vector. Its construction uses only the support graph. -/
theorem support_generator (left right : E → V) (x : E → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) (hne : x ≠ 0) :
    ∃ g : E → ℤ, KernelBasis.IntegralKernel left right g ∧
      (∀ e, |g e| ≤ 2) ∧ g ≠ 0 ∧ ∀ e, x e = 0 → g e = 0 := by
  obtain ⟨c, hcne, hsupp, hb, _⟩ := support_cycle left right x hx hne
  let g : E → ℤ := fun e => signValue (rationalSign x e) * (projection c.2.labels e : ℤ)
  refine ⟨g, KernelBasis.signed_projection_kernel left right (rationalSign x) c,
    KernelBasis.signed_projection_bound _ _ hb, ?_, ?_⟩
  · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil c.2.labels hcne
    have hp : 0 < projection c.2.labels e := List.count_pos_iff.mpr he
    intro hg
    have hge := congrFun hg e
    cases rationalSign x e <;> simp [g, signValue] at hge <;> omega
  · intro e he
    have hnot : e ∉ c.2.labels := fun h => hsupp e h he
    have hp : projection c.2.labels e = 0 := List.count_eq_zero.mpr hnot
    simp [g, hp]

/-- The nonzero-coordinate support used as the elimination measure. -/
def support (x : E → ℚ) : Finset E := Finset.univ.filter fun e => x e ≠ 0

omit [DecidableEq E] in
@[simp] theorem mem_support (x : E → ℚ) (e : E) : e ∈ support x ↔ x e ≠ 0 := by
  simp [support]

/-- Rational multiples of bounded integral kernel vectors. -/
abbrev Term (E : Type*) := ℚ × (E → ℤ)

/-- The rational vector represented by one term. -/
def termVector (t : Term E) : E → ℚ := fun e => t.1 * (t.2 e : ℚ)

/-- Successive support elimination uses at most one bounded generator per
original nonzero coordinate. No coordinate-magnitude measure is used. -/
theorem sparse_decomposition (left right : E → V) (x : E → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) :
    ∃ ts : List (Term E),
      (ts.map termVector).sum = x ∧ ts.length ≤ (support x).card ∧
      ∀ t ∈ ts, KernelBasis.IntegralKernel left right t.2 ∧ ∀ e, |t.2 e| ≤ 2 := by
  classical
  by_cases hzero : x = 0
  · subst x
    exact ⟨[], by simp, by simp, by simp⟩
  · obtain ⟨g, hg, hb, hgne, hsup⟩ := support_generator left right x hx hzero
    obtain ⟨e, he⟩ : ∃ e, g e ≠ 0 := by
      by_contra! h
      exact hgne (funext h)
    have hge : (g e : ℚ) ≠ 0 := by exact_mod_cast he
    let a : ℚ := x e / (g e : ℚ)
    let r : E → ℚ := x - a • (fun f => (g f : ℚ))
    have hr : r ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin :=
      (LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin).sub_mem hx
        ((LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin).smul_mem a
          ((KernelBasis.integralKernel_iff left right g).mp hg))
    have hre : r e = 0 := by simp [r, a, div_mul_cancel₀ _ hge]
    have hxe : x e ≠ 0 := fun h => he (hsup e h)
    have hsubset : support r ⊆ support x := by
      intro f hf
      simp only [mem_support] at hf ⊢
      intro hxf
      have hgf := hsup f hxf
      exact hf (by simp [r, hxf, hgf])
    have hlt : (support r).card < (support x).card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
      intro heq
      have hmem : e ∈ support r := heq.symm ▸ (mem_support x e).mpr hxe
      exact (mem_support r e).mp hmem hre
    obtain ⟨ts, hts, hlen, hbounded⟩ := sparse_decomposition left right r hr
    refine ⟨(a, g) :: ts, ?_, by simp only [List.length_cons]; omega, ?_⟩
    · rw [List.map_cons, List.sum_cons, hts]
      ext f
      simp [termVector, r]
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨hg, hb⟩
      · exact hbounded t ht
termination_by (support x).card

omit [DecidableEq E] [Fintype E] in
/-- A sum of terms belongs to every subspace containing their integral rows. -/
theorem term_sum_mem (P : Submodule ℚ (E → ℚ)) (ts : List (Term E))
    (h : ∀ t ∈ ts, (fun e => (t.2 e : ℚ)) ∈ P) : (ts.map termVector).sum ∈ P := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      rw [List.map_cons, List.sum_cons]
      apply P.add_mem
      · convert P.smul_mem t.1 (h t List.mem_cons_self) using 1
        ext e
        simp [termVector]
      · exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht))

/-- The rational vectors represented by a list of integral rows. -/
def generators (gs : List (E → ℤ)) : Set (E → ℚ) :=
  {u | ∃ g ∈ gs, u = fun e => (g e : ℚ)}

/-- A rational kernel-spanning family with `r` members yields at most `m*r`
bounded integral generators, where `m` is the number of edges. -/
theorem sparse_spanning_family {I : Type*} [Fintype I]
    (left right : E → V) (xs : I → E → ℚ)
    (hspan : Submodule.span ℚ (Set.range xs) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) :
    ∃ gs : List (E → ℤ), gs.length ≤ Fintype.card E * Fintype.card I ∧
      (∀ g ∈ gs, KernelBasis.IntegralKernel left right g ∧ ∀ e, |g e| ≤ 2) ∧
      Submodule.span ℚ (generators gs) =
        LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  classical
  have hx (i : I) : xs i ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose ts heq hlen hb using fun i => sparse_decomposition left right (xs i) (hx i)
  let gs : List (E → ℤ) := Finset.univ.toList.flatMap (fun i => (ts i).map Prod.snd)
  have hmem (i : I) (t : Term E) (ht : t ∈ ts i) : t.2 ∈ gs := by
    apply List.mem_flatMap.mpr
    exact ⟨i, by simp, List.mem_map.mpr ⟨t, ht, rfl⟩⟩
  have hbound : ∀ g ∈ gs, KernelBasis.IntegralKernel left right g ∧ ∀ e, |g e| ≤ 2 := by
    intro g hg
    obtain ⟨i, _, hgi⟩ := List.mem_flatMap.mp hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hgi
    exact hb i t ht
  refine ⟨gs, ?_, hbound, ?_⟩
  · have hle (l : List I) :
        (l.flatMap (fun i => (ts i).map Prod.snd)).length ≤ l.length * Fintype.card E := by
      induction l with
      | nil => simp
      | cons i l ih =>
          have hcard : (support (xs i)).card ≤ Fintype.card E := Finset.card_le_univ _
          have hi := hlen i
          simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
          nlinarith
    simpa only [gs, Finset.length_toList, Finset.card_univ, Nat.mul_comm] using hle Finset.univ.toList
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro u ⟨g, hg, rfl⟩
      exact (KernelBasis.integralKernel_iff left right g).mp (hbound g hg).1
    · rw [← hspan]
      apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      rw [← heq i]
      apply term_sum_mem
      intro t ht
      exact Submodule.subset_span ⟨t.2, hmem i t ht, rfl⟩

/-- A bounded complement can be selected from the sparse generated family,
which has at most the edge count times the input family size many rows. -/
theorem sparse_complement {I : Type*} [Fintype I]
    (left right : E → V) (xs : I → E → ℚ)
    (hspan : Submodule.span ℚ (Set.range xs) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (P : Submodule ℚ (E → ℚ))
    (hP : P ≤ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) :
    ∃ gs : List (E → ℤ), gs.length ≤ Fintype.card E * Fintype.card I ∧
      ∃ W : Fin (Module.finrank ℚ (LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) -
          Module.finrank ℚ P) → E → ℤ,
        (∀ i, W i ∈ gs ∧ KernelBasis.IntegralKernel left right (W i) ∧ ∀ e, |W i e| ≤ 2) ∧
        P ⊔ Submodule.span ℚ (Set.range (fun i e => (W i e : ℚ))) =
          LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  obtain ⟨gs, hlen, hb, hgs⟩ := sparse_spanning_family left right xs hspan
  obtain ⟨f, hf, hcomp⟩ := Complement.exists_fin_complement P _ hP (generators gs) hgs
  simp only [generators, Set.mem_ofPred_eq] at hf
  choose W hW heq using hf
  have hfeq : f = fun i e => (W i e : ℚ) := funext heq
  rw [hfeq] at hcomp
  exact ⟨gs, hlen, W, fun i => ⟨hW i, hb (W i) (hW i)⟩, hcomp⟩

end WeightedMIS.SparseKernel
