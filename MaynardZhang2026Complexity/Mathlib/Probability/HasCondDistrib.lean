/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.MapComap
public import MaynardZhang2026Complexity.Mathlib.Probability.Kernel.Composition.CompProd
public import MaynardZhang2026Complexity.Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Lemmas on conditional distributions

General facts about Mathlib's `HasCondDistrib`, complementing LML's
`LeanMachineLearning.ForMathlib.Probability.HasCondDistrib`.

## Main statements

* `HasCondDistrib.comp_hasLaw`, `HasCondDistrib.of_comp_hasLaw`: a conditional distribution is
  transported along a map `g` carrying `P` to `P'`, and conversely;
* `HasCondDistrib.const_comp_right`: a constant conditional law given `Z` is a constant
  conditional law given any measurable function of `Z`;
* `HasLaw.hasCondDistrib_snd_const`: if `(X, Y)` has law `Q ⊗ R`, then `Y` has the constant
  conditional law `R` given `X`;
* `HasCondDistrib.map_id_prod_const`: if `Y` has the constant conditional law `Q` given `X`, then
  `f (X, Y)` has conditional law `(Kernel.id ×ₖ Kernel.const _ Q).map f` given `X`;
* `HasCondDistrib.snd_of_const_prod`: if `(Y, Z)` has the constant conditional law `Q ⊗ R` given
  `X`, then `Z` has the constant conditional law `R` given `(X, Y)`;
* `hasCondDistrib_snd_compProd`, `hasCondDistrib_snd_compProd_comap`: the conditional law of the
  second coordinate under `μ ⊗ₘ κ` and `μ ⊗ₘ η.comap f`;
* `HasCondDistrib.compProd_left_of_sectR`, `HasCondDistrib.compProd_left`: if `Y` has conditional
  law `η (a, ·)` given `X` under every `κ a`, then under `μ ⊗ₘ κ` the variable `Y ∘ snd` has
  conditional law `η` given `(fst, X ∘ snd)`;
* `HasCondDistrib.map_of_forall_map_eq`: if `Y` has conditional law `κ` given `X`, then
  `F X Y` has conditional law `K` given `G X` when `K (G a) = (κ a).map (F a)`;
* `HasCondDistrib.restrict_preimage`: a conditional law given `X` is preserved by restricting the
  measure to an event determined by `X`;
* `HasCondDistrib.measureReal_le_mul`, `HasCondDistrib.measureReal_sub_le`: a uniform bound on
  the conditional probability of an event given `Z` bounds its probability;
* `HasCondDistrib.lintegral_prodMk`, `HasCondDistrib.integral_prodMk`: the integral of a function
  of `(X, Y)` is the integral of its integral against the conditional law of `Y` given `X`, and
  `hasCondDistrib_of_lintegral_eq`: this characterizes the conditional law;
* `HasCondDistrib.condExp_comap_ae_eq_integral`: `𝔼[f (X, Y) | σ(X)] = ∫ f (X, y) dκ(X)` almost
  surely for bounded measurable `f` (no standard Borel assumption, unlike Mathlib's
  `condExp_prod_ae_eq_integral_condDistrib`);
* `HasCondDistrib.congr_kernel`: the conditional law can be replaced by a kernel agreeing with it
  on a measurable set containing the conditioning variable almost surely;
* `HasCondDistrib.prodMk_right_of_comap_fst`: conditioning on a conditionally independent variable
  changes nothing;
* `HasCondDistrib.map_prodMk`: recording a measurable function of the conditioning variable and of
  the random variable.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

section transport

variable {Ω Ω' 𝓧 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓩 : MeasurableSpace 𝓩} {P : Measure Ω} {P' : Measure Ω'}
  {g : Ω → Ω'}

/-- A conditional distribution is transported along a map `g` carrying `P` to `P'`. -/
lemma HasCondDistrib.comp_hasLaw {X : Ω' → 𝓧} {Z : Ω' → 𝓩}
    {κ : Kernel 𝓧 𝓩} (h : HasCondDistrib Z X κ P') (hg : HasLaw g P' P) :
    HasCondDistrib (Z ∘ g) (X ∘ g) κ P := by
  have h' : HasLaw ((fun ω ↦ (X ω, Z ω)) ∘ g) (P'.map X ⊗ₘ κ) P := HasLaw.comp h hg
  have hX : P'.map X = P.map (X ∘ g) := by
    rw [← hg.map_eq, AEMeasurable.map_map_of_aemeasurable (hg.map_eq ▸ h.aemeasurable_fst)
      hg.aemeasurable]
  rw [hX] at h'
  exact h'

/-- A conditional distribution of `Z ∘ g` given `X ∘ g` under `P` is a conditional distribution
of `Z` given `X` under the law `P'` of `g`. -/
lemma HasCondDistrib.of_comp_hasLaw {X : Ω' → 𝓧} {Z : Ω' → 𝓩} {κ : Kernel 𝓧 𝓩}
    (hX : Measurable X) (hZ : Measurable Z) (hg : HasLaw g P' P)
    (h : HasCondDistrib (Z ∘ g) (X ∘ g) κ P) :
    HasCondDistrib Z X κ P' := by
  refine ⟨(hX.prodMk hZ).aemeasurable, ?_⟩
  have h1 : P'.map (fun ω ↦ (X ω, Z ω)) = P.map ((fun ω ↦ (X ω, Z ω)) ∘ g) := by
    rw [← hg.map_eq,
      AEMeasurable.map_map_of_aemeasurable (hX.prodMk hZ).aemeasurable hg.aemeasurable]
  have h2 : P'.map X = P.map (X ∘ g) := by
    rw [← hg.map_eq, AEMeasurable.map_map_of_aemeasurable hX.aemeasurable hg.aemeasurable]
  rw [h1, h2]
  exact h.map_eq

end transport

section const

variable {Ω 𝓧 𝓨 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩} {P : Measure Ω} {X : Ω → 𝓧} {Y : Ω → 𝓨}

/-- A constant conditional law given `Z` is a constant conditional law given any measurable
function of `Z`. -/
lemma HasCondDistrib.const_comp_right [SFinite P] {ν : Measure 𝓨} [SFinite ν] {Z : Ω → 𝓩}
    (h : HasCondDistrib Y Z (Kernel.const 𝓩 ν) P) {f : 𝓩 → 𝓧} (hf : Measurable f) :
    HasCondDistrib Y (f ∘ Z) (Kernel.const 𝓧 ν) P := by
  refine HasCondDistrib.comp_right (hf := hf) ?_
  rwa [Kernel.comap_const]

/-- If `(X, Y)` has law `Q ⊗ R`, then the conditional law of `Y` given `X` is the constant
kernel `R`. -/
lemma HasLaw.hasCondDistrib_snd_const [IsFiniteMeasure P] {Q : Measure 𝓧} {R : Measure 𝓨}
    [IsProbabilityMeasure R] (h : HasLaw (fun ω ↦ (X ω, Y ω)) (Q.prod R) P) :
    HasCondDistrib Y X (Kernel.const 𝓧 R) P := by
  unfold HasCondDistrib
  rw [Measure.compProd_const]
  have hX : P.map X = Q := by
    rw [← Measure.fst_map_prodMk₀ h.aemeasurable.fst h.aemeasurable.snd, h.map_eq, Measure.fst_prod]
  rw [hX]
  exact h

/-- If the conditional law of `Y` given `X` is the constant `Q`, then the conditional law of
`f (X, Y)` given `X` is the kernel `x ↦ Q.map (f (x, ·))`, drawing a fresh `y ∼ Q` and returning
`f (x, y)`. -/
lemma HasCondDistrib.map_id_prod_const [SFinite P] {Q : Measure 𝓨} [SFinite Q]
    (h : HasCondDistrib Y X (Kernel.const 𝓧 Q) P) {f : 𝓧 × 𝓨 → 𝓩} (hf : Measurable f) :
    HasCondDistrib (fun ω ↦ f (X ω, Y ω)) X ((Kernel.id ×ₖ Kernel.const 𝓧 Q).map f) P := by
  have hX := h.aemeasurable_fst
  have hY := h.aemeasurable_snd
  refine ⟨by fun_prop, ?_⟩
  have h1 := h.map_eq
  rw [Measure.compProd_const] at h1
  calc P.map (fun ω ↦ (X ω, f (X ω, Y ω)))
      = (P.map (fun ω ↦ (X ω, Y ω))).map (fun p ↦ (p.1, f p)) := by
        rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
        rfl
    _ = ((P.map X).prod Q).map (fun p ↦ (p.1, f p)) := by rw [h1]
    _ = P.map X ⊗ₘ (Kernel.id ×ₖ Kernel.const 𝓧 Q).map f :=
        (Measure.compProd_map_id_prod_const _ Q hf).symm

/-- If the conditional law of `(Y, Z)` given `X` is the constant `Q ⊗ R`, then the conditional
law of `Z` given `(X, Y)` is the constant `R`. -/
lemma HasCondDistrib.snd_of_const_prod [SFinite P] {Z : Ω → 𝓩} {Q : Measure 𝓨} {R : Measure 𝓩}
    [SFinite Q] [IsProbabilityMeasure R]
    (h : HasCondDistrib (fun ω ↦ (Y ω, Z ω)) X (Kernel.const 𝓧 (Q.prod R)) P) :
    HasCondDistrib Z (fun ω ↦ (X ω, Y ω)) (Kernel.const (𝓧 × 𝓨) R) P := by
  rw [← Kernel.const_compProd_const] at h
  exact h.of_compProd

end const

section compProd

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- Under `μ ⊗ₘ η.comap f`, the second coordinate has conditional law `η` given `f` of the
first coordinate, when `η` is a probability measure at every point of the range of `f`. -/
lemma hasCondDistrib_snd_compProd_comap (μ : Measure α) [SFinite μ]
    (η : Kernel β γ) [IsSFiniteKernel η] {f : α → β} (hf : Measurable f)
    (hη : ∀ a, IsProbabilityMeasure (η (f a))) :
    HasCondDistrib Prod.snd (fun p : α × γ ↦ f p.1) η (μ ⊗ₘ η.comap f hf) := by
  have : IsMarkovKernel (η.comap f hf) := ⟨fun a ↦ by rw [Kernel.comap_apply]; exact hη a⟩
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.map_prodMk_compProd_comap μ η hf]
  congr 1
  conv_lhs => rw [← Measure.fst_compProd μ (η.comap f hf)]
  rw [Measure.fst, Measure.map_map hf measurable_fst]
  rfl

/-- Under `μ ⊗ₘ κ`, the second coordinate has conditional law `κ` given the first. -/
lemma hasCondDistrib_snd_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsMarkovKernel κ] :
    HasCondDistrib Prod.snd Prod.fst κ (μ ⊗ₘ κ) where
  aemeasurable := by fun_prop
  map_eq := by
    rw [show (fun p : α × β ↦ (p.1, p.2)) = id from rfl, Measure.map_id,
      show (μ ⊗ₘ κ).map Prod.fst = (μ ⊗ₘ κ).fst from rfl, Measure.fst_compProd]

variable {δ : Type*} {mδ : MeasurableSpace δ}

/-- If `Y` has conditional law `η.sectR a` given `X` under every `κ a`, then under `μ ⊗ₘ κ` the
variable `Y ∘ snd` has conditional law `η` given `(fst, X ∘ snd)`. -/
lemma HasCondDistrib.compProd_left_of_sectR {μ : Measure α} [SFinite μ] {κ : Kernel α β}
    [IsMarkovKernel κ] {X : β → γ} {Y : β → δ} {η : Kernel (α × γ) δ} [IsSFiniteKernel η]
    (hX : Measurable X) (hY : Measurable Y) (h : ∀ a, HasCondDistrib Y X (η.sectR a) (κ a)) :
    HasCondDistrib (fun p ↦ Y p.2) (fun p ↦ (p.1, X p.2)) η (μ ⊗ₘ κ) where
  aemeasurable := by fun_prop
  map_eq := by
    have hκ : κ.map (fun b ↦ (X b, Y b)) = κ.map X ⊗ₖ η := by
      ext a : 1
      rw [Kernel.map_apply _ (hX.prodMk hY), (h a).map_eq,
        Kernel.compProd_apply_eq_compProd_sectR, Kernel.map_apply _ hX]
    calc (μ ⊗ₘ κ).map (fun p ↦ ((p.1, X p.2), Y p.2))
        = ((μ ⊗ₘ κ).map (fun p ↦ (p.1, (X p.2, Y p.2)))).map
            MeasurableEquiv.prodAssoc.symm := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
      _ = (μ ⊗ₘ κ.map (fun b ↦ (X b, Y b))).map MeasurableEquiv.prodAssoc.symm := by
          rw [Measure.compProd_map (hX.prodMk hY)]; rfl
      _ = (μ ⊗ₘ κ.map X) ⊗ₘ η := by
          rw [hκ, Measure.compProd_assoc]
      _ = ((μ ⊗ₘ κ).map (fun p ↦ (p.1, X p.2))) ⊗ₘ η := by
          rw [Measure.compProd_map hX]; rfl

/-- If `Y` has conditional law `η` given `X` under every `κ a`, then under `μ ⊗ₘ κ` the variable
`Y ∘ snd` has conditional law `η` given `(fst, X ∘ snd)`. -/
lemma HasCondDistrib.compProd_left {μ : Measure α} [SFinite μ] {κ : Kernel α β}
    [IsMarkovKernel κ] {X : β → γ} {Y : β → δ} {η : Kernel γ δ} [IsSFiniteKernel η]
    (hX : Measurable X) (hY : Measurable Y) (h : ∀ a, HasCondDistrib Y X η (κ a)) :
    HasCondDistrib (fun p ↦ Y p.2) (fun p ↦ (p.1, X p.2)) (Kernel.prodMkLeft α η) (μ ⊗ₘ κ) :=
  compProd_left_of_sectR hX hY fun a ↦ by rw [Kernel.sectR_prodMkLeft]; exact h a

end compProd

section map

variable {Ω α β γ δ : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {P : Measure Ω}
  [SFinite P] {X : Ω → α} {Y : Ω → β} {κ : Kernel α β} [IsSFiniteKernel κ]

/-- If `Y` has conditional law `κ` given `X`, then `F X Y` has conditional law `K` given `G X`
as soon as `K (G a)` is the image of `κ a` by `F a` for every `a`. -/
lemma HasCondDistrib.map_of_forall_map_eq (h : HasCondDistrib Y X κ P) {G : α → γ}
    (hG : Measurable G) {F : α → β → δ} (hF : Measurable (Function.uncurry F)) (K : Kernel γ δ)
    [IsSFiniteKernel K] (hK : ∀ a, K (G a) = (κ a).map (F a)) :
    HasCondDistrib (fun ω ↦ F (X ω) (Y ω)) (G ∘ X) K P := by
  refine ⟨(hG.comp_aemeasurable h.aemeasurable_fst).prodMk (hF.comp_aemeasurable h.aemeasurable),
    ?_⟩
  have hφ : Measurable fun p : α × β ↦ (G p.1, F p.1 p.2) := (hG.comp measurable_fst).prodMk hF
  calc P.map (fun ω ↦ ((G ∘ X) ω, F (X ω) (Y ω)))
      = (P.map (fun ω ↦ (X ω, Y ω))).map (fun p ↦ (G p.1, F p.1 p.2)) := by
        rw [AEMeasurable.map_map_of_aemeasurable hφ.aemeasurable h.aemeasurable]
        rfl
    _ = (P.map X ⊗ₘ κ).map (fun p ↦ (G p.1, F p.1 p.2)) := by rw [h.map_eq]
    _ = (P.map X).map G ⊗ₘ K := Measure.map_compProd_of_forall_map_eq _ _ hG hF K hK
    _ = P.map (G ∘ X) ⊗ₘ K := by
        rw [AEMeasurable.map_map_of_aemeasurable hG.aemeasurable h.aemeasurable_fst]

/-- A conditional law given `X` is a conditional law given `(c, X)` for any constant `c`. -/
lemma HasCondDistrib.prodMk_const_left (h : HasCondDistrib Y X κ P) (c : γ) :
    HasCondDistrib Y (fun ω ↦ (c, X ω)) (κ.prodMkLeft γ) P :=
  h.map_of_forall_map_eq (G := fun a ↦ (c, a)) (by fun_prop) (F := fun _ b ↦ b) measurable_snd _
    fun a ↦ by simp [Kernel.prodMkLeft_apply]

/-- A conditional law given `X` is a conditional law given `X` under the restriction of `P` to an
event determined by `X`. -/
lemma HasCondDistrib.restrict_preimage (hX : Measurable X) (hY : Measurable Y)
    (h : HasCondDistrib Y X κ P) {s : Set α} (hs : MeasurableSet s) :
    HasCondDistrib Y X κ (P.restrict (X ⁻¹' s)) := by
  refine ⟨(hX.prodMk hY).aemeasurable, ?_⟩
  have h1 : (fun ω ↦ (X ω, Y ω)) ⁻¹' (s ×ˢ Set.univ) = X ⁻¹' s := by ext ω; simp
  calc (P.restrict (X ⁻¹' s)).map (fun ω ↦ (X ω, Y ω))
      = (P.map (fun ω ↦ (X ω, Y ω))).restrict (s ×ˢ Set.univ) := by
        rw [Measure.restrict_map (hX.prodMk hY) (hs.prod MeasurableSet.univ), h1]
    _ = (P.map X ⊗ₘ κ).restrict (s ×ˢ Set.univ) := by rw [h.map_eq]
    _ = (P.map X).restrict s ⊗ₘ κ := Measure.restrict_compProd_prod_univ _ _ hs
    _ = (P.restrict (X ⁻¹' s)).map X ⊗ₘ κ := by rw [Measure.restrict_map hX hs]

end map

section bound

variable {Ω β 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β}
  {m𝓩 : MeasurableSpace 𝓩} {P : Measure Ω} [IsFiniteMeasure P] {W : Ω → β} {Z : Ω → 𝓩}
  {κ : Kernel 𝓩 β} {G : Set 𝓩} {G' : Set (𝓩 × β)} {δ : ℝ}

/-- If the conditional law of `W` given `Z` is `κ` and, for every `z` in the measurable set `G`,
the section of the measurable set `G'` at `z` has `κ z`-probability at most `δ`, then
`P(Z ∈ G, (Z, W) ∈ G') ≤ δ P(Z ∈ G)`. -/
lemma HasCondDistrib.measureReal_le_mul [IsFiniteKernel κ] (h : HasCondDistrib W Z κ P)
    (hG : MeasurableSet G) (hG' : MeasurableSet G') (hδ0 : 0 ≤ δ)
    (hδ : ∀ z ∈ G, (κ z).real (Prod.mk z ⁻¹' G') ≤ δ) :
    P.real (Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G') ≤ δ * P.real (Z ⁻¹' G) := by
  have hS : MeasurableSet ((G ×ˢ Set.univ) ∩ G') := (hG.prod MeasurableSet.univ).inter hG'
  have h1 : Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G' =
      (fun ω ↦ (Z ω, W ω)) ⁻¹' ((G ×ˢ Set.univ) ∩ G') := by
    ext ω
    simp
  have h2 : ∀ z, κ z (Prod.mk z ⁻¹' ((G ×ˢ Set.univ) ∩ G')) =
      G.indicator (fun z ↦ κ z (Prod.mk z ⁻¹' G')) z := fun z ↦ by
    by_cases hz : z ∈ G
    · rw [Set.indicator_of_mem hz]
      congr 1
      ext w
      simp [hz]
    · rw [Set.indicator_of_notMem hz]
      convert measure_empty (μ := κ z)
      ext w
      simp [hz]
  rw [h1, measureReal_def, measureReal_def,
    ← Measure.map_apply_of_aemeasurable h.aemeasurable_fst hG,
    ← Measure.map_apply_of_aemeasurable h.aemeasurable hS, h.map_eq, Measure.compProd_apply hS]
  simp_rw [h2]
  rw [lintegral_indicator hG, ← ENNReal.toReal_ofReal hδ0, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) ?_
  rw [← setLIntegral_const]
  refine setLIntegral_mono' hG fun z hz ↦ ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top (κ z) _)]
  exact ENNReal.ofReal_le_ofReal (hδ z hz)

/-- If the conditional law of `W` given `Z` is `κ` and, for every `z` in the measurable set `G`,
the section of the measurable set `G'` at `z` has `κ z`-probability at least `1 - δ`, then
`P((Z, W) ∈ G') ≥ P(Z ∈ G) - δ`. -/
lemma HasCondDistrib.measureReal_sub_le [IsProbabilityMeasure P] [IsMarkovKernel κ]
    (h : HasCondDistrib W Z κ P) (hG : MeasurableSet G) (hG' : MeasurableSet G') (hδ0 : 0 ≤ δ)
    (hδ : ∀ z ∈ G, 1 - δ ≤ (κ z).real (Prod.mk z ⁻¹' G')) :
    P.real (Z ⁻¹' G) - δ ≤ P.real ((fun ω ↦ (Z ω, W ω)) ⁻¹' G') := by
  have h1 := h.measureReal_le_mul hG hG'.compl hδ0 fun z hz ↦ by
    rw [Set.preimage_compl, measureReal_compl (measurable_prodMk_left hG'), probReal_univ]
    linarith [hδ z hz]
  have h2 : P.real (Z ⁻¹' G) ≤ P.real (Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G') +
      P.real (Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G'ᶜ) := by
    refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
    intro ω hω
    by_cases hω' : (Z ω, W ω) ∈ G' <;> simp [hω]
  have h3 : P.real (Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G') ≤
      P.real ((fun ω ↦ (Z ω, W ω)) ⁻¹' G') := measureReal_mono Set.inter_subset_right
  have h4 : δ * P.real (Z ⁻¹' G) ≤ δ := by
    calc δ * P.real (Z ⁻¹' G) ≤ δ * 1 := by gcongr; exact measureReal_le_one
      _ = δ := mul_one δ
  linarith

end bound

section integral

variable {Ω α β : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {P : Measure Ω} {X : Ω → α} {Y : Ω → β} {κ : Kernel α β}

/-- The Lebesgue integral of a function of `(X, Y)` is the integral of its integral against the
conditional law of `Y` given `X`. -/
lemma HasCondDistrib.lintegral_prodMk [SFinite P] [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (X ω, Y ω) ∂P = ∫⁻ ω, ∫⁻ b, f (X ω, b) ∂κ (X ω) ∂P := by
  rw [HasLaw.lintegral_comp h hf.aemeasurable, Measure.lintegral_compProd hf,
    lintegral_map' (hf.lintegral_kernel_prod_right').aemeasurable h.aemeasurable_fst]

/-- The integral of a function of `(X, Y)` is the integral of its integral against the
conditional law of `Y` given `X`. -/
lemma HasCondDistrib.integral_prodMk [SFinite P] [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α × β → E} (hfm : StronglyMeasurable f) (hf : Integrable f (P.map X ⊗ₘ κ)) :
    ∫ ω, f (X ω, Y ω) ∂P = ∫ ω, ∫ b, f (X ω, b) ∂κ (X ω) ∂P := by
  have h1 := HasLaw.integral_comp h hf.aestronglyMeasurable
  simp only [Function.comp_def] at h1
  rw [h1, Measure.integral_compProd hf, integral_map h.aemeasurable_fst]
  exact hfm.integral_kernel_prod_right'.aestronglyMeasurable

/-- A kernel `κ` is the conditional law of `Y` given `X` if the integral of every nonnegative
measurable function of `(X, Y)` is the integral of its integral against `κ (X ω)`. -/
lemma hasCondDistrib_of_lintegral_eq [IsFiniteMeasure P] [IsSFiniteKernel κ]
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h : ∀ f : α × β → ℝ≥0∞, Measurable f →
      ∫⁻ ω, f (X ω, Y ω) ∂P = ∫⁻ ω, ∫⁻ b, f (X ω, b) ∂κ (X ω) ∂P) :
    HasCondDistrib Y X κ P := by
  refine ⟨hX.prodMk hY, ?_⟩
  ext B hB
  rw [Measure.compProd_apply hB,
    lintegral_map' (Kernel.measurable_kernel_prodMk_left hB).aemeasurable hX,
    ← lintegral_indicator_one hB, lintegral_map' (measurable_one.indicator hB).aemeasurable
      (hX.prodMk hY), h _ (measurable_one.indicator hB)]
  refine lintegral_congr fun ω ↦ ?_
  rw [← lintegral_indicator_one (measurable_prodMk_left hB)]
  rfl

/-- If `Y` has conditional law `κ` given `X`, then for a bounded measurable function `f`,
`𝔼[f (X, Y) | σ(X)] = ∫ f (X, y) dκ(X)` almost surely. Unlike Mathlib's
`condExp_prod_ae_eq_integral_condDistrib`, no standard Borel assumption is needed on the space of
`Y`: the kernel `κ` is given. -/
lemma HasCondDistrib.condExp_comap_ae_eq_integral [IsFiniteMeasure P] [IsMarkovKernel κ]
    (h : HasCondDistrib Y X κ P) (hX : Measurable X) {f : α × β → ℝ} (hf : StronglyMeasurable f)
    {C : ℝ} (hfC : ∀ z, |f z| ≤ C) :
    P[fun ω ↦ f (X ω, Y ω) | mα.comap X] =ᵐ[P] fun ω ↦ ∫ y, f (X ω, y) ∂κ (X ω) := by
  have hg : StronglyMeasurable fun a ↦ ∫ y, f (a, y) ∂κ a := hf.integral_kernel_prod_right'
  have hgC : ∀ a, |∫ y, f (a, y) ∂κ a| ≤ C := fun a ↦ by
    simpa using norm_integral_le_of_norm_le_const (μ := κ a) (f := fun y ↦ f (a, y))
      (C := C) (.of_forall fun y ↦ by simpa using hfC (a, y))
  have hint : Integrable (fun ω ↦ f (X ω, Y ω)) P :=
    Integrable.of_bound (hf.aestronglyMeasurable.comp_aemeasurable h.aemeasurable) C
      (.of_forall fun ω ↦ by simpa using hfC _)
  have hgm : StronglyMeasurable[mα.comap X] fun ω ↦ ∫ y, f (X ω, y) ∂κ (X ω) :=
    hg.comp_measurable (comap_measurable X)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hint
    (fun s _ _ ↦ (Integrable.of_bound (hgm.mono hX.comap_le).aestronglyMeasurable C
      (.of_forall fun ω ↦ by simpa using hgC _)).integrableOn) (fun s hs _ ↦ ?_)
    hgm.aestronglyMeasurable).symm
  obtain ⟨B, hB, rfl⟩ := hs
  set F : α × β → ℝ := fun z ↦ B.indicator 1 z.1 * f z with hF
  have hFm : StronglyMeasurable F :=
    ((stronglyMeasurable_const.indicator hB).comp_measurable measurable_fst).mul hf
  have hFint : Integrable F ((P.map X) ⊗ₘ κ) := by
    refine Integrable.of_bound hFm.aestronglyMeasurable C (.of_forall fun z ↦ ?_)
    simp only [hF, Real.norm_eq_abs, abs_mul]
    by_cases hz : z.1 ∈ B
    · simpa [hz] using hfC z
    · simpa [hz] using (abs_nonneg _).trans (hfC z)
  rw [← integral_indicator (hX hB), ← integral_indicator (hX hB)]
  calc ∫ ω, (X ⁻¹' B).indicator (fun ω ↦ ∫ y, f (X ω, y) ∂κ (X ω)) ω ∂P
      = ∫ ω, ∫ y, F (X ω, y) ∂κ (X ω) ∂P := by
        refine integral_congr_ae (.of_forall fun ω ↦ ?_)
        by_cases hω : X ω ∈ B <;> simp [hF, hω]
    _ = ∫ ω, F (X ω, Y ω) ∂P := (h.integral_prodMk hFm hFint).symm
    _ = ∫ ω, (X ⁻¹' B).indicator (fun ω ↦ f (X ω, Y ω)) ω ∂P := by
        refine integral_congr_ae (.of_forall fun ω ↦ ?_)
        by_cases hω : X ω ∈ B <;> simp [hF, hω]

end integral

section congr

variable {Ω α β δ : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {mδ : MeasurableSpace δ} {P : Measure Ω} {X : Ω → α} {Y : Ω → β}
  {κ : Kernel α β}

/-- The conditional law of `Y` given `X` is only determined on a set of full measure for the law of
`X`: it can be replaced by any kernel that agrees with it on a measurable set containing `X`
almost surely. -/
lemma HasCondDistrib.congr_kernel [IsSFiniteKernel κ] {κ' : Kernel α β} [IsSFiniteKernel κ']
    (h : HasCondDistrib Y X κ P) {s : Set α} (hs : MeasurableSet s) (hXs : ∀ᵐ ω ∂P, X ω ∈ s)
    (hκ : ∀ x ∈ s, κ x = κ' x) :
    HasCondDistrib Y X κ' P := by
  refine ⟨h.aemeasurable, ?_⟩
  rw [h.map_eq]
  refine Measure.compProd_congr ?_
  have h_ae : ∀ᵐ x ∂(P.map X), x ∈ s := (ae_map_iff h.aemeasurable_fst hs).mpr hXs
  filter_upwards [h_ae] with x hx using hκ x hx

/-- If the conditional distribution of `V` given `(W, Y)` does not depend on `Y` (that is, `V` and
`Y` are conditionally independent given `W`), then the conditional law of `Y` given `(W, V)` is
its conditional law given `W`: observing `V` brings no information about `Y` beyond `W`. -/
lemma HasCondDistrib.prodMk_right_of_comap_fst {W : Ω → α} {V : Ω → δ} {η : Kernel α δ}
    [SFinite P] [IsMarkovKernel κ] [IsMarkovKernel η]
    (h1 : HasCondDistrib Y W κ P)
    (h2 : HasCondDistrib V (fun a ↦ (W a, Y a)) (η.prodMkRight β) P) :
    HasCondDistrib Y (fun a ↦ (W a, V a)) (κ.prodMkRight δ) P := by
  have hW : AEMeasurable W P := h1.aemeasurable_fst
  have hY : AEMeasurable Y P := h1.aemeasurable_snd
  have hV : AEMeasurable V P := h2.aemeasurable_snd
  have hjoint : P.map (fun a ↦ ((W a, Y a), V a)) = (P.map W ⊗ₘ κ) ⊗ₘ η.prodMkRight β := by
    rw [h2.map_eq, h1.map_eq]
  have hswap : ((P.map W ⊗ₘ κ) ⊗ₘ η.prodMkRight β).map (fun p ↦ ((p.1.1, p.2), p.1.2))
      = (P.map W ⊗ₘ η) ⊗ₘ κ.prodMkRight δ :=
    Measure.compProd_comap_fst_comm _ _ _
  have hWV : P.map (fun a ↦ (W a, V a)) = P.map W ⊗ₘ η := by
    have h_eq : (fun a ↦ (W a, V a))
        = Prod.fst ∘ ((fun p : (α × β) × δ ↦ ((p.1.1, p.2), p.1.2))
          ∘ (fun a ↦ ((W a, Y a), V a))) := rfl
    rw [h_eq, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop),
      ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop), hjoint, hswap]
    exact Measure.fst_compProd _ _
  refine ⟨(hW.prodMk hV).prodMk hY, ?_⟩
  have h_eq : (fun a ↦ ((W a, V a), Y a))
      = (fun p : (α × β) × δ ↦ ((p.1.1, p.2), p.1.2)) ∘ (fun a ↦ ((W a, Y a), V a)) := rfl
  rw [h_eq, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop), hjoint, hswap,
    hWV]

/-- Recording a measurable function of the conditioning variable and of the random variable. -/
lemma HasCondDistrib.map_prodMk {F : α × β → δ} [SFinite P] [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) (hF : Measurable F) :
    HasCondDistrib (fun a ↦ F (X a, Y a)) X ((Kernel.id ×ₖ κ).map F) P := by
  refine ⟨h.aemeasurable_fst.prodMk (hF.comp_aemeasurable h.aemeasurable), ?_⟩
  have h_eq : (fun a ↦ (X a, F (X a, Y a)))
      = (fun p : α × β ↦ (p.1, F p)) ∘ (fun a ↦ (X a, Y a)) := rfl
  rw [h_eq, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) h.aemeasurable, h.map_eq,
    Measure.compProd_map_prodMk _ _ hF]

end congr

end ProbabilityTheory
