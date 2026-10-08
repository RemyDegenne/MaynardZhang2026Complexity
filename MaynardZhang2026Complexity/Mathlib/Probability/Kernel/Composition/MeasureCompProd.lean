/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import MaynardZhang2026Complexity.Mathlib.Probability.Kernel.Composition.Prod

/-!
# Images and restrictions of composition-products of a measure and a kernel

## Main statements

* `Measure.map_compProd_of_forall_map_eq`: the image of a composition-product `μ ⊗ₘ κ` by a map
  `(a, b) ↦ (G a, F a b)` is the composition-product `μ.map G ⊗ₘ K` when
  `K (G a) = (κ a).map (F a)` for all `a`;
* `Measure.map_prodMk_compProd_comap`, `Measure.map_snd_compProd_comap`: transport of
  `μ ⊗ₘ η.comap f` along `f` in the first coordinate;
* `Measure.compProd_map_id_prod_const`: the composition-product of `μ` with the kernel drawing a
  fresh `z ∼ Q` and returning `f (x, z)` is the image of `μ.prod Q` by `p ↦ (p.1, f p)`;
* `Measure.restrict_compProd_prod_univ`: `(μ ⊗ₘ κ).restrict (s ×ˢ univ) = μ.restrict s ⊗ₘ κ`;
* `Measure.compProd_comap_fst_comm`: drawing two conditionally independent coordinates in either
  order;
* `Measure.compProd_map_prodMk`: recording a measurable function of the input and of the draw.
-/

@[expose] public section

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

/-- The image of `μ ⊗ₘ κ` by `(a, b) ↦ (G a, F a b)` is `μ.map G ⊗ₘ K` as soon as `K (G a)` is
the image of `κ a` by `F a` for every `a`. -/
lemma map_compProd_of_forall_map_eq (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsSFiniteKernel κ] {G : α → γ} (hG : Measurable G) {F : α → β → δ}
    (hF : Measurable (Function.uncurry F)) (K : Kernel γ δ) [IsSFiniteKernel K]
    (hK : ∀ a, K (G a) = (κ a).map (F a)) :
    (μ ⊗ₘ κ).map (fun p ↦ (G p.1, F p.1 p.2)) = μ.map G ⊗ₘ K := by
  have hφ : Measurable fun p : α × β ↦ (G p.1, F p.1 p.2) := (hG.comp measurable_fst).prodMk hF
  ext s hs
  rw [Measure.map_apply hφ hs, Measure.compProd_apply (hφ hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hG]
  refine lintegral_congr fun a ↦ ?_
  have hFa : Measurable (F a) := hF.comp measurable_prodMk_left
  rw [hK a, Measure.map_apply hFa (measurable_prodMk_left hs)]
  rfl

/-- Transporting `μ ⊗ₘ η.comap f` along `f` in the first coordinate gives `μ.map f ⊗ₘ η`. -/
lemma map_prodMk_compProd_comap (μ : Measure α) [SFinite μ] (η : Kernel β γ) [IsSFiniteKernel η]
    {f : α → β} (hf : Measurable f) :
    (μ ⊗ₘ η.comap f hf).map (fun p : α × γ ↦ (f p.1, p.2)) = μ.map f ⊗ₘ η :=
  map_compProd_of_forall_map_eq μ _ hf (F := fun _ c ↦ c) measurable_snd η
    fun a ↦ by rw [Kernel.comap_apply, Measure.map_id']

/-- The law of the second coordinate under `μ ⊗ₘ η.comap f` is its law under `μ.map f ⊗ₘ η`. -/
lemma map_snd_compProd_comap (μ : Measure α) [SFinite μ] (η : Kernel β γ) [IsSFiniteKernel η]
    {f : α → β} (hf : Measurable f) :
    (μ ⊗ₘ η.comap f hf).map Prod.snd = (μ.map f ⊗ₘ η).map Prod.snd := by
  rw [← map_prodMk_compProd_comap μ η hf, Measure.map_map measurable_snd (by fun_prop)]
  rfl

/-- The composition-product of `μ` with the kernel drawing a fresh `z ∼ Q` and returning
`f (x, z)` is the image of `μ.prod Q` by `p ↦ (p.1, f p)`. -/
lemma compProd_map_id_prod_const (μ : Measure α) [SFinite μ] (Q : Measure β) [SFinite Q]
    {f : α × β → γ} (hf : Measurable f) :
    μ ⊗ₘ (Kernel.id ×ₖ Kernel.const α Q).map f = (μ.prod Q).map (fun p ↦ (p.1, f p)) := by
  have h := map_compProd_of_forall_map_eq μ (Kernel.const α Q) measurable_id
    (F := fun a b ↦ f (a, b)) hf ((Kernel.id ×ₖ Kernel.const α Q).map f)
    fun a ↦ by rw [Kernel.map_id_prod_const_apply Q hf, Kernel.const_apply]; rfl
  rw [Measure.map_id, Measure.compProd_const] at h
  exact h.symm

/-- The restriction of `μ ⊗ₘ κ` to `s ×ˢ univ` is `μ.restrict s ⊗ₘ κ`. -/
lemma restrict_compProd_prod_univ (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsSFiniteKernel κ] {s : Set α} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ).restrict (s ×ˢ Set.univ) = μ.restrict s ⊗ₘ κ := by
  ext t ht
  rw [Measure.restrict_apply ht, Measure.compProd_apply (ht.inter (hs.prod MeasurableSet.univ)),
    Measure.compProd_apply ht, ← lintegral_indicator hs]
  refine lintegral_congr fun a ↦ ?_
  by_cases ha : a ∈ s
  · have : Prod.mk a ⁻¹' (t ∩ s ×ˢ Set.univ) = Prod.mk a ⁻¹' t := by ext b; simp [ha]
    simp [Set.indicator, ha, this]
  · have : Prod.mk a ⁻¹' (t ∩ s ×ˢ Set.univ) = ∅ := by ext b; simp [ha]
    simp [Set.indicator, ha, this]

/-- Exchanging two conditionally independent coordinates: if `κ` and `η` are two kernels on `α`,
the joint law of `(a, b, c)` obtained by drawing `b` from `κ a` and then `c` from `η a` is, up to
the exchange of `b` and `c`, the one obtained by drawing `c` first. -/
lemma compProd_comap_fst_comm (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α γ) [IsSFiniteKernel η] :
    ((μ ⊗ₘ κ) ⊗ₘ η.prodMkRight β).map (fun p ↦ ((p.1.1, p.2), p.1.2))
      = (μ ⊗ₘ η) ⊗ₘ κ.prodMkRight γ := by
  have key : ∀ (a : α) (t : Set (β × γ)), MeasurableSet t →
      ∫⁻ b, η a (Prod.mk b ⁻¹' t) ∂(κ a) = ∫⁻ c, κ a ((fun b ↦ (b, c)) ⁻¹' t) ∂(η a) := by
    intro a t ht
    rw [← Measure.prod_apply ht, ← Measure.prod_apply_symm ht]
  ext s hs
  have hF : Measurable (fun p : (α × β) × γ ↦ ((p.1.1, p.2), p.1.2)) := by fun_prop
  rw [Measure.map_apply hF hs, Measure.compProd_apply (hs.preimage hF), Measure.compProd_apply hs,
    Measure.lintegral_compProd (Kernel.measurable_kernel_prodMk_left (hs.preimage hF)),
    Measure.lintegral_compProd (Kernel.measurable_kernel_prodMk_left hs)]
  refine lintegral_congr fun a ↦ ?_
  simp only [Kernel.prodMkRight_apply]
  exact key a {q : β × γ | ((a, q.2), q.1) ∈ s} (hs.preimage (by fun_prop))

/-- Recording a measurable function of the input and of the draw: the image of `μ ⊗ₘ κ` by
`p ↦ (p.1, F p)` is the composition-product of `μ` with the kernel `(Kernel.id ×ₖ κ).map F`. -/
lemma compProd_map_prodMk (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    {F : α × β → γ} (hF : Measurable F) :
    (μ ⊗ₘ κ).map (fun p ↦ (p.1, F p)) = μ ⊗ₘ ((Kernel.id ×ₖ κ).map F) := by
  have hG : Measurable (fun p : α × β ↦ (p.1, F p)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hG hs, Measure.compProd_apply (hs.preimage hG), Measure.compProd_apply hs]
  refine lintegral_congr fun a ↦ ?_
  have ht : MeasurableSet (F ⁻¹' (Prod.mk a ⁻¹' s)) := (measurable_prodMk_left hs).preimage hF
  rw [Kernel.map_apply' _ hF _ (measurable_prodMk_left hs), Kernel.prod_apply,
    Measure.prod_apply ht, Kernel.id_apply, lintegral_dirac' _ (measurable_measure_prodMk_left ht)]
  rfl

end MeasureTheory.Measure
