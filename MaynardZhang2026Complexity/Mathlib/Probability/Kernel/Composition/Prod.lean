/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Kernels drawing fresh randomness

The kernel `(Kernel.id ×ₖ Kernel.const X μ).map f` draws a fresh `z ∼ μ` and returns `f (x, z)`:
this is how randomized decision rules (the policies of randomized algorithms, the reward kernels
of additive-noise environments) are written.

## Main statements

* `Kernel.map_id_prod_const_apply`: the value of that kernel at `x` is the image of `μ` by
  `f (x, ·)`;
* `Kernel.comap_map_id_prod_const`: precomposing it with a measurable map `g` gives the kernel
  drawing `z ∼ μ` and returning `f (g w, z)`.

TODO: upstream to Mathlib (`Mathlib/Probability/Kernel/Composition/Prod.lean`).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {X Y Z : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  {mZ : MeasurableSpace Z}

/-- The kernel drawing a fresh `z ∼ μ` and returning `f (x, z)` maps `x` to the image of `μ` by
`f (x, ·)`. -/
lemma map_id_prod_const_apply (μ : Measure Z) [SFinite μ] {f : X × Z → Y} (hf : Measurable f)
    (x : X) : ((Kernel.id ×ₖ Kernel.const X μ).map f) x = μ.map fun z ↦ f (x, z) := by
  rw [map_apply _ hf, prod_apply, id_apply, const_apply, Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left]
  rfl

/-- Precomposing the kernel drawing a fresh `z ∼ μ` and returning `f (x, z)` with a measurable map
`g` gives the kernel drawing a fresh `z ∼ μ` and returning `f (g w, z)`. -/
lemma comap_map_id_prod_const {W : Type*} {mW : MeasurableSpace W} (μ : Measure Z) [SFinite μ]
    {f : X × Z → Y} (hf : Measurable f) {g : W → X} (hg : Measurable g) :
    ((Kernel.id ×ₖ Kernel.const X μ).map f).comap g hg =
      (Kernel.id ×ₖ Kernel.const W μ).map fun p ↦ f (g p.1, p.2) := by
  have hf' : Measurable fun p : W × Z ↦ f (g p.1, p.2) := by fun_prop
  ext w : 1
  rw [comap_apply, map_id_prod_const_apply μ hf, map_id_prod_const_apply μ hf']

end ProbabilityTheory.Kernel
