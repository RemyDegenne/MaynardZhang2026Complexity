/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Composition-product of constant kernels

## Main statements

* `Kernel.const_compProd_const`: the composition-product of two constant kernels is the constant
  kernel of the product measure.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {X Y Z : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  {mZ : MeasurableSpace Z}

/-- The composition-product of two constant kernels is the constant kernel of the product
measure. -/
@[simp]
lemma const_compProd_const (μ : Measure Y) [SFinite μ] (ν : Measure Z) [SFinite ν] :
    Kernel.const X μ ⊗ₖ Kernel.const (X × Y) ν = Kernel.const X (μ.prod ν) := by
  ext x s hs
  rw [Kernel.const_apply, Kernel.compProd_apply hs, Measure.prod_apply hs]
  simp [Kernel.const_apply]

end ProbabilityTheory.Kernel
