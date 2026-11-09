/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Logic.Equiv.Defs

/-!
# The discrete measurable space on permutations

The type `Equiv.Perm α` of permutations of `α` is given the discrete σ-algebra (meant for finite
or countable `α`, e.g. uniformly random permutations of `Fin n`), as Mathlib does for other
countable types such as `ℕ` or `Fin n`.
-/

@[expose] public section

namespace Equiv.Perm

variable {α : Type*}

instance instMeasurableSpace : MeasurableSpace (Equiv.Perm α) := ⊤

instance instDiscreteMeasurableSpace : DiscreteMeasurableSpace (Equiv.Perm α) :=
  ⟨fun _ ↦ trivial⟩

end Equiv.Perm
