/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Mathlib.Data.Rel

/-- Typeclass for the α-equivalence notation `x =α y`. -/
class HasAlphaEquiv (β : Type u) where
  /-- α-equivalence relation for type β. -/
  AlphaEquiv : Rel β β

notation m:max " =α " n:max => HasAlphaEquiv.AlphaEquiv m n
