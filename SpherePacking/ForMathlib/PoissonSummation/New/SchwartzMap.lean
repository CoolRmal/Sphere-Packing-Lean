/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Yongxi Lin

Reference: Loukas Grafakos, *Classical Fourier Analysis*
-/

import Mathlib

/-!
# Summability of mFourier coefficients of Schwartz Functions on ℝⁿ
-/

open Set Algebra Submodule MeasureTheory UnitAddTorus FourierTransform Asymptotics

open Asymptotics TopologicalSpace Real Filter ContinuousMap ZLattice Submodule

variable {d : Type*} [Fintype d] {f : EuclideanSpace ℝ d → ℂ}

#synth InnerProductSpace ℝ (EuclideanSpace ℝ d)

/- I am using EuclideanSpace ℝ d instead of d → ℝ because the first one has an instance of
InnerProductSpace. We need this instance for Real.fourierIntegral 𝓕.
-/

namespace RpowDecay

#check Function.Periodic.lift

def Periodicization (f : EuclideanSpace ℝ d → ℂ) : UnitAddTorus d → ℂ :=
  -- fun x ↦ Quotient.liftOn' x f
  sorry
  /- In the proof of the one dimensional case for the Poisson summation formula. They first use
  `f : ℝ → ℂ` to get a periodic function defined by `∑' (n : ℤ), f (x + n)`. They then use
  `Function.Periodic.lift` to get a function defined on the circle.

  Here's one approach to define the d dimensional periodicization. Just like the one dimensional
  case, we use `periodic_tsum_comp_add_zsmul` to get a periodic function defined by
  ∑' n : d → ℤ, f (x + n). We then use Function.Periodic.lift to get a function defined on
  (ℝ/ℤ)ᵈ. However, we are not done yet because in Mathlib, UnitAddTorus d is defined as (ℝ/ℤ)ᵈ.
  We need to use an isomorphism between ℝᵈ/ℤᵈ and (ℝ/ℤ)ᵈ to get a function in UnitAddTorus d → ℂ.
  -/

lemma Summable_mFourier_coeff {b : ℝ} (hb : Fintype.card d < b)
    (hf : f =O[cocompact (EuclideanSpace ℝ d)] (‖·‖ ^ (-b)))
    (h_sum : Summable fun n : d → ℤ => 𝓕 f fun i => n i) :
    Summable (mFourierCoeff (Periodicization f)) := by
  -- Use `tendstoUniformly_tsum_nat` but somehow generalise statement by replacing ℕ with countable
  sorry

/- For each (n : d → ℤ) 𝓕 f (fun i => n i)) = mFourierCoeff (Periodicization f) n. -/
lemma mFourierCoeff_Periodicization_eq_FourierTransform {b : ℝ} (hb : Fintype.card d < b)
    (hf : f =O[cocompact (EuclideanSpace ℝ d)] (‖·‖ ^ (-b))) (n : d → ℤ) :
    𝓕 f (fun i => n i) = mFourierCoeff (Periodicization f) n := by sorry

/- Periodicization is continuous. -/
lemma cont_Periodicization {b : ℝ} (hb : Fintype.card d < b)
    (hf : f =O[cocompact (EuclideanSpace ℝ d)] (‖·‖ ^ (-b))) (n : d → ℤ) :
    Continuous (Periodicization f) := by sorry
/- We assume f decays very fast so that ∑' n : d → ℤ, f (x + n) is dominated by a convergent
  series. We can then deduce that ∑' n : d → ℤ, f (x + n) converges uniformly by the Weierstrass M-
  test. ∑' n : d → ℤ, f (x + n) is thus continuous as the uniform limit of continuous functions.
  -/

/-- **Poisson summation formula** for continuous functions with fast decay and and its Fourier
transform is summable. -/
theorem tsum_mFourier_coeff_eq_tsum_fourierIntegralof_rpow_decay_of_summable {b : ℝ}
    (hc : Continuous f) (hb : Fintype.card d < b)
    (hf : f =O[cocompact (EuclideanSpace ℝ d)] (‖·‖ ^ (-b)))
    (h_sum : Summable fun n : d → ℤ => 𝓕 f fun i => n i)
    (x : EuclideanSpace ℝ d) :
    ∑' n : d → ℤ, f (fun i => (n i + x i : ℝ)) =
    ∑' n : d → ℤ, 𝓕 f (fun i => n i) • mFourier n (fun i => x i) := by
  sorry

/-- d-dimensional analogue of the absolute convergence of p-series. -/
lemma summable_abs_int_rpow {b : ℝ} :
    Summable (fun (v : d → ℤ) =>
    @Norm.norm (EuclideanSpace ℝ d) (PiLp.instNorm 2 fun x ↦ ℝ) (fun i => v i) ^ (-b)) := by
  sorry
  /-There should be a better way to write this. -/

/-- The inclusion from ℤᵈ to ℝᵈ maps the filter of cofinite sets to the filter of cocompact sets.
This is the d-dimensional analogue of `Int.tendsto_coe_cofinite`. -/
lemma IntLattice.tendsto_coe_cofinite :
    Filter.Tendsto (fun n : d → ℤ => fun i => (n i : ℝ))
    Filter.cofinite (Filter.cocompact (EuclideanSpace ℝ d)) := by sorry

/-- **Poisson summation formula**, assuming that both `f` and its Fourier transform decay fast. -/
theorem tsum_mFourier_coeff_eq_tsum_fourierIntegralof_rpow_decay {b : ℝ}
    (hc : Continuous f) (hb : Fintype.card d < b)
    (hf : f =O[cocompact (EuclideanSpace ℝ d)] (‖·‖ ^ (-b)))
    (hFf : 𝓕 f =O[cocompact (EuclideanSpace ℝ d)] (‖·‖ ^ (-b))) (x : EuclideanSpace ℝ d) :
    ∑' n : d → ℤ, f (fun i => n i + x i) =
    ∑' n : d → ℤ, 𝓕 f (fun i => n i) * mFourier n (fun i => x i) := by
  refine tsum_mFourier_coeff_eq_tsum_fourierIntegralof_rpow_decay_of_summable hc hb hf
    (summable_of_isBigO (summable_abs_int_rpow hb) ?_) x
  suffices h : (𝓕 f ∘ fun n : d → ℤ => fun i => n i) =O[cofinite]
    ((fun x ↦ @Norm.norm (EuclideanSpace ℝ d) (PiLp.instNorm 2 fun x ↦ ℝ) x ^ (-b)) ∘ fun n : d → ℤ
    => fun i => n i) from by
    exact h
  exact hFf.comp_tendsto IntLattice.tendsto_coe_cofinite

end RpowDecay

namespace SchwartzMap

/-- **Poisson summation formula** for Schwartz maps. -/
theorem tsum_mFourier_coeff_eq_tsum_fourierIntegral (f : 𝓢(EuclideanSpace ℝ d, ℂ))
    (x : EuclideanSpace ℝ d) :
    ∑' n : d → ℤ, f (fun i => n i + x i) =
    ∑' n : d → ℤ, 𝓕 f (fun i => n i) * mFourier n (fun i => x i) :=
  RpowDecay.tsum_mFourier_coeff_eq_tsum_fourierIntegralof_rpow_decay f.continuous
    (by simp : (Fintype.card d : ℝ) < Fintype.card d + 1)
    (f.isBigO_cocompact_rpow (-(Fintype.card d + 1)))
    ((fourierTransformCLM ℝ f).isBigO_cocompact_rpow (-(Fintype.card d + 1))) x

variable (Λ : Submodule ℤ (EuclideanSpace ℝ d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- This is the analogue of `UnitAddTorus.mFourier` for a general ZLattice. There should
exsts a scaling factor related to the volume of the fundamental area of this ZLattice, but I
didn't include it yet as I am not sure how to define it. -/
def _root_.ZLattice.mFourier (n : Λ) : C(UnitAddTorus d, ℂ) where
  toFun x := sorry
  continuous_toFun := sorry

/-- **Poisson summation formula** for a general lattice. We need to use
`integral_image_eq_integral_abs_det_fderiv_smul`. -/
theorem _root_.ZLattice.tsum_mFourier_coeff_eq_tsum_fourierIntegral (f : 𝓢(EuclideanSpace ℝ d, ℂ))
  (x : EuclideanSpace ℝ d) :
  ∑' n : Λ, f (fun i => n.val i + x i) =
  ∑' n : Λ, 𝓕 f (fun i => n.val i) * ZLattice.mFourier Λ n (fun i => x i) := by sorry

end SchwartzMap

#min_imports
