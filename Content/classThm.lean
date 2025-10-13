import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Classical

/-- Just a short name for √2. -/
noncomputable def s : ℝ := Real.sqrt 2

lemma s_pos : 0 < s := by
  have : 0 < (2 : ℝ) := by norm_num
  simpa [s] using Real.sqrt_pos.mpr this

lemma s_nonneg : 0 ≤ s := le_of_lt s_pos

/-- `√2` is irrational (library lemma). -/
lemma s_irrational : Irrational s :=
  irrational_sqrt_two

/-- Every real is either irrational or (equal to) some rational.
This is exactly using excluded middle on `Irrational x`. -/
lemma rational_or_irrational (x : ℝ) :
    (∃ q : ℚ, x = q) ∨ Irrational x := by
  classical
  by_cases h : Irrational x
  · exact Or.inr h
  · -- From ¬(∀ q, x ≠ q) obtain ∃ q, x = q
    have : ¬ (∀ q : ℚ, x ≠ q) := by simpa [Irrational] using h
    rcases not_forall.mp this with ⟨q, hq⟩
    exact Or.inl ⟨q, not_not.mp hq⟩

/-- The “folklore” theorem:
there exist irrational `p q : ℝ` such that `p^q` is rational.
We use real exponentiation `Real.rpow`. -/
theorem exists_irrational_irrational_pow_rational :
    ∃ p q : ℝ, Irrational p ∧ Irrational q ∧ ∃ r : ℚ, Real.rpow p q = r := by
  classical
  -- set s = √2
  let s := s
  have hsirr : Irrational s := s_irrational
  have hsnn : 0 ≤ s := s_nonneg

  -- Consider x = s^s
  let x : ℝ := Real.rpow s s
  -- Case split by excluded middle on “x is irrational”
  cases rational_or_irrational x with
  | inl hx_rat =>
      rcases hx_rat with ⟨r, hr⟩
      -- Case 1: x is rational. Take p = q = √2
      refine ⟨s, s, hsirr, hsirr, ?_⟩
      exact ⟨r, hr⟩
  | inr hx_irr =>
      -- Case 2: x is irrational. Take p = x and q = √2
      have hx : Irrational x := hx_irr
      -- Compute (s^s)^s = s^(s*s) = s^2 = 2
      -- (library lemma: `Real.rpow_mul` with base ≥ 0)
      have h1 : Real.rpow x s = Real.rpow s (s * s) := by
        -- `Real.rpow_mul hsnn s s` usually rewrites `s^(s*s) = (s^s)^s`;
        -- we rewrite it the other way around.
        -- In many builds this lemma is named `Real.rpow_mul`:
        --   `Real.rpow_mul hsnn a b : s^(a*b) = (s^a)^b`.
        simpa [x] using (Real.rpow_mul hsnn s s).symm
      -- Now `s * s = 2` since s = √2
      have hss : s * s = (2 : ℝ) := by
        have : 0 ≤ (2 : ℝ) := by norm_num
        simpa [s] using Real.sqrt_mul_self this
      -- Turn exponent 2 (a real) into a natural exponent and simplify.
      -- Lemma names you can use here:
      -- * `Real.rpow_nat` : `Real.rpow s (n : ℝ) = s ^ n`
      -- * `Real.sqrt_sq` / `Real.sq_sqrt` / `Real.sqrt_mul_self` to finish `s^2 = 2`
      have h2 : Real.rpow s (s * s) = 2 := by
        -- convert to `Real.rpow s 2`
        have : Real.rpow s (2 : ℝ) = s ^ (2 : ℕ) := Real.rpow_nat _ 2
        -- and `s ^ 2 = s * s`
        have : Real.rpow s (2 : ℝ) = s * s := by
          simpa using (Real.rpow_nat _ 2)
        -- combine with `s*s = 2`
        simpa [hss] using this
      -- Put the chain together
      have hx_pow_rational : ∃ r : ℚ, Real.rpow x s = r := by
        -- From `Real.rpow x s = 2` and `2 : ℚ`, we are done
        refine ⟨(2 : ℚ), ?_⟩
        simpa [h1, h2]
      exact ⟨x, s, hx, hsirr, hx_pow_rational⟩
  