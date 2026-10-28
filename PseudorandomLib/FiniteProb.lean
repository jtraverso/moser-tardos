/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-! # Finite product probability spaces

A product probability space over a finite index type `ι` with a finite coordinate type `α`
is given by a family `P : ι → α → ℝ` of probability mass functions (`IsPMF P`). An outcome is
a function `ω : ι → α`, with weight `pw P ω = ∏ i, P i (ω i)`. Expectations `pE` and
probabilities `pProb` are explicit finite sums, so nothing measure-theoretic is needed.
-/

@[expose] public section

namespace Pseudorandom

open Finset

section Basic

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- `P` is a family of probability mass functions on `α`, one for each coordinate. -/
def IsPMF (P : ι → α → ℝ) : Prop := (∀ i a, 0 ≤ P i a) ∧ ∀ i, ∑ a, P i a = 1

/-- The product weight of an outcome. -/
def pw (P : ι → α → ℝ) (ω : ι → α) : ℝ := ∏ i, P i (ω i)

/-- Expectation in the product space. -/
def pE (P : ι → α → ℝ) (f : (ι → α) → ℝ) : ℝ := ∑ ω, pw P ω * f ω

open Classical in
/-- Probability of an event in the product space. -/
noncomputable def pProb (P : ι → α → ℝ) (S : (ι → α) → Prop) : ℝ :=
  pE P (fun ω => if S ω then 1 else 0)

variable {P : ι → α → ℝ}

omit [DecidableEq ι] in
theorem pw_nonneg (hP : IsPMF P) (ω : ι → α) : 0 ≤ pw P ω :=
  prod_nonneg fun i _ => hP.1 i (ω i)

theorem sum_pw (hP : IsPMF P) : ∑ ω, pw P ω = 1 := by
  unfold pw
  rw [← Fintype.prod_sum (fun i a => P i a)]
  simp [hP.2]

theorem pE_const (hP : IsPMF P) (c : ℝ) : pE P (fun _ => c) = c := by
  unfold pE
  rw [← sum_mul, sum_pw hP, one_mul]

theorem pE_add (f g : (ι → α) → ℝ) : pE P (fun ω => f ω + g ω) = pE P f + pE P g := by
  unfold pE
  rw [← sum_add_distrib]
  congr 1; funext ω; ring

theorem pE_sub (f g : (ι → α) → ℝ) : pE P (fun ω => f ω - g ω) = pE P f - pE P g := by
  unfold pE
  rw [← sum_sub_distrib]
  congr 1; funext ω; ring

theorem pE_const_mul (c : ℝ) (f : (ι → α) → ℝ) : pE P (fun ω => c * f ω) = c * pE P f := by
  unfold pE
  rw [mul_sum]
  congr 1; funext ω; ring

theorem pE_neg (f : (ι → α) → ℝ) : pE P (fun ω => -f ω) = -pE P f := by
  have := pE_const_mul (P := P) (-1) f
  simpa using this

theorem pE_sum {κ : Type*} (s : Finset κ) (f : κ → (ι → α) → ℝ) :
    pE P (fun ω => ∑ k ∈ s, f k ω) = ∑ k ∈ s, pE P (f k) := by
  unfold pE
  simp_rw [mul_sum]
  rw [sum_comm]

theorem pE_mono (hP : IsPMF P) {f g : (ι → α) → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    pE P f ≤ pE P g :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (pw_nonneg hP ω)

/-- Monotonicity only needs the inequality on outcomes of positive weight. -/
theorem pE_mono_supp (hP : IsPMF P) {f g : (ι → α) → ℝ} (h : ∀ ω, 0 < pw P ω → f ω ≤ g ω) :
    pE P f ≤ pE P g := by
  refine sum_le_sum fun ω _ => ?_
  rcases (pw_nonneg hP ω).lt_or_eq with hpos | hzero
  · exact mul_le_mul_of_nonneg_left (h ω hpos) hpos.le
  · rw [← hzero]; simp

theorem pE_nonneg (hP : IsPMF P) {f : (ι → α) → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ pE P f := by
  have := pE_mono hP (f := fun _ => (0 : ℝ)) h
  rwa [pE_const hP] at this

/-- Expectation of a product of functions of distinct coordinates (independence). -/
theorem pE_prod (g : ι → α → ℝ) :
    pE P (fun ω => ∏ i, g i (ω i)) = ∏ i, ∑ a, P i a * g i a := by
  unfold pE pw
  rw [Fintype.prod_sum (fun i a => P i a * g i a)]
  congr 1; funext ω
  rw [prod_mul_distrib]

/-- Expectation of a function of a single coordinate. -/
theorem pE_coord (hP : IsPMF P) (i : ι) (g : α → ℝ) :
    pE P (fun ω => g (ω i)) = ∑ a, P i a * g a := by
  have h := pE_prod (P := P) (fun j a => if j = i then g a else 1)
  have hl : (fun ω : ι → α => ∏ j, (if j = i then g (ω j) else 1)) = fun ω => g (ω i) := by
    funext ω
    rw [prod_ite_eq' univ i (fun j => g (ω j))]
    simp
  simp only [hl] at h
  rw [h, prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj, hP.2 j]
  · simp

theorem pProb_nonneg (hP : IsPMF P) (S : (ι → α) → Prop) : 0 ≤ pProb P S := by
  classical
  unfold pProb
  exact pE_nonneg hP fun ω => by split_ifs <;> norm_num

theorem pProb_le_one (hP : IsPMF P) (S : (ι → α) → Prop) : pProb P S ≤ 1 := by
  classical
  unfold pProb
  calc _ ≤ pE P (fun _ => (1 : ℝ)) := pE_mono hP fun ω => by split_ifs <;> norm_num
    _ = 1 := pE_const hP 1

theorem pProb_mono (hP : IsPMF P) {S T : (ι → α) → Prop} (h : ∀ ω, S ω → T ω) :
    pProb P S ≤ pProb P T := by
  classical
  unfold pProb
  refine pE_mono hP fun ω => ?_
  by_cases hs : S ω
  · simp [hs, h ω hs]
  · simp only [hs, if_false]; split_ifs <;> norm_num

/-- Union bound. -/
theorem pProb_exists_le {κ : Type*} (hP : IsPMF P) (s : Finset κ) (S : κ → (ι → α) → Prop) :
    pProb P (fun ω => ∃ k ∈ s, S k ω) ≤ ∑ k ∈ s, pProb P (S k) := by
  classical
  unfold pProb
  rw [← pE_sum]
  refine pE_mono hP fun ω => ?_
  split_ifs with h
  · obtain ⟨k, hk, hS⟩ := h
    calc (1 : ℝ) = if S k ω then 1 else 0 := by simp [hS]
      _ ≤ ∑ k ∈ s, if S k ω then (1 : ℝ) else 0 :=
          single_le_sum (f := fun k => if S k ω then (1 : ℝ) else 0)
            (fun k _ => by show (0:ℝ) ≤ if S k ω then 1 else 0; split_ifs <;> norm_num) hk
  · exact sum_nonneg fun k _ => by split_ifs <;> norm_num

theorem pProb_or_le (hP : IsPMF P) (S T : (ι → α) → Prop) :
    pProb P (fun ω => S ω ∨ T ω) ≤ pProb P S + pProb P T := by
  classical
  unfold pProb
  rw [← pE_add]
  refine pE_mono hP fun ω => ?_
  by_cases hs : S ω <;> by_cases ht : T ω <;> simp [hs, ht]

theorem pProb_not (hP : IsPMF P) (S : (ι → α) → Prop) :
    pProb P (fun ω => ¬ S ω) = 1 - pProb P S := by
  classical
  unfold pProb
  have h := pE_sub (P := P) (fun _ => (1 : ℝ)) (fun ω => if S ω then 1 else 0)
  rw [pE_const hP] at h
  rw [← h]
  congr 1; funext ω
  by_cases hs : S ω <;> simp [hs]

/-- If an event has probability `< 1`, some outcome of positive weight avoids it. -/
theorem exists_of_pProb_lt_one (hP : IsPMF P) {S : (ι → α) → Prop} (h : pProb P S < 1) :
    ∃ ω, 0 < pw P ω ∧ ¬ S ω := by
  classical
  by_contra hcon
  push_neg at hcon
  have : pProb P S = 1 := by
    unfold pProb pE
    have : ∑ ω, pw P ω * (if S ω then (1 : ℝ) else 0) = ∑ ω, pw P ω := by
      refine sum_congr rfl fun ω _ => ?_
      rcases (pw_nonneg hP ω).lt_or_eq with hpos | hzero
      · simp [hcon ω hpos]
      · rw [← hzero]; simp
    rw [this, sum_pw hP]
  linarith

/-- Probability of the event that a function is at least `t` is at most `E f / t`
(Markov's inequality, for nonnegative `f`). -/
theorem pProb_ge_le_markov (hP : IsPMF P) {f : (ι → α) → ℝ} (hf : ∀ ω, 0 ≤ f ω) {t : ℝ}
    (ht : 0 < t) : pProb P (fun ω => t ≤ f ω) ≤ pE P f / t := by
  classical
  rw [le_div_iff₀ ht]
  unfold pProb
  rw [mul_comm, ← pE_const_mul]
  refine pE_mono hP fun ω => ?_
  split_ifs with h
  · linarith
  · linarith [hf ω]


/-- A probability is the expectation of any indicator function of the event. -/
theorem pProb_eq_pE (S : (ι → α) → Prop) (g : (ι → α) → ℝ) (h1 : ∀ ω, S ω → g ω = 1)
    (h0 : ∀ ω, ¬ S ω → g ω = 0) : pProb P S = pE P g := by
  classical
  unfold pProb
  congr 1; funext ω
  by_cases hs : S ω
  · rw [if_pos hs, h1 ω hs]
  · rw [if_neg hs, h0 ω hs]

/-- Probability of a cylinder event: prescribed values on a finite set of coordinates. -/
theorem pProb_cylinder (hP : IsPMF P) (S : Finset ι) (x : ι → α) :
    pProb P (fun ω => ∀ i ∈ S, ω i = x i) = ∏ i ∈ S, P i (x i) := by
  classical
  rw [pProb_eq_pE _ (fun ω => ∏ i, (if i ∈ S then (if ω i = x i then (1 : ℝ) else 0) else 1))]
  · rw [pE_prod (fun i a => if i ∈ S then (if a = x i then (1 : ℝ) else 0) else 1)]
    have : ∀ i, ∑ a, P i a * (if i ∈ S then (if a = x i then (1 : ℝ) else 0) else 1) =
        if i ∈ S then P i (x i) else 1 := by
      intro i
      by_cases hi : i ∈ S
      · simp [hi]
      · simp [hi, hP.2 i]
    simp_rw [this]
    rw [prod_ite_mem univ S, univ_inter]
  · intro ω h
    refine prod_eq_one fun i _ => ?_
    split_ifs with h1 h2 <;> simp_all
  · intro ω h
    push_neg at h
    obtain ⟨i, hi, hne⟩ := h
    exact prod_eq_zero (mem_univ i) (by simp [hi, hne])

/-- Probability of the complement of a cylinder event. -/
theorem pProb_not_cylinder (hP : IsPMF P) (S : Finset ι) (x : ι → α) :
    pProb P (fun ω => ¬ ∀ i ∈ S, ω i = x i) = 1 - ∏ i ∈ S, P i (x i) := by
  rw [pProb_not hP, pProb_cylinder hP]

theorem pProb_congr {S T : (ι → α) → Prop} (h : ∀ ω, S ω ↔ T ω) : pProb P S = pProb P T := by
  have : S = T := funext fun ω => propext (h ω)
  rw [this]

end Basic

/-! ## Transport along an equivalence of index types -/

section Transport

variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype α]

theorem pE_equiv (e : ι ≃ κ) (P : ι → α → ℝ) (f : (ι → α) → ℝ) :
    pE P f = pE (fun j => P (e.symm j)) (fun ω' => f (ω' ∘ e)) := by
  unfold pE pw
  refine Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl α)) _ _ fun ω => ?_
  have h1 : (Equiv.arrowCongr e (Equiv.refl α) ω) ∘ e = ω := by
    funext i; simp [Equiv.arrowCongr_apply]
  dsimp only
  rw [h1]
  congr 1
  refine Fintype.prod_equiv e _ _ fun i => ?_
  simp [Equiv.arrowCongr_apply]

theorem pProb_equiv (e : ι ≃ κ) (P : ι → α → ℝ) (S : (ι → α) → Prop) :
    pProb P S = pProb (fun j => P (e.symm j)) (fun ω' => S (ω' ∘ e)) := by
  classical
  unfold pProb
  rw [pE_equiv e]

end Transport

end Pseudorandom
