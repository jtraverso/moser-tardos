/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MoserTardos.LogTree

/-!
# The Moser–Tardos theorem

Run the Moser–Tardos algorithm on a random table of depth `t` (independent entries, the entries
of variable `i` with law `P i`). If `P(ev j) ≤ x j ∏_{k ∈ Γ(j)} (1 - x k)` for all `j`, with
`0 ≤ x j < 1`, then:

* `expected_count_le`: the expected number of resamplings of event `j` among the first `t` steps
  is at most `x j / (1 - x j)`;
* `expected_totalCount_le`: the expected total number of resamplings among the first `t` steps is
  at most `∑ j, x j / (1 - x j)`;
* `pProb_running_le`: the probability that the algorithm is still running after `t` steps is at
  most `(∑ j, x j / (1 - x j)) / t`;
* `exists_avoiding`: hence (the Lovász Local Lemma) some assignment avoids all the events.

The proof: each resampling of `j` has a witness tree, distinct resamplings have distinct trees
(`build_injective`), each passes the `τ`-check on the table (`check_build`), a tree passes the
check with probability at most its weight (`pProb_check_le`), and the total weight of the trees
rooted at `j` is at most `x j / (1 - x j)` (`sum_weight_le`).
-/

@[expose] public section

namespace MoserTardos

open Finset Pseudorandom

namespace Inst

variable {ι α : Type*} [DecidableEq ι] {n : ℕ} (I : Inst ι α n)

open Classical in
/-- The number of resamplings of `j` is at most the number of trees passing the check. -/
theorem count_le_card_check (a₀ : α) {t : ℕ} (T : ι × Fin t → α) (j : Fin n) :
    I.count (extend a₀ T) j t ≤
      (univ.filter fun τ : I.Tr (t + 1) j => I.Check a₀ τ T).card := by
  classical
  unfold count
  refine card_le_card_of_injOn (fun s => I.build (extend a₀ T) s t s j) ?_ ?_
  · intro s hs
    obtain ⟨hs, hl⟩ := mem_filter.1 hs
    exact mem_filter.2 ⟨mem_univ _, I.check_build a₀ T hl (mem_range.1 hs) (mem_range.1 hs).le⟩
  · intro s₁ h₁ s₂ h₂ h
    obtain ⟨r₁, l₁⟩ := mem_filter.1 (mem_coe.1 h₁)
    obtain ⟨r₂, l₂⟩ := mem_filter.1 (mem_coe.1 h₂)
    exact I.build_injective l₁ l₂ (mem_range.1 r₁).le (mem_range.1 r₂).le h

variable [Fintype ι] [Fintype α] {P : ι → α → ℝ} {x : Fin n → ℝ}

open Classical in
/-- **The Moser–Tardos theorem.** Under the condition of the Lovász Local Lemma, the expected
number of resamplings of the event `j` among the first `t` steps of the algorithm, run on a random
table of depth `t`, is at most `x j / (1 - x j)`. -/
theorem expected_count_le (hP : IsPMF P) (a₀ : α) (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j < 1)
    (hlll : ∀ j, pProb P (I.ev j) ≤ x j * ∏ k ∈ I.nbr j, (1 - x k)) (j : Fin n) (t : ℕ) :
    pE (tableLaw P t) (fun T => (I.count (extend a₀ T) j t : ℝ)) ≤ x j / (1 - x j) := by
  have hPL := tableLaw_isPMF hP t
  calc pE (tableLaw P t) (fun T => (I.count (extend a₀ T) j t : ℝ))
      ≤ pE (tableLaw P t)
          (fun T => ∑ τ : I.Tr (t + 1) j, if I.Check a₀ τ T then (1 : ℝ) else 0) := by
        refine pE_mono hPL fun T => ?_
        have h := I.count_le_card_check a₀ T j
        rw [card_filter] at h
        exact_mod_cast h
    _ = ∑ τ : I.Tr (t + 1) j, pProb (tableLaw P t) (I.Check a₀ τ) := by
        rw [pE_sum]
        rfl
    _ ≤ ∑ τ : I.Tr (t + 1) j, I.weight (fun k => pProb P (I.ev k)) (t + 1) j τ :=
        sum_le_sum fun τ _ => I.pProb_check_le hP a₀ t τ
    _ ≤ x j / (1 - x j) :=
        I.sum_weight_le (fun k => pProb_nonneg hP _) hx0 hx1 hlll (t + 1) j

theorem totalCount_eq_sum (T : ι → ℕ → α) (t : ℕ) :
    I.totalCount T t = ∑ j, I.count T j t := by
  classical
  unfold totalCount count
  rw [← card_biUnion]
  · congr 1
    ext s
    simp only [mem_filter, mem_biUnion, mem_univ, true_and, Option.isSome_iff_exists]
    constructor
    · rintro ⟨hs, j, hj⟩
      exact ⟨j, hs, hj⟩
    · rintro ⟨j, hs, hj⟩
      exact ⟨hs, j, hj⟩
  · intro j _ k _ hjk
    refine disjoint_left.2 fun s hs hs' => hjk ?_
    exact Option.some.inj ((mem_filter.1 hs).2.symm.trans (mem_filter.1 hs').2)

/-- The expected total number of resamplings among the first `t` steps is at most
`∑ j, x j / (1 - x j)`. -/
theorem expected_totalCount_le (hP : IsPMF P) (a₀ : α) (hx0 : ∀ j, 0 ≤ x j)
    (hx1 : ∀ j, x j < 1) (hlll : ∀ j, pProb P (I.ev j) ≤ x j * ∏ k ∈ I.nbr j, (1 - x k))
    (t : ℕ) :
    pE (tableLaw P t) (fun T => (I.totalCount (extend a₀ T) t : ℝ)) ≤
      ∑ j, x j / (1 - x j) := by
  simp_rw [totalCount_eq_sum, Nat.cast_sum]
  rw [pE_sum]
  exact sum_le_sum fun j _ => I.expected_count_le hP a₀ hx0 hx1 hlll j t

theorem logAt_succ_eq_none {T : ι → ℕ → α} {r : ℕ} (h : I.logAt T r = none) :
    I.logAt T (r + 1) = none := by
  have : I.run T (r + 1) = I.run T r := by
    show I.step T (I.run T r) = I.run T r
    unfold step
    rw [show I.firstViolated (I.run T r).val = none from h]
  unfold logAt
  rw [this]
  exact h

theorem totalCount_le (T : ι → ℕ → α) (t : ℕ) : I.totalCount T t ≤ t := by
  classical
  unfold totalCount
  exact (card_filter_le _ _).trans (card_range t).le

/-- If the algorithm is still running after `t` steps, all of them were resamplings. -/
theorem totalCount_eq_of_running {T : ι → ℕ → α} {t : ℕ} (h : ∀ s < t, (I.logAt T s).isSome) :
    I.totalCount T t = t := by
  classical
  unfold totalCount
  rw [filter_true_of_mem fun s hs => h s (mem_range.1 hs), card_range]

/-- The probability that the algorithm is still running after `t` steps is at most
`(∑ j, x j / (1 - x j)) / t`. -/
theorem pProb_running_le (hP : IsPMF P) (a₀ : α) (hx0 : ∀ j, 0 ≤ x j)
    (hx1 : ∀ j, x j < 1) (hlll : ∀ j, pProb P (I.ev j) ≤ x j * ∏ k ∈ I.nbr j, (1 - x k))
    {t : ℕ} (ht : 0 < t) :
    pProb (tableLaw P t) (fun T => ∀ s < t, (I.logAt (extend a₀ T) s).isSome) ≤
      (∑ j, x j / (1 - x j)) / t := by
  have hPL := tableLaw_isPMF hP t
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  calc pProb (tableLaw P t) (fun T => ∀ s < t, (I.logAt (extend a₀ T) s).isSome)
      ≤ pProb (tableLaw P t) (fun T => (t : ℝ) ≤ (I.totalCount (extend a₀ T) t : ℝ)) :=
        pProb_mono hPL fun T h => by rw [I.totalCount_eq_of_running h]
    _ ≤ pE (tableLaw P t) (fun T => (I.totalCount (extend a₀ T) t : ℝ)) / t :=
        pProb_ge_le_markov hPL (fun T => Nat.cast_nonneg _) htR
    _ ≤ (∑ j, x j / (1 - x j)) / t :=
        div_le_div_of_nonneg_right (I.expected_totalCount_le hP a₀ hx0 hx1 hlll t) htR.le

theorem not_ev_of_firstViolated_eq_none {ω : ι → α} (h : I.firstViolated ω = none) (j : Fin n) :
    ¬ I.ev j ω := by
  classical
  intro hj
  unfold firstViolated at h
  rw [dif_pos ⟨j, mem_filter.2 ⟨mem_univ _, hj⟩⟩] at h
  cases h

/-- **The Lovász Local Lemma**, as a consequence: under its condition, some assignment avoids all
the events (it is found by the algorithm). -/
theorem exists_avoiding (hP : IsPMF P) (a₀ : α) (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j < 1)
    (hlll : ∀ j, pProb P (I.ev j) ≤ x j * ∏ k ∈ I.nbr j, (1 - x k)) :
    ∃ ω : ι → α, ∀ j, ¬ I.ev j ω := by
  set S := ∑ j, x j / (1 - x j)
  have hS : 0 ≤ S := sum_nonneg fun j _ => div_nonneg (hx0 j) (by linarith [hx1 j])
  set t := ⌊S⌋₊ + 1
  have ht : 0 < t := Nat.succ_pos _
  have htR : S < t := by
    have := Nat.lt_floor_add_one S
    push_cast [t]
    exact this
  have hlt : pProb (tableLaw P t) (fun T => ∀ s < t, (I.logAt (extend a₀ T) s).isSome) < 1 := by
    refine (I.pProb_running_le hP a₀ hx0 hx1 hlll ht).trans_lt ?_
    rw [div_lt_one (by exact_mod_cast ht)]
    exact htR
  obtain ⟨T, -, hT⟩ := exists_of_pProb_lt_one (tableLaw_isPMF hP t) hlt
  push_neg at hT
  obtain ⟨s, -, hs⟩ := hT
  refine ⟨(I.run (extend a₀ T) s).val, I.not_ev_of_firstViolated_eq_none ?_⟩
  simpa [logAt] using hs

end Inst

end MoserTardos
