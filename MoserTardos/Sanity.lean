/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MoserTardos.Main

/-!
# Sanity checks

The smallest nontrivial instance: one fair coin and one event "the coin shows `true`". Its
probability is `1/2`, it has no neighbours, and the condition of the Lovász Local Lemma holds with
`x = 1/2`; the theorems then give an expected number of resamplings at most `1` and an assignment
avoiding the event.
-/

@[expose] public section

namespace MoserTardos.Sanity

open Finset Pseudorandom

/-- One fair coin, one event: the coin shows `true`. -/
def coin : Inst Unit Bool 1 where
  vbl _ := {()}
  ev _ ω := ω () = true
  dep _ ω ω' h := by simp [h () (mem_singleton_self _)]

/-- The fair coin. -/
noncomputable def fair : Unit → Bool → ℝ := fun _ _ => 1 / 2

theorem fair_isPMF : IsPMF fair :=
  ⟨fun _ _ => by norm_num [fair], fun _ => by simp [fair]⟩

theorem pProb_coin (j : Fin 1) : pProb fair (coin.ev j) = 1 / 2 := by
  rw [pProb_congr (S := coin.ev j) (T := fun ω => ∀ i ∈ (univ : Finset Unit), ω i = true)
    (fun ω => ⟨fun h i _ => h, fun h => h () (mem_univ _)⟩), pProb_cylinder fair_isPMF]
  simp [fair]

theorem nbr_coin (j : Fin 1) : coin.nbr j = ∅ := by
  ext k
  simp [coin.mem_nbr, Fin.fin_one_eq_zero k, Fin.fin_one_eq_zero j]

theorem lll_coin (j : Fin 1) :
    pProb fair (coin.ev j) ≤
      (fun _ => (1 : ℝ) / 2) j * ∏ k ∈ coin.nbr j, (1 - (fun _ => (1 : ℝ) / 2) k) := by
  rw [pProb_coin, nbr_coin]
  simp

/-- The expected number of resamplings is at most `1`. -/
example (t : ℕ) :
    pE (tableLaw fair t) (fun T => (coin.count (extend false T) 0 t : ℝ)) ≤ 1 := by
  have := coin.expected_count_le fair_isPMF false (x := fun _ => 1 / 2) (fun _ => by norm_num)
    (fun _ => by norm_num) lll_coin 0 t
  norm_num at this
  exact this

/-- Some assignment avoids the event: the coin shows `false`. -/
example : ∃ ω : Unit → Bool, ω () = false := by
  obtain ⟨ω, h⟩ := coin.exists_avoiding fair_isPMF false (x := fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num) lll_coin
  exact ⟨ω, by simpa [coin] using h 0⟩

/-- The condition of the Lovász Local Lemma fails for an event that always holds, as it must:
then no assignment avoids it. -/
example (x : Fin 1 → ℝ) (hx1 : ∀ j, x j < 1) :
    ¬ ∀ j, pProb fair (fun _ : Unit → Bool => True) ≤ x j * ∏ k ∈ coin.nbr j, (1 - x k) := by
  intro h
  have := h 0
  rw [nbr_coin, prod_empty, mul_one,
    pProb_eq_pE _ (fun _ => 1) (fun _ _ => rfl) (fun _ h => absurd trivial h),
    pE_const fair_isPMF] at this
  linarith [hx1 0]

end MoserTardos.Sanity
