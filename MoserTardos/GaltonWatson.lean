/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MoserTardos.Defs

/-!
# Proper witness trees and the Galton–Watson bound

A *proper witness tree* of depth at most `d` with root label `j` is a root labelled `j` together
with, for each neighbour `k` of `j` (including `j` itself), at most one child labelled `k`, which
is itself a proper witness tree of depth at most `d - 1` with root label `k`. Children of a vertex
thus have distinct labels. We encode them by the type `Tr d j`, so that the trees of bounded depth
form a finite type.

Given vertex weights `p j ≥ 0`, the weight of a tree is the product of the weights of its vertex
labels. The total weight satisfies the recursion
`∑_{τ : Tr (d+1) j} w τ = p j ∏_{k ∈ Γ⁺(j)} (1 + ∑_{σ : Tr d k} w σ)` (`sum_weight_succ`), and under
the condition `p j ≤ x j ∏_{k ∈ Γ(j)} (1 - x k)` of the Lovász Local Lemma it is at most
`x j / (1 - x j)` for every depth (`sum_weight_le`). This is the counting half of the
Moser–Tardos analysis.
-/

@[expose] public section

namespace MoserTardos

open Finset

namespace Inst

variable {ι α : Type*} [DecidableEq ι] {n : ℕ} (I : Inst ι α n)

/-- Proper witness trees of depth at most `d` with root label `j`. -/
def Tr : ℕ → Fin n → Type
  | 0, _ => PEmpty
  | d + 1, j => (k : I.nbrIncl j) → Option (Tr d k)

/-- The trees of bounded depth form a finite type. -/
noncomputable instance instFintypeTr : (d : ℕ) → (j : Fin n) → Fintype (I.Tr d j)
  | 0, _ => inferInstanceAs (Fintype PEmpty)
  | d + 1, j =>
    have := fun k : Fin n => instFintypeTr d k
    inferInstanceAs (Fintype ((k : I.nbrIncl j) → Option (I.Tr d k)))

/-- The weight of a tree: the product of `p` over its vertex labels. -/
noncomputable def weight (p : Fin n → ℝ) : (d : ℕ) → (j : Fin n) → I.Tr d j → ℝ
  | 0, _, τ => PEmpty.elim τ
  | d + 1, j, τ => p j * ∏ k : I.nbrIncl j, (match τ k with
      | none => 1
      | some σ => weight p d k σ)

theorem sum_weight_zero (p : Fin n → ℝ) (j : Fin n) : ∑ τ : I.Tr 0 j, I.weight p 0 j τ = 0 := by
  show ∑ τ : PEmpty, _ = 0
  exact Finset.sum_of_isEmpty _

/-- The Galton–Watson recursion for the total weight. -/
theorem sum_weight_succ (p : Fin n → ℝ) (d : ℕ) (j : Fin n) :
    ∑ τ : I.Tr (d + 1) j, I.weight p (d + 1) j τ =
      p j * ∏ k : I.nbrIncl j, (1 + ∑ σ : I.Tr d k, I.weight p d k σ) := by
  show ∑ τ : ((k : I.nbrIncl j) → Option (I.Tr d k)), p j * ∏ k : I.nbrIncl j,
      (match τ k with
        | none => 1
        | some σ => I.weight p d k σ) = _
  rw [← Finset.mul_sum]
  congr 1
  have h : ∀ k : I.nbrIncl j, (1 + ∑ σ : I.Tr d k, I.weight p d k σ) =
      ∑ o : Option (I.Tr d k), (match o with
        | none => (1 : ℝ)
        | some σ => I.weight p d k σ) := fun k => by
    rw [Fintype.sum_option]
  rw [Finset.prod_congr rfl fun k _ => h k, Fintype.prod_sum]

theorem weight_nonneg {p : Fin n → ℝ} (hp : ∀ j, 0 ≤ p j) :
    ∀ (d : ℕ) (j : Fin n) (τ : I.Tr d j), 0 ≤ I.weight p d j τ
  | 0, _, τ => PEmpty.elim τ
  | d + 1, j, τ => by
    refine mul_nonneg (hp j) (Finset.prod_nonneg fun k _ => ?_)
    show 0 ≤ (match τ k with
      | none => (1 : ℝ)
      | some σ => I.weight p d k σ)
    cases τ k with
    | none => exact zero_le_one
    | some σ => exact weight_nonneg hp d k σ

theorem not_mem_nbr_self (j : Fin n) : j ∉ I.nbr j := by
  simp [nbr]

/-- **The Galton–Watson bound.** Under the condition of the Lovász Local Lemma, the total weight
of the proper witness trees of any bounded depth rooted at `j` is at most `x j / (1 - x j)`. -/
theorem sum_weight_le {p x : Fin n → ℝ} (hp : ∀ j, 0 ≤ p j) (hx0 : ∀ j, 0 ≤ x j)
    (hx1 : ∀ j, x j < 1) (hlll : ∀ j, p j ≤ x j * ∏ k ∈ I.nbr j, (1 - x k)) :
    ∀ (d : ℕ) (j : Fin n), ∑ τ : I.Tr d j, I.weight p d j τ ≤ x j / (1 - x j)
  | 0, j => by
    rw [sum_weight_zero]
    exact div_nonneg (hx0 j) (by linarith [hx1 j])
  | d + 1, j => by
    rw [sum_weight_succ]
    have h1 : ∀ k : I.nbrIncl j, 1 + ∑ σ : I.Tr d k, I.weight p d k σ ≤ 1 / (1 - x k) := by
      intro k
      have := sum_weight_le hp hx0 hx1 hlll d k
      have hk : 0 < 1 - x k := by linarith [hx1 k]
      calc 1 + ∑ σ : I.Tr d k, I.weight p d k σ ≤ 1 + x k / (1 - x k) := by linarith
        _ = 1 / (1 - x k) := by field_simp; ring
    have h0 : ∀ k : I.nbrIncl j, 0 ≤ 1 + ∑ σ : I.Tr d k, I.weight p d k σ := fun k =>
      add_nonneg zero_le_one (Finset.sum_nonneg fun σ _ => I.weight_nonneg hp d k σ)
    have hprod : ∏ k : I.nbrIncl j, (1 + ∑ σ : I.Tr d k, I.weight p d k σ) ≤
        ∏ k : I.nbrIncl j, (1 / (1 - x k)) :=
      Finset.prod_le_prod₀ (fun k _ => h0 k) (fun k _ => h1 k)
    have hsplit : ∏ k : I.nbrIncl j, (1 / (1 - x k)) =
        (1 / (1 - x j)) * ∏ k ∈ I.nbr j, (1 / (1 - x k)) := by
      rw [Finset.prod_coe_sort (I.nbrIncl j) (fun k => 1 / (1 - x k)), nbrIncl,
        Finset.prod_insert (I.not_mem_nbr_self j)]
    have hpos : ∀ k, 0 < 1 - x k := fun k => by linarith [hx1 k]
    calc p j * ∏ k : I.nbrIncl j, (1 + ∑ σ : I.Tr d k, I.weight p d k σ)
        ≤ p j * ∏ k : I.nbrIncl j, (1 / (1 - x k)) :=
          mul_le_mul_of_nonneg_left hprod (hp j)
      _ ≤ (x j * ∏ k ∈ I.nbr j, (1 - x k)) * ∏ k : I.nbrIncl j, (1 / (1 - x k)) :=
          mul_le_mul_of_nonneg_right (hlll j)
            (Finset.prod_nonneg fun k _ => le_of_lt (one_div_pos.2 (hpos k)))
      _ = x j / (1 - x j) := by
          have hprod1 : (∏ k ∈ I.nbr j, (1 - x k)) * ∏ k ∈ I.nbr j, (1 / (1 - x k)) = 1 := by
            rw [← Finset.prod_mul_distrib]
            exact Finset.prod_eq_one fun k _ => mul_one_div_cancel (ne_of_gt (hpos k))
          rw [hsplit]
          calc (x j * ∏ k ∈ I.nbr j, (1 - x k)) * (1 / (1 - x j) * ∏ k ∈ I.nbr j, (1 / (1 - x k)))
              = x j * (1 / (1 - x j)) *
                  ((∏ k ∈ I.nbr j, (1 - x k)) * ∏ k ∈ I.nbr j, (1 / (1 - x k))) := by ring
            _ = x j / (1 - x j) := by rw [hprod1]; ring

end Inst

end MoserTardos
