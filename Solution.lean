/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MoserTardos.Main

/-!
# The Moser–Tardos theorem

R. A. Moser and G. Tardos, *A constructive proof of the general Lovász Local Lemma*, J. ACM 57
(2010), Art. 11, doi:10.1145/1667053.1667060.

The *variable setting*: finitely many independent random variables indexed by `ι`, with values in
a finite type `α` and laws `P i`; `n` bad events, event `j` determined by the variables in
`vbl j`; events sharing a variable are neighbours (`nbr`). The Moser–Tardos algorithm samples all
variables and, while some event holds, picks the first one (in the order of `Fin n`) and
resamples its variables. It is run on a *resampling table* `T : ι → ℕ → α`: variable `i` takes the
values `T i 0, T i 1, …` in turn (`run`, `logAt`, `count`). A random table of depth `t` has
independent entries, the entries of variable `i` with law `P i` (`tableLaw`); entries beyond depth
`t` are read as a fixed `a₀` (`extend`), which does not affect the first `t` steps.

Statements in the namespace `MoserTardosTheorem`, under the condition of the Lovász Local Lemma
`P(ev j) ≤ x j ∏_{k ∈ nbr j} (1 - x k)` with `0 ≤ x j < 1`:

* `expected_count_le`: the expected number of resamplings of event `j` among the first `t` steps
  is at most `x j / (1 - x j)` (Moser–Tardos, Theorem 1.2);
* `expected_totalCount_le`: the expected total number of resamplings among the first `t` steps is
  at most `∑ j, x j / (1 - x j)`;
* `pProb_running_le`: the probability that the algorithm has not stopped after `t` steps is at
  most `(∑ j, x j / (1 - x j)) / t`;
* `exists_avoiding`: some assignment avoids all the events (the Lovász Local Lemma in the variable
  setting).

The finite product spaces (`IsPMF`, `pw`, `pE`, `pProb`) are copied verbatim from the registered
entry on pseudorandom hypergraph matchings (`PseudorandomLib.FiniteProb`). The Mathlib definitions
used are reproduced in `MATHLIB_DEFINITIONS.md`.
-/

@[expose] public section

namespace MoserTardosTheorem

open Finset

section Prob

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

end Prob

variable {ι α : Type*} {n : ℕ}

open Classical in
/-- The neighbours of event `j`: the other events sharing a variable with it. -/
noncomputable def nbr (vbl : Fin n → Finset ι) (j : Fin n) : Finset (Fin n) :=
  univ.filter fun k => k ≠ j ∧ ¬ Disjoint (vbl j) (vbl k)

open Classical in
/-- The first event (in the order of `Fin n`) holding at `ω`, if any. -/
noncomputable def firstViolated (ev : Fin n → (ι → α) → Prop) (ω : ι → α) : Option (Fin n) :=
  if h : (univ.filter fun j => ev j ω).Nonempty then some ((univ.filter fun j => ev j ω).min' h)
  else none

open Classical in
/-- One step of the algorithm on a state (current assignment, next table index of each
variable): resample the variables of the first violated event from the table, if any. -/
noncomputable def step (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop)
    (T : ι → ℕ → α) (st : (ι → α) × (ι → ℕ)) : (ι → α) × (ι → ℕ) :=
  match firstViolated ev st.1 with
  | none => st
  | some j => (fun i => if i ∈ vbl j then T i (st.2 i) else st.1 i,
      fun i => if i ∈ vbl j then st.2 i + 1 else st.2 i)

/-- The state after `t` steps; initially every variable takes its first table entry. -/
noncomputable def run (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop) (T : ι → ℕ → α) :
    ℕ → (ι → α) × (ι → ℕ)
  | 0 => (fun i => T i 0, fun _ => 1)
  | t + 1 => step vbl ev T (run vbl ev T t)

/-- The event resampled at step `s` (`none` once the algorithm has stopped). -/
noncomputable def logAt (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop) (T : ι → ℕ → α)
    (s : ℕ) : Option (Fin n) :=
  firstViolated ev (run vbl ev T s).1

open Classical in
/-- The number of resamplings of event `j` among the first `t` steps. -/
noncomputable def count (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop)
    (T : ι → ℕ → α) (j : Fin n) (t : ℕ) : ℕ :=
  ((range t).filter fun s => logAt vbl ev T s = some j).card

open Classical in
/-- The total number of resamplings among the first `t` steps. -/
noncomputable def totalCount (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop)
    (T : ι → ℕ → α) (t : ℕ) : ℕ :=
  ((range t).filter fun s => (logAt vbl ev T s).isSome).card

/-- The law of a resampling table of depth `L`: independent entries, entry `(i, l)` with law
`P i`. -/
def tableLaw (P : ι → α → ℝ) (L : ℕ) : ι × Fin L → α → ℝ := fun e => P e.1

/-- A table of depth `L` read as an infinite table (entries beyond depth `L` are `a₀`). -/
def extend {L : ℕ} (a₀ : α) (T : ι × Fin L → α) : ι → ℕ → α :=
  fun i k => if h : k < L then T (i, ⟨k, h⟩) else a₀

/-! ### Transport to the library (`MoserTardos.Inst`) -/

/-- The instance of the library with these variable sets and events. -/
def inst (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop)
    (hdep : ∀ j (ω ω' : ι → α), (∀ i ∈ vbl j, ω i = ω' i) → (ev j ω ↔ ev j ω')) :
    MoserTardos.Inst ι α n := ⟨vbl, ev, hdep⟩

theorem run_eq (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop)
    (hdep : ∀ j (ω ω' : ι → α), (∀ i ∈ vbl j, ω i = ω' i) → (ev j ω ↔ ev j ω'))
    (T : ι → ℕ → α) : ∀ t, run vbl ev T t =
      (((inst vbl ev hdep).run T t).val, ((inst vbl ev hdep).run T t).cnt)
  | 0 => rfl
  | t + 1 => by
    rw [run, run_eq vbl ev hdep T t]
    show _ = (((inst vbl ev hdep).step T ((inst vbl ev hdep).run T t)).val,
      ((inst vbl ev hdep).step T ((inst vbl ev hdep).run T t)).cnt)
    unfold step MoserTardos.Inst.step
    have hf : firstViolated ev ((inst vbl ev hdep).run T t).val =
        (inst vbl ev hdep).firstViolated ((inst vbl ev hdep).run T t).val := rfl
    simp only [hf]
    rcases (inst vbl ev hdep).firstViolated ((inst vbl ev hdep).run T t).val with _ | j
    · rfl
    · rfl

theorem logAt_eq' (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop)
    (hdep : ∀ j (ω ω' : ι → α), (∀ i ∈ vbl j, ω i = ω' i) → (ev j ω ↔ ev j ω')) :
    logAt vbl ev = (inst vbl ev hdep).logAt := by
  funext T s
  unfold logAt MoserTardos.Inst.logAt
  rw [run_eq vbl ev hdep]
  rfl

theorem count_eq' (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop)
    (hdep : ∀ j (ω ω' : ι → α), (∀ i ∈ vbl j, ω i = ω' i) → (ev j ω ↔ ev j ω')) :
    count vbl ev = (inst vbl ev hdep).count := by
  funext T j t
  unfold count MoserTardos.Inst.count
  rw [logAt_eq' vbl ev hdep]

theorem totalCount_eq' (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop)
    (hdep : ∀ j (ω ω' : ι → α), (∀ i ∈ vbl j, ω i = ω' i) → (ev j ω ↔ ev j ω')) :
    totalCount vbl ev = (inst vbl ev hdep).totalCount := by
  funext T t
  unfold totalCount MoserTardos.Inst.totalCount
  rw [logAt_eq' vbl ev hdep]

theorem pE_eq {κ : Type*} [Fintype κ] [DecidableEq κ] [Fintype α] (Q : κ → α → ℝ) (f : (κ → α) → ℝ) :
    pE Q f = Pseudorandom.pE Q f := rfl

theorem pProb_eq {κ : Type*} [Fintype κ] [DecidableEq κ] [Fintype α] (Q : κ → α → ℝ)
    (S : (κ → α) → Prop) : pProb Q S = Pseudorandom.pProb Q S := rfl

variable [Fintype ι] [DecidableEq ι] [Fintype α]

/-- **The Moser–Tardos theorem.** Under the condition of the Lovász Local Lemma, the expected
number of resamplings of event `j` among the first `t` steps, on a random table of depth `t`, is
at most `x j / (1 - x j)`. -/
theorem expected_count_le (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop)
    (hdep : ∀ j (ω ω' : ι → α), (∀ i ∈ vbl j, ω i = ω' i) → (ev j ω ↔ ev j ω'))
    {P : ι → α → ℝ} (hP : IsPMF P) (a₀ : α) {x : Fin n → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hx1 : ∀ j, x j < 1) (hlll : ∀ j, pProb P (ev j) ≤ x j * ∏ k ∈ nbr vbl j, (1 - x k)) (j : Fin n) (t : ℕ) :
    pE (tableLaw P t) (fun T => (count vbl ev (extend a₀ T) j t : ℝ)) ≤ x j / (1 - x j) := by
  rw [pE_eq, count_eq' vbl ev hdep]
  exact (inst vbl ev hdep).expected_count_le hP a₀ hx0 hx1 hlll j t

/-- The expected total number of resamplings among the first `t` steps is at most
`∑ j, x j / (1 - x j)`. -/
theorem expected_totalCount_le (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop)
    (hdep : ∀ j (ω ω' : ι → α), (∀ i ∈ vbl j, ω i = ω' i) → (ev j ω ↔ ev j ω'))
    {P : ι → α → ℝ} (hP : IsPMF P) (a₀ : α) {x : Fin n → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hx1 : ∀ j, x j < 1) (hlll : ∀ j, pProb P (ev j) ≤ x j * ∏ k ∈ nbr vbl j, (1 - x k)) (t : ℕ) :
    pE (tableLaw P t) (fun T => (totalCount vbl ev (extend a₀ T) t : ℝ)) ≤
      ∑ j, x j / (1 - x j) := by
  rw [pE_eq, totalCount_eq' vbl ev hdep]
  exact (inst vbl ev hdep).expected_totalCount_le hP a₀ hx0 hx1 hlll t

/-- The probability that the algorithm has not stopped after `t` steps is at most
`(∑ j, x j / (1 - x j)) / t`. -/
theorem pProb_running_le (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop)
    (hdep : ∀ j (ω ω' : ι → α), (∀ i ∈ vbl j, ω i = ω' i) → (ev j ω ↔ ev j ω'))
    {P : ι → α → ℝ} (hP : IsPMF P) (a₀ : α) {x : Fin n → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hx1 : ∀ j, x j < 1) (hlll : ∀ j, pProb P (ev j) ≤ x j * ∏ k ∈ nbr vbl j, (1 - x k)) {t : ℕ} (ht : 0 < t) :
    pProb (tableLaw P t) (fun T => ∀ s < t, (logAt vbl ev (extend a₀ T) s).isSome) ≤
      (∑ j, x j / (1 - x j)) / t := by
  rw [pProb_eq, logAt_eq' vbl ev hdep]
  exact (inst vbl ev hdep).pProb_running_le hP a₀ hx0 hx1 hlll ht

/-- **The Lovász Local Lemma** in the variable setting: under its condition some assignment
avoids all the events. -/
theorem exists_avoiding (vbl : Fin n → Finset ι) (ev : Fin n → (ι → α) → Prop)
    (hdep : ∀ j (ω ω' : ι → α), (∀ i ∈ vbl j, ω i = ω' i) → (ev j ω ↔ ev j ω'))
    {P : ι → α → ℝ} (hP : IsPMF P) (a₀ : α) {x : Fin n → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hx1 : ∀ j, x j < 1) (hlll : ∀ j, pProb P (ev j) ≤ x j * ∏ k ∈ nbr vbl j, (1 - x k)) :
    ∃ ω : ι → α, ∀ j, ¬ ev j ω := (inst vbl ev hdep).exists_avoiding hP a₀ hx0 hx1 hlll

end MoserTardosTheorem
