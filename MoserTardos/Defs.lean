/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.FiniteProb

/-!
# The Moser–Tardos resampling algorithm: definitions

The *variable setting* of the Lovász Local Lemma. There are finitely many independent random
variables indexed by `ι`, with values in a finite type `α` and laws `P i` (a product space in the
sense of `PseudorandomLib.FiniteProb`). There are `n` bad events; event `j` is determined by the
variables in `vbl j`. Two events are neighbours when their variable sets meet.

The Moser–Tardos algorithm samples all variables, and while some event holds it picks the first
one (in the order of `Fin n`) and resamples its variables. We run it on a *resampling table*
`T : ι → ℕ → α`: variable `i` takes the values `T i 0, T i 1, …` in turn. On a table, the run is
deterministic.

* `Inst`: an instance (variable sets and events, each event determined by its variables);
* `Inst.nbr`, `Inst.nbrIncl`: neighbours of an event (excluding, resp. including, itself);
* `Inst.run`: the state (current assignment and table counters) after `t` steps;
* `Inst.logAt`: the event resampled at step `s` (`none` once the algorithm has stopped);
* `Inst.count`: the number of resamplings of event `j` among the first `t` steps;
* `tableLaw`: the law of a table of depth `L` (independent entries, entry `(i, l)` with law
  `P i`), and `Inst.extend`: a table of depth `L` read as an infinite table.
-/

@[expose] public section

namespace MoserTardos

open Finset Pseudorandom

open Classical in
/-- An instance of the variable setting: `n` events on assignments `ι → α`, event `j` determined
by the variables in `vbl j`. -/
structure Inst (ι α : Type*) (n : ℕ) where
  /-- The variables of each event. -/
  vbl : Fin n → Finset ι
  /-- The events. -/
  ev : Fin n → (ι → α) → Prop
  /-- Each event is determined by its variables. -/
  dep : ∀ j (ω ω' : ι → α), (∀ i ∈ vbl j, ω i = ω' i) → (ev j ω ↔ ev j ω')

namespace Inst

variable {ι α : Type*} {n : ℕ} (I : Inst ι α n)

open Classical in
/-- The neighbours of event `j`: the other events sharing a variable with it. -/
noncomputable def nbr (j : Fin n) : Finset (Fin n) :=
  univ.filter fun k => k ≠ j ∧ ¬ Disjoint (I.vbl j) (I.vbl k)

theorem mem_nbr {j k : Fin n} : k ∈ I.nbr j ↔ k ≠ j ∧ ¬ Disjoint (I.vbl j) (I.vbl k) := by
  classical
  unfold nbr
  simp

/-- The neighbours of event `j` together with `j`. -/
noncomputable def nbrIncl [DecidableEq ι] (j : Fin n) : Finset (Fin n) := insert j (I.nbr j)

/-- The state of the algorithm: the current assignment and, for each variable, the index of the
next table entry to use. -/
structure State (ι α : Type*) where
  /-- The current assignment. -/
  val : ι → α
  /-- The next table index of each variable. -/
  cnt : ι → ℕ

open Classical in
/-- The first event (in the order of `Fin n`) holding at `ω`, if any. -/
noncomputable def firstViolated (ω : ι → α) : Option (Fin n) :=
  if h : (univ.filter fun j => I.ev j ω).Nonempty then some ((univ.filter fun j => I.ev j ω).min' h)
  else none

open Classical in
/-- Resample the variables of event `j` from the table `T`. -/
noncomputable def resample (T : ι → ℕ → α) (j : Fin n) (st : State ι α) : State ι α where
  val i := if i ∈ I.vbl j then T i (st.cnt i) else st.val i
  cnt i := if i ∈ I.vbl j then st.cnt i + 1 else st.cnt i

/-- One step of the algorithm: resample the first violated event, if any. -/
noncomputable def step (T : ι → ℕ → α) (st : State ι α) : State ι α :=
  match I.firstViolated st.val with
  | none => st
  | some j => I.resample T j st

/-- The initial state: every variable takes its first table entry. -/
def init (T : ι → ℕ → α) : State ι α where
  val i := T i 0
  cnt _ := 1

/-- The state after `t` steps. -/
noncomputable def run (T : ι → ℕ → α) : ℕ → State ι α
  | 0 => init T
  | t + 1 => I.step T (run T t)

/-- The event resampled at step `s` (`none` if the algorithm has stopped). -/
noncomputable def logAt (T : ι → ℕ → α) (s : ℕ) : Option (Fin n) := I.firstViolated (I.run T s).val

open Classical in
/-- The number of resamplings of event `j` among the first `t` steps. -/
noncomputable def count (T : ι → ℕ → α) (j : Fin n) (t : ℕ) : ℕ :=
  ((range t).filter fun s => I.logAt T s = some j).card

open Classical in
/-- The total number of resamplings among the first `t` steps. -/
noncomputable def totalCount (T : ι → ℕ → α) (t : ℕ) : ℕ :=
  ((range t).filter fun s => (I.logAt T s).isSome).card

end Inst

/-- The law of a resampling table of depth `L`: independent entries, entry `(i, l)` with law
`P i`. -/
def tableLaw {ι α : Type*} (P : ι → α → ℝ) (L : ℕ) : ι × Fin L → α → ℝ := fun e => P e.1

/-- A table of depth `L` read as an infinite table (entries beyond depth `L` are `a₀`). -/
def extend {ι α : Type*} {L : ℕ} (a₀ : α) (T : ι × Fin L → α) : ι → ℕ → α :=
  fun i k => if h : k < L then T (i, ⟨k, h⟩) else a₀

end MoserTardos
