import OMAReductions.R_OeisA182126_conjecture3_R1

-- Step OeisA182126.conjecture3.R1.H2: hypothesis H2 of reduction OeisA182126.conjecture3.R1
-- Credit: @GiridhariPradeep
-- H2 := ∀ n : ℕ, 0 < n → n ≤ 61 → (OeisA182126.a n).Prime → OeisA182126.a n ∈ ([2, 7, 11, 13, 29] : List ℕ)

/-!
A finite computation. The first 63 primes are listed explicitly and identified with
`Nat.nth Nat.Prime` through `Nat.nth_count`; then `a n` for `1 ≤ n ≤ 61` is evaluated by `decide`.
-/

namespace OMA.OeisA182126H2

/-- The first 63 primes. -/
def L : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,
  103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,
  229,233,239,241,251,257,263,269,271,277,281,283,293,307]

set_option maxRecDepth 100000 in
lemma L_spec : ∀ i < 63, Nat.count Nat.Prime (L.getD i 0) = i ∧ Nat.Prime (L.getD i 0) := by
  decide +kernel

lemma nth_eq (i : ℕ) (hi : i < 63) : Nat.nth Nat.Prime i = L.getD i 0 := by
  obtain ⟨h1, h2⟩ := L_spec i hi
  have h := Nat.nth_count h2
  rw [h1] at h
  exact h

/-- The computable version of `a`. -/
def b (n : ℕ) : ℕ := (L.getD (n - 1) 0 * L.getD n 0) % L.getD (n + 1) 0

lemma a_eq (n : ℕ) (h0 : 0 < n) (h1 : n ≤ 61) : OeisA182126.a n = b n := by
  unfold OeisA182126.a OeisA182126.prime b
  rw [if_neg (by omega), nth_eq (n - 1) (by omega), nth_eq (n + 1 - 1) (by omega),
    nth_eq (n + 2 - 1) (by omega)]
  rw [show n + 1 - 1 = n by omega, show n + 2 - 1 = n + 1 by omega]

set_option maxRecDepth 100000 in
lemma b_spec : ∀ n < 62, 0 < n → (b n).Prime → b n ∈ ([2, 7, 11, 13, 29] : List ℕ) := by
  decide +kernel

end OMA.OeisA182126H2

theorem OMA.solution : OMA.R_OeisA182126_conjecture3_R1.H2 := by
  intro n h0 h1 hp
  rw [OMA.OeisA182126H2.a_eq n h0 h1] at hp ⊢
  exact OMA.OeisA182126H2.b_spec n (by omega) h0 hp
