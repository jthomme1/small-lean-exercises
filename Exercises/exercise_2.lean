open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := (fun h: ∃ _ : α, r => Exists.elim h (fun _ => id))
example (a : α) : r → (∃ _ : α, r) := (fun r_p => ⟨a, r_p⟩ )

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := Iff.intro
  (fun h => match h with
    | ⟨ s, t ⟩ => ⟨ ⟨s, t.left⟩, t.right⟩ )
  (fun h: (∃ x, p x) ∧ r => match h.left with
    | ⟨x_p, p_x⟩ => ⟨ x_p, p_x, h.right ⟩ )


example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := Iff.intro
  (fun h => match h with
    | ⟨ x, px_qx ⟩ => Or.elim px_qx (fun p_x: p x => Or.inl (Exists.intro x p_x)) (fun q_x: q x => Or.inr (Exists.intro x q_x))
  )
  (fun h => Or.elim h (fun exists_px => Exists.elim exists_px (fun a p_a => Exists.intro a (Or.inl p_a))) (fun ⟨a, q_x⟩ => Exists.intro a (Or.inr q_x)))

example : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro ⟨x, p_x⟩ 
  apply (Exists.intro x (Or.inl p_x))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := Iff.intro
  (fun h ⟨x, hx⟩ => hx (h x))
  (fun not_exists_x_px x =>
  have all_not_not: ∀a, ¬¬ p a := (fun a pa => not_exists_x_px (Exists.intro a pa))
  have not_not_x: ¬¬ p x := by simp[all_not_not]
  show p x by apply byContradiction not_not_x
  )

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
          apply And.intro; repeat (first | simp[Or.inl hp] | simp[Or.inr hp])

