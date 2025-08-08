variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := Iff.intro (fun h: p ∧ q => show q ∧ p from And.intro h.right h.left) (fun h: q ∧ p => show p ∧ q from And.intro h.right h.left)
example : p ∨ q ↔ q ∨ p := Iff.intro
  (fun h: p ∨ q => Or.elim h Or.inr Or.inl)
  (fun h: q ∨ p => Or.elim h Or.inr Or.inl)


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := Iff.intro
  (fun h: (p ∧ q) ∧ r => And.intro (h.left.left) (And.intro h.left.right h.right))
  (fun h: p ∧ (q ∧ r) => And.intro (And.intro h.left h.right.left) h.right.right)


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := Iff.intro
  (fun pqr: (p ∨ q) ∨ r => Or.elim pqr
    (fun pq: p ∨ q => Or.elim pq (Or.intro_left (q ∨ r))
      (Or.inr ∘ Or.inl)
    )
    (Or.inr ∘ Or.inr)
  )
  (fun pqr: p ∨ q ∨ r => Or.elim pqr
    (Or.inl ∘ Or.inl)
    (fun q_or_r: q ∨ r => Or.elim q_or_r
      (Or.inl ∘ Or.inr)
      (Or.inr)
    )
  )
