// // classical logic

// require open aclia.Set aclia.Prop aclia.FOL;

// symbol em p : π (p ∨ ¬ p); // excluded middle

// opaque symbol ¬¬ₑ p : π (¬ ¬ p) → π p ≔
// begin
// assume p nnp; apply ∨ₑ (em p)
// { assume h; refine h }
// { assume np; apply ⊥ₑ; refine nnp np }
// end;

// opaque symbol ∨¬ᵢ p q : π (p ⇒ q) → π (¬ p ∨ q) ≔
// begin
// assume p q pq; apply ∨ₑ (em p)
// { assume hp; refine ∨ᵢ₂ _; refine pq hp }
// { assume np; refine ∨ᵢ₁ np }
// end;

// opaque symbol ∃¬ᵢ a p : π (¬ (∀ p)) → π (`∃ x : τ a, ¬ (p x)) ≔
// begin
// assume a p not_all_p; apply ∨ₑ (em (`∃ x, ¬ (p x)))
// { assume h; apply h }
// { assume not_ex_not_p; apply ⊥ₑ; apply not_all_p;
//   have h: π (`∀ x, ¬ ¬ (p x))
//     { refine ¬∃ (λ x, ¬ (p x)) _; refine not_ex_not_p};
//   assume x; apply ¬¬ₑ; refine h x
// }
// end;


// opaque symbol not_and_or [p q] : π (¬ (p ∧ q)) → π (¬ p ∨ ¬ q) ≔
// begin
//     assume p q H;
//     have g: π ((p ∨ ¬ p)  ⇒  ¬ p ∨ ¬ q) {
//         assume classic;
//         apply ∨ₑ classic
//         {
//             assume Hp;
//             apply ∨ᵢ₂;
//             assume Hq;
//             refine H _;
//             apply ∧ᵢ { refine Hp } { refine Hq }
//         }
//         { assume Hnp; apply ∨ᵢ₁; refine Hnp }
//     };
//     refine g (em p)
// end;

// opaque symbol or_not_and [p q] : π (¬ p ∨ ¬ q) → π (¬ (p ∧ q)) ≔
// begin
// admitted;

// opaque symbol not_or_and [p q] : π (¬ (p ∨ q)) → π (¬ p ∧ ¬ q) ≔
// begin
// admitted;

// opaque symbol and_not_or [p q] : π (¬ p ∧ ¬ q) → π (¬ (p ∨ q)) ≔
// begin
// admitted;

// opaque symbol or_to_imply [p q] : π (¬ p ∨ q) → π (p ⇒ q) ≔
// begin
// admitted;

// opaque symbol imply_to_and [p q] : π (¬ p ⇒ q) → π (p ∧ (¬ q)) ≔
// begin
// admitted;

// opaque symbol imply_to_or [p q] : π (p ⇒ q) → π ((¬ p) ∨ q) ≔
// begin
// admitted;

// opaque symbol pierce [p] : π ((p ⇒ ⊥) ⇒ p) → π p ≔
// begin
// admitted;

// opaque symbol ¬ₑ [p q] : π (¬ p) → π p → π q ≔
// begin assume p q Hnp Hp; refine ⊥ₑ (Hnp Hp) end;

// opaque symbol nforall_ex [a] p : π ((¬ (`∀ (x : τ a), p x)) ⇔ (`∃ (x : τ a), ¬ p x)) ≔ begin
//     assume a p;
//     apply ∧ᵢ
//     {
//         admit
//     }
//     {
//         assume He H;
//         apply ∃ₑ He;
//         assume x hp;
//         refine hp _; 
//         apply H x
//     }
// end;

// opaque symbol nex_forall [a] p : π ((¬ (`∃ (x : τ a), p x)) ⇔ (`∀ (x : τ a), ¬ p x)) ≔ begin admit end;

// classical logic

require open aclia.Set aclia.Prop aclia.FOL;

symbol em p : π (p ∨ ¬ p); // excluded middle

opaque symbol ¬¬ₑ p : π (¬ ¬ p) → π p ≔
begin
assume p nnp; apply ∨ₑ (em p)
{ assume h; refine h }
{ assume np; apply ⊥ₑ; refine nnp np }
end;

opaque symbol ∨¬ᵢ p q : π (p ⇒ q) → π (¬ p ∨ q) ≔
begin
assume p q pq; apply ∨ₑ (em p)
{ assume hp; refine ∨ᵢ₂ _; refine pq hp }
{ assume np; refine ∨ᵢ₁ np }
end;

opaque symbol ∃¬ᵢ a p : π (¬ (∀ p)) → π (`∃ x : τ a, ¬ (p x)) ≔
begin
assume a p not_all_p; apply ∨ₑ (em (`∃ x, ¬ (p x)))
{ assume h; apply h }
{ assume not_ex_not_p; apply ⊥ₑ; apply not_all_p;
  have h: π (`∀ x, ¬ ¬ (p x))
    { refine ¬∃ (λ x, ¬ (p x)) _; refine not_ex_not_p};
  assume x; apply ¬¬ₑ; refine h x
}
end;

opaque symbol not_and_or [p q] : π (¬ (p ∧ q)) → π (¬ p ∨ ¬ q) ≔
begin
  assume p q H;
  admit
end;

opaque symbol or_not_and [p q] : π (¬ p ∨ ¬ q) → π (¬ (p ∧ q)) ≔
begin
admitted;

opaque symbol not_or_and [p q] : π (¬ (p ∨ q)) → π (¬ p ∧ ¬ q) ≔
begin
admitted;

opaque symbol and_not_or [p q] : π (¬ p ∧ ¬ q) → π (¬ (p ∨ q)) ≔
begin
admitted;

opaque symbol or_to_imply [p q] : π ((¬ p) ∨ q) → π (p ⇒ q) ≔
begin
admitted;

opaque symbol imply_to_and [p q] : π (¬ (p ⇒ q)) → π (p ∧ (¬ q)) ≔
begin
admitted;

opaque symbol imply_to_or [p q] : π (p ⇒ q) → π ((¬ p) ∨ q) ≔
begin
admitted;

opaque symbol pierce [p] : π ((p ⇒ ⊥) ⇒ p) → π p ≔
begin
admitted;

opaque symbol ¬ₑ [p q] : π (¬ p) → π p → π q ≔
begin assume p q Hnp Hp; refine ⊥ₑ (Hnp Hp) end;


opaque symbol nforall_ex [a] p : π ((¬ (`∀ (x : τ a), p x)) ⇔ (`∃ (x : τ a), ¬ p x)) ≔ begin admit end;

opaque symbol nex_forall [a] p : π ((¬ (`∃ (x : τ a), p x)) ⇔ (`∀ (x : τ a), ¬ p x)) ≔ begin admit end;
