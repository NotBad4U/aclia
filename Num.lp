require open aclia.Q aclia.Set aclia.Prod aclia.Nat aclia.Z aclia.Bool aclia.HOL aclia.Comp;

symbol † [a: Set] : τ a → τ a → τ a;
rule (@† nat) ↪ (aclia.Nat.+)
with (@† int) ↪ (aclia.Z.+)
with (@† rational) ↪ (aclia.Q.q+);

notation † infix right 20;

symbol ⨪ [a: Set] : τ a → τ a → τ a;
notation ⨪ infix left 20;
rule (@⨪ nat) ↪ (aclia.Nat.-)
with (@⨪ int) ↪ (aclia.Z.-);

print aclia.Nat.-;
print aclia.Z.-;


assert ⊢ (aclia.Nat._10 † aclia.Nat._10): ℕ;
assert ⊢ (12 + 10): ℤ;

symbol ⨱ [a: Set] : τ a → τ a → τ a;
rule (@⨱ nat) ↪ (aclia.Nat.+)
with (@⨱ int) ↪ (aclia.Z.+)
with (@⨱ rational) ↪ (aclia.Q.q+);

notation ⨱ infix right 22;

require open aclia.Prop aclia.Eq aclia.reify;

symbol l1 (x y: ℤ) : π((x † y) ⨪ (x † y) ≠ 1) ≔
begin
  assume x y;
  refine ≐_decides_neq _;
  rewrite left .[z in z ≐ _] reify_correct;
  set e ≔ reify ((x † y) ⨪ (x † y));
  rewrite .[z in val z] eta_prod;
  compute e;
  rewrite left norm_correct (e ₁) (e ₂) _ { refine ⊤ᵢ } { refine Lt≠Eq }
end;