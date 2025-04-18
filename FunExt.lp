require open aclia.Set aclia.Prop aclia.Eq aclia.FOL aclia.HOL;

symbol funExt [a b] (f g : τ (a ⤳ b)) : π(`∀ x, f x = g x) → π(f = g);

