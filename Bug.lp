require open aclia.reify;

symbol F: τ int;

compute reify F; // ≡ Var 0 1 ‚ (F ⸬ □)
compute reify ((— 4) * F); // ≡ Var 0 1 ‚ (F ⸬ □)
compute reify (F * (— 4)); // ≡ Var 0 1 ‚ (F ⸬ □)