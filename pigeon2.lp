require open aclia.Prop;

require open aclia.Set;

require open aclia.Eq;

require open aclia.Z;

require open aclia.FOL;

require open aclia.Prod;

require open aclia.HOL;

require open aclia.Impred;

require open aclia.Classic;

require open aclia.PropExt;

require open aclia.Alethe;

require open aclia.reify;

symbol p_0_0 : τ (int);

symbol p_0_1 : τ (int);

symbol p_1_0 : τ (int);

symbol p_1_1 : τ (int);

symbol p_2_0 : τ (int);

symbol p_2_1 : τ (int);

symbol p_3 ≔ (p_0_1 + p_1_1 + p_2_1);

symbol p_6 ≔ ((— 1) * (p_0_0 + p_0_1));

symbol p_7 ≔ (p_0_0 + p_0_1);

symbol p_8 ≔ ((— 1) * 1);

symbol p_11 ≔ ((— 1) * (p_1_0 + p_1_1));

symbol p_12 ≔ (p_1_0 + p_1_1);

symbol p_15 ≔ ((— 1) * (p_2_0 + p_2_1));

symbol p_16 ≔ (p_2_0 + p_2_1);

symbol p_19 ≔ (p_0_0 + p_1_0 + p_2_0);

opaque symbol t1 : π̇ ((¬ ((p_3 ≤ 1)))
     ⟇ (¬ ((p_6 ≤ p_8)))
     ⟇ (¬ ((p_11 ≤ p_8)))
     ⟇ (¬ ((p_15 ≤ p_8)))
     ⟇ (¬ ((p_19 < 2)))
     ⟇ ((p_3 + p_6 + p_11 + p_15 + p_19) < (1 + p_8 + p_8 + p_8 + 2))
    ⟇ ▩) ≔ 
begin
have Hla : π̇ (((¬ (((p_0_1 + p_1_1 + p_2_1) ≤ 1))) ∨ (¬ ((((— 1) * (p_0_0 + p_0_1)) ≤ ((— 1) * 1)))) ∨ (¬ ((((— 1) * (p_1_0 + p_1_1)) ≤ ((— 1) * 1)))) ∨ (¬ ((((— 1) * (p_2_0 + p_2_1)) ≤ ((— 1) * 1)))) ∨ (¬ (((p_0_0 + p_1_0 + p_2_0) < 2))) ∨ (((p_0_1 + p_1_1 + p_2_1) + ((— 1) * (p_0_0 + p_0_1)) + ((— 1) * (p_1_0 + p_1_1)) + ((— 1) * (p_2_0 + p_2_1)) + (p_0_0 + p_1_0 + p_2_0)) < (1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 2)))
        ⟇ ▩) {
    apply ∨ᵢ₁;
    rewrite .[x in _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ x] Zlt_not_ge;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_lt_eq;
    rewrite Z_diff_geq_Z0_eq ((— (p_0_1 + p_1_1 + p_2_1))) ((— 1));
    rewrite Z_diff_geq_Z0_eq ((— ((— 1) * (p_0_0 + p_0_1)))) ((— ((— 1) * 1)));
    rewrite Z_diff_geq_Z0_eq ((— ((— 1) * (p_1_0 + p_1_1)))) ((— ((— 1) * 1)));
    rewrite Z_diff_geq_Z0_eq ((— ((— 1) * (p_2_0 + p_2_1)))) ((— ((— 1) * 1)));
    rewrite Z_diff_gt_Z0_eq ((— (p_0_0 + p_1_0 + p_2_0))) ((— 2));
    rewrite Z_diff_geq_Z0_eq (((p_0_1 + p_1_1 + p_2_1) + ((— 1) * (p_0_0 + p_0_1)) + ((— 1) * (p_1_0 + p_1_1)) + ((— 1) * (p_2_0 + p_2_1)) + (p_0_0 + p_1_0 + p_2_0))) ((1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 2));
    rewrite Zgt_le_succ_r_eq (((— (p_0_0 + p_1_0 + p_2_0)) - (— 2))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (p_0_1 + p_1_1 + p_2_1)) - (— 1))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— ((— 1) * (p_0_0 + p_0_1))) - (— ((— 1) * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— ((— 1) * (p_1_0 + p_1_1))) - (— ((— 1) * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— ((— 1) * (p_2_0 + p_2_1))) - (— ((— 1) * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (p_0_0 + p_1_0 + p_2_0)) - (— 2))) ((0 + 1));
    rewrite Zmult_ge_compat_eq (1) ((((p_0_1 + p_1_1 + p_2_1) + ((— 1) * (p_0_0 + p_0_1)) + ((— 1) * (p_1_0 + p_1_1)) + ((— 1) * (p_2_0 + p_2_1)) + (p_0_0 + p_1_0 + p_2_0)) - (1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 2))) (0);
    try rewrite Z_eq_antisym;
    rewrite imp_eq_or;
    assume H0;
    rewrite imp_eq_or;
    assume H1;
    rewrite imp_eq_or;
    assume H2;
    rewrite imp_eq_or;
    assume H3;
    rewrite imp_eq_or;
    assume H4;
    assume H5;
    set H0l' ≔ (1 * ((— (p_0_1 + p_1_1 + p_2_1)) - (— 1)));
    set H0r' ≔ (1 * 0);
    set H1l' ≔ (1 * ((— ((— 1) * (p_0_0 + p_0_1))) - (— ((— 1) * 1))));
    set H1r' ≔ (1 * 0);
    set H2l' ≔ (1 * ((— ((— 1) * (p_1_0 + p_1_1))) - (— ((— 1) * 1))));
    set H2r' ≔ (1 * 0);
    set H3l' ≔ (1 * ((— ((— 1) * (p_2_0 + p_2_1))) - (— ((— 1) * 1))));
    set H3r' ≔ (1 * 0);
    set H4l' ≔ (1 * ((— (p_0_0 + p_1_0 + p_2_0)) - (— 2)));
    set H4r' ≔ (1 * (0 + 1));
    set H5l' ≔ (1 * (((p_0_1 + p_1_1 + p_2_1) + ((— 1) * (p_0_0 + p_0_1)) + ((— 1) * (p_1_0 + p_1_1)) + ((— 1) * (p_2_0 + p_2_1)) + (p_0_0 + p_1_0 + p_2_0)) - (1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 2)));
    set H5r' ≔ (1 * 0);
    set l ≔  (H0l' + H1l' + H2l' + H3l' + H4l' + H5l');
    set r ≔  (H0r' + H1r' + H2r' + H3r' + H4r' + H5r');
    have sum : π (l ≥ r) {
        refine (Zsum_geq_s H0l' H0r' (H1l' + H2l' + H3l' + H4l' + H5l') (H1r' + H2r' + H3r' + H4r' + H5r') H0 (Zsum_geq_s H1l' H1r' (H2l' + H3l' + H4l' + H5l') (H2r' + H3r' + H4r' + H5r') H1 (Zsum_geq_s H2l' H2r' (H3l' + H4l' + H5l') (H3r' + H4r' + H5r') H2 (Zsum_geq_s H3l' H3r' (H4l' + H5l') (H4r' + H5r') H3 (Zsum_geq_s H4l' H4r' H5l' H5r' H4 H5)))))
    };
    refine sum _;
    rewrite left reify_correct l;
    rewrite left reify_correct r;
    set l' ≔ reify l;
    set r' ≔ reify r;
    rewrite eta_prod l';
    rewrite eta_prod r';
    rewrite left norm_correct (l' ₁) (l' ₂) _ { refine ⊤ᵢ } { print  <; apply ⊤ᵢ };
};
simplify;
rewrite or_identity_r;
apply (π̇ₗ Hla);
end;
