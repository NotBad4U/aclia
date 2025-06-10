require open aclia.Prop;

require open aclia.Set;

require open aclia.Eq;

require open aclia.Z;

require open aclia.Classic;

require open aclia.Alethe;

require open aclia.Lia;

symbol p_0_0 : τ (int);

symbol p_0_1 : τ (int);

symbol p_1_0 : τ (int);

symbol p_1_1 : τ (int);

symbol p_2_0 : τ (int);

symbol p_2_1 : τ (int);

symbol p_2 ≔ ((((p_0_1 + p_1_1 + p_2_1) + ((— 1) * (p_0_0 + p_0_1)) + ((— 1) * (p_1_0 + p_1_1)) + ((— 1) * (p_2_0 + p_2_1)) + (p_0_0 + p_1_0 + p_2_0)) < (1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 2)) = ⊥);

symbol p_3 ≔ (((p_0_1 + p_1_1 + p_2_1) + ((— 1) * (p_0_0 + p_0_1)) + ((— 1) * (p_1_0 + p_1_1)) + ((— 1) * (p_2_0 + p_2_1)) + (p_0_0 + p_1_0 + p_2_0)) < (1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 2));

symbol p_4 ≔ ((p_0_1 + p_1_1 + p_2_1) + ((— 1) * (p_0_0 + p_0_1)) + ((— 1) * (p_1_0 + p_1_1)) + ((— 1) * (p_2_0 + p_2_1)) + (p_0_0 + p_1_0 + p_2_0));

symbol p_5 ≔ (p_0_1 + p_1_1 + p_2_1);

symbol p_6 ≔ ((— 1) * (p_0_0 + p_0_1));

symbol p_7 ≔ (p_0_0 + p_0_1);

symbol p_8 ≔ ((— 1) * (p_1_0 + p_1_1));

symbol p_9 ≔ (p_1_0 + p_1_1);

symbol p_10 ≔ ((— 1) * (p_2_0 + p_2_1));

symbol p_11 ≔ (p_2_0 + p_2_1);

symbol p_12 ≔ (p_0_0 + p_1_0 + p_2_0);

symbol p_13 ≔ (1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 2);

symbol p_14 ≔ ((— 1) * 1);

symbol p_17 ≔ (¬ ((((p_0_1 + p_1_1 + p_2_1) + ((— 1) * (p_0_0 + p_0_1)) + ((— 1) * (p_1_0 + p_1_1)) + ((— 1) * (p_2_0 + p_2_1)) + (p_0_0 + p_1_0 + p_2_0)) ≥ (1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 2))));

symbol p_18 ≔ (((p_0_1 + p_1_1 + p_2_1) + ((— 1) * (p_0_0 + p_0_1)) + ((— 1) * (p_1_0 + p_1_1)) + ((— 1) * (p_2_0 + p_2_1)) + (p_0_0 + p_1_0 + p_2_0)) ≥ (1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 2));

symbol p_20 ≔ (p_0_1 + p_1_1 + p_2_1 + ((— 1) * (p_0_0 + p_0_1)) + ((— 1) * (p_1_0 + p_1_1)) + ((— 1) * (p_2_0 + p_2_1)) + p_0_0 + p_1_0 + p_2_0);

symbol p_25 ≔ (((— 1) * p_0_0) + ((— 1) * p_0_1));

symbol p_26 ≔ ((— 1) * p_0_0);

symbol p_27 ≔ ((— 1) * p_0_1);

symbol p_29 ≔ (((— 1) * p_1_0) + ((— 1) * p_1_1));

symbol p_30 ≔ ((— 1) * p_1_0);

symbol p_31 ≔ ((— 1) * p_1_1);

symbol p_33 ≔ (((— 1) * p_2_0) + ((— 1) * p_2_1));

symbol p_34 ≔ ((— 1) * p_2_0);

symbol p_35 ≔ ((— 1) * p_2_1);

symbol p_40 ≔ (p_0_1 + p_1_1 + p_2_1 + (((— 1) * p_0_0) + ((— 1) * p_0_1)) + (((— 1) * p_1_0) + ((— 1) * p_1_1)) + (((— 1) * p_2_0) + ((— 1) * p_2_1)) + p_0_0 + p_1_0 + p_2_0);

symbol p_48 ≔ (1 + (— 1) + (— 1) + (— 1) + 2);

symbol p_52 ≔ (0 ≥ 0);

symbol p_56 ≔ (¬ (⊤));

symbol p_60 ≔ ((p_0_1 + p_1_1 + p_2_1) ≤ 1);

symbol p_62 ≔ (((— 1) * (p_0_0 + p_0_1)) ≤ ((— 1) * 1));

symbol p_64 ≔ (((— 1) * (p_1_0 + p_1_1)) ≤ ((— 1) * 1));

symbol p_66 ≔ (((— 1) * (p_2_0 + p_2_1)) ≤ ((— 1) * 1));

symbol p_68 ≔ ((p_0_0 + p_1_0 + p_2_0) < 2);

symbol p_70 ≔ (((— 1) < 0) ∧ᶜ ((p_0_0 + p_0_1) ≥ 1));

symbol p_71 ≔ ((— 1) < 0);

symbol p_72 ≔ ((p_0_0 + p_0_1) ≥ 1);

symbol p_74 ≔ (¬ (((— 1) < 0)));

symbol p_77 ≔ (((— 1) < 0) = ⊤);

symbol p_80 ≔ (((— 1) < 0) ∧ᶜ ((p_1_0 + p_1_1) ≥ 1));

symbol p_81 ≔ ((p_1_0 + p_1_1) ≥ 1);

symbol p_85 ≔ (((— 1) < 0) ∧ᶜ ((p_2_0 + p_2_1) ≥ 1));

symbol p_86 ≔ ((p_2_0 + p_2_1) ≥ 1);

symbol p_90 ≔ ((¬ (((p_0_0 + p_1_0 + p_2_0) ≥ 2))) = ((p_0_0 + p_1_0 + p_2_0) < 2));

symbol p_91 ≔ (¬ (((p_0_0 + p_1_0 + p_2_0) ≥ 2)));

symbol p_92 ≔ ((p_0_0 + p_1_0 + p_2_0) ≥ 2);

symbol p_96 ≔ (((p_0_0 + p_1_0 + p_2_0) ≤ 1) = (¬ (((p_0_0 + p_1_0 + p_2_0) ≥ 2))));

symbol p_97 ≔ ((p_0_0 + p_1_0 + p_2_0) ≤ 1);

symbol p_100 ≔ (¬ (((p_0_0 + p_1_0 + p_2_0) ≥ (1 + 1))));

symbol p_101 ≔ ((p_0_0 + p_1_0 + p_2_0) ≥ (1 + 1));

symbol p_102 ≔ (1 + 1);

opaque symbol t29 : π̇ ((¬ ((p_5 ≤ 1)))
     ⟇ (¬ ((p_6 ≤ p_14)))
     ⟇ (¬ ((p_8 ≤ p_14)))
     ⟇ (¬ ((p_10 ≤ p_14)))
     ⟇ (¬ ((p_12 < 2)))
     ⟇ p_3
    ⟇ ▩) ≔ 
begin
have Hla : π̇ (((¬ (((p_0_1 + p_1_1 + p_2_1) ≤ 1))) ∨ᶜ (¬ ((((— 1) * (p_0_0 + p_0_1)) ≤ ((— 1) * 1)))) ∨ᶜ (¬ ((((— 1) * (p_1_0 + p_1_1)) ≤ ((— 1) * 1)))) ∨ᶜ (¬ ((((— 1) * (p_2_0 + p_2_1)) ≤ ((— 1) * 1)))) ∨ᶜ (¬ (((p_0_0 + p_1_0 + p_2_0) < 2))) ∨ᶜ (((p_0_1 + p_1_1 + p_2_1) + ((— 1) * (p_0_0 + p_0_1)) + ((— 1) * (p_1_0 + p_1_1)) + ((— 1) * (p_2_0 + p_2_1)) + (p_0_0 + p_1_0 + p_2_0)) < (1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 2)))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite .[x in _ ∨ᶜ _ ∨ᶜ _ ∨ᶜ _ ∨ᶜ _ ∨ᶜ x] Zlt_not_ge;
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
    apply ⇒ᶜᵢ;
    assume H0;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H1;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H2;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H3;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H4;
    apply ¬ᶜᵢ;
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
    have contra : πᶜ ((denote (reify (H0l' + H1l' + H2l' + H3l' + H4l' + H5l'))) ≥ (denote (reify (H0r' + H1r' + H2r' + H3r' + H4r' + H5r')))) {
        rewrite inj;
        rewrite inj;
        apply (Zsum_geq_s H0l' H0r' (H1l' + H2l' + H3l' + H4l' + H5l') (H1r' + H2r' + H3r' + H4r' + H5r') H0 (Zsum_geq_s H1l' H1r' (H2l' + H3l' + H4l' + H5l') (H2r' + H3r' + H4r' + H5r') H1 (Zsum_geq_s H2l' H2r' (H3l' + H4l' + H5l') (H3r' + H4r' + H5r') H2 (Zsum_geq_s H3l' H3r' (H4l' + H5l') (H4r' + H5r') H3 (Zsum_geq_s H4l' H4r' H5l' H5r' H4 H5)))));
    };
    apply (⇒ᶜₑ' contra);
    apply trivial;
};
simplify;
rewrite or_identity_r;
apply (π̇ₗ Hla);
end;
