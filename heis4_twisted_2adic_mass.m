SetColumns(0);
F2 := GF(2);
F4<omega> := GF(4);
F4elts := [ x : x in F4 ];
F4basis := [ F4!1, omega ];
function TraceBit(x)
    return Trace(x) eq F2!0 select 0 else 1;
end function;
function CoordinatesInF4Basis(x)
    return [ Integers()!c : c in Eltseq(x) ];
end function;
function MaskToBetaCoefficients(mask)
    return [ (mask div 2^(i-1)) mod 2 : i in [1..4] ];
end function;
function BetaCoefficientsToMask(coeffs)
    return &+[ coeffs[i]*2^(i-1) : i in [1..4] ];
end function;
function Beta(a, b, coeffs)
    a_coords := CoordinatesInF4Basis(a);
    b_coords := CoordinatesInF4Basis(b);
    return (&+[ coeffs[2*(i-1)+j] * a_coords[i] * b_coords[j]
                : i,j in [1..2] ]) mod 2;
end function;
function HeisIndex(g)
    return (Position(F4elts, g[1])-1)*16
         + (Position(F4elts, g[2])-1)*4
         +  Position(F4elts, g[3]);
end function;
function HeisMultiply(g, h)
    return <g[1] + h[1],
            g[2] + h[2],
            g[3] + h[3] + g[1]*h[2]>;
end function;
function HeisInverse(g)
    return <g[1], g[2], g[3] + g[1]*g[2]>;
end function;
function HeisCommutator(g, h)
    return HeisMultiply(HeisMultiply(HeisMultiply(g, h), HeisInverse(g)),
                        HeisInverse(h));
end function;
function GeneratedSubgroupOrder(generators, multiplication_table, identity_index)
    H := { identity_index };
    frontier := [ identity_index ];
    while #frontier gt 0 do
        h := frontier[#frontier];
        Prune(~frontier);
        for s in generators do
            hs := multiplication_table[h][s];
            if not hs in H then
                Include(~H, hs);
                Append(~frontier, hs);
            end if;
        end for;
    end while;
    return #H;
end function;
G := [];
for a in F4elts do
    for b in F4elts do
        for c in F4elts do
            Append(~G, <a,b,c>);
        end for;
    end for;
end for;
identity_index := HeisIndex(<F4!0, F4!0, F4!0>);
assert #G eq 64;
for i in [1..#G] do
    assert HeisIndex(G[i]) eq i;
end for;
multiplication_table := [
    [ HeisIndex(HeisMultiply(G[i], G[j])) : j in [1..#G] ]
    : i in [1..#G]
];
square_table := [ multiplication_table[i][i] : i in [1..#G] ];
commutator_table := [
    [ HeisIndex(HeisCommutator(G[i], G[j])) : j in [1..#G] ]
    : i in [1..#G]
];
for i in [1..#G] do
    assert square_table[i] eq HeisIndex(<F4!0, F4!0, G[i][1]*G[i][2]>);
    for j in [1..#G] do
        assert commutator_table[i][j]
            eq HeisIndex(<F4!0, F4!0, G[i][1]*G[j][2] + G[j][1]*G[i][2]>);
    end for;
end for;
admissible_triples := [];
for index_minus1 in [1..#G] do
    for index_5 in [1..#G] do
        for index_2 in [1..#G] do
            if square_table[index_minus1] eq commutator_table[index_5][index_2] then
                comm_minus1_5 := commutator_table[index_minus1][index_5];
                comm_5_2 := commutator_table[index_5][index_2];
                comm_minus1_2 := commutator_table[index_minus1][index_2];
                square_2 := square_table[index_2];
                G1_order := GeneratedSubgroupOrder(
                    [index_minus1, index_2, comm_minus1_5],
                    multiplication_table,
                    identity_index
                );
                G5_order := GeneratedSubgroupOrder(
                    [index_2, comm_5_2, comm_minus1_2],
                    multiplication_table,
                    identity_index
                );
                G13_order := GeneratedSubgroupOrder(
                    [comm_minus1_2, square_2],
                    multiplication_table,
                    identity_index
                );
                G29_order := GeneratedSubgroupOrder(
                    [square_2],
                    multiplication_table,
                    identity_index
                );
                d := 4*(1 - 1/(Rationals()!G1_order))
                   + 2*(1 - 1/(Rationals()!G5_order))
                   +     (1 - 1/(Rationals()!G13_order))
                   +     (1 - 1/(Rationals()!G29_order));
                Append(~admissible_triples,
                       <index_minus1, index_5, index_2, Integers()!(64*d)>);
            end if;
        end for;
    end for;
end for;
assert #admissible_triples eq 68608;
discriminant_exponents := Sort(SetToSequence({ t[4] : t in admissible_triples }));
R<x> := PolynomialRing(Rationals());
K<rho> := NumberField(x^64 - 2);
function TwistedMass(beta_mask, admissible_triples, G, discriminant_exponents, rho)
    beta_coeffs := MaskToBetaCoefficients(beta_mask);
    signed_count := AssociativeArray();
    for e in discriminant_exponents do
        signed_count[e] := 0;
    end for;
    for triple in admissible_triples do
        g_minus1 := G[triple[1]];
        g_5 := G[triple[2]];
        g_2 := G[triple[3]];
        e := triple[4];
        sign_exponent := (Beta(g_minus1[1], g_minus1[2], beta_coeffs)
                        + Beta(g_5[1],      g_2[2],      beta_coeffs)
                        + Beta(g_2[1],      g_5[2],      beta_coeffs)) mod 2;
        signed_count[e] +:= sign_exponent eq 0 select 1 else -1;
    end for;
    return &+[ (Rationals()!signed_count[e])/#G * rho^(-e)
               : e in discriminant_exponents ];
end function;
function RealValue(alpha, precision_digits)
    RR := RealField(precision_digits);
    rho_real := (RR!2)^(RR!1/RR!64);
    coeffs := Eltseq(alpha);
    return &+[ (RR!coeffs[i]) * rho_real^(i-1) : i in [1..#coeffs] ];
end function;
function CompareWithClaim(label, computed_mass, claimed_mass,
                          precision_digits, agreement_digits)
    RR := RealField(precision_digits);
    computed_real := RealValue(computed_mass, precision_digits);
    claimed_real := RealValue(claimed_mass, precision_digits);
    difference := Abs(computed_real - claimed_real);
    tolerance := (RR!10)^(-agreement_digits);
    print "";
    print label;
    print "computed mass from admissible triples =", computed_mass;
    print "mass claimed in the paper =", claimed_mass;
    print "computed decimal =", computed_real;
    print "claimed decimal  =", claimed_real;
    print "absolute difference =", difference;
    if difference lt tolerance then
        print "These agree to at least", agreement_digits, "decimal digits.";
        return true;
    else
        print "WARNING: these do not agree to", agreement_digits, "decimal digits.";
        print "This means either the computation, the claimed formula, or the";
        print "chosen numerical precision/agreement threshold needs to be checked.";
        return false;
    end if;
end function;
QGstarWdualMasks := {
    BetaCoefficientsToMask([ TraceBit(u*a*b) : a in F4basis, b in F4basis ])
    : u in F4elts
};
internal_checks_passed := true;
if #QGstarWdualMasks ne 4 then
    print "WARNING: expected #Q_G^* W^vee = 4, but computed",
          #QGstarWdualMasks;
    internal_checks_passed := false;
end if;
computed_masses := AssociativeArray();
for beta_mask in [0..15] do
    computed_masses[beta_mask] :=
        TwistedMass(beta_mask, admissible_triples, G, discriminant_exponents, rho);
end for;
computed_masses_in_QGstarWdual := {
    computed_masses[beta_mask] : beta_mask in QGstarWdualMasks
};
computed_masses_outside_QGstarWdual := {
    computed_masses[beta_mask] : beta_mask in [0..15]
    | not beta_mask in QGstarWdualMasks
};
mass_collapse_passed :=
    (#computed_masses_in_QGstarWdual eq 1)
    and (#computed_masses_outside_QGstarWdual eq 1);
if mass_collapse_passed then
    computed_tau_in_QGstarWdual :=
        SetToSequence(computed_masses_in_QGstarWdual)[1];
    computed_tau_outside_QGstarWdual :=
        SetToSequence(computed_masses_outside_QGstarWdual)[1];
else
    print "WARNING: the computed masses did not collapse into the two expected";
    print "classes beta in Q_G^* W^vee and beta outside Q_G^* W^vee.";
    print "Computed masses for beta in Q_G^* W^vee:";
    print computed_masses_in_QGstarWdual;
    print "Computed masses for beta outside Q_G^* W^vee:";
    print computed_masses_outside_QGstarWdual;
end if;
claimed_tau_in_QGstarWdual :=
    (313 + 54*rho^16 + 54*rho^32 + 9*rho^48)/16;
claimed_tau_outside_QGstarWdual :=
    (247 + 30*rho^16 + 36*rho^32 - 3*rho^48)/16;
print "rho satisfies rho^64 = 2, so rho^16 = 2^(1/4).";
print "Number of admissible triples =", #admissible_triples;
print "Masks for Q_G^* W^vee =", Sort(SetToSequence(QGstarWdualMasks));
precision_digits := 120;
agreement_digits := 80;
if mass_collapse_passed then
    comparison_in_QGstarWdual_passed := CompareWithClaim(
        "Case beta in Q_G^* W^vee",
        computed_tau_in_QGstarWdual,
        claimed_tau_in_QGstarWdual,
        precision_digits,
        agreement_digits
    );
    comparison_outside_QGstarWdual_passed := CompareWithClaim(
        "Case beta outside Q_G^* W^vee",
        computed_tau_outside_QGstarWdual,
        claimed_tau_outside_QGstarWdual,
        precision_digits,
        agreement_digits
    );
else
    comparison_in_QGstarWdual_passed := false;
    comparison_outside_QGstarWdual_passed := false;
    print "";
    print "Skipping comparison with the paper because the computed masses did";
    print "not first collapse into the two expected beta-classes.";
end if;
print "";
if internal_checks_passed
   and mass_collapse_passed
   and comparison_in_QGstarWdual_passed
   and comparison_outside_QGstarWdual_passed then
    print "Final status: all checks passed.";
    print "Computed all 16 bilinear forms beta:F_4 x F_4 -> F_2.";
    print "The claimed formulas were not used in the admissible-triple computation.";
else
    print "Final status: one or more checks failed.";
    print "Review the WARNING messages above before using this as verification";
    print "of the corollary.";
end if;
