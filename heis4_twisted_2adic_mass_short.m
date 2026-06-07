SetColumns(0);

/*
  Verification of Corollary "numerical 2-adic mass of Heis_4".

  We write

      G = Heis_4 = { (a,b,c) : a,b,c in F_4 }

  with multiplication

      (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b').

  The central extension

      0 -> F_4 -> G -> F_4 + F_4 -> 0

  has quadratic map Q_G(a,b)=ab.  A bilinear form
  beta:F_4 x F_4 -> F_2 is encoded by a mask 0..15, whose coefficients are

      [ beta(1,1), beta(1,omega), beta(omega,1), beta(omega,omega) ].

  The code evaluates the admissible-triple formula

      (1/|G|) sum 2^(-d(g_-1,g_5,g_2))
        (-1)^( beta(a_-1,b_-1) + beta(a_5,b_2) + beta(a_2,b_5) )

  for all sixteen bilinear forms beta.  The claimed formulas from the paper
  appear only at the end, where they are printed next to the computed masses
  and compared numerically.

  Roadmap of the computation
  --------------------------

      finite-field helpers
          |
          v
      beta masks 0..15  ----->  Beta(a,b,coeffs)
          |                         |
          |                         v
          |                    sign in the twisted
          |                    admissible-triple sum
          |
          v
      Q_G^* W^vee masks, computed as beta(a,b)=Tr(uab)


      Heis_4 group law
          |
          v
      multiplication, square, and commutator tables
          |
          v
      admissible triples (g_-1,g_5,g_2), with g_-1^2=[g_5,g_2]
          |
          v
      subgroup orders |G_1|, |G_5|, |G_13|, |G_29|
          |
          v
      exponents e = 64*d(g_-1,g_5,g_2)
          |
          v
      TwistedMass(beta_mask): signed counts by e, then sum signed_count[e]/64*rho^(-e)
          |
          v
      computed masses for all 16 beta masks
          |
          v
      only now introduce the two claimed paper formulas and compare numerically

  The claimed coefficients 313,54,54,9 and 247,30,36,-3 are not used in
  constructing admissible triples, signs, signed counts, or computed masses.
*/

F2 := GF(2);
F4<omega> := GF(4);
F4elts := [ x : x in F4 ];
F4basis := [ F4!1, omega ];

/*
  Finite-field and beta-encoding helpers.

  TraceBit realizes a linear functional F_4 -> F_2 as an integer 0 or 1.
  CoordinatesInF4Basis writes x in the fixed basis [1,omega].

  A mask is just a compact human-readable way to loop through all sixteen
  bilinear forms beta:F_4 x F_4 -> F_2.  Its four bits are the values of beta
  on the ordered basis pairs

      (1,1), (1,omega), (omega,1), (omega,omega).

  The function Beta then evaluates the bilinear form with these coefficients.
*/

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

/*
  Heisenberg-group helpers.

  The group elements are stored as triples <a,b,c>, matching the paper.
  HeisIndex gives a stable index in [1..64] so that we can build small lookup
  tables.  The lookup tables are not mathematically necessary, but they make
  the repeated subgroup-order computations much faster and keep the triple
  enumeration readable.

  HeisCommutator uses the convention [g,h]=g*h*g^-1*h^-1, which is the
  convention used in the admissibility relation g_-1^2=[g_5,g_2].
*/

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

/*
  Breadth-first subgroup generation from a short list of generator indices.

  The admissible-triple formula only needs the orders of G_1, G_5, G_13,
  and G_29.  Since G has only 64 elements, the simplest reliable strategy is
  to close the set of generated elements under right-multiplication by the
  given generators, using multiplication_table for O(1) products.
*/

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

/*
  Build G=Heis_4 and the three tables needed later:

      multiplication_table[i][j] = index of G[i]*G[j],
      square_table[i]           = index of G[i]^2,
      commutator_table[i][j]    = index of [G[i],G[j]].

  The assertions immediately after the table construction check the formulas

      (a,b,c)^2 = (0,0,ab),
      [(a,b,c),(a',b',c')] = (0,0,ab' + a'b),

  which are exactly the group-theoretic formulas used in the paper.
*/

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

/*
  A homomorphism Gamma_{Q_2} -> G corresponds to an admissible triple
  (g_-1,g_5,g_2), i.e. a triple satisfying

      g_-1^2 = [g_5,g_2].

  For such a triple, the paper defines

      G_1  = < g_-1, g_2, [g_-1,g_5] >,
      G_5  = < g_2, [g_5,g_2], [g_-1,g_2] >,
      G_13 = < [g_-1,g_2], g_2^2 >,
      G_29 = < g_2^2 >.

  We store e = 64*d(g_-1,g_5,g_2), so that if rho^64=2 then
  2^(-d) = rho^(-e).

  The tuple stored for each admissible triple is

      < index_minus1, index_5, index_2, e >.

  The first three entries point back into G; the last entry records the
  discriminant contribution and is independent of beta.
*/

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

/*
  TwistedMass is the central numerical routine.

  Input:
      beta_mask              one of the 16 bilinear forms beta
      admissible_triples     precomputed beta-independent triple data
      discriminant_exponents possible values of e=64*d
      rho                    a root of rho^64=2

  Strategy:
      1. Convert beta_mask into the four values of beta on basis pairs.
      2. For each admissible triple, evaluate the sign exponent

             beta(a_-1,b_-1) + beta(a_5,b_2) + beta(a_2,b_5).

      3. Add +1 or -1 to signed_count[e], according to that sign.
      4. Only after all triples are counted, form the exact algebraic number

             sum_e signed_count[e]/|G| * rho^(-e).

  This routine has no access to the claimed closed forms from the paper.
*/

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

/*
  Convert an exact element of Q(rho), rho^64=2, to a high-precision real.
  This is used only for the final numerical comparison with the claimed
  expressions; it is not part of the mass computation itself.
*/

function RealValue(alpha, precision_digits)
    RR := RealField(precision_digits);
    rho_real := (RR!2)^(RR!1/RR!64);
    coeffs := Eltseq(alpha);
    return &+[ (RR!coeffs[i]) * rho_real^(i-1) : i in [1..#coeffs] ];
end function;

/*
  Print both sides of a proposed identity.

  The philosophy is intentionally conservative: do not use the claimed formula
  as an assertion inside the computation.  Instead, display the exact computed
  algebraic number, display the claimed algebraic number, and then report their
  agreement to a chosen number of decimal digits.
*/

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

/*
  The subgroup Q_G^* W^vee consists of the bilinear forms

      beta(a,b) = alpha(Q_G(a,b)) = alpha(ab),

  with alpha in W^vee.  We realize alpha as x |-> Tr_{F_4/F_2}(u*x).

  These masks are computed directly from Q_G(a,b)=ab.  They are not read from
  the claimed answer.
*/

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

/*
  Compute all masses before introducing the claimed formulas.

  The two set constructions below merely check what the computation discovers:
  all beta in Q_G^* W^vee give one mass, and all remaining beta give one other
  mass.  The assertions check this collapse, not agreement with the paper.
*/

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

/*
  Claimed expressions from the paper.  These are deliberately placed after
  the computation of computed_tau_in_QGstarWdual and
  computed_tau_outside_QGstarWdual.
*/

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
