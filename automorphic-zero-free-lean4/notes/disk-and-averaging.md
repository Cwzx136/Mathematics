# The weighted disk inequality

Let the fixed automorphic function be entire near all the disks below and have no zeros in the open half-plane to the right of 1. Write γ for any admissible exponent of its central t-aspect bound, allowing an arbitrarily small epsilon. Assume its normalized Euler logarithm in real part 1+v is bounded absolutely by O(log(2+1/v)). This follows for standard cuspidal factors from Cauchy–Schwarz on unramified prime powers using the self Rankin–Selberg factor and the Dedekind function. The fixed bad places contribute bounded terms.

Set s=1+u/L+iτ, where L=log|T|, u>0 is fixed, and τ=ℓT+O(1) for a fixed positive frequency ℓ. Choose a disk about s of radius R between 1/4 and 1/3, avoiding zeros on the boundary. The differentiated disk Poisson–Jensen identity is

    −Re (L'/L)(s) = −Σ_{|s−ρ|<R} (Re s−Re ρ)(|s−ρ|^(−2)−R^(−2))
                     − (1/(πR))∫ log|L(s+R exp(iθ))| cos θ dθ.

To derive it, divide by the finite Blaschke product of all the disk zeros with multiplicities. The analytic logarithm of the quotient has harmonic real part agreeing with the original boundary logarithm. Differentiate its Poisson integral at the center. Each Blaschke logarithmic derivative at the center has real part (Re s−Re ρ)(|s−ρ|^(−2)−R^(−2)). All these terms are nonnegative. The same identity holds for a meromorphic function if the disk avoids its poles, as happens here at large shifted height.

On the right semicircle the lower Euler bound is at worst −O(log L). Phragmén–Lindelöf between real parts 1/2 and 1+ε gives on the left semicircle the upper bound 2γ(−R cos θ)L+O_π(εL)+O_{π,ε}(log L), uniformly in R. For σ≥1+ε one uses absolute convergence. As the integral of cos² on a half-circle is π/2, the entire boundary term is at most (γ+o(1))L. The constants are uniform in the admissible R and bounded perturbations in τ. Epsilon tends to zero after large height. In particular the single target keeps its complete real reciprocal at its own ordinate up to O(1); the standard G upper bound is the weighted sum of the central growth exponents of all shifted positive-degree factors. At GL₂/Q use K. Aggarwal, arXiv:1810.10479. For GLₖ/Q, k≥3, P. Nelson, arXiv:2109.15230, Theorem 1.1, permits every exponent greater than (k/4)(1−2/(3k⁵−2k⁴−k²)).

For averaging, take an even probability μ on the physical shift variable v, whose characteristic function h(x) is integrable and nonnegative. Apply the same inequality with each ordinate translated by the common v/L, and integrate against μ. At every Euler prime power of log norm y this multiplies the existing positive amplifier by h(y/L)≥0. Take a fixed compact v-range first. Outside it the unaveraged Euler logarithmic derivatives in abscissa 1+u/L have absolute value O_π(L/u), uniform at every height, by the corresponding prime-power bound; thus the normalized tails vanish when the compact expands. The pole parts of the finitely many fixed static terms and the shifted target's retained term converge under dominated convergence. The elementary Laplace transform and Fubini give

    ∫ Re 1/(z+iv) dμ(v) = ∫₀∞ h(x)e^(−zx) dx       (z>0).

If w=L(1−β) tends to a finite w* along a hypothetical zero sequence, the resulting inequality is

    ∫₀∞ h(x)(e^(−(u+w*)x)−P e^(−ux)) dx ≤ G.

Let u tend to zero using integrability. For any test h and desired excluded W>0, apply the last inequality to x↦h(Wx). For w*≤W this gives ∫₀∞ h(x)(e^(−x)−P)dx ≤ GW. Any strict reverse inequality proves the claimed exclusion, including the boundary. Positive compactly supported autocorrelations of nonnegative L² functions meet these assumptions by Plancherel and Fourier inversion, with spectral density proportional to the squared Fourier modulus.

For the directly verified square [30,71,86,42], Research.WeylAmplifier proves P=10521/22436, G=101085917/110587044 with Weyl and Nelson. Without spectral averaging the optimal logarithmic abscissa δ log|T| is (sqrt(P)−P)/G. The single fixed rational substitute 59/250 already certifies reciprocal widths 9.19983 (Weyl and Nelson) or 9.2111 (Weyl and convexity). At B=13/8 the compact polynomial-bump moment supplied separately gives a reciprocal width below 6.194 for this same square.
