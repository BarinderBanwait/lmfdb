

# This file was mechanically preparsed from Alain Chamarie's ClassGroupLean.sage.
# Keep local changes small: the LMFDB integration relies on the public
# generate_class_group_lean entry point near the end of this file.
from sage.all_cmdline import *   # import sage library

_sage_const_1 = Integer(1); _sage_const_2 = Integer(2); _sage_const_0 = Integer(0); _sage_const_4 = Integer(4); _sage_const_10 = Integer(10); _sage_const_7 = Integer(7); _sage_const_20 = Integer(20); _sage_const_3 = Integer(3); _sage_const_40 = Integer(40); _sage_const_50 = Integer(50); _sage_const_12345 = Integer(12345); _sage_const_100 = Integer(100); _sage_const_8 = Integer(8); _sage_const_200 = Integer(200); _sage_const_0p01 = RealNumber('0.01'); _sage_const_6 = Integer(6); _sage_const_0p00001 = RealNumber('0.00001'); _sage_const_400 = Integer(400)
# Single-file Sage script for Lean class group certificates
# Entry point: generate_class_group_lean(T, B_polys, num)
#
# Usage example (degree 3):
#
#   load('ClassGroupLean.sage')
#   R.<x> = PolynomialRing(ZZ)
#   M.<a> = PolynomialRing(QQ)
#   f = x^3 + 150*x - 50
#   K.<a> = NumberField(f, a)
#   B = [1, a, 1/5*a^2]          # integral basis of K
#   label = '3_1_542700_3'       # names the output folder NF<label> and the files in it
#   generate_class_group_lean(f, B, label)
#
# This writes only .lean files (Irreducible/RI/PrimesBelow*/ClassGroupData/
# ClassGroupSaturated*/RelationIdeals*/Invariants/Results) into ./NF<label>/.


from itertools import combinations
import itertools
import os
from functools import lru_cache

from sage.rings.number_field.number_field_base import NumberField as NumberField_base


def sqpow(t, f, p):
    s = p.bit_length() - _sage_const_1 
    binary_list = [int(bit) for bit in bin(p)[_sage_const_2 :]]
    bit = binary_list[::-_sage_const_1 ]
    hp = [_sage_const_0  for i in range(s)] + [t]
    gp = [_sage_const_0  for i in range(s)]
    for i in range(s-_sage_const_1 , -_sage_const_1 , -_sage_const_1 ):
        gp[i], hp[i] = (hp[i+_sage_const_1 ] ** _sage_const_2  * t**(bit[i])).quo_rem(f)
    return hp, gp

def factorLists(T, p):
    F = factor(T.change_ring(GF(p)))
    Fp = [x for x in F]
    Fp[_sage_const_0 ] = (F.unit() * F[_sage_const_0 ][_sage_const_0 ], F[_sage_const_0 ][_sage_const_1 ])
    lF = []
    for p in Fp:
        lF = lF + p[_sage_const_1 ] * [p[_sage_const_0 ].list()]
    return lF

def ListDegree(T, p):
    deg = T.degree()
    d = []
    for P in factor(T.change_ring(GF(p))):
        d = d + P[_sage_const_1 ] * [P[_sage_const_0 ].degree()]
    return d

def SubSums(l):
    sub = [_sage_const_0 ]
    for i in range(_sage_const_1 , len(l) + _sage_const_1 ):
        combs = [list(x) for x in combinations(l, i)]
        if len(combs) > _sage_const_0 :
            aux = [sum(c) for c in combs]
            sub = sub + aux
    return sub

def IntersectListDegrees(T, l):
    inter = SubSums(ListDegree(T, l[_sage_const_0 ]))
    for p in l:
        inter = set(inter).intersection(set(SubSums(ListDegree(T, p))))
    return inter

def FindMinimalCommonDegree(T, size, rangep):
    C = []
    dmin = _sage_const_1 
    GPrimes = [p for p in primes(rangep) if T.leading_coefficient() % p != _sage_const_0 ]
    for l in [list(x) for x in combinations(GPrimes, size)]:
        if min((IntersectListDegrees(T, l)) - {_sage_const_0 }) >= dmin:
            dmin = min((IntersectListDegrees(T, l)) - {_sage_const_0 })
            C = C + [(dmin, l)]
    Cp = []
    for x in C:
        if x[_sage_const_0 ] == dmin:
            Cp = Cp + [x[_sage_const_1 ]]
    return dmin, Cp

def ScoreCertificate(T, l):
    M = _sage_const_0 
    for p in l:
        M = float(M + sum([i**_sage_const_2  for i in ListDegree(T, p)]) * log(p))
    return M

def BestCertificateSize(T, size, rangep):
    M = _sage_const_0 
    Best = []
    dmin, C = FindMinimalCommonDegree(T, size, rangep)
    N = Infinity
    for c in C:
        M = ScoreCertificate(T, c)
        if M < N:
            N = M
            Best = c
    return dmin, Best, N

def BestCertificate(T, ranges, rangep):
    N = Infinity
    dmin = -Infinity
    Best = []
    for i in range(_sage_const_1 , ranges + _sage_const_1 ):
        d, C, M = BestCertificateSize(T, i, rangep)
        if d > dmin:
            dmin = d
            N = M
            Best = C
        elif d == dmin:
            if M < N:
                N = M
                Best = C
    return dmin, Best, N

def CauchyBoundScale(l, s):
    m = len(l)
    an = l[-_sage_const_1 ]
    aux = [abs(l[i]/an) * s**(i - (m - _sage_const_1 ) + _sage_const_1 ) for i in range(m - _sage_const_1 )]
    return (s + max(aux))

def CauchyBoundScaleOpt(l):
    B = Infinity
    j = _sage_const_0 
    n = len(l) - _sage_const_1 
    an = l[-_sage_const_1 ]
    S = max([float((abs(l[i]/an) * (n - i - _sage_const_1 )) ** (_sage_const_1  / (n - i))) for i in range(n)])
    for i in range(_sage_const_1 , ceil(S * _sage_const_4 )):
        if CauchyBoundScale(l, i / _sage_const_4 ) < B:
            B = CauchyBoundScale(l, i / _sage_const_4 )
            j = i/_sage_const_4 
    return j, B

def FindPrimeFactorLPFW(f, B, d, k):
    t = ceil(B + _sage_const_1 )
    m = _sage_const_0 
    flagC = _sage_const_0 
    prime = Infinity
    rangeL = []
    cont = _sage_const_0 
    for i in range(t, t + k):
        rangeL = rangeL + [i, -i]
    for i in rangeL:
        cont = cont + _sage_const_1 
        sB = (abs(i) - B) ** d
        V = abs(f(i))
        F = factor(V)
        for p in F:
            if V / (p[_sage_const_0 ]) < sB and p[_sage_const_0 ] < prime:
                flagC = _sage_const_1 
                prime = p[_sage_const_0 ]
                m = i
                break
    if flagC == _sage_const_1 :
        return True, m, prime
    else:
        return False, _sage_const_0 , _sage_const_0 

def CertificateIrrModpFFP(f, p, N):
    """Certificate of irreducibility for f mod p using Rabin's test (with degree factoring).
    Returns a Lean string for a term of type CertificateIrreducibleZModOfList'."""
    R = PolynomialRing(GF(p), names=('X',)); (X,) = R._first_ngens(1)
    f = R(f.list())
    s = p.bit_length() - _sage_const_1 
    binary_list = [int(bit) for bit in bin(p)[_sage_const_2 :]]
    bit = binary_list[::-_sage_const_1 ]
    n = f.degree()
    F = factor(n)
    P = [x[_sage_const_0 ] for x in F]
    E = [x[_sage_const_1 ] for x in F]

    if n == _sage_const_1 :
        h = [X, X]
        gaux = [(X**p - X)/f]
    else:
        h = [X] + [_sage_const_0  for i in range(n)]
        gaux = [_sage_const_0  for i in range(n)]
        for i in range(n):
            gaux[i], h[i+_sage_const_1 ] = (h[i] ** p).quo_rem(f)

    hprime = [[] for i in range(n)]
    gprime = [[] for i in range(n)]
    for i in range(n):
        hp, gp = sqpow(h[i], f, p)
        hprime[i] = hp
        gprime[i] = gp

    a = [_sage_const_0  for i in range(n)]
    b = [_sage_const_0  for i in range(n)]
    d = [_sage_const_0  for i in range(n)]
    for x in P:
        d[n // x], a[n // x], b[n // x] = xgcd(f, h[n // x] - X)

    h = [list(h[i]) for i in range(n + _sage_const_1 )]
    hprime = [[list(R(hprime[i][j])) for j in range(s+_sage_const_1 )] for i in range(n)]
    g = [[list(R(gprime[i][j])) for j in range(s)] for i in range(n)]
    a = [list(R(a[i])) for i in range(n)]
    b = [list(R(b[i])) for i in range(n)]

    if n == _sage_const_1 :
        hprime[_sage_const_0 ][_sage_const_0 ] = [_sage_const_0 , _sage_const_1 ]
        if s > _sage_const_1 :
            g[_sage_const_0 ][_sage_const_0 ] = []
        else:
            g[_sage_const_0 ][_sage_const_0 ] = (R((X ** _sage_const_2  * X ** (bit[_sage_const_0 ]) - X)/f)).list()

    strg = ", ".join('!' + str(g[i]) for i in range(len(g)))
    strh = ", ".join('!' + str(hprime[i]) for i in range(len(hprime)))

    out = f"def P{p}P{N} : CertificateIrreducibleZModOfList' {p} {n} 2 {s} {f.list()} where\n"
    out += f" m := {len(P)}\n"
    out += f" P := !{P}\n"
    out += f" exp := !{E}\n"
    out += " hneq := by decide\n"
    out += " hP := by decide\n"
    out += " hlen := by decide\n"
    out += " htr := by decide\n"
    out += f" bit := !{bit}\n"
    out += " hbits := by decide\n"
    out += f" h := !{h}\n"
    out += " g := ![" + strg + "]\n"
    out += " h' := ![" + strh + "]\n"
    out += " hs := by decide\n"
    out += " hz := by decide\n"
    out += " hmul := by decide\n"
    out += f" a := !{a}\n"
    out += f" b := !{b}\n"
    out += " hhz := by decide\n"
    out += " hhn := by decide\n"
    out += " hgcd := by decide\n"
    return out

def GlobalCertificateIrrF(T, lprimes):
    """Lean certificate for irreducibility via degree analysis.
    Returns a string for a term of type IrreducibleCertificateIntPolynomial."""
    m = [len(factorLists(T, p)) for p in lprimes]
    out = "noncomputable def C : IrreducibleCertificateIntPolynomial T l where\n"
    out += " hpol := T_ofList'\n"
    out += f" n := {len(lprimes)}\n"
    out += f" d := {T.degree()}\n"
    out += " hprim := by decide\n"
    out += " hdeg := by decide\n"
    out += " hnn := by decide\n"
    out += " hdn := by decide\n"
    out += f" p := !{lprimes}\n"
    out += " hp := by\n"
    out += "  intro i\n"
    out += "  fin_cases i\n"
    for p in lprimes:
        out += f"  exact hp{p}'.out\n"
    out += f" hlc := by decide\n"
    out += f" m := !{m}\n"
    out += " F := fun i =>\n"
    out += "  match i with\n"
    for i in range(len(lprimes)):
        out += f"  | {i} => !{factorLists(T, lprimes[i])}\n"
    out += " D := fun i =>\n"
    out += "  match i with\n"
    for i in range(len(lprimes)):
        out += f"  | {i} => !{[len(factorLists(T, lprimes[i])[j]) - _sage_const_1  for j in range(m[i])]}\n"
    out += " hl := by decide\n"
    out += " hirr := by\n"
    out += "  intro i ; intro j\n"
    out += "  fin_cases i <;> fin_cases j\n"
    for p in lprimes:
        F = factor(T.change_ring(GF(p)))
        for i in range(len(F)):
            if F[i][_sage_const_0 ].degree() == _sage_const_1 :
                for j in range(F[i][_sage_const_1 ]):
                    out += f"  · exact irreducible_ofList_of_linear (R := ZMod {p}) _ (by decide) rfl\n"
            else:
                for j in range(F[i][_sage_const_1 ]):
                    out += f"  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P{p}PI{i}\n"
    out += " hm := by decide\n"
    out += " hprod := by decide\n"
    out += " hinter := by decide\n"
    return out

def GlobalCertificateLPFWDegree(T, lprimes, dmin, scaling_factor, rho, M, prime):
    """Lean certificate for irreducibility via LPFW with degree analysis.
    Returns a string for a term of type CertificateIrreducibleIntOfPrimeDegreeAnalysis."""
    l = T.list()
    s = abs(T(M)) / prime
    m = [len(factorLists(T, p)) for p in lprimes]

    out = "noncomputable def C : CertificateIrreducibleIntOfPrimeDegreeAnalysis T l where\n"
    out += " hpol := T_ofList'\n"
    out += " hdeg := by decide\n"
    out += " hprim := by decide\n"
    out += f" n := {len(lprimes)}\n"
    out += f" d := {dmin}\n"
    out += f" s := {s}\n"
    out += f" P := {prime}\n"
    out += f" M := {M}\n"
    out += f" r := {scaling_factor}\n"
    out += f" ρ := {rho}\n"
    # Primality by norm_num verified fast up to 10-digit primes on the pinned
    # toolchain (mathlib norm_num prime extension); beyond that fall back to
    # sorry, which the LMFDB wrapper detects and refuses to serve.
    if floor(log(prime, _sage_const_10 ) + _sage_const_1 ) < 11:
        out += " hPPrime := by norm_num\n"
    else:
        out += " hPPrime := sorry -- Consider using Pratt certificate\n"
        print(f"ERROR: 'sorry' used for hPPrime in declaration 'C' -- prime {prime} has "
              f"{floor(log(prime, _sage_const_10 ) + _sage_const_1 )} digits, too large for norm_num. Proof is incomplete.")
    out += " hrpos := by norm_num\n"
    out += " hnn := by decide\n"
    out += " hdn := by decide\n"
    out += f" p := !{lprimes}\n"
    out += " hp := by\n"
    out += "  intro i\n"
    out += "  fin_cases i\n"
    for p in lprimes:
        out += f"  exact hp{p}'.out\n"
    out += f" hlc := by decide\n"
    out += f" m := !{m}\n"
    out += " F := fun i =>\n"
    out += "  match i with\n"
    for i in range(len(lprimes)):
        out += f"  | {i} => !{factorLists(T, lprimes[i])}\n"
    out += " D := fun i =>\n"
    out += "  match i with\n"
    for i in range(len(lprimes)):
        out += f"  | {i} => !{[len(factorLists(T, lprimes[i])[j]) - _sage_const_1  for j in range(m[i])]}\n"
    out += " hl := by decide\n"
    out += " hirr := by\n"
    out += "  intro i ; intro j\n"
    out += "  fin_cases i <;> fin_cases j\n"
    for p in lprimes:
        F = factor(T.change_ring(GF(p)))
        for i in range(len(F)):
            if F[i][_sage_const_0 ].degree() == _sage_const_1 :
                for j in range(F[i][_sage_const_1 ]):
                    out += f"  · exact irreducible_ofList_of_linear (R := ZMod {p}) _ (by decide) rfl\n"
            else:
                for j in range(F[i][_sage_const_1 ]):
                    out += f"  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P{p}PI{i}\n"
    out += " hm := by decide\n"
    out += " hprod := by decide\n"
    out += " hinter := by decide\n"
    out += " hrhoeq := by decide\n"
    out += " hrho := by decide\n"
    out += " hs := by norm_num\n"
    out += " heval := by norm_num\n"
    return out

def GlobalCertificateLPFW(T, scaling_factor, rho, M, prime):
    """Lean certificate for irreducibility via LPFW without degree analysis.
    Returns a string for a term of type CertificateIrreducibleIntOfPrime."""
    s = abs(T(M)) / prime
    out = "noncomputable def C : CertificateIrreducibleIntOfPrime T l where\n"
    out += " hpol := T_ofList'\n"
    out += " hdeg := by decide\n"
    out += " hprim := by decide\n"
    out += " hlz := by decide\n"
    out += f" s := {s}\n"
    out += f" P := {prime}\n"
    out += f" M := {M}\n"
    out += f" r := {scaling_factor}\n"
    out += f" ρ := {rho}\n"
    # Primality by norm_num verified fast up to 10-digit primes on the pinned
    # toolchain (mathlib norm_num prime extension); beyond that fall back to
    # sorry, which the LMFDB wrapper detects and refuses to serve.
    if floor(log(prime, _sage_const_10 ) + _sage_const_1 ) < 11:
        out += " hPPrime := by norm_num\n"
    else:
        out += " hPPrime := sorry -- Consider using Pratt certificate\n"
        print(f"ERROR: 'sorry' used for hPPrime in declaration 'C' -- prime {prime} has "
              f"{floor(log(prime, _sage_const_10 ) + _sage_const_1 )} digits, too large for norm_num. Proof is incomplete.")
    out += " hrpos := by norm_num\n"
    out += " hrhoeq := by decide\n"
    out += " hrho := by decide\n"
    out += " hs := by norm_num\n"
    out += " heval := by norm_num\n"
    return out

def LeanProofIrreducible(T):
    """Produces a complete Lean proof of irreducibility for T.
    Returns the Lean file content as a string."""
    flagP = _sage_const_0 
    dmin = _sage_const_0 
    l = T.list()
    T_lean = str(T).replace('x', 'X')
    scaling_factor, rho = CauchyBoundScaleOpt(l)
    flag, M, prime = FindPrimeFactorLPFW(T, rho, _sage_const_1 , _sage_const_20 )

    if prime != _sage_const_0  and floor(log(prime, _sage_const_10 ) + _sage_const_1 ) < _sage_const_7 :
        flagP = _sage_const_1 
    else:
        dmin, lprimes, N = BestCertificate(T, _sage_const_3 , _sage_const_40 )

    if dmin == T.degree() and flagP == _sage_const_0 :
        out = f"""import IdealArithmetic.DedekindProject.Polynomial.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => ({T_lean} : ℤ[X])

local notation "l" => {T.list()}

lemma T_ofList' : T = ofList l := by norm_num ; ring
"""
        for p in lprimes:
            out += f"instance hp{p}' : Fact $ Nat.Prime {p} := fact_iff.2 (by norm_num)\n"
        out += "\n"
        for p in lprimes:
            F = factor(T.change_ring(GF(p)))
            for N in range(len(F)):
                if (F[N][_sage_const_0 ].degree()) > _sage_const_1 :
                    if N == _sage_const_0 :
                        out += CertificateIrrModpFFP(F.unit() * F[N][_sage_const_0 ], p, 'I' + str(N))
                        out += "\n"
                    else:
                        out += CertificateIrrModpFFP(F[N][_sage_const_0 ], p, 'I' + str(N))
                        out += "\n"
        out += GlobalCertificateIrrF(T, lprimes)
        out += "\n"
        out += "theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C\n"
        return out
    else:
        out = f"""import IdealArithmetic.DedekindProject.Polynomial.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import IdealArithmetic.DedekindProject.Polynomial.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => ({T_lean} : ℤ[X])

local notation "l" => {T.list()}

unseal Rat.add Rat.mul Rat.inv

lemma T_ofList' : T = ofList l := by norm_num ; ring
"""
        if flagP == _sage_const_0 :
            flag, M, prime = FindPrimeFactorLPFW(T, rho, dmin, _sage_const_50 )
        if abs(T(M)) / prime >= abs(M) - rho and dmin > _sage_const_1  and flagP == _sage_const_0 :
            for p in lprimes:
                out += f"instance hp{p}' : Fact $ Nat.Prime {p} := fact_iff.2 (by norm_num)\n"
            out += "\n"
            for p in lprimes:
                F = factor(T.change_ring(GF(p)))
                for N in range(len(F)):
                    if (F[N][_sage_const_0 ].degree()) > _sage_const_1 :
                        if N == _sage_const_0 :
                            out += CertificateIrrModpFFP(F.unit() * F[N][_sage_const_0 ], p, 'I' + str(N))
                            out += "\n"
                        else:
                            out += CertificateIrrModpFFP(F[N][_sage_const_0 ], p, 'I' + str(N))
                            out += "\n"
            out += GlobalCertificateLPFWDegree(T, lprimes, dmin, scaling_factor, rho, M, prime)
            out += "\n"
            out += "theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrimeDegrees _ _ C\n"
            return out
        else:
            out += GlobalCertificateLPFW(T, scaling_factor, rho, M, prime)
            out += "\n"
            out += "theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C\n"
            return out
def BasisToMatrix(B):
    n = len(B)
    d = _sage_const_1 
    L = [i.list() + (n - len(i.list())) * [_sage_const_0 ] for i in B]
    M = matrix(L).transpose()
    for i in range(n):
        for j in range(n):
            d = lcm(d, denominator(M[i,j]))
    return d * M, d

def SubalgebraBuilderF(T, C, d):
    """Builds a term of type SubalgebraBuilderLists in Lean.
    Returns (str, A, auxTemp) where A is the times table and auxTemp is B^{-1} * (d * e_1)."""
    n = T.degree()
    K = NumberField(T, names=('a',)); (a,) = K._first_ngens(1)
    S = PolynomialRing(ZZ, names=('X',)); (X,) = S._first_ngens(1)
    T_S = S(T.coefficients(sparse=False))
    MM = (_sage_const_1 /d) * C
    MMinv = MM.inverse()
    A = [[[] for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            A[i][j] = (MMinv * matrix([(K(MM.column(i)) * K(MM.column(j))).list()]).transpose()).transpose().list()

    s = [[-S(C.column(i).list()) * S(C.column(j).list()) // T_S for j in range(n)] for i in range(n)]
    B = [S(C.column(i).list()) for i in range(n)]
    s = [[s[i][j].list() for j in range(n)] for i in range(n)]

    out = f"noncomputable def BQ : SubalgebraBuilderLists {n} ℤ  ℚ K T l where\n"
    out += f" d := {d}\n"
    out += " hlen := rfl\n"
    out += " htr := rfl\n"
    out += " hofL := T_ofList.symm\n"
    out += " hm := rfl\n"
    out += " B := !["
    items = ['!' + str(B[i].list() + [_sage_const_0 ] * (n - len(B[i].list()))) for i in range(n)]
    out += ", ".join(items[:-_sage_const_1 ])
    if len(items) > _sage_const_1 :
        out += ", "
    out += items[-_sage_const_1 ] + "]\n"

    stra = " "
    for i in range(n):
        stra += "!["
        for j in range(n):
            if j != n - _sage_const_1 :
                stra += '!' + str(A[i][j]) + ','
            else:
                stra += '!' + str(A[i][j])
        if i != n - _sage_const_1 :
            stra += '], \n'
        else:
            stra += ']'
    stra += "]"
    out += " a := ![" + stra + "\n"

    strs = ""
    for i in range(n):
        if i != n - _sage_const_1 :
            strs += '!' + str(s[i]) + ','
        else:
            strs += '!' + str(s[i])
    strs += "]"
    out += " s := ![" + strs + "\n"
    out += """ h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide \n"""
    return out, A, C.inverse() * (d * vector([_sage_const_0  if i != _sage_const_1  else _sage_const_1  for i in range(n)]))

def CertificateDedekindCriterionF(T, p):
    """Certificate of Dedekind criterion for T at prime p.
    Returns a Lean string if T satisfies the criterion at p, or None otherwise."""
    S = PolynomialRing(ZZ, names=('X',)); (X,) = S._first_ngens(1)
    R = PolynomialRing(GF(p), names=('x',)); (x,) = R._first_ngens(1)
    T_coeffs = T.coefficients(sparse=False)
    T_S = S(T_coeffs)
    T_R = R(T_coeffs)
    g = radical(T_R)
    F = T_R.factor()
    kl = len(F)
    n = max([F[i][_sage_const_1 ] for i in range(kl)])
    t, ap, bp = xgcd(g, derivative(g))
    k = R((g**n) / T_R)
    h = S(R(T_R / g))
    f = (S(g) * h - T_S) / p
    gcd, at, bt = xgcd(R(f), g)
    gcd2, at2, c = xgcd(gcd, R(h))
    a = at2 * at
    b = at2 * bt
    c = c

    if gcd2 == _sage_const_1 :
        out = f"def CD{p}: CertificateDedekindCriterionLists l {p} where\n"
        out += f" n := {n}\n"
        out += f" a' := {ap.list()}\n"
        out += f" b' := {bp.list()}\n"
        out += f" k := {k.list()}\n"
        out += f" f := {f.list()}\n"
        out += f" g := {g.list()}\n"
        out += f" h := {h.list()}\n"
        out += f" a := {a.list()}\n"
        out += f" b := {b.list()}\n"
        out += f" c := {c.list()}\n"
        out += " hdvdpow := rfl\n"
        out += " hcop := rfl\n"
        out += " hf := by rfl\n"
        out += " habc := by rfl\n\n"
        return out
    return None

def CertificateDedekindF(T):
    """Certificate proving T satisfies Dedekind criterion at all primes except those in 'bad'.
    Returns (str, bad) where str is the Lean code and bad is the list of exceptional primes."""
    D, a, b = xgcd(T, derivative(T))
    if D < _sage_const_0 :
        a = -a
        b = -b
    F = factor(D)
    n = len(F)
    pl = [t[_sage_const_0 ] for t in F]
    exp = [t[_sage_const_1 ] for t in F]

    out = ""
    for p in set(pl):
        out += f"instance hp{p}: Fact $ Nat.Prime {p} := fact_iff.2 (by norm_num)\n"
    out += "\n"

    good = []
    for p in pl:
        cert = CertificateDedekindCriterionF(T, p)
        if cert is not None:
            out += cert
            good.append(p)

    bad = list(set(pl) - set(good))

    out += f"noncomputable def D : CertificateDedekindAlmostAllLists T l {bad} where\n"
    out += f" n := {len(pl)}\n"
    out += f" p := !{pl}\n"
    out += f" exp := !{exp}\n"
    out += f" pdgood := {good}\n"
    out += " hsub := by decide\n"
    out += " hp := by\n"
    out += "  intro i ; fin_cases i\n"
    for p in pl:
        out += f"  exact hp{p}.out\n"
    out += f" a := {a.list()}\n"
    out += f" b := {b.list()}\n"
    out += " hab := by decide\n"
    out += " hd := by \n"
    out += "  intro p hp \n"
    out += "  fin_cases hp\n"
    for p in good:
        out += f"  exact satisfiesDedekindCriterion_of_certificate_lists T l {p} T_ofList CD{p}\n"
    out += "\n"
    return out, bad

def CertificatePMaximalityF(T, C, denom, p, Table):
    """Certificate of p-maximality for the order with basis encoded in C/denom.
    Returns (str, flag, flagW) where flag=1 means unramified case, flagW=1 means witness found."""
    d = T.degree()
    t = _sage_const_0 
    while p**t < d:
        t = t + _sage_const_1 
    K = NumberField(T, names=('a',)); (a,) = K._first_ngens(1)
    O = K.maximal_order()

    M = (_sage_const_1 /denom) * C
    B = [K(M.column(i).list()) for i in range(d)]

    MFrob = matrix([(i**(p**t)).list() for i in B]).transpose()
    Coeff = M.inverse() * MFrob
    MS = MatrixSpace(GF(p), d)
    CoeffMod = MS(Coeff)

    m = CoeffMod.right_nullity()
    n = d - m

    v = CoeffMod.right_kernel().matrix().rows()
    v_ind = CoeffMod.right_kernel().matrix().pivots()
    w_ind = CoeffMod.transpose().echelon_form().pivots()
    X = CoeffMod.solve_right(CoeffMod.transpose().echelon_form().transpose())
    wFrob = [CoeffMod.transpose().echelon_form().transpose().column(i) for i in range(n)]
    w = [X.column(i) for i in range(n)]

    flag = _sage_const_0 
    flagW = _sage_const_0 
    out = ""

    if m == _sage_const_0 :
        flag = _sage_const_1 
        out += f"noncomputable def M{p} : MaximalOrderCertificateOfUnramifiedLists {p} O Om hm where\n"
        out += f" n := {n}\n"
        out += f" t := {t}\n"
        out += " hpos := by decide\n"
        out += " TT := timesTableO\n"
        out += " B' := B'\n"
        out += " T := Table\n"
        out += " heq := timesTableT_eq_Table\n"
        strT = ""
        for i in range(d):
            if i != d - _sage_const_1 :
                strT += '!' + str([[GF(p)(Table[i][j][k]) for k in range(d)] for j in range(d)]) + ', \n'
            else:
                strT += '!' + str([[GF(p)(Table[i][j][k]) for k in range(d)] for j in range(d)])
        out += " TMod := ![" + strT + "]\n"
        out += " hTMod := by decide\n"
        out += " hle := by decide\n"
        strw = ""
        for i in range(n):
            if i != n - _sage_const_1 :
                strw += '!' + str(w[i].list()) + ','
            else:
                strw += '!' + str(w[i].list())
        out += " w := ![" + strw + "]\n"
        strF = ""
        for i in range(n):
            if i != n - _sage_const_1 :
                strF += '!' + str(wFrob[i].list()) + ','
            else:
                strF += '!' + str(wFrob[i].list())
        out += " wFrob := ![" + strF + "]\n"
        out += " w_ind := !" + str([w_ind[i] for i in range(n)]) + "\n"
        out += """ hindw := by decide
 hwFrobComp := by decide \n"""
    else:
        MQQ = MatrixSpace(ZZ, d)
        MQ1 = MatrixSpace(ZZ, m, d)
        MQ2 = MatrixSpace(ZZ, n, d)
        if m > _sage_const_0 :
            Brad = MQ1(matrix(v)).transpose().augment(p * MQ2(matrix(w)).transpose())
        else:
            Brad = p * MQ2(matrix(w)).transpose()
        Brad2 = M * Brad

        ListBasisRad = [K(Brad2.column(i)) for i in range(d)]

        def MatrixEndoMul(j):
            return MS(Brad2.inverse() * matrix([(B[j] * ListBasisRad[i]).list() for i in range(d)]).transpose())

        set_random_seed(_sage_const_12345 )

        for i in range(_sage_const_100 ):
            W = random_vector(ZZ, d, floor(d/_sage_const_2 ))
            LII = matrix([(MatrixEndoMul(i) * W).list() for i in range(d)]).transpose()
            if not LII.is_singular():
                flagW = _sage_const_1 
                break

        if flagW == _sage_const_1 :
            LII = matrix([(MatrixEndoMul(i) * W).list() for i in range(d)]).transpose()
            Wit = K((Brad2 * W).list())
            G = LII.inverse()
            g = [[ZZ(G[i][j]) for i in range(d)] for j in range(d)]

            def Endo(j):
                return Brad2.inverse() * vector(((K((M * matrix(g[j]).transpose()).list())) * Wit).list())

            for j in range(d):
                denom_j = LCM([(Endo(j)[k]).denominator() for k in range(d)])
                g[j] = [denom_j * g[j][i] for i in range(d)]

            def a_aux(i):
                return [Endo(i)[k] for k in range(m)]
            def c_aux(i):
                return [Endo(i)[m + k] for k in range(n)]

            a = [a_aux(i) for i in range(d)]
            c = [c_aux(i) for i in range(d)]

            def ac_ind_aux(i):
                if i < m:
                    return 'Sum.inl ' + str(i)
                else:
                    return 'Sum.inr ' + str(i - m)
        else:
            MM = matrix([(MatrixEndoMul(j)).list() for j in range(d)])
            ab_aux = MM.echelon_form().pivots()
            gm = MQQ((MM.transpose().solve_right(MM.echelon_form().transpose()))).columns()
            g = [[gm[j][i] for i in range(d)] for j in range(d)]

            def Endo(j):
                return Brad2.inverse() * (matrix([((K((M * matrix(g[j]).transpose()).list())) * ListBasisRad[i]).list() for i in range(d)]).transpose())

            for j in range(d):
                denom_j = LCM([LCM([(Endo(j)[i][k]).denominator() for k in range(d)]) for i in range(d)])
                g[j] = [denom_j * g[j][i] for i in range(d)]

            def a_aux(i, j):
                return [Endo(i).column(j)[k] for k in range(m)]
            def c_aux(i, j):
                return [Endo(i).column(j)[m + k] for k in range(n)]

            a = [[a_aux(i, j) for j in range(m)] for i in range(d)]
            c = [[c_aux(i, j) for j in range(m)] for i in range(d)]
            dl = [[a_aux(i, m + j) for j in range(n)] for i in range(d)]
            e = [[c_aux(i, m + j) for j in range(n)] for i in range(d)]

            def index_adjust(i, m, n):
                dd = m + n
                r = i % dd
                s = floor(i / dd)
                col = ('Sum.inl ' + str(r)) if r < m else ('Sum.inr ' + str(r - m))
                row = ('Sum.inl ' + str(s)) if s < m else ('Sum.inr ' + str(s - m))
                return (col, row)

            ab_ind = [index_adjust(i, m, n) for i in ab_aux]

        if flagW == _sage_const_1 :
            out += f"noncomputable def M{p} : MaximalOrderCertificateWLists {p} O Om hm where\n"
        else:
            out += f"noncomputable def M{p} : MaximalOrderCertificateLists {p} O Om hm where\n"
        out += f" m := {m}\n"
        out += f" n := {n}\n"
        out += f" t := {t}\n"
        out += " hpos := by decide\n"
        out += " TT := timesTableO\n"
        out += " B' := B'\n"
        out += " T := Table\n"
        out += " heq := timesTableT_eq_Table\n"
        strT = ""
        for i in range(d):
            if i != d - _sage_const_1 :
                strT += '!' + str([[GF(p)(Table[i][j][k]) for k in range(d)] for j in range(d)]) + ', \n'
            else:
                strT += '!' + str([[GF(p)(Table[i][j][k]) for k in range(d)] for j in range(d)])
        out += " TMod := ![" + strT + "]\n"
        out += " hTMod := by decide\n"
        out += " hle := by decide\n"
        strv = ""
        for i in range(m):
            if i != m - _sage_const_1 :
                strv += '!' + str(v[i].list()) + ','
            else:
                strv += '!' + str(v[i].list())
        out += " b1 := ![" + strv + "]\n"
        strw = ""
        for i in range(n):
            if i != n - _sage_const_1 :
                strw += '!' + str(w[i].list()) + ','
            else:
                strw += '!' + str(w[i].list())
        out += " b2 := ![" + strw + "]\n"
        out += " v := ![" + strv + "]\n"
        out += " w := ![" + strw + "]\n"
        strF = ""
        for i in range(n):
            if i != n - _sage_const_1 :
                strF += '!' + str(wFrob[i].list()) + ','
            else:
                strF += '!' + str(wFrob[i].list())
        out += " wFrob := ![" + strF + "]\n"
        out += " v_ind := !" + str([v_ind[i] for i in range(m)]) + "\n"
        out += " w_ind := !" + str([w_ind[i] for i in range(n)]) + "\n"
        out += """ hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide \n"""
        strg = ""
        for i in range(d):
            if i != d - _sage_const_1 :
                strg += '!' + str(g[i]) + ','
            else:
                strg += '!' + str(g[i])
        out += " g := ![" + strg + "]\n"

        if flagW == _sage_const_1 :
            out += " w1 := !" + str([W[i] for i in range(m)]) + "\n"
            out += " w2 := !" + str([W[m + i] for i in range(n)]) + "\n"
            stra = ""
            for i in range(d):
                if i != d - _sage_const_1 :
                    stra += '!' + str(a[i]) + ','
                else:
                    stra += '!' + str(a[i])
            out += " a := ![" + stra + "]\n"
            strc = ""
            for i in range(d):
                if i != d - _sage_const_1 :
                    strc += '!' + str(c[i]) + ','
                else:
                    strc += '!' + str(c[i])
            out += " c := ![" + strc + "]\n"
            out += " hmulw := by decide \n"
            strac_indw = ""
            for i in range(d):
                if i != d - _sage_const_1 :
                    strac_indw += ac_ind_aux(i) + ', '
                else:
                    strac_indw += ac_ind_aux(i)
            out += " ac_indw := ![" + strac_indw + "]\n"
            out += " hacindw := by decide \n\n"
        else:
            stra = ""
            for i in range(d):
                stra += '!['
                for j in range(m):
                    if j != m - _sage_const_1 :
                        stra += '!' + str(a[i][j]) + ','
                    else:
                        stra += '!' + str(a[i][j])
                if i != d - _sage_const_1 :
                    stra += '],'
                else:
                    stra += ']'
            out += " a := ![" + stra + "]\n"

            strc = ""
            for i in range(d):
                strc += '!['
                for j in range(m):
                    if j != m - _sage_const_1 :
                        strc += '!' + str(c[i][j]) + ','
                    else:
                        strc += '!' + str(c[i][j])
                if i != d - _sage_const_1 :
                    strc += '],'
                else:
                    strc += ']'
            out += " c := ![" + strc + "]\n"

            strd = ""
            for i in range(d):
                strd += '!['
                for j in range(n):
                    if j != n - _sage_const_1 :
                        strd += '!' + str(dl[i][j]) + ','
                    else:
                        strd += '!' + str(dl[i][j])
                if i != d - _sage_const_1 :
                    strd += '],'
                else:
                    strd += ']'
            out += " d := ![" + strd + "]\n"

            stre = ""
            for i in range(d):
                stre += '!['
                for j in range(n):
                    if j != n - _sage_const_1 :
                        stre += '!' + str(e[i][j]) + ','
                    else:
                        stre += '!' + str(e[i][j])
                if i != d - _sage_const_1 :
                    stre += '],'
                else:
                    stre += ']'
            out += " e := ![" + stre + "]\n"

            strind = ""
            for i in range(d):
                if i != d - _sage_const_1 :
                    strind += '(' + ab_ind[i][_sage_const_0 ] + ', ' + ab_ind[i][_sage_const_1 ] + '),'
                else:
                    strind += '(' + ab_ind[i][_sage_const_0 ] + ', ' + ab_ind[i][_sage_const_1 ] + ')'
            out += " ab_ind := ![" + strind + "]\n"
            out += """ hindab := by decide
 hmul1 := by decide
 hmul2 := by decide
            \n"""
    return out, flag, flagW
def elems_to_matrix_power(l, n):
    M = [x.list() + [_sage_const_0 ] * (n - len(x.list())) for x in l]
    return Matrix(M).transpose()

@lru_cache(maxsize=int(_sage_const_8 ))
def _basis_matrix_inverse(B_tuple):
    return elems_to_matrix_power(list(B_tuple), len(B_tuple)).inverse()

def elems_to_basis(x, B):
    # B (the integral basis) is invariant across the tens of thousands of calls made while
    # generating certificates for one number field, so its change-of-basis matrix and its
    # inverse are cached instead of being rebuilt and re-inverted on every call.
    return _basis_matrix_inverse(tuple(B)) * (elems_to_matrix_power(x, len(B)))

def matrix_of_matrix_lists(M, m, n):
    L = []
    for i in range(m):
        for j in range(n):
            L = L + [M[i][j]]
    M = Matrix(L).transpose()
    return M

def IntegralBasisIdeal(I, B):
    n = len(B)
    Z_basis = I.basis()
    W = (((Matrix(ZZ, n, n, (elems_to_basis(Z_basis, B))).transpose())[:, ::-_sage_const_1 ].echelon_form())[:, ::-_sage_const_1 ])[::-_sage_const_1 , :].transpose()
    return W

def PseudoProject(M, b):
    # The second return value (a "norm", used only to rank/report candidates) is discarded by
    # every caller of SolveRightInteger, so it is computed here as a squared norm (an exact
    # integer/rational dot product) rather than via norm(): on an integer/rational vector,
    # norm() builds a symbolic sqrt() expression, which is orders of magnitude slower than the
    # dot product it's derived from and buys nothing since nothing downstream consumes it.
    n = len(M.columns())
    if n == _sage_const_0 :
        return b, float(vector(b).dot_product(vector(b)))
    else:
        L = []
        x = _sage_const_0  * M[:, _sage_const_0 ]
        S = []
        for i in range(n):
            L = L + [floor((vector(M[:, i]).dot_product(vector(b))) / (vector(M[:, i]).dot_product(vector(M[:, i]))))]
        for m in range(n):
            for j in range(m):
                x = x + L[j] * M[:, j]
            diff = vector(b) - vector(x)
            S = S + [(diff, diff.dot_product(diff))]
        Ls = sorted(S, key=lambda t: t[_sage_const_1 ])
        return Ls[_sage_const_0 ][_sage_const_0 ], float(Ls[_sage_const_0 ][_sage_const_1 ])

def SolveRightInteger(M, b):
    MAux, Echel = M.transpose().echelon_form(transformation=True)
    faux = Echel.transpose() * (MAux.transpose()).solve_right(b)
    faux, nm = PseudoProject(Echel.transpose()[:, len(M.rows()):], faux)
    return faux

def IdealEqSpanCertificate(K, ideal_gens, B):
    O = K.ring_of_integers()
    I = K.ideal(ideal_gens)
    n = len(B)
    Z_basis = I.basis()
    W = (((matrix(ZZ, (elems_to_basis(Z_basis, B))).transpose())[:, ::-_sage_const_1 ].echelon_form())[:, ::-_sage_const_1 ])[::-_sage_const_1 , :].transpose()
    M = Matrix(K, len(ideal_gens), n)
    MB = [[[] for j in range(n)] for i in range(len(ideal_gens))]

    for i in range(len(ideal_gens)):
        for j in range(n):
            M[i, j] = (ideal_gens[i]) * B[j]
            MB[i][j] = (elems_to_basis([M[i, j]], B)).list()

    Mland = Matrix(ZZ, matrix_of_matrix_lists(MB, len(ideal_gens), len(B)))
    faux = [() for k in range(n)]
    for k in range(n):
        faux[k] = SolveRightInteger(Mland, (vector(W[:, k])))

    f = [[[[] for j in range(n)] for i in range(len(ideal_gens))] for k in range(n)]
    for k in range(n):
        for i in range(len(ideal_gens)):
            for j in range(n):
                f[k][i][j] = faux[k][n * i + j]

    g = [[[[] for k in range(n)] for j in range(n)] for i in range(len(ideal_gens))]
    for i in range(len(ideal_gens)):
        for j in range(n):
            g[i][j] = (W.solve_right(vector(MB[i][j]))).list()

    w = [[] for i in range(n)]
    v = [[] for i in range(len(ideal_gens))]

    for i in range(len(ideal_gens)):
        v[i] = (elems_to_basis([ideal_gens[i]], B)).list()
    for j in range(n):
        w[j] = (W[:, j]).list()

    return Mland, f, g, v, w

def ExList(string):
    l = ''
    for x in string:
        if x == '[':
            l = l + '!['
        else:
            l = l + x
    return l

def MultiplicationTable(f, B):
    n = len(B)
    K = NumberField(f, names=('a',)); (a,) = K._first_ngens(1)
    A = [[[] for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            A[i][j] = (elems_to_basis([B[i] * B[j]], B)).list()
    return A

def IdealEqSpanCertificateLean(K, ideal_gens, B, name, ideal_name):
    """Returns (str, w) where w is the Z-basis of the ideal as column list."""
    Mland, f, g, v, w = IdealEqSpanCertificate(K, ideal_gens, B)
    n = len(B)
    out = "def " + name + ": IdealEqSpanCertificate timesTableO " + ideal_name + '\n '
    out += ExList(str(v)) + ' \n ' + ExList(str(w)) + ' where\n'
    out += """  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl \n"""
    bt = ZZ(len((Mland[_sage_const_0 , :]).list()) / len(ideal_gens))
    M = [[[] for j in range(n)] for i in range(len(ideal_gens))]
    for i in range(len(ideal_gens)):
        for j in range(bt):
            M[i][j] = (Mland[:, bt * i + j]).list()
    out += "  M :=" + ExList(str(M)) + "\n"
    out += "  hmulB := by decide\n"
    out += "  f := " + ExList(str(f)) + "\n"
    out += "  g := " + ExList(str(g)) + "\n"
    out += "  hle1 := by decide\n"
    out += "  hle2 := by decide\n"
    return out, w

def IdealEqSpanCertificateLeanComp(K, ideal_gens, B, name):
    """Returns (str, w) where w is the Z-basis of the ideal as column list."""
    Mland, f, g, v, w = IdealEqSpanCertificate(K, ideal_gens, B)
    n = len(B)
    out = "def " + name + ": IdealEqSpanCertificate' Table " + ExList(str(v)) + ' \n ' + ExList(str(w)) + ' where\n'
    bt = ZZ(len((Mland[_sage_const_0 , :]).list()) / len(ideal_gens))
    M = [[[] for j in range(n)] for i in range(len(ideal_gens))]
    for i in range(len(ideal_gens)):
        for j in range(bt):
            M[i][j] = (Mland[:, bt * i + j]).list()
    out += "  M :=" + ExList(str(M)) + "\n"
    out += "  hmulB := by decide  \n"
    out += "  f := " + ExList(str(f)) + "\n"
    out += "  g := " + ExList(str(g)) + "\n"
    out += "  hle1 := by decide   \n"
    out += "  hle2 := by decide  \n"
    return out, w

def IdealLift(K, B, ideal_gens, elem):
    n = len(B)
    O = K.ring_of_integers()
    I = K.ideal(ideal_gens)
    M = Matrix(K, len(ideal_gens), n)
    MB = [[[] for j in range(n)] for i in range(len(ideal_gens))]
    for i in range(len(ideal_gens)):
        for j in range(n):
            M[i, j] = (ideal_gens[i]) * B[j]
            MB[i][j] = (elems_to_basis([M[i, j]], B)).list()
    Mland = Matrix(ZZ, matrix_of_matrix_lists(MB, len(ideal_gens), n))
    faux = SolveRightInteger(Mland, (vector(elems_to_basis([elem], B))))
    flag = _sage_const_0 
    for z in faux:
        if z not in ZZ:
            flag = _sage_const_1 
            return _sage_const_0 
    k = len(ideal_gens)
    x = [_sage_const_0  for j in range(k)]
    for j in range(k):
        for i in range(n):
            x[j] = x[j] + faux[n * j + i] * B[i]
    check = _sage_const_0 
    for j in range(k):
        check = check + x[j] * ideal_gens[j]
    if check == elem:
        return x
    else:
        raise ValueError('IdealLift: something went wrong.')

def IdealMultiplication(K, B, ideal_gens1, ideal_gens2):
    O = K.ring_of_integers()
    I1 = K.ideal(ideal_gens1)
    I2 = K.ideal(ideal_gens2)
    p = factor((I1 * I2).norm())[_sage_const_0 ][_sage_const_0 ]
    if I1 * I2 == K.ideal(p):
        ideal_gens3 = [p]
    else:
        ideal_gens3 = (I1 * I2).gens_reduced(proof=False)
    M = [[[] for j in range(len(ideal_gens2))] for i in range(len(ideal_gens1))]
    Mcoord = [[[] for j in range(len(ideal_gens2))] for i in range(len(ideal_gens1))]
    for i in range(len(ideal_gens1)):
        for j in range(len(ideal_gens2)):
            M[i][j] = ideal_gens1[i] * ideal_gens2[j]
            Mcoord[i][j] = (elems_to_basis([M[i][j]], B)).list()
    Maux = []
    for i in range(len(ideal_gens1)):
        Maux = Maux + M[i]
    f = [[[[] for i in range(len(ideal_gens2))] for j in range(len(ideal_gens1))] for k in range(len(ideal_gens3))]
    for i in range(len(ideal_gens3)):
        faux = IdealLift(K, B, Maux, ideal_gens3[i])
        for j in range(len(ideal_gens1)):
            for k in range(len(ideal_gens2)):
                f[i][j][k] = elems_to_basis([faux[(len(ideal_gens2)) * j + k]], B).list()
    g = [[[[] for i in range(len(ideal_gens3))] for j in range(len(ideal_gens2))] for k in range(len(ideal_gens1))]
    for i in range(len(ideal_gens1)):
        for j in range(len(ideal_gens2)):
            for k in range(len(ideal_gens3)):
                g[i][j][k] = elems_to_basis([IdealLift(K, B, ideal_gens3, M[i][j])[k]], B).list()
    return ideal_gens3, Mcoord, f, g

def IdealPowerGenerator(K, B, gens, m):
    """Return a generator list for gens^m, computed via the same repeated
    IdealMultiplication used by IteratedMulLean/IdealPowLean.

    gens_reduced() doesn't return a canonical representative, so computing a
    power's generator via a *different* path than the certificate-generation
    code (e.g. a direct (ideal^m).gens_reduced() call) risks landing on a
    different, but equally valid, associate -- which IdealPowLean's
    exact-equality check then rejects. Using this same iterated-multiplication
    path wherever a power's generator is needed keeps every computation of it
    consistent by construction.
    """
    accum = gens
    for _ in range(m - _sage_const_1 ):
        accum = IdealMultiplication(K, B, accum, gens)[_sage_const_0 ]
    return accum

def IdealMulEqCertificateLean(nameC, K, B, ideal_gens1, ideal_gens2, proof1_name, proof2_name, ideal1_name, ideal2_name):
    """Returns (str, ideal_gens3)."""
    ideal_gens3, Mcoord, f, g = IdealMultiplication(K, B, ideal_gens1, ideal_gens2)
    ideal_gens1_coord = [elems_to_basis([ideal_gens1[i]], B).list() for i in range(len(ideal_gens1))]
    ideal_gens2_coord = [elems_to_basis([ideal_gens2[i]], B).list() for i in range(len(ideal_gens2))]
    ideal_gens3_coord = [elems_to_basis([ideal_gens3[i]], B).list() for i in range(len(ideal_gens3))]
    out = f"def {nameC} : IdealMulEqCertificate timesTableO " + ideal1_name + ' ' + ideal2_name + "\n"
    out += '  ' + ExList(str(ideal_gens1_coord)) + ' ' + ExList(str(ideal_gens2_coord)) + "\n"
    out += '  ' + ExList(str(ideal_gens3_coord)) + ' where\n'
    out += f" T := Table\n heq := timesTableT_eq_Table\n hI1 := {proof1_name}\n hI2 := {proof2_name}\n"
    out += ' M := ' + ExList(str(Mcoord)) + "\n"
    out += ' hmul := by decide\n'
    out += ' f := ' + ExList(str(f)) + "\n"
    out += ' g := ' + ExList(str(g)) + "\n"
    out += ' hle1 := by decide\n'
    out += ' hle2 := by decide\n'
    return out, ideal_gens3

def IdealMulEqCertificateLeanComp(nameC, K, B, ideal_gens1, ideal_gens2):
    """Returns (str, ideal_gens3)."""
    ideal_gens3, Mcoord, f, g = IdealMultiplication(K, B, ideal_gens1, ideal_gens2)
    ideal_gens1_coord = [elems_to_basis([ideal_gens1[i]], B).list() for i in range(len(ideal_gens1))]
    ideal_gens2_coord = [elems_to_basis([ideal_gens2[i]], B).list() for i in range(len(ideal_gens2))]
    ideal_gens3_coord = [elems_to_basis([ideal_gens3[i]], B).list() for i in range(len(ideal_gens3))]
    out = f"def {nameC} : IdealMulEqCertificate' Table \n"
    out += '  ' + ExList(str(ideal_gens1_coord)) + ' ' + ExList(str(ideal_gens2_coord)) + "\n"
    out += '  ' + ExList(str(ideal_gens3_coord)) + ' where\n'
    out += ' M := ' + ExList(str(Mcoord)) + "\n"
    out += ' hmul := by decide\n'
    out += ' f := ' + ExList(str(f)) + "\n"
    out += ' g := ' + ExList(str(g)) + "\n"
    out += ' hle1 := by decide\n'
    out += ' hle2 := by decide\n'
    return out, ideal_gens3

def IdealMulLeCertificateLeanComp(nameC, K, B, ideal_gens1, ideal_gens2):
    """Returns (str, ideal_gens3)."""
    ideal_gens3, Mcoord, f, g = IdealMultiplication(K, B, ideal_gens1, ideal_gens2)
    ideal_gens1_coord = [elems_to_basis([ideal_gens1[i]], B).list() for i in range(len(ideal_gens1))]
    ideal_gens2_coord = [elems_to_basis([ideal_gens2[i]], B).list() for i in range(len(ideal_gens2))]
    ideal_gens3_coord = [elems_to_basis([ideal_gens3[i]], B).list() for i in range(len(ideal_gens3))]
    out = f"def {nameC} : IdealMulLeCertificate' Table \n"
    out += '  ' + ExList(str(ideal_gens1_coord)) + ' ' + ExList(str(ideal_gens2_coord)) + "\n"
    out += '  ' + ExList(str(ideal_gens3_coord)) + ' where\n'
    out += ' M := ' + ExList(str(Mcoord)) + "\n"
    out += ' hmul := by decide  \n'
    out += ' g := ' + ExList(str(g)) + "\n"
    out += ' hle2 := by decide  \n'
    return out, ideal_gens3

def IteratedMulLean(K, B, ideal_gens, ideal_pows, proof1_name, proof2_name, ideal_name, flagg):
    """Returns (str, ideal_gens_succ, ideal_gens_accum)."""
    suffix = '0'
    if flagg == _sage_const_1 :
        suffix = ''
    ideal_name_accum = ideal_name + suffix
    m = len(ideal_gens)
    ideal_gens_succ = [[_sage_const_1 ]]
    ideal_gens_accum = ideal_gens[_sage_const_0 ]
    ideal_gens_succ = ideal_gens_succ + [ideal_gens_accum]
    cont = _sage_const_0 
    proof_name = proof1_name
    out = ""
    for i in range(m):
        if i == _sage_const_0 :
            for j in range(ideal_pows[i] - _sage_const_1 ):
                sub_out, ideal_gens_accum = IdealMulEqCertificateLean(
                    'Mul' + str(ideal_name) + str(cont), K, B,
                    ideal_gens_accum, ideal_gens[i], proof_name, proof2_name,
                    '(' + ideal_name_accum + ')', str(ideal_name) + suffix)
                out += sub_out + "\n"
                ideal_name_accum = ideal_name_accum + '*' + str(ideal_name) + suffix
                proof_name = "ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ " + 'Mul' + str(ideal_name) + str(cont)
                cont = cont + _sage_const_1 
                ideal_gens_succ = ideal_gens_succ + [ideal_gens_accum]
        else:
            for j in range(ideal_pows[i]):
                sub_out, ideal_gens_accum = IdealMulEqCertificateLean(
                    'Mul' + str(ideal_name) + str(cont), K, B,
                    ideal_gens_accum, ideal_gens[i], proof_name, proof2_name,
                    '(' + ideal_name_accum + ')', str(ideal_name) + str(i))
                out += sub_out + "\n"
                ideal_name_accum = ideal_name_accum + '*' + str(ideal_name) + str(i)
                proof_name = "ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ " + 'Mul' + str(ideal_name) + str(cont)
                cont = cont + _sage_const_1 
                ideal_gens_succ = ideal_gens_succ + [ideal_gens_accum]
    return out, ideal_gens_succ, ideal_gens_accum

def IteratedMulLeanComp(K, B, ideal_gens, ideal_pows, ideal_name):
    """Returns (str, ideal_gens_succ, ideal_gens_accum)."""
    m = len(ideal_gens)
    ideal_gens_succ = [[_sage_const_1 ]]
    ideal_gens_accum = ideal_gens[_sage_const_0 ]
    ideal_gens_succ = ideal_gens_succ + [ideal_gens_accum]
    cont = _sage_const_0 
    out = ""
    for i in range(m):
        if i == _sage_const_0 :
            for j in range(ideal_pows[i] - _sage_const_1 ):
                sub_out, ideal_gens_accum = IdealMulEqCertificateLeanComp(
                    'Mul' + str(ideal_name) + str(cont), K, B,
                    ideal_gens_accum, ideal_gens[i])
                out += sub_out
                cont = cont + _sage_const_1 
                ideal_gens_succ = ideal_gens_succ + [ideal_gens_accum]
        else:
            for j in range(ideal_pows[i]):
                sub_out, ideal_gens_accum = IdealMulEqCertificateLeanComp(
                    'Mul' + str(ideal_name) + str(cont), K, B,
                    ideal_gens_accum, ideal_gens[i])
                out += sub_out
                cont = cont + _sage_const_1 
                ideal_gens_succ = ideal_gens_succ + [ideal_gens_accum]
    return out, ideal_gens_succ, ideal_gens_accum

def IteratedMulLeLeanComp(K, B, ideal_gens, ideal_pows, ideal_name):
    """Returns (str, ideal_gens_succ, ideal_gens_accum)."""
    m = len(ideal_gens)
    ideal_gens_succ = [[_sage_const_1 ]]
    ideal_gens_accum = ideal_gens[_sage_const_0 ]
    ideal_gens_succ = ideal_gens_succ + [ideal_gens_accum]
    cont = _sage_const_0 
    out = ""
    for i in range(m):
        if i == _sage_const_0 :
            for j in range(ideal_pows[i] - _sage_const_1 ):
                sub_out, ideal_gens_accum = IdealMulLeCertificateLeanComp(
                    'Mul' + str(ideal_name) + str(cont), K, B,
                    ideal_gens_accum, ideal_gens[i])
                out += sub_out
                cont = cont + _sage_const_1 
                ideal_gens_succ = ideal_gens_succ + [ideal_gens_accum]
        else:
            for j in range(ideal_pows[i]):
                sub_out, ideal_gens_accum = IdealMulLeCertificateLeanComp(
                    'Mul' + str(ideal_name) + str(cont), K, B,
                    ideal_gens_accum, ideal_gens[i])
                out += sub_out
                cont = cont + _sage_const_1 
                ideal_gens_succ = ideal_gens_succ + [ideal_gens_accum]
                out += "\n"
    return out, ideal_gens_succ, ideal_gens_accum

def IteratedMulLeanWithCert(K, B, ideal_gens, ideal_pows, proof_cert, ideal_name, ideal_pow_gens):
    """Returns (str, ideal_gens_accum)."""
    m = len(ideal_gens)
    O = K.ring_of_integers()

    ideal_name_pow = ['' for i in range(m)]
    for i in range(m):
        for j in range(ideal_pows[i]):
            if j == _sage_const_0 :
                ideal_name_pow[i] = str(ideal_name) + str(i)
            else:
                ideal_name_pow[i] = '(' + ideal_name_pow[i] + '*' + str(ideal_name) + str(i) + ')'

    name_lemma_aux = [ideal_name + str(i) + '_' + str(ideal_pows[i]) for i in range(m)]
    name_lemma = ''.join(name_lemma_aux)
    exp_lemma = '*'.join([ideal_name + str(i) + ' ^ ' + str(ideal_pows[i]) for i in range(m)])
    pows_label = ''.join([str(i) for i in ideal_pows])

    ideal_gens_pow = [ideal_pow_gens[i][ideal_pows[i]] for i in range(m)]

    name_lemma_aux_filtered = [name_lemma_aux[i] for i in range(m) if ideal_pows[i] != _sage_const_0 ]
    ideal_gens_pow = [ideal_gens_pow[i] for i in range(m) if ideal_pows[i] != _sage_const_0 ]
    ideal_name_pow = [ideal_name_pow[i] for i in range(m) if ideal_pows[i] != _sage_const_0 ]
    proof_cert = [proof_cert[i] for i in range(m) if ideal_pows[i] != _sage_const_0 ]
    ideal_pows = [ideal_pows[i] for i in range(m) if ideal_pows[i] != _sage_const_0 ]
    ideal_gens_accum = ideal_gens_pow[_sage_const_0 ]

    ideal_name_accum = ideal_name_pow[_sage_const_0 ]
    ideal_name_accum2 = name_lemma_aux_filtered[_sage_const_0 ]

    proof_cert_c = ['' for i in range(len(proof_cert))]
    if proof_cert[_sage_const_0 ] != 'rfl':
        proof_cert_c[_sage_const_0 ] = "ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ " + proof_cert[_sage_const_0 ]
    else:
        proof_cert_c[_sage_const_0 ] = 'rfl'

    proof_name = proof_cert_c[_sage_const_0 ]
    out = ""

    for i in range(len(ideal_name_pow) - _sage_const_1 ):
        if proof_cert[i + _sage_const_1 ] != 'rfl':
            proof_cert_c[i + _sage_const_1 ] = "ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ " + proof_cert[i + _sage_const_1 ]
        else:
            proof_cert_c[i + _sage_const_1 ] = 'rfl'
        ideal_name_accum2 = ideal_name_accum2 + str(name_lemma_aux_filtered[i + _sage_const_1 ])
        sub_out, ideal_gens_accum = IdealMulEqCertificateLean(
            'MulR' + pows_label + '_' + str(ideal_name_accum2), K, B,
            ideal_gens_accum, ideal_gens_pow[i + _sage_const_1 ], proof_name, proof_cert_c[i + _sage_const_1 ],
            '(' + ideal_name_accum + ')', str(ideal_name_pow[i + _sage_const_1 ]))
        out += sub_out
        ideal_name_accum = ideal_name_accum + ' * ' + str(ideal_name_pow[i + _sage_const_1 ])
        proof_name = "ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ " + 'MulR' + pows_label + '_' + ideal_name_accum2

    out += "\n"
    gens_coords = ExList(str([list(elems_to_basis(ideal_gens_accum, B).columns()[i]) for i in range(len(ideal_gens_accum))]))
    out += f"lemma Pow{name_lemma} : {exp_lemma} = Ideal.span (Set.range fun i ↦ B.equivFun.symm ({gens_coords} i)) := by \n"
    out += " simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]\n"
    if sum(ideal_pows) == _sage_const_1 :
        out += " rfl\n"
    else:
        if len(ideal_name_pow) > _sage_const_1 :
            out += f" simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR{pows_label}_{ideal_name_accum2}]\n"
            out += " rfl\n"
        else:
            out += f" simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ {proof_cert[_sage_const_0 ]}]\n"
            out += " rfl     \n"
    return out, ideal_gens_accum

def IdealMemZLean2(K, B, ideal_gens, mem_coords, name_lemma, name_ideal, cert_name_eq):
    """Returns a Lean certificate string for membership in the ideal, or '' if check fails."""
    Mland, f, g, v, w = IdealEqSpanCertificate(K, ideal_gens, B)
    g = Matrix(w).transpose().solve_right(vector(mem_coords))
    for x in g:
        if x not in ZZ:
            return ""
    out = f"def {name_lemma} : IdealMemCertificate B {name_ideal}\n"
    out += ' ' + ExList(str(w)) + ' ' + ExList(str(mem_coords)) + ' where\n'
    out += f" hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl {cert_name_eq}\n"
    out += ' g := ' + ExList(str(g.list())) + "\n"
    out += ' hmem := by decide\n'
    return out

def IsOrderOf(p, name):
    """Returns a Lean proof string that primitive_root(p) has order p-1 in ZMod p."""
    out = f"def {name} : IsOrderOf ({primitive_root(p)} : ZMod {p}) {p-_sage_const_1 } where\n"
    F = factor(p - _sage_const_1 )
    m = len(F)
    out += f" m := {m}\n"
    P = [x[_sage_const_0 ] for x in F]
    e = [x[_sage_const_1 ] for x in F]
    out += " P := " + ExList(str(P)) + "\n"
    out += " e := " + ExList(str(e)) + "\n"
    out += """ hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow\n"""
    return out

def DiscreteLog(O, I, x, z):
    R = QuotientRing(O, I, 'y')
    for i in range(I.norm()):
        if R(x) == R(z)**i:
            return i, Mod(z**i, I.norm())

def MatrixPrimesG(K, O, p, elems, expo, T):
    L = []
    U = K.unit_group(proof=False).gens()
    flag_dvdtor = _sage_const_0 

    for i in range(len(U)):
        if i == _sage_const_0 :
            if order(U[_sage_const_0 ]) % p == _sage_const_0 :
                L = L + [U[_sage_const_0 ]]
                flag_dvdtor = _sage_const_1 
        else:
            L = L + [U[i]]

    phi_dvd = [i for i in range(len(elems)) if expo[i] % p == _sage_const_0 ]

    if flag_dvdtor == _sage_const_1 :
        L = L[_sage_const_1 :] + [L[_sage_const_0 ]] + [elems[i] for i in phi_dvd]
    else:
        L = L + [elems[i] for i in phi_dvd]

    Ql = []
    A = []
    cont = _sage_const_0 
    for q in primes(T + _sage_const_1 ):
        if cont == len(L):
            break
        else:
            if (q - _sage_const_1 ) % p == _sage_const_0 :
                z = primitive_root(q)
                F = factor(K.ideal(q))
                for Q in F:
                    if Q[_sage_const_0 ].norm() == q:
                        flF = true
                        for j in range(len(L)):
                            if L[j] in Q[_sage_const_0 ]:
                                flF = false
                                break
                        if flF == true:
                            B_mat = A + [[DiscreteLog(O, Q[_sage_const_0 ], L[j], z)[_sage_const_0 ] % p for j in range(len(L))]]
                            if Matrix(B_mat).change_ring(GF(p)).rank() > cont:
                                Ql = Ql + [Q]
                                cont = cont + _sage_const_1 
                                A = B_mat
        if cont == len(L):
            pivots = Matrix(GF(p), A)[:, :-len(phi_dvd)].transpose().pivots()
            A_initial = [A[i] for i in pivots]
            A_last = [A[i] for i in range(len(L)) if i not in pivots]
            Ql_initial = [Ql[i][_sage_const_0 ] for i in pivots]
            Ql_last = [Ql[i][_sage_const_0 ] for i in range(len(L)) if i not in pivots]
            A = A_initial + A_last
            Ql = Ql_initial + Ql_last
            return phi_dvd, Matrix(A), Ql, L, flag_dvdtor
    return _sage_const_0 

def FindNzEntry(w):
    for i in range(len(w)):
        for j in range(len(w[_sage_const_0 ])):
            if w[i][j] != _sage_const_0 :
                return i, j

def DiscreteLogCLean(K, B, name, ideal_gens, hcard, hprim_root, p, x, x_name, name_ideal, cert_name_eq):
    """Returns (str, k_mod_p, m)."""
    mem_coords = elems_to_basis([x], B).list()
    O = K.ring_of_integers()
    I = K.ideal(ideal_gens)
    q = I.norm()
    k, m = DiscreteLog(O, I, x, primitive_root(q))
    mem_coords[_sage_const_0 ] = mem_coords[_sage_const_0 ] - ZZ(m)
    out = IdealMemZLean2(K, B, ideal_gens, mem_coords, name + 'Mem', name_ideal, cert_name_eq)
    out += "\n"
    out += f"def {name}: DiscreteLogCertificate {hcard} {hprim_root} {p} {x_name} {k % p} where\n"
    out += f" r := {len(B)}\n"
    out += " hN := by infer_instance\n"
    out += " hpdvd := by decide\n"
    out += " B := B\n"
    out += " hone := B_one\n"
    out += " xcoord := " + ExList(str(elems_to_basis([x], B).list())) + "\n"
    out += " hxeq :=  rfl\n"
    out += f" m := {m}\n"
    out += " C := " + ExList(str(mem_coords)) + "\n"
    out += " hCeq := by rfl\n"
    out += " hmem := mem_of_certificate _ _ _ _ " + name + "Mem\n"
    out += f" k := {k}\n"
    out += " hpow := by zmod_pow\n"
    out += " heql := by decide\n"
    return out, k % p, m

def DiscreteLogListLean(K, B, list_ideal_gens, ideal_name, p, list_elems, name_elems):
    """Returns (str, L, M) where L is the discrete log matrix and M is the value matrix."""
    O = K.ring_of_integers()
    N = set([K.ideal(x).norm() for x in list_ideal_gens])
    L = zero_matrix(len(list_ideal_gens), len(list_elems))
    M = zero_matrix(len(list_ideal_gens), len(list_elems))
    out = ""

    for q in N:
        out += f"instance hq{q} : Fact $ Nat.Prime {q} := {{out := by norm_num}}\n"
    out += "\n"

    for q in N:
        out += IsOrderOf(q, 'R' + str(q))
        out += "\n"

    for i in range(len(list_ideal_gens)):
        gensc = [elems_to_basis([x], B).list() for x in list_ideal_gens[i]]
        out += f"def {ideal_name}{i} : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (" + ExList(str(gensc)) + " i)))\n"
    out += "\n"

    for i in range(len(list_ideal_gens)):
        sub_out, w = IdealEqSpanCertificateLeanComp(K, list_ideal_gens[i], B, 'A' + str(i))
        out += sub_out
        ik, jk = FindNzEntry(w)
        out += "\n"
        out += f"lemma N{i} : Nat.card (O ⧸ {ideal_name}{i}) = {K.ideal(list_ideal_gens[i]).norm()} := \n"
        out += f"ideal_norm_eq_prod' B _ _ (by decide) {ik} {jk} (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A{i})\n"
        out += "\n"

    for i in range(len(list_ideal_gens)):
        for j in range(len(list_elems)):
            sub_out, l, m = DiscreteLogCLean(
                K, B, 'Log' + str(i) + str(j), list_ideal_gens[i],
                'N' + str(i),
                f'((orderOf_of_IsOrderOf R{K.ideal(list_ideal_gens[i]).norm()}) ▸ IsPrimitiveRoot.orderOf _)',
                p, list_elems[j], name_elems[j], ideal_name + str(i), 'A' + str(i))
            out += sub_out
            out += "\n"
            L[i, j] = l
            M[i, j] = m
    return out, L, M

def IdealPowLean(K, B, lemma_name, ideal_gens, ideal_name, elem, elem_name, m):
    """Returns (str, ig) where ig is the sequence of intermediate generators."""
    gensc = [elems_to_basis([x], B).list() for x in ideal_gens]
    out = f"def {ideal_name} : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (" + ExList(str(gensc)) + " i)))\n"
    sub_out, ig, a = IteratedMulLean(K, B, [ideal_gens], [m], 'rfl', 'rfl', ideal_name, _sage_const_1 )
    out += sub_out
    if a[_sage_const_0 ] != elem:
        raise ValueError(f"IdealPowLean: generators don't match. Computed: {a[_sage_const_0 ]}, Given: {elem}")
    out += f"lemma {lemma_name} : {ideal_name} ^ {m} = " + "Ideal.span {" + elem_name + "} := by\n"
    out += f" simp only [pow_succ, pow_one, pow_zero, one_mul]\n"
    out += f" simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ Mul{ideal_name}{m - _sage_const_2 }, {elem_name}]\n"
    out += f" rfl\n"
    return out, ig

def PrimePNeDvd(K, B, p):
    O = K.ring_of_integers()
    for q in prime_range(_sage_const_1 , _sage_const_100 ):
        if (q - _sage_const_1 ) % p != _sage_const_0  and p != q:
            F = factor(K.ideal(q))
            for I in F:
                if I[_sage_const_0 ].norm() == q:
                    return I[_sage_const_0 ], [x for x in I[_sage_const_0 ].gens_reduced(proof=False)]

def pNeDvdTorsionLean(K, B, finrank_proof, integral_closure_eq, ideal_name, p):
    """Returns a Lean proof string that p does not divide the torsion order."""
    out = ""
    if K.degree() % _sage_const_2  != _sage_const_0  and finrank_proof != '':
        out += f"lemma ne_dvd_torsion{p} : ¬{p} ∣ Nat.card ↥(CommGroup.torsion (↥O)ˣ) := by\n"
        out += f""" suffices ¬ {p} ∣ 2 from ?_
 · convert this
   rw [{integral_closure_eq}, ← Fintype.card_eq_nat_card,
   ←  NumberField.Units.torsionOrder_eq_two_of_odd_finrank (by erw [{finrank_proof}] ; decide)]
   rfl
 · decide\n"""
    else:
        I, gens = PrimePNeDvd(K, B, p)
        gensc = [elems_to_basis([gens[i]], B).list() for i in range(len(gens))]
        out += f"def {ideal_name} : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (" + ExList(str(gensc)) + " i)))\n"
        out += "\n"
        sub_out, w = IdealEqSpanCertificateLean(K, gens, B, f'A{ideal_name}', ideal_name)
        out += sub_out
        out += "\n"
        out += f" lemma ne_dvd_torsion{p} : ¬{p} ∣ Nat.card ↥(CommGroup.torsion (↥O)ˣ) := by \n"
        out += f"""  refine prime_not_dvd_torsion_of_not_dvd (by decide) {ideal_name}
     (ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate A{ideal_name}))
     (by decide) (by decide)\n"""
    return out

def IsUnitInvLean(B, list_elems, list_names):
    """Returns Lean proofs that the given elements are units."""
    list_elems_inv = [x**(-_sage_const_1 ) for x in list_elems]
    gensc = [elems_to_basis([x], B).list() for x in list_elems_inv]
    out = ""
    for i in range(len(list_elems)):
        out += f"lemma isUnit_{list_names[i]} : IsUnit {list_names[i]} := by \n"
        out += f" apply IsUnit.of_mul_eq_one (B.equivFun.symm {ExList(str(gensc[i]))})\n"
        out += """ rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide\n"""
        out += "\n"
    return out

def SturmSequencePseudo(p, q):
    R = PolynomialRing(ZZ, names=('X',)); (X,) = R._first_ngens(1)
    P = [p, q]
    if gcd(p, q) != _sage_const_1 :
        raise ValueError('SturmSequencePseudo: polynomials p and q are not coprime')
    e = []
    f = []
    Q = []
    deg = p.degree()
    i = _sage_const_0 
    g = _sage_const_1 
    h = _sage_const_1 
    while deg > _sage_const_0  and i < _sage_const_100 :
        delta = P[i].degree() - P[i + _sage_const_1 ].degree()
        e = e + [abs(((P[i + _sage_const_1 ]).list()[-_sage_const_1 ])**(delta + _sage_const_1 ))]
        paux = e[i] * P[i]
        p_i2 = -paux % P[i + _sage_const_1 ]
        Q = Q + [ZZ[X]((paux + p_i2) / P[i + _sage_const_1 ])]
        f = f + [g * (h**delta)]
        P = P + [p_i2 / f[i]]
        deg = p_i2.degree()
        i = i + _sage_const_1 
        g = abs((P[i]).list()[-_sage_const_1 ])
        h = h**(_sage_const_1  - delta) * g**delta
    return e, f, [q.list() for q in Q], [p.list() for p in P]

def SturmCertificateLean(p, name):
    """Returns (str, P) where P is the Sturm sequence."""
    q = p.derivative()
    e, f, Q, P = SturmSequencePseudo(p, q)
    out = f"""def {name} : SturmBuilderOfList {P} {P[_sage_const_0 ]} {P[_sage_const_1 ]} where
  hlen := by decide
  h0 := by decide
  h1 := by decide
  hlast := by decide
  hdrop := by decide
  hmono := by
    dsimp
    intro i hic
    have hi : i < {len(P) - _sage_const_1 } := by omega
    interval_cases i <;> (dsimp ; decide)
  e := {e}
  f := {f}
  epos := by decide
  fpos := by decide
  Q := {Q}
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    dsimp
    intro i hi
    have hi : i < {len(P) - _sage_const_2 } := by omega
    interval_cases i <;> (dsimp ; decide)\n"""
    return out, P

def RankUnitCertificateLean(f, proof_ofList, proof_AdjoinRoot, proof_integral_closure_eq, name_cert):
    """Returns a Lean certificate string for the rank of units."""
    R = PolynomialRing(ZZ, names=('X',)); (X,) = R._first_ngens(1)
    F = PolynomialRing(RR, names=('x',)); (x,) = F._first_ngens(1)
    sturm_str, P = SturmCertificateLean(f, f'Sturm{name_cert}')
    k = len((F(f)).roots())
    r = (k + f.degree()) / _sage_const_2 
    out = sturm_str
    out += "\n"
    out += f"def {name_cert} : RankUnitsCertificate O where\n"
    out += f"  f := {R(f)}\n"
    out += f"  l := {R(f).list()}\n"
    out += f"  hl := {proof_ofList}\n"
    out += "  hlz := by decide\n"
    out += "  hz := by decide\n"
    out += f"  hAdj := {proof_AdjoinRoot}\n"
    out += f"  heq := {proof_integral_closure_eq}\n"
    out += f"  P := {P}\n"
    out += f"  SB := Sturm{name_cert}\n"
    out += f"  k := {k}\n"
    out += f"  r := {r}\n"
    out += "  hr := by decide\n"
    out += "  hreq := by decide \n"
    return out

def TorsionUnitProof(K, B, v, name):
    """Returns (str, m) where m is the multiplicative order of v."""
    m = K(v).multiplicative_order()
    out = f"lemma v_pow_one : {name} ^ {m} = 1 := by\n"
    out += "  rw [← B_one_repr]\n"
    out += "  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) \n"
    out += "   timesTableT_eq_Table _ (by norm_num)\n"
    out += "  decide\n"
    return out, m

def CertificateMaximalUnitsNDvdT(M, p, zeta_names, prefix, prime_ideal_name, primes_q, name_rank_cert):
    """Returns a Lean certificate string for maximal units (p does not divide torsion)."""
    name_ring = 'O'
    u0 = ', '.join(zeta_names)
    d = len(list(M[_sage_const_0 , :])[_sage_const_0 ])
    In = ', '.join([prefix + '.' + prime_ideal_name + str(i) for i in range(d)])
    M = Matrix(GF(p), M)
    out = f"def NPCU{p} : pMaximalUnitsCertificateNDvdT {name_ring} {p} where \n"
    out += f" hp := by decide\n"
    out += f" r := {len(zeta_names)}\n"
    out += f" huc := by \n  erw [units_finrank_of_RankUnitsCertificate {name_rank_cert}]\n  decide\n"
    out += f" u := ![{u0}]\n"
    if len(zeta_names) == _sage_const_0 :
        out += " hu := by decide\n"
    else:
        out += " hu := fun i => \n  match i with \n"
        for i in range(len(zeta_names)):
            out += f"  | {i} => isUnit_{zeta_names[i]}\n"
    out += f" t := {len(primes_q)}\n"
    out += " hrle := by decide\n"
    out += f" q := {ExList(str(primes_q))}\n"
    out += " hqP := by \n  intro i \n  match i with \n"
    for i in range(len(primes_q)):
        out += f"  | {i} => exact {prefix}.hq{primes_q[i]}\n"
    out += f" I := ![{In}]\n"
    out += " hcard := fun i =>\n  match i with  \n"
    for i in range(d):
        out += f"  | {i} => {prefix}.N{i}\n"
    out += f" ζ := !{[primitive_root(q) for q in primes_q]}\n"
    out += " hr := fun i =>\n  match i with \n"
    for i in range(len(primes_q)):
        out += f"  | {i} => ((orderOf_of_IsOrderOf {prefix}.R{primes_q[i]}) ▸ IsPrimitiveRoot.orderOf _)\n"
    out += f" hdvd := by decide\n"
    out += f" hpndvdt := ne_dvd_torsion{p}\n"
    out += f" M := {ExList(str([list(list(M[i, _sage_const_0 :len(zeta_names)])[_sage_const_0 ]) for i in range(d)]))}\n"
    out += " hM1 := by \n  intro i j\n  fin_cases i <;> fin_cases j \n"
    for i in range(len(primes_q)):
        for j in range(len(zeta_names)):
            out += f"  · erw [eq_of_DiscreteLogCertificate {prefix}.Log{i}{j}] ; decide\n"
    _M_inv = Matrix(GF(p), M[_sage_const_0 :len(zeta_names), _sage_const_0 :len(zeta_names)]).inverse()
    _Minv = [list(_M_inv.row(i)) for i in range(len(zeta_names))]
    out += f" Minv := {ExList(str(_Minv))} \n"
    out += " hInv := by decide\n"
    return out

def CertificateMaximalUnitsDvdT(M, p, zeta_names, v_name, order_v, prefix, prime_ideal_name, primes_q, name_rank_cert):
    """Returns a Lean certificate string for maximal units (p divides torsion)."""
    name_ring = 'O'
    u0 = ', '.join(zeta_names)
    d = len(list(M[_sage_const_0 , :])[_sage_const_0 ])
    In = ', '.join([prefix + '.' + prime_ideal_name + str(i) for i in range(d)])
    M = Matrix(GF(p), M)
    out = f"def NPCU{p} : pMaximalUnitsCertificateDvdT {name_ring} {p} where \n"
    out += f" hp := by decide\n"
    out += f" r := {len(zeta_names)}\n"
    out += f" huc := by \n  erw [units_finrank_of_RankUnitsCertificate {name_rank_cert}]\n  decide\n"
    out += f" u := ![{u0}]\n"
    if len(zeta_names) == _sage_const_0 :
        out += " hu := by decide\n"
    else:
        out += " hu := fun i => \n  match i with \n"
        for i in range(len(zeta_names)):
            out += f"  | {i} => isUnit_{zeta_names[i]}\n"
    out += f" v := {v_name}\n"
    out += f" m := {order_v}\n"
    out += " hm := by norm_num\n"
    out += " hmv := v_pow_one\n"
    out += f" t := {len(primes_q)}\n"
    out += " hrle := by decide\n"
    out += f" q := {ExList(str(primes_q))}\n"
    out += " hqP := by \n  intro i \n  match i with \n"
    for i in range(len(primes_q)):
        out += f"  | {i} => exact {prefix}.hq{primes_q[i]}\n"
    out += f" I := ![{In}]\n"
    out += " hcard := fun i =>\n  match i with  \n"
    for i in range(d):
        out += f"  | {i} => {prefix}.N{i}\n"
    out += f" ζ := !{[primitive_root(q) for q in primes_q]}\n"
    out += " hr := fun i =>\n  match i with \n"
    for i in range(len(primes_q)):
        out += f"  | {i} => ((orderOf_of_IsOrderOf {prefix}.R{primes_q[i]}) ▸ IsPrimitiveRoot.orderOf _)\n"
    out += f" hdvd := by decide\n"
    out += f" M := {ExList(str([list(list(M[i, _sage_const_0 :len(zeta_names) + _sage_const_1 ])[_sage_const_0 ]) for i in range(d)]))}\n"
    out += " hM1 := by \n  intro i j hj\n  fin_cases i <;> interval_cases j \n"
    for i in range(len(primes_q)):
        for j in range(len(zeta_names)):
            out += f"  · erw [eq_of_DiscreteLogCertificate {prefix}.Log{i}{j}] ; decide\n"
    out += " hM2 := by \n  intro i \n  fin_cases i \n"
    for i in range(len(primes_q)):
        out += f"  · erw [eq_of_DiscreteLogCertificate {prefix}.Log{i}{len(zeta_names)}] ; decide\n"
    _M_inv = M[_sage_const_0 :len(zeta_names) + _sage_const_1 , _sage_const_0 :len(zeta_names) + _sage_const_1 ].inverse()
    _Minv = [list(_M_inv.row(i)) for i in range(len(zeta_names) + _sage_const_1 )]
    out += f" Minv := {ExList(str(_Minv))}\n"
    out += " hInv := by decide\n"
    return out

def CertificateSaturatedNDvdT(M, p, elem_names, ideal_name, exponents, phi, ideal_pows_proofs, name_unit_cert, prefix):
    """Returns a Lean saturation certificate (p does not divide torsion)."""
    name_ring = 'O'
    inv_phi = [_sage_const_0  for i in range(len(elem_names))]
    for j in range(len(phi)):
        inv_phi[phi[j]] = j
    d = len(list(M[_sage_const_0 , :])[_sage_const_0 ])
    M = Matrix(GF(p), M)
    In = ', '.join([ideal_name + str(i) for i in range(len(elem_names))])
    out = f"def NPSU{p} : pSaturatedClassGroupCertificateNDvdT {p} ![{In}] !{exponents} where \n"
    out += f" topMaximalUnitsCertificateNDvdT := {name_unit_cert}\n"
    out += f" a := ![{','.join(elem_names)}]\n"
    out += f" γ := {len(phi)}\n"
    out += " hc := by decide\n"
    out += f" ψ := !{phi}\n"
    out += f" iψ := !{inv_phi} \n"
    out += " hψ := by decide \n"
    out += " hψn := by \n  intro i \n  fin_cases i \n"
    for i in range(len(exponents)):
        if exponents[i] % p != _sage_const_0 :
            out += f"""  · convert true_imp_iff.2 ?_
    · decide
    · dsimp [{elem_names[i]}]
      refine (LinearEquiv.map_ne_zero_iff B.equivFun.symm).mpr (by decide) \n"""
        else:
            out += "  · decide\n"
    out += " h := fun i =>\n  match i with \n"
    for i in range(len(elem_names)):
        out += f"  | {i} => by convert {ideal_pows_proofs[i]}\n"
    out += f" N := {ExList(str([list(list(M[i, d - len(phi):])[_sage_const_0 ]) for i in range(d)]))}\n"
    out += f" hM2 := by \n  intro (i : Fin {d}) j\n  match i , j with \n"
    for i in range(d):
        for j in range(len(phi)):
            out += f"  | {i}, {j} => exact {prefix}.Log{i}{d - len(phi) + j}\n"
    out += " hDl := by decide \n"
    _M_inv = M.inverse()
    _NInv = [list(_M_inv.row(i)) for i in range(d)]
    out += f" NInv := {ExList(str(_NInv))}\n"
    out += " hN := by decide \n"
    return out

def CertificateSaturatedDvdT(M, p, elem_names, ideal_name, exponents, phi, ideal_pows_proofs, name_unit_cert, prefix):
    """Returns a Lean saturation certificate (p divides torsion)."""
    name_ring = 'O'
    inv_phi = [_sage_const_0  for i in range(len(elem_names))]
    for j in range(len(phi)):
        inv_phi[phi[j]] = j
    d = len(list(M[_sage_const_0 , :])[_sage_const_0 ])
    M = Matrix(GF(p), M)
    In = ', '.join([ideal_name + str(i) for i in range(len(elem_names))])
    out = f"def NPSU{p} : pSaturatedClassGroupCertificateDvdT {p} ![{In}] !{exponents} where \n"
    out += f" topMaximalUnitsCertificateDvdT := {name_unit_cert}\n"
    out += f" a := ![{','.join(elem_names)}]\n"
    out += f" γ := {len(phi)}\n"
    out += " hc := by decide\n"
    out += f" ψ := !{phi}\n"
    out += f" iψ := !{inv_phi} \n"
    out += " hψ := by decide \n"
    out += " hψn := by \n  intro i \n  fin_cases i \n"
    for i in range(len(exponents)):
        if exponents[i] % p != _sage_const_0 :
            out += f"""  · convert true_imp_iff.2 ?_
    · decide
    · dsimp [{elem_names[i]}]
      refine (LinearEquiv.map_ne_zero_iff B.equivFun.symm).mpr (by decide) \n"""
        else:
            out += "  · decide\n"
    out += " h := fun i =>\n  match i with \n"
    for i in range(len(elem_names)):
        out += f"  | {i} => by convert {ideal_pows_proofs[i]}\n"
    out += f" N := {ExList(str([list(list(M[i, d - len(phi):])[_sage_const_0 ]) for i in range(d)]))}\n"
    out += f" hM3 := by \n  intro (i : Fin {d}) j\n  match i , j with \n"
    for i in range(d):
        for j in range(len(phi)):
            out += f"  | {i}, {j} => exact {prefix}.Log{i}{d - len(phi) + j}\n"
    out += " hDl := by decide \n"
    _M_inv = M.inverse()
    _NInv = [list(_M_inv.row(i)) for i in range(d)]
    out += f" NInv := {ExList(str(_NInv))}\n"
    out += " hN := by decide \n"
    return out
def RandomPrimitiveElementQuot(K, ideal_gens, p):
    S = PolynomialRing(ZZ, names=('X',)); (X,) = S._first_ngens(1)
    O = K.ring_of_integers()
    I = K.ideal(ideal_gens)
    L = PolynomialRing(GF(p), names=('x',)); (x,) = L._first_ngens(1)
    flag = _sage_const_0 
    cont = _sage_const_0 
    while flag == _sage_const_0  and cont < _sage_const_200 :
        g = O.random_element()
        if g != _sage_const_0 :
            cont = cont + _sage_const_1 
            poly = g.minpoly()
            F = factor(L(g.minpoly()))
            for f in F:
                if p ** f[_sage_const_0 ].degree() == I.norm() and ((ZZ[X](f[_sage_const_0 ])(g)) in I):
                    flag = _sage_const_1 
                    return g, f[_sage_const_0 ]

def PrimalityCertificateComp(K, B, ideal_gens, p, ideal_name, label, name_prime_proof):
    """Returns a Lean string for the primality certificate of the ideal."""
    S = PolynomialRing(ZZ, names=('X',)); (X,) = S._first_ngens(1)
    O = K.ring_of_integers()
    I = K.ideal(ideal_gens)
    N = I.norm()
    ideal_name_full = ideal_name + str(p) + 'N' + str(label)
    gensc = [elems_to_basis([x], B).list() for x in ideal_gens]
    out = "\n"
    out += f"def {ideal_name_full} : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (" + ExList(str(gensc)) + " i)))\n"
    out += "\n"
    span_label = 'SI' + str(p) + 'N' + str(label)
    span_out, w = IdealEqSpanCertificateLeanComp(K, ideal_gens, B, span_label)
    out += span_out
    ik, jk = FindNzEntry(w)
    out += "\n"

    if N == p:
        out += f"lemma N{ideal_name_full} : Nat.card (O ⧸ {ideal_name_full}) = {N} := \n"
        out += f" ideal_norm_eq_prod' B _ _ (by decide) {ik} {jk} (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl {span_label})\n"
        out += "\n"
        out += f"lemma isPrime{ideal_name_full} : Ideal.IsPrime {ideal_name_full} := prime_ideal_of_norm_prime {name_prime_proof} _ N{ideal_name_full}\n"
    else:
        prim_elem, min_poly = RandomPrimitiveElementQuot(K, ideal_gens, p)
        a = list((elems_to_basis([prim_elem], B)).transpose()[_sage_const_0 ])
        c = list((elems_to_basis([ZZ[X](min_poly)(prim_elem)], B)).transpose()[_sage_const_0 ])
        g_coeff = Matrix(w).transpose().solve_right(vector(c))
        out += "\n"
        out += CertificateIrrModpFFP(GF(p)[X](min_poly), p, label)
        out += f"""
def P{ideal_name_full} : CertifiedPrimeIdeal' {span_label} {p} where
  n := {min_poly.degree()}
  hpos := by decide
  P := {list(min_poly)}
  hirr := P{p}P{label}
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := !{c}
  a := !{a}
  z := !{[_sage_const_1 ] + [_sage_const_0  for i in range(len(B) - _sage_const_1 )]}
  hpol := by decide
  g := {ExList(str(g_coeff.list()))}
  hcmem := by decide
  hpmem := by decide
"""
        out += "\n"
        out += f"lemma isPrime{ideal_name_full} : Ideal.IsPrime {ideal_name_full} := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl P{ideal_name_full} B_one_repr\n"
        out += f"lemma N{ideal_name_full} : Nat.card (O ⧸ {ideal_name_full}) = {N} := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table P{ideal_name_full}\n"
    return out

def PrimesBelowGens(K, p):
    set_random_seed(_sage_const_10 )
    O = K.ring_of_integers()
    F = factor(K.ideal(p))
    ideal_gens = [[[], F[i][_sage_const_1 ], _sage_const_0 ] for i in range(len(F))]
    for i in range(len(F)):
        ideal_gens[i][_sage_const_0 ] = list(F[i][_sage_const_0 ].gens_reduced(proof=False))
        if len(ideal_gens[i][_sage_const_0 ]) == _sage_const_1 :
            ideal_gens[i][_sage_const_2 ] = _sage_const_1 
    return ideal_gens

def PrimesBelowBound(K, B, M1, M2, list_exclude, primes_below_gens):
    """Generates Lean code certifying prime ideals above rational primes in [M1, M2].
    Returns a string of Lean code."""
    set_random_seed(_sage_const_10 )
    out = ""
    for p in primes(M1, M2 + _sage_const_1 ):
        F = primes_below_gens(p)
        l = len(F)
        if p not in list_exclude:
            out += f"instance hp{p} : Fact (Nat.Prime {p}) := {{out := by norm_num}}\n"

        for i in range(l):
            out += PrimalityCertificateComp(K, B, F[i][_sage_const_0 ], p, 'I', i, 'hp' + str(p) + '.out')

        ideal_gens = [F[i][_sage_const_0 ] for i in range(l)]
        exp = [F[i][_sage_const_1 ] for i in range(l)]

        sub_out, _, _ = IteratedMulLeLeanComp(K, B, ideal_gens, exp, 'I' + str(p) + 'N')
        out += sub_out

        ideal_names_list = []
        for i in range(l):
            ideal_names_list = ideal_names_list + F[i][_sage_const_1 ] * ['I' + str(p) + 'N' + str(i)]

        name_ideals_rep = "[" + ", ".join(ideal_names_list) + "]"

        out += "\n"
        out += f"def PBC{p} : ContainsPrimesAboveP {p} !{name_ideals_rep} where \n"
        out += "  Ip := by \n"
        out += "    intro i \n"
        out += "    fin_cases i \n"
        for i in range(len(ideal_names_list)):
            out += "    exact isPrime" + ideal_names_list[i] + "\n"

        if len(ideal_names_list) >= _sage_const_2 :
            C = '𝕀'
            for i in range(len(ideal_names_list) - _sage_const_1 ):
                C = C + ' ⊙ ' + f'MulI{p}N{i}'
            out += f"  hPprod := by \n"
            out += "    simp only [← Fin.prod_ofFn]\n"
            out += f"    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr {p} (by decide) ({C})\n"
        else:
            out += f"  hPprod := by \n"
            out += "    simp only [← Fin.prod_ofFn]\n"
            out += f"    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![!{[p] + [_sage_const_0  for i in range(len(B) - _sage_const_1 )]}]) timesTableT_eq_Table B_one_repr {p} (by decide) 𝕀\n"
            out += "\n"
    return out

def RelationsGeneratorInterval(K, B, M1, M2, J_ideal_gens, J_name, name_cert, generators_vec, primes_below_gens, minkowski_bound, class_group):
    """Generates Lean relation certificates for prime ideals above primes in [M1, M2].
    Returns (str, BM) where BM is the list of exponent lists."""
    s = len(J_ideal_gens)
    BM = []
    O = K.ring_of_integers()
    J_name_list = [J_name + str(i) for i in range(s)]
    J = [K.ideal(J_ideal_gens[i]) for i in range(s)]
    out = ""
    for p in primes(M1, M2 + _sage_const_1 ):
        F = primes_below_gens(p)
        l = len(F)
        BMp = []
        for cont in range(l):
            I = K.ideal(F[cont][_sage_const_0 ])
            if I.norm() < minkowski_bound:
                expon = [(class_group(I)).exponents()[i] for i in range(s)]
                BMp.append(expon)
                if expon != [_sage_const_0  for i in range(s)]:
                    set_random_seed(_sage_const_10 )
                    JJ = prod([J[i]**(expon[i]) for i in range(s)])
                    genel = (I / JJ).gens_reduced(proof=False)[_sage_const_0 ]
                    d = genel.denominator()
                    for t_p in prime_divisors(d):
                        while (d % t_p == _sage_const_0 ) and ((d // t_p) * genel in O):
                            d = d // t_p
                    x = d * genel

                    alpha = elems_to_basis([x], B).list()
                    JJ_gens_reduced = generators_vec([expon[i] for i in range(s)])
                    A = [x * i for i in JJ_gens_reduced]
                    C = ([d * i for i in F[cont][_sage_const_0 ]])
                    CC = F[cont][_sage_const_0 ]

                    Gen1 = [elems_to_basis(A, B).transpose().rows()[j].list() for j in range(len(A))]
                    Gen2 = [elems_to_basis(C, B).transpose().rows()[j].list() for j in range(len(A))]
                    before_div = [elems_to_basis(CC, B).transpose().rows()[j].list() for j in range(len(A))]
                    JJ_gens = [elems_to_basis(JJ_gens_reduced, B).transpose().rows()[j].list() for j in range(len(JJ_gens_reduced))]

                    h = [IdealLift(K, B, C, A[i]) for i in range(len(A))]
                    g = [IdealLift(K, B, A, C[i]) for i in range(len(C))]

                    gp = [[elems_to_basis(g[i], B).transpose().rows()[j].list() for j in range(len(A))] for i in range(len(g))]
                    hp = [[elems_to_basis(h[i], B).transpose().rows()[j].list() for j in range(len(C))] for i in range(len(h))]

                    if s < _sage_const_2 :
                        J_name_exp = J_name_list[_sage_const_0 ] + f' ^ {expon[_sage_const_0 ]}'
                    else:
                        J_name_exp = J_name_list[_sage_const_0 ] + f' ^ {expon[_sage_const_0 ]}'
                        for i in range(_sage_const_1 , s):
                            J_name_exp = J_name_exp + '*' + J_name_list[i] + f'^ {expon[i]}'

                    cont2 = cont

                    out += f"""

noncomputable def E{p}RS{cont} : RelationCertificate Table {d} {ExList(str(before_div))}
  !{alpha} {ExList(str(JJ_gens))} where
    su := {ExList(str(Gen2))}
    hsu := by decide
    w := {ExList(str(Gen1))}
    hw := by decide
    g := {ExList(str(gp))}
    h := {ExList(str(hp))}
    hle1 := by decide
    hle2 := by decide

lemma R{p}N{cont} : Ideal.span {{{d}}} * I{p}N{cont2} =  Ideal.span {{B.equivFun.symm !{alpha}}} * ({J_name_exp}) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl {name_cert(expon)} E{p}RS{cont} \n"""
        BM = BM + [BMp]
    return out, BM

def PrimesBelowBoundCertificteGenInterval(K, B, M, number_interval, primes_below_gens, interval_size=None):
    """Generates interval and gluing strings for the PrimesBelow certificate.
    Returns (interval_strings, gluing_string, ideals_below_interval_flatten,
             ideals_below_flag_p_interval_flatten, ideals_below_flatten, ideals_below_flag_p_flatten)."""
    import io, contextlib
    O = K.ring_of_integers()
    N = []
    Np = []
    I_names = []
    N_names = []
    for p in primes(M):
        Lp = []
        Fp = []
        I_names_p = []
        N_names_p = []
        for i in range(len(primes_below_gens(p))):
            Lp = Lp + ((primes_below_gens(p))[i][_sage_const_1 ]) * [(K.ideal((primes_below_gens(p))[i][_sage_const_0 ])).norm()]
            Fp = Fp + ((primes_below_gens(p))[i][_sage_const_1 ]) * [(primes_below_gens(p))[i][_sage_const_2 ]]
            I_names_p = I_names_p + ((primes_below_gens(p))[i][_sage_const_1 ]) * [f'I{p}N{i}']
            N_names_p = N_names_p + ((primes_below_gens(p))[i][_sage_const_1 ]) * [f'NI{p}N{i}']
        N = N + [Lp]
        Np = Np + [Fp]
        I_names = I_names + [I_names_p]
        N_names = N_names + [N_names_p]

    m = len(N)
    m1 = interval_size if interval_size is not None else ceil(m / number_interval)

    def split_intervals(l):
        L = []
        for i in range(number_interval):
            if i < number_interval - _sage_const_1 :
                L = L + [[l[j] for j in range(i * m1, (i + _sage_const_1 ) * m1)]]
            else:
                L = L + [[l[j] for j in range(i * m1, len(l))]]
        return L

    g = [len(N[i]) for i in range(m)]
    G = split_intervals(g)

    ideals_below = [[I_names[i][j] for j in range(g[i]) if N[i][j] < M] for i in range(m)]
    Ideals_below = split_intervals(ideals_below)

    ideals_below_flag_p = [[Np[i][j] for j in range(g[i]) if N[i][j] < M] for i in range(m)]
    Ideals_below_flag_p = split_intervals(ideals_below_flag_p)

    P = [p for p in primes(M)]
    PP = split_intervals(P)
    PP_aux = [[_sage_const_1 ]] + split_intervals(P)

    NN = split_intervals(N)
    NN_names = split_intervals(N_names)
    II_names = split_intervals(I_names)

    ideals_below_flatten = [I for sublist in ideals_below for I in sublist]
    ideals_below_flag_p_flatten = [I for sublist in ideals_below_flag_p for I in sublist]
    ideals_below_interval_flatten = [[I for sublist in Ideals_below[i] for I in sublist] for i in range(len(Ideals_below))]
    ideals_below_flag_p_interval_flatten = [[I for sublist in Ideals_below_flag_p[i] for I in sublist] for i in range(len(Ideals_below))]

    interval_strings = []
    e = []
    for j in range(number_interval):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            Il = PP_aux[j][-_sage_const_1 ]
            Iu = max(PP_aux[j + _sage_const_1 ][-_sage_const_1 ], (floor((j + _sage_const_1 ) / number_interval)) * (M - _sage_const_1 ))
            print('')
            print(f"""lemma PB{M}I{j}_primes (p : ℕ) :
  p ∈ Set.range !{[p for p in primes(Iu + _sage_const_1 ) if Il < p]} ↔ Nat.Prime p ∧ {Il} < p ∧ p ≤ {Iu} := by
  rw [← List.mem_ofFn']
  convert primes_range {Il} {Iu} (by omega)""")

            ideals_below_as_string = "[" + ", ".join("[" + ", ".join(sub) + "]" for sub in Ideals_below[j]) + "]"
            ideals_names_as_string = ["[" + ", ".join(sub) + "]" for sub in II_names[j]]
            e = e + [PP_aux[j][-_sage_const_1 ]]
            print('')
            print(f'''def PB{M}I{j} : PrimesBelowBoundCertificateInterval' O {PP_aux[j][-_sage_const_1 ]} {max(PP_aux[j+_sage_const_1 ][-_sage_const_1 ], (floor((j + _sage_const_1 )/number_interval))*(M-_sage_const_1 ))} {M} where
  m := {len(PP[j])}
  g := !{G[j]}
  P := !{PP[j]}
  hP := PB{M}I{j}_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i ''')
            for i in range(len(PP[j])):
                print(f'    · exact !{ideals_names_as_string[i]}')
            print(f'''  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i''')
            for i in range(len(PP[j])):
                print(f'    · exact PBC{PP[j][i]}')
            print(f'''  N := fun i => by
    cases i
    rename_i i h
    interval_cases i''')
            for i in range(len(PP[j])):
                print(f'    · exact !{NN[j][i]}')
            print(f'''  hNz := by decide''')
            print(f'''  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i ''')
            for i in range(len(PP[j])):
                print('''    · dsimp ; intro j
      fin_cases j''')
                for k in range(G[j][i]):
                    print(f'      exact {NN_names[j][i][k]}')
            print(f'  Il := !{ideals_below_as_string}')
            print('''  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl''')
        interval_strings.append(buf.getvalue())

    glue_buf = io.StringIO()
    with contextlib.redirect_stdout(glue_buf):
        print('')
        print(f'''def PB{M} : PrimesBelowBoundCertificate' O {M} := by
  refine primesBelowBoundCertificate_of_Interval' O !{e + [M - _sage_const_1 ]} {M - _sage_const_1 } rfl rfl ?_ ?_
  · decide
  · rintro ⟨i,hi⟩
    interval_cases i ''')
        for i in range(number_interval):
            print(f'    exact PB{M}I{i}')
    gluing_string = glue_buf.getvalue()

    return interval_strings, gluing_string, ideals_below_interval_flatten, ideals_below_flag_p_interval_flatten, ideals_below_flatten, ideals_below_flag_p_flatten
def LeanProof(T, basis, nameIrr, num, comment, flagD):
    """Builds the Lean proof file for the ring of integers of the number field defined by T.
    Returns (str, bad, flagl, flaglW, flagD)."""
    d = T.degree()
    T_lean = str(T).replace('x', 'X')
    C, denom = BasisToMatrix(basis)

    out = f"""
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF{num}.{nameIrr}"""
    if flagD == _sage_const_1 :
        out += "\nimport IdealArithmetic.DedekindProject.Discriminant"
    out += f"""

{comment}

open Polynomial Module

noncomputable def T : ℤ[X] := {T_lean}
lemma T_def : T = {T_lean} := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => {T.list()}

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
"""
    out += f"-- We build the subalgebra with integral basis {basis} \n\n"

    sub_out, Table, auxTemp = SubalgebraBuilderF(T, C, denom)
    out += sub_out

    out += f"""
lemma T_degree : T.natDegree = {T.degree()} := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B' : Basis (Fin {T.degree()}) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin {T.degree()}) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ

noncomputable def B : Basis (Fin {T.degree()}) ℤ O := timesTableO.basis
"""
    strTa = ""
    out += f"def Table : Fin {T.degree()} → Fin {T.degree()} → List ℤ := \n !["
    for i in range(d):
        if i != d - _sage_const_1 :
            strTa = strTa + ' !' + str(Table[i]) + ', \n'
        else:
            strTa = strTa + ' !' + str(Table[i])
    out += strTa + "]\n"

    out += f"""
lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ !{auxTemp.list()} [] (by decide)
"""
    ded_out, bad = CertificateDedekindF(T)
    out += ded_out

    flagl = []
    flaglW = []
    for p in bad:
        pmax_out, flagp, flagW = CertificatePMaximalityF(T, C, denom, p, Table)
        out += pmax_out
        flagl = flagl + [(p, flagp)]
        flaglW = flaglW + [(p, flagW)]
    flagl = dict(flagl)
    flaglW = dict(flaglW)

    straux = ''
    for i in range(d - _sage_const_1 ):
        if i == _sage_const_0 :
            straux = straux + '0'
        else:
            straux = straux + ',0'

    out += f"""
open BigOperators Classical Matrix Polynomial

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm !{[_sage_const_1 ] + [_sage_const_0  for i in range(d - _sage_const_1 )]} = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr

lemma B_int_repr {{n : ℤ}} : B.equivFun.symm ![n, {straux}] = n := by
  suffices B.equivFun.symm ![n, {straux}] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
  rw [← B_one_repr, ← LinearEquiv.map_smul]
  simp only [Basis.equivFun_symm_apply, zsmul_eq_mul, Matrix.smul_cons, smul_eq_mul, mul_one,
    mul_zero, Matrix.smul_empty]

instance : IsDomain O := by
  haveI hirr : Fact $ Irreducible (map (algebraMap ℤ ℚ) T) :=
  {{out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible}}
  letI hola : Field K := by
    unfold K
    exact AdjoinRoot.instField
  haveI : IsDomain K := by infer_instance
  refine Subalgebra.isDomain O

 noncomputable instance : Mul (Ideal ↥O) := Submodule.mul (R := O) (A := O)
 noncomputable instance  : AddCommMonoid ↥O := AddSubmonoidClass.toAddCommMonoid O
 noncomputable instance : Module ℤ O := O.instModuleSubtypeMem
 noncomputable instance  : Algebra ℤ O := O.algebra'

"""
    return out, bad, flagl, flaglW, flagD

def SaturatedCertLean(K, B, num, Ql, pr, elems, names, prefix):
    """Builds the Lean saturation certificate file for prime pr.
    Returns a string of Lean code."""
    out = f"""import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF{num}.RI{num}

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace {prefix} \n"""

    sub_out, L, M_mat = DiscreteLogListLean(K, B, Ql, 'I', pr, elems, names)
    out += sub_out
    out += f"end {prefix}\n"
    return out

def CertNames(l):
    L = ['' for i in range(len(l))]
    for i in range(len(l)):
        if l[i] == _sage_const_0 :
            L[i] = 'dummy'
        elif l[i] == _sage_const_1 :
            L[i] = 'rfl'
        else:
            L[i] = 'MulJ' + str(i) + str(l[i] - _sage_const_2 )
    return L

def ClassGroupDataLean(K, B, num, J, ideal_gens, J_name, x, t, u):
    """Builds ClassGroupData Lean file content.
    Returns (str, giL, MAux)."""
    out = f"""import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF{num}.RI{num}

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

"""
    names_alpha = [f'alpha{i}' for i in range(len(x))]
    names_unit = ['v'] + [f'zeta{i + _sage_const_1 }' for i in range(len(u) - _sage_const_1 )]

    flagpdvd = _sage_const_0 
    if gcd(u[_sage_const_0 ].multiplicative_order(), prod(t)) != _sage_const_1 :
        flagpdvd = _sage_const_1 

    for i in range(len(names_alpha)):
        out += f'def {names_alpha[i]} := B.equivFun.symm ' + ExList(str(elems_to_basis([x[i]], B).list())) + '\n\n'

    for i in range(len(names_unit)):
        out += f'def {names_unit[i]} := B.equivFun.symm ' + ExList(str(elems_to_basis([u[i]], B).list())) + '\n\n'

    giL = []
    for j in range(len(J)):
        pow_out, ig = IdealPowLean(K, B, J_name + str(j) + '_pow' + str(t[j]), ideal_gens[j],
                                   J_name + str(j), x[j], 'alpha' + str(j), t[j])
        out += pow_out
        giL = giL + [ig]

    out += IsUnitInvLean(B, u[_sage_const_1 :], names_unit[_sage_const_1 :])

    if flagpdvd == _sage_const_1 :
        torsion_out, order_v = TorsionUnitProof(K, B, u[_sage_const_0 ], names_unit[_sage_const_0 ])
        out += torsion_out

    MAux = {}
    for idx in itertools.product(*[range(n) for n in t]):
        if sum(idx) != _sage_const_0 :
            mul_out, ideal_gens_accum = IteratedMulLeanWithCert(K, B, ideal_gens, list(idx),
                                                                 CertNames(list(idx)), 'J', giL)
            out += mul_out
            MAux[idx] = ideal_gens_accum

    return out, giL, MAux

def ClassGroupOrderProofSplit(I, F_flags, BM, name_primes_cert, bound, J_names, group_str,
                               names_sat_cert, interval_size=None):
    """Builds the class group order proof section of the Invariants file.
    Returns str."""
    out = ""
    number_interval = len(I)

    def split_by_sizes(L, sizes):
        result = []
        idx = _sage_const_0 
        for size in sizes:
            result.append(L[idx:idx + size])
            idx += size
        return result

    Idedup = [[] for i in range(number_interval)]
    Fdedup = [[] for i in range(number_interval)]

    for i in range(number_interval):
        for j in range(len(I[i])):
            if I[i][j] not in Idedup[i]:
                Idedup[i].append(I[i][j])
                Fdedup[i].append(F_flags[i][j])

    e = [len(Idedup[i]) for i in range(number_interval)]
    m = len(prime_range(bound))
    m1 = interval_size if interval_size is not None else ceil(m / number_interval)
    s = [m1 for i in range(number_interval - _sage_const_1 )] + [m - (number_interval - _sage_const_1 ) * m1]

    n = sum(e)

    I_dedup_string = ["[" + ", ".join(Idedup[i]) + "]" for i in range(number_interval)]
    I_string = ["[" + ", ".join(I[i]) + "]" for i in range(number_interval)]

    fac_grp = factor(prod(group_str))
    prime_list = [fac_grp[i][_sage_const_0 ] for i in range(len(fac_grp))]
    exp_list = [fac_grp[i][_sage_const_1 ] for i in range(len(fac_grp))]

    BMM = split_by_sizes(BM, e)

    if number_interval > _sage_const_0 :
        out += f'def e := !{e}\n'
        out += f'def s := !{s}\n\n'
    else:
        # No primes below the Minkowski bound: the interval lists are empty, so
        # the empty matrix literals need explicit types for Lean to elaborate.
        out += 'def e : Fin 0 → ℕ := ![]\n'
        out += 'def s : Fin 0 → ℕ := ![]\n\n'

    out += f'def g : (i : Fin {number_interval}) → Fin (e i) → Ideal O := by \n'
    out += f'  rintro ⟨i, hi⟩ \n  interval_cases i \n'
    for i in range(number_interval):
        out += '  exact !' + I_dedup_string[i] + '\n'
    out += '\n'

    out += f'def BM : (i : Fin {number_interval}) → Fin (e i) → (Fin {len(J_names)} → ℕ) := by \n'
    out += f'  rintro ⟨i, hi⟩ \n  interval_cases i \n'
    for i in range(number_interval):
        out += '  exact ' + ExList(str(BMM[i])) + '\n'
    out += '\n'

    for i in range(number_interval):
        out += f"""lemma primesGenerationAux{i}  {{y}} :
    y ∈ (List.ofFn (fun (x : Fin (s {i})) => {name_primes_cert}.Il ((indexPair_inv s) ⟨{i},x⟩))).flatten ↔ y ∈ List.ofFn (g {i}) := by
  erw [ primesBelowBoundCertificate_of_Interval_Il_apply' _ (by decide)]
  show y ∈ {I_string[i]} ↔ y ∈ {I_dedup_string[i]}
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self, or_self_left]

"""

    out += f'lemma primesGenerationAux {{x}} : x ∈ (List.ofFn {name_primes_cert}.Il).flatten ↔ x ∈ List.ofFn (Fin.addCasesIter e g) := by\n'
    out += f'  refine (list_flatten_eq_list_addCasesIter g (s := s) {name_primes_cert}.Il ?_ x)\n'
    out += f'  rintro ⟨i, hi⟩ x\n  interval_cases i \n'
    for i in range(number_interval):
        out += f'  · exact primesGenerationAux{i}\n'
    out += '\n'

    out += f"""lemma primesGenerationBelow : {{I : Ideal O | 0 < I.absNorm ∧ I.IsPrime ∧ I.absNorm < {bound}}} ⊆ Set.range (Fin.addCasesIter e g) :=
  le_primes_below_bound_of_PrimesBelowBoundCertificate_le' (Subalgebra.equivOfEq _ _ O_integral_closure).toRingEquiv ((Fin.addCasesIter e g)) {name_primes_cert} (fun _ hx => primesGenerationAux.1 hx)

def g' : Fin {n} → nonZeroDivisors (Ideal O) := by
  intro i
  have : (Fin.addCasesIter e g) i ∈ (List.ofFn {name_primes_cert}.Il).flatten := by
    simp only [primesGenerationAux, List.mem_ofFn, exists_apply_eq_apply]
  exact Ideal.toNonZeroDivisorOfNeZero ((Fin.addCasesIter e g) i)
    (fun hc => ((zero_ne_mem_of_PrimesBelowCertificate' _ {name_primes_cert}) (hc ▸ this) ))

def x : Fin {len(J_names)} → Ideal O := ![{','.join(J_names)}]

def x' :  Fin {len(J_names)} → nonZeroDivisors (Ideal O) := by
  refine fun i => Ideal.toNonZeroDivisorOfNeZero (x i) (?_ )
  unfold x
"""

    if names_sat_cert != []:
        out += f"""  rw [← Submodule.zero_eq_bot, ← pow_ne_zero_iff (n := !{group_str} i) (by fin_cases i <;> decide) , {names_sat_cert[_sage_const_0 ][_sage_const_0 ]}.h]
  simp only [ Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot, {names_sat_cert[_sage_const_0 ][_sage_const_0 ]}]
  fin_cases i
"""
        for i in range(len(group_str)):
            out += f'  · dsimp [alpha{i}] ; rw [(LinearEquiv.map_eq_zero_iff B.equivFun.symm)] ; decide \n'
    else:
        out += '  simp \n'

    out += f"""
lemma g'_apply : ∀ (i : Fin {n}), ↑(g' i) = (Fin.addCasesIter e g) i := by
  intro i
  rfl

lemma x'_apply : ∀ (i : Fin {len(J_names)}), ↑(x' i) = x i := by
  intro i
  rfl

"""

    for i in range(number_interval):
        out += f"""lemma relations_proof{i} (i : Fin {e[i]}) : IsInClass O x (g {i} i) (BM {i} i) := by
  show IsInClass O x (g {i} i) ({ExList(str(BMM[i]))} i)
  unfold IsInClass
  simp only [Fin.isValue, Fin.prod_univ_castSucc, Finset.univ_eq_empty, Finset.prod_empty, Fin.succ_zero_eq_one, one_mul]
  dsimp
  fin_cases i
"""
        for j in range(e[i]):
            if Fdedup[i][j] != _sage_const_1 :
                out += f"""  · refine Exists.intro _ (Exists.intro ?_ (Exists.intro (?_) (Exists.intro ?_ (by convert R{(Idedup[i][j])[_sage_const_1 :]}))))
    refine Nat.cast_ne_zero.2 (by decide)
    exact (LinearEquiv.map_ne_zero_iff B.equivFun.symm).mpr (by decide)
"""
            else:
                out += """  · simp only [Fin.isValue, Fin.reduceFinMk, Nat.succ_eq_add_one, Nat.reduceAdd, cons_val',
    cons_val_zero, cons_val_fin_one, cons_val, cons_val_one, pow_zero, mul_one]
    exact ideal_mem_principal_class'' B _ _ (by decide) rfl
"""
        out += '\n'

    out += f"""theorem class_group_generator : Subgroup.closure (Set.range (fun i => ClassGroup.mk0 (x' i))) = ⊤ := by
  refine subgroup_closure_eq_classGroup'' (Subalgebra.equivOfEq _ _ O_integral_closure).toRingEquiv
      g'_apply x'_apply ?_ primesGenerationBelow (Fin.addCasesIter e BM) ?_
  · refine lt_of_le_of_lt K_minowski ?_
    norm_num
  · refine forall_addCasesIter_prop g BM (IsInClass O x) ?_
    rintro ⟨i, hi⟩
    interval_cases i
"""
    for i in range(number_interval):
        out += f'    · exact relations_proof{i}\n'
    out += '\n'

    out += f"""def ClassGroupO_equiv : (∀ i : Fin {len(group_str)} , (ZMod (!{group_str} i))) ≃+ Additive (ClassGroup O) := by
  haveI : ∀ (i : Fin {len(group_str)}), NeZero (!{group_str} i) := by
    intro i
    fin_cases i <;>  exact {{out := by decide}}
"""

    if names_sat_cert != []:
        out += f"""  refine ClassGroup_equiv_of_pSaturatedCertificate x'_apply {names_sat_cert[_sage_const_0 ][_sage_const_0 ]}.h class_group_generator ?_
  rintro ⟨p, hp1, hp2⟩
  have : ∏ i, !{group_str} i = ∏ i, (!{prime_list} i) ^ (!{exp_list} i)  := by decide
  rw [this] at hp2
  have hp_cases : p ∈ {prime_list} := by
    obtain ⟨j ,hj1, hj2⟩  := Prime.exists_mem_finset_dvd (Nat.prime_iff.mp hp1) hp2
    show p ∈ List.ofFn !{prime_list}
    rw [(Nat.prime_dvd_prime_iff_eq hp1 ?_).1 (Nat.Prime.dvd_of_dvd_pow hp1 hj2), List.mem_ofFn]
    exact ⟨j, rfl⟩
    fin_cases j <;> decide
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp_cases
"""
        for i in range(len(prime_list)):
            lr = 'right' if names_sat_cert[i][_sage_const_1 ] == _sage_const_0  else 'left'
            out += f'  by_cases h : p = {prime_list[i]}\n'
            out += f'  simp_rw [h] ; {lr}\n'
            out += f'  exact {names_sat_cert[i][_sage_const_0 ]}\n'
        out += '  omega\n'
    else:
        out += f"""  refine ClassGroup_equiv_of_pSaturatedCertificate x'_apply (a := ![1]) (n := ![1])
    (by simp [x]; exact Eq.symm Ideal.span_singleton_one) class_group_generator ?_
  rintro ⟨p, hp1, hp2⟩
  simp at hp2
  exact (Nat.Prime.ne_one hp1 hp2).elim
"""

    out += f"""
def class_group_equiv : (∀ i : Fin {len(group_str)} , (ZMod (!{group_str} i))) ≃+ Additive (ClassGroup (NumberField.RingOfIntegers K)) := by
 refine AddEquiv.trans ClassGroupO_equiv ?_
 exact MulEquiv.toAdditive (ClassGroup.congr
    ((Subalgebra.equivOfEq _ _ O_integral_closure).toRingEquiv))

theorem class_number_K_eq_{prod(group_str)} : NumberField.classNumber K = {prod(group_str)} := by
  unfold NumberField.classNumber
  rw [Fintype.card_eq_nat_card, ← Nat.card_congr (Additive.toMul),
    Nat.card_congr (class_group_equiv).symm.toEquiv, Nat.card_pi]
  simp [Fin.isValue, Fin.prod_succ]
  try decide
"""
    return out

def build_invariants_content(T, K, B, num, bad, flagl, flaglW, flagD,
                              t_orders, ideal_gens, u, primesCN, local_data_sat,
                              NF, listIint, listPint, BM, D, num_gens, NI):
    """Builds the full Invariants{num}.lean file content. Returns str."""
    out = ""
    T_lean = str(T).replace('x', 'X')
    d = K.degree()
    M = K.minkowski_bound()
    bound = floor(M + _sage_const_0p01 ) + _sage_const_1 

    # Imports
    for pr in primesCN:
        out += f'import IdealArithmetic.Examples.NF{num}.ClassGroupSaturated{num}_{pr}\n'
    if primesCN == []:
        out += 'import IdealArithmetic.Saturation.PrincipalityCertificate\n'
    if num_gens > _sage_const_0 :
        for i in range(NF):
            out += f'import IdealArithmetic.Examples.NF{num}.RelationIdeals{num}F{i}\n'
    out += f"""import IdealArithmetic.Examples.NF{num}.PrimesBelowCert{num}
import Mathlib.NumberTheory.NumberField.ClassNumber
import IdealArithmetic.Signature.ResultantRecursive
import IdealArithmetic.DedekindProject.Discriminant
import IdealArithmetic.Generation.ClassGroupGeneration

set_option linter.all false

/- Number field `K(α)` with α root of polynomial `{T_lean}`.
Class group structure `{t_orders}`, generated by class of ideals `{ideal_gens}`. -/

/- Ring of integers with basis `{B}` -/

open BigOperators Classical Matrix Polynomial Module

noncomputable section

instance hirr : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

instance K_field : Field K := by
  unfold K
  exact AdjoinRoot.instField

instance K_numberField : NumberField K := by
  unfold K
  exact AdjoinRoot.instNumberFieldRat

instance : Module ℚ K := Algebra.toModule
instance : @Algebra ℤ K CommRing.toCommSemiring CommRing.toCommSemiring.toSemiring := Ring.toIntAlgebra K
instance : @CharZero K CommRing.toCommSemiring.toNonAssocSemiring.toAddCommMonoidWithOne.toAddMonoidWithOne := charZero_of_expChar_one' K

lemma K_finrank : Module.finrank ℚ K = {d} := by
  unfold K
  erw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux _), Polynomial.natDegree_map_eq_of_injective, T_degree]
  · simp
  · exact RingHom.injective_int (algebraMap ℤ ℚ)
  · exact Irreducible.ne_zero hirr.out

theorem O_integral_closure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ {bad}
  · fin_cases hc
"""
    for p in bad:
        if flagl[p] == _sage_const_0 :
            if flaglW[p] == _sage_const_1 :
                out += f'    exact @pMaximal_of_MaximalOrderCertificateWLists K {p} _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M{p}\n'
            else:
                out += f'    exact @pMaximal_of_MaximalOrderCertificateLists K {p} _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M{p}\n'
        else:
            out += f'    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K {p} _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M{p}\n'

    out += f"""  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T _ T_ofList {bad} D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_integral_closure] ; rfl

instance : Module.Finite ℤ (Additive ((↥O)ˣ ⧸ CommGroup.torsion (↥O)ˣ)) := by
  rw [O_integral_closure]
  exact NumberField.Units.instFiniteIntAdditiveQuotientUnitsRingOfIntegersSubgroupTorsion K

instance : Module.Free ℤ (Additive ((↥O)ˣ ⧸ CommGroup.torsion (↥O)ˣ)) := by
  rw [O_integral_closure]
  exact NumberField.Units.instFreeIntAdditiveQuotientUnitsRingOfIntegersSubgroupTorsion K

instance :  Fintype ↥(CommGroup.torsion (↥O)ˣ) := by
  rw [O_integral_closure]
  exact NumberField.Units.instFintypeSubtypeUnitsRingOfIntegersMemSubgroupTorsion K

instance : IsCyclic ↥(CommGroup.torsion (↥O)ˣ) := by
  rw [O_integral_closure]
  exact NumberField.Units.instIsCyclicSubtypeUnitsRingOfIntegersMemSubgroupTorsion K

instance DD' : IsDedekindDomain O  := by
  rw [O_integral_closure]
  exact integralClosure.isDedekindDomain ℤ ℚ K

instance : Module.Free ℤ ↥O := Module.Free.of_basis B

instance  : IdemCommSemiring (Ideal O) := Ideal.instIdemCommSemiring
instance : CharZero O := SubsemiringClass.instCharZero O

"""

    T_QQ = T.change_ring(QQ)
    out += RankUnitCertificateLean(T_QQ, 'T_ofList', 'Adj', 'O_integral_closure', 'RC')
    out += '\n'

    for i in range(len(primesCN)):
        pr = primesCN[i]
        A, phi, Qlq, names, flag = local_data_sat[i][_sage_const_0 ], local_data_sat[i][_sage_const_1 ], local_data_sat[i][_sage_const_2 ], local_data_sat[i][_sage_const_3 ], local_data_sat[i][_sage_const_4 ]
        alpha_names = [f'alpha{k}' for k in range(len(t_orders))]
        pow_names = ['J' + str(k) + '_pow' + str(t_orders[k]) for k in range(len(t_orders))]
        if flag == _sage_const_1 :
            out += CertificateMaximalUnitsDvdT(A, pr, names[:-len(phi)-_sage_const_1 ], 'v',
                                               u[_sage_const_0 ].multiplicative_order(),
                                               f'Sat{pr}', 'I', Qlq, 'RC')
            out += '\n'
            out += CertificateSaturatedDvdT(A, pr, alpha_names, 'J', t_orders, phi,
                                            pow_names, f'NPCU{pr}', f'Sat{pr}')
        else:
            out += pNeDvdTorsionLean(K, B, 'K_finrank', 'O_integral_closure', 'IC', pr)
            out += '\n'
            out += CertificateMaximalUnitsNDvdT(A, pr, names[:-len(phi)],
                                                f'Sat{pr}', 'I', Qlq, 'RC')
            out += '\n'
            out += CertificateSaturatedNDvdT(A, pr, alpha_names, 'J', t_orders, phi,
                                             pow_names, f'NPCU{pr}', f'Sat{pr}')

    if flagD == _sage_const_1 :
        Dabs = abs(D)
        sqrt_Dabs = float(sqrt(Dabs))
        sqrt_Dabs_rounded = round(sqrt_Dabs, _sage_const_6 ) + _sage_const_0p00001 
        fac_coeff = float(factorial(d)) / float(d ** d)
        minkowski_upper = round(fac_coeff * sqrt_Dabs_rounded + _sage_const_0p01 , _sage_const_6 )
        out += f"""
lemma T_discr : T.discr = {T.discriminant()} :=  by
  convert discriminant_eq_DiscriminantOfPRemainder_of_SturmBuilderOfList SturmRC
  rw [T_ofList]

theorem K_discr : NumberField.discr K = {D} := by
  rw [discr_numberField_eq_discrSubalgebraBuilder T_irreducible BQ O_integral_closure]
  rw [T_discr]
  rfl

lemma K_nrComplexPlaces : NumberField.InfinitePlace.nrComplexPlaces K = {K.signature()[_sage_const_1 ]} := by
  rw [nrComplexPlaces_of_RankUnitsCertificate RC]
  rfl

theorem K_minowski : MinkowskiBound K ≤ ({float(M + _sage_const_0p01 )} : ℝ) := by
  refine K_minkowski_decimal _ ?_
  erw [K_nrComplexPlaces, K_discr, K_finrank]
  have hraux: √{Dabs} ≤ {sqrt_Dabs_rounded} := by
      refine Real.sqrt_le_iff.mpr ?_
      norm_num
  have : {fac_coeff} * √{Dabs} ≤ {minkowski_upper} := by
    refine le_trans (mul_le_mul_of_nonneg (by rfl) hraux (by norm_num) (by norm_num)) ?_
    norm_num
  norm_num
  try {{linarith}}

"""

    # Adjust t and BM for trivial class group
    if t_orders == []:
        t_final = [_sage_const_1 ]
        BM_final = [BM[i] + [_sage_const_0 ] for i in range(len(BM))]
        J_names = ['⊤']
    else:
        t_final = t_orders
        BM_final = BM
        J_names = [f'J{i}' for i in range(len(t_final))]

    names_sat_cert = [[f'NPSU{pr}', _sage_const_1  if u[_sage_const_0 ].multiplicative_order() % pr == _sage_const_0  else _sage_const_0 ]
                      for pr in primesCN]

    if NF > _sage_const_100 :
        out += "set_option maxRecDepth 20000\n\n"
    out += ClassGroupOrderProofSplit(
        listIint, listPint, BM_final,
        f'PB{bound}', bound,
        J_names, t_final, names_sat_cert, NI
    )

    return out

def generate_class_group_lean(T, B_polys, num, output_dir=None):
    """Generate all Lean files for the class group certificate.

    T       : irreducible polynomial in ZZ['x']
    B_polys : list of elements of NumberField(T, 'a') forming the integral basis
    num     : label string for the output directory and file names
    output_dir : parent directory for ``NF<num>``; defaults to the current directory
    """
    K = None
    if len(B_polys) > _sage_const_1  and hasattr(B_polys[_sage_const_1 ], 'parent'):
        parent0 = B_polys[_sage_const_1 ].parent()
        if hasattr(parent0, 'number_field'):
            # parent0 is an order (e.g. from K.maximal_order().basis()); recover the field.
            K = parent0.number_field()
        elif isinstance(parent0, NumberField_base):
            K = parent0
    if K is None:
        K = NumberField(T, 'a')
    B = B_polys
    T_lean = str(T).replace('x', 'X')

    folder = os.path.join(output_dir or os.curdir, f"NF{num}")
    os.makedirs(folder, exist_ok=True)

    # 1. Irreducible{num}.lean
    irr_str = LeanProofIrreducible(T)
    with open(f"{folder}/Irreducible{num}.lean", "w") as f:
        f.write(irr_str)

    # 2. RI{num}.lean (ring of integers)
    ri_str, bad, flagl, flaglW, flagD = LeanProof(T, B, f'Irreducible{num}', num, '', _sage_const_1 )
    with open(f"{folder}/RI{num}.lean", "w") as f:
        f.write(ri_str)

    # 3. Global numeric data
    disc_factors = [factor(T.discriminant())[i][_sage_const_0 ]
                    for i in range(len(factor(T.discriminant())))]
    M = K.minkowski_bound()
    bound = floor(M + _sage_const_0p01 ) + _sage_const_1 
    PP = list(primes(bound))
    m = len(PP)
    NI = ceil(_sage_const_20  / harmonic_number(K.degree()))
    NF = ceil(m / NI)
    D = K.discriminant()

    # Precompute PrimesBelowGens for all primes up to bound
    pbg_list = [_sage_const_0 ] * (bound + _sage_const_1 )
    for p in PP:
        pbg_list[p] = PrimesBelowGens(K, p)

    def primes_below_gens(p):
        return pbg_list[p]

    # 4. PrimesBelow{num}F{i}.lean + PrimesBelowCert{num}.lean
    interval_strings, gluing_string, listIint, listPint, listI, listP =         PrimesBelowBoundCertificteGenInterval(K, B, bound, NF, primes_below_gens, NI)

    for i in range(NF):
        lo = PP[i * NI]
        hi = PP[min((i + _sage_const_1 ) * NI - _sage_const_1 , m - _sage_const_1 )]
        header = f"""
import IdealArithmetic.Examples.NF{num}.RI{num}
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve2

set_option linter.all false

open Classical Polynomial

noncomputable section """
        pb_str = PrimesBelowBound(K, B, lo, hi, disc_factors, primes_below_gens)
        with open(f"{folder}/PrimesBelow{num}F{i}.lean", "w") as f:
            f.write(header + pb_str + "\n" + interval_strings[i])

    if NF > _sage_const_0 :
        cert_header = "".join(
            f"import IdealArithmetic.Examples.NF{num}.PrimesBelow{num}F{i}\n"
            for i in range(NF)
        )
    else:
        # No primes below the Minkowski bound: there are no PrimesBelow files to
        # supply the base modules transitively, so import them directly.
        cert_header = (
            f"import IdealArithmetic.Examples.NF{num}.RI{num}\n"
            "import IdealArithmetic.Generation.ClassGroupGeneration\n"
            "import IdealArithmetic.IdealArithmetic\n"
            "import IdealArithmetic.Computation.PrimeSieve2\n"
            "\nopen Classical Polynomial\n"
        )
    cert_header += "\nnoncomputable section"
    if NF > _sage_const_100 :
        cert_header += "\nset_option maxRecDepth 20000"
    with open(f"{folder}/PrimesBelowCert{num}.lean", "w") as f:
        f.write(cert_header + gluing_string)

    # 5. Class group data
    # Computed with proof=False (i.e. assuming GRH) rather than under Sage's default
    # provably-correct mode, which can be orders of magnitude slower.
    O = K.ring_of_integers()
    Cl = K.class_group(proof=False)
    num_gens = len(list(Cl.gens()))
    ideal_gens = [Cl.gens()[i].ideal().gens_reduced(proof=False) for i in range(num_gens)]
    J = [K.ideal(ideal_gens[i]) for i in range(num_gens)]
    t_orders = [Cl(J[i]).order() for i in range(num_gens)]
    # x[i] must be the exact value IdealPowLean will independently recompute for
    # J[i]^t_orders[i] (see IdealPowerGenerator) -- not an independently
    # gens_reduced() ideal power, which can land on a different associate.
    x = [IdealPowerGenerator(K, B, ideal_gens[i], t_orders[i])[_sage_const_0 ] for i in range(num_gens)]
    u = [K(g) for g in K.unit_group(proof=False).gens()]
    primesCN = [factor(prod(t_orders))[i][_sage_const_0 ]
                for i in range(len(factor(prod(t_orders))))] if t_orders else []

    # 6. ClassGroupData{num}.lean
    set_random_seed(_sage_const_10 )
    cg_str, giL, MAux = ClassGroupDataLean(K, B, num, J, ideal_gens, 'J', x, t_orders, u)
    with open(f"{folder}/ClassGroupData{num}.lean", "w") as f:
        f.write(cg_str)

    # 7. ClassGroupSaturated{num}_{pr}.lean for each prime
    local_data_sat = []
    for pr in primesCN:
        # MatrixPrimesG needs enough auxiliary primes q = 1 (mod pr) below its
        # search bound to reach full rank; it returns 0 when the bound is too
        # small (e.g. pr = 47 admits a single q < 400), so retry with more room.
        res = _sage_const_0
        aux_bound = _sage_const_400
        while res == _sage_const_0 and aux_bound <= 400000:
            res = MatrixPrimesG(K, O, pr, x, t_orders, aux_bound)
            aux_bound *= _sage_const_10
        if res == _sage_const_0 :
            raise RuntimeError(
                f"MatrixPrimesG found no rank-complete set of auxiliary primes"
                f" below {aux_bound // _sage_const_10 } for p={pr}")
        phi, A, Q, elems, flag = res
        elems = [K(r) for r in elems]
        Ql = [list(Q[j].gens()) for j in range(len(Q))]
        Qlq = [Ql[j][_sage_const_0 ] for j in range(len(Ql))]
        if flag == _sage_const_0 :
            names = [f'zeta{j + _sage_const_1 }' for j in range(len(elems) - len(phi))] +                     [f'alpha{phi[j]}' for j in range(len(phi))]
        else:
            names = [f'zeta{j + _sage_const_1 }' for j in range(len(elems) - len(phi) - _sage_const_1 )] +                     ['v'] + [f'alpha{phi[j]}' for j in range(len(phi))]
        local_data_sat.append([A, phi, Qlq, names, flag])

        set_random_seed(_sage_const_10 )
        sat_import = f"import IdealArithmetic.Examples.NF{num}.ClassGroupData{num}\n"
        sat_body = SaturatedCertLean(K, B, num, Ql, pr, elems, names, f'Sat{pr}')
        with open(f"{folder}/ClassGroupSaturated{num}_{pr}.lean", "w") as f:
            f.write(sat_import + sat_body)

    # 8. RelationIdeals{num}F{i}.lean
    def name_cert_alt(l):
        if l == [_sage_const_0 ] * len(l):
            return 'rfl'
        return 'Pow' + ''.join(f'J{i}_{l[i]}' for i in range(len(l)))

    def generators_vec(l):
        return MAux[tuple(l)]

    BMf = []
    set_random_seed(_sage_const_10 )
    for i in range(NF):
        lo = PP[i * NI]
        hi = PP[min((i + _sage_const_1 ) * NI - _sage_const_1 , m - _sage_const_1 )]
        rel_out, BMp = RelationsGeneratorInterval(
            K, B, lo, hi, ideal_gens, 'J',
            name_cert_alt, generators_vec, primes_below_gens,
            bound, Cl
        )
        if num_gens > _sage_const_0 :
            rel_header = f"""import IdealArithmetic.Examples.NF{num}.PrimesBelow{num}F{i}
import IdealArithmetic.Examples.NF{num}.ClassGroupData{num}

set_option linter.all false

noncomputable section
"""
            with open(f"{folder}/RelationIdeals{num}F{i}.lean", "w") as f:
                f.write(rel_header + rel_out)
        BMf += BMp

    BM = [e for sublist in BMf for e in sublist]

    # 9. Invariants{num}.lean
    inv_str = build_invariants_content(
        T, K, B, num, bad, flagl, flaglW, flagD,
        t_orders, ideal_gens, u, primesCN, local_data_sat,
        NF, listIint, listPint, BM, D, num_gens, NI
    )
    with open(f"{folder}/Invariants{num}.lean", "w") as f:
        f.write(inv_str)

    # 10. Results{num}.lean
    t_final = [_sage_const_1 ] if t_orders == [] else t_orders
    results_str = f"""import IdealArithmetic.Examples.NF{num}.Invariants{num}

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `{T_lean}`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) ({T_lean})) := rfl

lemma T_irreducible' : Irreducible ({T_lean} : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'
"""
    if flagD == _sage_const_1 :
        results_str += f"""
theorem K_discr' : discr K = {D} := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = {K.signature()[_sage_const_1 ]} := K_nrComplexPlaces
"""
    results_str += f"""
def class_group_equiv' :
  (∀ i : Fin {len(t_final)} , (ZMod (!{t_final} i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_{prod(t_final)}' : classNumber K = {prod(t_final)} := class_number_K_eq_{prod(t_final)}
"""
    with open(f"{folder}/Results{num}.lean", "w") as f:
        f.write(results_str)

    print(f"Generated Lean files in {folder}/")
