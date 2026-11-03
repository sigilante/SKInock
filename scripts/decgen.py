"""decgen.py J.dag NOUN: print `dag ...` for J applied to encNoun(NOUN), skinock's encoding
(Nock2Ski/Noun.lean): atomT b = S (K K) (S (K K) (S (K K) (S I (K b)))); cellT h t =
K (S (K K) (S (K K) (pairT h t))); formT h t k = K (K (S (K K) (S (pairT h t) (K k))));
pairT a b = S (S I (K a)) (K b); bits LSB first, nil K, cons K (pairT bit rest), T = K, F = K I.
NOUN is Python syntax: ints, 2-tuples (cells), ('form', h, t, k) with k a noun used as code."""
import sys
src = open(sys.argv[1]).read().split()
assert src[0] == 'dag'
defs = [d for d in src[1:] if not d.startswith('@')]
jroot = int(src[-1][1:])
ids = {}
out = list(defs)
nxt = max(int(d.split('=')[0]) for d in defs) + 1
def node(rhs):
    global nxt
    if rhs in ids: return ids[rhs]
    i = nxt; nxt += 1
    out.append(f"{i}={rhs}"); ids[rhs] = i
    return i
S, K, I = node('S'), node('K'), node('I')
def ap(f, x): return node(f"{f}.{x}")
def pairT(a, b): return ap(ap(S, ap(ap(S, I), ap(K, a))), ap(K, b))
KK = ap(K, K)
def bl(n):
    if n == 0: return K
    return ap(K, pairT(K if n & 1 else ap(K, I), bl(n >> 1)))
def atomT(b): return ap(ap(S, KK), ap(ap(S, KK), ap(ap(S, KK), ap(ap(S, I), ap(K, b)))))
def cellT(h, t): return ap(K, ap(ap(S, KK), ap(ap(S, KK), pairT(h, t))))
def formT(h, t, k): return ap(K, ap(K, ap(ap(S, KK), ap(ap(S, pairT(h, t)), ap(K, k)))))
def enc(n):
    if isinstance(n, int): return atomT(bl(n))
    if n[0] == 'form': return formT(enc(n[1]), enc(n[2]), enc(n[3]))
    return cellT(enc(n[0]), enc(n[1]))
root = ap(jroot, enc(eval(sys.argv[2])))
print('dag ' + ' '.join(out) + f' @{root}')
