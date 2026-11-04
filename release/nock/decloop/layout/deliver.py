"""The 12-leaf term that hands a fresh wrapper `K P` to a dynamic
continuation k, folded into the thunk `K (K P) w`, on a model of lean-ski's
write-once heap machine (Ski/Heap.lean `mstep`).  Stack [k, P], k on top.

    T = S (K (S (S (K (S (K (S I)) K)) K))) K

    park k as K k, bring P to the top, write K P (the continuation of that
    S is constant code), park K P as K (K P), fold it over the parked k, and
    run the fold: k receives K (K P) w, never K P itself."""
import sys

H = []

def add(c):
    H.append(c)
    return len(H) - 1

def parse(s):
    toks = [c for c in s if c != ' ']
    def p(i):
        if toks[i] == '(':
            f, i = p(i + 1)
            while toks[i] != ')':
                x, i = p(i)
                f = add(('app', f, x))
            return f, i + 1
        return add((toks[i],)), i + 1
    return p(0)[0]

def run(hd, stk, goal, fuel=500):
    for _ in range(fuel):
        if goal(hd, stk):
            return True
        c = H[hd]
        if c[0] == 'app':
            stk = add(('cons', c[2], stk)); hd = c[1]; continue
        args = []
        s = stk
        while len(args) < 3 and H[s][0] == 'cons':
            args.append(H[s][1]); s = H[s][2]
        need = {'I': 1, 'K': 2, 'S': 3}.get(c[0])
        if need is None or len(args) < need:
            return False
        rest = stk
        for _ in range(need):
            rest = H[rest][2]
        if c[0] == 'I':
            hd, stk = args[0], rest
        elif c[0] == 'K':
            hd, stk = args[0], rest
        else:
            x, y, z = args
            yz = add(('app', y, z)); c1 = add(('cons', yz, rest)); c2 = add(('cons', z, c1))
            hd, stk = x, c2
    return False

T = parse("(S (K (S (S (K (S (K (S I)) K)) K))) K)")
nil = add(('nil',)); P = add(('atom', 'P')); k = add(('atom', 'k'))
st = add(('cons', k, add(('cons', P, nil))))

def isKof(q, x):
    return H[q][0] == 'app' and H[H[q][1]][0] == 'K' and H[q][2] == x

seen = {}
def goal(hd, stk):
    if hd != k or H[stk][0] != 'cons':
        return False
    q = H[stk][1]
    seen['bare'] = isKof(q, P)
    return H[q][0] == 'app' and H[H[q][1]][0] == 'app' and H[H[H[q][1]][1]][0] == 'K' and isKof(H[H[q][1]][2], P)

ok = run(T, st, goal)
print("T = S (K (S (S (K (S (K (S I)) K)) K))) K on [k, P]:",
      "k receives the thunk K (K P) w" if ok else "FAILED",
      "(and not K P bare)" if ok and not seen.get('bare') else "")
sys.exit(0 if ok else 1)
