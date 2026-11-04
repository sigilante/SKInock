/* Exhaustive search over SKI terms on lean-ski's write-once heap machine
 * (Ski/Heap.lean `mstep`: an application at the head pushes a stack cell; I
 * and K pop; S x y z writes the one application cell `y z` and continues with
 * x over z, (y z)).  Two opaque atoms stand for input-dependent pointers; a
 * goal is a state the term must reach.
 *
 *   search GOAL ORDER MAXLEAVES
 *
 *   ORDER 0: the stack is [P, k] (P on top); ORDER 1: [k, P].
 *   GOAL 1  k at the head with P itself on top            (hand P back bare)
 *   GOAL 2  k at the head with a fresh `K P` on top       (a wrapper, bare)
 *   GOAL 3  J at the head with `K P` on top               (control: J constant)
 *   GOAL 4  J at the head with `K P (K k)` or `S (K P) (K k)` on top
 *           (a two-field cell, both fields input-dependent)
 *   GOAL 5  k at the head with a K-thunk `K (K P) w` on top (any w)
 * Goals 3 and 4 add the constant atom J to the leaf alphabet. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
enum { CS, CK, CI, CAPP, CNIL, CCONS, CATOM };
typedef struct { int t, a, b; } Cell;
#define HMAX 4000
static Cell H[HMAX];
static int hn, Pp, Kp, Jp, goal;
static int leaves[16], lp, pos;
static const char *shp;
static int add(int t, int a, int b) { H[hn].t = t; H[hn].a = a; H[hn].b = b; return hn++; }
static int build(void) {
  if (shp[pos] == 'l') { pos++; int c = leaves[lp++]; if (c == 3) return Jp; return add(c == 0 ? CS : c == 1 ? CK : CI, 0, 0); }
  pos++; int f = build(); int x = build(); return add(CAPP, f, x);
}
static int isK(int a) { return H[a].t == CK; }
static int isKof(int q, int x) { return H[q].t == CAPP && isK(H[q].a) && H[q].b == x; }
static int check(int hd, int stk) {
  if (H[stk].t != CCONS) return 0;
  int q = H[stk].a;
  switch (goal) {
  case 1: return hd == Kp && q == Pp;
  case 2: return hd == Kp && isKof(q, Pp);
  case 3: return hd == Jp && isKof(q, Pp);
  case 4: {
    if (hd != Jp || H[q].t != CAPP) return 0;
    int f = H[q].a, g = H[q].b;
    if (!isKof(g, Kp) || H[f].t != CAPP) return 0;
    if (isK(H[f].a) && H[f].b == Pp) return 1;
    return H[H[f].a].t == CS && isKof(H[f].b, Pp);
  }
  case 5: {
    if (hd != Kp || H[q].t != CAPP) return 0;
    int f = H[q].a;
    return H[f].t == CAPP && isK(H[f].a) && isKof(H[f].b, Pp);
  }
  }
  return 0;
}
static int run(int hd, int stk, int fuel) {
  while (fuel--) {
    if (check(hd, stk)) return 1;
    if (hn > HMAX - 10) return 0;
    Cell c = H[hd];
    if (c.t == CAPP) { int s = add(CCONS, c.b, stk); hd = c.a; stk = s; continue; }
    if (H[stk].t != CCONS) return 0;
    if (c.t == CI) { hd = H[stk].a; stk = H[stk].b; continue; }
    int s1 = H[stk].b; if (H[s1].t != CCONS) return 0;
    if (c.t == CK) { hd = H[stk].a; stk = H[s1].b; continue; }
    int s2 = H[s1].b; if (H[s2].t != CCONS) return 0;
    if (c.t == CS) {
      int x = H[stk].a, y = H[s1].a, z = H[s2].a, s3 = H[s2].b;
      int yz = add(CAPP, y, z); int c1 = add(CCONS, yz, s3); int c2 = add(CCONS, z, c1);
      hd = x; stk = c2; continue;
    }
    return 0;
  }
  return 0;
}
static char **memo[16]; static int cnt[16];
static int shapes(int n, char ***res) {
  if (memo[n]) { *res = memo[n]; return cnt[n]; }
  char **r; int k = 0;
  if (n == 1) { r = malloc(sizeof(char *)); r[0] = strdup("l"); k = 1; }
  else {
    int total = 0; char **a, **b;
    for (int i = 1; i < n; i++) total += shapes(i, &a) * shapes(n - i, &b);
    r = malloc(sizeof(char *) * total);
    for (int i = 1; i < n; i++) {
      int na = shapes(i, &a), nb = shapes(n - i, &b);
      for (int p = 0; p < na; p++) for (int q = 0; q < nb; q++) {
        char *s = malloc(2 * n + 2); s[0] = 'a'; strcpy(s + 1, a[p]); strcat(s, b[q]); r[k++] = s;
      }
    }
  }
  memo[n] = r; cnt[n] = k; *res = r; return k;
}
static void show(const char *s, const int *lv) {
  int j = 0; for (int i = 0; s[i]; i++) putchar(s[i] == 'a' ? '`' : "SKIJ"[lv[j++]]);
  putchar('\n');
}
int main(int argc, char **argv) {
  if (argc != 4) { fprintf(stderr, "usage: search GOAL ORDER MAXLEAVES\n"); return 2; }
  goal = atoi(argv[1]); int order = atoi(argv[2]), maxn = atoi(argv[3]);
  int B = goal == 3 || goal == 4 ? 4 : 3; long found = 0, terms = 0;
  for (int n = 1; n <= maxn; n++) {
    char **sh; int ns = shapes(n, &sh); long tot = 1; for (int i = 0; i < n; i++) tot *= B;
    for (int si = 0; si < ns; si++) for (long code = 0; code < tot; code++) {
      long c = code; for (int i = 0; i < n; i++) { leaves[i] = c % B; c /= B; }
      hn = 0; int nil = add(CNIL, 0, 0); Pp = add(CATOM, 1, 0); Kp = add(CATOM, 2, 0); Jp = add(CATOM, 3, 0);
      pos = 0; lp = 0; shp = sh[si]; int t = build();
      int st = order == 0 ? add(CCONS, Pp, add(CCONS, Kp, nil)) : add(CCONS, Kp, add(CCONS, Pp, nil));
      terms++;
      if (run(t, st, 300)) { found++; if (found <= 3) { printf("  found: "); show(sh[si], leaves); } }
    }
  }
  printf("goal %d, order %d, terms of 1..%d leaves: %ld terms, %ld reach the goal\n", goal, order, maxn, terms, found);
  return 0;
}
