#ifndef NAUTY_WRAPPER_C
#define NAUTY_WRAPPER_C

#include <stdio.h>
#include <nauty/naututil.h>
#include <nauty/nautinv.h>
#include <nauty/nauty.h>

typedef unsigned long long int ullong;

void _nauty_wrapper(
    ullong n, ullong m, graph* g, int* lab, int* ptn, int* orbits, optionblk options)
{
    if (m > 0) {
        options.getcanon = 1;
        options.defaultptn = 0;
        statsblk stats;
        graph cannon[n * m];
        densenauty(g, lab, ptn, orbits, &options, &stats, m, n, cannon);
    } else {
        ullong p = 0;
        ullong s = 0;
        ullong mi = n;
        for (ullong i = 0; i < n; ++i) {
            if (mi > (ullong) lab[i]) {
                mi = lab[i];
            }
            if (ptn[i] == 0) {
                for (ullong j = s; j <= p; ++j) {
                    orbits[lab[j]] = mi;
                }
                mi = n;
                s = p + 1;
            }
            ++p;
        }
    }
}

void nauty_wrapper(ullong n, ullong m, graph* g, int* lab, int* ptn, int* orbits) {
    static DEFAULTOPTIONS_GRAPH(options);
    _nauty_wrapper(n, m, g, lab, ptn, orbits, options);
}

void nauty_wrapper_directed(ullong n, ullong m, graph* g, int* lab, int* ptn, int* orbits) {
    static DEFAULTOPTIONS_DIGRAPH(options);
    _nauty_wrapper(n, m, g, lab, ptn, orbits, options);
}

int wordsize() { return WORDSIZE; }

int setwordsneeded(int n) { return SETWORDSNEEDED(n); }

void emptyset(set* s, int m) { EMPTYSET(s, m); }

void addelement(set* s, int e) { ADDELEMENT(s, e); }

void delelement(set* s, int e) { DELELEMENT(s, e); }

void flipelement(set* s, int e) { FLIPELEMENT(s, e); }

int iselement(const set* s, int e) { return ISELEMENT(s, e); }

set allbits() { return ALLBITS; }

set bitmask(int i) { return BITMASK(i); }

set allmask(int i) { return ALLMASK(i); }

void emptygraph(graph* g, int m, int n) { EMPTYGRAPH(g, m, n); }

set* graphrow(graph* g, int v, int m) { return GRAPHROW(g, v, m); }

set* graphrowmut(const graph* g, int v, int m) { return GRAPHROW(g, v, m); }

void addoneedge(graph* g, int v, int w, int m) { ADDONEEDGE(g, v, w, m); }

#endif
