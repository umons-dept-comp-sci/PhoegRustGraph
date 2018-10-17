#ifndef NAUTY_WRAPPER_C
#define NAUTY_WRAPPER_C

#include <nauty/naututil.h>
#include <nauty/nauty.h>
#include <stdio.h>

void init_graph(graph* tab, unsigned long n, unsigned long m, unsigned char* g)
{
    EMPTYGRAPH(tab, n, m);
    unsigned char d = 7;
    for (unsigned long i = 1; i < n; ++i) {
        for (unsigned long j = 0; j < i; ++j) {
            if ((*g >> d) % 2) {
                ADDONEEDGE(tab, i, j, m);
            }
            if (d == 0) {
                d = 7;
                ++g;
            } else {
                --d;
            }
        }
    }
}

void nauty_wrapper(
    int n, int m, unsigned char* g, int* lab, int* ptn, int* orbits)
{
    if (m > 0) {
        static DEFAULTOPTIONS_GRAPH(options);
        options.getcanon = 1;
        options.defaultptn = 0;
        statsblk stats;
        graph tab[n * m];
        init_graph(tab, n, m, g);
        graph cannon[n * m];
        densenauty(tab, lab, ptn, orbits, &options, &stats, m, n, cannon);
    } else {
        int p = 0;
        int s = 0;
        int mi = n;
        for (int i = 0; i < n; ++i) {
            if (mi > lab[i]) {
                mi = lab[i];
            }
            if (ptn[i] == 0) {
                for (int j = s; j <= p; ++j) {
                    orbits[lab[j]] = mi;
                }
                mi = n;
                s = p + 1;
            }
            ++p;
        }
    }
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
