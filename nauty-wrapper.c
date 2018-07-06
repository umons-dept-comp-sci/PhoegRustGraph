#ifndef NAUTY_WRAPPER_C
#define NAUTY_WRAPPER_C

#include <stdio.h>
#include <nauty.h>

void init_graph(graph *tab, unsigned long n, unsigned long m, unsigned char *g)
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
            }
            else {
                --d;
            }
        }
    }
}

void init_fixed(int *lab, int *ptn, int n, int *fixed, int nfixed)
{
    for (long p = 0; p < n; ++p) {
        lab[p] = n;
    }
    for (long f = 0; f < nfixed; ++f) {
        lab[fixed[f]] = fixed[f];
    }
    long p = 0;
    for (long i = 0; i < n; ++i) {
        if (lab[i] == n) {
            lab[i] = i;
        }
        else {
            long tmp = lab[p];
            lab[p] = lab[i];
            lab[i] = tmp;
            ++p;
        }
        if (i < nfixed || i == n - 1) {
            ptn[i] = 0;
        }
        else {
            ptn[i] = 1;
        }
    }
}

void nauty_wrapper(int n, int m, unsigned char *g, int *lab, int *ptn, int *orbits)
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
    }
    else {
        int p = 0;
        int s = 0;
        int mi = n;
        for (int i = 0; i < n; ++i) {
            if (mi > lab[i]) {
                mi = lab[i];
            }
            if (ptn[i] == 0) {
                for (int j = s; i <= p; ++j) {
                    orbits[lab[j]] = mi;
                }
                mi = n;
                s = p+1;
            }
            ++p;
        }
    }
}

#endif
