/************************************************************************************[lpr-check.c]
Copyright (c) 2019 Marijn Heule, Carnegie Mellon University.
Last edit, December 21, 2019

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#define DELETED		-1
#define SUCCESS		1
#define UNKNOWN		2
#define FAILED		0
#define REDUCED		2
#define SATISFIED	3
#define CNF		100
#define LPR		200
#define CLPR		300

long long *alpha, *omega, now;

int *clsList, clsAlloc, clsLast;
int *table, tableSize, tableAlloc, maskAlloc;

int  getType   (int* list) { return list[1]; }
int  getIndex  (int* list) { return list[0]; }
int  getLength (int* list) { int i = 2; while (list[i]) i++; return i - 2; }
int* getHints  (int* list) { return list + getLength (list) + 2; }
int  nReduced  (int* list) { int c = 0; while (*list) if ((*list++) < 0) c++; return c; }

int convertLit (int lit)   { return (abs(lit) * 2) + (lit < 0); }

void printClause (int* clause) {
  while (*clause) printf ("%i ", *clause++); printf ("0\n"); }

void printHints (int* hints) {
  while (*hints > 0) printf ("%i ", *hints++); printf ("0\n"); }

int checkWitness (int *clause, int mask) {
  int res = SATISFIED;
  while (*clause) {
    int clit = convertLit (*clause++);
    if (omega[clit^1] == mask) res = REDUCED;
    if (omega[clit  ] == mask) return SATISFIED; }
  return res; }

int checkRedundancy (int pivot, int start, int *hints, long long thisMask, long long wMask) {
  int res = abs(*hints++);

  if (res != 0) { // skip below for the initial hints (to extend alpha)
    // check whether res is the first clause after start that is reduced and not satisfied by the witness
    while (start < res) {
      if (clsList[start++] != DELETED) {
        int *clause = table + clsList[start-1];
        if (checkWitness (clause, wMask) == REDUCED) { printf ("c ERROR: hint %i is missing\n", start-1); return FAILED; } } }
    if (clsList[res] == DELETED) { printf ("c ERROR: using DELETED clause %i\n", res); exit (2); }

    if (checkWitness (table + clsList[start], wMask) != REDUCED) {
      printf ("c ERROR: hint is not reduced by witness\n"); return FAILED; }

    // check whether the hint is blocked (i.e, saitsified by the assignment
    int flag = 0, *clause = table + clsList[res];
    while (*clause) {
      int clit = convertLit (*clause++);
      if (alpha[clit  ] >= thisMask) continue;       // lit is falsified
      if (alpha[clit^1] >= thisMask && omega[clit^1] != wMask) { return SUCCESS; } // blocked
      if (alpha[clit^1] >= thisMask && omega[clit^1] != wMask) { printf ("%i %lli %lli %lli %lli %lli\n", clit, thisMask, alpha[clit], alpha[clit^1], omega[clit], omega[clit^1]); return SUCCESS; } // blocked
      alpha[clit] = thisMask; } }

  // extend the current assignment with the unit clauses in the hints
  while (*hints > 0) {
    int hint = *(hints++);
    if (clsList[hint] == DELETED) { printf ("c ERROR: using DELETED clause %i\n", hint); exit (2); };
    int unit = 0, *clause = table + clsList[hint];
    while (*clause) {
      int clit = convertLit (*(clause++));
      if (alpha[clit] >= thisMask) continue; // lit is falsified
      if (unit != 0) {
        printf ("c ERROR: hint %i has multiple unassigned literals\n", hint); return FAILED; }
      unit = clit; }
    if (unit == 0) return SUCCESS; // hint is falsified (empty clause)
    alpha[unit^1] = thisMask; } // hint is unit: assign to alpha

  if (res == 0) return UNKNOWN;
  printf ("c ERROR: reached end of hint %i without conflict\n", res);
  return FAILED; }

int checkClause (int* list, int size, int* hints) {
  now++;
  int i, pivot = convertLit (list[0]);
  int nRed = nReduced (hints + 1);

  // assign all literals in the clause to false (using mask: now + nRed)
  for (i = 0; i < size; i++) {
    int clit = convertLit (list[i]);
    if ((i > 0) && (clit == pivot)) break; // start of witness
    if (clit >= maskAlloc) { // found a new auxiliary variable
      maskAlloc = (clit * 3) >> 1;
      alpha = (long long *) realloc (alpha, sizeof (long long) * maskAlloc);
      omega = (long long *) realloc (omega, sizeof (long long) * maskAlloc);
      if (alpha == NULL || omega == NULL) exit(0); }
    alpha[clit] = now + nRed; }

  int finalMask = now + nRed;
  int res = checkRedundancy (pivot, 0, hints, finalMask, finalMask);
  //printf("%i\n", res);

  if (res  == FAILED) {
    printf ("c ERROR: failed while checking hint %i\n", res);
    return FAILED; }
  if (res  == SUCCESS) return SUCCESS;
  if (nRed == 0) {
    printf ("c ERROR: clause ");
    for (i = 0; i < size; i++) printf ("%i ", list[i]);
    printf("has no hints\n");
    return FAILED; }

  // set witness
  omega[pivot] = finalMask;
  for (; i < size; i++) {
    int clit = convertLit (list[i]);
    omega[clit] = finalMask;
    // need to reduce omega?
    // or provide a warning?
  }

  int start = 1;
  while (1) {
    hints++; now++; while (*hints > 0) hints++;
    if (*hints == 0) break;
    if (checkRedundancy (pivot, start, hints, now, finalMask) == FAILED) return FAILED;
    start = abs(*hints) + 1; }

  // check whether no hint is missing
  while (start <= clsLast) {
    if (clsList[start++] != DELETED) {
      int *clause = table + clsList[start-1];
      if (checkWitness (clause, finalMask) == REDUCED) { printf ("c ERROR: hint %i is missing\n", start-1); return FAILED; } } }

  return SUCCESS; }

void addClause (int index, int* literals, int size) {
  if (index >= clsAlloc) {
    int i = clsAlloc;
    clsAlloc = (index * 3) >> 1;
    clsList = (int*) realloc (clsList, sizeof(int) * clsAlloc);
    while (i < clsAlloc) clsList[i++] = DELETED; }

  if (tableSize + size >= tableAlloc) { // increase table if too small
    tableAlloc = (tableAlloc * 3) >> 1;
    table = (int*) realloc (table, sizeof (int) * tableAlloc); }

  int pivot = literals[0];
  clsList[index] = tableSize;
  int i; for (i = 0; i < size; i++) {
    if (i > 0 && literals[i] == pivot) break; // don't store the witness
    table[tableSize++] = literals[i]; }
  table[tableSize++] = 0;
  clsLast = index; }

void deleteClauses (int* list) {
  while (*list) {
    int index = *list++;
    if (clsList[index] == DELETED) {
      printf ("c WARNING: clause %i has already been deleted\n", index); }
    clsList[index] = DELETED; } }

int parseLine (FILE* file, int *list, int mode) {
  int lit, index, tmp, count = 0;

  if (mode == CNF) {
    while (1) {
      tmp = fscanf (file, " %i ", &lit);
      if (tmp == EOF) return 0;
      if (tmp == 0  ) {
        int i; char ignore[1<<16];
        if (fgets (ignore, sizeof (ignore), file) == NULL) printf ("c\n");
        if (ignore[0] != 'c') { printf ("c parsing error: %s\n", ignore); exit (255); }
        for (i = 0; i < sizeof ignore; i++) { if (ignore[i] == '\n') break; }
        if (i == sizeof ignore) {
          printf ("c ERROR: comment longer than %zu characters: %s\n", sizeof ignore, ignore); }
        return parseLine (file, list, mode); }
      list[count++] = lit;
      if (lit == 0) return count; } }

  if (mode == LPR) {
    int zeros = 2;
    tmp = fscanf (file, " %i ", &index);
    if (tmp == 0 || tmp == EOF) return 0;
    list[count++] = index;

    tmp = fscanf (file, " d %i ", &lit);
    if (tmp == 1) {
      list[count++] = (int) 'd';
      list[count++] = lit; zeros--;
      if (lit   == 0) zeros--;
      if (zeros == 0) return count; }
    else { list[count++] = (int) 'a'; }

    while (1) {
      tmp = fscanf (file, " %i ", &lit);
      if (tmp == 0 || tmp == EOF) return 0;
      list[count++] = lit;
      if (lit   == 0) zeros--;
      if (zeros == 0) return count; } }

  return 0; }

int main (int argc, char** argv) {
  now = 0, clsLast = 0;

  int i, nVar = 0, nCls = 0;
  char ignore[1024];
  FILE* cnf   = fopen (argv[1], "r");
  for (;;) {
    int tmp = fscanf (cnf, " p cnf %i %i ", &nVar, &nCls);
    if (nVar > 0) break;
    char* c = fgets (ignore, sizeof (ignore), cnf);
    int j; for (j = 0; j < 1024; j++) { if (ignore[j] == '\n') break; }
    if (j == 1024) {
      printf ("c ERROR: comment longer than 1024 characters: %s\n", ignore); exit (0); } }

  clsAlloc = nCls * 2;
  clsList  = (int*) malloc (sizeof(int) * clsAlloc);
  for (i = 0; i < clsAlloc; i++) clsList[i] = DELETED;

  tableSize  = 0;
  tableAlloc = nCls * 2;
  table = (int *) malloc (sizeof(int) * tableAlloc);

  int* list = (int*) malloc (sizeof (int) * nVar * 10);
  int index = 1;
  while (1) {
    int size = parseLine (cnf, list, CNF);
    if (size == 0) break;
    if (index > nCls) { printf ("c too many clauses in formula\n"), exit (255); }
    addClause (index++, list, size); }
  fclose (cnf);

  printf ("c parsed a formula with %i variables and %i clauses\n", nVar, nCls);

  maskAlloc = 20 * nVar;
  alpha = (long long*) malloc (sizeof(long long) * maskAlloc);
  omega = (long long*) malloc (sizeof(long long) * maskAlloc);
  for (i = 0; i < maskAlloc; i++) alpha[i] = omega[i] = 0;

  FILE* proof = fopen (argv[2], "r");
  int mode = LPR;
  while (1) {
    int size = parseLine (proof, list, mode);
    if (size == 0) break;

    if (getType (list) == (int) 'd') {
      deleteClauses (list + 2); }
    else if (getType (list) == (int) 'a') {
      int  index  = getIndex  (list);
      int  length = getLength (list);
      int* hints  = getHints  (list);

      if (checkClause (list + 2, length, hints) == SUCCESS) {
        addClause (index, list + 2, length); }
      else {
        printf("c failed to check clause: "); printClause (list + 2);
        printf("s NOT VERIFIED\n");
        exit (0); }

      if (length == 0) {
        printf ("s VERIFIED\n");
        exit (1); }
    }
    else {
      printf ("c failed type\n");
      exit (0); }
  }
}
