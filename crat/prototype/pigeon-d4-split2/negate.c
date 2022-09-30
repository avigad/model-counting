#include <stdio.h>
#include <stdlib.h>

int main (int argc, char** argv) {

  FILE *input = fopen (argv[1], "r");

  int size = 0;
  while (1) {
    int lit;
    int tmp = fscanf (input, " %i ", &lit);
    if (tmp == EOF || tmp == 0) break;
    if (size == 0) printf ("a");
    size++;
    printf (" %i", -lit);
    if (lit == 0) { size = 0; printf ("\n"); }
  }

  fclose (input);
}
